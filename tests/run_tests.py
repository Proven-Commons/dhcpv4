#!/usr/bin/env python3
"""Tests for the Lean DHCPv4 wire message parser and printer.

Five parts.

1. Fixed cases built by hand from RFC 2131 and RFC 2132: a
   DISCOVER, an OFFER, a REQUEST, an ACK, a RELEASE, and an
   INFORM, each written out byte by byte here; the pad cases
   (pad bytes among the options, zero padding after the end
   byte, and a message with no end byte); and the rejection
   shapes (a 239 byte message, a wrong cookie, an option
   length overrunning the end, a code byte as the last byte,
   no option 53, option 53 with length 2, option 53 with
   value 0 and with value 9, option 53 twice, op 3, hlen 17,
   a nonzero byte after the end byte, a truncated fixed
   field, an empty input, and an option area with nothing the
   message type rule can use).

2. A differential run against a strict Python oracle written
   in this harness from the rules in SPEC.md: random well
   formed messages, some with pad bytes sprinkled among the
   options, some with zero padding after the end byte, some
   with no end byte; random raw byte strings; random option
   areas behind a fixed part and the cookie, built to reach
   the edges of the option reader (option 53 missing,
   repeated, of length 0 or 2, or of any value; option 52;
   options in file and sname; bytes after the end byte; no
   end byte; a lone code byte; an option running past the
   end); and mutations of one rich message (every
   truncation, every single byte flip, and targeted
   changes).

3. A Scapy cross check: packets built with Scapy's BOOTP and
   DHCP layers, each fed to the tool and to the oracle; the
   tool must agree with the oracle on each one. Scapy is only
   a source of independently built bytes here; the oracle
   settles every verdict. The packets are stored in
   tests/scapy-packets.txt with the Scapy version that built
   them, so every run feeds the same inputs whether or not
   Scapy is installed; `--rebuild-scapy` rebuilds the file
   with Scapy from this interpreter or from the project venv
   at ../venv. Neither ISC DHCP nor dnsmasq is installed in
   this environment, and no capture from either is available,
   so no capture corpus was run; the record says so too.

4. Malformed request lines must be answered `error`.

5. A Wireshark cross check: every message the parts above
   feed the tool, and the probes (WS_PROBES: options built by
   hand at the edges of WsModel, below, each in a DISCOVER
   after option 53, fed to the tool and checked against the
   oracle like the rest), taken and turned away alike, is
   written by this script as the UDP payload of an
   Ethernet/IPv4/UDP frame (port 68 to 67, or 67 to 68 for
   op 2) into a pcap file, and dissected in batches by
   Wireshark's DHCP/BOOTP dissector with
   `tshark -n -r FILE -T json -x`. For a
   message the tool takes, Wireshark must show op, htype,
   hlen, hops, xid, secs, flags, ciaddr, yiaddr, siaddr,
   giaddr, chaddr, sname, file and the cookie as the tool's
   reprint holds them, read at the offsets SPEC.md gives;
   the same options, code, length and value bytes, in order;
   the same end option and bytes after it; the same message
   type; and no Malformed Packet mark and no expert error.
   For a message the tool turns away, Wireshark must stop
   with an exception at a rule the tool turns it away for
   (WS_AGREE), or find no payload. Where Wireshark 4.2 reads
   a message differently from SPEC.md on purpose, the
   difference is a named one (WS_NAMED). The harness finds
   the reason for each in the message's bytes: the fixed
   fields and option 53 as SPEC.md reads them, and, for each
   fault Wireshark reports, the same fault in WsModel, the
   harness's account of what Wireshark 4.2.2's dissector does
   with those bytes, written from its code (packet-dhcp.c,
   and get_dns_name in packet-dns.c, at tag v4.2.2). Each
   Malformed Packet must be one the model finds, at the same
   option, and each expert error one the model finds in the
   same option, and the other way round, in every option.
   For a message the tool turns away, each rule it breaks
   that Wireshark's dissection reaches must show in
   Wireshark's own reading too. Every other difference is a
   failure. The record lists the named differences this run
   found, each with its count, and what the harness found
   under each.
   The part runs when tshark is on PATH; without it the
   record says the part did not run, and
   `--require-wireshark` makes that a failure.

Two more line checks stand apart from the fixed cases of
part 1: the requests `parse ` and `parse`, with no codes,
must be answered `none` (the empty message is turned away).
The results file counts them on their own line, not as
fixed cases. So is the example request in README.md: the
harness reads it from the page, runs it, and checks that the
answer is `ok:` and the same codes, as the page says.

The readings SPEC.md lists as departing from the RFCs each
have a case too (no end byte, bytes after the end byte,
option 52 with a second option 53 in file or sname, a
message type split over two items, a repeated option, and
the registered types 9 to 18). For each, the harness checks
that its oracle gives the verdict SPEC.md states, then that
the tool agrees.

Every `ok:` answer is also checked to be a well formed
message, as `Spec.parse_wf` says: op 1 or 2, hlen at most
16, the cookie at offset 236, codes from 1 to 254, and option
53 exactly once with a value from 1 to 8.

    python3 tests/run_tests.py [--seed N] [--count N]
        [--raw-count N] [--area-count N] [--rebuild-scapy]
        [--require-wireshark]

The tool is driven one batch process per chunk of requests,
input written and closed, output drained until the process
exits. It builds the executable first, writes
tests/TEST-RESULTS.md, and exits non-zero if any check fails.
It needs Python 3.11 or later.
"""

import argparse
import json
import os
import platform
import random
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import threading
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "dhcpv4"
RESULTS = ROOT / "tests" / "TEST-RESULTS.md"
README = ROOT / "README.md"
TIMEOUT = 900
BUILD_TIMEOUT = 3600
CHUNK = 200

SEED_DEFAULT = 20261026

COOKIE = bytes([99, 130, 83, 99])


def codes(data):
    return ",".join(str(b) for b in data)


def request(data):
    return "parse " + codes(data)


def run_tool(lines, timeout=TIMEOUT):
    """Run the tool on a batch of request lines.

    Returns (answers, problem). No right answer is longer than
    its request plus a small constant, so output past twice the
    input plus 64 bytes a line is stopped, not read until memory
    runs out.
    """
    data = "".join(line + "\n" for line in lines)
    raw = data.encode("utf-8")
    limit = 2 * len(raw) + 64 * (len(lines) + 1)
    try:
        proc = subprocess.Popen(
            [str(EXE)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except OSError as e:
        return [], f"could not run {EXE}: {e.strerror or e}"
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf, cap):
        while chunk := stream.read1(1 << 16):
            buf += chunk
            if len(buf) > cap:
                proc.kill()
                return

    threads = [
        threading.Thread(target=feed),
        threading.Thread(target=drain, args=(proc.stdout, out, limit)),
        threading.Thread(target=drain, args=(proc.stderr, err, 1 << 20)),
    ]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if len(out) > limit:
        problem = problem or f"more than {limit} bytes of output, stopped"
    elif proc.returncode != 0 and not problem:
        tail = " / ".join(
            bytes(err).decode("utf-8", "backslashreplace").splitlines()[-3:]
        )
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    answers = text.split("\n")
    if answers and answers[-1] == "":
        answers.pop()
    if len(answers) != len(lines) and not problem:
        problem = f"tool gave {len(answers)} answers for {len(lines)} requests"
    return answers, problem


def ask_all(lines):
    """Chunked run_tool. Answers align with lines, or None entries."""
    answers = []
    problems = []
    for i in range(0, len(lines), CHUNK):
        chunk = lines[i : i + CHUNK]
        ans, problem = run_tool(chunk)
        if problem:
            problems.append(problem)
            ans = ans + [None] * (len(chunk) - len(ans))
        answers += ans
    return answers, problems


# ---------------------------------------------------------------- the
# builders and the strict oracle, written from the rules in SPEC.md.


def ip4(text):
    return int.from_bytes(bytes(int(p) for p in text.split(".")), "big")


def fixed_bytes(op, htype, hlen, hops, xid, secs, flags,
                ciaddr, yiaddr, siaddr, giaddr, chaddr, sname, file):
    out = bytes([op, htype, hlen, hops])
    out += xid.to_bytes(4, "big")
    out += secs.to_bytes(2, "big")
    out += flags.to_bytes(2, "big")
    for a in (ciaddr, yiaddr, siaddr, giaddr):
        out += a.to_bytes(4, "big")
    out += chaddr + sname + file
    assert len(out) == 236
    return out


def option_area(options, end=True):
    out = bytearray()
    for c, v in options:
        out += bytes([c, len(v)]) + v
    if end:
        out.append(255)
    return bytes(out)


def oracle_parse(data):
    """The strict reading of the rules in SPEC.md, as a parse
    into the canonical reprint. The reprinted bytes, or None
    when the message is rejected."""
    if len(data) < 240:
        return None
    op = data[0]
    hlen = data[2]
    if op not in (1, 2):
        return None
    if hlen > 16:
        return None
    if data[236:240] != COOKIE:
        return None
    options = []
    i = 240
    while i < len(data):
        b = data[i]
        if b == 0:
            i += 1
            continue
        if b == 255:
            if any(x != 0 for x in data[i + 1:]):
                return None
            i = len(data)
            break
        if i + 1 >= len(data):
            return None
        ln = data[i + 1]
        if i + 2 + ln > len(data):
            return None
        options.append((b, bytes(data[i + 2: i + 2 + ln])))
        i += 2 + ln
    types = [v for c, v in options if c == 53]
    if len(types) != 1:
        return None
    t = types[0]
    if len(t) != 1 or not (1 <= t[0] <= 8):
        return None
    out = bytearray(data[:240])
    for c, v in options:
        out += bytes([c, len(v)]) + v
    out.append(255)
    return bytes(out)


def expected(data):
    got = oracle_parse(data)
    if got is None:
        return "none"
    return "ok:" + codes(got)


def reprint_problem(answer):
    """What `Spec.parse_wf` says, checked on the tool's own
    answer: when the answer is `ok:`, the reprinted message is
    well formed. Returns why it is not, or None. The reprint is
    in canonical form, so it has no pad bytes and ends at its
    one end byte."""
    if not answer.startswith("ok:"):
        return None
    try:
        data = bytes(int(x) for x in answer[3:].split(","))
    except ValueError:
        return "the reprint is not a list of byte codes"
    if len(data) < 241:
        return "the reprint is shorter than 241 bytes"
    if data[0] not in (1, 2):
        return f"op {data[0]}"
    if data[2] > 16:
        return f"hlen {data[2]}"
    if data[236:240] != COOKIE:
        return "no cookie at offset 236"
    types = []
    i = 240
    while data[i] != 255:
        c = data[i]
        if c == 0:
            return "a pad byte in the reprint"
        if i + 1 >= len(data) or i + 2 + data[i + 1] > len(data):
            return "an option runs past the end of the reprint"
        if c == 53:
            types.append(bytes(data[i + 2:i + 2 + data[i + 1]]))
        i += 2 + data[i + 1]
        if i >= len(data):
            return "no end byte in the reprint"
    if i != len(data) - 1:
        return "bytes after the end byte of the reprint"
    if len(types) != 1 or len(types[0]) != 1 or not 1 <= types[0][0] <= 8:
        return f"option 53 values {[t.hex() for t in types]}"
    return None


# ---------------------------------------------------------------- checks


class Tally:
    def __init__(self):
        self.inputs = 0
        self.agreements = 0
        self.failures = []
        # Every message checked, with the tool's answer, for the
        # Wireshark cross check (part 5).
        self.messages = []

    def check(self, data, answer, label):
        self.inputs += 1
        self.messages.append((label, bytes(data), answer))
        want = expected(data)
        problem = reprint_problem(str(answer))
        if answer == want and problem is None:
            self.agreements += 1
        elif problem is not None:
            self.failures.append(f"{label}: reprint not well formed: {problem}")
        else:
            self.failures.append(
                f"{label}: want {want[:80]}, got {str(answer)[:80]}"
            )

    def check_line(self, line, answer, want, label):
        self.inputs += 1
        if answer == want:
            self.agreements += 1
        else:
            self.failures.append(f"{label}: want {want}, got {answer}")


MAC = bytes([0x00, 0x0B, 0x82, 0x01, 0xFC, 0x42]) + bytes(10)
ZEROS64 = bytes(64)
ZEROS128 = bytes(128)
SERVER = ip4("192.168.1.1")
OFFERED = ip4("192.168.1.100")
MASK = ip4("255.255.255.0")


def discover():
    f = fixed_bytes(1, 1, 6, 0, 0x12345678, 0, 0x8000,
                    0, 0, 0, 0, MAC, ZEROS64, ZEROS128)
    return f + COOKIE + option_area([(53, bytes([1])),
                                     (55, bytes([1, 3, 6, 15]))])


def offer():
    f = fixed_bytes(2, 1, 6, 0, 0x12345678, 0, 0x8000,
                    0, OFFERED, SERVER, 0, MAC, ZEROS64, ZEROS128)
    return f + COOKIE + option_area([
        (53, bytes([2])),
        (54, SERVER.to_bytes(4, "big")),
        (51, (3600).to_bytes(4, "big")),
        (1, MASK.to_bytes(4, "big")),
    ])


def request_msg():
    f = fixed_bytes(1, 1, 6, 0, 0x12345679, 0, 0x8000,
                    0, 0, 0, 0, MAC, ZEROS64, ZEROS128)
    return f + COOKIE + option_area([
        (53, bytes([3])),
        (50, OFFERED.to_bytes(4, "big")),
        (54, SERVER.to_bytes(4, "big")),
    ])


def ack():
    f = fixed_bytes(2, 1, 6, 0, 0x12345679, 0, 0x8000,
                    0, OFFERED, SERVER, 0, MAC, ZEROS64, ZEROS128)
    return f + COOKIE + option_area([
        (53, bytes([5])),
        (54, SERVER.to_bytes(4, "big")),
        (51, (3600).to_bytes(4, "big")),
    ])


def release():
    f = fixed_bytes(1, 1, 6, 0, 0x87654321, 0, 0,
                    OFFERED, 0, 0, 0, MAC, ZEROS64, ZEROS128)
    return f + COOKIE + option_area([
        (53, bytes([7])),
        (54, SERVER.to_bytes(4, "big")),
    ])


def inform():
    f = fixed_bytes(1, 1, 6, 0, 0x0BADF00D, 3, 0,
                    OFFERED, 0, 0, 0, MAC, ZEROS64, ZEROS128)
    return f + COOKIE + option_area([(53, bytes([8]))])


def fixed_cases():
    d = discover()
    cases = [
        ("discover", d),
        ("offer", offer()),
        ("request", request_msg()),
        ("ack", ack()),
        ("release", release()),
        ("inform", inform()),
    ]
    # The pad cases. Pads among the options parse to the same
    # value as the same message without them.
    f = fixed_bytes(1, 1, 6, 0, 0x12345678, 0, 0x8000,
                    0, 0, 0, 0, MAC, ZEROS64, ZEROS128)
    padded = (
        f + COOKIE
        + bytes([0, 0, 53, 1, 1, 0, 55, 4, 1, 3, 6, 15, 0, 255])
    )
    cases.append(("pads-among-options", padded))
    # Zero padding after the end byte parses clean and is
    # dropped by the reprint.
    cases.append(("zeros-after-end", d + bytes(32)))
    # No end byte: the options run exactly to the end.
    cases.append(("no-end-byte", d[:-1]))
    # Pads and trailing zeros together.
    cases.append(("pads-and-zeros", padded + bytes(17)))
    # The rejection shapes.
    bad = bytearray(d)
    bad[238] = 100
    cases.append(("wrong-cookie", bytes(bad)))
    cases.append(("short-239", d[:239]))
    cases.append(("truncated-fixed", d[:100]))
    overrun = f + COOKIE + bytes([53, 1, 1, 55, 10, 1, 3, 6])
    cases.append(("option-overrun", overrun))
    codelast = f + COOKIE + bytes([53, 1, 1, 55])
    cases.append(("code-last-byte", codelast))
    no53 = f + COOKIE + option_area([(55, bytes([1, 3, 6, 15]))])
    cases.append(("no-option-53", no53))
    len2 = f + COOKIE + option_area([(53, bytes([1, 2]))])
    cases.append(("option-53-length-2", len2))
    val0 = f + COOKIE + option_area([(53, bytes([0]))])
    cases.append(("option-53-value-0", val0))
    val9 = f + COOKIE + option_area([(53, bytes([9]))])
    cases.append(("option-53-value-9", val9))
    twice = f + COOKIE + option_area([(53, bytes([1])),
                                      (53, bytes([1]))])
    cases.append(("option-53-twice", twice))
    badop = bytearray(d)
    badop[0] = 3
    cases.append(("op-3", bytes(badop)))
    badhlen = bytearray(d)
    badhlen[2] = 17
    cases.append(("hlen-17", bytes(badhlen)))
    cases.append(("nonzero-after-end", d + bytes([1])))
    cases.append(("empty", b""))
    cases.append(("cookie-only", f + COOKIE))
    cases.append(("end-only", f + COOKIE + bytes([255])))
    return cases


def choice_cases():
    """The readings SPEC.md lists under "Readings that depart
    from the RFCs", each with the verdict the page states: True
    when the message is taken, False when it is turned away."""
    d = discover()
    f = fixed_bytes(1, 1, 6, 0, 0x12345678, 0, 0x8000,
                    0, 0, 0, 0, MAC, ZEROS64, ZEROS128)
    cases = [
        # RFC 2131 4.1: the last option must be the end option.
        # Taken here.
        ("no-end-byte", d[:-1], True),
        # RFC 2132 3.2: the bytes after the end option should be
        # pad bytes. A nonzero one is refused here.
        ("bytes-after-end", d + bytes([0xDE, 0xAD, 0xBE, 0xEF]), False),
    ]
    # Option 52 says file (1), sname (2), or both (3) carry more
    # options, and they hold a second option 53. Not read here:
    # the type comes from the options field alone.
    file_opts = bytes([53, 1, 3, 255]) + bytes(124)
    sname_opts = bytes([53, 1, 5, 255]) + bytes(60)
    for value, sname, file in [(1, ZEROS64, file_opts),
                               (2, sname_opts, ZEROS128),
                               (3, sname_opts, file_opts)]:
        fo = fixed_bytes(1, 1, 6, 0, 0x12345678, 0, 0x8000,
                         0, 0, 0, 0, MAC, sname, file)
        cases.append((f"overload-{value}-second-53", fo + COOKIE
                      + option_area([(53, bytes([1])),
                                     (52, bytes([value]))]), True))
    # RFC 3396: repeated options are joined. Not here, so a type
    # split over two items is two option 53 items, refused.
    cases.append(("option-53-split",
                  f + COOKIE + option_area([(53, b""), (53, bytes([1]))]),
                  False))
    # Repeats of another option are kept as separate items.
    cases.append(("option-55-repeated",
                  f + COOKIE + option_area([(53, bytes([1])),
                                            (55, bytes([1, 3])),
                                            (55, bytes([6, 15]))]),
                  True))
    # The registered message types 9 to 18, refused on purpose.
    for t in range(9, 19):
        cases.append((f"registered-type-{t}",
                      f + COOKIE + option_area([(53, bytes([t]))]),
                      False))
    return cases


def run_choices():
    tally = Tally()
    cases = choice_cases()
    answers, problems = ask_all([request(d) for _, d, _ in cases])
    tally.failures += problems
    for (label, data, taken), answer in zip(cases, answers):
        if (oracle_parse(data) is not None) != taken:
            tally.inputs += 1
            tally.failures.append(
                f"reading {label}: the harness oracle does not give the"
                f" verdict SPEC.md states")
            continue
        tally.check(data, answer, f"reading {label}")
    return tally


def random_message(rng):
    op = rng.choice([1, 2])
    htype = rng.choice([1, 6, rng.randrange(256)])
    hlen = rng.randint(0, 16)
    hops = rng.randrange(4)
    xid = rng.randrange(2**32)
    secs = rng.randrange(2**16)
    flags = rng.choice([0, 0x8000, rng.randrange(2**16)])

    def addr():
        return rng.choice(
            [0, 0xFFFFFFFF, rng.randrange(2**32),
             ip4("10.0.0.7"), ip4("172.16.0.1")]
        )

    if rng.random() < 0.6:
        chaddr = bytes(rng.randrange(256) for _ in range(6)) + bytes(10)
    else:
        chaddr = bytes(rng.randrange(256) for _ in range(16))

    def field(n):
        r = rng.random()
        if r < 0.5:
            return bytes(n)
        if r < 0.75:
            word = bytes(rng.randrange(1, 256) for _ in range(rng.randint(1, 8)))
            return word + bytes(n - len(word))
        return bytes(rng.randrange(256) for _ in range(n))

    options = []
    for _ in range(rng.randint(0, 5)):
        c = rng.choice([c for c in range(1, 255) if c != 53])
        v = bytes(rng.randrange(256) for _ in range(rng.randint(0, 24)))
        options.append((c, v))
    t = rng.randint(1, 8)
    options.insert(rng.randint(0, len(options)), (53, bytes([t])))
    for _ in range(rng.randint(0, 2)):
        c = rng.choice([c for c in range(1, 255) if c != 53])
        v = bytes(rng.randrange(256) for _ in range(rng.randint(0, 8)))
        options.append((c, v))

    f = fixed_bytes(op, htype, hlen, hops, xid, secs, flags,
                    addr(), addr(), addr(), addr(),
                    chaddr, field(64), field(128))
    # The option area, with pads sprinkled at item boundaries,
    # and one of three endings: the end byte, the end byte and
    # zero padding, or no end byte at all.
    area = bytearray()
    for c, v in options:
        area += bytes(rng.randint(0, 3))
        area += bytes([c, len(v)]) + v
    area += bytes(rng.randint(0, 2))
    ending = rng.random()
    if ending < 0.4:
        area.append(255)
    elif ending < 0.7:
        area.append(255)
        area += bytes(rng.randint(1, 40))
    return f + COOKIE + bytes(area)


def run_fixed():
    tally = Tally()
    cases = fixed_cases()
    answers, problems = ask_all([request(d) for _, d in cases])
    tally.failures += problems
    for (label, data), answer in zip(cases, answers):
        tally.check(data, answer, f"fixed {label}")
    lines = Tally()
    answers, problems = ask_all(["parse ", "parse"])
    lines.failures += problems
    for line, answer in zip(["parse ", "parse"], answers):
        lines.check_line(line, answer, "none", "no codes")
    tally.lines = lines
    return tally


def run_readme():
    """The example request on the page, run as written. The page
    says the answer is `ok:` and the same codes back."""
    tally = Tally()
    prefix = "printf 'parse "
    suffix = "\\n' | .lake/build/bin/dhcpv4"
    lines = [l for l in README.read_text().splitlines()
             if l.startswith(prefix) and l.endswith(suffix)]
    if len(lines) != 1:
        tally.inputs += 1
        tally.failures.append(
            f"README example: found {len(lines)} example lines, want 1")
        return tally
    arg = lines[0][len(prefix):-len(suffix)]
    req = "parse " + arg
    answers, problems = ask_all([req])
    tally.failures += problems
    for answer in answers:
        tally.check_line("README example", answer, "ok:" + arg,
                         "README example")
        try:
            message = bytes(int(x) for x in arg.split(","))
        except ValueError:
            continue
        tally.messages.append(("README example", message, answer))
    return tally


def run_random(seed, valid_count, raw_count):
    """The random well formed messages and the random raw byte
    strings, from one generator seeded with `seed`. Returns a
    tally for each."""
    valid, raw = Tally(), Tally()
    rng = random.Random(seed)
    docs = [random_message(rng) for _ in range(valid_count)]
    answers, problems = ask_all([request(d) for d in docs])
    valid.failures += problems
    for i, (data, answer) in enumerate(zip(docs, answers)):
        valid.check(data, answer, f"random valid {i}")
    raws = []
    for _ in range(raw_count):
        n = rng.randint(0, 340)
        raws.append(bytes(rng.randrange(256) for _ in range(n)))
    answers, problems = ask_all([request(d) for d in raws])
    raw.failures += problems
    for i, (data, answer) in enumerate(zip(raws, answers)):
        raw.check(data, answer, f"random raw {i}")
    return valid, raw


def random_area_message(rng):
    """A fixed part, the cookie, and an option area built to
    reach the edges of the option reader: zero, one, or two
    option 53 items of length 0 to 2 with any value, option 52
    with values 0 to 4, pad bytes between items, and one of
    seven endings (the end byte; the end byte and zeros; the
    end byte and other bytes; no end byte; a lone code byte; an
    option whose length runs past the end; the end byte, a
    zero, and a nonzero byte). A quarter of them carry a second
    option 53 in file, and some in sname, as option 52 would
    announce. One in ten has an op or hlen at the edge of its
    rule."""
    op, hlen = rng.choice([1, 2]), rng.choice([0, 6, 16])
    if rng.random() < 0.1:
        op = rng.choice([0, 1, 2, 3, 255])
        hlen = rng.choice([6, 16, 17, 255])
    sname, file = ZEROS64, ZEROS128
    if rng.random() < 0.25:
        fo = bytes([53, 1, rng.randint(1, 18), 255])
        file = fo + bytes(128 - len(fo))
    if rng.random() < 0.15:
        so = bytes([53, 1, rng.randint(1, 18), 255])
        sname = so + bytes(64 - len(so))
    f = fixed_bytes(op, 1, hlen, 0, rng.randrange(2**32), 0, 0,
                    0, 0, 0, 0, MAC, sname, file)
    items = []
    for _ in range(rng.choices([0, 1, 2], weights=[1, 6, 2])[0]):
        ln = rng.choices([0, 1, 2], weights=[1, 8, 1])[0]
        items.append((53, bytes(rng.randint(1, 8) if rng.random() < 0.8
                                else rng.randrange(256)
                                for _ in range(ln))))
    for _ in range(rng.randint(0, 5)):
        c = rng.choice([rng.randint(1, 254), 52, 55, 12, 61])
        if c == 52:
            v = bytes([rng.randint(0, 4)])
        else:
            v = bytes(rng.randrange(256) for _ in range(rng.randint(0, 12)))
        items.append((c, v))
    rng.shuffle(items)
    area = bytearray()
    for c, v in items:
        area += bytes(rng.choice([0, 0, 0, 1, 2]))
        area += bytes([c, len(v)]) + v
    ending = rng.randrange(7)
    if ending == 0:
        area.append(255)
    elif ending == 1:
        area.append(255)
        area += bytes(rng.randint(1, 30))
    elif ending == 2:
        area.append(255)
        area += bytes(rng.randrange(256) for _ in range(rng.randint(1, 8)))
    elif ending == 3:
        pass
    elif ending == 4:
        area.append(rng.randint(1, 254))
    elif ending == 5:
        area += bytes([rng.randint(1, 254), rng.randint(1, 40)])
        area += bytes(rng.randrange(256) for _ in range(rng.randint(0, 3)))
    else:
        area += bytes([255, 0, rng.randint(1, 255)])
    return f + COOKIE + bytes(area)


def run_areas(seed, count):
    """Random option areas, from a generator of their own seeded
    from `seed`, so the other random runs keep their inputs."""
    tally = Tally()
    rng = random.Random(seed + 1)
    docs = [random_area_message(rng) for _ in range(count)]
    tally.taken = sum(1 for d in docs if oracle_parse(d) is not None)
    answers, problems = ask_all([request(d) for d in docs])
    tally.failures += problems
    for i, (data, answer) in enumerate(zip(docs, answers)):
        tally.check(data, answer, f"option area {i}")
    return tally


def run_mutations():
    tally = Tally()
    base = bytearray(discover())
    # Add a third option so the flips walk more shapes: rebuild
    # with a hostname option (12) before the end byte.
    f = fixed_bytes(1, 1, 6, 0, 0x12345678, 0, 0x8000,
                    0, 0, 0, 0, MAC, ZEROS64, ZEROS128)
    rich = f + COOKIE + option_area([
        (53, bytes([1])),
        (55, bytes([1, 3, 6, 15])),
        (12, b"client-7"),
        (43, bytes([1, 2, 3, 4, 5])),
    ])
    inputs = []
    labels = []
    for n in range(len(rich)):
        inputs.append(rich[:n])
        labels.append(f"truncate {n}")
    for i in range(len(rich)):
        flips = bytearray(rich)
        flips[i] ^= 0xFF
        inputs.append(bytes(flips))
        labels.append(f"flip {i}")
    targeted = []
    dup = bytearray(rich)
    spot = 240 + 3  # just after the option 53 item
    dup = dup[:spot] + bytes([53, 1, 2]) + dup[spot:]
    targeted.append(("option-53-inserted", bytes(dup)))
    biglen = bytearray(rich)
    biglen[244] = 250  # the option 55 length byte, now overrun
    targeted.append(("length-250", bytes(biglen)))
    answers_in, problems = ask_all([request(d) for d in inputs])
    tally.failures += problems
    for label, data, answer in zip(labels, inputs, answers_in):
        tally.check(bytes(data), answer, f"mutation {label}")
    answers_in, problems = ask_all([request(d) for _, d in targeted])
    tally.failures += problems
    for (label, data), answer in zip(targeted, answers_in):
        tally.check(data, answer, f"mutation targeted {label}")
    return tally


SCAPY_SCRIPT = r'''
import sys
from scapy.all import BOOTP, DHCP, raw

MAC = bytes([0x00, 0x0B, 0x82, 0x01, 0xFC, 0x42]) + bytes(10)

def build(**kw):
    try:
        return raw(BOOTP(**kw["bootp"]) / DHCP(options=kw["options"]))
    except Exception:
        return None

jobs = [
    dict(bootp=dict(op=1, htype=1, hlen=6, xid=0x11111111,
                    flags=0x8000, chaddr=MAC),
         options=[("message-type", "discover"),
                  ("param_req_list", [1, 3, 6, 15]), "end"]),
    dict(bootp=dict(op=2, htype=1, hlen=6, xid=0x11111111,
                    yiaddr="192.168.1.100", siaddr="192.168.1.1",
                    chaddr=MAC),
         options=[("message-type", "offer"),
                  ("subnet_mask", "255.255.255.0"),
                  ("lease_time", 3600), "end"]),
    dict(bootp=dict(op=1, htype=1, hlen=6, xid=0x11111112,
                    chaddr=MAC),
         options=[("message-type", "request"),
                  ("requested_addr", "192.168.1.100"),
                  ("server_id", "192.168.1.1"), "end"]),
    dict(bootp=dict(op=2, htype=1, hlen=6, xid=0x11111112,
                    yiaddr="192.168.1.100", siaddr="192.168.1.1",
                    chaddr=MAC),
         options=[("message-type", "ack"),
                  ("lease_time", 7200), "end"]),
    dict(bootp=dict(op=1, htype=1, hlen=6, xid=0x11111113,
                    ciaddr="192.168.1.100", chaddr=MAC),
         options=[("message-type", "release"),
                  ("server_id", "192.168.1.1"), "end"]),
    dict(bootp=dict(op=1, htype=1, hlen=6, xid=0x11111114,
                    ciaddr="192.168.1.100", chaddr=MAC),
         options=[("message-type", "inform"),
                  ("param_req_list", [1, 3, 6]), "end"]),
    dict(bootp=dict(op=2, htype=1, hlen=6, xid=0x11111115,
                    chaddr=MAC),
         options=[("message-type", "nak"), "end"]),
    dict(bootp=dict(op=1, htype=1, hlen=6, xid=0x11111116,
                    ciaddr="192.168.1.100", chaddr=MAC),
         options=[("message-type", "decline"),
                  ("requested_addr", "192.168.1.100"), "end"]),
    dict(bootp=dict(op=1, htype=1, hlen=6, xid=0x11111117,
                    hops=2, secs=11, chaddr=MAC),
         options=[("message-type", "discover"),
                  ("hostname", "client-7"),
                  ("param_req_list", [1, 3, 6, 15, 43]), "end"]),
    dict(bootp=dict(op=2, htype=1, hlen=6, xid=0x11111118,
                    yiaddr="10.0.0.7", siaddr="10.0.0.1",
                    giaddr="10.0.0.254", chaddr=MAC),
         options=[("message-type", "offer"),
                  ("router", "10.0.0.1"),
                  ("domain_name_server", "10.0.0.2"), "end"]),
]

import scapy
sys.stdout.write("version " + scapy.__version__ + "\n")
for job in jobs:
    pkt = build(**job)
    if pkt is not None:
        sys.stdout.write(pkt.hex() + "\n")
'''


SCAPY_FIXTURE = ROOT / "tests" / "scapy-packets.txt"


def build_scapy_packets():
    """Packets built by Scapy now, as (version, packets), or None
    when Scapy is reachable neither in this interpreter nor in
    the project venv at ../venv."""
    venv_python = ROOT / "venv" / "bin" / "python"
    for python in [sys.executable, str(venv_python)]:
        if python != sys.executable and not venv_python.exists():
            continue
        try:
            proc = subprocess.run(
                [python, "-c", SCAPY_SCRIPT],
                capture_output=True, text=True, timeout=300,
            )
        except OSError:
            continue
        lines = proc.stdout.split()
        if proc.returncode == 0 and len(lines) > 2 and lines[0] == "version":
            return lines[1], [bytes.fromhex(line) for line in lines[2:]]
    return None


def rebuild_scapy_fixture():
    built = build_scapy_packets()
    if built is None:
        print("Scapy is not reachable here; the fixture was not rebuilt")
        return 1
    version, pkts = built
    text = [
        f"# Built by Scapy {version} with its BOOTP and DHCP layers,",
        "# from the jobs in SCAPY_SCRIPT in tests/run_tests.py.",
        "# Rebuild with: python3 tests/run_tests.py --rebuild-scapy",
        f"scapy {version}",
    ] + [p.hex() for p in pkts]
    SCAPY_FIXTURE.write_text("\n".join(text) + "\n")
    print(f"wrote {len(pkts)} packets built by Scapy {version}")
    return 0


def scapy_fixture():
    """The packets Scapy built, as stored in the fixture, and the
    Scapy version that built them. Stored, so that every run
    feeds the tool the same inputs, with or without Scapy."""
    if not SCAPY_FIXTURE.is_file():
        return None, []
    version, pkts = None, []
    for line in SCAPY_FIXTURE.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        if line.startswith("scapy "):
            version = line.split()[1]
        else:
            pkts.append(bytes.fromhex(line))
    return version, pkts


def run_scapy():
    tally = Tally()
    version, pkts = scapy_fixture()
    tally.version = version
    if version is None or not pkts:
        tally.inputs += 1
        tally.failures.append(f"no Scapy packets in {SCAPY_FIXTURE.name}")
        return tally
    answers, problems = ask_all([request(d) for d in pkts])
    tally.failures += problems
    for i, (data, answer) in enumerate(zip(pkts, answers)):
        tally.check(data, answer, f"scapy {i}")
    return tally


MALFORMED = [
    "",
    "parse 1,,2",
    "parse 256",
    "parse -1",
    "parse 1.5",
    "parse x",
    "bogus 1",
    "parse 1 2",
    "parse  1",
    "parse 999999999999999999999",
    "parse 01x",
    "PARSE 1",
]


def run_malformed():
    tally = Tally()
    answers, problems = ask_all(MALFORMED)
    tally.failures += problems
    for line, answer in zip(MALFORMED, answers):
        tally.check_line(repr(line), answer, "error", "malformed")
    return tally


# ---------------------------------------------------------------- the
# Wireshark cross check (part 5): every message above, dissected by
# Wireshark's DHCP/BOOTP dissector through tshark, and compared with the
# tool's answer.
#
# Two accounts of each message meet here. Wireshark's own, read from
# tshark's JSON (ws_reading). And the harness's account of what that
# dissector does with the same bytes (WsModel): where it stops with an
# exception, which expert errors it reports, and why. The model follows
# the dissector's code in Wireshark 4.2.2 (epan/dissectors/packet-dhcp.c,
# and get_dns_name in packet-dns.c, at tag v4.2.2) and is computed from
# the message's bytes alone. It gives each difference its reason; it is
# not trusted on its own. A fault Wireshark reports that the model does
# not find in the message is a failure, and so is a fault the model
# finds that Wireshark does not report.

WS_BATCH = 500
# Ethernet (14 bytes), IPv4 (20) and UDP (8) come before the message
# in each frame, so a message byte at offset n is frame byte n + 42.
WS_PAYLOAD = 42
# The severity Wireshark gives an expert error (PI_ERROR). Notes and
# warnings are lower, and are not faults.
WS_ERROR = 0x00800000

# The fixed fields, with the offset and size SPEC.md gives each one:
# Wireshark must read each at the same place.
WS_FIXED = {
    "dhcp.type": ("op", 0, 1),
    "dhcp.hw.type": ("htype", 1, 1),
    "dhcp.hw.len": ("hlen", 2, 1),
    "dhcp.hops": ("hops", 3, 1),
    "dhcp.id": ("xid", 4, 4),
    "dhcp.secs": ("secs", 8, 2),
    "dhcp.flags": ("flags", 10, 2),
    "dhcp.ip.client": ("ciaddr", 12, 4),
    "dhcp.ip.your": ("yiaddr", 16, 4),
    "dhcp.ip.server": ("siaddr", 20, 4),
    "dhcp.ip.relay": ("giaddr", 24, 4),
    "dhcp.server": ("sname", 44, 64),
    "dhcp.file": ("file", 108, 128),
    "dhcp.cookie": ("cookie", 236, 4),
}
WS_CHADDR = ("dhcp.hw.mac_addr", "dhcp.hw.addr", "dhcp.hw.addr_padding")

# The named differences: each is a place where Wireshark 4.2 and
# SPEC.md read a message differently on purpose. A message is put
# under one only when the harness finds the reason in the message
# itself; any other difference is a failure.
WS_NAMED = {
    "no-end": (
        "the option area has no end byte: Wireshark reports the expert"
        " error End option missing (it does so when the message has an"
        " option 53), as RFC 2131 section 4.1 says the last option must"
        " be the end option; SPEC.md takes such a message (No end byte,"
        " under Readings that depart from the RFCs)"),
    "overload": (
        "option 52: Wireshark takes the byte after the length byte of"
        " the last option 52 (its first value byte) for the overload"
        " value; where its 2 bit (sname) or 1 bit (file) is set, it"
        " shows no sname or file text, and when the byte is 1, 2 or 3"
        " (the values RFC 2132 section 9.3 defines) it reads those"
        " fields as more options, with faults of their own (an option"
        " whose value fails its check, no end option in the field); an"
        " option 52 of length 0 as the last bytes of the message makes"
        " it read past the end; SPEC.md carries file and sname as bytes"
        " and option 52 as an ordinary option (Option overload is not"
        " read)"),
    "option-value": (
        "an option other than 53 whose value Wireshark checks against"
        " that option's own definition, and the value fails the check"
        " the harness applies (the length the definition needs, or the"
        " structure inside the value, as listed below): Wireshark"
        " reports an expert error, or stops with an exception (Malformed"
        " Packet) inside that option; SPEC.md carries every option but"
        " 53 as code and value bytes, unchecked (the slice boundary,"
        " under Option 53)"),
    "joined": (
        "options 119 or 120 more than once: Wireshark joins their values"
        " into one before reading them, as RFC 3396 asks, and the joined"
        " value fails its check; SPEC.md keeps each item as it stands"
        " (Repeated options are not joined)"),
    "hlen-0": (
        "hlen 0: Wireshark shows no client hardware address, only the"
        " note Client address not given; SPEC.md carries the 16 chaddr"
        " bytes as they stand, so there is nothing of Wireshark's to"
        " compare them with"),
    "secs-le": (
        "secs whose first byte is nonzero and second byte is 0:"
        " Wireshark takes the field for a little endian value, shows"
        " the bytes swapped, and adds the note Seconds elapsed appears"
        " to be encoded as little-endian; SPEC.md reads secs big"
        " endian, as RFC 2131 lays the field out, and the tool's secs"
        " with its two bytes swapped must be the value Wireshark"
        " shows"),
    "op": (
        "op is not 1 or 2: Wireshark shows the value and reports no"
        " error; SPEC.md turns the message away (The fixed fields)"),
    "hlen": (
        "hlen above 16: Wireshark shows no client hardware address and"
        " reports a note, not an error, except in a request (op 1)"
        " whose hlen bytes from offset 28 run past the end of the"
        " message, where it stops with an exception before it shows"
        " anything, as it reads them first; SPEC.md turns the message"
        " away (The fixed fields)"),
    "no-cookie": (
        "no DHCP cookie at offset 236: Wireshark reads the message as"
        " plain BOOTP (RFC 951), with a 64 byte vendor area at offset"
        " 236 and options after it, from offset 300, so a message"
        " shorter than 300 bytes ends inside that area (Malformed"
        " Packet), and any fault it finds in the options from offset"
        " 300 is its own; SPEC.md turns the message away (The fixed"
        " fields)"),
    "after-end": (
        "a nonzero byte after the end byte: Wireshark shows the bytes"
        " after the end option as padding and reports no error (RFC"
        " 2132 section 3.2 says only that they should be pad bytes);"
        " SPEC.md turns the message away (Bytes after the end byte)"),
    "no-53": (
        "no option 53: Wireshark reads a BOOTP message with vendor"
        " extensions (it marks it dhcp.bootp) and reports no error;"
        " SPEC.md turns the message away, as the plan requires option"
        " 53 (Option 53)"),
    "53-repeated": (
        "option 53 more than once: Wireshark reads each one and reports"
        " no error; SPEC.md turns the message away (Option 53: exactly"
        " once; Repeated options are not joined)"),
    "53-length": (
        "option 53 longer than one byte: Wireshark reads its first"
        " value byte as the type and reports no error; SPEC.md turns"
        " the message away (Option 53: length 1)"),
    "53-registered": (
        "option 53 value 9 to 18: Wireshark reads these registered"
        " types (Force Renew to TLS) and reports no error; SPEC.md"
        " refuses them on purpose (Message types 9 to 18 are refused"
        " on purpose)"),
    "53-unknown": (
        "option 53 value 0, or above 18: Wireshark shows Unknown"
        " Message Type and reports no error; SPEC.md turns the message"
        " away (Option 53: 1 to 8)"),
}
# The rules of SPEC.md at which Wireshark also faults a message, when
# its dissection gets there: a message the tool turns away for one of
# these agrees with Wireshark when Wireshark stops there.
WS_AGREE = {
    "short": "the message is shorter than the fixed fields and the"
             " cookie, and Wireshark stops with an exception before any"
             " option",
    "overrun": "an option runs past the end of the message, and"
               " Wireshark stops with an exception at that option",
    "code-last": "the last byte is an option code with no length byte,"
                 " and Wireshark stops with an exception there",
    "53-empty": "option 53 has length 0, and Wireshark stops with an"
                " exception reading the type byte",
}


# ---------------------------------------------------------------- the
# model: what Wireshark 4.2.2's dissector does with a message.

class WsStop(Exception):
    """The dissector stops with an exception, shown as Malformed
    Packet; `what` says why."""

    def __init__(self, what, reason=None):
        super().__init__(what)
        self.what = what
        self.reason = reason


def ws_need(value, end, what):
    """The dissector reads up to byte `end` of a value; past its end it
    stops with an exception."""
    if end > len(value):
        raise WsStop(what)


def ws_dns_name(buf, offset, max_len, base):
    """The bytes one DNS name takes, as get_dns_name in Wireshark
    4.2.2's packet-dns.c reads it from `buf` at `offset` (with its
    compression pointers counted from `base`); WsStop where it throws."""
    start, length, pointers = offset, -1, 0
    written, name_len, room = 0, 0, 255
    found = None  # a name Wireshark puts in place of the one it reads

    def get(i):
        if not 0 <= i < len(buf):
            raise WsStop("a domain name runs past the value")
        return buf[i]

    def put(count):
        nonlocal written, room
        if room > 0:
            written, room = (written + count, room - count) \
                if room >= count else (written, 0)

    while True:
        if max_len and offset - start > max_len - 1:
            break
        c = get(offset)
        offset += 1
        if c == 0:
            break
        if c & 0xC0 == 0x00:
            if written:
                if room > 0:
                    written, name_len, room = written + 1, name_len + 1, room - 1
            else:
                room -= 1
            while c > 0:
                if max_len and offset - start > max_len - 1:
                    raise WsStop("a domain name label runs past the room"
                                 " the name has")
                if room > 0:
                    get(offset)
                    written, name_len, room = written + 1, name_len + 1, room - 1
                c -= 1
                offset += 1
        elif c & 0xC0 == 0x40:
            if c & 0x3F != 0x01:
                found = "<Unknown extended label>"
                length = offset - start
                break
            bits = get(offset)
            offset += 1
            put(3)
            for _ in range(int((bits - 1) / 8) + 1):  # C division
                if room > 0:
                    get(offset)
                    put(2)
                offset += 1
            put(len(f"/{bits}]"))
        elif c & 0xC0 == 0x80:
            raise WsStop("a domain name label of the reserved type 0x80")
        else:
            target = base + (((c & 0x3F) << 8) | get(offset))
            offset += 1
            pointers += 1
            if length < 0:
                length = offset - start
            if target == offset + 2 or pointers > 255:
                found = "<Name contains a pointer that loops>"
                break
            offset = target
    if found is None and room <= 0:
        found = "<Name too long>"
    empty = found is None and written == 0
    if found is not None:
        name_len = len(found)
    if length < 0:
        length = offset - start
    if empty and length <= 2:
        return length
    if length < 2 or (length > 2 and name_len == 0):
        raise WsStop("a domain name Wireshark cannot read")
    return length


# Options Wireshark 4.2.2 reads with its basic types
# (DHCP_OPTION_BASICTYPE_RANGE and default_dhcp_opt in packet-dhcp.c),
# as (is or multiple, n, what): a value of exactly n bytes, or a whole
# number of n byte items. A value of another length draws the expert
# error dhcp.bad_length. The strings in that range have no check.
WS_BASIC = {}
for _c in (1, 16, 28, 32, 50, 54):
    WS_BASIC[_c] = ("is", 4, "an IPv4 address")
for _c in (2, 24, 35, 38, 51, 58, 59, 91, 153):
    WS_BASIC[_c] = ("is", 4, "a time in seconds")
for _c in (3, 4, 5, 6, 7, 8, 9, 10, 11, 41, 42, 44, 45, 48, 49, 65, 68,
           69, 70, 71, 72, 73, 74, 75, 76, 92, 112, 118, 136, 138, 142,
           150):
    WS_BASIC[_c] = ("multiple", 4, "IPv4 addresses")
for _c in (19, 20, 27, 29, 30, 31, 34, 36, 39, 157):
    WS_BASIC[_c] = ("is", 1, "a boolean")
for _c in (23, 37, 46, 116, 156):
    WS_BASIC[_c] = ("is", 1, "a byte")
for _c in (13, 22, 26, 57):
    WS_BASIC[_c] = ("is", 2, "a 16 bit number")
WS_BASIC[25] = ("multiple", 2, "16 bit numbers")
# Options whose own dissectors check only a length, the same way.
WS_BASIC[21] = ("multiple", 8, "address and mask pairs")
WS_BASIC[33] = ("multiple", 8, "address and router pairs")
WS_BASIC[85] = ("multiple", 4, "IPv4 addresses")
WS_BASIC[93] = ("multiple", 2, "16 bit architecture types")
for _c in (152, 154, 155, 159):
    WS_BASIC[_c] = ("is", 4, "a 4 byte value")


def ws_length(rule, n):
    """The fault a basic type finds in a value of length n, or None."""
    how, size, what = rule
    if how == "is" and n != size:
        return f"length other than {size} ({what})"
    if how == "multiple" and n % size:
        return f"length not a multiple of {size} ({what})"
    return None


# Option 63's sub-options with a basic type (o63_opt in packet-dhcp.c),
# and option 82's (o82_opt): 1 to 4 of option 63 are flags that must
# be empty.
WS_O63 = {1: ("is", 0, "a flag"), 2: ("is", 0, "a flag"),
          3: ("is", 0, "a flag"), 4: ("is", 0, "a flag"),
          5: ("is", 1, "a boolean"), 6: ("multiple", 4, "IPv4 addresses"),
          7: ("multiple", 4, "IPv4 addresses"), 8: ("is", 1, "a byte"),
          9: ("is", 1, "a byte"), 10: ("is", 1, "a boolean"),
          11: ("is", 4, "an IPv4 address")}
WS_O82 = {4: ("is", 4, "a 32 bit number"), 5: ("is", 4, "an IPv4 address"),
          10: ("is", 1, "a byte"), 11: ("is", 4, "an IPv4 address"),
          19: ("is", 2, "a 16 bit number"),
          150: ("is", 4, "an IPv4 address"),
          152: ("is", 4, "an IPv4 address")}


def ws_rule_61(v, m):
    # Client identifier: only type 255 (RFC 4361) is read further.
    n = len(v)
    if not n or v[0] != 255:
        return
    ws_need(v, 7, "type 255 with no room for its IAID and DUID type")
    duid = v[5] << 8 | v[6]
    if duid == 1 and n < 8:
        m.error("type 255 with a DUID-LLT shorter than its fields")
    elif duid == 1:
        ws_need(v, 13, "type 255 with a DUID-LLT that ends inside its fields")
    elif duid == 2:
        ws_need(v, 11, "type 255 with a DUID-EN that ends inside its fields")
    elif duid == 3:
        ws_need(v, 9, "type 255 with a DUID-LL that ends inside its fields")


def ws_rule_63(v, m):
    # NetWare/IP sub-options.
    off = 0
    while off < len(v):
        if off + 1 >= len(v):
            m.error("a sub-option with no length byte")
            return
        sub, ln = v[off], v[off + 1]
        ws_need(v, off + 2 + ln, "a sub-option runs past the value")
        fault = WS_O63.get(sub) and ws_length(WS_O63[sub], ln)
        if fault:
            m.error(f"sub-option {sub}: {fault}")
        off += 2 + ln


def ws_rule_77(v, m):
    # User class (RFC 3004), or Microsoft's form when the first byte is 0.
    n = len(v)
    if n < 2:
        return m.error("length below 2")
    if v[0] == 0:
        off = 2 + v[1]
        ws_need(v, off, "a Microsoft user class whose data runs past the value")
        off += (4 - v[1] % 4) & 3
        ws_need(v, off, "a Microsoft user class whose padding runs past the value")
        for _ in range(2):
            ws_need(v, off + 2, "a Microsoft user class with no room for a length")
            off += 2 + (v[off] << 8 | v[off + 1])
            ws_need(v, off, "a Microsoft user class whose text runs past the value")
        return
    off = 0
    while off < n and v[off] < n - off:  # longer ones are read as text
        if v[off] == 0:
            return m.error("a user class of length 0")
        off += 1 + v[off]


def ws_rule_78(v, m):
    # SLP directory agent (RFC 2610): a mandatory byte, then addresses.
    if not v:
        return m.error("length 0")
    off = 2 if v[0] == 0x80 and len(v) > 1 else 1
    if v[0] == 0x80 and len(v) == 1:
        return
    if (len(v) - off) % 4:
        m.error("addresses not a multiple of 4 bytes")


def ws_rule_81(v, m):
    # Client FQDN (RFC 4702): flags, two rcodes, then the name.
    if len(v) < 3:
        return m.error("length below 3")
    if len(v) > 3 and v[0] & 0x04:
        ws_dns_name(v, 3, len(v) - 3, 3)


def ws_rule_82(v, m):
    # Relay agent information (RFC 3046) sub-options.
    off = 0
    while off < len(v):
        if off + 1 >= len(v):
            return m.error("a sub-option with no length byte")
        sub, ln = v[off], v[off + 1]
        so, end = off + 2, off + 2 + ln
        if end > len(v):
            return m.error("a sub-option runs past the value")
        fault = WS_O82.get(sub) and ws_length(WS_O82[sub], ln)
        if fault:
            m.error(f"sub-option {sub}: {fault}")
        if sub == 13 and ln == 0:
            # o82_opt gives 13 the type bytes, so the length check in
            # its own case never runs; its field is a one byte number,
            # read here from 0 bytes (_ws.type_length.mismatch).
            m.error("sub-option 13: a number read from 0 bytes")
            raise WsStop("sub-option 13: a number read from 0 bytes")
        if sub == 16 and ln < 6:
            # A MAC address field read from fewer than 6 bytes.
            m.error("sub-option 16: a MAC address shorter than 6 bytes")
            raise WsStop("sub-option 16: a MAC address shorter than 6 bytes")
        while sub == 9 and so < end:
            ws_need(v, so + 5, "a vendor block runs past the value")
            if int.from_bytes(v[so:so + 4], "big") == 4491:
                return m.unfollowed("a CableLabs vendor block")
            ws_need(v, so + 5 + v[so + 4], "a vendor block runs past the value")
            so += 5 + v[so + 4]
        off = end


# Option 43 goes to the first of Wireshark's vendor-specific information
# readers (heuristic dissectors) that takes it. All but one take it by
# the vendor class (option 60) the first pass found, and are tried
# first; the model does not follow them. The last, Alcatel-Lucent's,
# takes it by its own bytes.
WS_VENDOR_CLASSES = (b"cisco", b"AEROHIVE", b"AAPLBSDPC", b"ArubaInstantAP",
                     b"ArubaAP", b"pktc", b"docsis", b"OpenCable2.0",
                     b"CableHome", b"RPD", b"RMD", b"ECM", b"PTA", b"DEMARC",
                     b"TR", b"SROUTER", b"PXEClient")


def ws_rule_43(v, m):
    # Vendor-specific information (RFC 2132 section 8.4).
    vc = m.vendor_class
    if vc is not None and vc.split(b"\0")[0].startswith(WS_VENDOR_CLASSES):
        return m.unfollowed("option 43 read for a vendor class (option 60)"
                            " Wireshark has its own reader for")
    if not v or v[0] not in (58, 64, 65, 66, 67):
        return
    # test_encapsulated_vendor_options: every sub-option fits, up to an
    # end byte (255); pad bytes (0) have no length byte.
    off = 0
    while off < len(v) and v[off] != 255:
        if v[off] == 0:
            off += 1
            continue
        if off + 1 >= len(v) or off + 2 + v[off + 1] > len(v):
            return
        off += 2 + v[off + 1]
    # Alcatel-Lucent's sub-options: the first one with an unknown code
    # or the wrong length draws an error and ends the option.
    sizes = {58: 2, 64: 4, 65: 4, 66: 1}
    off = 0
    while off < len(v) and v[off] != 255:
        sub = v[off]
        if sub == 0:
            off += 1
            continue
        if sub not in sizes and sub != 67:
            return m.error(f"Alcatel-Lucent sub-option {sub}: a code"
                           f" Wireshark does not know")
        if sub in sizes and v[off + 1] != sizes[sub]:
            return m.error(f"Alcatel-Lucent sub-option {sub}: length other"
                           f" than {sizes[sub]}")
        off += 2 + v[off + 1]


WS_PACKETCABLE = (b"pktc1.0:", b"pktc1.5:", b"pktc2.0:", b"docsis1.1:",
                  b"docsis2.0:", b"docsis3.0:")


def ws_rule_60(v, m):
    # Vendor class identifier: text, and PacketCable capabilities after
    # some vendor classes, which the model does not follow.
    if v.startswith(WS_PACKETCABLE):
        m.unfollowed("the PacketCable capabilities in option 60")


def ws_rule_83(v, m):
    # iSNS (RFC 4174): fixed fields, then addresses.
    n = len(v)
    if n < 14:
        return m.error("length below 14")
    off = 14
    if v[5] & 0x03 == 0x03:
        if n < 18:
            return m.error("heartbeat set and length below 18")
        off = 18
    if (n - off) % 4:
        m.error("secondary servers not a multiple of 4 bytes")


def ws_rule_90(v, m):
    # Authentication (RFC 3118).
    if len(v) < 11:
        return m.error("length below 11")
    if v[0] == 1 and v[1] == 1 and m.dhcp_type != 1 and len(v) - 11 < 20:
        m.error("delayed HMAC-MD5 authentication outside a DISCOVER with"
                " fewer than 20 bytes of secret id and hash")


def ws_rule_94(v, m):
    # Client network interface identifier (RFC 4578).
    ws_need(v, 1, "length 0")
    if v[0] == 1:
        ws_need(v, 3, "type 1 with no room for its version bytes")


def ws_rule_99(v, m):
    # Civic location (RFC 4776): what, country, then CAtype elements.
    off = 3
    while len(v) >= 3 and len(v) - off >= 2:
        off += 2 + v[off + 1]
        if off > len(v):
            return m.error("a civic address element runs past the value")


def ws_rule_117(v, m):
    # Name service search (RFC 2937): 16 bit option codes.
    if len(v) < 2:
        return m.error("length below 2")
    if len(v) % 2:
        return m.error("odd length")
    for i in range(0, len(v), 2):
        if v[i] << 8 | v[i + 1] not in (0, 6, 41, 44, 65):
            m.error("a name service other than 0, 6, 41, 44 and 65")


def ws_rule_121(v, m):
    # Classless static routes (RFC 3442), and Microsoft's option 249.
    if len(v) < 5:
        return m.error("length below 5")
    off = 0
    while off < len(v):
        if v[off] > 32:
            return m.error("a mask width above 32")
        # Its check for a route that runs past the value never fires
        # (tvb_reported_length_remaining is never below 0): it reads on.
        off += 1 + (v[off] + 7) // 8 + 4
        ws_need(v, off, "a route runs past the value")


def ws_rule_122(v, m):
    # CableLabs client configuration (RFC 3495), as
    # dissect_packetcable_ietf_ccc reads it under its default
    # preference (RFC 3495). Each sub-option is a code byte and a length
    # byte; what comes next depends on the code, and where the next
    # sub-option starts too. A check that fails ends the option with an
    # expert error (dhcp.missing_subopt_length or
    # dhcp.missing_subopt_value). It does not check a sub-option's
    # length against the value: where a code has no check, a read past
    # the value stops it with an exception, and a sub-option that runs
    # past the value ends the option.
    n, off = len(v), 0
    while off < n:
        code = v[off]
        if off + 1 >= n:
            return m.error("a sub-option with no length byte")
        ln, at = v[off + 1], off + 2
        if code in (1, 2):
            # Primary and secondary DHCP server: an IPv4 address.
            if at + 4 > n:
                return m.error(f"sub-option {code}: fewer than 4 value"
                               f" bytes left")
            off = at + ln
        elif code == 3:
            # Provisioning server: a type byte, then a domain name (0)
            # or an IPv4 address (1). It moves on by the length less 1,
            # from after the type byte.
            if at + 1 > n:
                return m.error("sub-option 3: no type byte left")
            kind, at = v[at], at + 1
            if kind == 0:
                ws_dns_name(v, at, ln, at)
            elif kind == 1 and at + 4 > n:
                return m.error("sub-option 3: fewer than 4 address bytes"
                               " left")
            off = at + ln - 1
        elif code == 4:
            # AS-REQ/AS-REP backoff and retry: 12 bytes.
            if at + 12 > n:
                return m.error("sub-option 4: fewer than 12 value bytes"
                               " left")
            off = at + ln
        elif code == 5:
            # AP-REQ/AP-REP backoff and retry: read only at length 12,
            # with no check first.
            if ln == 12:
                ws_need(v, at + 12, "sub-option 5: its 12 bytes run past"
                                    " the value")
            off = at + ln
        elif code == 6:
            # Kerberos realm: a domain name.
            ws_dns_name(v, at, ln, at)
            off = at + ln
        elif code in (7, 8):
            # Ticket control and provisioning timer: one byte, whatever
            # the length byte says.
            if at + 1 > n:
                return m.error(f"sub-option {code}: no value byte left")
            off = at + 1
        elif code == 9:
            # Security ticket control: 2 bytes.
            if at + 2 > n:
                return m.error("sub-option 9: fewer than 2 value bytes"
                               " left")
            off = at + ln
        else:
            off = at + ln


def ws_rule_123(v, m):
    # Coordinate based location (RFC 3825), or CableLabs DSS_IDs.
    n = len(v)
    if n == 16:
        return
    if n >= 69:
        return m.error("length 69 or more, and not 16")
    ws_need(v, 2, "a DSS_ID with no length byte")
    s = v[1]
    ws_need(v, 2 + s, "a DSS_ID runs past the value")
    if n > s + 2:
        ws_need(v, 4 + s, "a second DSS_ID with no length byte")
        # Wireshark 4.2.2 reads the second DSS_ID at 4 plus its own
        # length, not at 4 plus the first one's.
        ws_need(v, 4 + 2 * v[3 + s], "a second DSS_ID runs past the value")


def ws_rule_124(v, m):
    # Vendor-identifying vendor class (RFC 3925).
    n, off = len(v), 0
    if n == 1:
        return
    while n - off >= 5:
        dl = v[off + 4]
        off += 5
        end = off + dl
        # Its check for a block that runs past the value never fires
        # (tvb_reported_length_remaining is never below 0).
        while off < end:
            ws_need(v, off + dl, "a vendor class item runs past the value")
            dl = v[off]
            ws_need(v, off + 1 + dl, "a vendor class item runs past the value")
            off += 1 + dl
    if n - off:
        m.error("bytes left over, too few for an enterprise block")


def ws_rule_125(v, m):
    # Vendor-identifying vendor-specific information (RFC 3925).
    n, off = len(v), 0
    while n - off >= 5:
        ent, dl = int.from_bytes(v[off:off + 4], "big"), v[off + 4]
        off += 5
        end = off + dl
        # Its check for a block that runs past the value never fires
        # (tvb_reported_length_remaining is never below 0), so it reads
        # the block's sub-options up to `end`, wherever that is.
        if ent in (3561, 4491):
            return m.unfollowed(f"enterprise {ent}, which Wireshark reads"
                                f" with a dissector of its own")
        while off < end:
            ws_need(v, off + 1, "a sub-option runs past the value")
            if off + 1 >= end:
                m.error("a sub-option with no length byte")
                off = end
                continue
            ws_need(v, off + 2, "a sub-option runs past the value")
            if off + 2 + v[off + 1] > end:
                m.error("a sub-option runs past its enterprise block")
                off = end
                continue
            ws_need(v, off + 2 + v[off + 1], "a sub-option runs past the value")
            off += 2 + v[off + 1]
    if n - off > 0:
        m.error("bytes left over, too few for an enterprise block")


def ws_rule_146(v, m):
    # RDNSS selection (RFC 6731).
    if len(v) < 10:
        return m.error("length below 10")
    ws_dns_name(v, 9, len(v) - 9, 9)


def ws_rule_158(v, m):
    # PCP server (RFC 7291): lists of addresses.
    if len(v) < 5:
        return m.error("length below 5")
    off = 0
    while len(v) - off >= 5:
        ln = v[off]
        ws_need(v, off + ln, "a PCP server list runs past the value")
        off, got = off + 1, 1
        while (ln - 1) % 4 == 0 and got < ln and len(v) - off >= 4:
            off, got = off + 4, got + 4


def ws_rule_212(v, m):
    # 6RD (RFC 5969).
    if len(v) < 22:
        return m.error("length below 22")
    if (len(v) - 22) % 4:
        m.error("border relays not a multiple of 4 bytes")


WS_AVAYA = ("TLSSRVR=", "HTTPSRVR=", "HTTPDIR=", "STATIC=", "MCIPADD=",
            "DOT1X=", "ICMPDU=", "ICMPRED=", "L2Q=", "L2QVLAN=",
            "LOGLOCAL=", "PHY1STAT=", "PHY2STAT=", "PROCPSWD=",
            "PROCSTAT=", "SNMPADD=", "SNMPSTRING=", "VLANTEST=")


def ws_rule_242(v, m):
    # Avaya IP telephones: text up to the first zero byte, name=value
    # pairs split at commas.
    if len(v) < 5:
        return m.error("length below 5")
    # It reads the value as ASCII text (ENC_ASCII): a byte above 0x7F
    # becomes U+FFFD (3 bytes in UTF-8), and the text ends at the first
    # zero byte.
    text = "".join(chr(b) if b < 0x80 else "�"
                   for b in v.split(b"\0")[0])
    # wmem_strsplit gives no fields at all for empty text, so a value
    # that starts with a zero byte draws no error.
    if not text:
        return

    def number(s):
        # ws_strtoi32 (wsutil/strtoi.c): g_ascii_strtoll in base 10
        # (leading ASCII white space, a sign, digits) over the whole
        # text, and a value that fits in 32 bits.
        hit = re.fullmatch(r"[ \t\n\v\f\r]*([+-]?[0-9]+)", s)
        return bool(hit) and -2**31 <= int(hit.group(1)) < 2**31

    def check(p, at):
        # dissect_vendor_avaya_param gets the parameter's text and the
        # offset `at` it counts for it. Both are in bytes of the text in
        # UTF-8, where each U+FFFD takes 3 bytes, not the 1 byte of the
        # value it stands for.
        known = [k for k in WS_AVAYA if p.startswith(k) and len(p) > len(k)]
        if not known:
            m.error("a parameter Wireshark does not know")
        # Wireshark 4.2.2 flags L2QVLAN when its value is a number.
        elif known[-1] == "L2QVLAN=" and number(p[8:]):
            m.error("an L2QVLAN value")
        elif known[-1] == "VLANTEST=" and not number(p[9:]):
            m.error("a VLANTEST value that is not a 32 bit number")
        # The other parameters it knows hold text, which it adds with
        # proto_tree_add_string at (at, UTF-8 length): test_length
        # throws when that runs past the value. L2QVLAN and VLANTEST go
        # in with proto_tree_add_int, which does not check.
        elif known[-1] not in ("L2QVLAN=", "VLANTEST=") and (
                at + len(p.encode()) > len(v)):
            raise WsStop("a text parameter that, counted in UTF-8 bytes,"
                         " runs past the value")

    param, at = "", 0
    for field in text.split(","):
        if "=" in field:
            if param:
                check(param, at)
                at += len(param.encode()) + 1
            param = field
        elif param:
            param += "," + field
        else:
            return m.error("text before the first parameter")
    if param:
        check(param, at)


# The readers inside the dissector that the model does not follow (the
# rules above mark an option that reaches one: WsModel.unfollowed).
WS_UNFOLLOWED = (
    "option 43 when the vendor class (option 60) starts with "
    + ", ".join(c.decode() for c in WS_VENDOR_CLASSES[:-1])
    + f" or {WS_VENDOR_CLASSES[-1].decode()}",
    "option 60 when it starts with " + ", ".join(
        c.decode() for c in WS_PACKETCABLE[:-1])
    + f" or {WS_PACKETCABLE[-1].decode()} (PacketCable capabilities)",
    "option 82 sub-option 9, from a CableLabs vendor block"
    " (enterprise 4491) on",
    "option 125, from a block for enterprise 3561 or 4491 on",
)

WS_RULES = {
    43: ws_rule_43, 60: ws_rule_60, 61: ws_rule_61, 63: ws_rule_63,
    77: ws_rule_77, 78: ws_rule_78, 81: ws_rule_81, 82: ws_rule_82, 83: ws_rule_83, 90: ws_rule_90,
    94: ws_rule_94, 99: ws_rule_99, 117: ws_rule_117, 121: ws_rule_121,
    122: ws_rule_122, 123: ws_rule_123, 124: ws_rule_124,
    125: ws_rule_125, 146: ws_rule_146, 158: ws_rule_158,
    212: ws_rule_212, 242: ws_rule_242, 249: ws_rule_121,
    79: lambda v, m: ws_need(v, 1, "length 0"),
    151: lambda v, m: None if v else m.error("length 0"),
}


# Options built by hand to reach the edges of the rules above. Each was
# found where the model and Wireshark 4.2.2 once parted (in an
# adversarial check, a seed sweep or a fuzz run), or sits on one side
# of a boundary a rule follows. Each probe goes into a DISCOVER after
# option 53, then the end option, so the tool takes it, and part 5
# checks that the model finds the faults Wireshark reports there, no
# more and no fewer, as it does for every message.
WS_PROBES = [[(242, v)] for v in (
    # 242: length below 5; empty text (a zero byte first); text before
    # the first parameter, and after the last; parameters Wireshark
    # does not know; L2QVLAN and VLANTEST numbers as ws_strtoi32 reads
    # them.
    b"ABCD", b"\0ABCD", b"\0HTTPSRVR=1", b"abc,TLSSRVR=1",
    b"TLSSRVR=1,abc", b"FOO=1", b"TLSSRVR=", b"L2QVLAN=5", b"L2QVLAN=x",
    b"VLANTEST=5", b"VLANTEST=--5", b"VLANTEST=+5", b"VLANTEST= 5",
    b"VLANTEST=2147483647", b"VLANTEST=2147483648",
    b"VLANTEST=-2147483648", b"VLANTEST=-2147483649", b"VLANTEST=5x",
    # 242: a byte above 0x7F is U+FFFD, 3 bytes in UTF-8. A text
    # parameter counted that way must fit in the value, from the offset
    # Wireshark counts the same way (13 bytes do not hold
    # SNMPSTRING=\xe9, 14 do); L2QVLAN and VLANTEST are not checked.
    b"HTTPSRVR=\xff", b"TLSSRVR=\x80\x80\x80", b"STATIC=\x80\x80",
    b"TLSSRVR=a\x80,HTTPDIR=b", b"SNMPSTRING=\xe9\0", b"SNMPSTRING=\xe9\0\0",
    b"A=\x80\x80\x80,TLSSRVR=5", b"A=\x80\x80\x80,L2QVLAN=5",
    b"A=\x80\x80\x80,VLANTEST=x", b"VLANTEST=\xff", b"L2QVLAN=\xff\xff",
    b"TLSSRVR=1,\xff\0\0", b"TLSSRVR=1,\xff\0", b"STATIC=1,HTTPDIR=\xff\xff",
    b"TLSSRVR=1,HTTPDIR=\xff\0", b"TLSSRVR=1,HTTPDIR=\xff\0\0",
    b"Q=\xff\xff,MCIPADD=1.2.3.4\0\0\0\0", b"Q=\xff\xff,MCIPADD=1.2.3.4\0\0\0",
    b"Q=\xff\xff,MCIPADD=1.2.3.4",
    b"\xffAB=1", b"TLSSRVR=1\0\xff\xff", b"DOT1X=\xff\xff\0\0\0\0\0",
    b"DOT1X=\xff\xff\0\0\0",
)] + [[(122, bytes.fromhex(h))] for h in (
    # 122: each sub-option's own check; domain names in 3 (type 0) and
    # 6; the 12 byte read of 5 at length 12; 7 and 8 moving on one
    # byte; 3 moving on by its length less 1; an unknown code.
    "0a73", "0673", "01", "0104c0a80001", "0104c0a8", "0201",
    "030600036162630000", "030501c0a80001", "030501c0a8", "0300",
    "040c" + "00" * 12, "040c" + "00" * 8, "050c" + "00" * 12,
    "050c" + "00" * 8, "05040000", "0600", "06050361626300", "0700",
    "070005", "0800", "0902", "09020001", "0901", "070008010a00",
)] + [[(43, bytes.fromhex(h))] for h in (
    # 43 with no option 60: Alcatel-Lucent's reader takes it when its
    # first byte is 58 or 64 to 67 and every sub-option fits.
    "3a020001", "3a0100", "400400000001", "4003000000", "420101",
    "4203010203", "4303616263", "3a0200010700", "3a020001ff07",
    "3a050001", "39020001", "3a00", "003a020001", "003a0100",
    "41040a000001", "43003a0100",
)] + [
    # 43 with a vendor class Wireshark has no reader of its own for,
    # before it or after it.
    [(60, b"MSFT 5.0"), (43, b"\x3a\x01\x00")],
    [(43, b"\x3a\x01\x00"), (60, b"MSFT 5.0")],
    [(60, b"PXEClien"), (43, b"\x3a\x01\x00")],
    [(43, b"\x3a\x01\x00"), (60, b"PXEClien")],
] + [[(82, bytes.fromhex(h))] for h in (
    # 82: sub-option 13 (o82_opt gives it the type bytes) and 16.
    "0d00", "0d0105", "0d020005", "0d03000005", "01036162630d00",
    "1005" + "01" * 5, "1006" + "01" * 6,
)]


def probe_cases():
    f = fixed_bytes(1, 1, 6, 0, 0x12345678, 0, 0x8000,
                    0, 0, 0, 0, MAC, ZEROS64, ZEROS128)
    return [(" ".join(f"{c}={v.hex()}" for c, v in opts),
             f + COOKIE + option_area([(53, bytes([1]))] + opts))
            for opts in WS_PROBES]


def run_probes():
    tally = Tally()
    cases = probe_cases()
    answers, problems = ask_all([request(d) for _, d in cases])
    tally.failures += problems
    for (label, data), answer in zip(cases, answers):
        tally.check(data, answer, f"probe {label}")
    return tally


class WsItem:
    """One item of an option area: a run of pad bytes, the end option,
    or an option with its code, length and value. Both accounts use it:
    the model's, and Wireshark's as tshark shows it."""

    def __init__(self, offset, code, kind="option", length=None,
                 value=None, parent=None):
        self.offset = offset
        self.code = code
        self.kind = kind
        self.length = length
        self.value = value
        self.parent = parent  # the option whose tree holds this one
        self.type = None      # dhcp.option.dhcp: the message type
        self.unfollowed = None  # why the model does not follow its value

    def top(self):
        item = self
        while item.parent is not None:
            item = item.parent
        return item


class WsComposite:
    """The values of options 119 or 120 Wireshark joins (RFC 3396)."""

    def __init__(self, total):
        self.total = total  # the items the first pass counted
        self.index = 0
        self.value = None
        self.parts = 0


class WsModel:
    """What Wireshark 4.2.2's DHCP/BOOTP dissector does with one
    message, as dissect_dhcp in packet-dhcp.c runs: a first pass over
    the options for 52, 53, 119 and 120; the fixed fields; then the
    options, each through its own dissector."""

    def __init__(self, data):
        self.data = data
        n = len(data)
        self.cookie = n >= 240 and data[236:240] == COOKIE
        # Before it builds any tree, the dissector reads op, htype and
        # hlen, and for a request the hlen bytes of chaddr.
        self.dissected = n >= 3 and not (
            data[0] == 1 and data[2] and 28 + data[2] > n)
        self.fields = False      # the fixed fields are shown
        self.dhcp_type = None    # the type byte the first pass found
        self.overload = 0        # the overload byte the first pass found
        self.vendor_class = None  # the option 60 value the first pass found
        self.items = []          # every item, in the order shown
        self.top = []            # the items of the options field
        self.end = None          # offset of the end option there
        self.trailing = None     # the bytes shown after it
        self.faults = []         # (item or None, reason, what): errors
        # Where it stops with an exception: (item or None, reason,
        # what, whether inside the dissector of the item's option).
        self.stop = None
        self.current = None      # the option whose dissector runs
        self.reason = None       # the named difference for its faults
        try:
            self.run()
        except WsStop as e:
            self.stop = (self.items[-1] if self.items else None,
                         e.reason or self.reason, e.what, e.reason is None)

    def where(self, offset):
        """The named difference for a fault at `offset`, when where it
        is says it: the sname and file fields, read as options under
        option 52, or the options read after a BOOTP vendor area."""
        if offset is not None and offset < 236:
            return "overload"
        if not self.cookie:
            return "no-cookie"
        return None

    def error(self, what):
        item = self.current
        self.faults.append((item, self.where(item.offset) or self.reason, what))

    def unfollowed(self, what):
        self.current.unfollowed = what

    def run(self):
        data, n = self.data, len(self.data)
        if not n:
            return
        if not self.dissected:
            raise WsStop("it ends before the bytes the dissector reads"
                         " first: op, htype, hlen, and hlen bytes of"
                         " chaddr in a request",
                         "short" if n < 240 else "hlen")
        if n < 240:
            raise WsStop("the message ends inside the fixed fields and"
                         " cookie", "short")
        voff = 240 if self.cookie else 300
        # The first pass: option 52, option 53, and counts of 119 and 120.
        blocks = {119: 0, 120: 0}
        off = voff
        while off < n:
            c = data[off]
            if c == 0:
                while off < n and data[off] == 0:
                    off += 1
                continue
            if c == 255 or off + 1 >= n:
                break
            ln = data[off + 1]
            if off + 2 + ln <= n:
                if c in (52, 53) and off + 2 >= n:
                    raise WsStop(
                        f"option {c} of length 0 ends the message, and the"
                        f" first pass reads its value byte past the end",
                        self.where(None) or ("overload" if c == 52 else "53-empty"))
                if c == 52:
                    self.overload = data[off + 2]
                elif c == 53:
                    self.dhcp_type = data[off + 2]
                elif c == 60:
                    self.vendor_class = bytes(data[off + 2:off + 2 + ln])
                elif c in blocks:
                    blocks[c] += 1
            off += 2 + ln
        self.fields = True
        if not self.cookie and n < 300:
            raise WsStop("no cookie, and the message ends inside the 64"
                         " byte BOOTP vendor area", "no-cookie")
        self.composite = {c: WsComposite(t) for c, t in blocks.items()}
        at_end, off = self.area(voff, n, None, [self.overload])
        if at_end:
            self.end = off - 1
            if off < n:
                self.trailing = data[off:]
        elif self.dhcp_type is not None:
            self.faults.append((None, self.where(None) or "no-end",
                                "no end option"))

    def area(self, start, end, parent, cell):
        """The option loop of dissect_dhcp, or of an sname or file
        field read as options: items from `start` to `end`. Returns
        (at the end option, offset reached)."""
        data, n = self.data, len(self.data)
        off = start
        while off < end:
            c = data[off]
            if c == 0:
                i = off + 1
                while i < end and data[i] == 0:
                    i += 1
                self.add(WsItem(off, 0, "pad", i - off, parent=parent))
                off = i
                continue
            if c == 255:
                self.add(WsItem(off, 255, "end", parent=parent))
                return True, off + 1
            if off + 1 >= n:
                raise WsStop("an option code with no length byte",
                             self.where(off) or "code-last")
            ln = data[off + 1]
            item = WsItem(off, c, "option", ln, parent=parent)
            self.add(item)
            if off + 2 + ln > n:
                raise WsStop("an option runs past the end of the message",
                             self.where(off) or "overrun")
            item.value = bytes(data[off + 2:off + 2 + ln])
            self.current, self.reason = item, self.where(off) or "option-value"
            self.option(item, cell)
            off += 2 + ln
        return False, off

    def add(self, item):
        self.items.append(item)
        if item.parent is None:
            self.top.append(item)

    def option(self, item, cell):
        """What the dissector for the item's option code does."""
        c, v = item.code, item.value
        if c == 52:
            if not v:
                return self.error("length 0")
            if 1 <= cell[0] <= 3:
                for bit, name, lo, hi in ((2, "sname", 44, 108),
                                          (1, "file", 108, 236)):
                    if v[0] & bit:
                        for comp in self.composite.values():
                            comp.index = 0
                        at_end, _ = self.area(lo, hi, item, [0])
                        self.current, self.reason = item, "overload"
                        if not at_end:
                            self.error(f"no end option in {name} read as"
                                       f" options")
                cell[0] = 0
        elif c == 53:
            self.reason = self.where(item.offset) or "53-empty"
            ws_need(v, 1, "option 53 of length 0")
        elif c in (119, 120):
            self.joined_option(item)
        elif c in WS_BASIC:
            fault = ws_length(WS_BASIC[c], len(v))
            if fault:
                self.error(fault)
        elif c in WS_RULES:
            WS_RULES[c](v, self)

    def joined_option(self, item):
        """Options 119 and 120: Wireshark joins their values (RFC 3396)
        and reads the joined value at the last one the first pass
        counted."""
        comp, v = self.composite[item.code], item.value
        comp.index += 1
        if v:
            comp.value = (comp.value or b"") + v
            comp.parts += 1
        if comp.index != comp.total or comp.value is None:
            return
        whole = comp.value
        if comp.parts > 1:
            self.reason = self.where(item.offset) or "joined"
        if item.code == 119:
            off = 0
            while off < len(whole):
                off += ws_dns_name(whole, off, len(whole), 0)
            comp.value = None
        elif whole[0] == 0 and len(whole) < 3:
            self.error("a domain name list shorter than 3 bytes")
        elif whole[0] == 0:
            off = 1
            while off < len(whole):
                off += ws_dns_name(whole, off, len(whole), 1)
            comp.value = None
        elif whole[0] == 1 and len(whole) < 5:
            self.error("addresses: length below 5")
        elif whole[0] == 1 and (len(whole) - 1) % 4:
            self.error("addresses not a multiple of 4 bytes")
        elif whole[0] > 1:
            self.error("an encoding byte other than 0 and 1")


# ---------------------------------------------------------------- the
# Wireshark side: tshark's JSON, read back.

def ip_checksum(header):
    total = sum(int.from_bytes(header[i:i + 2], "big")
                for i in range(0, len(header), 2))
    while total >> 16:
        total = (total & 0xFFFF) + (total >> 16)
    return (~total) & 0xFFFF


def udp_frame(payload):
    """An Ethernet/IPv4/UDP frame carrying `payload`: from the client
    port 68 to the server port 67, or from 67 to 68 when the message's
    op byte says it is a reply (2). The UDP checksum is 0, "none"."""
    sport, dport = (67, 68) if payload[:1] == b"\x02" else (68, 67)
    udp = struct.pack("!HHHH", sport, dport, 8 + len(payload), 0) + payload
    ip = bytearray(struct.pack("!BBHHHBBH4s4s", 0x45, 0, 20 + len(udp),
                               0, 0, 64, 17, 0, bytes(4), b"\xff" * 4))
    ip[10:12] = ip_checksum(ip).to_bytes(2, "big")
    eth = b"\xff" * 6 + MAC[:6] + b"\x08\x00"
    return eth + bytes(ip) + udp


def write_pcap(path, payloads):
    """A classic pcap file (link type 1, Ethernet), one frame for each
    payload, a second apart."""
    out = bytearray(struct.pack("<IHHiIII", 0xA1B2C3D4, 2, 4, 0, 0,
                                65535, 1))
    for i, payload in enumerate(payloads):
        frame = udp_frame(payload)
        out += struct.pack("<IIII", i, 0, len(frame), len(frame)) + frame
    path.write_bytes(bytes(out))


class WsObj(list):
    """A JSON object from tshark, kept as its (key, value) pairs in
    order: tshark writes a key once for each option, so a dict would
    keep only the last one."""


def tshark_version(tshark):
    try:
        out = subprocess.run([tshark, "--version"], capture_output=True,
                             text=True, timeout=120).stdout
    except (OSError, subprocess.TimeoutExpired):
        return None
    lines = out.strip().splitlines()
    return lines[0].rstrip(".") if lines else None


def run_tshark(tshark, payloads, workdir):
    """Wireshark's dissection of each payload, as each frame's layers
    (a WsObj), and a problem or None. tshark runs with an empty
    personal configuration directory, so no saved preference of
    whoever runs the tests changes the dissection."""
    pcap = workdir / "messages.pcap"
    write_pcap(pcap, payloads)
    env = dict(os.environ)
    env["WIRESHARK_CONFIG_DIR"] = str(workdir / "config")
    try:
        proc = subprocess.run(
            [tshark, "-n", "-r", str(pcap), "-T", "json", "-x"],
            capture_output=True, timeout=TIMEOUT, env=env)
    except (OSError, subprocess.TimeoutExpired) as e:
        return None, f"tshark did not run: {e}"
    if proc.returncode != 0:
        tail = " / ".join(proc.stderr.decode("utf-8", "replace")
                          .strip().splitlines()[-2:])
        return None, f"tshark exit status {proc.returncode}: {tail}"
    try:
        frames = json.loads(proc.stdout.decode("utf-8", "replace"),
                            object_pairs_hook=WsObj)
    except ValueError as e:
        return None, f"tshark wrote no JSON: {e}"
    if len(frames) != len(payloads):
        return None, (f"tshark gave {len(frames)} frames for"
                      f" {len(payloads)} messages")
    layers = []
    for frame in frames:
        source = dict(frame).get("_source") if isinstance(frame, WsObj) else None
        got = dict(source).get("layers") if isinstance(source, WsObj) else None
        layers.append(got if isinstance(got, WsObj) else None)
    return layers, None


def ws_hex(raw):
    """The bytes of a field's raw entry from `tshark -x`, a list of
    the hex, the frame offset, the length and more, or None. When a
    field runs past the frame, tshark writes a note, not hex."""
    if not isinstance(raw, list) or not raw or not isinstance(raw[0], str):
        return None
    try:
        return bytes.fromhex(raw[0])
    except ValueError:
        return None


def ws_offset(raw):
    """The message offset of a field's raw entry, or None."""
    if isinstance(raw, list) and len(raw) > 1 and isinstance(raw[1], int):
        return raw[1] - WS_PAYLOAD
    return None


class WsReading:
    """What Wireshark read in one frame."""

    def __init__(self):
        self.dissected = False   # a dhcp layer is there
        self.malformed = False   # Malformed Packet: an exception
        self.errors = []         # expert errors: (option item, key, message)
        self.notes = set()       # the key of every expert item, any severity
        self.frame_problems = []  # anything wrong outside the message
        self.fields = {}         # field: (shown value, raw bytes, offset, size)
        self.items = []          # option items of the options field
        self.all = []            # every option item, nested ones too
        self.trailing = None     # the padding shown after the end option
        self.bootp = False       # marked plain BOOTP, no message type


def ws_expert(obj):
    pairs = dict(obj)
    names = [k for k, _ in obj if not k.startswith("_ws.expert")]
    try:
        severity = int(pairs.get("_ws.expert.severity", "0"))
    except ValueError:
        severity = 0
    return (names[0] if names else "?",
            str(pairs.get("_ws.expert.message", "")), severity)


def ws_walk(obj, reading, owner):
    """Read a dhcp tree, or a subtree of it, in order. `owner` is the
    option item whose tree this is, or None at the top."""
    raws = {}
    item = None
    for key, value in obj:
        if key.endswith("_raw"):
            raws[key[:-4]] = value
            continue
        raw = raws.get(key)
        if key == "_ws.expert" and isinstance(value, WsObj):
            name, message, severity = ws_expert(value)
            reading.notes.add(name)
            if severity >= WS_ERROR:
                reading.errors.append((owner, name, message))
        elif key == "dhcp.option.type":
            hexed = ws_hex(raw)
            try:
                # The code byte; Wireshark shows 0 for the end option, so
                # the raw bytes say it better when they are there.
                code = hexed[0] if hexed else int(value)
            except (TypeError, ValueError):
                code = None
            item = WsItem(ws_offset(raw), code, parent=owner)
            (reading.items if owner is None else []).append(item)
            reading.all.append(item)
        elif key == "dhcp.option.type_tree" and isinstance(value, WsObj):
            if item is None:
                reading.frame_problems.append("an option tree with no option")
                continue
            parts = dict(value)
            if "dhcp.option.padding" in parts:
                item.kind = "pad"
            elif "dhcp.option.end" in parts:
                item.kind = "end"
            try:
                if "dhcp.option.length" in parts:
                    item.length = int(parts["dhcp.option.length"])
                item.value = ws_hex(parts.get("dhcp.option.value_raw"))
                if item.value is None and item.length == 0:
                    # No value field for an empty value: Wireshark
                    # reads the length 0 and nothing after it.
                    item.value = b""
                if "dhcp.option.dhcp" in parts:
                    item.type = int(parts["dhcp.option.dhcp"])
            except (TypeError, ValueError):
                reading.frame_problems.append("an option Wireshark shows"
                                              " in a form the harness"
                                              " cannot read")
            ws_walk(value, reading, item)
        elif owner is None and (key in WS_FIXED or key in WS_CHADDR):
            if key not in reading.fields and ws_hex(raw) is not None:
                reading.fields[key] = (value, ws_hex(raw), ws_offset(raw),
                                       raw[2])
        elif owner is None and key == "dhcp.option.padding":
            reading.trailing = ws_hex(raw)
        elif owner is None and key == "dhcp.bootp":
            reading.bootp = True
        elif isinstance(value, WsObj):
            ws_walk(value, reading, owner)


def ws_experts_in(obj):
    found = []
    for key, value in obj:
        if key == "_ws.expert" and isinstance(value, WsObj):
            found.append(ws_expert(value)[1])
        elif isinstance(value, WsObj):
            found += ws_experts_in(value)
    return found


def ws_reading(layers):
    reading = WsReading()
    if layers is None:
        reading.frame_problems.append("no dissection of this frame")
        return reading
    names = [key for key, _ in layers if not key.endswith("_raw")]
    if names[:4] != ["frame", "eth", "ip", "udp"]:
        reading.frame_problems.append(f"layers {names}")
    for key, value in layers:
        if key.endswith("_raw"):
            continue
        if key == "dhcp":
            reading.dissected = True
            if isinstance(value, WsObj):
                ws_walk(value, reading, None)
        elif key == "_ws.malformed":
            reading.malformed = True
        elif key.startswith("_ws."):
            reading.frame_problems.append(key)
        elif isinstance(value, WsObj):
            reading.frame_problems += [f"{key}: {m}"
                                       for m in ws_experts_in(value)]
    return reading


# ---------------------------------------------------------------- the
# comparison.

def read_area(data):
    """The options of a message's option area as the rules of SPEC.md
    read them; the offset of the end byte, or None when there is
    none; and the first rule of the option area it breaks, or None.
    Like oracle_parse, but going on to say why."""
    options = []
    i = 240
    while i < len(data):
        b = data[i]
        if b == 0:
            i += 1
            continue
        if b == 255:
            return options, i, ("after-end" if any(data[i + 1:]) else None)
        if i + 1 >= len(data):
            return options, None, "code-last"
        ln = data[i + 1]
        if i + 2 + ln > len(data):
            return options, None, "overrun"
        options.append((b, bytes(data[i + 2:i + 2 + ln])))
        i += 2 + ln
    return options, None, None


def input_breaks(data):
    """The rules of SPEC.md a message breaks, found from its bytes: the
    fixed fields, and then, when the cookie is there, the option area
    and option 53."""
    if len(data) < 240:
        return ["short"]
    out = []
    if data[0] not in (1, 2):
        out.append("op")
    if data[2] > 16:
        out.append("hlen")
    if data[236:240] != COOKIE:
        return out + ["no-cookie"]
    options, _, area = read_area(data)
    if area:
        out.append(area)
    types = [v for c, v in options if c == 53]
    if not types:
        out.append("no-53")
    if len(types) > 1:
        out.append("53-repeated")
    for v in types:
        if not v:
            out.append("53-empty")
            continue
        if len(v) > 1:
            out.append("53-length")
        if 9 <= v[0] <= 18:
            out.append("53-registered")
        elif not 1 <= v[0] <= 8:
            out.append("53-unknown")
    return list(dict.fromkeys(out))


def tool_reading(answer):
    """The fields and options of the tool's reprint. The reprint has
    passed reprint_problem, so it is in canonical form."""
    data = bytes(int(x) for x in answer[3:].split(","))

    def word(a, b):
        return int.from_bytes(data[a:b], "big")

    got = {
        "op": data[0], "htype": data[1], "hlen": data[2], "hops": data[3],
        "xid": word(4, 8), "secs": word(8, 10), "flags": word(10, 12),
        "ciaddr": word(12, 16), "yiaddr": word(16, 20),
        "siaddr": word(20, 24), "giaddr": word(24, 28),
        "chaddr": data[28:44], "sname": data[44:108],
        "file": data[108:236], "cookie": data[236:240],
    }
    options = []
    i = 240
    while data[i] != 255:
        options.append((data[i], data[i + 2:i + 2 + data[i + 1]]))
        i += 2 + data[i + 1]
    got["options"] = options
    got["type"] = [v[0] for c, v in options if c == 53][0]
    return got


def ws_text(raw):
    """The text Wireshark shows for an sname or file field: the bytes
    before the first zero byte, as ASCII, with each byte above 127
    shown as U+FFFD."""
    return "".join(chr(b) if b < 0x80 else "�"
                   for b in raw.split(b"\0")[0])


def ws_shown(key, shown):
    """A fixed field's value as Wireshark shows it, as an int or bytes."""
    if key in ("dhcp.server", "dhcp.file"):
        return shown
    if key.startswith("dhcp.ip.") or key == "dhcp.cookie":
        quad = bytes(int(p) for p in shown.split("."))
        return quad if key == "dhcp.cookie" else int.from_bytes(quad, "big")
    return int(shown, 0)


class WsVerdict:
    """The outcome for one message: how it agrees (or None), the named
    differences found, as {name: {what}}, and the failures."""

    def __init__(self):
        self.agreed = None
        self.named = {}
        self.fails = []

    def name(self, key, what=None):
        self.named.setdefault(key, set())
        if what:
            self.named[key].add(what)


def ws_faults(model, ws, out):
    """Match each fault Wireshark reports with one the model finds in
    the message, and the other way round. A matched fault puts the
    message under the model's reason for it."""
    if ws.frame_problems:
        out.fails += [f"frame: {p}" for p in ws.frame_problems]
    if model.dissected != ws.dissected:
        out.fails.append(f"Wireshark {'dissects' if ws.dissected else 'does not dissect'}"
                         f" it as BOOTP, the model says otherwise")
        return
    items = {it.offset: it for it in model.items}

    def unknown(at):
        item = items.get(at)
        if item is not None and item.top().unfollowed:
            return f" (the harness does not follow {item.top().unfollowed})"
        return ""

    # The exception: there or not, and where.
    stop = model.stop
    last = ws.all[-1] if ws.all else None
    if ws.malformed and stop is None:
        at = last.offset if last else None
        out.fails.append(f"Wireshark: Malformed Packet after the item at"
                         f" {at}, which the model does not find in the"
                         f" message{unknown(at)}")
    elif stop is not None and not ws.malformed:
        out.fails.append(f"the model finds an exception ({stop[2]})"
                         f" Wireshark does not raise")
    elif stop is not None:
        mine = (stop[0].offset, stop[0].code) if stop[0] else None
        theirs = (last.offset, last.code) if last else None
        if mine != theirs:
            out.fails.append(f"Wireshark stops after the item {theirs},"
                             f" the model after {mine}"
                             f"{unknown(last.offset if last else None)}")
        else:
            out.name(stop[1], ws_why(stop[0] if stop[3] else None, stop[2]))
    # The expert errors, item by item.
    mine, theirs = {}, {}
    for item, reason, what in model.faults:
        mine.setdefault(item.offset if item else None, []).append(
            (item, reason, what))
    for owner, key, message in ws.errors:
        theirs.setdefault(owner.offset if owner else None, []).append(
            (key, message))
    reached = {it.offset for it in ws.all} | {None}
    for at in sorted(set(mine) | set(theirs), key=lambda x: -1 if x is None else x):
        got, want = theirs.get(at, []), mine.get(at, [])
        if got and not want:
            out.fails += [f"Wireshark: {m} ({k}) in the item at {at}, a"
                          f" fault the model does not find in the"
                          f" message{unknown(at)}" for k, m in got]
        elif want and not got and at in reached:
            out.fails += [f"the model finds {w} in the item at {at},"
                          f" Wireshark reports no error there"
                          for _, _, w in want]
        elif got and len(got) != len(want):
            out.fails.append(f"in the item at {at}: Wireshark reports"
                             f" {len(got)} errors, the model finds {len(want)}")
        elif got:
            for it, reason, what in want:
                out.name(reason, ws_why(it, what))


def ws_why(item, what):
    """A fault as the record lists it: the option code, then what the
    harness found."""
    return f"{item.code}: {what}" if item is not None else what


def ws_taken(data, tool, model, ws):
    """Compare a message the tool takes with Wireshark's reading of it."""
    out = WsVerdict()
    ws_faults(model, ws, out)
    if not ws.dissected or out.fails:
        return out
    for name in [r for r in out.named if r in WS_AGREE]:
        out.fails.append(f"the model finds {name}, a rule SPEC.md turns"
                         f" a message away for, in a message the tool takes")
    if not model.fields:
        # Wireshark stopped in its first pass, before any field.
        if ws.fields or ws.all:
            out.fails.append("Wireshark shows fields the model says it"
                             " does not reach")
        return out
    ours = tool["options"]
    ov = model.overload
    # The fixed fields: the value Wireshark shows, and where it read it.
    for key, (name, offset, size) in WS_FIXED.items():
        want = tool[name]
        if (key == "dhcp.server" and ov & 2) or (key == "dhcp.file" and ov & 1):
            if key in ws.fields:
                out.fails.append(f"{name}: Wireshark shows it, though"
                                 f" option 52 says it carries options")
            else:
                out.name("overload", f"{name} not shown")
            continue
        if key not in ws.fields:
            out.fails.append(f"{name}: Wireshark shows no {key}")
            continue
        shown, raw, at, n = ws.fields[key]
        if (at, n) != (offset, size):
            out.fails.append(f"{name}: Wireshark reads {n} bytes at {at},"
                             f" SPEC.md has {size} at {offset}")
        try:
            value = ws_shown(key, shown)
        except ValueError:
            out.fails.append(f"{name}: Wireshark shows {shown!r}")
            continue
        if name in ("sname", "file"):
            if raw != want or value != ws_text(want):
                out.fails.append(f"{name}: Wireshark {shown[:40]!r},"
                                 f" the tool {want.hex()[:40]}")
        elif (name == "secs" and data[8] and not data[9]
              and value == data[8] and "dhcp.secs_le" in ws.notes):
            # Wireshark shows the two bytes swapped: the tool's secs,
            # swapped, must be what it shows.
            if ((want & 0xFF) << 8 | want >> 8) == value:
                out.name("secs-le")
            else:
                out.fails.append(f"secs: Wireshark {shown} (the bytes"
                                 f" swapped), the tool {want!r}")
        elif value != want:
            out.fails.append(f"{name}: Wireshark {shown}, the tool {want!r}")
    # chaddr: the address Wireshark shows, then its padding.
    addr = ws.fields.get("dhcp.hw.mac_addr") or ws.fields.get("dhcp.hw.addr")
    pad = ws.fields.get("dhcp.hw.addr_padding")
    if addr is None and pad is None:
        if tool["hlen"] == 0 and "dhcp.client_address_not_given" in ws.notes:
            out.name("hlen-0")
        else:
            out.fails.append("chaddr: Wireshark shows none")
    else:
        try:
            a = bytes.fromhex(addr[0].replace(":", "")) if addr else b""
            p = bytes.fromhex(pad[0].replace(":", "")) if pad else b""
        except ValueError:
            a, p = None, None
        chaddr = tool["chaddr"]
        if (a is None or a != chaddr[:len(a)] or (p and p != chaddr[16 - len(p):])
                or len(a) + len(p) < 16 or (addr and addr[2] != 28)):
            out.fails.append(f"chaddr: Wireshark {addr and addr[0]} padding"
                             f" {pad and pad[0]}, the tool {chaddr.hex()}")
    # The options: code, length and value, in order. Where Wireshark
    # stops with an exception, it shows those before it, as the model
    # says.
    theirs = [it for it in ws.items if it.kind == "option"]
    want = len([it for it in model.top if it.kind == "option"])
    if len(theirs) != (want if ws.malformed else len(ours)) or len(theirs) > len(ours):
        out.fails.append(f"Wireshark reads {len(theirs)} options, the tool"
                         f" {len(ours)}")
    for k, (it, (code, value)) in enumerate(zip(theirs, ours)):
        if it.code != code or it.length != len(value) or it.value != value:
            out.fails.append(f"option {k}: Wireshark code {it.code} length"
                             f" {it.length} value {it.value and it.value.hex()},"
                             f" the tool code {code} value {value.hex()}")
    if not ws.malformed:
        ends = [it for it in ws.items if it.kind == "end"]
        if len(ends) != (0 if model.end is None else 1):
            out.fails.append(f"Wireshark reads {len(ends)} end options")
        if ws.trailing != model.trailing:
            out.fails.append("Wireshark shows other bytes after the end")
    # The message type.
    types = [it.type for it in theirs if it.code == 53]
    if types and types[0] != tool["type"]:
        out.fails.append(f"type: Wireshark {types[0]}, the tool {tool['type']}")
    elif not types and not ws.malformed:
        out.fails.append("type: Wireshark shows none")
    return out


def ws_refused(data, model, ws):
    """Compare a message the tool turns away with Wireshark's reading
    of it."""
    out = WsVerdict()
    breaks = input_breaks(data)
    if not breaks:
        out.fails.append("the harness finds no rule this message breaks")
        return out
    if not data:
        if ws.dissected:
            out.fails.append("Wireshark dissects an empty payload")
        out.agreed = "empty"
        return out
    ws_faults(model, ws, out)
    if out.fails:
        return out
    # Agreement: Wireshark stops at a rule the tool turns it away for.
    stop = model.stop[1] if model.stop else None
    if stop in WS_AGREE:
        if stop not in breaks:
            out.fails.append(f"the model finds {stop}, which the harness's"
                             f" reading of SPEC.md does not")
            return out
        out.agreed = stop
        del out.named[stop]
        return out
    # Otherwise each rule broken is a named difference, shown in
    # Wireshark's own reading where its dissection reaches it.
    out.fails += ws_confirm(data, breaks, model, ws, out)
    if not out.named and not out.fails:
        out.fails.append("Wireshark reports no fault, and the harness"
                         " confirms no rule it breaks in Wireshark's reading")
    return out


def ws_confirm(data, breaks, model, ws, out):
    """For a message the tool turns away and Wireshark does not stop at
    any rule it breaks: for each rule Wireshark's dissection reaches,
    check that its reading shows what the harness found, and name it.
    Returns failures."""
    fails = []
    stopped = model.stop is not None

    def shown(key):
        try:
            return ws_shown(key, ws.fields[key][0])
        except (KeyError, ValueError):
            return None

    for b in breaks:
        if b in WS_AGREE:
            # Wireshark stops before it gets there, or it would agree.
            if not stopped:
                fails.append(f"Wireshark reports no fault at {b}")
            continue
        if not model.fields:
            continue  # Wireshark stops before it shows any field
        if b == "op":
            if shown("dhcp.type") != data[0]:
                fails.append(f"op: Wireshark {shown('dhcp.type')}, the"
                             f" message {data[0]}")
                continue
        elif b == "hlen":
            if shown("dhcp.hw.len") != data[2] or any(
                    k in ws.fields for k in WS_CHADDR):
                fails.append("hlen: Wireshark shows another hlen, or a"
                             " hardware address")
                continue
        elif b == "no-cookie":
            if "dhcp.cookie" in ws.fields:
                fails.append("Wireshark shows a cookie the harness does"
                             " not find")
                continue
        elif b == "no-53":
            if not ws.bootp:
                fails.append("Wireshark does not mark a message with no"
                             " option 53 as plain BOOTP")
                continue
        elif stopped:
            continue  # Wireshark stops before the end of the options
        elif b == "after-end":
            end = read_area(data)[1]
            if model.end != end or ws.trailing != data[end + 1:]:
                fails.append("Wireshark shows other bytes after the end"
                             " option")
                continue
        elif b.startswith("53-"):
            options = read_area(data)[0]
            ours = [(len(v), v[0]) for c, v in options if c == 53 and v]
            theirs = [(it.length, it.type) for it in ws.items
                      if it.kind == "option" and it.code == 53]
            if theirs != ours:
                fails.append(f"option 53: Wireshark reads {theirs}, the"
                             f" message holds {ours}")
                continue
        else:
            fails.append(f"the harness has no way to confirm {b}")
            continue
        out.name(b)
    return fails


class WsResult:
    def __init__(self):
        self.version = None
        self.reason = None     # why the cross check did not run
        self.rows = []         # (part, messages, agreed, named, failed)
        self.failures = []
        self.named = {}        # named difference: messages
        self.whys = {}         # (named difference, what): messages
        self.taken = {"agreed": 0, "named": 0, "failed": 0}
        self.refused = {}      # the rule Wireshark agrees at: messages
        self.refused_named = 0
        self.refused_failed = 0
        self.exact = 0         # faults matched both ways

    @property
    def messages(self):
        return sum(r[1] for r in self.rows)


def run_wireshark(parts, require):
    """Part 5: dissect every message the other parts fed the tool with
    Wireshark's DHCP/BOOTP dissector, and compare."""
    result = WsResult()
    tshark = shutil.which("tshark")
    if tshark is None:
        result.reason = "tshark is not on PATH"
        if require:
            result.failures.append("wireshark: tshark is not on PATH")
        return result
    result.version = tshark_version(tshark) or "tshark, version unknown"
    entries = [(name, label, data, answer) for name, t in parts
               for label, data, answer in getattr(t, "messages", [])]
    readings = []
    with tempfile.TemporaryDirectory() as tmp:
        workdir = Path(tmp)
        (workdir / "config").mkdir()
        for i in range(0, len(entries), WS_BATCH):
            batch = entries[i:i + WS_BATCH]
            layers, problem = run_tshark(
                tshark, [data for _, _, data, _ in batch], workdir)
            if problem:
                result.failures.append(f"wireshark: {problem}")
                layers = [None] * len(batch)
            readings += layers
    rows = {}
    for (name, label, data, answer), layers in zip(entries, readings):
        row = rows.setdefault(name, [0, 0, 0, 0])
        row[0] += 1
        ws = ws_reading(layers)
        model = WsModel(data)
        if answer == "none":
            out = ws_refused(data, model, ws)
        elif isinstance(answer, str) and reprint_problem(answer) is None \
                and answer.startswith("ok:"):
            out = ws_taken(data, tool_reading(answer), model, ws)
        else:
            out = WsVerdict()
            out.fails.append("the tool gave no answer to compare")
        if out.fails:
            row[3] += 1
            result.failures += [f"wireshark {label}: {f}" for f in out.fails]
        elif out.agreed or not out.named:
            row[1] += 1
        else:
            row[2] += 1
            for key, whys in out.named.items():
                result.named[key] = result.named.get(key, 0) + 1
                for why in whys:
                    result.whys[(key, why)] = result.whys.get((key, why), 0) + 1
        if answer == "none":
            if out.fails:
                result.refused_failed += 1
            elif out.agreed:
                result.refused[out.agreed] = result.refused.get(out.agreed, 0) + 1
            else:
                result.refused_named += 1
        else:
            result.taken["failed" if out.fails else
                         "named" if out.named else "agreed"] += 1
    result.rows = [(name, *rows[name]) for name, _ in parts if name in rows]
    return result


def wireshark_record(ws):
    """The Wireshark section of the results file."""
    lines = ["## Wireshark", ""]
    if not ws.version:
        return lines + [
            f"Not run: {ws.reason}. Install Wireshark's tshark to run"
            " this part; `--require-wireshark` makes its absence a"
            " failure.", ""]
    rows = ws.rows
    total = [sum(r[i] for r in rows) for i in range(1, 5)]
    lines += [
        f"{ws.version}. Each message the parts above fed the tool (the"
        " request lines with no codes and the malformed request lines"
        " are not messages) is written by the harness as the UDP"
        " payload of an Ethernet/IPv4/UDP frame, from port 68 to port"
        " 67, or from 67 to 68 when its op byte is 2, into a pcap"
        " file, and dissected in batches of"
        f" {WS_BATCH} by `tshark -n -r <file> -T json -x` with an empty"
        " personal configuration. For each message the tool takes,"
        " the harness compares op, htype, hlen, hops, xid, secs,"
        " flags, ciaddr, yiaddr, siaddr, giaddr, chaddr, sname, file"
        " and the cookie (each as Wireshark shows it, and read at the"
        " offset SPEC.md gives), every option's code, length and"
        " value bytes in order, the end option and what follows it,"
        " and the message type. For every message it checks whether"
        " Wireshark marks the frame Malformed Packet, where it stops,"
        " and each expert error it reports.",
        "",
        "Each such fault is matched with one the harness finds in the"
        " message's bytes by following the checks of Wireshark 4.2.2's"
        " DHCP/BOOTP dissector (`WsModel` in tests/run_tests.py, written"
        " from epan/dissectors/packet-dhcp.c and get_dns_name in"
        " packet-dns.c at tag v4.2.2): the same exception at the same"
        " option, the same number of errors in the same option. A fault"
        " Wireshark reports that the harness does not find is a"
        " failure, and so is one the harness finds that Wireshark does"
        " not report. The harness does not follow these readers"
        " Wireshark keeps for particular vendors: "
        + "; ".join(WS_UNFOLLOWED)
        + ". A fault Wireshark reports in one of them is a failure"
        " too, and the failure names the reader.",
        "",
        "| part | messages | agreed | named differences | failures |",
        "| --- | --- | --- | --- | --- |",
    ]
    lines += [f"| {name} | {n} | {a} | {d} | {f} |" for name, n, a, d, f in rows]
    lines += [
        f"| total | {total[0]} | {total[1]} | {total[2]} | {total[3]} |",
        "",
        "A message the tool takes agrees when Wireshark shows every"
        " compared field as the tool reads it and reports no fault. A"
        " message the tool turns away agrees when Wireshark stops with"
        " an exception at a rule the tool turns it away for: "
        + "; ".join(f"{k}, {v}" for k, v in WS_AGREE.items())
        + "; or when there is no payload at all. Any other difference"
        " is a failure unless the harness finds its reason in the"
        " message itself, under one of the named differences below;"
        " for a message the tool turns away, each rule it breaks that"
        " Wireshark's dissection reaches must show in Wireshark's own"
        " reading. The list is computed by this run, with the number"
        " of messages under each; a message can fall under more than"
        " one.",
        "",
        f"The tool takes {sum(ws.taken.values())} of the messages:"
        f" Wireshark agrees on {ws.taken['agreed']}, differs only under"
        f" named differences on {ws.taken['named']}, and fails on"
        f" {ws.taken['failed']}. The tool turns away"
        f" {sum(ws.refused.values()) + ws.refused_named + ws.refused_failed}:"
        " Wireshark agrees on "
        + ", ".join(f"{ws.refused[k]} ({'no payload to dissect' if k == 'empty' else k})"
                    for k in list(WS_AGREE) + ["empty"] if ws.refused.get(k))
        + f", differs only under named differences on"
        f" {ws.refused_named}, and fails on {ws.refused_failed}.",
        "",
        "### Named differences",
        "",
    ]
    named = [(key, ws.named[key]) for key in WS_NAMED if ws.named.get(key)]
    if not named:
        lines += ["No message falls under a named difference.", ""]
    else:
        lines += ["| difference | messages | reason found in the message |",
                  "| --- | --- | --- |"]
        lines += [f"| {key} | {n} | {WS_NAMED[key]} |" for key, n in named]
        lines.append("")
    for key in ("option-value", "joined", "overload", "no-cookie"):
        whys = sorted(((w, n) for (k, w), n in ws.whys.items() if k == key),
                      key=lambda x: ws_order(x[0]))
        if whys:
            lines += [
                f"What the harness found under {key}, as option code:"
                " check, with the number of messages: "
                + "; ".join(f"{w} ({n})" for w, n in whys) + ".",
                "",
            ]
    return lines


def ws_order(why):
    head = why.split(":")[0]
    return (int(head) if head.isdigit() else 999, why)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=SEED_DEFAULT)
    parser.add_argument("--count", type=int, default=1500)
    parser.add_argument("--raw-count", type=int, default=1200)
    parser.add_argument("--area-count", type=int, default=800)
    parser.add_argument("--skip-build", action="store_true")
    parser.add_argument("--rebuild-scapy", action="store_true",
                        help="rebuild tests/scapy-packets.txt with Scapy, then stop")
    parser.add_argument("--require-wireshark", action="store_true",
                        help="count it as a failure when tshark is not on PATH")
    args = parser.parse_args()
    if args.rebuild_scapy:
        return rebuild_scapy_fixture()

    env = dict(__import__("os").environ)
    env["PATH"] = str(Path.home() / ".elan" / "bin") + ":" + env.get("PATH", "")
    if not args.skip_build:
        build = subprocess.run(
            ["lake", "build"],
            cwd=ROOT,
            env=env,
            capture_output=True,
            text=True,
            timeout=BUILD_TIMEOUT,
        )
        if build.returncode != 0:
            print(build.stdout[-3000:])
            print(build.stderr[-3000:])
            print("lake build failed")
            return 1

    fixed = run_fixed()
    readme = run_readme()
    choices = run_choices()
    valid, raw = run_random(args.seed, args.count, args.raw_count)
    areas = run_areas(args.seed, args.area_count)
    mut = run_mutations()
    scapy = run_scapy()
    probes = run_probes()
    malf = run_malformed()

    parts = [
        ("fixed cases: hand-built messages, the pad cases, the"
         " rejection shapes", fixed),
        ("requests with no codes, answered none", fixed.lines),
        ("the README example, answered ok: with the same codes", readme),
        ("the readings that depart from the RFCs, with the verdict"
         " SPEC.md states", choices),
        (f"random well formed messages (seed {args.seed})", valid),
        (f"random raw byte strings (seed {args.seed})", raw),
        (f"random option areas behind a fixed part and cookie"
         f" (seed {args.seed} + 1)", areas),
        ("mutations of one message: every truncation, every single"
         " byte flip, two targeted changes", mut),
        (f"packets built by Scapy {scapy.version}, from"
         f" tests/{SCAPY_FIXTURE.name}", scapy),
        ("options built by hand at the edges of the harness's account"
         " of Wireshark's checks (WS_PROBES), each in a DISCOVER", probes),
        ("malformed request lines, answered error", malf),
    ]
    ws = run_wireshark(parts, args.require_wireshark)
    failures = [f for _, t in parts for f in t.failures] + ws.failures
    total_in = sum(t.inputs for _, t in parts)
    total_agree = sum(t.agreements for _, t in parts)

    lean_ver = subprocess.run(
        ["lake", "env", "lean", "--version"],
        cwd=ROOT, env=env, capture_output=True, text=True, timeout=120,
    ).stdout.strip()

    lines = [
        "# Test results",
        "",
        "Written by `tests/run_tests.py`. Rerun it to check these numbers.",
        "",
        "- Oracle: the harness oracle, `oracle_parse` in"
        " tests/run_tests.py run under Python"
        f" {platform.python_version()}, a second reading of SPEC.md"
        " that settles every verdict; and "
        + (f"Wireshark's DHCP/BOOTP dissector, {ws.version}, an outside"
           " decoder run on every message (see Wireshark below)"
           if ws.version else
           f"no outside decoder: Wireshark did not run ({ws.reason})")
        + f". Scapy {scapy.version} built some inputs, and RFC 2131"
        " and RFC 2132 others by hand",
        f"- Seed: {args.seed}",
        f"- Inputs: {total_in}",
        f"- Failures: {len(failures)}",
        f"- Command: python3 tests/run_tests.py --seed {args.seed}"
        f" --count {args.count} --raw-count {args.raw_count}"
        f" --area-count {args.area_count}",
        (f"- Wireshark: {ws.version}; {ws.messages} messages,"
         f" {sum(r[2] for r in ws.rows)} agreed,"
         f" {sum(r[3] for r in ws.rows)} with named differences,"
         f" {sum(r[4] for r in ws.rows)} failed"
         if ws.version else f"- Wireshark: not run, {ws.reason}"),
        "- ISC DHCP and dnsmasq captures: not used. Neither ISC DHCP"
        " nor dnsmasq is installed in this environment, and no capture"
        " from either is available, so no capture corpus ran. Of the"
        " oracles the plan in dhcpv4#1 names (ISC DHCP and dnsmasq"
        " captures, Scapy, and Wireshark's dissectors), "
        + ("these captures are the only ones this run does not use"
           if ws.version else
           "this run uses only Scapy's packets: Wireshark did not run"
           " either"),
        f"- Lean: {lean_ver}",
        "",
        "## Counts",
        "",
        "| part | inputs | agreed |",
        "| --- | --- | --- |",
    ]
    lines += [f"| {name} | {t.inputs} | {t.agreements} |" for name, t in parts]
    lines += [
        f"| total | {total_in} | {total_agree} |",
        "",
        "An input agrees when the tool's answer is the oracle's"
        " answer, byte for byte, and, when it is `ok:`, the reprint"
        " is a well formed message, as `Spec.parse_wf` says. Between"
        " the tool and the harness oracle there is no list of excused"
        " differences: every disagreement counts as a failure.",
        "",
        f"Of the {areas.inputs} random option areas, the oracle takes"
        f" {areas.taken} and turns away {areas.inputs - areas.taken}.",
        "",
    ]
    lines += wireshark_record(ws)
    if failures:
        lines.append("## Failures")
        lines += [f"- {f}" for f in failures[:40]]
        lines.append("")
    RESULTS.write_text("\n".join(lines))
    print("\n".join(lines))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
