#!/usr/bin/env python3
"""Tests for the Lean DHCPv4 wire message parser and printer.

Four parts.

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
   at ../venv. No ISC DHCP or dnsmasq captures were available
   in this environment, so no capture corpus was run; the
   record says so too.

4. Malformed request lines must be answered `error`.

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

The tool is driven one batch process per chunk of requests,
input written and closed, output drained until the process
exits. It builds the executable first, writes
tests/TEST-RESULTS.md, and exits non-zero if any check fails.
It needs Python 3.11 or later.
"""

import argparse
import platform
import random
import subprocess
import sys
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

    def check(self, data, answer, label):
        self.inputs += 1
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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seed", type=int, default=SEED_DEFAULT)
    parser.add_argument("--count", type=int, default=1500)
    parser.add_argument("--raw-count", type=int, default=1200)
    parser.add_argument("--area-count", type=int, default=800)
    parser.add_argument("--skip-build", action="store_true")
    parser.add_argument("--rebuild-scapy", action="store_true",
                        help="rebuild tests/scapy-packets.txt with Scapy, then stop")
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
        ("malformed request lines, answered error", malf),
    ]
    failures = [f for _, t in parts for f in t.failures]
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
        " that settles every verdict; Scapy"
        f" {scapy.version} built some inputs and RFC 2131 and RFC 2132"
        " others by hand, but no outside decoder judges any input",
        f"- Seed: {args.seed}",
        f"- Inputs: {total_in}",
        f"- Failures: {len(failures)}",
        f"- Command: python3 tests/run_tests.py --seed {args.seed}"
        f" --count {args.count} --raw-count {args.raw_count}"
        f" --area-count {args.area_count}",
        "- ISC DHCP and dnsmasq captures: not present in this"
        " environment, no capture corpus run",
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
        " is a well formed message, as `Spec.parse_wf` says. The"
        " harness keeps no list of excused differences: every"
        " disagreement counts as a failure.",
        "",
        f"Of the {areas.inputs} random option areas, the oracle takes"
        f" {areas.taken} and turns away {areas.inputs - areas.taken}.",
        "",
    ]
    if failures:
        lines.append("## Failures")
        lines += [f"- {f}" for f in failures[:40]]
        lines.append("")
    RESULTS.write_text("\n".join(lines))
    print("\n".join(lines))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
