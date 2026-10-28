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

Every `ok:` answer is also checked to be a well formed
message, as `Spec.parse_wf` says: op 1 or 2, hlen at most
16, the cookie at offset 236, codes from 1 to 254, and option
53 exactly once with a value from 1 to 8.

2. A differential run against a strict Python oracle written
   in this harness from the rules in SPEC.md: random well
   formed messages, some with pad bytes sprinkled among the
   options, some with zero padding after the end byte, some
   with no end byte; random raw byte strings; and mutations
   of one rich message (every truncation, every single byte
   flip, and targeted changes).

3. A Scapy cross check: packets built with Scapy's BOOTP and
   DHCP layers (Scapy 2.8.0), each fed to the tool and to the
   oracle; the tool must agree with the oracle on each one.
   Scapy is only a source of independently built bytes here;
   the oracle settles every verdict. When Scapy is not
   importable by this interpreter, the harness looks for the
   project venv at ../venv and uses its interpreter to build
   the packets. When neither works, the run says so on the
   record. No ISC DHCP or dnsmasq captures were available in
   this environment, so no capture corpus was run; the record
   says so too.

4. Malformed request lines must be answered `error`.

Two more line checks stand apart from the fixed cases of
part 1: the requests `parse ` and `parse`, with no codes,
must be answered `none` (the empty message is turned away).
The results file counts them on their own line, not as
fixed cases. So is the example request in README.md: the
harness reads it from the page, runs it, and checks that the
answer is `ok:` and the same codes, as the page says.

    python3 tests/run_tests.py [--seed N] [--count N]

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
    tally = Tally()
    rng = random.Random(seed)
    docs = [random_message(rng) for _ in range(valid_count)]
    answers, problems = ask_all([request(d) for d in docs])
    tally.failures += problems
    for i, (data, answer) in enumerate(zip(docs, answers)):
        tally.check(data, answer, f"random valid {i}")
    raws = []
    for _ in range(raw_count):
        n = rng.randint(0, 340)
        raws.append(bytes(rng.randrange(256) for _ in range(n)))
    answers, problems = ask_all([request(d) for d in raws])
    tally.failures += problems
    for i, (data, answer) in enumerate(zip(raws, answers)):
        tally.check(data, answer, f"random raw {i}")
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

for job in jobs:
    pkt = build(**job)
    if pkt is not None:
        sys.stdout.write(pkt.hex() + "\n")
'''


def scapy_packets():
    """Packets built by Scapy, or None when Scapy is reachable
    neither in this interpreter nor in the project venv.
    Returns (packets, how) where how says where Scapy ran."""
    try:
        import scapy  # noqa: F401

        scapy_here = True
    except ImportError:
        scapy_here = False
    if scapy_here:
        proc = subprocess.run(
            [sys.executable, "-c", SCAPY_SCRIPT],
            capture_output=True, text=True, timeout=300,
        )
        if proc.returncode == 0 and proc.stdout.strip():
            pkts = [bytes.fromhex(line) for line in proc.stdout.split()]
            return pkts, f"Scapy in this interpreter (Python {platform.python_version()})"
    venv_python = ROOT / "venv" / "bin" / "python"
    if venv_python.exists():
        proc = subprocess.run(
            [str(venv_python), "-c", SCAPY_SCRIPT],
            capture_output=True, text=True, timeout=300,
        )
        if proc.returncode == 0 and proc.stdout.strip():
            pkts = [bytes.fromhex(line) for line in proc.stdout.split()]
            return pkts, "Scapy in the project venv (venv/bin/python)"
    return None, "Scapy not reachable"


def run_scapy():
    tally = Tally()
    pkts, how = scapy_packets()
    tally.how = how
    if pkts is None:
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
    parser.add_argument("--skip-build", action="store_true")
    args = parser.parse_args()

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
    rand = run_random(args.seed, args.count, args.raw_count)
    mut = run_mutations()
    scapy = run_scapy()
    malf = run_malformed()

    failures = (
        fixed.failures + fixed.lines.failures + readme.failures
        + rand.failures
        + mut.failures + scapy.failures + malf.failures
    )
    total_in = (
        fixed.inputs + fixed.lines.inputs + rand.inputs
        + mut.inputs + scapy.inputs
    )
    total_agree = (
        fixed.agreements + fixed.lines.agreements
        + rand.agreements + mut.agreements + scapy.agreements
    )

    lean_ver = subprocess.run(
        ["lake", "env", "lean", "--version"],
        cwd=ROOT, env=env, capture_output=True, text=True, timeout=120,
    ).stdout.strip()

    lines = [
        "# Test results",
        "",
        "Written by `tests/run_tests.py`. Rerun it to check these numbers.",
        "",
        "- Oracle: a strict reading of the rules in SPEC.md written"
        f" in the harness (Python {platform.python_version()}), plus"
        " hand-built fixed cases from RFC 2131 and RFC 2132",
        f"- Scapy: {scapy.how}; packets built with its BOOTP and DHCP"
        " layers and settled by the oracle"
        if scapy.inputs else
        f"- Scapy: {scapy.how}, no cross check run",
        "- ISC DHCP and dnsmasq captures: not present in this"
        " environment, no capture corpus run",
        f"- Lean: {lean_ver}",
        f"- Seed: {args.seed}",
        f"- Fixed cases (hand-built messages, the pad cases, the"
        f" rejection shapes): {fixed.agreements} of {fixed.inputs} agreements",
        f"- Requests with no codes, answered none:"
        f" {fixed.lines.agreements} of {fixed.lines.inputs}",
        f"- README example answered ok: with the same codes:"
        f" {readme.agreements} of {readme.inputs}",
        f"- Random well formed messages: part of {rand.agreements} of"
        f" {rand.inputs} agreements in the random run (well formed"
        f" {args.count}, raw byte strings {args.raw_count})",
        f"- Mutations (every truncation, every single byte flip,"
        f" targeted): {mut.agreements} of {mut.inputs} agreements",
        f"- Scapy cross checks: {scapy.agreements} of {scapy.inputs} agreements"
        if scapy.inputs else "- Scapy cross checks: 0 run",
        f"- Malformed requests answered error: {malf.agreements} of {malf.inputs}",
        f"- Differential inputs: {total_in}",
        f"- Differential agreements: {total_agree}",
        "- Named differences: none",
        f"- Failures: {len(failures)}",
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
