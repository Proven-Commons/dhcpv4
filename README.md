# dhcpv4: a DHCPv4 wire message parser and printer, with proved round trips

A parser and printer for DHCPv4 wire messages, in Lean,
following RFC 2131 (the message format) and RFC 2132 (the
options). The definitions are in `Dhcp/Value.lean` (the data
model and the printer) and `Dhcp/Parse.lean` (the parser).
The proofs are in `Proofs/RoundTrip.lean`. This slice
carries no lease state, handles no relay agent behaviour,
and reads no DHCPv6.

Status: the specification has not been approved by a
reviewer, so do not call this verified. The statements a
reviewer approves (the bar's `Spec.lean`) have not been
added yet.

## What is proved

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed message gives the message back. | `Dhcp.Proofs.parse_print` |
| Printing a message the parser took gives the canonical form of the bytes it was read from. | `Dhcp.Proofs.print_parse` |

A message is well formed when op is 1 or 2, htype and hops
fit one byte, hlen is at most 16, xid and the four addresses
fit four bytes, secs and flags fit two bytes, chaddr,
sname, and file hold 16, 64, and 128 bytes, every option
code runs from 1 to 254, every option value fits one length
byte, and option 53, the message type, stands exactly once
with a one byte value from 1 to 8.

The canonical form of a message keeps the first 240 bytes
(the fixed fields and the cookie) as they stood, writes the
options with pad bytes dropped and zero padding after the
end byte dropped, and writes exactly one end byte,
supplying one when the input had none.

Both theorems check against the standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`), which a
reader can confirm with `#print axioms` on
`Dhcp.Proofs.parse_print` and `Dhcp.Proofs.print_parse`;
`Proofs/Verify.lean` prints them at build time.

The command-line tool in `Main.lean` calls these functions
directly.

## What is not proved

- That the parser accepts every message the rules in
  `SPEC.md` allow, and turns away every message they
  forbid. The round trips do not need either, so neither is
  proved. The differential tests in `tests/` check that
  behaviour instead, and the results file records the
  outcome, including any failure.
- The meaning of any option except option 53. Every other
  option is carried as its code and value bytes, and no per
  option length or content rule is checked.
- The contents of sname and file, such as where a name ends
  at a zero byte inside them. They are carried as full
  fixed size blocks.
- Anything about leases, address assignment over time,
  relay agents, or DHCPv6.
- Reading requests and printing answers in `Main.lean`:
  splitting lines, the decimal parser. The tests cover
  them, malformed requests included.
- Speed. The code works on lists of bytes, which suits
  proofs, not large data.

## What you must trust

- The Lean kernel, which checks the proofs.
- The Lean compiler, with the C compiler and linker shipped
  with it, and the runtime, which turn the proved
  definitions into the program that runs.
- Lean's core library, including the compiled code it puts
  in place of some definitions the proofs reason about.
- The operating system and hardware it runs on.
- The strict Python reading of the rules in `SPEC.md`,
  written in the test harness, as the oracle in the
  differential tests. Scapy 2.8.0 was present (in a venv
  inside the working directory, not in the system Python)
  and built the cross-check packets; the oracle settled
  every verdict on them. No ISC DHCP or dnsmasq captures
  were available in the build environment, so no capture
  corpus was run; the results file says so.

This project has no dependencies beyond Lean itself.

## Run it

Needs Linux and [elan](https://github.com/leanprover/elan).
Build, then feed request lines to the tool:

```
lake build
printf 'parse 1,1,6,0,18,52,86,120,0,0,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,11,130,1,252,66,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,99,130,83,99,53,1,1,55,4,1,3,6,15,255\n' | .lake/build/bin/dhcpv4
```

That request is a DISCOVER (broadcast flag set, a six byte
hardware address in chaddr, options 53 and 55) and the
answer is `ok:` with the same codes back, since the message
is already in canonical form. A message the parser turns
away, such as the single code `1`, answers `none`. A
malformed request answers `error`. See `SPEC.md` for the
full protocol.

## Re-check it

```
lake build
python3 tests/run_tests.py
```

The test run rebuilds the tool, runs the fixed cases, the
differential run, and the Scapy cross check, and rewrites
`tests/TEST-RESULTS.md`. The numbers in that file are the
record of the run described there. The Scapy cross check
runs when Scapy is reachable from the interpreter running
the harness, or from the venv at `venv/` beside it; to
rebuild that venv, run `python3 -m venv venv` here and
`venv/bin/pip install scapy`.
