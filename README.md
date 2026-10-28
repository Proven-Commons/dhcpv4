# dhcpv4: a DHCPv4 wire message parser and printer, with proved round trips

Status: in-progress

A parser and printer for DHCPv4 wire messages, in Lean,
following RFC 2131 (the message format) and RFC 2132 (the
options). The definitions are in `Dhcp/Value.lean` (the
data model, the printer, and the canonical form of an
option area) and `Dhcp/Parse.lean` (the parser). The rules
are written out in `SPEC.md`. This slice carries no lease
state, handles no relay agent behaviour, and reads no
DHCPv6.

The statements a reviewer approves are in `Spec.lean`,
with their proofs in `Proofs/SpecProofs.lean`. No reviewer
has approved them yet, so this project is not called
verified.

## How to run it

`lake build` builds the library, the proofs, and the
command line tool. The tool reads one request per line:
the word `parse`, a space, and the message as
comma-separated decimal byte codes. It answers `ok:` and
the byte codes of the canonical reprint when the message
parses, `none` when the message is turned away, and
`error` when the request itself is malformed.

```
lake build
printf 'parse 1,1,6,0,18,52,86,120,0,0,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,11,130,1,252,66,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,99,130,83,99,53,1,1,55,4,1,3,6,15,255\n' | .lake/build/bin/dhcpv4
```

That request is a 250 byte DISCOVER: 34 bytes of fields
(op 1, htype 1, hlen 6, xid 0x12345678, the broadcast flag
set, and the six byte hardware address 00:0b:82:01:fc:42 at
the front of chaddr), 202 zero bytes (the rest of chaddr,
then sname and file), the cookie at offset 236, then
option 53 with value 1, option 55 with four codes, and the
end byte. The answer is `ok:` followed by the same 250
codes, since the message is already in canonical form. A
message the parser turns away, such as the single code
`1`, answers `none`. See `SPEC.md` for the full protocol.

`python3 tests/run_tests.py` rebuilds the tool, runs the
fixed cases, the README example above, the cases for the
readings that depart from the RFCs, the differential run
against the harness oracle, the Scapy cross check, and the
mutation and malformed cases, and writes the outcome to
`tests/TEST-RESULTS.md`. The Scapy cross check feeds the
packets stored in `tests/scapy-packets.txt`, which Scapy
built, so it runs the same with or without Scapy
installed. To build them again,
`python3 tests/run_tests.py --rebuild-scapy` uses Scapy
from the interpreter running the harness, or from the
virtual environment at `venv/` here; to make that venv, run
`python3 -m venv venv` and `venv/bin/pip install scapy`.

## What is proved

Each claim below names the theorem behind it. The
theorems are stated in `Spec.lean` (the challenge file,
where they end in `sorry`) and proved in
`Proofs/SpecProofs.lean`, under the same names.
`comparator.json` lists all of them.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed message gives the message back. | `Spec.parse_print` |
| Printing a message the parser took gives the canonical form of the bytes it was read from: the first 240 bytes as they stood, then the canonical option area. | `Spec.print_parse` |
| Every message the parser takes is well formed, in the sense below. This is about the message it returns; a parser that refuses everything also meets it, and `Spec.parse_print` rules that parser out. | `Spec.parse_wf` |
| A message of 239 bytes is refused: the fixed fields and the cookie need 240. | `Spec.rejects_short_message` |
| A message with a wrong magic cookie is refused: the cookie must be 99, 130, 83, 99. | `Spec.rejects_wrong_cookie` |
| An option whose length runs past the end of the message is refused. | `Spec.rejects_option_overrun` |
| A message with no option 53, the message type, is refused. | `Spec.rejects_no_option_53` |
| An option 53 of length 2 is refused: its length must be 1. | `Spec.rejects_option_53_length_2` |
| An option 53 with value 0 is refused: the value must run from 1 to 8. | `Spec.rejects_option_53_value_0` |
| An option 53 with value 9 is refused: the value must run from 1 to 8. Value 9 is DHCPFORCERENEW (RFC 3203), a registered type this slice refuses on purpose. | `Spec.rejects_option_53_value_9` |
| A message with two option 53 items is refused: the message type stands exactly once. | `Spec.rejects_option_53_twice` |
| A message with op 3 is refused: op must be 1 or 2. | `Spec.rejects_op_3` |
| A message with hlen 17 is refused: the hardware address cannot be longer than the chaddr field. | `Spec.rejects_hlen_17` |
| A nonzero byte after the end byte is refused: only zero padding may follow it. This is stricter than RFC 2132 section 3.2, which says only that those bytes should be pad bytes. | `Spec.rejects_nonzero_after_end` |

A message is well formed when op is 1 or 2, htype and hops
fit one byte, hlen is at most 16, xid and the four
addresses fit four bytes, secs and flags fit two bytes,
chaddr, sname, and file hold 16, 64, and 128 bytes, every
option code runs from 1 to 254, every option value fits
one length byte, and option 53, the message type, stands
exactly once with a one byte value from 1 to 8. The full
list is in `SPEC.md`.

The canonical form of a message keeps the first 240 bytes
(the fixed fields and the cookie) as they stood, writes
the options with pad bytes dropped and zero padding after
the end byte dropped, and writes exactly one end byte,
supplying one when the input had none.

The round trip and soundness theorems rest on the proofs
in `Proofs/RoundTrip.lean`, where they are
`Dhcp.Proofs.parse_print`, `Dhcp.Proofs.print_parse`, and
`Dhcp.Proofs.parse_wf`. All three check against the
standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`), which a reader can confirm with
`#print axioms`, or by running
`lake env lean Proofs/Verify.lean`. The refusal theorems
are single inputs checked in the kernel with
`decide +kernel`. Under the round trips, the steps are
proved one by one in the same file: the two and four byte
numbers both ways, the readers on printed forms and on
read forms, the fixed fields both ways, the option reader
on printed options, and the lemma that a read option area
canonicalizes to the printed options of the value it read
to.

The command line tool in `Main.lean` calls `Dhcp.parse`
and `Dhcp.print` directly, the same functions the theorems
are about.

## What is not proved

- That the parser accepts every message the rules in
  `SPEC.md` allow. The round trips do not need it, and it
  is not proved.
- That the parser turns away every message the rules
  forbid, beyond what `Spec.parse_wf` says about the
  message it returns. The rules on the input bytes
  themselves, such as the cookie, the zero bytes after the
  end byte, and a code byte with no length byte, are
  pinned by the refusal theorems on one input each, not in
  general. The differential tests in `tests/` check that
  behaviour instead, and the results file records the
  outcome, including any failure.
- A capture based differential, and a differential
  against an outside decoder. The plan names ISC DHCP and
  dnsmasq captures and the Wireshark dissectors as
  oracles. No captures are available in this environment,
  so no capture corpus ran, and no Wireshark dissector
  judged any input; nothing in the results rests on
  either. The outside
  bytes in the tests came from Scapy, which built packets
  with its BOOTP and DHCP layers; the harness oracle
  settled every verdict on them.
- Independence of the differential oracle. The Python
  oracle in the test harness is a reading of the same
  `SPEC.md` the parser was written from, so the
  differential run checks that two readings of one
  document agree, not that either matches an independent
  reading of the RFCs. The hand-built fixed cases are
  written from RFC 2131 and RFC 2132 directly.
- The readings in `SPEC.md` that depart from the RFCs,
  listed there under "Readings that depart from the RFCs":
  an option area with no end byte is taken, though RFC
  2131 section 4.1 says the last option must be the end
  option; a nonzero byte after the end byte is refused,
  though RFC 2132 section 3.2 says only that those bytes
  should be pad bytes; option overload (option 52) is not
  read, so file and sname are never read as options and
  the message type comes from the options field alone;
  repeated options are not joined as RFC 3396 asks, so a
  message type split over two items is refused; and the
  registered message types 9 to 18 (RFC 3203, RFC 4388,
  RFC 6926, RFC 7724) are refused on purpose. These are
  choices, checked by the tests, not departures the proofs
  rule out.
- The meaning of any option except option 53. Every other
  option is carried as its code and value bytes, and no
  per option length or content rule is checked.
- The contents of sname and file, such as where a name
  ends at a zero byte inside them. They are carried as
  full fixed size blocks.
- Anything about leases, address assignment over time,
  relay agents, or DHCPv6.
- Reading requests and printing answers in `Main.lean`:
  splitting lines, the decimal parser. The tests cover
  them, malformed requests included.
- Speed. The code works on lists of bytes, which suits
  proofs, not large data.

## What you must trust

- The Lean kernel (Lean 4.35.0, pinned in
  `lean-toolchain`), which checks every proof.
- The Lean compiler, with the C compiler and linker
  shipped with it, which turns the proved definitions into
  the program that runs.
- The Lean runtime, which runs that program.
- The hardware the program runs on.
- Every dependency in `lake-manifest.json`: the manifest
  lists no packages, so there are no library dependencies
  to trust beyond the Lean toolchain itself.
- Lean's core library, including the compiled code it puts
  in place of some definitions the proofs reason about.
- The operating system the program runs on.
- That `SPEC.md` states the reading of RFC 2131 and
  RFC 2132 you intend. The proofs are about the parser and
  printer in this repo following each other exactly; the
  fidelity of the spec to the RFCs is a reading, pinned in
  `SPEC.md` where the RFCs leave a choice open.
- The Python oracle in `tests/run_tests.py` and the
  packets Scapy built. Both are evidence, not proof. The
  results file names the versions used, and states
  plainly which oracles were and were not available.
- The line handling in `Main.lean` (splitting a request
  line, reading decimal codes). The tests drive it, and no
  proof covers it.
- There are no exceptions to item 4 of the bar: the
  project uses none of the features it forbids.

## Re-check it

1. `lake comparator --paranoid`: builds the challenge
   file `Spec.lean` and the proofs in a sandbox and
   checks that each theorem named in `comparator.json`
   proves exactly the statement in the challenge file,
   uses no axiom but the three standard ones, and is
   accepted by Lean's kernel and every other kernel
   shipped with Lean.
2. `python3 tests/run_tests.py`: the fixed cases, the
   README example, the cases for the readings that depart
   from the RFCs, the differential against the harness
   oracle, the Scapy cross check, and the mutation and
   malformed cases, with the seed, the input count and any
   failures written to `tests/TEST-RESULTS.md`.
3. `lake build`: the library, the proofs, and the tool
   build clean, and `lake env lean Proofs/Verify.lean`
   prints the axiom list for the round trip theorems.
4. Read `SPEC.md` against RFC 2131 and RFC 2132 and check
   the pinned readings are the ones you want.
