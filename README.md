# dhcpv4: a DHCPv4 wire message parser and printer, with proved round trips

Status: in progress

A parser and printer for DHCPv4 wire messages, in Lean,
following RFC 2131 (the message format) and RFC 2132 (the
options). The code is in `Dhcp/Value.lean` (the data
model and the printer) and `Dhcp/Parse.lean` (the parser).
The rules are written out in `SPEC.md`. This slice carries no lease
state, handles no relay agent behaviour, and reads no
DHCPv6.

The statements a reviewer approves are in `Spec.lean`,
with the definitions they use in `Spec/Defs.lean` (the
rules an input must follow, the option area grammar among
them, the canonical option area, and what a well formed
message is) and their proofs
in `Proofs/SpecProofs.lean`.
No reviewer has approved them yet, so this project is not
called verified.

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
against the harness oracle, the Scapy cross check, the
mutation and malformed cases, and the Wireshark cross
check, and writes the outcome to `tests/TEST-RESULTS.md`.
The Scapy cross check feeds the
packets stored in `tests/scapy-packets.txt`, which Scapy
built, so it runs the same with or without Scapy
installed. To build them again,
`python3 tests/run_tests.py --rebuild-scapy` uses Scapy
from the interpreter running the harness, or from the
virtual environment at `venv/` here; to make that venv, run
`python3 -m venv venv` and `venv/bin/pip install scapy`.

The Wireshark cross check runs Wireshark's DHCP/BOOTP
dissector as an outside decoder on every message the other
parts feed the tool, the ones it takes and the ones it turns
away: the fixed cases, the README example, the readings
cases, the random messages, raw byte strings and option
areas, the mutations, and the Scapy packets. The harness
writes each message as the UDP payload of an
Ethernet/IPv4/UDP frame into a pcap file of its own, has
`tshark` dissect the file in batches (`-T json`), and
compares what Wireshark read with what the tool read: op,
htype, hlen, hops, xid, secs, flags, ciaddr, yiaddr, siaddr,
giaddr, chaddr, sname, file, the cookie, each option's code,
length and value, the end option and what follows it, and
the message type; and, for every message, whether Wireshark
marks the frame Malformed Packet, where it stops, and which
expert errors it reports.

Wireshark does not read a message the way `SPEC.md` does:
it wants the end option, reads option 52 overload, joins
repeated options 119 and 120 (RFC 3396), checks the values
of options this slice carries unread, and takes messages
this slice turns away, such as the registered types 9 to 18
or a message with nonzero bytes after the end option. So
each difference must be either agreement or a named
difference whose reason the harness finds in the message's
bytes. For the fixed fields and option 53 it reads the
bytes by the rules of `SPEC.md`. For each fault Wireshark
reports, it finds the same fault by following the checks
of Wireshark 4.2.2's dissector, which it carries as
`WsModel` in `tests/run_tests.py`, written from that
dissector's source code; a fault that either side finds
and the other does not is a failure, except in the one
option whose checks the model follows only in part (122,
listed in the results file). A message the tool turns away
agrees with Wireshark only when Wireshark stops with an
exception at the rule the tool turns it away for. Any other
difference is a failure.

The committed record was made with TShark 4.2.2 on the
4,090 messages of the run with seed 20261026 (the other 14
inputs are request lines with no message), with 0
failures:

- The tool takes 1,918 messages. Wireshark agrees on 635
  and differs only under named differences on 1,283.
- The tool turns away 2,172. Wireshark agrees on 1,421: it
  stops with an exception where the message is too short
  (1,071), an option runs past the end (127), a code byte
  has no length byte (120), or option 53 has length 0 (97),
  or it finds no payload (6). It differs only under named
  differences on 751.

| Named difference | Messages | Where Wireshark and `SPEC.md` part |
|------------------|----------|-----------------------------------|
| no-end | 527 | no end byte: Wireshark reports End option missing; `SPEC.md` takes the message |
| overload | 105 | option 52: Wireshark hides sname or file, or reads them as options |
| option-value | 1,056 | an option other than 53 whose value fails the check Wireshark applies to that option; `SPEC.md` does not read it |
| hlen-0 | 128 | hlen 0: Wireshark shows no hardware address |
| secs-le | 5 | secs that look little endian: Wireshark shows them swapped |
| op | 392 | op not 1 or 2: Wireshark reports no error |
| hlen | 375 | hlen above 16: Wireshark reports no error, or stops reading a request's hlen bytes |
| no-cookie | 371 | no cookie: Wireshark reads plain BOOTP |
| after-end | 190 | nonzero bytes after the end byte: Wireshark shows them as padding |
| no-53 | 58 | no option 53: Wireshark reads plain BOOTP |
| 53-repeated | 106 | option 53 more than once: Wireshark reads each |
| 53-length | 54 | option 53 longer than one byte: Wireshark reads its first byte |
| 53-registered | 13 | types 9 to 18: Wireshark names them |
| 53-unknown | 104 | type 0 or above 18: Wireshark shows Unknown Message Type |

A message can fall under more than one. The results file
gives each reason in full and, under option-value, overload
and no-cookie, what the harness found, by option code.

The part needs `tshark` on `PATH`; without it the record
says the part did not run, and `--require-wireshark` makes
that a failure. Where CI's runner has no `tshark`, CI's
rerun skips this part; the input count and the failure
count it checks are the same either way, since the part
judges the same messages and a clean run adds no failure.

## What is proved

Each claim below names the theorem behind it. The
theorems are stated in `Spec.lean` (the challenge file,
where they end in `sorry`) and proved in
`Proofs/SpecProofs.lean`, under the same names.
`comparator.json` lists all of them. The first four are
general: each holds for every message or input it names.
Each row that starts "Example, one input" is proved for
that one input only: it shows one rule on a case, and the
rule itself is proved in general by
`Spec.parse_accepts_iff`. The test DISCOVER is the 250
byte request in the example above.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed message gives the message back. | `Spec.parse_print` |
| The option area of every input the parser takes, the bytes after the first 240, is one the option area grammar derives, carrying exactly the options of the parsed message; and printing that message gives the canonical form of the input: the first 240 bytes as they stood, then the canonical option area carrying those options (`canonArea` in `Spec/Defs.lean`), which is each option, in order, as its code byte, its length byte, and its value bytes, then exactly one end byte, with no pad bytes and nothing after the end byte. | `Spec.print_parse` |
| Every message the parser takes is well formed, in the sense below. This is about the message it returns; a parser that refuses everything also meets it, and `Spec.parse_print` rules that parser out. | `Spec.parse_wf` |
| The parser takes an input exactly when it follows the rules of `SPEC.md`: at least 240 bytes, op 1 or 2, hlen at most 16, and the cookie at bytes 236 to 239; an option area after them that the grammar derives; and option 53 once among the options that area carries, with a one byte value from 1 to 8. So it turns away every input that breaks a rule, takes every input that follows them all, and reads from it the options the grammar derives. | `Spec.parse_accepts_iff` |
| Example, one input: the test DISCOVER cut to 239 bytes is refused. The fixed fields and the cookie need 240. | `Spec.rejects_short_message` |
| Example, one input: the test DISCOVER with its third cookie byte set to 100 is refused. The cookie must be 99, 130, 83, 99. | `Spec.rejects_wrong_cookie` |
| Example, one input: a message whose option 55 claims ten value bytes, with three left, is refused. | `Spec.rejects_option_overrun` |
| Example, one input: a message whose last byte is the code of option 55, with no length byte after it, is refused. | `Spec.rejects_code_last_byte` |
| Example, one input: a message with option 55 and no option 53, the message type, is refused. | `Spec.rejects_no_option_53` |
| Example, one input: a message whose only option 53 has length 2 is refused. Its length must be 1. | `Spec.rejects_option_53_length_2` |
| Example, one input: a message whose only option 53 has value 0 is refused. The value must run from 1 to 8. | `Spec.rejects_option_53_value_0` |
| Example, one input: a message whose only option 53 has value 9 is refused. Value 9 is DHCPFORCERENEW (RFC 3203), a registered type this slice refuses on purpose. | `Spec.rejects_option_53_value_9` |
| Example, one input: a message with two option 53 items, both DISCOVER, is refused. The message type stands exactly once. | `Spec.rejects_option_53_twice` |
| Example, one input: the test DISCOVER with op 3 is refused. op must be 1 or 2. | `Spec.rejects_op_3` |
| Example, one input: the test DISCOVER with hlen 17 is refused. The hardware address cannot be longer than the chaddr field. | `Spec.rejects_hlen_17` |
| Example, one input: the test DISCOVER with a 1 after its end byte is refused. Only zero padding may follow the end byte, a choice stricter than RFC 2132 section 3.2, which says only that those bytes should be pad bytes. | `Spec.rejects_nonzero_after_end` |

A message is well formed when op is 1 or 2, htype and hops
fit one byte, hlen is at most 16, xid and the four
addresses fit four bytes, secs and flags fit two bytes,
chaddr, sname, and file hold 16, 64, and 128 bytes, every
option code runs from 1 to 254, every option value fits
one length byte, and option 53, the message type, stands
exactly once with a one byte value from 1 to 8. The full
list is in `SPEC.md`.

The rules are written in Lean in `Spec/Defs.lean`:
`FixedRules` for the fixed fields, `TypeRule` for option
53, and the option area grammar `OptionArea`. The grammar
is the rules of `SPEC.md` (The options) written as the
four ways an option area may go: it ends with the input;
the end byte follows, then only zero bytes; a pad byte,
then the rest; or an item (a code byte other than 0 and
255, a length byte, and exactly that many value bytes),
then the rest. Nothing else is an option area.

The canonical form of a message keeps the first 240 bytes
(the fixed fields and the cookie) as they stood, writes
the options with pad bytes dropped and zero padding after
the end byte dropped, and writes exactly one end byte,
supplying one when the input had none: the canonical
option area carrying the options the grammar reads from
the area. That area is `canonArea` in `Spec/Defs.lean`,
written apart from the printer: each option, in order, as
its code byte, its length byte, and its value bytes, then
exactly one end byte, 255. `Spec.print_parse` states the
print with `canonArea`, not with the printer's own option
writer, so a printer that wrote pad bytes, left out the
end byte, or wrote zeros after it, for a message the
parser took, would fail it.

The round trip and soundness theorems rest on the proofs
in `Proofs/RoundTrip.lean`, where they are
`Dhcp.Proofs.parse_print`, `Dhcp.Proofs.print_parse`, and
`Dhcp.Proofs.parse_wf`, and the statement of which inputs
the parser takes rests on `Dhcp.Proofs.parse_accepts_iff`
in `Proofs/Accept.lean`. All four check against the
standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`), which a reader can confirm with
`#print axioms`, or by running
`lake env lean Proofs/Verify.lean`. The refusal theorems
are single inputs checked in the kernel with
`decide +kernel`. Under the round trips, the steps are
proved one by one in the same file: the two and four byte
numbers both ways, the readers on printed forms and on
read forms, the fixed fields both ways, the option reader
on printed options, the lemma that the printer writes the
options as `canonArea`, and the lemma that every option
area the reader takes is one the grammar derives, with the
options it read. Under the soundness theorem, three lemmas
there say that read fixed fields are well formed, that
every option read has a code from 1 to 254 and a value of
at most 255 bytes, and that options passing the option 53
check hold option 53 once with a value from 1 to 8. In
`Proofs/Accept.lean`, the option reader follows every
derivation of the grammar, and the fixed fields of an
input that follows the fixed field rules read through.

The command line tool in `Main.lean` calls `Dhcp.parse`
and `Dhcp.print` directly, the same functions the theorems
are about.

## What is not proved

- That `FixedRules`, `OptionArea`, `TypeRule` and
  `canonArea` in `Spec/Defs.lean` say what `SPEC.md` says
  in words. `Spec.parse_accepts_iff` and
  `Spec.print_parse` hold the parser and printer to the
  Lean definitions; that these say what the page says is a
  reading, which the reviewer checks and the differential
  tests in `tests/` probe from the other side, with an
  oracle written from the words.
- A capture based differential. The plan in issue #1
  names ISC DHCP and dnsmasq captures, the Scapy packet
  builder, and the Wireshark dissectors as oracles. Scapy
  and Wireshark are used (see How to run it). ISC DHCP and
  dnsmasq captures are still not used: neither ISC DHCP nor
  dnsmasq is available in this environment, and no capture
  from either is at hand, so no capture corpus ran and
  nothing in the results rests on one. Of the plan's
  oracles, these captures are the only ones missing, so the
  open waiver question is about them alone. The messages
  Wireshark judged are the test messages, built by hand, by
  the harness's random and mutation generators, and by
  Scapy, not traffic that a DHCP server or client sent.
- Independence of the differential oracle, in part. The
  Python oracle in the test harness is a reading of the
  same `SPEC.md` the parser was written from, so the
  differential run against it checks that two readings of
  one document agree. Wireshark's dissector is an outside
  reading, but it is not an oracle for the verdict: it
  reads many messages this slice turns away, and turns away
  some this slice takes, on purpose. The harness names each
  such difference with the reason it finds in the message,
  and checks each fault against its account of Wireshark's
  checks (`WsModel`), both ways; that account is written
  from Wireshark's code, and that the named differences are
  the right ones to accept is a reading a reviewer checks.
  The hand-built fixed cases are written from RFC 2131 and
  RFC 2132 directly.
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
  choices. `Spec.parse_accepts_iff` holds the parser to
  each of them, through the rules in `Spec/Defs.lean`, and
  the tests check them; that they depart from the RFCs is
  what this item records.
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
  printer in this repo following each other, and the rules
  in `Spec/Defs.lean`, exactly; the
  fidelity of the spec to the RFCs is a reading, pinned in
  `SPEC.md` where the RFCs leave a choice open, and listed
  there where it departs from them. Likewise, that the
  rules in `Spec/Defs.lean` are the rules `SPEC.md` states
  in words.
- The Python oracle in `tests/run_tests.py`, the packets
  Scapy built, and Wireshark's DHCP/BOOTP dissector (TShark
  4.2.2 for the committed record) with the harness code
  that reads its output and its account of Wireshark's
  checks, `WsModel`. All are evidence, not proof. The
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
   oracle, the Scapy cross check, the mutation and
   malformed cases, and, with `tshark` installed, the
   Wireshark cross check, with the seed, the input count,
   Wireshark's version, its counts and named differences,
   and any failures written to `tests/TEST-RESULTS.md`.
3. `lake build`: the library, the proofs, and the tool
   build clean, and `lake env lean Proofs/Verify.lean`
   prints the axiom list for the round trip and soundness
   theorems, and for the statement of which inputs the
   parser takes.
4. Read `SPEC.md` against RFC 2131 and RFC 2132 and check
   the pinned readings, and the readings that depart from
   the RFCs, are the ones you want. Then read
   `Spec/Defs.lean` against `SPEC.md`.
