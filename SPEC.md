# Specification: dhcpv4

A DHCPv4 wire message parser and printer in Lean, following
RFC 2131 (the message format) and RFC 2132 (the options).
This slice carries lease state nowhere, handles no relay
agent behaviour, and reads no DHCPv6.

## The fixed fields

A message starts with the fixed fields of RFC 2131 section
2, in the BOOTP legacy layout, then the magic cookie:

| Bytes | Field |
|-------|-------|
| 0 | op: 1 is a request (BOOTREQUEST), 2 is a reply (BOOTREPLY) |
| 1 | htype: the hardware address type |
| 2 | hlen: the hardware address length |
| 3 | hops: the relay hop count |
| 4 to 7 | xid: the transaction identifier, big endian |
| 8, 9 | secs: seconds since the client began, big endian |
| 10, 11 | flags, big endian; the top bit is the broadcast flag |
| 12 to 15 | ciaddr: the client address |
| 16 to 19 | yiaddr: the address offered to the client |
| 20 to 23 | siaddr: the server address |
| 24 to 27 | giaddr: the relay agent address |
| 28 to 43 | chaddr: the client hardware address field, 16 bytes |
| 44 to 107 | sname: the server host name field, 64 bytes |
| 108 to 235 | file: the boot file name field, 128 bytes |
| 236 to 239 | the magic cookie: 99, 130, 83, 99 |

The field rules, one by one:

- A message shorter than 240 bytes is turned away. The
  fixed fields and the cookie cannot fit in less.
- The four cookie bytes must be 99, 130, 83, 99, in that
  order. The cookie is what marks the tail as DHCP options
  rather than old vendor extension bytes. A wrong cookie is
  turned away.
- op must be 1 or 2. Any other value is turned away.
- hlen must be at most 16, the size of the chaddr field. A
  longer hardware address could not fit, and is turned away.
- htype, hops, secs, and flags are carried unchecked: any
  byte or two byte value they hold is kept as it stands.
- chaddr is carried as the full sixteen bytes as they stand
  on the wire. It is not cut down to hlen: printing must
  give the wire bytes back, and a cut would lose bytes the
  message carried.
- sname and file are carried as their full fixed size byte
  blocks. What the bytes mean, such as where a name ends at
  a zero byte inside sname, is not read in this slice.

Addresses and the other multi byte fields are held as the
values of their bytes, read big endian, and printed back big
endian.

The four rules that turn a message away (the 240 byte
minimum, the cookie, op, and hlen) are written in Lean as
`FixedRules` in `Spec/Defs.lean`.

## The options

After the cookie come the options of RFC 2132, as a row of
items. Each item is one of:

- A pad byte, 0. It has no length and no value, it carries
  no meaning, and it is not part of the message value. A
  reader skips it wherever it stands among the options.
- An end byte, 255. It stops the option list.
- A code byte (1 to 254), a length byte, and that many
  value bytes.

The readings for the ends of the list:

- After the end byte, every remaining byte must be zero.
  Senders pad messages to a minimum size with zeros, so zero
  padding after the end byte is read and dropped. A nonzero
  byte after the end byte turns the message away.
- With no end byte, the options must run exactly to the end
  of the input. A last item whose value ends at the last
  input byte is complete.
- A length that runs past the end of the message turns the
  message away: the value bytes are not there to read.
- A code byte with no length byte after it, a code at the
  very last byte, turns the message away.
  `Spec.rejects_code_last_byte` pins this on one input.
- An option area may be empty of items (the input ends at
  the cookie, or an end byte follows the cookie at once),
  but see the option 53 rule below: such a message is turned
  away for want of a message type.

These rules make a grammar, written in Lean as
`OptionArea` in `Spec/Defs.lean`. An option area is one
of:

- nothing at all: the input ends after the last item, with
  no end byte;
- the end byte, then only zero bytes;
- a pad byte, then an option area;
- an item, which is a code byte other than 0 and 255, a
  length byte, and exactly that many value bytes, then an
  option area.

The options an area carries are its items, in order, each
as its code and value bytes. Nothing else is an option
area: a code byte with no length byte after it, a length
that runs past the end, and a nonzero byte after the end
byte have no place in the grammar. Which of the four an
area is depends on its first byte, and an item's length
byte says where its value ends.

## Option 53

Option 53, the message type, is the one option whose value
this slice reads. The rules:

- Option 53 must stand in the list. A message without it is
  turned away.
- It must stand exactly once. Two message types cannot both
  hold, so a second option 53 turns the message away.
- Its length must be 1.
- Its one value byte must run from 1 to 8: 1 DISCOVER, 2
  OFFER, 3 REQUEST, 4 DECLINE, 5 ACK, 6 NAK, 7 RELEASE, 8
  INFORM. Any other value turns the message away, including
  the registered types 9 to 18, which this slice refuses on
  purpose (see the readings below).

These four rules are written in Lean as `TypeRule` in
`Spec/Defs.lean`: exactly one option carries code 53, and
its value is one byte from 1 to 8.

Every other option is carried uninterpreted, as its code
and value bytes, in wire order. An option may repeat; the
repeats are kept in order as separate items, not joined
(see the readings below). No other option's value is
checked in this slice: not its length against any per option
rule, and not its contents. That is the slice boundary.

## Readings that depart from the RFCs

Where this slice reads a message differently from RFC 2131,
RFC 2132, RFC 3396, or the registered message types, the
reading is a choice, listed here. Each one is what the
parser does, what `Spec.parse_accepts_iff` holds it to
through the rules in `Spec/Defs.lean`, and what the tests
check.

- No end byte. RFC 2131 section 4.1 says "The last option
  must always be the 'end' option." This parser is more
  lenient: an option area with no end byte is taken when
  its last item ends exactly at the last input byte, and
  the reprint adds the end byte. Scapy 2.8.0 also decodes
  such a message; Wireshark 4.2.2 dissects it but reports
  the expert error End option missing.
- Bytes after the end byte. RFC 2132 section 3.2 says only
  that the octets after the end option "should be filled
  with pad options". This parser is stricter: any nonzero
  byte after the end byte turns the message away, so a
  message another decoder takes (Scapy 2.8.0 decodes it and
  keeps the trailing bytes, and Wireshark 4.2.2 shows them
  as padding with no error) is refused here.
  `Spec.rejects_nonzero_after_end` pins this choice on one
  input.
- Option overload is not read. RFC 2131 section 4.1 and
  RFC 2132 section 9.3 let option 52 say that the file and
  sname fields carry further options, which a reader must
  then interpret, file first, then sname. This slice never
  reads file or sname as options: they are carried as byte
  blocks, and option 52 is carried as an ordinary option.
  So the message type comes from the options field alone.
  A message whose options field holds one option 53 and
  option 52, and whose file field holds a second option 53,
  is taken with the type from the options field, where a
  reader that follows option 52 would see two. Wireshark
  4.2.2 follows option 52: with value 1, 2 or 3 it reads
  file or sname, or both, as options.
- Repeated options are not joined. RFC 3396 section 7 (and
  RFC 2131 section 4.1 before it) asks a reader to join the
  values of repeated options into one. This slice keeps
  each repeat as its own item, in wire order, and the
  reprint writes them back the same way. For option 53 the
  exactly once rule applies to the items as they stand: a
  type split over two items, such as `53 0` then `53 1 1`,
  turns the message away, where a reader that joins them
  would see one type, DISCOVER. Wireshark 4.2.2 shows each
  repeat as its own item too, and joins the values only of
  repeated options 119 and 120, before it reads them.
- Message types 9 to 18 are refused on purpose. They are
  registered: 9 DHCPFORCERENEW (RFC 3203); 10
  DHCPLEASEQUERY, 11 DHCPLEASEUNASSIGNED, 12
  DHCPLEASEUNKNOWN, 13 DHCPLEASEACTIVE (RFC 4388); 14
  DHCPBULKLEASEQUERY, 15 DHCPLEASEQUERYDONE (RFC 6926); 16
  DHCPACTIVELEASEQUERY, 17 DHCPLEASEQUERYSTATUS, 18 DHCPTLS
  (RFC 7724). The plan for this slice covers types 1 to 8
  only, so a message of any of these types is turned away,
  the same answer as for a malformed message.
  `Spec.rejects_option_53_value_9` pins the refusal of
  DHCPFORCERENEW on one input. Wireshark 4.2.2 reads these
  types and reports no error for them.

## Printing and the canonical form

The printer writes the fixed fields as they stood, the
cookie, then each option as a code byte, a length byte, and
its value bytes, then exactly one end byte, 255. It writes
no pad bytes.

So a message that parses prints to a canonical form: the
first 240 bytes as they stood, then the options with pad
bytes anywhere among them dropped, zero padding after the
end byte dropped, exactly one end byte written, and an end
byte supplied when the input had none. A message already
in canonical form prints to itself, byte for byte.

The canonical option area carrying a list of options is
written in Lean as `canonArea` in `Spec/Defs.lean`, apart
from the printer: each option, in order, as its code byte,
its length byte, and its value bytes, then exactly one end
byte, 255. It holds no pad bytes, and nothing follows the
end byte. In terms of the grammar, the canonical form of
an option area is the canonical option area carrying the
options it derives.

## The claims

`Spec.parse_print`: for every well formed message, parsing
its printed form gives the message back.

Well formed means: op is 1 or 2; htype and hops fit one
byte; hlen is at most 16; xid and the four addresses fit
four bytes; secs and flags fit two bytes; chaddr, sname,
and file hold 16, 64, and 128 bytes; every option code runs
from 1 to 254; every option value fits one length byte; and
option 53 stands exactly once with a one byte value from 1
to 8.

`Spec.print_parse`: for every byte list the parser takes,
the bytes after the first 240 are an option area the
grammar derives, carrying exactly the options of the
parsed message, and printing that message gives the
canonical form of the input, as spelled out above: the
first 240 bytes as they stood, then the canonical option
area carrying those options, `canonArea`. The statement
names `canonArea`, not the printer's own option writer, so
a printer that wrote pad bytes, left out the end byte, or
wrote zeros after it, for a message the parser took, would
fail it.

`Spec.parse_wf`: every message the parser takes is well
formed, in the sense spelled out under `Spec.parse_print`.
The statement is about the message the parser returns, not
about the input bytes on their own. A parser that refuses
every input also meets it; `Spec.parse_print` rules that
parser out.

`Spec.parse_accepts_iff`: the parser takes an input,
reading the options `os` from it, exactly when the input
follows the rules above: `FixedRules` on its first 240
bytes, an option area after them that the grammar derives
with `os`, and `TypeRule` on `os`. These are the rules of
The fixed fields, The options, and Option 53, written in
Lean in `Spec/Defs.lean`. So the parser turns away every
message the rules forbid, takes every message they allow,
and reads from it the options the grammar derives.
Together with `Spec.print_parse` and `Spec.parse_wf`, which
say what it returns, this covers every input: whether the
parser takes it, and what it reads from it.

Single refusals, one for each rule above that turns a
message away, are also pinned as theorems (`Spec.rejects_*`
in the table below), each on one concrete input from the
test harness: the 240 byte minimum, the cookie, op, hlen,
a nonzero byte after the end byte, a length that runs past
the end, a code byte with no length byte, and the four
option 53 rules. Each is an instance of
`Spec.parse_accepts_iff`, kept as an example a reader can
check. The tests in `tests/` check the behaviour on many
more inputs (see The tests).

## The tests

`tests/run_tests.py` checks the tool against these rules on
4,104 inputs (seed 20261026) and writes the outcome to
`tests/TEST-RESULTS.md`. The committed record has 0
failures. Its oracles:

- The harness oracle, `oracle_parse`, a second reading of
  these rules in Python, settles the verdict on every input:
  the tool's answer must be the oracle's, byte for byte.
- Scapy 2.8.0 built ten of the messages with its BOOTP and
  DHCP layers; they are stored in `tests/scapy-packets.txt`.
- Wireshark's DHCP/BOOTP dissector, TShark 4.2.2, reads all
  4,090 messages among the inputs, the ones the tool takes
  and the ones it turns away, each written by the harness as
  the UDP payload of an Ethernet/IPv4/UDP frame in a pcap
  file. For a message the tool takes, Wireshark must show
  the fixed fields, the cookie, the options (code, length,
  value), the end option and the message type as the tool
  reads them; for every message, each Malformed Packet and
  expert error must be one the harness finds in the bytes
  by following Wireshark 4.2.2's own checks, and the other
  way round. Where Wireshark reads a message differently
  from these rules on purpose, the difference is a named
  one, counted only when the harness finds its reason in the
  message. Wireshark agrees on 2,056 messages: 635 the tool
  takes, and 1,421 the tool turns away where Wireshark stops
  with an exception at the same rule or finds no payload.
  The other 2,034 differ only under named differences, with
  these counts (a message can fall under more than one):
  no end byte (no-end) 527; option 52 overload (overload)
  105; an option other than 53 whose value fails Wireshark's
  check for it (option-value) 1,056; hlen 0 (hlen-0) 128;
  secs that look little endian (secs-le) 5; op not 1 or 2
  (op) 392; hlen above 16 (hlen) 375; no cookie, read as
  plain BOOTP (no-cookie) 371; nonzero bytes after the end
  byte (after-end) 190; no option 53 (no-53) 58; option 53
  more than once (53-repeated) 106; option 53 longer than
  one byte (53-length) 54; types 9 to 18 (53-registered) 13;
  type 0 or above 18 (53-unknown) 104. The results file
  gives each reason in full.

The plan (issue #1) also names ISC DHCP and dnsmasq
captures as oracles. They are not used: neither program is
available in this environment and no capture from either is
at hand, so no capture corpus ran. They are the only oracle
the plan names that the tests do not use.

## The command-line tool

`Main.lean` is a small front end used by the tests. It reads
one request per line and prints one answer per line. A
request is the word `parse`, then optionally one space and
the message bytes as comma-separated decimal numbers (with
no numbers, the input is empty). The answer is `ok:` and
the comma-separated codes of the canonical reprint when the
message parses, or `none` when it is turned away. A
malformed request (an unknown operation, a field that is
not plain decimal digits, a code above 255, extra spaces)
prints `error`. A line may end in LF or CR LF.

## Properties and their theorems

Each property a reader can check in the page (`README.md`)
names its theorem. The theorems are stated in `Spec.lean`,
with the definitions they use besides the code (the
grammar `OptionArea`, the canonical option area
`canonArea`, the rules `FixedRules` and `TypeRule`, and
`WF` and its parts) in `Spec/Defs.lean`,
and proved in `Proofs/SpecProofs.lean`, resting on the
proofs in `Proofs/RoundTrip.lean`, where they are
`Dhcp.Proofs.parse_print`, `Dhcp.Proofs.print_parse`, and
`Dhcp.Proofs.parse_wf`, and in `Proofs/Accept.lean`, where
the last is `Dhcp.Proofs.parse_accepts_iff`. The refusal
theorems are single inputs, one for each named rejection
case in the test harness, so each row that starts
"Example, one input" is proved for that input only; the
rule it shows is proved in general by
`Spec.parse_accepts_iff`, and the tests in `tests/` cover
each rule on many more inputs. The
test DISCOVER is the harness's DISCOVER, the 250 byte
example request in `README.md`.

| Property | Theorem |
|----------|---------|
| Parsing the printed form of a well formed message gives the message back | `Spec.parse_print` |
| The option area of every input the parser takes is one the grammar derives, carrying exactly the options of the parsed message, and printing that message gives the canonical form of the input: the first 240 bytes as they stood, then the canonical option area carrying those options (`canonArea`), which is each option, in order, as its code byte, its length byte, and its value bytes, then exactly one end byte, with no pad bytes and nothing after the end byte | `Spec.print_parse` |
| Every message the parser takes is well formed | `Spec.parse_wf` |
| The parser takes an input, reading the options `os`, exactly when the input follows the fixed field rules, its option area derives `os` in the grammar, and `os` meets the option 53 rule | `Spec.parse_accepts_iff` |
| Example, one input: the test DISCOVER cut to 239 bytes is refused | `Spec.rejects_short_message` |
| Example, one input: the test DISCOVER with its third cookie byte set to 100 is refused | `Spec.rejects_wrong_cookie` |
| Example, one input: a message whose option 55 claims ten value bytes, with three left, is refused | `Spec.rejects_option_overrun` |
| Example, one input: a message whose last byte is the code of option 55, with no length byte after it, is refused | `Spec.rejects_code_last_byte` |
| Example, one input: a message with option 55 and no option 53 is refused | `Spec.rejects_no_option_53` |
| Example, one input: a message whose only option 53 has length 2 is refused | `Spec.rejects_option_53_length_2` |
| Example, one input: a message whose only option 53 has value 0 is refused | `Spec.rejects_option_53_value_0` |
| Example, one input: a message whose only option 53 has value 9, DHCPFORCERENEW, is refused | `Spec.rejects_option_53_value_9` |
| Example, one input: a message with two option 53 items is refused | `Spec.rejects_option_53_twice` |
| Example, one input: the test DISCOVER with op 3 is refused | `Spec.rejects_op_3` |
| Example, one input: the test DISCOVER with hlen 17 is refused | `Spec.rejects_hlen_17` |
| Example, one input: the test DISCOVER with a 1 after its end byte is refused | `Spec.rejects_nonzero_after_end` |
