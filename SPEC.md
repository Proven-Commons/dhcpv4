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
parser does and what the tests check.

- No end byte. RFC 2131 section 4.1 says "The last option
  must always be the 'end' option." This parser is more
  lenient: an option area with no end byte is taken when
  its last item ends exactly at the last input byte, and
  the reprint adds the end byte. Scapy 2.8.0 also decodes
  such a message; other decoders may refuse it.
- Bytes after the end byte. RFC 2132 section 3.2 says only
  that the octets after the end option "should be filled
  with pad options". This parser is stricter: any nonzero
  byte after the end byte turns the message away, so a
  message another decoder takes (Scapy 2.8.0 decodes it and
  keeps the trailing bytes) is refused here.
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
  reader that follows option 52 would see two.
- Repeated options are not joined. RFC 3396 section 7 (and
  RFC 2131 section 4.1 before it) asks a reader to join the
  values of repeated options into one. This slice keeps
  each repeat as its own item, in wire order, and the
  reprint writes them back the same way. For option 53 the
  exactly once rule applies to the items as they stand: a
  type split over two items, such as `53 0` then `53 1 1`,
  turns the message away, where a reader that joins them
  would see one type, DISCOVER.
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
  DHCPFORCERENEW on one input.

## Printing and the canonical form

The printer writes the fixed fields as they stood, the
cookie, then each option as a code byte, a length byte, and
its value bytes, then exactly one end byte, 255. It writes
no pad bytes.

So a message that parses prints to a canonical form: the
first 240 bytes as they stood, then the options with pad
bytes anywhere among them dropped, zero padding after the
end byte dropped, exactly one end byte written, and an end
byte supplied when the input had none. A message already in
canonical form prints to itself, byte for byte.

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
printing the parsed message gives the canonical form of
the input, as spelled out above: the first 240 bytes as
they stood, then the canonical option area (the theorem
states this with the `canonOptions` function, which walks
the option area dropping pads and trailing zeros and ends
it with one end byte).

`Spec.parse_wf`: every message the parser takes is well
formed, in the sense spelled out under `Spec.parse_print`.
The statement is about the message the parser returns, not
about the input bytes on their own. A parser that refuses
every input also meets it; `Spec.parse_print` rules that
parser out.

That the parser accepts every message these rules allow is
not proved. That it turns away every message they forbid is
proved only as far as `Spec.parse_wf` reaches: whatever it
returns is well formed. Single refusals, one for each rule
above that turns a message away, are pinned as theorems
(`Spec.rejects_*` in the table below), each on one concrete
input from the test harness: the 240 byte minimum, the
cookie, op, hlen, a nonzero byte after the end byte, a
length that runs past the end, a code byte with no length
byte, and the four option 53 rules. The readings that take
an input, such as an option area with no end byte or with
no items, have no theorem. The differential tests in
`tests/` check the behaviour on many more inputs.

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
names its theorem. The theorems are stated in `Spec.lean`
and proved in `Proofs/SpecProofs.lean`, resting on the
proofs in `Proofs/RoundTrip.lean`, where they are
`Dhcp.Proofs.parse_print`, `Dhcp.Proofs.print_parse`, and
`Dhcp.Proofs.parse_wf`. The refusal theorems are single
inputs, one for each named rejection case in the test
harness, so each row that starts "Example, one input" is
proved for that input only, not as a general rule; the
tests in `tests/` cover each rule on many more inputs. The
test DISCOVER is the harness's DISCOVER, the 250 byte
example request in `README.md`.

| Property | Theorem |
|----------|---------|
| Parsing the printed form of a well formed message gives the message back | `Spec.parse_print` |
| Printing a message the parser took gives the canonical form of the bytes it was read from | `Spec.print_parse` |
| Every message the parser takes is well formed | `Spec.parse_wf` |
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
