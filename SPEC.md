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
  INFORM.

Every other option is carried uninterpreted, as its code
and value bytes, in wire order. An option may repeat; the
repeats are kept in order. No other option's value is
checked in this slice: not its length against any per option
rule, and not its contents. That is the slice boundary.

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

`Dhcp.Proofs.parse_print`: for every well formed message,
parsing its printed form gives the message back.

Well formed means: op is 1 or 2; htype and hops fit one
byte; hlen is at most 16; xid and the four addresses fit
four bytes; secs and flags fit two bytes; chaddr, sname,
and file hold 16, 64, and 128 bytes; every option code runs
from 1 to 254; every option value fits one length byte; and
option 53 stands exactly once with a one byte value from 1
to 8.

`Dhcp.Proofs.print_parse`: for every byte list the parser
takes, printing the parsed message gives the canonical form
of the input, as spelled out above: the first 240 bytes as
they stood, then the canonical option area (the theorem
states this with the `canonOptions` function, which walks
the option area dropping pads and trailing zeros and ends
it with one end byte).

That the parser accepts every message these rules allow,
and turns away every message they forbid, is not proved.
The differential tests in `tests/` check that behaviour
instead.

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
