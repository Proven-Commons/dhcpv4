/-
  The DHCPv4 message data model and the canonical printer.

  A message is the fixed fields of RFC 2131 section 2, in the
  BOOTP legacy layout, then the magic cookie, then the options
  of RFC 2132 read as code, length, value items.

  The fixed fields are 236 bytes: op, htype, hlen, and hops at
  one byte each; xid at four; secs and flags at two each; the
  four addresses ciaddr, yiaddr, siaddr, and giaddr at four
  each; chaddr at sixteen; sname at sixty four; and file at
  one hundred twenty eight. The cookie is the four bytes 99,
  130, 83, 99. Options follow it.

  Numbers are held as plain natural numbers, not as fixed
  width types. chaddr is held as the full sixteen bytes as
  they stand on the wire, not cut down to hlen: the printer
  must give the wire bytes back, and a cut would lose bytes
  the message carried. sname and file are likewise held as
  their full fixed size byte blocks; what the bytes mean,
  such as where a name ends inside sname, is not read in this
  slice.

  An option is a code and its value bytes. Code 0 is the pad
  byte and code 255 the end byte, so neither is held as an
  option. Pad bytes are not held at all: the printer writes
  none, so a message with pads and the same message without
  parse to the same value.
-/

namespace Dhcp

/-- One option: a code and its value bytes. The code is held
    as a number; in a well formed message it runs from 1 to
    254. -/
abbrev DhcpOption := Nat × List UInt8

/-- The fixed fields of a message, in wire order. op, htype,
    hlen, and hops are one byte values; secs and flags are two
    byte values; xid and the four addresses are four byte
    values; chaddr, sname, and file are byte blocks of
    sixteen, sixty four, and one hundred twenty eight bytes. -/
structure Fixed where
  /-- 1 for a request (BOOTREQUEST), 2 for a reply
      (BOOTREPLY). -/
  op : Nat
  /-- The hardware address type. Carried unchecked. -/
  htype : Nat
  /-- The hardware address length, at most 16 in a well
      formed message. -/
  hlen : Nat
  /-- Relay hop count. Carried unchecked. -/
  hops : Nat
  /-- The transaction identifier, a four byte value. -/
  xid : Nat
  /-- Seconds since the client began, a two byte value. -/
  secs : Nat
  /-- Flags, a two byte value; the top bit is the broadcast
      flag. Carried unchecked in this slice. -/
  flags : Nat
  /-- The client address, a four byte value. -/
  ciaddr : Nat
  /-- The address offered or assigned to the client. -/
  yiaddr : Nat
  /-- The server address. -/
  siaddr : Nat
  /-- The relay agent (gateway) address. -/
  giaddr : Nat
  /-- The client hardware address: the full sixteen bytes. -/
  chaddr : List UInt8
  /-- The server host name field: the full sixty four bytes,
      contents not read in this slice. -/
  sname : List UInt8
  /-- The boot file name field: the full one hundred twenty
      eight bytes, contents not read in this slice. -/
  file : List UInt8
  deriving DecidableEq, Repr

/-- A message: the fixed fields and the option list, in wire
    order. -/
structure Message where
  fixed : Fixed
  options : List DhcpOption
  deriving DecidableEq, Repr

/-- A value as two bytes, big endian. The value is taken
    modulo 2^16; callers only pass values below that. -/
def be16 (n : Nat) : List UInt8 :=
  [ (n / 256).toUInt8, n.toUInt8 ]

/-- The value of two bytes read big endian. -/
def u16 (a b : UInt8) : Nat :=
  a.toNat * 256 + b.toNat

/-- A value as four bytes, big endian. The value is taken
    modulo 2^32; callers only pass values below that. -/
def be32 (n : Nat) : List UInt8 :=
  [ (n / 16777216).toUInt8, (n / 65536).toUInt8,
    (n / 256).toUInt8, n.toUInt8 ]

/-- The value of four bytes read big endian. -/
def u32 (a b c d : UInt8) : Nat :=
  a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat

/-- The magic cookie between the fixed fields and the
    options: 99, 130, 83, 99. -/
def cookie : List UInt8 := [99, 130, 83, 99]

/-- The fixed fields in printed form: the 236 field bytes,
    then the cookie. -/
def printFixed (f : Fixed) : List UInt8 :=
  [ f.op.toUInt8, f.htype.toUInt8, f.hlen.toUInt8,
    f.hops.toUInt8 ] ++
  be32 f.xid ++ be16 f.secs ++ be16 f.flags ++
  be32 f.ciaddr ++ be32 f.yiaddr ++ be32 f.siaddr ++
  be32 f.giaddr ++
  f.chaddr ++ f.sname ++ f.file ++ cookie

/-- The options in printed form: each as a code byte, a
    length byte, and its value bytes, then the end byte 255.
    No pad bytes are written, and exactly one end byte is. -/
def printOptions : List DhcpOption → List UInt8
  | [] => [255]
  | (c, v) :: os => (c.toUInt8 :: v.length.toUInt8 :: v) ++
      printOptions os

/-- A message in printed form. -/
def print (m : Message) : List UInt8 :=
  printFixed m.fixed ++ printOptions m.options

/-- Well formed fixed fields: op is 1 or 2, hlen fits the
    sixteen byte chaddr field, the other numbers fit their
    widths, and the three byte blocks hold their full
    lengths. -/
def WFFixed (f : Fixed) : Prop :=
  (f.op = 1 ∨ f.op = 2) ∧ f.htype < 256 ∧ f.hlen ≤ 16 ∧
  f.hops < 256 ∧
  f.xid < 4294967296 ∧ f.secs < 65536 ∧ f.flags < 65536 ∧
  f.ciaddr < 4294967296 ∧ f.yiaddr < 4294967296 ∧
  f.siaddr < 4294967296 ∧ f.giaddr < 4294967296 ∧
  f.chaddr.length = 16 ∧ f.sname.length = 64 ∧
  f.file.length = 128

/-- Well formed options: every code runs from 1 to 254,
    every value fits one length byte, and option 53, the
    message type, stands exactly once, with a one byte value
    from 1 to 8. -/
def WFOptions (os : List DhcpOption) : Prop :=
  (∀ o ∈ os, 1 ≤ o.1 ∧ o.1 ≤ 254 ∧ o.2.length ≤ 255) ∧
  ∃ t : UInt8, os.filter (fun o => o.1 == 53) = [(53, [t])] ∧
    1 ≤ t.toNat ∧ t.toNat ≤ 8

/-- A well formed message: well formed fixed fields and well
    formed options. -/
def WF (m : Message) : Prop :=
  WFFixed m.fixed ∧ WFOptions m.options

end Dhcp
