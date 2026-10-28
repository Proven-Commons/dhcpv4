/-
  The DHCPv4 message parser. It reads a list of bytes and
  returns the message, or `none` when the bytes break any of
  the rules the plan states:

  - The fixed fields take 236 bytes and the magic cookie
    four more, so a message shorter than 240 bytes is turned
    away, and so is one whose cookie is not 99, 130, 83, 99.
    The cookie is what marks the tail as DHCP options rather
    than old vendor extension bytes.
  - op must be 1 or 2. hlen must be at most 16, the size of
    the chaddr field; a longer hardware address could not
    fit. htype, hops, secs, and flags are carried unchecked.
  - Options are read as a code byte, a length byte, and that
    many value bytes. Code 0 is a pad byte and is skipped; it
    is not part of the message value. Code 255 is the end
    byte: it stops the list, and every byte after it must be
    zero padding, as senders pad messages to a minimum size
    with zeros. With no end byte, the options must run
    exactly to the end of the input. A length that runs past
    the end of the message turns the message away, and so
    does a code byte with no length byte after it.
  - Option 53, the message type, must stand exactly once.
    Its length must be 1, and its value must run from 1 to 8:
    DISCOVER, OFFER, REQUEST, DECLINE, ACK, NAK, RELEASE, or
    INFORM. Any other option may repeat and is carried as its
    code and value bytes; no other option's value is read in
    this slice.

  `parseOptionsGo` takes a fuel count, one more than the
  length of the input at the top level, which is always
  enough, since every step takes at least one byte. A hostile
  input is rejected, never looped on.
-/

import Dhcp.Value

namespace Dhcp

/-- Read one byte as a value, with the rest of the input. -/
def getU8 : List UInt8 → Option (Nat × List UInt8)
  | b :: rest => some (b.toNat, rest)
  | [] => none

/-- Read two bytes as a big endian value, with the rest of
    the input. Fewer than two bytes gives `none`. -/
def getU16 : List UInt8 → Option (Nat × List UInt8)
  | a :: b :: rest => some (u16 a b, rest)
  | _ => none

/-- Read four bytes as a big endian value, with the rest of
    the input. Fewer than four bytes gives `none`. -/
def getU32 : List UInt8 → Option (Nat × List UInt8)
  | a :: b :: c :: d :: rest => some (u32 a b c d, rest)
  | _ => none

/-- Read `n` bytes as a block, with the rest of the input.
    Fewer than `n` bytes gives `none`. -/
def getBytes (n : Nat) (bs : List UInt8) :
    Option (List UInt8 × List UInt8) :=
  if (bs.take n).length = n then some (bs.take n, bs.drop n)
  else none

/-- Read the magic cookie. Returns the rest of the input, or
    `none` when the next four bytes are not 99, 130, 83, 99. -/
def getCookie (bs : List UInt8) : Option (List UInt8) :=
  if bs.take 4 = cookie then some (bs.drop 4) else none

/-- Read the fixed fields and the cookie. Returns the fields
    and the input after the cookie. The field checks are op
    in {1, 2} and hlen at most 16; a failed check gives
    `none`. -/
def parseFixed (bs : List UInt8) : Option (Fixed × List UInt8) :=
  getU8 bs >>= fun (op, r1) =>
  getU8 r1 >>= fun (htype, r2) =>
  getU8 r2 >>= fun (hlen, r3) =>
  getU8 r3 >>= fun (hops, r4) =>
  getU32 r4 >>= fun (xid, r5) =>
  getU16 r5 >>= fun (secs, r6) =>
  getU16 r6 >>= fun (flags, r7) =>
  getU32 r7 >>= fun (ciaddr, r8) =>
  getU32 r8 >>= fun (yiaddr, r9) =>
  getU32 r9 >>= fun (siaddr, r10) =>
  getU32 r10 >>= fun (giaddr, r11) =>
  getBytes 16 r11 >>= fun (chaddr, r12) =>
  getBytes 64 r12 >>= fun (sname, r13) =>
  getBytes 128 r13 >>= fun (file, r14) =>
  getCookie r14 >>= fun r15 =>
  if (op = 1 ∨ op = 2) ∧ hlen ≤ 16 then
    some (⟨op, htype, hlen, hops, xid, secs, flags, ciaddr,
      yiaddr, siaddr, giaddr, chaddr, sname, file⟩, r15)
  else none

/-- Read the options from the front of the input, taking the
    whole of it. `fuel` bounds the steps. Pad bytes are
    skipped. The end byte stops the list, and the bytes after
    it must all be zero. With no end byte the options must run
    exactly to the end of the input. -/
def parseOptionsGo : Nat → List UInt8 → Option (List DhcpOption)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, b :: rest =>
    if b = 0 then parseOptionsGo fuel rest
    else if b = 255 then
      if rest.all (fun x => x == 0) then some [] else none
    else
      match rest with
      | [] => none
      | len :: rest' =>
        if (rest'.take len.toNat).length = len.toNat then
          (parseOptionsGo fuel (rest'.drop len.toNat)).map
            (fun os => (b.toNat, rest'.take len.toNat) :: os)
        else none

/-- Read the options, with enough fuel for the whole input. -/
def parseOptions (bs : List UInt8) : Option (List DhcpOption) :=
  parseOptionsGo (bs.length + 1) bs

/-- The option 53 check: exactly one option carries code 53,
    its value is one byte, and that byte runs from 1 to 8. -/
def check53 (os : List DhcpOption) : Bool :=
  match os.filter (fun o => o.1 == 53) with
  | [(_, [t])] => decide (1 ≤ t.toNat ∧ t.toNat ≤ 8)
  | _ => false

/-- Parse a whole message: the fixed fields and the cookie,
    then the options, then the option 53 check. -/
def parse (bs : List UInt8) : Option Message :=
  parseFixed bs >>= fun (f, rest) =>
  parseOptions rest >>= fun os =>
  if check53 os then some ⟨f, os⟩ else none

end Dhcp
