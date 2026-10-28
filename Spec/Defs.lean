/-
  The definitions the statements in `Spec.lean` use besides
  the code under proof: the rules an input must follow, and
  what a well formed message is. Neither the parser nor the
  printer uses them; they only give the statements their
  meaning. So they are part of the specification, with
  `Spec.lean` and `SPEC.md`, and the approval hash covers
  their text, not only their names.

  - `OptionArea`: the grammar of an option area, which
    `Spec.print_parse` and `Spec.parse_accepts_iff` are
    stated with. The canonical form of an area is the printed
    form of the options it derives.
  - `FixedRules` and `TypeRule`: the fixed field rules on the
    first 240 bytes, and the option 53 rule on the options,
    which `Spec.parse_accepts_iff` is stated with.
  - `WFFixed`, `WFOptions` and `WF`: a well formed message,
    the predicate `Spec.parse_print` assumes and
    `Spec.parse_wf` concludes.
-/

import Dhcp.Value

namespace Dhcp

/-- The option area grammar of `SPEC.md` (The options), as a
    relation between the bytes of an option area, everything
    after the cookie, and the options those bytes carry. An
    area is read from the front, one piece at a time, and each
    constructor is one way an area may go on. Nothing else is
    an option area: a code byte with no length byte after it,
    a length that runs past the end, and a nonzero byte after
    the end byte have no derivation. The grammar is written
    from the rules, not from the parser: it has no fuel, and
    it says what an area is, not how to read one. -/
inductive OptionArea : List UInt8 → List DhcpOption → Prop where
  /-- The input ends after the last item, with no end byte.
      No more options. -/
  | stop : OptionArea [] []
  /-- The end byte, 255, then only zero bytes, which are
      padding. No more options. -/
  | finish {zeros : List UInt8} (hz : ∀ z ∈ zeros, z = 0) :
      OptionArea (255 :: zeros) []
  /-- A pad byte, 0, which carries nothing, then the rest of
      the area. -/
  | pad {rest : List UInt8} {os : List DhcpOption}
      (h : OptionArea rest os) : OptionArea (0 :: rest) os
  /-- An item: a code byte, any byte but 0 and 255, a length
      byte, exactly that many value bytes, then the rest of the
      area. The item carries the option of that code and those
      value bytes. -/
  | item {code len : UInt8} {value rest : List UInt8}
      {os : List DhcpOption} (h0 : code ≠ 0) (h255 : code ≠ 255)
      (hlen : value.length = len.toNat) (h : OptionArea rest os) :
      OptionArea (code :: len :: (value ++ rest))
        ((code.toNat, value) :: os)

/-- The rules of `SPEC.md` (The fixed fields) on the bytes
    before the option area: there are at least 240 bytes; op,
    byte 0, is 1 or 2; hlen, byte 2, is at most 16; and bytes
    236 to 239 are the magic cookie, 99, 130, 83, 99. Every
    other byte of the first 240 is carried unchecked. -/
def FixedRules (bs : List UInt8) : Prop :=
  240 ≤ bs.length ∧
  (bs.getD 0 0 = 1 ∨ bs.getD 0 0 = 2) ∧
  (bs.getD 2 0).toNat ≤ 16 ∧
  (bs.drop 236).take 4 = [99, 130, 83, 99]

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

/-- The option 53 rule of `SPEC.md` (Option 53): option 53,
    the message type, stands exactly once among the options,
    with a one byte value from 1 to 8. -/
def TypeRule (os : List DhcpOption) : Prop :=
  ∃ t : UInt8, os.filter (fun o => o.1 == 53) = [(53, [t])] ∧
    1 ≤ t.toNat ∧ t.toNat ≤ 8

/-- Well formed options: every code runs from 1 to 254,
    every value fits one length byte, and the option 53 rule
    holds. -/
def WFOptions (os : List DhcpOption) : Prop :=
  (∀ o ∈ os, 1 ≤ o.1 ∧ o.1 ≤ 254 ∧ o.2.length ≤ 255) ∧
  TypeRule os

/-- A well formed message: well formed fixed fields and well
    formed options. -/
def WF (m : Message) : Prop :=
  WFFixed m.fixed ∧ WFOptions m.options

end Dhcp
