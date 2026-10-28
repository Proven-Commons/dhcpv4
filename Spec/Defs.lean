/-
  The definitions the statements in `Spec.lean` use besides
  the code under proof: what a well formed message is, and
  the canonical form of an option area. Neither the parser
  nor the printer uses them; they only give the statements
  their meaning. So they are part of the specification, with
  `Spec.lean` and `SPEC.md`, and the approval hash covers
  their text, not only their names.

  - `WFFixed`, `WFOptions` and `WF`: a well formed message,
    the predicate `Spec.parse_print` assumes and
    `Spec.parse_wf` concludes.
  - `canonOptionsGo` and `canonOptions`: the canonical form
    of an option area, which `Spec.print_parse` is stated
    with.
-/

import Dhcp.Value

namespace Dhcp

/-- The canonical form of an option area: the options as the
    printer writes them, pad bytes dropped, trailing zeros
    after the end byte dropped, exactly one end byte, and an
    end byte supplied when the area had none. Defined with
    the same fuel shape as the reader. The `print_parse`
    statement is stated with it. -/
def canonOptionsGo : Nat → List UInt8 → List UInt8
  | 0, _ => [255]
  | _ + 1, [] => [255]
  | fuel + 1, b :: rest =>
    if b = 0 then canonOptionsGo fuel rest
    else if b = 255 then [255]
    else
      match rest with
      | [] => [255]
      | len :: rest' => b :: len :: (rest'.take len.toNat) ++
          canonOptionsGo fuel (rest'.drop len.toNat)

/-- The canonical form of an option area. -/
def canonOptions (bs : List UInt8) : List UInt8 :=
  canonOptionsGo (bs.length + 1) bs

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
