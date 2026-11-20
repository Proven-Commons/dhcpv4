/-
  Which inputs the parser takes: exactly those that follow the
  rules of `SPEC.md`, as `Spec/Defs.lean` writes them. The
  rules are the fixed field rules on the first 240 bytes
  (`FixedRules`), an option area the grammar derives
  (`OptionArea`), and the option 53 rule on the options that
  area carries (`TypeRule`).

  - `rules_of_parse`: an input the parser takes, with the
    options it read, follows every rule. The fixed field
    rules come from the read fields printing back to the
    first 240 bytes, the grammar from `parseOptionsGo_area`,
    and the option 53 rule from the check.
  - `parse_of_rules`: an input that follows every rule is
    taken, with the options the grammar derives. The fixed
    fields read through, since the first 240 bytes are long
    enough and op, hlen and the cookie pass; the option
    reader follows any derivation of the grammar
    (`area_parseOptionsGo`); and the check passes.
-/

import Dhcp
import Spec.Defs
import Proofs.RoundTrip

namespace Dhcp.Proofs

open Dhcp

/-! ## The option reader follows the grammar -/

/-- An option area the grammar derives is read by the option
    reader, given more fuel than the area has bytes, to the
    options the derivation carries. Each constructor is one
    step of the reader. -/
theorem area_parseOptionsGo {bs : List UInt8}
    {os : List DhcpOption} (h : OptionArea bs os) :
    ∀ fuel, bs.length < fuel → parseOptionsGo fuel bs = some os := by
  induction h with
  | stop =>
    intro fuel hf
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    rfl
  | finish hz =>
    intro fuel hf
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    rw [parseOptionsGo_step,
      ite_eq_right (by decide : ¬ ((255 : UInt8) = 0)),
      ite_eq_left rfl,
      ite_eq_left (List.all_eq_true.mpr fun x hx => by
        simp [hz x hx])]
  | pad h ih =>
    intro fuel hf
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    rw [parseOptionsGo_step, ite_eq_left rfl]
    exact ih k (by simp only [List.length_cons] at hf; omega)
  | item h0 h255 hlen h ih =>
    intro fuel hf
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    rw [parseOptionsGo_step_cons, ite_eq_right h0,
      ite_eq_right h255, ← hlen, List.take_left, ite_eq_left rfl,
      List.drop_left, ih k (by
        simp only [List.length_cons, List.length_append] at hf
        omega)]
    rfl

/-- An option area the grammar derives is read to the options
    the derivation carries, at the top level. -/
theorem area_parseOptions {bs : List UInt8}
    {os : List DhcpOption} (h : OptionArea bs os) :
    parseOptions bs = some os :=
  area_parseOptionsGo h _ (Nat.lt_succ_self _)

/-! ## The option 53 rule and the check -/

/-- Options that meet the option 53 rule pass the check. -/
theorem check53_of_TypeRule {os : List DhcpOption}
    (h : TypeRule os) : check53 os = true := by
  obtain ⟨t, hfilter, h1, h8⟩ := h
  unfold check53
  rw [hfilter]
  show decide (1 ≤ t.toNat ∧ t.toNat ≤ 8) = true
  rw [decide_eq_true_eq]
  exact ⟨h1, h8⟩

/-! ## The fixed fields read through -/

/-- A block read when there are enough bytes. -/
theorem withBytes_of_le {α : Type} {n : Nat} {bs : List UInt8}
    (k : List UInt8 → List UInt8 → Option α)
    (h : n ≤ bs.length) :
    withBytes n bs k = k (bs.take n) (bs.drop n) := by
  unfold withBytes
  rw [ite_eq_left (by rw [List.length_take]; omega)]

/-- A cookie read when the next four bytes are the cookie. -/
theorem withCookie_of {α : Type} {bs : List UInt8}
    (k : List UInt8 → Option α) (h : bs.take 4 = cookie) :
    withCookie bs k = k (bs.drop 4) := by
  unfold withCookie
  rw [ite_eq_left h]

/-- The first 240 bytes of an input that follows the fixed
    field rules read as well formed fixed fields, and the read
    goes on with the bytes after them. -/
theorem parseFixed_of_rules {bs : List UInt8}
    (h : FixedRules bs) :
    ∃ f, parseFixed bs = some (f, bs.drop 240) := by
  obtain ⟨hlen, hop, hhlen, hck⟩ := h
  rcases bs with
    _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5,
    _ | ⟨b6, _ | ⟨b7, _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11,
    _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | ⟨b16, _ | ⟨b17,
    _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27,
    rest⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try
    (simp only [List.length_cons, List.length_nil] at hlen; omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hop hhlen
  simp only [List.length_cons] at hlen
  have hck' : (((rest.drop 16).drop 64).drop 128).take 4 = cookie := by
    simp only [List.drop_drop]
    exact hck
  have hop' : b0.toNat = 1 ∨ b0.toNat = 2 := by
    rcases hop with e | e <;> rw [e] <;> decide
  refine ⟨⟨b0.toNat, b1.toNat, b2.toNat, b3.toNat,
    u32 b4 b5 b6 b7, u16 b8 b9, u16 b10 b11, u32 b12 b13 b14 b15,
    u32 b16 b17 b18 b19, u32 b20 b21 b22 b23, u32 b24 b25 b26 b27,
    rest.take 16, (rest.drop 16).take 64,
    ((rest.drop 16).drop 64).take 128⟩, ?_⟩
  rw [parseFixed.eq_1, withU8_cons, withU8_cons, withU8_cons,
    withU8_cons, withU32_cons, withU16_cons, withU16_cons,
    withU32_cons, withU32_cons, withU32_cons, withU32_cons,
    withBytes_of_le _ (by omega),
    withBytes_of_le _ (by rw [List.length_drop]; omega),
    withBytes_of_le _ (by rw [List.length_drop, List.length_drop]; omega),
    withCookie_of _ hck', ite_eq_left ⟨hop', hhlen⟩]
  simp only [List.drop_drop]
  rfl

/-! ## Both directions -/

/-- An input the parser takes, with the options it read,
    follows every rule. -/
theorem rules_of_parse {bs : List UInt8} {f : Fixed}
    {os : List DhcpOption} (h : parse bs = some ⟨f, os⟩) :
    FixedRules bs ∧ OptionArea (bs.drop 240) os ∧ TypeRule os := by
  have harea := (print_parse h).1
  have hwf := parse_wf h
  refine ⟨?_, harea, hwf.2.2⟩
  simp only [parse] at h
  obtain ⟨⟨f', rest⟩, hf, _⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hfix, hc16, hs64, hf128⟩ := parseFixed_inv hf
  obtain ⟨hop, _, hhlen, _⟩ := parseFixed_wf hf
  have hlen := printFixed_length hc16 hs64 hf128
  subst hfix
  -- printFixed is the 236 field bytes, then the cookie.
  have hpre : (printFixed f' ++ rest).drop 236 = cookie ++ rest := by
    have e : printFixed f' ++ rest =
        ([ f'.op.toUInt8, f'.htype.toUInt8, f'.hlen.toUInt8,
          f'.hops.toUInt8 ] ++
        be32 f'.xid ++ be16 f'.secs ++ be16 f'.flags ++
        be32 f'.ciaddr ++ be32 f'.yiaddr ++ be32 f'.siaddr ++
        be32 f'.giaddr ++ f'.chaddr ++ f'.sname ++ f'.file) ++
        (cookie ++ rest) := by
      simp only [printFixed, List.append_assoc]
    rw [e]
    apply List.drop_left'
    simp only [be16, be32, List.length_append, List.length_cons,
      List.length_nil, hc16, hs64, hf128]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.length_append, hlen]; omega
  · show f'.op.toUInt8 = 1 ∨ f'.op.toUInt8 = 2
    rcases hop with e | e <;> rw [e] <;> decide
  · show (f'.hlen.toUInt8).toNat ≤ 16
    rw [toUInt8_toNat]
    omega
  · rw [hpre]
    exact List.take_left' rfl

/-- An input that follows every rule is taken, with the
    options the grammar derives from its option area. -/
theorem parse_of_rules {bs : List UInt8} {os : List DhcpOption}
    (hf : FixedRules bs) (ha : OptionArea (bs.drop 240) os)
    (ht : TypeRule os) : ∃ f, parse bs = some ⟨f, os⟩ := by
  obtain ⟨f, hpf⟩ := parseFixed_of_rules hf
  refine ⟨f, ?_⟩
  simp only [parse]
  rw [hpf]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [area_parseOptions ha]
  simp only [Option.bind_some]
  rw [ite_eq_left (check53_of_TypeRule ht)]

/-- The parser takes an input, reading the options `os`,
    exactly when the input follows the fixed field rules, its
    option area derives `os` in the grammar, and `os` meets
    the option 53 rule. -/
theorem parse_accepts_iff {bs : List UInt8} {os : List DhcpOption} :
    (∃ f, parse bs = some ⟨f, os⟩) ↔
      FixedRules bs ∧ OptionArea (bs.drop 240) os ∧ TypeRule os := by
  constructor
  · rintro ⟨f, h⟩
    exact rules_of_parse h
  · rintro ⟨hf, ha, ht⟩
    exact parse_of_rules hf ha ht

end Dhcp.Proofs
