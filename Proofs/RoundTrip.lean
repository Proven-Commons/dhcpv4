/-
  The round trip proofs.

  Three claims are proved here: the plan's main claim, its
  mirror, and soundness:

  - `parse_print`: for every well formed message, parsing its
    printed form gives the message back.
  - `print_parse`: for every byte list the parser takes,
    the bytes after the first 240 are an option area the
    grammar `OptionArea` (in `Spec/Defs.lean`) derives,
    carrying the options read, and printing the parsed
    message gives the canonical form of the input: the first
    240 bytes as they stood (the fixed fields and the cookie
    stand unchanged under printing), then those options
    printed, with no pad bytes and exactly one end byte.
  - `parse_wf`: every message the parser takes is well
    formed, in the sense of `WF`.

  The steps: the two and four byte numbers read back as the
  values they were printed from, and printed numbers recover
  the bytes they were read from; the readers invert on
  printed forms and on read forms; the fixed fields invert
  both ways; the option reader inverts on printed options;
  and every option area the reader takes is one the grammar
  derives, with the options it read. For soundness, the
  read fixed fields, each option read, and the option 53 check
  each give their part of `WF`.
-/

import Dhcp
import Spec.Defs

namespace Dhcp.Proofs

open Dhcp

/-! ## Byte and number basics -/

/-- A byte printed from a number reads back as the number
    modulo 256. -/
theorem toUInt8_toNat (n : Nat) : (n.toUInt8).toNat = n % 256 := rfl

/-- A byte's value fits in 256. -/
theorem toNat_lt (b : UInt8) : b.toNat < 256 := UInt8.toNat_lt_size b

/-- A byte rebuilt from its value is the byte. -/
theorem toNat_toUInt8 (b : UInt8) : b.toNat.toUInt8 = b := by
  apply UInt8.toNat_inj.mp
  show (b.toNat.toUInt8).toNat = b.toNat
  rw [toUInt8_toNat]
  exact Nat.mod_eq_of_lt (toNat_lt b)

/-- Two bytes printed from a value below 2^16 read back as
    the value. -/
theorem u16_be16 (n : Nat) (h : n < 65536) :
    u16 (n / 256).toUInt8 n.toUInt8 = n := by
  simp only [u16, toUInt8_toNat]
  omega

/-- The bytes read as a two byte value print back to those
    bytes. -/
theorem be16_u16 (a b : UInt8) : be16 (u16 a b) = [a, b] := by
  have ha := toNat_lt a
  have hb := toNat_lt b
  have e1 : u16 a b / 256 = a.toNat := by
    simp only [u16]; omega
  have e2 : (u16 a b).toUInt8 = b := by
    apply UInt8.toNat_inj.mp
    show ((u16 a b).toUInt8).toNat = b.toNat
    rw [toUInt8_toNat]; simp only [u16]; omega
  simp only [be16, e1, e2, toNat_toUInt8]

/-- Four bytes printed from a value below 2^32 read back as
    the value. -/
theorem u32_be32 (n : Nat) (h : n < 4294967296) :
    u32 (n / 16777216).toUInt8 (n / 65536).toUInt8
      (n / 256).toUInt8 n.toUInt8 = n := by
  simp only [u32, toUInt8_toNat]
  omega

/-- The bytes read as a four byte value print back to those
    bytes. -/
theorem be32_u32 (a b c d : UInt8) :
    be32 (u32 a b c d) = [a, b, c, d] := by
  have ha := toNat_lt a
  have hb := toNat_lt b
  have hc := toNat_lt c
  have hd := toNat_lt d
  have e1 : u32 a b c d / 16777216 = a.toNat := by
    simp only [u32]; omega
  have e2 : (u32 a b c d / 65536).toUInt8 = b := by
    apply UInt8.toNat_inj.mp
    show ((u32 a b c d / 65536).toUInt8).toNat = b.toNat
    rw [toUInt8_toNat]; simp only [u32]; omega
  have e3 : (u32 a b c d / 256).toUInt8 = c := by
    apply UInt8.toNat_inj.mp
    show ((u32 a b c d / 256).toUInt8).toNat = c.toNat
    rw [toUInt8_toNat]; simp only [u32]; omega
  have e4 : (u32 a b c d).toUInt8 = d := by
    apply UInt8.toNat_inj.mp
    show ((u32 a b c d).toUInt8).toNat = d.toNat
    rw [toUInt8_toNat]; simp only [u32]; omega
  simp only [be32, e1, e2, e3, e4, toNat_toUInt8]

/-! ## The readers, on printed forms and on read forms

Each reader lemma is stated for any continuation `k`, so a
proof about the fixed part rewrites one reader at a time: the
continuation in the goal is matched as it stands, and what is
left is its body, applied to the field read. -/

/-- A printed two byte value, as its two bytes in front of
    what follows it. -/
theorem be16_append (n : Nat) (r : List UInt8) :
    be16 n ++ r = (n / 256).toUInt8 :: n.toUInt8 :: r := rfl

/-- A printed four byte value, as its four bytes in front of
    what follows it. -/
theorem be32_append (n : Nat) (r : List UInt8) :
    be32 n ++ r =
      (n / 16777216).toUInt8 :: (n / 65536).toUInt8 ::
        (n / 256).toUInt8 :: n.toUInt8 :: r := rfl

/-- One step of the one byte reader. -/
theorem withU8_cons {α : Type} (b : UInt8) (r : List UInt8)
    (k : Nat → List UInt8 → Option α) :
    withU8 (b :: r) k = k b.toNat r := rfl

/-- One step of the two byte reader. -/
theorem withU16_cons {α : Type} (a b : UInt8) (r : List UInt8)
    (k : Nat → List UInt8 → Option α) :
    withU16 (a :: b :: r) k = k (u16 a b) r := rfl

/-- One step of the four byte reader. -/
theorem withU32_cons {α : Type} (a b c d : UInt8)
    (r : List UInt8) (k : Nat → List UInt8 → Option α) :
    withU32 (a :: b :: c :: d :: r) k = k (u32 a b c d) r := rfl

/-- The two byte reader on a printed value reads the value. -/
theorem withU16_be16 {α : Type} {n : Nat} (h : n < 65536)
    (r : List UInt8) (k : Nat → List UInt8 → Option α) :
    withU16 (be16 n ++ r) k = k n r := by
  rw [be16_append, withU16_cons, u16_be16 n h]

/-- The four byte reader on a printed value reads the
    value. -/
theorem withU32_be32 {α : Type} {n : Nat} (h : n < 4294967296)
    (r : List UInt8) (k : Nat → List UInt8 → Option α) :
    withU32 (be32 n ++ r) k = k n r := by
  rw [be32_append, withU32_cons, u32_be32 n h]

/-- The block reader on a block of the length it asks for
    reads the block. -/
theorem withBytes_app {α : Type} {n : Nat} {v : List UInt8}
    (hv : v.length = n) (r : List UInt8)
    (k : List UInt8 → List UInt8 → Option α) :
    withBytes n (v ++ r) k = k v r := by
  unfold withBytes
  have ht : (v ++ r).take n = v := by
    rw [← hv]; exact List.take_left
  have hd : (v ++ r).drop n = r := by
    rw [← hv]; exact List.drop_left
  rw [ht, hd, ite_eq_left hv]

/-- The cookie reader on a printed cookie reads past it. -/
theorem withCookie_app {α : Type} (r : List UInt8)
    (k : List UInt8 → Option α) :
    withCookie (cookie ++ r) k = k r := by
  unfold withCookie
  have ht : (cookie ++ r).take 4 = cookie := List.take_left' rfl
  have hd : (cookie ++ r).drop 4 = r := List.drop_left' rfl
  rw [ht, hd, ite_eq_left rfl]

/-- A successful one byte read: the input was the byte and
    the rest, and the value fits a byte. -/
theorem withU8_inv {α : Type} {bs : List UInt8}
    {k : Nat → List UInt8 → Option α} {x : α}
    (h : withU8 bs k = some x) :
    ∃ n r, bs = n.toUInt8 :: r ∧ n < 256 ∧ k n r = some x := by
  cases bs with
  | nil =>
    have h0 : withU8 ([] : List UInt8) k = none := rfl
    rw [h0] at h
    cases h
  | cons b r =>
    rw [withU8_cons] at h
    exact ⟨b.toNat, r, by rw [toNat_toUInt8], toNat_lt b, h⟩

/-- A successful two byte read: the input was the printed
    value and the rest, and the value fits two bytes. -/
theorem withU16_inv {α : Type} {bs : List UInt8}
    {k : Nat → List UInt8 → Option α} {x : α}
    (h : withU16 bs k = some x) :
    ∃ n r, bs = be16 n ++ r ∧ n < 65536 ∧ k n r = some x := by
  cases bs with
  | nil =>
    have h0 : withU16 ([] : List UInt8) k = none := rfl
    rw [h0] at h
    cases h
  | cons a bs' =>
    cases bs' with
    | nil =>
      have h0 : withU16 [a] k = none := rfl
      rw [h0] at h
      cases h
    | cons b r =>
      rw [withU16_cons] at h
      refine ⟨u16 a b, r, ?_, ?_, h⟩
      · rw [be16_u16]
        rfl
      · have ha := toNat_lt a
        have hb := toNat_lt b
        simp only [u16]; omega

/-- A successful four byte read: the input was the printed
    value and the rest, and the value fits four bytes. -/
theorem withU32_inv {α : Type} {bs : List UInt8}
    {k : Nat → List UInt8 → Option α} {x : α}
    (h : withU32 bs k = some x) :
    ∃ n r, bs = be32 n ++ r ∧ n < 4294967296 ∧ k n r = some x := by
  cases bs with
  | nil =>
    have h0 : withU32 ([] : List UInt8) k = none := rfl
    rw [h0] at h
    cases h
  | cons a bs1 =>
    cases bs1 with
    | nil =>
      have h0 : withU32 [a] k = none := rfl
      rw [h0] at h
      cases h
    | cons b bs2 =>
      cases bs2 with
      | nil =>
        have h0 : withU32 [a, b] k = none := rfl
        rw [h0] at h
        cases h
      | cons c bs3 =>
        cases bs3 with
        | nil =>
          have h0 : withU32 [a, b, c] k = none := rfl
          rw [h0] at h
          cases h
        | cons d r =>
          rw [withU32_cons] at h
          refine ⟨u32 a b c d, r, ?_, ?_, h⟩
          · rw [be32_u32]
            rfl
          · have ha := toNat_lt a
            have hb := toNat_lt b
            have hc := toNat_lt c
            have hd := toNat_lt d
            simp only [u32]; omega

/-- A successful block read: the block holds `n` bytes, and
    the input was the block and the rest. -/
theorem withBytes_inv {α : Type} {n : Nat} {bs : List UInt8}
    {k : List UInt8 → List UInt8 → Option α} {x : α}
    (h : withBytes n bs k = some x) :
    ∃ v r, v.length = n ∧ bs = v ++ r ∧ k v r = some x := by
  unfold withBytes at h
  by_cases hc : (bs.take n).length = n
  · rw [ite_eq_left hc] at h
    exact ⟨bs.take n, bs.drop n, hc,
      (List.take_append_drop n bs).symm, h⟩
  · rw [ite_eq_right hc] at h
    cases h

/-- A successful cookie read: the input was the cookie and
    the rest. -/
theorem withCookie_inv {α : Type} {bs : List UInt8}
    {k : List UInt8 → Option α} {x : α}
    (h : withCookie bs k = some x) :
    ∃ r, bs = cookie ++ r ∧ k r = some x := by
  unfold withCookie at h
  by_cases hc : bs.take 4 = cookie
  · rw [ite_eq_left hc] at h
    refine ⟨bs.drop 4, ?_, h⟩
    calc bs = bs.take 4 ++ bs.drop 4 :=
        (List.take_append_drop 4 bs).symm
    _ = cookie ++ bs.drop 4 := by rw [hc]
  · rw [ite_eq_right hc] at h
    cases h

/-! ## The fixed fields -/

/-- The printed fixed fields are 240 bytes: 236 of fields and
    the four cookie bytes. -/
theorem printFixed_length {f : Fixed}
    (hc : f.chaddr.length = 16) (hs : f.sname.length = 64)
    (hf : f.file.length = 128) :
    (printFixed f).length = 240 := by
  simp only [printFixed, be16, be32, cookie, List.length_append,
    List.length_cons, List.length_nil, hc, hs, hf]

/-- The printed fixed fields read back as the fields, over
    any bytes that follow them. The proof reads the fields one
    reader at a time; each step is a rewrite with a reader
    lemma, so no kernel has to evaluate the parser. -/
theorem parseFixed_printFixed {f : Fixed} (hw : WFFixed f)
    (rest : List UInt8) :
    parseFixed (printFixed f ++ rest) = some (f, rest) := by
  obtain ⟨hop, hhtype, hhlen, hhops, hxid, hsecs, hflags,
    hci, hyi, hsi, hgi, hch, hsn, hfi⟩ := hw
  have hop' : (f.op.toUInt8).toNat = f.op := by
    rw [toUInt8_toNat]
    exact Nat.mod_eq_of_lt (by rcases hop with h | h <;> omega)
  have hhtype' : (f.htype.toUInt8).toNat = f.htype := by
    rw [toUInt8_toNat]; exact Nat.mod_eq_of_lt hhtype
  have hhlen' : (f.hlen.toUInt8).toNat = f.hlen := by
    rw [toUInt8_toNat]; exact Nat.mod_eq_of_lt (by omega)
  have hhops' : (f.hops.toUInt8).toNat = f.hops := by
    rw [toUInt8_toNat]; exact Nat.mod_eq_of_lt hhops
  have key : printFixed f ++ rest =
      f.op.toUInt8 :: f.htype.toUInt8 :: f.hlen.toUInt8 ::
      f.hops.toUInt8 ::
      (be32 f.xid ++ (be16 f.secs ++ (be16 f.flags ++
      (be32 f.ciaddr ++ (be32 f.yiaddr ++ (be32 f.siaddr ++
      (be32 f.giaddr ++ (f.chaddr ++ (f.sname ++
      (f.file ++ (cookie ++ rest))))))))))) := by
    simp only [printFixed, ← List.append_assoc, List.cons_append,
      List.nil_append]
  rw [key, parseFixed.eq_1, withU8_cons, withU8_cons, withU8_cons,
    withU8_cons, withU32_be32 hxid, withU16_be16 hsecs,
    withU16_be16 hflags, withU32_be32 hci, withU32_be32 hyi,
    withU32_be32 hsi, withU32_be32 hgi, withBytes_app hch,
    withBytes_app hsn, withBytes_app hfi, withCookie_app,
    hop', hhtype', hhlen', hhops', ite_eq_left ⟨hop, hhlen⟩]

/-- The fixed fields a successful read gives print back to
    the bytes they were read from, and its three byte blocks
    hold their full lengths. -/
theorem parseFixed_inv {bs : List UInt8} {f : Fixed}
    {rest : List UInt8} (h : parseFixed bs = some (f, rest)) :
    bs = printFixed f ++ rest ∧ f.chaddr.length = 16 ∧
    f.sname.length = 64 ∧ f.file.length = 128 := by
  rw [parseFixed.eq_1] at h
  obtain ⟨op, r1, e1, _, h⟩ := withU8_inv h
  obtain ⟨htype, r2, e2, _, h⟩ := withU8_inv h
  obtain ⟨hlen, r3, e3, _, h⟩ := withU8_inv h
  obtain ⟨hops, r4, e4, _, h⟩ := withU8_inv h
  obtain ⟨xid, r5, e5, _, h⟩ := withU32_inv h
  obtain ⟨secs, r6, e6, _, h⟩ := withU16_inv h
  obtain ⟨flags, r7, e7, _, h⟩ := withU16_inv h
  obtain ⟨ciaddr, r8, e8, _, h⟩ := withU32_inv h
  obtain ⟨yiaddr, r9, e9, _, h⟩ := withU32_inv h
  obtain ⟨siaddr, r10, e10, _, h⟩ := withU32_inv h
  obtain ⟨giaddr, r11, e11, _, h⟩ := withU32_inv h
  obtain ⟨chaddr, r12, l12, e12, h⟩ := withBytes_inv h
  obtain ⟨sname, r13, l13, e13, h⟩ := withBytes_inv h
  obtain ⟨file, r14, l14, e14, h⟩ := withBytes_inv h
  obtain ⟨r15, e15, h⟩ := withCookie_inv h
  by_cases hc : (op = 1 ∨ op = 2) ∧ hlen ≤ 16
  · rw [ite_eq_left hc] at h
    cases h
    refine ⟨?_, l12, l13, l14⟩
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13,
      e14, e15]
    simp only [printFixed, ← List.append_assoc, List.cons_append,
      List.nil_append]
  · rw [ite_eq_right hc] at h
    cases h

/-- The fixed fields a successful read gives are well formed:
    op is 1 or 2, hlen is at most 16, every number fits the
    bytes it was read from, and the three byte blocks hold
    their full lengths. -/
theorem parseFixed_wf {bs : List UInt8} {f : Fixed}
    {rest : List UInt8} (h : parseFixed bs = some (f, rest)) :
    WFFixed f := by
  rw [parseFixed.eq_1] at h
  obtain ⟨op, r1, _, _, h⟩ := withU8_inv h
  obtain ⟨htype, r2, _, b2, h⟩ := withU8_inv h
  obtain ⟨hlen, r3, _, _, h⟩ := withU8_inv h
  obtain ⟨hops, r4, _, b4, h⟩ := withU8_inv h
  obtain ⟨xid, r5, _, b5, h⟩ := withU32_inv h
  obtain ⟨secs, r6, _, b6, h⟩ := withU16_inv h
  obtain ⟨flags, r7, _, b7, h⟩ := withU16_inv h
  obtain ⟨ciaddr, r8, _, b8, h⟩ := withU32_inv h
  obtain ⟨yiaddr, r9, _, b9, h⟩ := withU32_inv h
  obtain ⟨siaddr, r10, _, b10, h⟩ := withU32_inv h
  obtain ⟨giaddr, r11, _, b11, h⟩ := withU32_inv h
  obtain ⟨chaddr, r12, l12, _, h⟩ := withBytes_inv h
  obtain ⟨sname, r13, l13, _, h⟩ := withBytes_inv h
  obtain ⟨file, r14, l14, _, h⟩ := withBytes_inv h
  obtain ⟨r15, _, h⟩ := withCookie_inv h
  by_cases hc : (op = 1 ∨ op = 2) ∧ hlen ≤ 16
  · rw [ite_eq_left hc] at h
    cases h
    exact ⟨hc.1, b2, hc.2, b4, b5, b6, b7, b8, b9, b10, b11,
      l12, l13, l14⟩
  · rw [ite_eq_right hc] at h
    cases h

/-! ## The options -/

/-- One step of the option reader on a byte and what follows
    it, stated for rewriting. -/
theorem parseOptionsGo_step (fuel : Nat) (b : UInt8)
    (rest : List UInt8) :
    parseOptionsGo (fuel + 1) (b :: rest) =
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
          else none := rfl

/-- One step of the option reader on a code byte, a length
    byte, and what follows them, stated for rewriting. -/
theorem parseOptionsGo_step_cons (fuel : Nat) (b len : UInt8)
    (rest' : List UInt8) :
    parseOptionsGo (fuel + 1) (b :: len :: rest') =
      if b = 0 then parseOptionsGo fuel (len :: rest')
      else if b = 255 then
        if (len :: rest').all (fun x => x == 0) then some []
        else none
      else
        if (rest'.take len.toNat).length = len.toNat then
          (parseOptionsGo fuel (rest'.drop len.toNat)).map
            (fun os => (b.toNat, rest'.take len.toNat) :: os)
        else none := rfl

/-- One step of the option reader on a lone byte, stated for
    rewriting. -/
theorem parseOptionsGo_step_single (fuel : Nat) (b : UInt8) :
    parseOptionsGo (fuel + 1) [b] =
      if b = 0 then parseOptionsGo fuel []
      else if b = 255 then some []
      else none := rfl

/-- Printed options read back as the options. -/
theorem parseOptionsGo_printOptions :
    ∀ (os : List DhcpOption) (fuel : Nat),
    (∀ o ∈ os, 1 ≤ o.1 ∧ o.1 ≤ 254 ∧ o.2.length ≤ 255) →
    (printOptions os).length < fuel →
    parseOptionsGo fuel (printOptions os) = some os := by
  intro os
  induction os with
  | nil =>
    intro fuel _ hf
    have h1 : (printOptions ([] : List DhcpOption)).length = 1 := rfl
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    show parseOptionsGo (f + 1) [255] = some []
    rw [parseOptionsGo_step, ite_eq_right (by decide : ¬ ((255 : UInt8) = 0)),
      ite_eq_left rfl]
    exact rfl
  | cons o os ih =>
    intro fuel hw hf
    obtain ⟨c, v⟩ := o
    have hhead : 1 ≤ c ∧ c ≤ 254 ∧ v.length ≤ 255 :=
      hw (c, v) (by simp)
    obtain ⟨hc1, hc254, hv255⟩ := hhead
    have htail : ∀ x ∈ os, 1 ≤ x.1 ∧ x.1 ≤ 254 ∧ x.2.length ≤ 255 :=
      fun x hx => hw x (List.mem_cons_of_mem (c, v) hx)
    have hlen : (printOptions ((c, v) :: os)).length
        = v.length + 2 + (printOptions os).length := by
      show ((c.toUInt8 :: v.length.toUInt8 :: v) ++
        printOptions os).length
        = v.length + 2 + (printOptions os).length
      simp only [List.length_append, List.length_cons]
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hf' : (printOptions os).length < f := by omega
    have hb0 : ¬ (c.toUInt8 = 0) := by
      intro hcon
      have h2 : (c.toUInt8).toNat = 0 := by rw [hcon]; rfl
      rw [toUInt8_toNat] at h2
      omega
    have hb255 : ¬ (c.toUInt8 = 255) := by
      intro hcon
      have h2 : (c.toUInt8).toNat = 255 := by rw [hcon]; rfl
      rw [toUInt8_toNat] at h2
      omega
    have hlen' : (v.length.toUInt8).toNat = v.length := by
      rw [toUInt8_toNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hc' : (c.toUInt8).toNat = c := by
      rw [toUInt8_toNat]
      exact Nat.mod_eq_of_lt (by omega)
    show parseOptionsGo (f + 1)
      (c.toUInt8 :: v.length.toUInt8 :: (v ++ printOptions os))
      = some ((c, v) :: os)
    rw [parseOptionsGo_step, ite_eq_right hb0, ite_eq_right hb255]
    show (if ((v ++ printOptions os).take (v.length.toUInt8).toNat).length
        = (v.length.toUInt8).toNat then
      (parseOptionsGo f ((v ++ printOptions os).drop
        (v.length.toUInt8).toNat)).map
        (fun os' => (c.toUInt8.toNat,
          (v ++ printOptions os).take (v.length.toUInt8).toNat) :: os')
      else none) = some ((c, v) :: os)
    rw [hlen', List.take_left, ite_eq_left rfl, List.drop_left,
      ih f htail hf']
    simp only [Option.map_some, hc']

/-- Printed options read back as the options, at the top
    level. -/
theorem parseOptions_printOptions {os : List DhcpOption}
    (hw : ∀ o ∈ os, 1 ≤ o.1 ∧ o.1 ≤ 254 ∧ o.2.length ≤ 255) :
    parseOptions (printOptions os) = some os := by
  show parseOptionsGo ((printOptions os).length + 1)
    (printOptions os) = some os
  exact parseOptionsGo_printOptions os _ hw (Nat.lt_succ_self _)

/-- An option area the reader takes is one the grammar
    `OptionArea` derives, carrying the options the reader read.
    The proof follows the reader one step at a time: each step
    it takes is one constructor of the grammar. -/
theorem parseOptionsGo_area :
    ∀ (fuel : Nat) (bs : List UInt8) (os : List DhcpOption),
    parseOptionsGo fuel bs = some os → OptionArea bs os := by
  intro fuel
  induction fuel with
  | zero =>
    intro bs os h
    simp [parseOptionsGo] at h
  | succ f ih =>
    intro bs os h
    cases bs with
    | nil =>
      have h1 : parseOptionsGo (f + 1) ([] : List UInt8)
          = some [] := rfl
      rw [h1] at h
      simp only [Option.some.injEq] at h
      subst h
      exact OptionArea.stop
    | cons b rest =>
      by_cases hb0 : b = 0
      · subst hb0
        rw [parseOptionsGo_step, ite_eq_left rfl] at h
        exact OptionArea.pad (ih rest os h)
      · by_cases hb255 : b = 255
        · subst hb255
          rw [parseOptionsGo_step,
            ite_eq_right (by decide : ¬ ((255 : UInt8) = 0)),
            ite_eq_left rfl] at h
          by_cases hall : rest.all (fun x => x == 0) = true
          · rw [ite_eq_left hall] at h
            simp only [Option.some.injEq] at h
            subst h
            refine OptionArea.finish (fun z hz => ?_)
            have hz0 := List.all_eq_true.mp hall z hz
            exact beq_iff_eq.mp hz0
          · rw [ite_eq_right hall] at h
            simp at h
        · cases rest with
          | nil =>
            rw [parseOptionsGo_step_single, ite_eq_right hb0,
              ite_eq_right hb255] at h
            simp at h
          | cons len rest' =>
            rw [parseOptionsGo_step_cons, ite_eq_right hb0,
              ite_eq_right hb255] at h
            by_cases hcond :
                (rest'.take len.toNat).length = len.toNat
            · rw [ite_eq_left hcond] at h
              obtain ⟨os', hos', hos''⟩ :=
                Option.map_eq_some_iff.mp h
              subst hos''
              have hitem := OptionArea.item hb0 hb255 hcond
                (ih _ _ hos')
              rw [List.take_append_drop] at hitem
              exact hitem
            · rw [ite_eq_right hcond] at h
              simp at h

/-- Every option the reader takes has a code from 1 to 254
    and a value of at most 255 bytes: a pad or end byte is
    never read as a code, and a value is as long as the one
    length byte before it says. -/
theorem parseOptionsGo_wf :
    ∀ (fuel : Nat) (bs : List UInt8) (os : List DhcpOption),
    parseOptionsGo fuel bs = some os →
    ∀ o ∈ os, 1 ≤ o.1 ∧ o.1 ≤ 254 ∧ o.2.length ≤ 255 := by
  intro fuel
  induction fuel with
  | zero =>
    intro bs os h
    simp [parseOptionsGo] at h
  | succ f ih =>
    intro bs os h
    cases bs with
    | nil =>
      have h1 : parseOptionsGo (f + 1) ([] : List UInt8)
          = some [] := rfl
      rw [h1] at h
      cases h
      intro o ho
      cases ho
    | cons b rest =>
      by_cases hb0 : b = 0
      · subst hb0
        rw [parseOptionsGo_step, ite_eq_left rfl] at h
        exact ih rest os h
      · by_cases hb255 : b = 255
        · subst hb255
          rw [parseOptionsGo_step,
            ite_eq_right (by decide : ¬ ((255 : UInt8) = 0)),
            ite_eq_left rfl] at h
          by_cases hall : rest.all (fun x => x == 0) = true
          · rw [ite_eq_left hall] at h
            cases h
            intro o ho
            cases ho
          · rw [ite_eq_right hall] at h
            cases h
        · cases rest with
          | nil =>
            rw [parseOptionsGo_step_single, ite_eq_right hb0,
              ite_eq_right hb255] at h
            cases h
          | cons len rest' =>
            rw [parseOptionsGo_step_cons, ite_eq_right hb0,
              ite_eq_right hb255] at h
            by_cases hcond :
                (rest'.take len.toNat).length = len.toNat
            · rw [ite_eq_left hcond] at h
              obtain ⟨os', hos', hos''⟩ :=
                Option.map_eq_some_iff.mp h
              subst hos''
              intro o ho
              cases ho with
              | head =>
                have hlt := toNat_lt b
                have hl := toNat_lt len
                have h0 : b.toNat ≠ 0 := fun e =>
                  hb0 (UInt8.toNat_inj.mp e)
                have h255 : b.toNat ≠ 255 := fun e =>
                  hb255 (UInt8.toNat_inj.mp e)
                dsimp only
                rw [hcond]
                omega
              | tail _ ho' => exact ih _ os' hos' o ho'
            · rw [ite_eq_right hcond] at h
              cases h

/-! ## The option 53 check -/

/-- Well formed options pass the option 53 check. -/
theorem check53_of_WFOptions {os : List DhcpOption}
    (hw : WFOptions os) : check53 os = true := by
  obtain ⟨_, t, hfilter, h1, h8⟩ := hw
  unfold check53
  rw [hfilter]
  show decide (1 ≤ t.toNat ∧ t.toNat ≤ 8) = true
  rw [decide_eq_true_eq]
  exact ⟨h1, h8⟩

/-- Options that pass the option 53 check hold option 53
    exactly once, with a one byte value from 1 to 8. -/
theorem check53_type {os : List DhcpOption}
    (h : check53 os = true) :
    ∃ t : UInt8, os.filter (fun o => o.1 == 53) = [(53, [t])] ∧
      1 ≤ t.toNat ∧ t.toNat ≤ 8 := by
  unfold check53 at h
  split at h
  · rename_i c t heq
    have hmem : (c, [t]) ∈ os.filter (fun o => o.1 == 53) := by
      rw [heq]; exact List.mem_singleton_self _
    have hc : c = 53 := by
      have h53 := (List.mem_filter.mp hmem).2
      exact Nat.eq_of_beq_eq_true h53
    subst hc
    exact ⟨t, heq, of_decide_eq_true h⟩
  · cases h

/-! ## The headline theorems -/

/-- The main claim: for every well formed message, parsing
    its printed form gives the message back. -/
theorem parse_print {m : Message} (hw : WF m) :
    parse (print m) = some m := by
  obtain ⟨hwf, hwo⟩ := hw
  show parse (printFixed m.fixed ++ printOptions m.options)
    = some m
  simp only [parse]
  rw [parseFixed_printFixed hwf (printOptions m.options)]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [parseOptions_printOptions hwo.1]
  simp only [Option.bind_some]
  rw [ite_eq_left (check53_of_WFOptions hwo)]

/-- The mirror claim: printing a message the parser took
    gives the canonical form of the bytes it was read from.
    The bytes after the first 240 are an option area the
    grammar derives, carrying the options read, and the print
    is the first 240 bytes as they stood, then those options
    printed. -/
theorem print_parse {bs : List UInt8} {m : Message}
    (h : parse bs = some m) :
    OptionArea (bs.drop 240) m.options ∧
      print m = bs.take 240 ++ printOptions m.options := by
  simp only [parse] at h
  obtain ⟨⟨f, rest⟩, hf, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨os, hos, h⟩ := Option.bind_eq_some_iff.mp h
  by_cases hc : check53 os = true
  · rw [ite_eq_left hc] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hfix, hc16, hs64, hf128⟩ := parseFixed_inv hf
    have hlen := printFixed_length hc16 hs64 hf128
    have htake : bs.take 240 = printFixed f := by
      rw [hfix, ← hlen]; exact List.take_left
    have hdrop : bs.drop 240 = rest := by
      rw [hfix, ← hlen]; exact List.drop_left
    have hos' : parseOptionsGo (rest.length + 1) rest
        = some os := hos
    refine ⟨?_, ?_⟩
    · rw [hdrop]
      exact parseOptionsGo_area (rest.length + 1) rest os hos'
    · show printFixed f ++ printOptions os
        = bs.take 240 ++ printOptions os
      rw [htake]
  · rw [ite_eq_right hc] at h
    simp at h

/-- Soundness: every message the parser takes is well formed,
    in the sense of `WF`, the same predicate `parse_print`
    assumes. -/
theorem parse_wf {bs : List UInt8} {m : Message}
    (h : parse bs = some m) : WF m := by
  simp only [parse] at h
  obtain ⟨⟨f, rest⟩, hf, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨os, hos, h⟩ := Option.bind_eq_some_iff.mp h
  by_cases hc : check53 os = true
  · rw [ite_eq_left hc] at h
    cases h
    exact ⟨parseFixed_wf hf,
      parseOptionsGo_wf (rest.length + 1) rest os hos,
      check53_type hc⟩
  · rw [ite_eq_right hc] at h
    cases h

end Dhcp.Proofs
