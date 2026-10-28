/-
  The round trip proofs.

  Two claims are proved here, matching the plan's main claim
  and its mirror:

  - `parse_print`: for every well formed message, parsing its
    printed form gives the message back.
  - `print_parse`: for every byte list the parser takes,
    printing the parsed message gives the canonical form of
    the input: the first 240 bytes as they stood (the fixed
    fields and the cookie stand unchanged under printing),
    then the options with pad bytes dropped and exactly one
    end byte. `canonOptions`, in `Dhcp/Value.lean` beside
    the printer, spells that canonical option area out as a
    function.

  The steps: the two and four byte numbers read back as the
  values they were printed from, and printed numbers recover
  the bytes they were read from; the readers invert on
  printed forms and on read forms; the fixed fields invert
  both ways; the option reader inverts on printed options;
  and the canonical form lemma ties a read option area to the
  printed options of the value it read to.
-/

import Dhcp

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

/-! ## The readers, on printed forms and on read forms -/

/-- One step of the one byte reader, stated for rewriting. -/
theorem getU8_cons (b : UInt8) (r : List UInt8) :
    getU8 (b :: r) = some (b.toNat, r) := rfl

/-- Reading two bytes off the front of a printed value and
    what follows it. -/
theorem getU16_be16 (n : Nat) (h : n < 65536) (r : List UInt8) :
    getU16 (be16 n ++ r) = some (n, r) := by
  show getU16 ((n / 256).toUInt8 :: n.toUInt8 :: r) = some (n, r)
  show some (u16 (n / 256).toUInt8 n.toUInt8, r) = some (n, r)
  rw [u16_be16 n h]

/-- Reading four bytes off the front of a printed value and
    what follows it. -/
theorem getU32_be32 (n : Nat) (h : n < 4294967296)
    (r : List UInt8) :
    getU32 (be32 n ++ r) = some (n, r) := by
  show getU32 ((n / 16777216).toUInt8 :: (n / 65536).toUInt8 ::
    (n / 256).toUInt8 :: n.toUInt8 :: r) = some (n, r)
  show some (u32 (n / 16777216).toUInt8 (n / 65536).toUInt8
    (n / 256).toUInt8 n.toUInt8, r) = some (n, r)
  rw [u32_be32 n h]

/-- Reading a byte block off the front of a printed block and
    what follows it. -/
theorem getBytes_app {n : Nat} {v : List UInt8} (hv : v.length = n)
    (r : List UInt8) : getBytes n (v ++ r) = some (v, r) := by
  unfold getBytes
  have ht : (v ++ r).take n = v := by
    rw [← hv]; exact List.take_left
  have hd : (v ++ r).drop n = r := by
    rw [← hv]; exact List.drop_left
  rw [ht, hd, if_pos hv]

/-- Reading the cookie off the front of a printed cookie and
    what follows it. -/
theorem getCookie_app (r : List UInt8) :
    getCookie (cookie ++ r) = some r := by
  unfold getCookie
  have ht : (cookie ++ r).take 4 = cookie := List.take_left' rfl
  have hd : (cookie ++ r).drop 4 = r := List.drop_left' rfl
  rw [ht, hd, if_pos rfl]

/-- A byte read by the one byte reader prints back as that
    byte: the input was the byte and the rest. -/
theorem getU8_inv {bs : List UInt8} {n : Nat} {r : List UInt8}
    (h : getU8 bs = some (n, r)) : bs = n.toUInt8 :: r := by
  cases bs with
  | nil => simp [getU8] at h
  | cons b r' =>
    have hstep : getU8 (b :: r') = some (b.toNat, r') := rfl
    rw [hstep] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [toNat_toUInt8]

/-- Bytes read by the two byte reader print back as those
    bytes, and the value fits two bytes. -/
theorem getU16_inv {bs : List UInt8} {n : Nat} {r : List UInt8}
    (h : getU16 bs = some (n, r)) :
    bs = be16 n ++ r ∧ n < 65536 := by
  cases bs with
  | nil => simp [getU16] at h
  | cons a bs' =>
    cases bs' with
    | nil => simp [getU16] at h
    | cons b r' =>
      have hstep : getU16 (a :: b :: r') = some (u16 a b, r') := rfl
      rw [hstep] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_⟩
      · simp only [be16_u16, List.cons_append, List.nil_append]
      · have ha := toNat_lt a
        have hb := toNat_lt b
        simp only [u16]; omega

/-- Bytes read by the four byte reader print back as those
    bytes, and the value fits four bytes. -/
theorem getU32_inv {bs : List UInt8} {n : Nat} {r : List UInt8}
    (h : getU32 bs = some (n, r)) :
    bs = be32 n ++ r ∧ n < 4294967296 := by
  cases bs with
  | nil => simp [getU32] at h
  | cons a bs1 =>
    cases bs1 with
    | nil => simp [getU32] at h
    | cons b bs2 =>
      cases bs2 with
      | nil => simp [getU32] at h
      | cons c bs3 =>
        cases bs3 with
        | nil => simp [getU32] at h
        | cons d r' =>
          have hstep : getU32 (a :: b :: c :: d :: r')
              = some (u32 a b c d, r') := rfl
          rw [hstep] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, ?_⟩
          · simp only [be32_u32, List.cons_append, List.nil_append]
          · have ha := toNat_lt a
            have hb := toNat_lt b
            have hc := toNat_lt c
            have hd := toNat_lt d
            simp only [u32]; omega

/-- A block read by the block reader is its first `n` bytes,
    and the rest is the rest: the input was the block and the
    rest. -/
theorem getBytes_inv {n : Nat} {bs v : List UInt8}
    {r : List UInt8} (h : getBytes n bs = some (v, r)) :
    v.length = n ∧ bs = v ++ r := by
  unfold getBytes at h
  by_cases hc : (bs.take n).length = n
  · rw [if_pos hc] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hc, (List.take_append_drop n bs).symm⟩
  · rw [if_neg hc] at h
    simp at h

/-- An input the cookie reader takes started with the
    cookie. -/
theorem getCookie_inv {bs : List UInt8} {r : List UInt8}
    (h : getCookie bs = some r) : bs = cookie ++ r := by
  unfold getCookie at h
  by_cases hc : bs.take 4 = cookie
  · rw [if_pos hc] at h
    simp only [Option.some.injEq] at h
    subst h
    calc bs = bs.take 4 ++ bs.drop 4 :=
        (List.take_append_drop 4 bs).symm
    _ = cookie ++ bs.drop 4 := by rw [hc]
  · rw [if_neg hc] at h
    simp at h

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
    any bytes that follow them. -/
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
  rw [key]
  simp only [parseFixed]
  rw [getU8_cons]; simp only [Option.bind_eq_bind, Option.bind_some]
  rw [getU8_cons]; simp only [Option.bind_eq_bind, Option.bind_some]
  rw [getU8_cons]; simp only [Option.bind_eq_bind, Option.bind_some]
  rw [getU8_cons]; simp only [Option.bind_eq_bind, Option.bind_some]
  rw [getU32_be32 f.xid hxid]; simp only [Option.bind_eq_bind, Option.bind_some]
  rw [getU16_be16 f.secs hsecs]; simp only [Option.bind_eq_bind, Option.bind_some]
  rw [getU16_be16 f.flags hflags]; simp only [Option.bind_eq_bind, Option.bind_some]
  rw [getU32_be32 f.ciaddr hci]; simp only [Option.bind_eq_bind, Option.bind_some]
  rw [getU32_be32 f.yiaddr hyi]; simp only [Option.bind_eq_bind, Option.bind_some]
  rw [getU32_be32 f.siaddr hsi]; simp only [Option.bind_eq_bind, Option.bind_some]
  rw [getU32_be32 f.giaddr hgi]; simp only [Option.bind_eq_bind, Option.bind_some]
  rw [getBytes_app hch]; simp only [Option.bind_eq_bind, Option.bind_some]
  rw [getBytes_app hsn]; simp only [Option.bind_eq_bind, Option.bind_some]
  rw [getBytes_app hfi]; simp only [Option.bind_eq_bind, Option.bind_some]
  rw [getCookie_app]; simp only [Option.bind_eq_bind, Option.bind_some]
  rw [hop', hhtype', hhlen', hhops']
  rw [if_pos ⟨hop, hhlen⟩]

/-- The fixed fields a successful read gives print back to
    the bytes they were read from, and its three byte blocks
    hold their full lengths. -/
theorem parseFixed_inv {bs : List UInt8} {f : Fixed}
    {rest : List UInt8} (h : parseFixed bs = some (f, rest)) :
    bs = printFixed f ++ rest ∧ f.chaddr.length = 16 ∧
    f.sname.length = 64 ∧ f.file.length = 128 := by
  simp only [parseFixed] at h
  obtain ⟨⟨op, r1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨⟨htype, r2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨⟨hlen, r3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨⟨hops, r4⟩, h4, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨⟨xid, r5⟩, h5, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨⟨secs, r6⟩, h6, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨⟨flags, r7⟩, h7, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨⟨ciaddr, r8⟩, h8, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨⟨yiaddr, r9⟩, h9, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨⟨siaddr, r10⟩, h10, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨⟨giaddr, r11⟩, h11, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨⟨chaddr, r12⟩, h12, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨⟨sname, r13⟩, h13, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨⟨file, r14⟩, h14, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨r15, h15, h⟩ := Option.bind_eq_some_iff.mp h
  by_cases hc : (op = 1 ∨ op = 2) ∧ hlen ≤ 16
  · rw [if_pos hc] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, (getBytes_inv h12).1, (getBytes_inv h13).1,
      (getBytes_inv h14).1⟩
    rw [getU8_inv h1, getU8_inv h2, getU8_inv h3, getU8_inv h4,
      (getU32_inv h5).1, (getU16_inv h6).1, (getU16_inv h7).1,
      (getU32_inv h8).1, (getU32_inv h9).1, (getU32_inv h10).1,
      (getU32_inv h11).1, (getBytes_inv h12).2,
      (getBytes_inv h13).2, (getBytes_inv h14).2,
      getCookie_inv h15]
    simp only [printFixed, ← List.append_assoc, List.cons_append,
      List.nil_append]
  · rw [if_neg hc] at h
    simp at h

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
    rw [parseOptionsGo_step, if_neg (by decide : ¬ ((255 : UInt8) = 0)),
      if_pos rfl]
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
    rw [parseOptionsGo_step, if_neg hb0, if_neg hb255]
    show (if ((v ++ printOptions os).take (v.length.toUInt8).toNat).length
        = (v.length.toUInt8).toNat then
      (parseOptionsGo f ((v ++ printOptions os).drop
        (v.length.toUInt8).toNat)).map
        (fun os' => (c.toUInt8.toNat,
          (v ++ printOptions os).take (v.length.toUInt8).toNat) :: os')
      else none) = some ((c, v) :: os)
    rw [hlen', List.take_left, if_pos rfl, List.drop_left,
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

/-- One step of the canonical form on a byte and what
    follows it, stated for rewriting. -/
theorem canonOptionsGo_step (fuel : Nat) (b : UInt8)
    (rest : List UInt8) :
    canonOptionsGo (fuel + 1) (b :: rest) =
      if b = 0 then canonOptionsGo fuel rest
      else if b = 255 then [255]
      else
        match rest with
        | [] => [255]
        | len :: rest' => b :: len :: (rest'.take len.toNat) ++
            canonOptionsGo fuel (rest'.drop len.toNat) := rfl

/-- One step of the canonical form on a code byte, a length
    byte, and what follows them, stated for rewriting. -/
theorem canonOptionsGo_step_cons (fuel : Nat) (b len : UInt8)
    (rest' : List UInt8) :
    canonOptionsGo (fuel + 1) (b :: len :: rest') =
      if b = 0 then canonOptionsGo fuel (len :: rest')
      else if b = 255 then [255]
      else b :: len :: (rest'.take len.toNat) ++
        canonOptionsGo fuel (rest'.drop len.toNat) := rfl

/-- One step of the canonical form on a lone byte, stated
    for rewriting. -/
theorem canonOptionsGo_step_single (fuel : Nat) (b : UInt8) :
    canonOptionsGo (fuel + 1) [b] =
      if b = 0 then canonOptionsGo fuel []
      else if b = 255 then [255]
      else [255] := rfl

/-- An option area the reader takes canonicalizes to the
    printed form of the options it read to. -/
theorem canonOptionsGo_parse :
    ∀ (fuel : Nat) (bs : List UInt8) (os : List DhcpOption),
    parseOptionsGo fuel bs = some os →
    canonOptionsGo fuel bs = printOptions os := by
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
      rfl
    | cons b rest =>
      by_cases hb0 : b = 0
      · subst hb0
        rw [parseOptionsGo_step, if_pos rfl] at h
        rw [canonOptionsGo_step, if_pos rfl]
        exact ih rest os h
      · by_cases hb255 : b = 255
        · subst hb255
          rw [parseOptionsGo_step,
            if_neg (by decide : ¬ ((255 : UInt8) = 0)),
            if_pos rfl] at h
          by_cases hall : rest.all (fun x => x == 0) = true
          · rw [if_pos hall] at h
            simp only [Option.some.injEq] at h
            subst h
            rw [canonOptionsGo_step,
              if_neg (by decide : ¬ ((255 : UInt8) = 0)),
              if_pos rfl]
            rfl
          · rw [if_neg hall] at h
            simp at h
        · cases rest with
          | nil =>
            rw [parseOptionsGo_step_single, if_neg hb0,
              if_neg hb255] at h
            simp at h
          | cons len rest' =>
            rw [parseOptionsGo_step_cons, if_neg hb0,
              if_neg hb255] at h
            by_cases hcond :
                (rest'.take len.toNat).length = len.toNat
            · rw [if_pos hcond] at h
              obtain ⟨os', hos', hos''⟩ :=
                Option.map_eq_some_iff.mp h
              subst hos''
              rw [canonOptionsGo_step_cons, if_neg hb0,
                if_neg hb255, ih _ _ hos']
              show b :: len :: (rest'.take len.toNat) ++
                  printOptions os'
                = ((b.toNat).toUInt8 ::
                    (rest'.take len.toNat).length.toUInt8 ::
                    (rest'.take len.toNat)) ++ printOptions os'
              rw [toNat_toUInt8, hcond, toNat_toUInt8]
            · rw [if_neg hcond] at h
              simp at h

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
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (check53_of_WFOptions hwo)]

/-- The mirror claim: printing a message the parser took
    gives the canonical form of the bytes it was read from:
    the first 240 bytes as they stood, then the canonical
    option area. -/
theorem print_parse {bs : List UInt8} {m : Message}
    (h : parse bs = some m) :
    print m = bs.take 240 ++ canonOptions (bs.drop 240) := by
  simp only [parse] at h
  obtain ⟨⟨f, rest⟩, hf, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  obtain ⟨os, hos, h⟩ := Option.bind_eq_some_iff.mp h
  by_cases hc : check53 os = true
  · rw [if_pos hc] at h
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
    have hcanon : canonOptions rest = printOptions os :=
      canonOptionsGo_parse (rest.length + 1) rest os hos'
    show printFixed f ++ printOptions os
      = bs.take 240 ++ canonOptions (bs.drop 240)
    rw [htake, hdrop, hcanon]
  · rw [if_neg hc] at h
    simp at h

end Dhcp.Proofs
