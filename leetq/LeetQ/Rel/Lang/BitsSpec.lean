/-
  The bit-matrix plan (`Bits.lean`) read back. `TP.den` is the plan's relation in `Rel(Set)`; `rep_tableC` says the
  table side computes it under `tableC`'s one bit. The bit side is read at the codes: `Bits.Enc` says a matrix holds,
  at bit `i·w + j`, a relation between the elements `ua i`, `ub j`, and each bit rule maps encodings to encodings.
-/
import LeetQ.Rel.Lang.Bits
import LeetQ.Rel.CRelFold
import LeetQ.Rel.KernelWF.BitRows
import LeetQ.Rel.KernelWF.MemberSpec
import LeetQ.Rel.RepArith

namespace LeetQ.Rel.Lang.Bits

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep Freyd Freyd.Alg Freyd.Alg.RelSet

/-! ### The plan's relation -/

/-- The plan's relation in `Rel(Set)`: each node the set-theoretic op on its children's, a leaf its table's `rep`. -/
def TP.den : {A B : Obj} → TP A B → A.El → B.El → Prop
  | _, _, .leaf R => rep R
  | _, _, .comp R S => fun a c => ∃ b, R.den a b ∧ S.den b c
  | _, _, .conv R => fun b a => R.den a b
  | _, _, .meet R S => fun a b => R.den a b ∧ S.den a b
  | _, _, .join R S => fun a b => R.den a b ∨ S.den a b
  | _, _, .diff R S => fun a b => R.den a b ∧ ¬ S.den a b
  | _, _, .ldiv R S UB UC => fun b c =>
    (∀ a, R.den a b → S.den a c) ∧ ((∃ a, R.den a b) ∨ ((∃ p, UB.val.row p = b) ∧ ∃ j, UC.val.row j = c))

/-- **The table side**: under `tableC`'s bit the plan's table denotes `TP.den`, each node by its `CRel` op's
    read-back (`rep_comp`, `rep_inter`, `rep_union`, `rep_diffC`, `rep_leftDiv`, `rep_conv`). -/
theorem rep_tableC : ∀ {A B : Obj} (p : TP A B), p.tableC.ok = true →
    ∀ a b, rep p.tableC.rel a b ↔ p.den a b
  | _, _, .leaf _, _, _, _ => Iff.rfl
  | _, _, .comp R S, hb, a, c => by
    unfold TP.tableC at hb ⊢
    by_cases hz : (R.tableC.rel.n == 0) = true
    · rw [if_pos hz] at hb ⊢
      have ih := rep_tableC R hb
      have h0 : R.tableC.rel.n.toNat = 0 := by simp [beq_iff_eq.1 hz]
      refine ⟨fun ⟨i, _⟩ => i.elim0, fun ⟨b, hR, _⟩ => ?_⟩
      obtain ⟨i, -⟩ := (ih a b).2 hR
      exact absurd i.2 (by omega)
    · rw [if_neg hz] at hb ⊢
      have h := hb
      simp only [CRel.comp, CRel.guard_ok, Bool.and_eq_true] at h
      rw [CRel.rep_comp _ _ hb]
      have ihR := rep_tableC R h.1.1
      have ihS := rep_tableC S h.1.2
      exact ⟨fun ⟨b, h1, h2⟩ => ⟨b, (ihR a b).1 h1, (ihS b c).1 h2⟩,
        fun ⟨b, h1, h2⟩ => ⟨b, (ihR a b).2 h1, (ihS b c).2 h2⟩⟩
  | _, _, .conv R, hb, b, a => by
    unfold TP.tableC at hb ⊢
    rw [rep_conv]; exact rep_tableC R hb a b
  | _, _, .meet R S, hb, a, b => by
    unfold TP.tableC at hb ⊢
    have h := hb
    simp only [CRel.inter, CRel.guard_ok, Bool.and_eq_true] at h
    rw [CRel.rep_inter _ _ hb]
    exact and_congr (rep_tableC R h.1.1 a b) (rep_tableC S h.1.2 a b)
  | _, _, .join R S, hb, a, b => by
    unfold TP.tableC at hb ⊢
    have h := hb
    simp only [CRel.union, CRel.guard_ok, Bool.and_eq_true] at h
    rw [CRel.rep_union _ _ hb]
    exact or_congr (rep_tableC R h.1.1 a b) (rep_tableC S h.1.2 a b)
  | _, _, .diff R S, hb, a, b => by
    unfold TP.tableC at hb ⊢
    simp only [Bool.and_eq_true] at hb
    rw [rep_diffC _ _ hb.2]
    exact and_congr (rep_tableC R hb.1.1 a b) (not_congr (rep_tableC S hb.1.2 a b))
  | _, _, .ldiv R S UB UC, hb, b, c => by
    unfold TP.tableC at hb ⊢
    have h := hb
    simp only [CRel.leftDiv, CRel.guard_ok, Bool.and_eq_true] at h
    rw [CRel.rep_leftDiv _ _ _ _ hb]
    have ihR := rep_tableC R h.1.1
    have ihS := rep_tableC S h.1.2
    simp only [TP.den, ihR, ihS]

/-- `TP.table` denotes `TP.den` under `tableC`'s bit. -/
theorem rep_table {A B : Obj} (p : TP A B) (hb : p.tableC.ok = true) (a : A.El) (b : B.El) :
    rep p.table a b ↔ p.den a b := rep_tableC p hb a b

#print axioms rep_tableC

/-! ### Matrices read at the codes -/

/-- Bit `i·w + j` of `x`: code `i` related to code `j`. -/
def Bits.at (x : Bits) (i j : Nat) : Bool := Column.bitAt x.b (i * x.w + j)

/-- `x` holds `r` between the elements at its codes: for `i < na` and `j < w`, bit `(i, j)` is set iff
    `r (ua i) (ub j)`. -/
def Bits.Enc {A B : Obj} (ua : Nat → A.El) (ub : Nat → B.El) (x : Bits) (r : A.El → B.El → Prop) : Prop :=
  ∀ i < x.na, ∀ j < x.w, (x.at i j = true ↔ r (ua i) (ub j))

/-- Row `i`, column `j` lies inside the `na · w` bits. -/
theorem idx_lt {i j na w : Nat} (hi : i < na) (hj : j < w) : i * w + j < na * w := by
  have := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hi); rw [Nat.succ_mul] at this; omega

/-- A matrix `TP.fits` admits (`≤ 2²⁷` bits) counts its bits in a `USize`. -/
theorem toUSize_fit {n : Nat} (h : n ≤ 2 ^ 27) : n.toUSize.toNat = n :=
  USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (by decide) USize.le_size))

variable {A B C : Obj} {ua : Nat → A.El} {ub : Nat → B.El}

/-- The `Ew.bit` of two matrices of one shape, bit by bit. -/
theorem enc_bit (op : UInt8) (F : Prop → Prop → Prop) (hF : ∀ p q, Ew.bitStep op p q = true ↔ F (p = true) (q = true))
    {x y : Bits} {r s : A.El → B.El → Prop} (hx : x.Enc ua ub r) (hy : y.Enc ua ub s) (hn : y.na = x.na)
    (hw : y.w = x.w) (hfit : x.na * x.w ≤ 2 ^ 27) :
    (⟨x.na, x.w, Ew.bit op Ew.vv x.b y.b (x.na * x.w).toUSize⟩ : Bits).Enc ua ub fun a b => F (r a b) (s a b) := by
  intro i hi j hj
  have ht : i * x.w + j < (x.na * x.w).toUSize.toNat := by rw [toUSize_fit hfit]; exact idx_lt hi hj
  have ex := hx i hi j hj
  have ey := hy i (hn ▸ hi) j (hw ▸ hj)
  simp only [Bits.at, hw] at ex ey ⊢
  rw [bitAt_bit _ _ _ ht, hF, propext ex, propext ey]

/-- **`∩` as bits** (`rep_inter`'s side, `rep_tableC`): the `∧` of the two matrices holds `TP.meet`'s relation. -/
theorem rep_meetB {R S : TP A B} {x y : Bits} (hx : x.Enc ua ub R.den) (hy : y.Enc ua ub S.den) (hn : y.na = x.na)
    (hw : y.w = x.w) (hfit : x.na * x.w ≤ 2 ^ 27) : (x.meet y).Enc ua ub (TP.meet R S).den :=
  enc_bit _ And (fun p q => by rw [bitStep_lesser, Bool.and_eq_true]) hx hy hn hw hfit

/-- **`∪` as bits**: the `∨` of the two matrices holds `TP.join`'s relation. -/
theorem rep_joinB {R S : TP A B} {x y : Bits} (hx : x.Enc ua ub R.den) (hy : y.Enc ua ub S.den) (hn : y.na = x.na)
    (hw : y.w = x.w) (hfit : x.na * x.w ≤ 2 ^ 27) : (x.join y).Enc ua ub (TP.join R S).den :=
  enc_bit _ Or (fun p q => by rw [bitStep_greater, Bool.or_eq_true]) hx hy hn hw hfit

/-- **`−` as bits**: the `∧` with the complement (`notBits`) holds `TP.diff`'s relation. -/
theorem rep_diffB {R S : TP A B} {x y : Bits} (hx : x.Enc ua ub R.den) (hy : y.Enc ua ub S.den) (hn : y.na = x.na)
    (hw : y.w = x.w) (hfit : x.na * x.w ≤ 2 ^ 27) : (x.diff y).Enc ua ub (TP.diff R S).den := by
  have hy' : (⟨y.na, y.w, Ew.notBits (y.na * y.w).toUSize y.b⟩ : Bits).Enc ua ub fun a b => ¬ S.den a b := by
    intro i hi j hj
    have ht : i * y.w + j < (y.na * y.w).toUSize.toNat := by
      rw [toUSize_fit (hn ▸ hw ▸ hfit)]; exact idx_lt hi hj
    have ey := hy i hi j hj
    simp only [Bits.at] at ey ⊢
    rw [notBits_bitAt _ _ ht, Bool.not_eq_true', ← ey]; simp
  have := enc_bit _ And (fun p q => by rw [bitStep_lesser, Bool.and_eq_true]) hx hy' hn hw hfit
  intro i hi j hj; rw [Bits.diff, Bits.meet, this i hi j hj]; simp [TP.den]

#print axioms rep_diffB

/-! ### `≫` as bits: the segments of an ascending group column -/

/-- In an ascending list the entries below `g` are its first `countP (· < g)`. -/
theorem sorted_lt_iff (g : Nat) : ∀ {l : List Nat}, l.Pairwise (· ≤ ·) → ∀ {k} (hk : k < l.length),
    (l[k] < g ↔ k < l.countP (· < g))
  | [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | x :: l, hs, k, hk => by
    rw [List.pairwise_cons] at hs
    by_cases hx : x < g
    · rw [List.countP_cons_of_pos (by simpa using hx)]
      cases k with
      | zero => simp [hx]
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [sorted_lt_iff g hs.2 (by simpa using hk)]; omega
    · rw [List.countP_cons_of_neg (by simpa using hx)]
      have h0 : l.countP (fun y => decide (y < g)) = 0 :=
        List.countP_eq_zero.2 fun y hy => by have := hs.1 y hy; simp; omega
      rw [h0]
      cases k with
      | zero => simp [hx]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have := hs.1 _ (List.getElem_mem (l := l) (by simpa using hk))
        constructor <;> intro h <;> omega

/-- The entries below `g + 1` are those below `g` and those equal to `g`. -/
theorem countP_lt_succ (l : List Nat) (g : Nat) :
    l.countP (· < g + 1) = l.countP (· < g) + l.countP (· == g) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.countP_cons, ih]
    by_cases h1 : x < g
    · have : x ≠ g := by omega
      simp [h1, this, show x < g + 1 by omega]; omega
    · by_cases h2 : x = g
      · subst h2; simp; omega
      · have : ¬ x < g + 1 := by omega
        simp [h1, h2, this]

/-- The running total of the group sizes below `g` counts the entries below `g`. -/
theorem sum_countP_eq (l : List Nat) : ∀ g, ((List.range g).map fun h => l.countP (· == h)).sum = l.countP (· < g)
  | 0 => by simp
  | g + 1 => by
    simp [List.range_succ, sum_countP_eq l g, countP_lt_succ]

/-- **Segment `a` of an ascending list** is the positions holding `a`: `[countP (· < a), countP (· < a + 1))`. -/
theorem seg_iff {l : List Nat} (hs : l.Pairwise (· ≤ ·)) (a k : Nat) :
    (l.countP (· < a) ≤ k ∧ k < l.countP (· < a + 1)) ↔ ∃ hk : k < l.length, l[k] = a := by
  by_cases hk : k < l.length
  · have h0 := sorted_lt_iff a hs hk
    have h1 := sorted_lt_iff (a + 1) hs hk
    constructor
    · rintro ⟨e1, e2⟩
      have := mt h0.1 (by omega); have := h1.2 e2
      exact ⟨hk, by omega⟩
    · rintro ⟨hk', e⟩
      have e' : l[k]'hk = a := e
      exact ⟨Nat.le_of_not_lt fun h => absurd (h0.2 h) (by omega), h1.1 (by omega)⟩
  · have := List.countP_le_length (p := fun x => decide (x < a + 1)) (l := l)
    constructor
    · rintro ⟨-, e⟩; omega
    · rintro ⟨h, -⟩; exact absurd h hk

/-- A long below `2⁶³` reads back as itself through `Int64`'s clamp. -/
theorem clamp_toInt64 (u : UInt64) (h : u.toNat < 2 ^ 63) : u.toInt64.toNatClampNeg = u.toNat := by
  rw [Int64.toNatClampNeg, Int64.toInt, UInt64.toBitVec_toInt64, BitVec.toInt_eq_toNat_cond]
  simp only [UInt64.toNat_toBitVec]
  rw [if_pos (by omega)]; simp

/-- A long payload at `64` bits, as `groupSizes` reads it, is its `ids`. -/
theorem idsW_64 (d : ByteArray) : idsW 64 (len d) d = ids d := by
  have hl : len d = d.size / 8 := by rw [len_eq_ids, ids, List.length_map, List.length_range]
  have hc : Column.idsCap d 64 (len d) = d.size / 8 := by
    rw [Column.idsCap, if_neg (by decide), hl]; omega
  rw [idsW, hc, ids]
  refine List.map_congr_left fun k _ => ?_
  rw [Column.idAt, show (64 : Nat) = 8 * 8 from rfl, resAt_lane d 8 k (Nat.le_refl _), Nat.mul_comm]

/-- **`offsOf`'s segments**: over an ascending column `i` of codes below `na`, segment `a` (`segRange`) is the
    positions of `i` holding `a`. -/
theorem offsOf_seg (na : Nat) (i : ByteArray) (hs : (ids i).Pairwise (· ≤ ·))
    (hna : na ≤ 2 ^ 27) (hm : len i < min (2 ^ 63) USize.size) :
    (offsOf na i).size / 8 - 1 = na ∧ ∀ a < na, ∀ k,
      ((segRange (offsOf na i) (len i) a).1 ≤ k ∧ k < (segRange (offsOf na i) (len i) a).2) ↔
        ∃ hk : k < (ids i).length, (ids i)[k] = a := by
  have hm' : len i < 2 ^ 63 := Nat.lt_of_lt_of_le hm (Nat.min_le_left _ _)
  have hnaU : na.toUSize.toNat = na := toUSize_fit hna
  obtain ⟨cnts, hcn⟩ : ∃ c, c = Order.groupSizes na.toUSize 64 (len i).toUSize i := ⟨_, rfl⟩
  have ho : offsOf na i = concatBytes #[one 0, sums na.toUSize cnts] := by rw [hcn]; rfl
  have hids : ids cnts = (List.range na).map fun g => (ids i).countP (· == g) := by
    rw [hcn, groupSizes_spec, hnaU, USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hm (Nat.min_le_right _ _)),
      show (64 : USize).toNat = 64 by simp, idsW_64]
  have hlen : len cnts = na := by rw [len_eq_ids, hids]; simp
  have hcnt : ∀ g < na, (Column.bitsAt cnts (g * 8) 8).toNat = (ids i).countP (· == g) := fun g hg => by
    rw [ids_get hids (by simpa using hg)]; simp
  have hsum : ∀ g ≤ na, ((List.range g).map fun h => (Column.bitsAt cnts (h * 8) 8).toNat).sum =
      (ids i).countP (· < g) := fun g hg => by
    rw [← sum_countP_eq]; congr 1
    exact List.map_congr_left fun h hh => hcnt h (by simp at hh; omega)
  have hle : ∀ g, (ids i).countP (· < g) ≤ len i := fun g => by
    rw [len_eq_ids]; exact List.countP_le_length
  obtain ⟨hsz, hget⟩ := offsets_get na.toUSize cnts (by rw [hnaU, hlen]; exact Nat.le_refl _) (by
    rw [hnaU, hsum na (Nat.le_refl _)]; exact Nat.lt_of_le_of_lt (hle na) hm')
  rw [hnaU] at hsz hget
  -- offset `g` is the count below `g`, as `segRange`'s clamp reads it
  have hcut : ∀ g ≤ na, min (atI64 (offsOf na i) g).toNatClampNeg (len i) = (ids i).countP (· < g) := by
    intro g hg
    have e := hget g hg
    rw [hsum g hg] at e
    rw [atI64_eq, show g * 8 = 8 * g from Nat.mul_comm _ _, ho]
    rw [clamp_toInt64 _ (by rw [e]; exact Nat.lt_of_le_of_lt (hle g) hm'), e]
    exact Nat.min_eq_left (hle g)
  refine ⟨by rw [ho]; omega, fun a ha k => ?_⟩
  have h0 := hcut a (Nat.le_of_lt ha)
  have h1 := hcut (a + 1) ha
  have hmono : (ids i).countP (· < a) ≤ (ids i).countP (· < a + 1) := by rw [countP_lt_succ]; omega
  simp only [segRange, h0, h1, Nat.max_eq_right hmono]
  exact seg_iff hs a k

/-- **The rows of `S` folded over `R`'s segments**: from `r`'s code pairs `i`, `j` (`i` ascending, `r` read off them)
    and `t`'s matrix, `bitRowsOver`'s `∨` (`all = false`) holds `r t`, its `∧` (`all = true`) holds `r\t`'s
    `∀` clause; an empty segment answers `false`, resp. `true`. -/
theorem enc_rows {r : A.El → B.El → Prop} {t : B.El → C.El → Prop} {uc : Nat → C.El} (all : Bool) (na : Nat)
    (i j : ByteArray) {s : Bits} (hs : s.Enc ub uc t) (hl : len j = len i) (hsort : (ids i).Pairwise (· ≤ ·))
    (hJ : ∀ b ∈ ids j, b < s.na)
    (hR : ∀ a < na, ∀ y, r (ua a) y ↔
      ∃ (k : Nat) (hk : k < (ids i).length) (hk' : k < (ids j).length), (ids i)[k]'hk = a ∧ ub ((ids j)[k]'hk') = y)
    (hna : na ≤ 2 ^ 27) (hfit : s.na * s.w ≤ 2 ^ 27) (hsw : s.w ≤ 2 ^ 27)
    (hm : len i < min (2 ^ 63) USize.size) :
    (⟨na, s.w, bitRowsOver all s.w.toUSize (offsOf na i) j s.b⟩ : Bits).Enc ua uc
      fun a c => if all then ∀ y, r a y → t y c else ∃ y, r a y ∧ t y c := by
  intro a ha c hc
  change a < na at ha
  change c < s.w at hc
  have hsna : s.na ≤ 2 ^ 27 := Nat.le_trans (Nat.le_mul_of_pos_right _ (by omega)) hfit
  have hW : s.w.toUSize.toNat = s.w := toUSize_fit hsw
  obtain ⟨hsz, hseg⟩ := offsOf_seg na i hsort hna hm
  have hj8 : j.size / 8 = len i := by rw [← hl, len_eq_ids, ids, List.length_map, List.length_range]
  have e := bitRowsOver_spec all s.w.toUSize (offsOf na i) j s.b a c (segRange (offsOf na i) (j.size / 8) a).1
    (segRange (offsOf na i) (j.size / 8) a).2 (by omega) (by omega) rfl
  rw [hW, hj8] at e
  have hJl : (ids j).length = (ids i).length := by rw [← len_eq_ids, ← len_eq_ids, hl]
  -- position `k` of a segment reads row `j[k]` of `t`
  have hbit : ∀ k (hk' : k < (ids j).length),
      Column.bitAt s.b ((atI64 j k).toNatClampNeg * s.w + c) = true ↔ t (ub ((ids j)[k]'hk')) (uc c) := by
    intro k hk'
    have hb' : (ids j)[k]'hk' < s.na := hJ _ (List.getElem_mem hk')
    rw [atI64_eq, clamp_toInt64 _ (by rw [ids_get rfl hk']; omega), ids_get rfl hk']
    exact hs _ hb' c hc
  show Column.bitAt (bitRowsOver all s.w.toUSize (offsOf na i) j s.b) (a * s.w + c) = true ↔
    if all then ∀ y, r (ua a) y → t y (uc c) else ∃ y, r (ua a) y ∧ t y (uc c)
  rw [e]
  cases all
  · simp only [Bool.false_eq_true, ↓reduceIte]
    constructor
    · rintro ⟨k, h1, h2, hb⟩
      obtain ⟨hk, hka⟩ := (hseg a ha k).1 ⟨h1, h2⟩
      have hk' : k < (ids j).length := by rw [hJl]; exact hk
      exact ⟨_, (hR a ha _).2 ⟨k, hk, hk', hka, rfl⟩, (hbit k hk').1 hb⟩
    · rintro ⟨y, hy, hS⟩
      obtain ⟨k, hk, hk', hka, rfl⟩ := (hR a ha y).1 hy
      obtain ⟨h1, h2⟩ := (hseg a ha k).2 ⟨hk, hka⟩
      exact ⟨k, h1, h2, (hbit k hk').2 hS⟩
  · simp only [↓reduceIte]
    constructor
    · intro h y hy
      obtain ⟨k, hk, hk', hka, rfl⟩ := (hR a ha y).1 hy
      obtain ⟨h1, h2⟩ := (hseg a ha k).2 ⟨hk, hka⟩
      exact (hbit k hk').1 (h k h1 h2)
    · intro h k h1 h2
      obtain ⟨hk, hka⟩ := (hseg a ha k).1 ⟨h1, h2⟩
      have hk' : k < (ids j).length := by rw [hJl]; exact hk
      exact (hbit k hk').2 (h _ ((hR a ha _).2 ⟨k, hk, hk', hka, rfl⟩))

/-- **`≫` as bits** (`rep_comp`'s side, `rep_tableC`): `enc_rows`' `∨`, which holds `TP.comp`'s relation. -/
theorem rep_compB {R : TP A B} {S : TP B C} {uc : Nat → C.El} (na : Nat) (i j : ByteArray) {s : Bits}
    (hs : s.Enc ub uc S.den) (hl : len j = len i) (hsort : (ids i).Pairwise (· ≤ ·))
    (hJ : ∀ b ∈ ids j, b < s.na)
    (hR : ∀ a < na, ∀ y, R.den (ua a) y ↔
      ∃ (k : Nat) (hk : k < (ids i).length) (hk' : k < (ids j).length), (ids i)[k]'hk = a ∧ ub ((ids j)[k]'hk') = y)
    (hna : na ≤ 2 ^ 27) (hfit : s.na * s.w ≤ 2 ^ 27) (hsw : s.w ≤ 2 ^ 27)
    (hm : len i < min (2 ^ 63) USize.size) :
    (Bits.comp na i j s).Enc ua uc (TP.comp R S).den :=
  enc_rows false na i j hs hl hsort hJ hR hna hfit hsw hm

#print axioms rep_compB

/-! ### A table's code pairs as bits: `scatterPacked` at one bit -/

/-- Bit `i` is `resAt`'s one-bit field `i`. -/
theorem bitAt_resAt (P : ByteArray) (i : Nat) : Column.bitAt P i = ((Column.resAt P 0 1 i).toNat == 1) := by
  have h := resAt_field P 1 8 i (Or.inl ⟨rfl, rfl⟩)
  rw [Nat.mul_one] at h
  rw [h, Column.bitAt]
  generalize P[i / 8]?.getD 0 = x
  have hs : ((i % 8).toUInt8).toNat % 8 = i % 8 := by simp <;> omega
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq, ← UInt8.toNat_inj, UInt8.toNat_and, UInt8.toNat_shiftRight, hs, Nat.shiftRight_eq_div_pow,
    Nat.and_one_is_mod, UInt8.toNat_one]

/-- `k · w + v` with `v < w` determines `k` and `v`. -/
theorem mul_add_inj {w a b c d : Nat} (hb : b < w) (hd : d < w) : a * w + b = c * w + d ↔ a = c ∧ b = d := by
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩
  have h2 := congrArg (· / w) h
  simp only at h2
  rw [Nat.add_comm (a * w), Nat.add_comm (c * w), Nat.add_mul_div_right _ _ (by omega),
    Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, Nat.div_eq_of_lt hd] at h2
  simp only [Nat.zero_add] at h2; subst h2; omega

/-- **`Bits.ofCodes`, one bit**: bit `(a, b)` is set iff some row `r` holds the codes `(a, b)`. -/
theorem ofCodes_at {na w : Nat} {k v : ByteArray} (hl : len v = len k) (hk : ∀ x ∈ ids k, x < na)
    (hv : ∀ x ∈ ids v, x < w) (hfit : na * w ≤ 2 ^ 27) (hm : len k < USize.size) {a b : Nat} (ha : a < na)
    (hb : b < w) :
    (Bits.ofCodes na w k v).at a b = true ↔
      ∃ (r : Nat) (h1 : r < (ids k).length) (h2 : r < (ids v).length), (ids k)[r]'h1 = a ∧ (ids v)[r]'h2 = b := by
  have hw : w ≤ 2 ^ 27 := Nat.le_trans (Nat.le_mul_of_pos_left _ (by omega)) hfit
  have hna : na ≤ 2 ^ 27 := Nat.le_trans (Nat.le_mul_of_pos_right _ (by omega)) hfit
  have hn : (len k).toUSize.toNat = len k := USize.toNat_ofNat_of_lt' hm
  have hkl : (ids k).length = len k := (len_eq_ids k).symm
  have hvl : (ids v).length = len k := by rw [← len_eq_ids, hl]
  -- the index column: `k[r] · w + v[r]`
  have hwU : (w.toUInt64).toNat = w := by simp; omega
  obtain ⟨M, hM⟩ : ∃ M, M = Kernel.Ew.val Ew.mul Ew.i64 Ew.va nul k (one w.toUInt64) (len k).toUSize := ⟨_, rfl⟩
  have hix : ∀ r (hr : r < len k), (Column.bitsAt (Kernel.Ew.val Ew.add Ew.i64 Ew.vv nul M v (len k).toUSize)
      (r * 8) 8).toNat = (ids k)[r]'(hkl ▸ hr) * w + (ids v)[r]'(hvl ▸ hr) := by
    intro r hr
    have hr' : r < (len k).toUSize.toNat := by rw [hn]; exact hr
    have hkr : (ids k)[r]'(hkl ▸ hr) < na := hk _ (List.getElem_mem _)
    have hvr : (ids v)[r]'(hvl ▸ hr) < w := hv _ (List.getElem_mem _)
    have hlt := idx_lt hkr hvr
    have hkw : (ids k)[r]'(hkl ▸ hr) * w ≤ (ids k)[r]'(hkl ▸ hr) * w + (ids v)[r]'(hvl ▸ hr) := Nat.le_add_right _ _
    have ek := ids_get (b := k) rfl (hkl ▸ hr)
    have ev := ids_get (b := v) rfl (hvl ▸ hr)
    have em : (Column.bitsAt M (r * 8) 8).toNat = (ids k)[r]'(hkl ▸ hr) * w := by
      have h := (valStep_key (Column.bitsAt k (r * 8) 8) (Column.bitsAt (one w.toUInt64) 0 8)
        (by rw [ek]; omega) (by rw [bitsAt_one, hwU]; omega)).1 (by rw [ek, bitsAt_one, hwU]; omega)
      rw [ek, bitsAt_one, hwU] at h
      rw [hM, val_va_get _ _ _ _ hr', bitsAt_one]; exact h
    have h := (valStep_key (Column.bitsAt M (r * 8) 8) (Column.bitsAt v (r * 8) 8)
      (by rw [em]; omega) (by rw [ev]; omega)).2 (by rw [em, ev]; omega)
    rw [em, ev] at h
    rw [val_vv_get _ _ _ _ hr']; exact h
  -- the matrix the codes are scattered into: no bit set
  have hz : (zeros (na + 1)).size / 8 = na + 1 := by
    rw [zeros, KernelWF.Ew.val_size, USize.toNat_ofNat_of_lt'
      (Nat.lt_of_lt_of_le (by omega : na + 1 < 2 ^ 32) USize.le_size)]
    show (na + 1) * 8 / 8 = _; omega
  have hwT : w.toUSize.toNat = w := toUSize_fit hw
  have hdsz : (Bits.const false na w).b.size = (na * w + 7) / 8 := by
    simp only [Bits.const, bitRowsOver]; rw [KernelWF.packOf_size, hz, hwT]; simp
  have hd : ∀ t < na * w, Column.bitAt (Bits.const false na w).b t = false := by
    intro t ht
    simp only [Bits.const, bitRowsOver]
    rw [bitAt_packOf _ _ _ (by rw [hz, hwT]; simpa using ht)]
    simp [segRange]
  have hab := idx_lt ha hb
  simp only [Bits.ofCodes, Bits.at]
  rw [← hM]
  have hix8 : (Kernel.Ew.val Ew.add Ew.i64 Ew.vv nul M v (len k).toUSize).size / 8 = len k := by
    rw [KernelWF.Ew.val_size, hn]; show len k * 8 / 8 = _; omega
  generalize Kernel.Ew.val Ew.add Ew.i64 Ew.vv nul M v (len k).toUSize = IX at hix hix8 ⊢
  rw [bitAt_resAt]
  obtain ⟨-, hsc⟩ := scatterPacked_sub 1 8 (Or.inl ⟨rfl, rfl⟩) 1 (by simp) (Bits.const false na w).b IX ⟨#[1]⟩ 0 true
  rw [hsc _ (by rw [hdsz]; omega), hix8]
  cases hL : ((List.range (len k)).filter fun r => (Column.bitsAt IX (r * 8) 8).toNat == a * w + b).getLast? with
  | none =>
    have hnil := List.getLast?_eq_none_iff.1 hL
    simp only
    rw [← bitAt_resAt, hd _ hab]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨r, h1, h2, e1, e2⟩
    have hr : r < len k := hkl ▸ h1
    have := List.filter_eq_nil_iff.1 hnil r (List.mem_range.2 hr)
    rw [hix r hr] at this
    exact this (by simp [e1, e2])
  | some r =>
    have hmem := List.mem_of_getLast? hL
    rw [List.mem_filter, List.mem_range] at hmem
    obtain ⟨hr, he⟩ := hmem
    rw [hix r hr, beq_iff_eq, mul_add_inj (hv _ (List.getElem_mem _)) hb] at he
    have h1 : (Column.resAt ⟨#[1]⟩ 0 1 0).toNat = 1 := by rw [resAt_field _ 1 8 _ (Or.inl ⟨rfl, rfl⟩)]; decide
    simp only [↓reduceIte, USize.toNat_zero, Nat.add_zero, h1]
    exact ⟨fun _ => ⟨r, hkl ▸ hr, hvl ▸ hr, he.1, he.2⟩, fun _ => rfl⟩

/-- **A leaf as bits**: where `R`'s pairs at codes `a < na`, `b < nb` are the rows holding the codes `(a, b)`, the
    scattered code pairs hold `R`. -/
theorem rep_leafB {R : Rel A B} {na nb : Nat} {k v : ByteArray} (hl : len v = len k) (hk : ∀ x ∈ ids k, x < na)
    (hv : ∀ x ∈ ids v, x < nb) (hfit : na * nb ≤ 2 ^ 27) (hm : len k < USize.size)
    (hR : ∀ a < na, ∀ b < nb, rep R (ua a) (ub b) ↔
      ∃ (r : Nat) (h1 : r < (ids k).length) (h2 : r < (ids v).length), (ids k)[r]'h1 = a ∧ (ids v)[r]'h2 = b) :
    (Bits.ofCodes na nb k v).Enc ua ub (TP.leaf R).den := fun a ha b hb =>
  (ofCodes_at hl hk hv hfit hm ha hb).trans (hR a ha b hb).symm

#print axioms ofCodes_at
#print axioms rep_leafB

end LeetQ.Rel.Lang.Bits
