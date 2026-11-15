/-
  The sum, order and arithmetic ops under the run-time bit, as `CRel` does for `≫`, `∩`, `∪`: each twin
  `inlC`/`inrC`/`juncC`/`sumC`/`ltC`/`leqC`/`succC`/`ascC` answers its relation and a bit deciding every count
  bound its read-back theorem takes, so `rep_<op>C` holds under that one bit.
-/
import LeetQ.Rel.CRel
import LeetQ.Run.CRelDef
import LeetQ.Rel.RepOrd
import LeetQ.Run.CRelArithDef
import LeetQ.Rel.KernelWF.AscSpec

namespace LeetQ.Rel

namespace Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet
open OpsN UnionN

variable {A B C D : Obj}

/-- **`rep (inl X) = X? ι₁` under `inlC`'s bit**: the bit is `rep_inl`'s `h63`. -/
theorem rep_inlC {n : USize} (X : Vals A n) (hb : (inlC (B := B) X).2 = true) :
    rep (inlC (B := B) X).1 = corefl (A := (⟨A.El⟩ : RelSet.{0})) (fun x => ∃ i, X.row i = x) ≫
      (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₁ :=
  rep_inl X (of_decide_eq_true hb)

/-- **`rep (inr Y) = Y? ι₂` under `inrC`'s bit**: the bit is `rep_inr`'s `h63`. -/
theorem rep_inrC {n : USize} (Y : Vals B n) (hb : (inrC (A := A) Y).2 = true) :
    rep (inrC (A := A) Y).1 = corefl (A := (⟨B.El⟩ : RelSet.{0})) (fun y => ∃ i, Y.row i = y) ≫
      (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₂ :=
  rep_inr Y (of_decide_eq_true hb)

/-- **`rep [R, S] = [rep R, rep S]` under `juncC`'s bit**: `need`'s guard is `rep_junc_full`'s `hN`, the decided
    bound its `h63`, the raze's bit its `hF` (`razeC_fits`). -/
theorem rep_juncC (R : Rel A C) (S : Rel B C) (hb : (juncC R S).2 = true) :
    rep (juncC R S).1 = Freyd.Alg.junc (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩) (rep R) (rep S) := by
  unfold juncC need at hb
  split at hb
  · rename_i hN
    simp only [okbit] at hb
    exact rep_junc_full R S hN hb.1 (Obj.razeC_fits C R.val S.val _ rfl _ hb.2)
  · exact absurd hb Bool.false_ne_true

/-- **`rep (R + S) = ι₁° rep R ι₁ ∪ ι₂° rep S ι₂` under `sumC`'s bit**: the bit is `rep_sum`'s `hN` and `h63`. -/
theorem rep_sumC (R : Rel A C) (S : Rel B D) (hb : (sumC R S).2 = true) :
    rep (sumC R S).1 =
      ((sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₁° ≫ rep R ≫ (sumCop (⟨C.El⟩ : RelSet.{0}) ⟨D.El⟩).u₁) ∪
      ((sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₂° ≫ rep S ≫ (sumCop (⟨C.El⟩ : RelSet.{0}) ⟨D.El⟩).u₂) := by
  simp only [sumC, okbit] at hb; exact rep_sum R S hb.1 hb.2

/-- **`rep (lt U)` under `ltC`'s bit**: the decided bounds are `rep_lt`'s `hN`, `h63`, the diff's pair codes' bit
    its `hc` (`codesC_fits`, `codes_faithful_wf`, `pairs_eq_codes`), the `fitsN` bits its `hk`, `hv`
    (`pickFits_of_fitsN`). -/
theorem rep_ltC {n : USize} (U : Vals (.atom .long) n) (h : QAtomicType.long ≠ .general)
    (hb : (ltC U h).2 = true) (a b : Int64) :
    rep (ltC U h).1 a b ↔ (∃ i, U.row i = a) ∧ (∃ j, U.row j = b) ∧ a < b := by
  simp only [ltC, diffC, okbit] at hb
  obtain ⟨⟨⟨⟨hcb, hk⟩, hv⟩, hN⟩, h63⟩ := hb
  exact rep_lt U h hN h63 (ltRows U h) rfl
    (by rw [pairs_eq_codes, map_pair]; exact (codes_faithful_wf _ _ (Obj.codesC_fits _ _ hcb)).1)
    (pickFits_range _ _ hk) (pickFits_range _ _ hv) a b

/-- **`rep (leq U)` under `leqC`'s bit**: `ltC`'s bit gives `rep_leq`'s `rep_lt` hypotheses as in `rep_ltC`;
    `unionC`'s guard its `hNU`, its codes' bits `huK`, `huV` (`codesC_fits`, `codes_faithful_wf`), its `fitsN`
    bits `huk`, `huv`. The razes' bits go unused: `rep_leq` razes atoms, which fit by their count. -/
theorem rep_leqC {n : USize} (U : Vals (.atom .long) n) (h : QAtomicType.long ≠ .general)
    (hb : (leqC U h).2 = true) (a b : Int64) :
    rep (leqC U h).1 a b ↔ (∃ i, U.row i = a) ∧ (∃ j, U.row j = b) ∧ a ≤ b := by
  change ((ltC U h).2 && (unionC (lt U h) (idU U)).2) = true at hb
  simp only [ltC, diffC, okbit] at hb
  obtain ⟨⟨⟨⟨⟨hcb, hk⟩, hv⟩, hN⟩, h63⟩, hu⟩ := hb
  unfold unionC need at hu
  split at hu
  · rename_i hNU
    simp only [okbit] at hu
    obtain ⟨⟨⟨⟨⟨-, -⟩, hkc⟩, hvc⟩, hkf⟩, hvf⟩ := hu
    -- a raze twin's `.1` is `raze` at each constructor of the side
    have hr : ∀ (X : Obj) (cs : Array (Part X)) h, (X.razeC cs h).1 = X.raze cs h := by
      intro X; cases X <;> intros <;> rfl
    simp only [hr] at hkc hvc hkf hvf
    exact rep_leq U h hN h63 (ltRows U h) rfl
      (by rw [pairs_eq_codes, map_pair]; exact (codes_faithful_wf _ _ (Obj.codesC_fits _ _ hcb)).1)
      (pickFits_range _ _ hk) (pickFits_range _ _ hv) hNU _ rfl (oneOK_of_codesC _ _ hkc) (oneOK_of_codesC _ _ hvc)
      (pickFits_range _ _ hkf) (pickFits_range _ _ hvf) a b
  · exact absurd hu Bool.false_ne_true

/-- **`rep (succ U)` under `succC`'s bit**: the codes' bit gives `rep_succ`'s `hc` (`codesC_fits`,
    `codes_faithful_wf`, less its `w < 8` clause). -/
theorem rep_succC {n : USize} (U : Vals (.atom .long) n) (hb : (succC U).2 = true) (u w : Int64) :
    rep (succC U).1 u w ↔ (∃ i, U.row i = u) ∧ w = Ew.intStep Ew.add nul u 1 ∧ ∃ j, U.row j = w := by
  have hc := (codes_faithful_wf (.atom .long) #v[⟨n, valCol Ew.add Ew.va (longsOf U) (one 1)⟩, ⟨n, U⟩]
    (Obj.codesC_fits (.atom .long) _ hb)).1
  exact rep_succ U _ rfl _ rfl
    ⟨@fun _ _ hk hl _ _ hi hj => hc.1 hk hl hi hj, fun hk => ⟨(hc.2 hk).1, (hc.2 hk).2.1, (hc.2 hk).2.2.1⟩⟩ u w

/-- **`expand`'s copies' count is the counts summed**, each count below `2^63` (`expand_idx`): the `O(1)` length a
    twin decides a count bound on, in place of folding the counts. -/
theorem len_expand_sum {n : USize} {cnt : ByteArray} (hl : len cnt = n.toNat)
    (hc : ∀ t < n.toNat, (Column.bitsAt cnt (t * 8) 8).toNat < 2 ^ 63) :
    len (expandBytes 8 0 (tilLongs n) cnt) =
      ((List.range n.toNat).map fun r => (Column.bitsAt cnt (r * 8) 8).toNat).sum := by
  rw [len_eq_ids, expand_idx (Nat.le_of_eq hl) (fun t ht => hc t (hl ▸ ht)), List.length_flatMap, hl]
  simp only [List.length_replicate]

/-- `expand` of an array side's counts copies their sum, the payload count below `2^63` (`slicesOf_row`). -/
theorem len_expand_slicesOf {B : Obj} {n : USize} (X : Vals (.arr B) n) (hp : X.1.toNat < 2 ^ 63) :
    len (expandBytes 8 0 (tilLongs n) (slicesOf X).2) =
      ((List.range n.toNat).map fun r => (Column.bitsAt (slicesOf X).2 (r * 8) 8).toNat).sum :=
  len_expand_sum (len_slices _ _ _ _).2 fun t ht => by have := (slicesOf_row X hp ht).1; omega

/-- **`rep (asc X)` under `ascC`'s bit**, `S`-ordered as `rep_asc` reads it: the decided bounds are
    `rep_asc`'s `hp`, `hn`, `hfX`; inside `expand` the copies' count decided its `hS`, `expand`'s guard its `hU`,
    both through `len_expand_slicesOf`, and the payload's fit its `hf`. -/
theorem rep_ascC_by {n : USize} (X : Vals (.arr B) n) (hb : (ascC X).2 = true)
    (R : ∀ {m : USize}, Vals B m → Nat → Nat → Prop) (S : B.El → B.El → Prop)
    (hsort : ∀ {m : USize} (c : Vals B m), Vals.PickFits B c (List.range m.toNat) →
      (ids (Obj.sortBy B c (tilLongs m))).Perm (List.range m.toNat) ∧ (ids (Obj.sortBy B c (tilLongs m))).Pairwise (R c))
    (hRS : ∀ {m : USize} (c : Vals B m) a b (ha : a < m.toNat) (hb : b < m.toNat), R c a b →
      S (c.row ⟨a, ha⟩) (c.row ⟨b, hb⟩)) :
    (∀ xs ys, rep (ascC X).1 xs ys → (∃ j, X.row j = xs) ∧ ys.Perm xs ∧ ys.Pairwise S) ∧
      ∀ xs, (∃ j, X.row j = xs) → ∃ ys, rep (ascC X).1 xs ys := by
  simp only [ascC, expand, need, okbit] at hb
  obtain ⟨⟨⟨hp, hn⟩, hfX⟩, hb⟩ := hb
  split at hb
  · rename_i hx
    simp only [okbit, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨hm, hf⟩ := hb
    rw [USize.toNat_ofNat_of_lt' hx, len_expand_slicesOf X hp] at hm
    rw [len_expand_slicesOf X hp] at hx
    exact rep_asc X hp hn hm hx hfX hf R S hsort hRS
  · exact absurd hb Bool.false_ne_true

/-- **`rep (asc X)` at `long`**: an array of `X` goes to `ys` exactly when `ys` is a permutation of it,
    ascending — the one sorted member of its `perm` class (`rep_ascC_by` at `sortBy_long`, unique by
    `≤`'s antisymmetry). -/
theorem rep_ascC_long {n : USize} (X : Vals (.arr (.atom .long)) n) (hb : (ascC X).2 = true) :
    ∀ xs ys, rep (ascC X).1 xs ys ↔ (∃ j, X.row j = xs) ∧ ys.Perm xs ∧ ys.Pairwise (· ≤ ·) := by
  obtain ⟨hf, hd⟩ := rep_ascC_by X hb
    (fun c i j => ∀ (hc : i < _) (hc' : j < _), c.get ⟨i, hc⟩ < c.get ⟨j, hc'⟩ ∨
      (c.get ⟨i, hc⟩ = c.get ⟨j, hc'⟩ ∧ i < j)) (· ≤ ·) (fun c _ => sortBy_long c)
    (fun c a b ha hb h => by
      rw [Vals.row_atom, Vals.row_atom]; show _ ≤ _; rw [Int64.le_iff_lt_or_eq]
      rcases h ha hb with h | ⟨h, -⟩
      · exact .inl h
      · exact .inr h)
  refine fun xs ys => ⟨hf xs ys, fun ⟨hx, hpe, hs⟩ => ?_⟩
  obtain ⟨ys', h'⟩ := hd xs hx
  obtain ⟨-, hpe', hs'⟩ := hf xs ys' h'
  rwa [List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => Int64.le_antisymm h1 h2) hs hs' (hpe.trans hpe'.symm)]

/-- **`rep (asc X)`**, `asc` being `ascC`, `B` ordered: an array of `X` goes to a permutation of it ascending
    by `Obj.lt` (`sortsAsc_all`, `sortBy_asc`), and every array of `X` goes somewhere. -/
theorem rep_ascC {n : USize} (X : Vals (.arr B) n) (hB : B.Ordered) (hb : (ascC X).2 = true) :
    (∀ xs ys, rep (ascC X).1 xs ys → (∃ j, X.row j = xs) ∧ ys.Perm xs ∧ ys.Pairwise fun x y => ¬ B.lt y x) ∧
      ∀ xs, (∃ j, X.row j = xs) → ∃ ys, rep (ascC X).1 xs ys :=
  rep_ascC_by X hb (fun c i j => ∀ (hi : i < _) (hj : j < _), ¬ B.lt (c.row ⟨j, hj⟩) (c.row ⟨i, hi⟩))
    (fun x y => ¬ B.lt y x) (fun {m} c hc => by
      have hs := small_of_pickFits B c _ hc
      have hl : len (tilLongs m) < USize.size := by rw [len_tilLongs]; exact m.toNat_lt_size
      have hp : ∀ i ∈ ids (tilLongs m), i < m.toNat := fun i h => by rw [ids_tilLongs] at h; exact List.mem_range.1 h
      refine ⟨?_, sortBy_asc (sortsAsc_all B hB) c hs _ hl hp⟩
      rw [← ids_tilLongs]
      exact (sortsAsc_all B hB c hs _ hl hp (fun _ _ => True)
        (List.pairwise_iff_getElem.2 fun _ _ _ _ _ => trivial)).1)
    (fun _ _ _ _ _ h => h _ _)

#print axioms rep_juncC
#print axioms rep_ltC
#print axioms rep_leqC
#print axioms rep_succC
#print axioms rep_ascC_long

end Rep

namespace CRel

open QLean QLean.Kernel LeetQ.Rel.Alg Freyd Freyd.Alg Freyd.Alg.RelSet LeetQ.Rel.Rep

variable {A B C D : Obj}

theorem rep_inl {n : USize} (X : Vals A n) (hb : (inl (B := B) X).ok = true) :
    rep (inl (B := B) X).rel = corefl (A := (⟨A.El⟩ : RelSet.{0})) (fun x => ∃ i, X.row i = x) ≫
      (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₁ :=
  rep_inlC X hb

theorem rep_inr {n : USize} (Y : Vals B n) (hb : (inr (A := A) Y).ok = true) :
    rep (inr (A := A) Y).rel = corefl (A := (⟨B.El⟩ : RelSet.{0})) (fun y => ∃ i, Y.row i = y) ≫
      (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₂ :=
  rep_inrC Y hb

theorem rep_junc (R : CRel A C) (S : CRel B C) (hb : (R.junc S).ok = true) :
    rep (R.junc S).rel = Freyd.Alg.junc (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩) (rep R.rel) (rep S.rel) := by
  have e : R.junc S = _ := guard_eq ok hb; rw [e] at hb ⊢; exact rep_juncC R.rel S.rel hb

theorem rep_sum (R : CRel A C) (S : CRel B D) (hb : (R.sum S).ok = true) :
    rep (R.sum S).rel =
      ((sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₁° ≫ rep R.rel ≫ (sumCop (⟨C.El⟩ : RelSet.{0}) ⟨D.El⟩).u₁) ∪
      ((sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).u₂° ≫ rep S.rel ≫ (sumCop (⟨C.El⟩ : RelSet.{0}) ⟨D.El⟩).u₂) := by
  have e : R.sum S = _ := guard_eq ok hb; rw [e] at hb ⊢; exact rep_sumC R.rel S.rel hb

theorem rep_lt {n : USize} (U : Vals (.atom .long) n) (h : QAtomicType.long ≠ .general) (hb : (lt U h).ok = true)
    (a b : Int64) : rep (lt U h).rel a b ↔ (∃ i, U.row i = a) ∧ (∃ j, U.row j = b) ∧ a < b :=
  rep_ltC U h hb a b

theorem rep_leq {n : USize} (U : Vals (.atom .long) n) (h : QAtomicType.long ≠ .general) (hb : (leq U h).ok = true)
    (a b : Int64) : rep (leq U h).rel a b ↔ (∃ i, U.row i = a) ∧ (∃ j, U.row j = b) ∧ a ≤ b :=
  rep_leqC U h hb a b

theorem rep_succ {n : USize} (U : Vals (.atom .long) n) (hb : (succ U).ok = true) (u w : Int64) :
    rep (succ U).rel u w ↔ (∃ i, U.row i = u) ∧ w = Ew.intStep Ew.add nul u 1 ∧ ∃ j, U.row j = w :=
  rep_succC U hb u w

theorem rep_asc_long {n : USize} (X : Vals (.arr (.atom .long)) n) (hb : (asc X).ok = true) :
    ∀ xs ys, rep (asc X).rel xs ys ↔ (∃ j, X.row j = xs) ∧ ys.Perm xs ∧ ys.Pairwise (· ≤ ·) :=
  rep_ascC_long X hb

theorem rep_asc {n : USize} (X : Vals (.arr B) n) (hB : B.Ordered) (hb : (asc X).ok = true) :
    (∀ xs ys, rep (asc X).rel xs ys → (∃ j, X.row j = xs) ∧ ys.Perm xs ∧ ys.Pairwise fun x y => ¬ B.lt y x) ∧
      ∀ xs, (∃ j, X.row j = xs) → ∃ ys, rep (asc X).rel xs ys :=
  rep_ascC X hB hb

#print axioms rep_asc

end CRel

end LeetQ.Rel
