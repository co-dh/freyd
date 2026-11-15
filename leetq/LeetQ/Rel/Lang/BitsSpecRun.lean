/-
The bit run's bookkeeping: which columns a plan reads (`colsL`), the picked parts `run?` sizes its matrices by
(`spOf`), and a leaf's matrix from `codeAll`'s codes under `uOf`.
-/
import LeetQ.Rel.Lang.BitsSpecLdiv
import LeetQ.Rel.Lang.BitsSpecPairs
import LeetQ.Rel.Lang.BitsSpecCode

namespace LeetQ.Rel.Lang.Bits

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep

/-- The columns `TP.cols` appends, in its order. -/
def TP.colsL : {A B : Obj} → TP A B → List Col
  | A, B, .leaf R => [⟨A, ⟨R.n, R.key⟩⟩, ⟨B, ⟨R.n, R.val⟩⟩]
  | _, _, .comp R S | _, _, .meet R S | _, _, .join R S | _, _, .diff R S => R.colsL ++ S.colsL
  | _, _, .conv R => R.colsL
  | B, C, .ldiv R S UB UC =>
    R.colsL ++ S.colsL ++ [⟨B, ⟨UB.n, UB.key⟩⟩, ⟨B, ⟨UB.n, UB.val⟩⟩, ⟨C, ⟨UC.n, UC.key⟩⟩, ⟨C, ⟨UC.n, UC.val⟩⟩]

theorem cols_toList : ∀ {A B : Obj} (p : TP A B) (acc : Array Col), (p.cols acc).toList = acc.toList ++ p.colsL
  | _, _, .leaf _, _ => by simp [TP.cols, TP.colsL, relCols]
  | _, _, .comp R S, acc | _, _, .meet R S, acc | _, _, .join R S, acc | _, _, .diff R S, acc => by
    simp [TP.cols, TP.colsL, cols_toList S, cols_toList R]
  | _, _, .conv R, acc => by simp [TP.cols, TP.colsL, cols_toList R]
  | _, _, .ldiv R S _ _, acc => by simp [TP.cols, TP.colsL, relCols, cols_toList S, cols_toList R]

/-- An object's picked part as `run?` reads it from `codeAll`'s second result. -/
def spOf (sps : Array Col) (X : Obj) : Part X := match sps.find? (·.1 == X) with
  | some ⟨Y, q⟩ => if h : Y = X then h ▸ q else ⟨0, Vals.empty X⟩
  | none => ⟨0, Vals.empty X⟩

theorem spOf_eq {sps : Array Col} {X : Obj} {q : Part X} (h : sps.find? (·.1 == X) = some ⟨X, q⟩) :
    spOf sps X = q := by simp [spOf, h]

/-- `run?` is `codeAll`, `fits` with `capsOK` and the root read back at `spOf`. -/
theorem run?_eq {A B : Obj} (p : TP A B) : run? p = (do
    let (ids, sps) ← codeAll (p.cols #[])
    guard ((p.fits fun X => (spOf sps X).1.toNat) && capsOK (p.cols #[]) sps (spOf sps A) (spOf sps B))
    pure ((Id.run ((p.bits ids fun X => (spOf sps X).1.toNat).run' 0)).table (spOf sps A) (spOf sps B))) := rfl

/-- A leaf's matrix reads the two code columns at the state and moves it by two. -/
theorem bits_leaf (ids : Array ByteArray) (sz : Obj → Nat) {A B : Obj} (R : Rel A B) (n : Nat) :
    ((TP.leaf R).bits ids sz).run n = (Bits.ofCodes (sz A) (sz B) (ids.getD n .empty) (ids.getD (n + 1) .empty), n + 2) :=
  by rw [TP.bits]; rfl

/-- **A leaf at position `n` of the coded columns** holds `TP.leaf R`'s relation under `uOf`, its shape the objects'
    picked counts. -/
theorem enc_leaf (cs : Array Col) {out : Array ByteArray} {sps : Array Col} (h : codeAll cs = some (out, sps))
    {A B : Obj} (R : Rel A B) {n : Nat} (hj : n + 1 < cs.size) (ek : cs[n] = ⟨A, ⟨R.n, R.key⟩⟩)
    (ev : cs[n + 1] = ⟨B, ⟨R.n, R.val⟩⟩)
    (hfit : (spOf sps A).1.toNat * (spOf sps B).1.toNat ≤ 2 ^ 27) :
    let x := (((TP.leaf R).bits out fun X => (spOf sps X).1.toNat).run n).1
    x.na = (spOf sps A).1.toNat ∧ x.w = (spOf sps B).1.toNat ∧ x.Enc (uOf cs A) (uOf cs B) (TP.leaf R).den := by
  obtain ⟨qa, qb, ha, hb, he⟩ := codeAll_leaf cs h R (by omega) hj ek ev
  rw [spOf_eq ha, spOf_eq hb] at hfit; simp only [bits_leaf, spOf_eq ha, spOf_eq hb]
  exact ⟨rfl, rfl, he hfit⟩

#print axioms enc_leaf

/-! ### What `run?`'s success leaves: the coding, the fits and the capacities -/

theorem run?_some {A B : Obj} {p : TP A B} {R : Rel A B} (h : run? p = some R) :
    ∃ out sps, codeAll (p.cols #[]) = some (out, sps) ∧ (p.fits fun X => (spOf sps X).1.toNat) = true ∧
      capsOK (p.cols #[]) sps (spOf sps A) (spOf sps B) = true := by
  rw [run?_eq] at h
  cases hc : codeAll (p.cols #[]) with
  | none => simp [hc] at h
  | some r =>
    obtain ⟨out, sps⟩ := r
    cases hb : ((p.fits fun X => (spOf sps X).1.toNat) && capsOK (p.cols #[]) sps (spOf sps A) (spOf sps B))
    · rw [Bool.and_eq_false_iff] at hb; rcases hb with hb | hb <;> simp [hc, hb, guard, failure] at h
    · rw [Bool.and_eq_true] at hb; exact ⟨out, sps, rfl, hb.1, hb.2⟩

/-- Every column of the plan has fewer than `2^63` rows. -/
theorem caps_col {A B : Obj} {p : TP A B} {sps : Array Col} {pa : Part A} {pb : Part B}
    (h : capsOK (p.cols #[]) sps pa pb = true) : ∀ c ∈ p.colsL, c.2.1.toNat < 2 ^ 63 := fun c hc => by
  simp only [capsOK, Bool.and_eq_true, Array.all_eq_true', decide_eq_true_eq] at h
  exact h.1.1.1 c (by rw [← Array.mem_toList_iff, cols_toList]; simp [hc])

/-- Every object has at most `2²⁷` codes. -/
theorem caps_sz {A B : Obj} {cs sps : Array Col} {pa : Part A} {pb : Part B} (h : capsOK cs sps pa pb = true)
    (X : Obj) : (spOf sps X).1.toNat ≤ 2 ^ 27 := by
  simp only [capsOK, Bool.and_eq_true, Array.all_eq_true', decide_eq_true_eq] at h
  unfold spOf
  split
  · next Y q hf =>
    split
    · next e => subst e; exact h.1.1.2 _ (Array.mem_of_find?_eq_some hf)
    · simp
  · simp

/-- The root's picks at any at most `|A| · |B|` rows are in range. -/
theorem caps_pick {A B : Obj} {cs sps : Array Col} {pa : Part A} {pb : Part B} (h : capsOK cs sps pa pb = true)
    {ps : List Nat} (hl : ps.length ≤ pa.1.toNat * pb.1.toNat) : Vals.PickFits A pa.2 ps ∧ Vals.PickFits B pb.2 ps := by
  simp only [capsOK, Bool.and_eq_true] at h
  exact ⟨pickFits_of_fitsN A pa.2 _ h.1.2 ps hl, pickFits_of_fitsN B pb.2 _ h.2 ps hl⟩

/-! ### Code pairs as `rep_compB` and `rep_ldivB` read them -/

/-- Some position of `g`, `o` holds the codes `a`, `b`. -/
def PairAt (g o : ByteArray) (a b : Nat) : Prop :=
  ∃ (r : Nat) (h1 : r < (ids g).length) (h2 : r < (ids o).length), (ids g)[r]'h1 = a ∧ (ids o)[r]'h2 = b

/-- **`sortBy` re-orders the code pairs** (`grade_ofLongs`, `gather`): as many, `g` ascending, the same pairs. -/
theorem sortBy_spec (g o : ByteArray) (hl : len o = len g) (hN : len g < USize.size)
    (h63 : ∀ t ∈ ids g, t < 2 ^ 63) :
    len (sortBy g o).1 = len g ∧ len (sortBy g o).2 = len g ∧ (ids (sortBy g o).1).Pairwise (· ≤ ·) ∧
      ∀ a b, PairAt (sortBy g o).1 (sortBy g o).2 a b ↔ PairAt g o a b := by
  have hget : ∀ t < len g, (ids g).getD t 0 = (Column.bitsAt g (t * 8) 8).toNat := fun t ht => by
    have ht' : t < (ids g).length := by rw [← len_eq_ids]; exact ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht', Option.getD_some]
    exact ids_getElem ht'
  obtain ⟨hgp, hgs⟩ := grade_ofLongs g hN fun i hi => by
    rw [← hget i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [← len_eq_ids]; exact hi),
      Option.getD_some]
    exact h63 _ (List.getElem_mem _)
  show len (gather 8 g _) = _ ∧ len (gather 8 o _) = _ ∧ (ids (gather 8 g _)).Pairwise _ ∧
    ∀ a b, PairAt (gather 8 g _) (gather 8 o _) a b ↔ _
  generalize (Code.ofLongs g).grade = P at hgp hgs
  have hlt : ∀ t ∈ ids P, t < len g := fun t ht => List.mem_range.1 (hgp.subset ht)
  have e1 : ids (gather 8 g P) = (ids P).map fun t => (ids g).getD t 0 := ids_gather8 hlt
  have e2 : ids (gather 8 o P) = (ids P).map fun t => (ids o).getD t 0 := ids_gather8 (by rw [hl]; exact hlt)
  have hPl : (ids P).length = len g := by rw [hgp.length_eq, List.length_range]
  refine ⟨by rw [len_eq_ids, e1, List.length_map, hPl], by rw [len_eq_ids, e2, List.length_map, hPl], ?_, ?_⟩
  · rw [e1, List.pairwise_map]
    exact hgs.imp_of_mem fun {p q} hp hq h => by rw [hget p (hlt p hp), hget q (hlt q hq)]; omega
  · intro a b
    simp only [PairAt, e1, e2, List.getElem_map, List.length_map]
    constructor
    · rintro ⟨r, h1, -, rfl, rfl⟩
      have ht : (ids P)[r] < (ids g).length := by rw [← len_eq_ids]; exact hlt _ (List.getElem_mem h1)
      have ht' : (ids P)[r] < (ids o).length := by rw [← len_eq_ids, hl, len_eq_ids]; exact ht
      exact ⟨_, ht, ht', by simp [List.getD_eq_getElem?_getD, ht], by simp [List.getD_eq_getElem?_getD, ht']⟩
    · rintro ⟨r, h1, h2, rfl, rfl⟩
      obtain ⟨i, hi, e⟩ := List.getElem_of_mem
        (hgp.symm.subset (List.mem_range.2 (by rw [len_eq_ids]; exact h1)) : r ∈ ids P)
      exact ⟨i, hi, hi, by simp [e, List.getD_eq_getElem?_getD, h1], by simp [e, List.getD_eq_getElem?_getD, h2]⟩

variable {A B : Obj} {ua : Nat → A.El} {ub : Nat → B.El}

/-- **Code pairs `(g, o)` in the form `rep_compB`'s and `rep_ldivB`'s premises take**: as many of each, `g`
    ascending, `o` below `nb`, fewer than `2^63`, and `r` from the code `a < na` exactly to the elements at the
    codes paired with `a`. -/
def PairsOK (ua : Nat → A.El) (ub : Nat → B.El) (na nb : Nat) (r : A.El → B.El → Prop) (g o : ByteArray) : Prop :=
  len o = len g ∧ (ids g).Pairwise (· ≤ ·) ∧ (∀ t ∈ ids o, t < nb) ∧ len g < min (2 ^ 63) USize.size ∧
    ∀ a < na, ∀ y, r (ua a) y ↔
      ∃ (k : Nat) (hk : k < (ids g).length) (hk' : k < (ids o).length), (ids g)[k]'hk = a ∧ ub ((ids o)[k]'hk') = y

/-- **A table's pairs sorted**: its code columns `k`, `v` holding `r`, sorted by `k`. -/
theorem pairsOK_sort {r : A.El → B.El → Prop} {na nb : Nat} {k v : ByteArray} (hl : len v = len k)
    (hm : len k < min (2 ^ 63) USize.size) (hk : ∀ t ∈ ids k, t < 2 ^ 63) (hv : ∀ t ∈ ids v, t < nb)
    (hR : ∀ a < na, ∀ y, r (ua a) y ↔
      ∃ (q : Nat) (h1 : q < (ids k).length) (h2 : q < (ids v).length), (ids k)[q]'h1 = a ∧ ub ((ids v)[q]'h2) = y) :
    PairsOK ua ub na nb r (sortBy k v).1 (sortBy k v).2 := by
  obtain ⟨e1, e2, hs, hP⟩ := sortBy_spec k v hl (Nat.lt_of_lt_of_le hm (Nat.min_le_right _ _)) hk
  have via : ∀ (g o : ByteArray) a y, (∃ (q : Nat) (h1 : q < (ids g).length) (h2 : q < (ids o).length),
      (ids g)[q]'h1 = a ∧ ub ((ids o)[q]'h2) = y) ↔ ∃ b, PairAt g o a b ∧ ub b = y := fun _ _ _ _ =>
    ⟨fun ⟨q, h1, h2, e, e'⟩ => ⟨_, ⟨q, h1, h2, e, rfl⟩, e'⟩, fun ⟨_, ⟨q, h1, h2, e, e'⟩, e''⟩ => ⟨q, h1, h2, e, e' ▸ e''⟩⟩
  refine ⟨e2.trans e1.symm, hs, fun t ht => ?_, by rw [e1]; exact hm, fun a _ y => ?_⟩
  · obtain ⟨q, h2, rfl⟩ := List.getElem_of_mem ht
    have h1 : q < (ids (sortBy k v).1).length := by rw [← len_eq_ids, ← e2.trans e1.symm, len_eq_ids]; exact h2
    obtain ⟨q', -, h2', -, e⟩ := (hP _ _).1 ⟨q, h1, h2, rfl, rfl⟩
    exact e ▸ hv _ (List.getElem_mem h2')
  · rw [hR a ‹_› y, via, via]; exact exists_congr fun b => and_congr_left' (hP a b).symm

/-- **A matrix's pairs** (`pairs_spec`): where `x` holds `r` at the codes and `r` reaches only coded elements. -/
theorem pairsOK_bits {r : A.El → B.El → Prop} {x : Bits} (hx : x.Enc ua ub r) (hfit : x.na * x.w ≤ 2 ^ 27)
    (hsup : ∀ a < x.na, ∀ y, r (ua a) y → ∃ j < x.w, ub j = y) :
    PairsOK ua ub x.na x.w r x.pairs.1 x.pairs.2 := by
  obtain ⟨hl, hle, hs, h1, h2, hat⟩ := pairs_spec x hfit
  refine ⟨hl, hs, h2, Nat.lt_min.2 ⟨by omega, Nat.lt_of_le_of_lt hle
    (Nat.lt_of_le_of_lt hfit (Nat.lt_of_lt_of_le (by decide) USize.le_size))⟩, fun a ha y => ⟨fun hr => ?_, ?_⟩⟩
  · obtain ⟨j, hj, rfl⟩ := hsup a ha y hr
    obtain ⟨q, hq1, hq2, e1, e2⟩ := (hat a ha j hj).1 ((hx a ha j hj).2 hr)
    exact ⟨q, hq1, hq2, e1, by rw [e2]⟩
  · rintro ⟨q, hq1, hq2, rfl, rfl⟩
    have hj := h2 _ (List.getElem_mem hq2)
    exact (hx _ ha _ hj).1 ((hat _ ha _ hj).2 ⟨q, hq1, hq2, rfl, rfl⟩)

/-- A node that is no table reads its pairs off its matrix, of the converse under `flip`. -/
theorem pairs_node (ids : Array ByteArray) (sz : Obj → Nat) (flip : Bool) {A B : Obj} (p : TP A B)
    (hp : ∀ R, p ≠ .leaf R) (n : Nat) :
    (p.pairs ids sz flip).run n = (let x := ((p.bits ids sz).run n).1
      (if flip then x.conv.pairs else x.pairs, ((p.bits ids sz).run n).2)) := by
  cases p with
  | leaf R => exact absurd rfl (hp R)
  | _ => rw [TP.pairs] <;> first | rfl | (intro _ h; cases h)

/-- **A non-table node's pairs** in `rep_compB`'s form, and under `flip` in `rep_ldivB`'s. -/
theorem pairsOK_node (ids : Array ByteArray) (sz : Obj → Nat) {p : TP A B} (hp : ∀ R, p ≠ .leaf R) (n : Nat)
    (hx : ((p.bits ids sz).run n).1.Enc ua ub p.den)
    (hfit : ((p.bits ids sz).run n).1.na * ((p.bits ids sz).run n).1.w ≤ 2 ^ 27) :
    ((∀ a < ((p.bits ids sz).run n).1.na, ∀ y, p.den (ua a) y → ∃ j < ((p.bits ids sz).run n).1.w, ub j = y) →
      PairsOK ua ub ((p.bits ids sz).run n).1.na ((p.bits ids sz).run n).1.w p.den
        ((p.pairs ids sz false).run n).1.1 ((p.pairs ids sz false).run n).1.2) ∧
    ((∀ b < ((p.bits ids sz).run n).1.w, ∀ y, p.den y (ub b) → ∃ i < ((p.bits ids sz).run n).1.na, ua i = y) →
      PairsOK ub ua ((p.bits ids sz).run n).1.w ((p.bits ids sz).run n).1.na (fun b a => p.den a b)
        ((p.pairs ids sz true).run n).1.1 ((p.pairs ids sz true).run n).1.2) := by
  rw [pairs_node ids sz false p hp, pairs_node ids sz true p hp]
  generalize ((p.bits ids sz).run n).1 = x at hx hfit ⊢
  exact ⟨pairsOK_bits hx hfit, pairsOK_bits (rep_convB hx hfit) (by rw [Nat.mul_comm]; exact hfit)⟩

/-- A table's pairs read the two code columns at the state, sorted, and move it by two. -/
theorem pairs_leaf (ids : Array ByteArray) (sz : Obj → Nat) (flip : Bool) (R : Rel A B) (n : Nat) :
    ((TP.leaf R).pairs ids sz flip).run n = (if flip then sortBy (ids.getD (n + 1) .empty) (ids.getD n .empty)
      else sortBy (ids.getD n .empty) (ids.getD (n + 1) .empty), n + 2) := by
  rw [TP.pairs]; rfl

/-- **A table at position `n` of the coded columns, as code pairs**: in `rep_compB`'s form, and under `flip` in
    `rep_ldivB`'s, under `uOf`, the codes below the objects' picked counts, at most `2²⁷` of them. -/
theorem pairsOK_leaf (cs : Array Col) {out : Array ByteArray} {sps : Array Col} (h : codeAll cs = some (out, sps))
    (sz : Obj → Nat) (R : Rel A B) {n : Nat} (hj : n + 1 < cs.size) (ek : cs[n] = ⟨A, ⟨R.n, R.key⟩⟩)
    (ev : cs[n + 1] = ⟨B, ⟨R.n, R.val⟩⟩) (hm : R.n.toNat < 2 ^ 63) (ha27 : (spOf sps A).1.toNat ≤ 2 ^ 27)
    (hb27 : (spOf sps B).1.toNat ≤ 2 ^ 27) :
    PairsOK (uOf cs A) (uOf cs B) (spOf sps A).1.toNat (spOf sps B).1.toNat (TP.leaf R).den
      (((TP.leaf R).pairs out sz false).run n).1.1 (((TP.leaf R).pairs out sz false).run n).1.2 ∧
    PairsOK (uOf cs B) (uOf cs A) (spOf sps B).1.toNat (spOf sps A).1.toNat (fun b a => (TP.leaf R).den a b)
      (((TP.leaf R).pairs out sz true).run n).1.1 (((TP.leaf R).pairs out sz true).run n).1.2 := by
  obtain ⟨-, hany, hcol⟩ := codeAll_inv cs h
  have hin : ∀ i (hi : i < cs.size), (sps.any (·.1 == cs[i].1)) = true := fun i hi => by
    have := hany _ (List.getElem_mem (l := cs.toList) (by simpa using hi)); simpa using this
  obtain ⟨qa, hfa, hka, hca⟩ := hcol n (by omega) A _ ek (by have := hin n (by omega); rwa [ek] at this)
  obtain ⟨qb, hfb, hkb, hcb⟩ := hcol (n + 1) hj B _ ev (by have := hin (n + 1) hj; rwa [ev] at this)
  rw [spOf_eq hfa] at ha27 ⊢; rw [spOf_eq hfb] at hb27 ⊢
  simp only [pairs_leaf]
  generalize out.getD n .empty = k at hka hca
  generalize out.getD (n + 1) .empty = v at hkb hcb
  -- each row's codes decode to its elements, and decode injectively below the picked counts
  have dk : ∀ q h1 (h2 : q < (ids k).length), R.key.row ⟨q, h1⟩ = uOf cs A (ids k)[q] := fun q h1 h2 =>
    ((hca q h1 h2).2 _ (hca q h1 h2).1).1 rfl
  have dv : ∀ q h1 (h2 : q < (ids v).length), R.val.row ⟨q, h1⟩ = uOf cs B (ids v)[q] := fun q h1 h2 =>
    ((hcb q h1 h2).2 _ (hcb q h1 h2).1).1 rfl
  have hk : ∀ t ∈ ids k, t < qa.1.toNat := fun t ht => by
    obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem ht; exact (hca r (hka ▸ hr) hr).1
  have hv : ∀ t ∈ ids v, t < qb.1.toNat := fun t ht => by
    obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem ht; exact (hcb r (hkb ▸ hr) hr).1
  have hl : len v = len k := by rw [len_eq_ids, len_eq_ids, hka, hkb]
  have hmk : len k < min (2 ^ 63) USize.size := by
    rw [len_eq_ids, hka]; exact Nat.lt_min.2 ⟨hm, USize.toNat_lt_size R.n⟩
  refine ⟨pairsOK_sort hl hmk (fun t ht => by have := hk t ht; omega) hv fun a ha y => ?_,
    pairsOK_sort hl.symm (hl ▸ hmk) (fun t ht => by have := hv t ht; omega) hk fun b hb x => ?_⟩
  · show rep R _ _ ↔ _
    rw [rep_apply]
    constructor
    · rintro ⟨i, e1, e2⟩
      have h1 : i.1 < (ids k).length := by rw [hka]; exact i.2
      have h2 : i.1 < (ids v).length := by rw [hkb]; exact i.2
      exact ⟨i.1, h1, h2, ((hca i.1 i.2 h1).2 a ha).2 e1, by rw [← dv _ i.2 h2]; exact e2⟩
    · rintro ⟨q, h1, h2, e1, e2⟩
      exact ⟨⟨q, hka ▸ h1⟩, ((hca q _ h1).2 a ha).1 e1, by rw [dv _ _ h2]; exact e2⟩
  · show rep R _ _ ↔ _
    rw [rep_apply]
    constructor
    · rintro ⟨i, e1, e2⟩
      have h1 : i.1 < (ids k).length := by rw [hka]; exact i.2
      have h2 : i.1 < (ids v).length := by rw [hkb]; exact i.2
      exact ⟨i.1, h2, h1, ((hcb i.1 i.2 h2).2 b hb).2 e2, by rw [← dk _ i.2 h1]; exact e1⟩
    · rintro ⟨q, h2, h1, e2, e1⟩
      exact ⟨⟨q, hkb ▸ h2⟩, by rw [dk _ _ h1]; exact e1, ((hcb q _ h2).2 b hb).1 e2⟩

#print axioms run?_some
#print axioms caps_col
#print axioms caps_sz
#print axioms caps_pick
#print axioms sortBy_spec
#print axioms pairsOK_sort
#print axioms pairsOK_bits
#print axioms pairsOK_node
#print axioms pairsOK_leaf

end LeetQ.Rel.Lang.Bits
