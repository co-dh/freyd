/-
  q's joins over qlean columns, each a `RelRep` whose spec is a relational expression.
  * `ij` (inner join): `ij(L, S) ≜ L S` — the left pairs `L : a ↦ k` then the right column `S : k ↦ v`.
    Each left key probes the right side's sorted keys by two `bin`s (`QSortedRel.lookup`) and gathers.
  * `aj` (asof join): `aj(R) ≜ Λ((outl R) ∩ (outr ≥ outl°)) est(outl ≥ outl°)` — a left row `(k, t)` to
    the right rows `(t', v)` of key `k` with `t ≥ t'`, then the ones of greatest time. The key is found by
    `bin` on the strictly ascending key column, the time by `bin` (right = false) on the group's time column.
-/
import LeetQ.QRel
import AOP.A7_2_RelSet

namespace LeetQ.Join

open QLean QLean.Column QLean.Kernel QLean.Verify
open Freyd Freyd.Alg Freyd.Alg.RelSet LeetQ
open PowerAllegory

/-- `≥` on the numbers the `Int64`s denote: `a ↦ b` when `a ≥ b`. -/
def ge : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩ := fun a b => b.toInt ≤ a.toInt

/-! ## `ij`: composition -/

/-- The pairs of `ij`: each left pair `(a, k)` with every value the right column holds at `k`. -/
def ijL (l : List (Int64 × Int64)) (s : QSortedRel Int64) : List (Int64 × Int64) :=
  l.flatMap fun p => (s.lookup p.2).map (p.1, ·)

/-- q's `ij` of the left pairs `l : a ↦ k` and the right column `s : k ↦ v`. -/
def ij (l : List (Int64 × Int64)) (s : QSortedRel Int64) : RelRep Int64 Int64 := .pairs (FinRel.ofList (ijL l s))

/-- **`ij(l, s) = rel(l) rep(s)`**. -/
theorem rel_ij (l : List (Int64 × Int64)) (s : QSortedRel Int64) : (ij l s).rel = rel l ≫ s.rep := by
  show (FinRel.ofList _).rep = _
  rw [FinRel.rep_ofList]
  refine hom_ext fun a v => ?_
  show (a, v) ∈ ijL l s ↔ _
  rw [comp_apply]
  simp only [ijL, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a', k⟩, hp, v', hv, rfl, rfl⟩
    exact ⟨k, hp, QSortedRel.mem_rep.2 (QSortedRel.mem_lookup.1 hv)⟩
  · rintro ⟨k, hp, hr⟩
    exact ⟨(a, k), hp, v, QSortedRel.mem_lookup.2 (QSortedRel.mem_rep.1 hr), rfl, rfl⟩

/-! ## `aj`: composition, then `est(≥)` on the time -/

/-- The right table of `aj`: a strictly ascending key column, and per key a `QSortedRel` from time to
value, its times ascending. -/
structure AjRight where
  keys : Keys
  grp : Array (QSortedRel Int64)
  len : grp.size = keys.count
  strict : ∀ i j, i < j → j < keys.count → keys.get i < keys.get j
  fits : keys.fits

namespace AjRight

/-- The right rows: key `k` to `(time, value)` when `k`'s group holds that pair. -/
def rep (R : AjRight) : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64 × Int64⟩ :=
  fun k p => ∃ i, ∃ h : i < R.grp.size, R.keys.get i = k ∧ R.grp[i].rep p.1 p.2

theorem sorted (R : AjRight) : ∀ i j, i ≤ j → j < R.keys.count → R.keys.get i ≤ R.keys.get j := fun i j hij hj => by
  rcases Nat.lt_or_eq_of_le hij with h | rfl
  · exact Int64.le_iff_toInt_le.2 (Int.le_of_lt (Int64.lt_iff_toInt_lt.1 (R.strict i j h hj)))
  · exact Int64.le_iff_toInt_le.2 (Int.le_refl _)

theorem uniq (R : AjRight) {i j : Nat} (hi : i < R.keys.count) (hj : j < R.keys.count)
    (h : R.keys.get i = R.keys.get j) : i = j := by
  rcases Nat.lt_trichotomy i j with hl | rfl | hl
  · have := Int64.lt_iff_toInt_lt.1 (R.strict i j hl hj); rw [h] at this; omega
  · rfl
  · have := Int64.lt_iff_toInt_lt.1 (R.strict j i hl hi); rw [h] at this; omega

/-- The group of key `k`: `bin` (right = true) answers the least index whose key is `≥ k`. An answer is
an `Int64`, so at or above `2^63` keys the column is scanned, which no `ByteArray` in memory reaches. -/
def grpOf (R : AjRight) (k : Int64) : Option (QSortedRel Int64) :=
  if R.keys.count < 2 ^ 63 then
    let r := (bitsAt (R.keys.bin true k) 0 8).toInt64.toInt.toNat
    if R.keys.get r = k then R.grp[r]? else none
  else ((List.range R.keys.count).find? fun i => decide (R.keys.get i = k)).bind (R.grp[·]?)

theorem grpOf_eq_some (R : AjRight) (k : Int64) (q : QSortedRel Int64) :
    R.grpOf k = some q ↔ ∃ i, ∃ h : i < R.grp.size, R.keys.get i = k ∧ R.grp[i] = q := by
  unfold grpOf
  split
  · rename_i hn
    obtain ⟨r, hr, hout, hlo, hhi⟩ := R.keys.bin_spec true k R.fits hn R.sorted
    simp only [↓reduceIte] at hout hlo hhi
    simp only [hout, Int.toNat_natCast]
    constructor
    · intro h
      split at h
      · obtain ⟨hs, he⟩ := Array.getElem?_eq_some_iff.1 h
        exact ⟨r, hs, by assumption, he⟩
      · cases h
    · rintro ⟨i, hi, hk, rfl⟩
      have hic : i < R.keys.count := R.len ▸ hi
      have hri : r ≤ i := Nat.not_lt.1 fun h => by
        have := Int64.lt_iff_toInt_lt.1 (hlo i h); rw [hk] at this; omega
      have hrc : r < R.keys.count := by omega
      have e : R.keys.get r = k := Int64.toInt_inj.1 (by
        have := Int64.le_iff_toInt_le.1 (hhi hrc)
        have := Int64.le_iff_toInt_le.1 (R.sorted r i hri hic); rw [hk] at this; omega)
      obtain rfl := R.uniq hrc hic (e.trans hk.symm)
      rw [if_pos e]
      exact Array.getElem?_eq_getElem hi
  · constructor
    · intro h
      cases hf : (List.range R.keys.count).find? (fun i => decide (R.keys.get i = k)) with
      | none => rw [hf] at h; cases h
      | some j =>
        rw [hf, Option.bind_some] at h
        obtain ⟨hs, he⟩ := Array.getElem?_eq_some_iff.1 h
        have hp := List.find?_some hf
        exact ⟨j, hs, of_decide_eq_true (p := R.keys.get j = k) hp, he⟩
    · rintro ⟨i, hi, hk, rfl⟩
      have hic : i < R.keys.count := R.len ▸ hi
      cases hf : (List.range R.keys.count).find? (fun i => decide (R.keys.get i = k)) with
      | none =>
        exact absurd (decide_eq_true hk) (List.find?_eq_none.1 hf i (List.mem_range.2 hic))
      | some j =>
        have hj := List.mem_range.1 (List.mem_of_find?_eq_some hf)
        have hp := List.find?_some hf
        obtain rfl := R.uniq hj hic ((of_decide_eq_true (p := R.keys.get j = k) hp).trans hk.symm)
        rw [Option.bind_some]
        exact Array.getElem?_eq_getElem hi

end AjRight

/-- In one group, the pairs whose time is the greatest `≤ t`: `bin` (right = false) answers one less
than the partition point of `time ≤ t`, the index of that time, whose run `lookup` gathers. -/
def lastLE (q : QSortedRel Int64) (t : Int64) : List (Int64 × Int64) :=
  if q.count < 2 ^ 63 then
    let p := q.probe false t
    if 0 ≤ p then (q.lookup (q.keys.get p.toNat)).map (q.keys.get p.toNat, ·) else []
  else RelRep.estList (fun a b => decide (b.1.toInt ≤ a.1.toInt)) (q.toList.filter fun x => decide (x.1.toInt ≤ t.toInt))

theorem mem_lastLE {q : QSortedRel Int64} {t : Int64} {x : Int64 × Int64} :
    x ∈ lastLE q t ↔ (q.rep x.1 x.2 ∧ x.1.toInt ≤ t.toInt) ∧
      ∀ y : Int64 × Int64, q.rep y.1 y.2 ∧ y.1.toInt ≤ t.toInt → y.1.toInt ≤ x.1.toInt := by
  unfold lastLE
  split
  · rename_i hn
    obtain ⟨r, hr, e, lo, hhi⟩ := q.probe_spec false t hn
    simp only [Bool.false_eq_true, ↓reduceIte] at e lo hhi
    have mono : ∀ i j, i ≤ j → j < q.count → (q.keys.get i).toInt ≤ (q.keys.get j).toInt :=
      fun i j hij hj => Int64.le_iff_toInt_le.1 (q.sorted i j hij hj)
    -- an index whose time is `≤ t` lies below the partition point
    have below : ∀ i, i < q.count → (q.keys.get i).toInt ≤ t.toInt → i < r := fun i hi ht =>
      Nat.lt_of_not_le fun h => by have := hhi (by omega); have := mono r i h hi; omega
    simp only [e]
    split
    · rename_i hp
      have hm : ((r : Int) - 1).toNat = r - 1 := by omega
      rw [hm]
      simp only [List.mem_map, QSortedRel.mem_lookup, QSortedRel.mem_rep]
      constructor
      · rintro ⟨v, ⟨i, hi, hk, rfl⟩, rfl⟩
        refine ⟨⟨⟨i, hi, hk, rfl⟩, lo (r - 1) (by omega)⟩, fun y hy => ?_⟩
        obtain ⟨⟨j, hj, hjk, -⟩, hyt⟩ := hy
        rw [← hjk] at hyt ⊢
        have := below j hj hyt
        exact mono j (r - 1) (by omega) (by omega)
      · rintro ⟨⟨⟨i, hi, hk, hv⟩, ht⟩, hmax⟩
        have hir := below i hi (hk ▸ ht)
        have h1 := hmax (q.keys.get (r - 1), q.val (r - 1)) ⟨⟨r - 1, by omega, rfl, rfl⟩, lo (r - 1) (by omega)⟩
        have h2 := mono i (r - 1) (by omega) (by omega)
        simp only at h1
        rw [hk] at h2
        have e1 : (q.keys.get (r - 1)).toInt = x.1.toInt := by omega
        refine ⟨x.2, ⟨i, hi, Int64.toInt_inj.1 (by rw [hk]; exact e1.symm), hv⟩, ?_⟩
        exact Prod.ext (Int64.toInt_inj.1 e1) rfl
    · rename_i hp
      simp only [List.not_mem_nil, false_iff, not_and, QSortedRel.mem_rep]
      rintro ⟨⟨i, hi, hk, -⟩, ht⟩
      have := below i hi (hk ▸ ht); omega
  · simp only [RelRep.estList, List.mem_filter, List.all_eq_true, decide_eq_true_eq]
    show ((x ∈ q.toList ∧ _) ∧ _) ↔ ((x.1, x.2) ∈ q.toList ∧ _) ∧ ∀ y : Int64 × Int64, (y.1, y.2) ∈ q.toList ∧ _ → _
    exact ⟨fun ⟨h, hm⟩ => ⟨h, fun y hy => hm y hy⟩, fun ⟨h, hm⟩ => ⟨h, fun y hy => hm y hy⟩⟩

/-- The pairs of `aj` at a left row `(k, t)`: the group of `k`, then its greatest time `≤ t`. -/
def ajL (R : AjRight) (x : Int64 × Int64) : List (Int64 × Int64) :=
  match R.grpOf x.1 with
  | some q => lastLE q x.2
  | none => []

/-- q's `aj` against the right table `R`, at every left row `(k, t)`. -/
def aj (R : AjRight) : RelRep (Int64 × Int64) (Int64 × Int64) := .enum (ajL R)

/-- `outl ≥ outl°`: `≥` on the time. -/
def geT : (⟨Int64 × Int64⟩ : RelSet.{0}) ⟶ ⟨Int64 × Int64⟩ := graph Prod.fst ≫ ge ≫ (graph Prod.fst)°

/-- The candidates `(outl R) ∩ (outr ≥ outl°)`: `(k, t)` to each right `(t', v)` of key `k` with `t ≥ t'`. -/
def cand (R : AjRight) : (⟨Int64 × Int64⟩ : RelSet.{0}) ⟶ ⟨Int64 × Int64⟩ :=
  (graph Prod.fst ≫ R.rep) ∩ (graph Prod.snd ≫ ge ≫ (graph Prod.fst)°)

theorem geT_apply (w z : Int64 × Int64) : geT w z ↔ z.1.toInt ≤ w.1.toInt := by
  simp only [geT, comp_apply, graph_apply, recip_apply, ge]
  exact ⟨fun ⟨_, rfl, _, h, rfl⟩ => h, fun h => ⟨_, rfl, _, h, rfl⟩⟩

theorem cand_apply (R : AjRight) (x z : Int64 × Int64) :
    cand R x z ↔ R.rep x.1 z ∧ z.1.toInt ≤ x.2.toInt := by
  simp only [cand, inter_apply, comp_apply, graph_apply, recip_apply, ge]
  exact ⟨fun ⟨⟨_, rfl, h⟩, _, rfl, _, h', rfl⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ => ⟨⟨_, rfl, h⟩, _, rfl, _, h', rfl⟩⟩

/-- **`aj(R) = Λ((outl R) ∩ (outr ≥ outl°)) est(outl ≥ outl°)`**. -/
theorem rel_aj (R : AjRight) : (aj R).rel = Λ (cand R) ≫ est geT := hom_ext fun x w => by
  rw [Λ_comp_est_apply]
  show w ∈ ajL R x ↔ _
  simp only [cand_apply, geT_apply]
  unfold ajL
  cases hg : R.grpOf x.1 with
  | none =>
    simp only [List.not_mem_nil, false_iff]
    rintro ⟨⟨⟨i, hi, hk, -⟩, -⟩, -⟩
    exact nomatch hg.symm.trans ((R.grpOf_eq_some _ _).2 ⟨i, hi, hk, rfl⟩)
  | some q =>
    obtain ⟨i, hi, hk, rfl⟩ := (R.grpOf_eq_some _ _).1 hg
    have hic : i < R.keys.count := R.len ▸ hi
    have one : ∀ p : Int64 × Int64, R.rep x.1 p ↔ R.grp[i].rep p.1 p.2 := fun p =>
      ⟨fun ⟨j, hj, hjk, h⟩ => by obtain rfl := R.uniq (R.len ▸ hj) hic (hjk.trans hk.symm); exact h,
        fun h => ⟨i, hi, hk, h⟩⟩
    simp only [one]
    exact mem_lastLE

/-! ## Runs -/

/-- A right table from `(key, group pairs)`, the keys checked strictly ascending and encoded when `foR`; the
time columns stay dense. -/
def AjRight.ofList? (gs : List (Int64 × List (Int64 × Int64))) (foR : Bool := false) : Option AjRight :=
  if h : (gs.map Prod.fst).Pairwise (· < ·) then some {
    keys := Keys.ofList foR (gs.map Prod.fst)
    grp := (gs.map fun g => QSortedRel.ofList g.2 dense).toArray
    len := by simp [Keys.count_ofList]
    strict := fun i j hij hj => by
      rw [Keys.count_ofList] at hj
      rw [Keys.get_ofList _ _ _ (by omega), Keys.get_ofList _ _ _ hj]
      exact List.pairwise_iff_getElem.1 h i j (by omega) hj hij
    fits := Keys.fits_ofList _ _ }
  else none

#print axioms rel_ij
#print axioms rel_aj

/-! The kernel's runs, as in `L1`: `List.mergeSort` is well-founded recursion, so `simp` evaluates the
sorts and the kernel the rest. -/

theorem sortS : ([(1, 100), (3, 300), (1, 101)] : List (Int64 × Int64)).mergeSort QSortedRel.keyLE =
    [(1, 100), (1, 101), (3, 300)] := by
  simp [List.mergeSort, QSortedRel.keyLE]
theorem sortG : ([(2, 20), (5, 50)] : List (Int64 × Int64)).mergeSort QSortedRel.keyLE = [(2, 20), (5, 50)] := by
  simp [List.mergeSort, QSortedRel.keyLE]
theorem sortH : ([(4, 40)] : List (Int64 × Int64)).mergeSort QSortedRel.keyLE = [(4, 40)] := by
  simp

/-- The right table's keys are strictly ascending, so `AjRight.ofList?` answers `some`. -/
theorem keysOK : ([1, 3] : List Int64).Pairwise (· < ·) := by decide

example : ijL [(10, 1), (20, 2), (30, 1)] (QSortedRel.ofList [(1, 100), (3, 300), (1, 101)] dense) =
    [(10, 100), (10, 101), (30, 100), (30, 101)] := by
  simp only [ijL, QSortedRel.lookup, QSortedRel.probe, QLean.Kernel.binBytes,
    QSortedRel.ofList, QSortedRel.count, Keys.ofList, Keys.bin, Keys.get, Keys.count,
    Bool.false_eq_true, false_and, ↓reduceIte, sortS]
  decide +kernel
example : ijL [(10, 1), (20, 2), (30, 1)] (QSortedRel.ofList [(1, 100), (3, 300), (1, 101)] dense true) =
    [(10, 100), (10, 101), (30, 100), (30, 101)] := by
  simp only [ijL, QSortedRel.lookup, QSortedRel.probe, QLean.Kernel.foRBin, QLean.Kernel.Coc.encode,
    QLean.Kernel.Coc.decode, QLean.Kernel.Coc.elems, QLean.Kernel.binBytes, QSortedRel.ofList,
    QSortedRel.count, Keys.ofList, Keys.bin, Keys.count, sortS, List.length_map, List.length_cons,
    List.length_nil, USize.reduceToNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceLT, toNat_toUSize, lt_usize,
    and_self, ↓reduceIte]
  decide +kernel

example : (AjRight.ofList? [(1, [(2, 20), (5, 50)]), (3, [(4, 40)])]).map
    (fun R => [(1, 6), (1, 4), (1, 1), (3, 9), (2, 9)].map (ajL R)) = some [[(5, 50)], [(2, 20)], [], [(4, 40)], []] := by
  simp only [AjRight.ofList?, keysOK, ↓reduceDIte, Option.map_some, ajL, AjRight.grpOf, lastLE, List.map_cons,
    List.map_nil, QSortedRel.lookup,
    QSortedRel.probe, QLean.Kernel.binBytes, QSortedRel.ofList, QSortedRel.count, Keys.ofList,
    Keys.bin, Keys.get, Keys.count, Bool.false_eq_true, false_and, ↓reduceIte, sortG, sortH]
  decide +kernel
-- The encoded run exceeds the default recursion depth.
set_option maxRecDepth 10000 in
example : (AjRight.ofList? [(1, [(2, 20), (5, 50)]), (3, [(4, 40)])] true).map
    (fun R => [(1, 6), (1, 4), (1, 1), (3, 9), (2, 9)].map (ajL R)) = some [[(5, 50)], [(2, 20)], [], [(4, 40)], []] := by
  simp only [AjRight.ofList?, keysOK, ↓reduceDIte, Option.map_some, ajL, AjRight.grpOf, lastLE, List.map_cons,
    List.map_nil, QSortedRel.lookup,
    QSortedRel.probe, QLean.Kernel.foRBin, QLean.Kernel.Coc.encode, QLean.Kernel.Coc.decode, QLean.Kernel.Coc.elems,
    QLean.Kernel.binBytes, QSortedRel.ofList, QSortedRel.count, Keys.ofList, Keys.bin, Keys.count, sortG, sortH,
    List.length_map, List.length_cons, List.length_nil, USize.reduceToNat, Nat.reduceAdd, Nat.reducePow,
    Nat.reduceLT, toNat_toUSize, lt_usize, and_self, ↓reduceIte]
  decide +kernel

-- The compiled runs: `binBytes`/`foRBin` are the C `bin` and `coc_bin` here.
#guard ijL [(10, 1), (20, 2), (30, 1)] (QSortedRel.ofList [(1, 100), (3, 300), (1, 101)] dense) ==
  [(10, 100), (10, 101), (30, 100), (30, 101)]
#guard ijL [(10, 1), (20, 2), (30, 1)] (QSortedRel.ofList [(1, 100), (3, 300), (1, 101)] dense true) ==
  [(10, 100), (10, 101), (30, 100), (30, 101)]
#guard (AjRight.ofList? [(1, [(2, 20), (5, 50)]), (3, [(4, 40)])]).map (fun R => 
    [(1, 6), (1, 4), (1, 1), (3, 9), (2, 9)].map (ajL R)) ==
  some [[(5, 50)], [(2, 20)], [], [(4, 40)], []]
#guard (AjRight.ofList? [(1, [(2, 20), (5, 50)]), (3, [(4, 40)])] true).map (fun R => 
    [(1, 6), (1, 4), (1, 1), (3, 9), (2, 9)].map (ajL R)) ==
  some [[(5, 50)], [(2, 20)], [], [(4, 40)], []]

end LeetQ.Join
