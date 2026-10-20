/-
  LeetCode 1 — Two Sum over qlean columns: build `ix(xs)°` once as a `QSortedRel` (key `xs[k]`,
  value `k`), then probe it at `t − xs[j]` for every `j`. The spec is freyd's `twoSum`/`twoSumO`
  from `leet/L1.lean`, over the numbers the `Int64`s denote.
-/
import LeetQ.QRel
import leet.L1

namespace LeetQ.L1

open Freyd Freyd.Alg Freyd.Alg.RelSet Freyd.Alg.RelSet.LC1 LeetQ

/-- `ix(xs)°` as two columns: key `xs[k]`, value `k`. -/
def ixQ (xs : List Int64) : QSortedRel :=
  QSortedRel.ofList (xs.zipIdx.map fun p => (p.1, (p.2 : Int).toInt64))

/-- The index pairs `j < k` with `xs[j] + xs[k] = t`: probe the column at `t − xs[j]`, which no
element can equal when it falls outside the `Int64` range. -/
def qpairs (t : Int) (xs : List Int64) : List (Nat × Nat) :=
  let s := ixQ xs
  xs.zipIdx.flatMap fun p =>
    let d := t - p.1.toInt
    if -2 ^ 63 ≤ d ∧ d < 2 ^ 63 then
      (s.lookup d.toInt64).filterMap fun v =>
        if p.2 < v.toInt.toNat then some (p.2, v.toInt.toNat) else none
    else []

/-- The program: the first pair. -/
def qprog (t : Int) (xs : List Int64) : Option (Nat × Nat) := (qpairs t xs).head?

theorem mem_ixQ {xs : List Int64} (h : xs.length < 2 ^ 63) {k v : Int64} :
    v ∈ (ixQ xs).lookup k ↔ ∃ i : Nat, xs[i]? = some k ∧ v.toInt = i := by
  rw [QSortedRel.mem_lookup, ← QSortedRel.mem_rep, ixQ, QSortedRel.rep_ofList]
  show (k, v) ∈ _ ↔ _
  simp only [List.mem_map, Prod.mk.injEq, Prod.exists, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨a, i, hi, rfl, rfl⟩
    have := (List.getElem?_eq_some_iff.1 hi).1
    exact ⟨i, hi, Int64.toInt_ofInt_of_le (by omega) (by omega)⟩
  · rintro ⟨i, hi, hv⟩
    have := (List.getElem?_eq_some_iff.1 hi).1
    exact ⟨k, i, hi, rfl, Int64.toInt_inj.1 (by rw [hv]; exact Int64.toInt_ofInt_of_le (by omega) (by omega))⟩

/-- **The pairs are exactly `twoSum`'s**, for any list an `Int64` can index. -/
theorem mem_qpairs (t : Int) {xs : List Int64} (h : xs.length < 2 ^ 63) (j k : Nat) :
    (j, k) ∈ qpairs t xs ↔ twoSum t (xs.map Int64.toInt) j k := by
  show _ ↔ (∃ z, (xs.map Int64.toInt)[j]? = some z ∧ ∃ y, y = t - z ∧ (xs.map Int64.toInt)[k]? = some y) ∧ j < k
  simp only [qpairs, List.mem_flatMap, Prod.exists, List.mem_zipIdx_iff_getElem?, List.getElem?_map,
    Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, j', hj, hm⟩
    split at hm
    · rename_i hd
      obtain ⟨v, hv, he⟩ := List.mem_filterMap.1 hm
      split at he
      · rename_i hlt
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he)
        obtain ⟨i, hi, hvi⟩ := (mem_ixQ h).1 hv
        rw [hvi, Int.toNat_natCast] at hlt ⊢
        exact ⟨⟨a.toInt, ⟨a, hj, rfl⟩, _, rfl, _, hi, Int64.toInt_ofInt_of_le hd.1 hd.2⟩, hlt⟩
      · cases he
    · cases hm
  · rintro ⟨⟨_, ⟨a, hj, rfl⟩, _, rfl, b, hk, hb⟩, hlt⟩
    have hd : -2 ^ 63 ≤ t - a.toInt ∧ t - a.toInt < 2 ^ 63 := by
      have := b.le_toInt; have := b.toInt_lt; constructor <;> omega
    refine ⟨a, j, hj, ?_⟩
    rw [if_pos hd]
    refine List.mem_filterMap.2 ⟨(k : Int).toInt64, (mem_ixQ h).2 ⟨k, ?_, ?_⟩, ?_⟩
    · rw [hk, ← hb]; exact congrArg some (Int64.toInt_inj.1 (by rw [Int64.toInt_ofInt_of_le hd.1 hd.2]))
    · have := (List.getElem?_eq_some_iff.1 hk).1
      exact Int64.toInt_ofInt_of_le (by omega) (by omega)
    · have := (List.getElem?_eq_some_iff.1 hk).1
      rw [Int64.toInt_ofInt_of_le (by omega) (by omega), Int.toNat_natCast, if_pos hlt]

/-- `orNone(R)` at `a` is `orNone(S)` at `b` when `R` at `a` and `S` at `b` hold of the same points. -/
theorem orNone_congr {A A' B : RelSet.{0}} {R : A ⟶ B} {S : A' ⟶ B} {a : A.carrier} {b : A'.carrier}
    (h : ∀ y, R a y ↔ S b y) {o : Option B.carrier} (ho : orNone R a o) : orNone S b o := by
  have e : (graph (fun _ => a) : (⟨Unit⟩ : RelSet.{0}) ⟶ A) ≫ R = graph (fun _ => b) ≫ S :=
    hom_ext fun _ y => ⟨fun ⟨_, (hy : _ = _), hr⟩ => ⟨b, rfl, (h y).1 (hy ▸ hr)⟩,
      fun ⟨_, (hy : _ = _), hs⟩ => ⟨a, rfl, (h y).2 (hy ▸ hs)⟩⟩
  have : (graph (fun _ => a) ≫ orNone R : (⟨Unit⟩ : RelSet.{0}) ⟶ _) () o := ⟨a, rfl, ho⟩
  rw [graph_orNone, e, ← graph_orNone] at this
  obtain ⟨_, (hy : _ = _), hs⟩ := this
  exact hy ▸ hs

/-- **The program answers what freyd's spec allows**: `qprog(t)(xs)` is a pair of
`twoSum(t)(xs)`, or `none` when it has none — `twoSumO` of `leet/L1.lean` at the numbers `xs` denotes. -/
theorem qprog_spec (t : Int) (xs : List Int64) (h : xs.length < 2 ^ 63) :
    twoSumO t (xs.map Int64.toInt) (qprog t xs) :=
  ⟨_, rfl, orNone_congr (fun (p : Nat × Nat) => mem_qpairs t h p.1 p.2)
    (le_iff.mp head?_le_orNone (qpairs t xs) (qprog t xs) rfl)⟩

/-- `binBytes` reads its width as `USize.toNat`, which the kernel cannot reduce: `System.Platform.numBits`
is opaque. Rewriting the one literal leaves the rest to reduction. -/
theorem usize8 : (8 : USize).toNat = 8 := by simp

-- The kernel's run: `binBytes`' Lean body, by reduction.
example : qprog 9 [2, 7, 11, 15] = some (0, 1) := by
  simp only [qprog, qpairs, QSortedRel.lookup, QSortedRel.probe, QLean.Kernel.binBytes, usize8]; decide +kernel
example : qprog 6 [3, 2, 4] = some (1, 2) := by
  simp only [qprog, qpairs, QSortedRel.lookup, QSortedRel.probe, QLean.Kernel.binBytes, usize8]; decide +kernel
example : qprog 7 [1, 2, 3] = none := by
  simp only [qprog, qpairs, QSortedRel.lookup, QSortedRel.probe, QLean.Kernel.binBytes, usize8]; decide +kernel

-- The compiled run: `binBytes` is the C `bin` here.
#guard qprog 9 [2, 7, 11, 15] == some (0, 1)
#guard qprog 6 [3, 2, 4] == some (1, 2)
#guard qprog 7 [1, 2, 3] == none

end LeetQ.L1
