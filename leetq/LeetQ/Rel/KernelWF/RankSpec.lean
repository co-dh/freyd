/-
  `Ops.rank` read back at `long`: q's `rank` (`<<x`) is the ordinal rank of a stable ascending sort, so row
  `p` ranks below row `q` exactly when `p`'s value is below `q`'s, or the two are equal and `p` comes first.
-/
import LeetQ.Rel.KernelWF.BagSpec

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.KernelWF

/-- **Position in a list sorted by a strict order is that order**: `g` pairwise `R`, `R` asymmetric, so for
    `p q ∈ g` the first `p` stands before the first `q` exactly at `R p q`. -/
theorem idxOf_lt_iff {g : List Nat} {R : Nat → Nat → Prop} (hs : g.Pairwise R) (hasym : ∀ i j, R i j → ¬ R j i)
    {p q : Nat} (hp : p ∈ g) (hq : q ∈ g) :
    g.idxOf p < g.idxOf q ↔ R p q := by
  have ha := List.idxOf_lt_length_of_mem hp
  have hb := List.idxOf_lt_length_of_mem hq
  have ga : g[g.idxOf p] = p := beq_iff_eq.1 (@List.findIdx_getElem _ (· == p) g ha)
  have gb : g[g.idxOf q] = q := beq_iff_eq.1 (@List.findIdx_getElem _ (· == q) g hb)
  constructor
  · intro h
    have := List.pairwise_iff_getElem.1 hs _ _ ha hb h
    rwa [ga, gb] at this
  · intro h
    rcases Nat.lt_trichotomy (g.idxOf p) (g.idxOf q) with hl | he | hl
    · exact hl
    · have e : g[g.idxOf p] = g[g.idxOf q] := by simp only [he]
      rw [ga, gb] at e
      subst e; exact absurd h (hasym _ _ h)
    · have := List.pairwise_iff_getElem.1 hs _ _ hb ha hl
      rw [ga, gb] at this
      exact absurd this (hasym _ _ h)

/-- `invert p` read back: element `i` is where `i` first stands among `p`'s longs. -/
theorem ids_invert (p : ByteArray) (hm : len p < 2 ^ 64) :
    ids (Order.invert p) = (List.range (len p)).map fun i => (ids p).idxOf i := by
  have hp : ids p = (List.range (p.size / 8)).map fun j => (Column.bitsAt p (8 * j) 8).toNat :=
    List.map_congr_left fun j _ => by rw [Nat.mul_comm]
  have e : ∀ i, (List.range (p.size / 8)).findIdx (fun j => (Column.bitsAt p (8 * j) 8).toNat == i) =
      (ids p).idxOf i := fun i => by
    rw [hp]; unfold List.idxOf; rw [List.findIdx_map]; rfl
  have hi : Order.invert p = Order.indices ((List.range (len p)).map fun i => (ids p).idxOf i) := by
    show Order.indices ((List.range (p.size / 8)).map fun i =>
      (List.range (p.size / 8)).findIdx fun j => (Column.bitsAt p (8 * j) 8).toNat == i) = _
    exact congrArg Order.indices (List.map_congr_left fun i _ => e i)
  rw [hi]
  refine ids_indices _ fun i hi => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
  exact Nat.lt_of_le_of_lt (Nat.le_trans List.idxOf_le_length (Nat.le_of_eq (len_eq_ids p).symm)) hm

/-- `Ops.rank` at `long` is the kernel's `ranks` over the column's dense payload, on either encoding. -/
theorem longsOf_rank {n : USize} (x : Arr .long n) (h : QAtomicType.long ≠ .general) :
    longsOf (Ops.rank x h) = Order.ranks .i64 n (longsOf x) := by
  obtain ⟨_, he⟩ := Option.eq_some_iff_get_eq.1 (gradeColumn_long x true)
  have hb : longBytes n (Ops.rank x h).enc = some (Order.ranks .i64 n (longsOf x)) := by
    show longBytes n ((gradeColumn .long false n x.enc (rank := true)).get _) = _
    rw [he]; rfl
  exact Option.some_inj.1 ((Option.some_get _).trans hb)

/-- **q's `rank` at `long`, read back**: for rows `p q` below the count, each rank is below the count, and row
    `p` ranks below row `q` exactly when its value is below `q`'s, or the values are equal and `p` comes first —
    the ordinal rank of a stable ascending sort, q's null `0N` (the least `Int64`) below every other value. -/
theorem rank_long {n : USize} (x : Arr .long n) (h : QAtomicType.long ≠ .general) {p q : Nat}
    (hp : p < n.toNat) (hq : q < n.toNat) :
    (Column.bitsAt (longsOf (Ops.rank x h)) (p * 8) 8).toNat < n.toNat ∧
      ((Column.bitsAt (longsOf (Ops.rank x h)) (p * 8) 8).toNat <
          (Column.bitsAt (longsOf (Ops.rank x h)) (q * 8) 8).toNat ↔
        x.get ⟨p, hp⟩ < x.get ⟨q, hq⟩ ∨ (x.get ⟨p, hp⟩ = x.get ⟨q, hq⟩ ∧ p < q)) := by
  rw [longsOf_rank]
  obtain ⟨hperm, hsort⟩ := grade_long x
  generalize hG : Order.grade .i64 false n (longsOf x) = G at hperm hsort
  have hGl : len G = n.toNat := by rw [len_eq_ids, hperm.length_eq, List.length_range]
  have hR : Order.ranks .i64 n (longsOf x) = Order.invert G := by rw [← hG]; rfl
  have hI := ids_invert G (by rw [hGl]; exact usize_lt n)
  rw [hR]
  have hget : ∀ i (hi : i < n.toNat), (Column.bitsAt (Order.invert G) (i * 8) 8).toNat = (ids G).idxOf i :=
    fun i hi => by
      have hl : i < (ids (Order.invert G)).length := by rw [hI, List.length_map, List.length_range, hGl]; exact hi
      rw [← ids_getElem hl]; simp only [hI, List.getElem_map, List.getElem_range]
  have hmem : ∀ i, i < n.toNat → i ∈ ids G := fun i hi => hperm.mem_iff.2 (List.mem_range.2 hi)
  rw [hget p hp, hget q hq]
  -- the strict order the stable sort lists the rows in, `grade_long`'s at rows below the count
  let R : Nat → Nat → Prop := fun i j => ∃ (hi : i < n.toNat) (hj : j < n.toNat),
    x.get ⟨i, hi⟩ < x.get ⟨j, hj⟩ ∨ (x.get ⟨i, hi⟩ = x.get ⟨j, hj⟩ ∧ i < j)
  have hs : (ids G).Pairwise R := hsort.imp_of_mem fun {i j} hi hj h =>
    ⟨List.mem_range.1 (hperm.mem_iff.1 hi), List.mem_range.1 (hperm.mem_iff.1 hj), h _ _⟩
  have hasym : ∀ i j, R i j → ¬ R j i := fun i j ⟨_, _, h1⟩ ⟨_, _, h2⟩ => by
    simp only [Int64.lt_iff_toInt_lt, ← Int64.toInt_inj] at h1 h2
    omega
  have hlen : (ids G).length = n.toNat := by rw [hperm.length_eq, List.length_range]
  refine ⟨by rw [← hlen]; exact List.idxOf_lt_length_of_mem (hmem p hp), ?_⟩
  rw [idxOf_lt_iff hs hasym (hmem p hp) (hmem q hq)]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hp, hq, h⟩⟩

#print axioms idxOf_lt_iff
#print axioms ids_invert
#print axioms longsOf_rank
#print axioms rank_long

end LeetQ.Rel.Alg
