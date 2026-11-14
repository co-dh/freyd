/-
  `Ops.rank` read back at `long`: q's `rank` (`<<x`) is the ordinal rank of a stable ascending sort, so row
  `p` ranks below row `q` exactly when `p`'s value is below `q`'s, or the two are equal and `p` comes first.
-/
import LeetQ.Rel.KernelWF.PlaceSpec
import LeetQ.Rel.KernelWF.PickRow

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

/-- The `long` key `Order.keyAt .i64` sorts by, read as a number: `2^63` above the value. -/
theorem key_i64 (a : Int64) : ((a.toUInt64 ^^^ 0x8000000000000000).toNat : Int) = a.toInt + 2 ^ 63 := by
  rw [UInt64.toNat_xor, show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl]
  have hlt := a.toUInt64.toNat_lt
  have ht : a.toInt = if 2 * a.toUInt64.toNat < 2 ^ 64 then (a.toUInt64.toNat : Int)
      else (a.toUInt64.toNat : Int) - 2 ^ 64 := by
    rw [Int64.toInt, BitVec.toInt_eq_toNat_cond]; rfl
  rw [ht]
  by_cases h : a.toUInt64.toNat < 2 ^ 63
  · rw [xor_pow63 h, if_pos (by omega)]; omega
  · obtain ⟨y, hy, hx⟩ : ∃ y, y < 2 ^ 63 ∧ a.toUInt64.toNat = y ^^^ 2 ^ 63 :=
      ⟨a.toUInt64.toNat - 2 ^ 63, by omega, by rw [xor_pow63 (by omega)]; omega⟩
    rw [if_neg (by omega), hx, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, xor_pow63 hy]; omega

/-- `Ops.rank` at `long` is the kernel's `ranks` over the column's dense payload, on either encoding. -/
theorem longsOf_rank {n : USize} (x : Arr .long n) (h : QAtomicType.long ≠ .general) :
    longsOf (Ops.rank x h) = Order.ranks .i64 n (longsOf x) := by
  have hg : gradeColumn .long false n x.enc (rank := true) = some (.bytes (Order.ranks .i64 n (longsOf x))) := by
    rcases long_cases x.wf with ⟨b, hb⟩ | ⟨M, P, hb⟩
    · have hs : b.size / 8 = n.toNat := Arr.n_long_bytes x hb
      have hl : longsOf x = b := by unfold longsOf; simp only [hb, longBytes]; rfl
      rw [hl]
      unfold gradeColumn
      simp only [hb, orderKind, Enc.bytesOf]
      rw [if_neg (by decide), if_neg (by simp only [Scan.Kind.width]; omega)]
      simp only [↓reduceIte]
    · have hl : longsOf x = Coc.decode 8 M P n := by unfold longsOf; simp only [hb, longBytes]; rfl
      rw [hl]
      unfold gradeColumn
      simp only [hb, orderKind]
      rw [if_neg (by decide)]; rfl
  obtain ⟨_, he⟩ := Option.eq_some_iff_get_eq.1 hg
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
  generalize hB : longsOf x = B
  have hBs : len B = n.toNat := by
    obtain ⟨ws, hws⟩ : ∃ ws, longWords n x.enc = some ws := by
      rcases KernelWF.long_cases x.wf with ⟨b, h⟩ | ⟨M, P, h⟩ <;> simp [longWords, h]
    obtain ⟨B', hB', -, -, hS⟩ := Arr.dense_long x hws
    have : longsOf x = B' := by
      have e : longBytes n x.enc = some B' := by
        rcases hB' with h | ⟨md, pk, h, rfl⟩ <;> simp only [longBytes, h] <;> rfl
      exact Option.some_inj.1 ((Option.some_get _).trans e)
    rw [← hB, this]; exact hS
  have hval : ∀ i (hi : i < n.toNat), ((Order.keyAt .i64 B i).toNat : Int) = (x.get ⟨i, hi⟩).toInt + 2 ^ 63 :=
    fun i hi => by
      rw [← key_i64, ← longsOf_get x hi, hB]; rfl
  obtain ⟨hperm, hsort⟩ := grade_spec .i64 false n B
  have hav : min n.toNat (Scan.Kind.avail .i64 B) = n.toNat := by
    rw [show Scan.Kind.avail .i64 B = len B from rfl, hBs, Nat.min_self]
  rw [hav] at hperm
  generalize hG : Order.grade .i64 false n B = G at hperm hsort
  have hGl : len G = n.toNat := by rw [len_eq_ids, hperm.length_eq, List.length_range]
  have hR : Order.ranks .i64 n B = Order.invert G := by rw [← hG]; rfl
  have hI := ids_invert G (by rw [hGl]; exact usize_lt n)
  rw [hR]
  have hget : ∀ i (hi : i < n.toNat), (Column.bitsAt (Order.invert G) (i * 8) 8).toNat = (ids G).idxOf i :=
    fun i hi => by
      have hl : i < (ids (Order.invert G)).length := by rw [hI, List.length_map, List.length_range, hGl]; exact hi
      rw [← ids_getElem hl]; simp only [hI, List.getElem_map, List.getElem_range]
  have hmem : ∀ i, i < n.toNat → i ∈ ids G := fun i hi => hperm.mem_iff.2 (List.mem_range.2 hi)
  rw [hget p hp, hget q hq]
  -- the strict order the stable sort lists the rows in: by value, ties by position
  let R : Nat → Nat → Prop := fun i j =>
    Order.keyAt .i64 B i < Order.keyAt .i64 B j ∨ (Order.keyAt .i64 B i = Order.keyAt .i64 B j ∧ i < j)
  have hs : (ids G).Pairwise R := hsort.imp fun {i j} ⟨h1, h2⟩ => by
    simp only [keyOrd, Bool.false_eq_true, ↓reduceIte] at h1 h2
    rcases UInt64.lt_or_eq_of_le h1 with hl | he
    · exact .inl hl
    · exact .inr ⟨he, h2 (by rw [he]; exact UInt64.le_refl _)⟩
  have hasym : ∀ i j, R i j → ¬ R j i := fun i j h1 h2 => by
    simp only [R, UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj] at h1 h2
    omega
  have hlen : (ids G).length = n.toNat := by rw [hperm.length_eq, List.length_range]
  refine ⟨by rw [← hlen]; exact List.idxOf_lt_length_of_mem (hmem p hp), ?_⟩
  rw [idxOf_lt_iff hs hasym (hmem p hp) (hmem q hq)]
  simp only [R, UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj, Int64.lt_iff_toInt_lt, ← Int64.toInt_inj]
  have e1 := hval p hp; have e2 := hval q hq
  omega

#print axioms idxOf_lt_iff
#print axioms ids_invert
#print axioms key_i64
#print axioms longsOf_rank
#print axioms rank_long

end LeetQ.Rel.Alg
