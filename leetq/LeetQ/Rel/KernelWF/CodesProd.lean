/-
  What `Code.cat` and `Code.cut` CONTAIN: code `i` of a concatenation is code `i` of the part it falls in,
  moved past the counts before that part, and `cut` reads that back. Then the joint codes of a side of
  several parts, read through `raze`, `groupIdsColumn`, `Code.ofIds` and `cut`.
-/
import LeetQ.Rel.KernelWF.CodesSpec
import LeetQ.Rel.KernelWF.RazeSpec
import LeetQ.Rel.KernelWF.Lane

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

/-! ## Offsets -/

/-- A `USize` sum whose `Nat` sum fits a `USize` is that `Nat` sum. -/
theorem usize_foldl_add : ∀ (l : List USize) (a : USize), a.toNat + (l.map (·.toNat)).sum < USize.size →
    (l.foldl (· + ·) a).toNat = a.toNat + (l.map (·.toNat)).sum
  | [], a, _ => by simp
  | x :: l, a, h => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons] at h ⊢
    have hx : (a + x).toNat = a.toNat + x.toNat := by rw [USize.toNat_add, Nat.mod_eq_of_lt (show a.toNat + x.toNat < USize.size by omega)]
    rw [usize_foldl_add l (a + x) (by rw [hx]; omega), hx, Nat.add_assoc]

/-- The counts before part `k` and part `k`'s own lie within the whole. -/
theorem take_sum_le : ∀ (l : List Nat) {k : Nat} (hk : k < l.length), (l.take k).sum + l[k] ≤ l.sum
  | [], _, hk => absurd hk (by simp)
  | x :: l, 0, _ => by simp
  | x :: l, k + 1, hk => by
    have := take_sum_le l (k := k) (by simpa using hk)
    simp only [List.take_succ_cons, List.sum_cons, List.getElem_cons_succ]; omega

/-! ## `Code.cut` -/

/-- **Part `k` of `c.cut ns` reads `c` past the counts before it**, the counts summing to `c.n`: a byte
    extract at a byte lane, `cycleBits` at a bit, `cycleIds` at `2`/`4` bits. -/
theorem cut_get {p : Nat} (c : Code) (ns : Vector USize p)
    (hw : c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64)
    (hs : (ns.toList.map (·.toNat)).sum = c.n.toNat) {k : Nat} (hk : k < p) :
    (c.cut ns)[k].w = c.w ∧ (c.cut ns)[k].n = ns[k] ∧ (c.cut ns)[k].card = c.card ∧
      ∀ i < ns[k].toNat, Column.idAt (c.cut ns)[k].b c.w i =
        Column.idAt c.b c.w (((ns.toList.take k).map (·.toNat)).sum + i) := by
  have hle := take_sum_le (ns.toList.map (·.toNat)) (k := k) (by simpa using hk)
  simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take, hs] at hle
  unfold Code.cut
  by_cases hp : p = 1
  · subst hp
    have hk0 : k = 0 := by omega
    subst hk0
    rw [if_pos rfl]
    simp only [Vector.getElem_replicate, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add]
    have hn : ns.toList = [ns[0]] := by
      apply List.ext_getElem (by simp) fun j h1 _ => ?_
      simp at h1; subst h1; simp
    rw [hn] at hs
    exact ⟨by simp, USize.toNat_inj.1 (by simpa using hs.symm), by simp, fun _ _ => by simp⟩
  rw [if_neg hp]
  simp only [Vector.getElem_mapIdx]
  refine ⟨by simp, by simp, by simp, fun i hi => ?_⟩
  have ho : ((ns.toArray.extract 0 k).foldl (· + ·) 0).toNat = ((ns.toList.take k).map (·.toNat)).sum := by
    rw [← Array.foldl_toList, Array.toList_extract, List.extract_eq_drop_take, List.drop_zero, Nat.sub_zero,
      usize_foldl_add _ _ (by simp only [USize.toNat_zero, Nat.zero_add]; exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ ns[k].toNat) hle) c.n.toNat_lt_size)]
    rw [USize.toNat_zero, Nat.zero_add]; rfl
  generalize (ns.toArray.extract 0 k).foldl (· + ·) 0 = o at ho
  rw [← ho]
  have hn : o.toNat + ns[k].toNat ≤ c.n.toNat := by rw [ho]; exact hle
  rw [if_neg (by simp only [beq_iff_eq]; intro h; rw [h] at hi; simp at hi)]
  by_cases h8 : c.w % 8 = 0
  · rw [if_pos (by simpa using h8)]
    obtain ⟨q, hq, hq8⟩ : ∃ q, c.w = 8 * q ∧ q ≤ 8 := ⟨c.w / 8, by omega, by omega⟩
    rw [hq, idAt_lane _ hq8, idAt_lane _ hq8, show 8 * q / 8 = q by omega, bitsAt_extract]
    · congr 2; rw [Nat.add_mul, Nat.mul_comm q]
    · have : (i + 1) * q ≤ ns[k].toNat * q := Nat.mul_le_mul_right q hi
      rw [Nat.add_mul, Nat.one_mul] at this; rw [Nat.mul_add, Nat.mul_comm q ns[k].toNat]; omega
  rw [if_neg (by simpa using h8)]
  by_cases h1 : c.w = 1
  · rw [if_pos (by simpa using h1), h1, idAt_one, idAt_one]
    unfold cycleBits
    rw [bitAt_packOf _ _ _ hi, Nat.mod_eq_of_lt (by omega)]
  rw [if_neg (by simpa using h1)]
  have hw64 : c.w ≤ 64 := by omega
  unfold cycleIds
  rw [lane_toNat hw64, idAt_packIds (f := fun j => Column.idAt c.b c.w ((o.toNat + j) % c.n.toNat)) (by omega) hi
    (idAt_lt _ _ _ hw64), Nat.mod_eq_of_lt (by omega)]

end LeetQ.Rel.Alg
