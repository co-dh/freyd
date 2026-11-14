/-
  The grade that puts cells in place, read back: `cons` (and every op that lays cells out by a column of
  destinations) grades `Code.ofLongs` of the destinations, and where those are distinct and below their count
  the grade is the inverse permutation — position `d` holds the cell whose destination is `d`.
-/
import LeetQ.Rel.KernelWF.SortSpec
import LeetQ.Rel.KernelWF.SegSpec

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.KernelWF

/-- **A sort of distinct keys below their count is the inverse permutation**: `g` lists `til N` sorted by
    `key`, `key` one-to-one on `til N` and below `N`, so the key of `g[d]` is `d`. -/
theorem sorted_perm_key {N : Nat} (g : List Nat) (key : Nat → Nat) (hp : g.Perm (List.range N))
    (hs : g.Pairwise fun i j => key i ≤ key j) (hinj : ∀ i j, i < N → j < N → key i = key j → i = j)
    (hlt : ∀ i, i < N → key i < N) :
    ∀ d (hd : d < g.length), key g[d] = d := by
  have hnd : g.Pairwise (· ≠ ·) := hp.nodup_iff.2 List.nodup_range
  have hlen : g.length = N := by rw [hp.length_eq, List.length_range]
  have hmem : ∀ d (hd : d < g.length), g[d] < N := fun d hd => List.mem_range.1 (hp.mem_iff.1 (List.getElem_mem hd))
  have hstrict : ∀ d e (hd : d < g.length) (he : e < g.length), d < e → key g[d] < key g[e] := by
    intro d e hd he hde
    refine Nat.lt_of_le_of_ne (List.pairwise_iff_getElem.1 hs d e hd he hde) fun heq => ?_
    exact List.pairwise_iff_getElem.1 hnd d e hd he hde (hinj _ _ (hmem d hd) (hmem e he) heq)
  have hlow : ∀ d (hd : d < g.length), d ≤ key g[d] := by
    intro d
    induction d with
    | zero => intro _; exact Nat.zero_le _
    | succ d ih => intro hd; have := ih (by omega); have := hstrict d (d + 1) (by omega) hd (by omega); omega
  have hgap : ∀ k d (hd : d + k < g.length), key (g[d]'(by omega)) + k ≤ key g[d + k] := by
    intro k
    induction k with
    | zero => intro d _; exact Nat.le_refl _
    | succ k ih =>
      intro d hd
      have h1 := ih d (by omega)
      have h2 : key g[d + k] < key g[d + (k + 1)] := hstrict (d + k) (d + (k + 1)) (by omega) hd (by omega)
      omega
  intro d hd
  have h1 := hgap (g.length - 1 - d) d (by omega)
  have h2 := hlt _ (hmem (d + (g.length - 1 - d)) (by omega))
  have h3 := hlow d hd
  omega

/-- A long below `2^63` with its sign bit flipped is `2^63` above it. -/
theorem xor_pow63 {x : Nat} (h : x < 2 ^ 63) : x ^^^ 2 ^ 63 = 2 ^ 63 + x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  rcases Nat.lt_trichotomy i 63 with hi | rfl | hi
  · rw [Nat.testBit_two_pow_add_gt hi, decide_eq_false (by omega), Bool.xor_false]
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow h] <;> decide
  · have h64 : 2 ^ 64 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [decide_eq_false (by omega), Bool.xor_false, Nat.testBit_lt_two_pow (show x < 2 ^ i by omega),
      Nat.testBit_lt_two_pow (show 2 ^ 63 + x < 2 ^ i by omega)]

/-- **The grade of `Code.ofLongs b`, `b`'s longs distinct and below their count, is `b` inverted**: it lists
    every position of `b` once, and the long of `b` at its position `d` is `d`. -/
theorem grade_ofLongs_inv (b : ByteArray) (hN : len b < USize.size) (h63 : len b < 2 ^ 63)
    (hlt : ∀ i, i < len b → (Column.bitsAt b (i * 8) 8).toNat < len b)
    (hinj : ∀ i j, i < len b → j < len b → Column.bitsAt b (i * 8) 8 = Column.bitsAt b (j * 8) 8 → i = j) :
    ∃ hg : (ids (Code.ofLongs b).grade).length = len b,
      (∀ d (hd : d < len b), (Column.bitsAt b ((ids (Code.ofLongs b).grade)[d]'(Nat.lt_of_lt_of_eq hd hg.symm) * 8)
        8).toNat = d) ∧ ∀ d (hd : d < len b), (ids (Code.ofLongs b).grade)[d]'(Nat.lt_of_lt_of_eq hd hg.symm) < len b := by
  have hm : ((len b).toUSize).toNat = len b := USize.toNat_ofNat_of_lt' hN
  have hc : Code.ofLongs b = ⟨64, (len b).toUSize, 2 ^ 64, b⟩ := by
    unfold Code.ofLongs longCount need; rw [dif_pos hN]
  have hg : (Code.ofLongs b).grade = Order.grade .i64 false (len b).toUSize b := by rw [hc]; rfl
  obtain ⟨hp, hs⟩ := grade_spec .i64 false (len b).toUSize b
  have hav : min ((len b).toUSize).toNat (Scan.Kind.avail .i64 b) = len b := by
    rw [hm]; exact Nat.min_eq_left (Nat.le_of_eq rfl)
  rw [hav] at hp
  rw [← hg] at hp hs
  have hkey : ∀ i, i < len b → (Order.keyAt .i64 b i).toNat = 2 ^ 63 + (Column.bitsAt b (i * 8) 8).toNat := by
    intro i hi
    show (Column.bitsAt b (i * 8) 8 ^^^ 0x8000000000000000).toNat = _
    rw [UInt64.toNat_xor, show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl]
    exact xor_pow63 (by have := hlt i hi; omega)
  have hlen : (ids (Code.ofLongs b).grade).length = len b := by rw [hp.length_eq, List.length_range]
  refine ⟨hlen, fun d hd => ?_, fun d hd => List.mem_range.1 (hp.mem_iff.1 (List.getElem_mem _))⟩
  refine sorted_perm_key (N := len b) _ (fun i => (Column.bitsAt b (i * 8) 8).toNat) hp ?_ ?_ hlt d _
  · refine hs.imp_of_mem fun {i j} hi hj h => ?_
    have hi' := List.mem_range.1 (hp.mem_iff.1 hi)
    have hj' := List.mem_range.1 (hp.mem_iff.1 hj)
    have h := h.1
    simp only [keyOrd, Bool.false_eq_true, ↓reduceIte] at h
    have := UInt64.le_iff_toNat_le.1 h
    rw [hkey i hi', hkey j hj'] at this
    dsimp only
    omega
  · intro i j hi hj h
    exact hinj i j hi hj (UInt64.toNat_inj.1 h)

/-- **Cells laid out in consecutive blocks never collide**: block `r` holds `[P r, P (r+1))`, `P` ascending, so
    `P r + t = P r' + t'` with each inside its own block is one block at one place. -/
theorem block_inj {n : Nat} {P : Nat → Nat} (hPs : ∀ r < n, P r < P (r + 1)) :
    ∀ r t r' t', r < n → r' < n → P r + t < P (r + 1) → P r' + t' < P (r' + 1) → P r + t = P r' + t' →
      r = r' ∧ t = t' := by
  have hle : ∀ a b, a ≤ b → b ≤ n → P a ≤ P b := fun a b hab hb => by
    rcases Nat.lt_or_eq_of_le hab with h | rfl
    · exact Nat.le_of_lt (prefix_lt hPs a b h hb)
    · exact Nat.le_refl _
  intro r t r' t' hr hr' ht ht' e
  rcases Nat.lt_trichotomy r r' with h | rfl | h
  · have := hle (r + 1) r' (by omega) (by omega); omega
  · exact ⟨rfl, by omega⟩
  · have := hle (r' + 1) r (by omega) (by omega); omega

/-- **Two long payloads end to end, read back**: long `d` is the first's below its count, the second's past
    it, the first holding exactly its longs. -/
theorem concat2_get {a c : ByteArray} (ha : a.size = len a * 8) (d : Nat) :
    Column.bitsAt (concatBytes #[a, c]) (d * 8) 8 =
      if d < len a then Column.bitsAt a (d * 8) 8 else Column.bitsAt c ((d - len a) * 8) 8 := by
  have e : concatBytes #[a, c] = a ++ c := by simp [concatBytes]
  rw [e]
  split
  · exact KernelWF.bitsAt_congr fun j hj => by
      rw [ByteArray.data_append, Array.getElem?_append_left (by rw [ByteArray.size_data]; omega)]
  · exact KernelWF.bitsAt_congr fun j hj => by
      rw [ByteArray.data_append, Array.getElem?_append_right (by rw [ByteArray.size_data]; omega),
        ByteArray.size_data]
      exact congrArg (c.data[·]?) (by omega)

end LeetQ.Rel.Alg

#print axioms LeetQ.Rel.Alg.block_inj
#print axioms LeetQ.Rel.Alg.concat2_get
#print axioms LeetQ.Rel.Alg.sorted_perm_key
#print axioms LeetQ.Rel.Alg.xor_pow63
#print axioms LeetQ.Rel.Alg.grade_ofLongs_inv
