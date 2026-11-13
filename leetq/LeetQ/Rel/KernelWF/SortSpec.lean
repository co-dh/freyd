/-
  `Obj.sortBy` and `Code.grade`, read back: every grade kernel sorts `til m`, so a grade is a permutation of
  the rows it reads, and `sortBy`'s answer holds the rows it was handed, each once.
-/
import LeetQ.Rel.KernelWF.JoinContent
import LeetQ.Rel.KernelWF.CodesProd
import LeetQ.Rel.KernelWF.Reduce

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.KernelWF

/-- Element `j` of `ids b` is the long `j` of `b`. -/
theorem ids_getElem {b : ByteArray} {j : Nat} (hj : j < (ids b).length) :
    (ids b)[j] = (Column.bitsAt b (j * 8) 8).toNat := (ids_get rfl hj).symm

/-- A sort of `til m` written as longs reads back as a permutation of `til m`. -/
theorem ids_sort_range (m : Nat) (le : Nat → Nat → Bool) (hm : m < 2 ^ 64) :
    (ids (Order.indices ((List.range m).mergeSort le))).Perm (List.range m) := by
  have hp := List.mergeSort_perm (List.range m) le
  rw [ids_indices _ fun i hi => Nat.lt_trans (List.mem_range.1 (hp.mem_iff.1 hi)) hm]
  exact hp

/-- **`gather 8 p g` at a permutation `g` of `p`'s positions holds `p`'s longs, each once.** -/
theorem gather_perm {p g : ByteArray} (hg : (ids g).Perm (List.range (len p))) :
    (ids (gather 8 p g)).Perm (ids p) := by
  have hlt : ∀ j < len g, (Column.bitsAt g (j * 8) 8).toNat < len p := fun j hj => by
    have hj' : j < (ids g).length := by rw [← len_eq_ids]; exact hj
    rw [← ids_getElem hj']; exact List.mem_range.1 (hg.mem_iff.1 (List.getElem_mem hj'))
  have e : ids (gather 8 p g) = (ids g).map fun j => (ids p)[j]! := by
    apply List.ext_getElem
    · simp only [List.length_map, ← len_eq_ids, gather_len]
    · intro j h1 h2
      have hj : j < len g := by rw [len_eq_ids]; simpa using h2
      have hk : (Column.bitsAt g (j * 8) 8).toNat < (ids p).length := by rw [← len_eq_ids]; exact hlt j hj
      rw [ids_getElem h1, gather8_get hj (hlt j hj), List.getElem_map,
        ids_getElem (show j < (ids g).length by rw [← len_eq_ids]; exact hj), getElem!_pos (ids p) _ hk,
        ids_getElem hk]
  rw [e]
  refine (hg.map _).trans (List.Perm.of_eq ?_)
  apply List.ext_getElem
  · simp [← len_eq_ids]
  · intro j _ h2; simp only [List.getElem_map, List.getElem_range]; exact getElem!_pos (ids p) j h2

/-- **`Code.grade` of a well-formed code is a stable sort of its rows**: a permutation of `til n`, ascending in
    a key `κ` that agrees exactly where the codes do — `grade` at the lane's layout, `gradeLane` at `2`/`4` bits
    and past an `i16`/`i32` sign bit. Hypotheses: the lane is one a `Code` takes and the payload holds exactly
    its `n` codes. -/
theorem grade_code (c : Code) (hw : c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64)
    (hs : c.b.size = (c.n.toNat * c.w + 7) / 8) :
    (ids c.grade).Perm (List.range c.n.toNat) ∧ ∃ κ : Nat → Nat,
      (∀ i j, i < c.n.toNat → j < c.n.toNat → (κ i = κ j ↔ Column.idAt c.b c.w i = Column.idAt c.b c.w j)) ∧
      (ids c.grade).Pairwise fun i j => κ i ≤ κ j := by
  have h0 : 0 < c.w := by omega
  have h64 : c.w ≤ 64 := by omega
  have hl : (ids (Order.gradeLane false c.n c.w.toUSize c.b)).Perm (List.range c.n.toNat) ∧ ∃ κ : Nat → Nat,
      (∀ i j, i < c.n.toNat → j < c.n.toNat → (κ i = κ j ↔ Column.idAt c.b c.w i = Column.idAt c.b c.w j)) ∧
      (ids (Order.gradeLane false c.n c.w.toUSize c.b)).Pairwise fun i j => κ i ≤ κ j := by
    obtain ⟨hp, hsrt⟩ := gradeLane_spec false c.n c.w.toUSize c.b
    have hcap : c.w * c.n.toNat ≤ 8 * c.b.size := by rw [hs, Nat.mul_comm]; omega
    rw [lane_toNat h64, idsCap_full h0 hcap] at hp
    rw [lane_toNat h64] at hsrt
    exact ⟨hp, fun i => Column.idAt c.b c.w i, fun _ _ _ _ => Iff.rfl,
      hsrt.imp fun ⟨h1, _⟩ => by simpa using h1⟩
  unfold Code.grade Code.kind
  split
  next k hk =>
    split
    next => exact hl
    next =>
      obtain ⟨hp, hsrt⟩ := grade_spec k false c.n c.b
      rw [Nat.min_eq_left (avail_lane hk hs)] at hp
      refine ⟨hp, fun i => (Order.keyAt k c.b i).toNat, fun i j _ _ => ?_, hsrt.imp fun ⟨h1, _⟩ => ?_⟩
      · show (Order.keyAt k c.b i).toNat = (Order.keyAt k c.b j).toNat ↔ _
        rw [← keyAt_iff_idAt hk]; exact ⟨fun e => UInt64.toNat_inj.1 e, fun e => by rw [e]⟩
      · simp only [keyOrd, Bool.false_eq_true, ↓reduceIte] at h1; exact UInt64.le_iff_toNat_le.1 h1
  next => exact hl

/-- **Every grade `gradeColumn` answers ascending is a sort of `til m`** (`indices` of a `mergeSort`): `grade`,
    `gradeFoR`, `gradeSyms`, `gradeIds`, `gradeGuid` alike. -/
theorem gradeColumn_sort {t : QAtomicType} {n : USize} {e v : Enc} (h : gradeColumn t false n e = some v) :
    ∃ m le, v = .bytes (Order.indices ((List.range m).mergeSort le)) := by
  unfold gradeColumn at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  split at h
  all_goals first
    | (cases h; exact ⟨_, _, rfl⟩)
    | (obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨_, _, rfl⟩)
    | (split at h
       · cases h
       split at h
       · cases h
       split at h
       · cases h; exact ⟨_, _, rfl⟩
       · split at h
         · split at h
           · cases h
           · cases h; exact ⟨_, _, rfl⟩
         · cases h)

/-- **`Obj.sortBy` permutes the rows it is handed**: its answer holds the longs of `p`, each once, at every
    side. Hypotheses: `len p` fits a `USize`; every one-part code is well formed and of its part's count (the
    codes `sortBy` grades where no kernel orders the values). -/
theorem sortBy_perm
    (hW : ∀ (B : Obj) (x : Part B), (((Obj.codes B #v[x])[0]).w = 1 ∨ ((Obj.codes B #v[x])[0]).w = 2 ∨
      ((Obj.codes B #v[x])[0]).w = 4 ∨ ((Obj.codes B #v[x])[0]).w = 8 ∨ ((Obj.codes B #v[x])[0]).w = 16 ∨
      ((Obj.codes B #v[x])[0]).w = 32 ∨ ((Obj.codes B #v[x])[0]).w = 64) ∧
      ((Obj.codes B #v[x])[0]).b.size = (((Obj.codes B #v[x])[0]).n.toNat * ((Obj.codes B #v[x])[0]).w + 7) / 8 ∧
      ((Obj.codes B #v[x])[0]).n = x.1) :
    (A : Obj) → {n : USize} → (c : Vals A n) → (p : ByteArray) → len p < USize.size →
      (ids (A.sortBy c p)).Perm (ids p)
  | .atom t, n, c, p, hl => by
    have hx := pick_len t ⟨_, c⟩ p hl
    have hc : (ids (Code.grade (codes t #v[pick t ⟨_, c⟩ p])[0])).Perm (List.range (len p)) := by
      obtain ⟨hw, hs, hn⟩ := hW (.atom t) (pick t ⟨_, c⟩ p)
      have := (grade_code _ hw hs).1
      rw [show ((Obj.codes (.atom t) #v[pick t ⟨_, c⟩ p])[0]).n = _ from hn, hx] at this
      exact this
    simp only [Obj.sortBy]
    split
    next g hg =>
      obtain ⟨m, le, hv⟩ := gradeColumn_sort hg
      cases hv
      have hwf := gradeColumn_wf (pick t ⟨_, c⟩ p).2.wf hg
      simp only [Enc.WF, QAtomicType.width] at hwf
      rw [indices_size, List.length_mergeSort, List.length_range, hx] at hwf
      have hm : m = len p := by omega
      subst hm
      exact gather_perm (ids_sort_range _ le (Nat.lt_of_lt_of_le hl (by have := USize.size_le; omega)))
    next => exact gather_perm hc
  | .prod a b, n, c, p, hl => by
    have h2 := sortBy_perm hW b c.2 p hl
    have hl2 : len (b.sortBy c.2 p) < USize.size := by rw [len_eq_ids, h2.length_eq, ← len_eq_ids]; exact hl
    exact (sortBy_perm hW a c.1 _ hl2).trans h2
  | .arr b, n, c, p, hl => by
    obtain ⟨hw, hs, hn⟩ := hW (.arr b) (Vals.pickPart (.arr b) c p)
    have hpn : (Vals.pickPart (.arr b) c p).1.toNat = len p := by
      unfold Vals.pickPart need; rw [dif_pos hl]; exact USize.toNat_ofNat_of_lt' hl
    have := (grade_code _ hw hs).1
    rw [hn, hpn] at this
    exact gather_perm this
  | .sum a b, n, c, p, hl => by
    obtain ⟨hw, hs, hn⟩ := hW (.sum a b) (Vals.pickPart (.sum a b) c p)
    have hpn : (Vals.pickPart (.sum a b) c p).1.toNat = len p := by
      unfold Vals.pickPart need; rw [dif_pos hl]; exact USize.toNat_ofNat_of_lt' hl
    have := (grade_code _ hw hs).1
    rw [hn, hpn] at this
    exact gather_perm this

#print axioms gather_perm
#print axioms grade_code
#print axioms sortBy_perm

end LeetQ.Rel.Alg
