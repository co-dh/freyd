/-
  `Code.runStarts` read back at every lane. The three kernels — `runStarts` at a byte lane, `runStartsIds` at
  `2`/`4` bits, `runStartsBits` at one — are one fold, "push `i` where `f i ≠ f (i-1)`, then push `n`", so it is
  read back once for an arbitrary `f` (`runs_fold`) and instantiated at each lane (`code_runs`).
-/
import LeetQ.Rel.KernelWF.SortSpec

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.KernelWF

/-- **The run-start fold cuts a column into its runs**, for any `f`: `B` holds `m` starts and then `n`, read
    back as naturals, ascending; where `key` agrees exactly where `f` does and its equal elements stand
    together, the run keys are one-to-one and `key s = key (r j) ⟺ r j ≤ s < r (j+1)` (`runs_group`). -/
theorem runs_fold {α β : Type} [BEq α] [LawfulBEq α] (f : Nat → α) (n : Nat) (t : UInt64) (ht : t.toNat = n)
    (key : Nat → β) (hk : ∀ i j, i < n → j < n → (key i = key j ↔ f i = f j))
    (hcont : ∀ s t u, s ≤ t → t ≤ u → u < n → key s = key u → key t = key s)
    (B : ByteArray) (hB : B = Column.pushBits ((List.range n).foldl (init := ByteArray.empty) fun acc i =>
      if i == 0 || f i != f (i - 1) then Column.pushBits acc i.toUInt64 8 else acc) t 8) :
    ∃ m, B.size = 8 * (m + 1) ∧ (Column.bitsAt B (m * 8) 8).toNat = n ∧
      (∀ i j, i < j → j ≤ m → (Column.bitsAt B (i * 8) 8).toNat < (Column.bitsAt B (j * 8) 8).toNat) ∧
      (∀ j j', j < m → j' < m →
        key (Column.bitsAt B (j * 8) 8).toNat = key (Column.bitsAt B (j' * 8) 8).toNat → j = j') ∧
      (∀ s j, s < n → j < m → (key s = key (Column.bitsAt B (j * 8) 8).toNat ↔
        (Column.bitsAt B (j * 8) 8).toNat ≤ s ∧ s < (Column.bitsAt B ((j + 1) * 8) 8).toNat)) ∧
      (∀ s, s < n → ∃ j, j < m ∧
        (Column.bitsAt B (j * 8) 8).toNat ≤ s ∧ s < (Column.bitsAt B ((j + 1) * 8) 8).toNat) := by
  have hn64 : n < 2 ^ 64 := ht ▸ UInt64.toNat_lt t
  let p : Nat → Bool := fun i => i == 0 || f i != f (i - 1)
  have hp : ∀ r, p r = true ↔ (r = 0 ∨ f r ≠ f (r - 1)) := fun r => by
    simp only [p, Bool.or_eq_true, beq_iff_eq, bne_iff_ne]
  have hf : ∀ (l : List Nat) (acc : ByteArray),
      l.foldl (fun acc i => if p i then Column.pushBits acc i.toUInt64 8 else acc) acc =
        (l.filter p).foldl (fun acc i => Column.pushBits acc i.toUInt64 8) acc := by
    intro l; induction l with
    | nil => intro _; rfl
    | cons a l ih =>
      intro acc; simp only [List.foldl_cons, List.filter_cons]
      cases h : p a <;> simp only [ite_true, Bool.false_eq_true, ite_false, List.foldl_cons, ih]
  have htn : t = n.toUInt64 :=
    UInt64.toNat_inj.1 (by rw [ht, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hn64])
  obtain ⟨F, hFd⟩ : ∃ F, F = (List.range n).filter p := ⟨_, rfl⟩
  have hout : B = (F ++ [n]).foldl (fun acc i => Column.pushBits acc i.toUInt64 8) ByteArray.empty := by
    rw [hB, htn, hFd, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hf]
  have hmem : ∀ x, x ∈ F ↔ x < n ∧ p x = true := fun x => by rw [hFd, List.mem_filter, List.mem_range]
  have hF : F.Pairwise (· < ·) := by
    rw [hFd]; exact (by simpa using (pairwise_map_range_iff (· < ·) id n).2 (fun i j h _ => h) :
      (List.range n).Pairwise (· < ·)).filter p
  have hL : (F ++ [n]).Pairwise (· < ·) := List.pairwise_append.2 ⟨hF, by simp,
    fun a ha b hb => by rw [List.mem_singleton] at hb; rw [hb]; exact ((hmem a).1 ha).1⟩
  obtain ⟨hs, -, hg⟩ := foldl_pushBits (fun i : Nat => i.toUInt64) 8 (by decide) (F ++ [n]) ByteArray.empty
  rw [← hout, show ByteArray.empty.size = 0 from rfl] at hs hg
  have hlen : (F ++ [n]).length = F.length + 1 := by simp
  have hv : ∀ j (h : j < (F ++ [n]).length), (Column.bitsAt B (j * 8) 8).toNat = (F ++ [n])[j] := by
    intro j h
    have hle : (F ++ [n])[j] ≤ n := by
      have hm := List.getElem_mem h
      rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact Nat.le_of_lt ((hmem _).1 hm).1
      · exact Nat.le_of_eq hm
    have h64 : (F ++ [n])[j] < 2 ^ 64 := by omega
    rw [show j * 8 = 0 + 8 * j by omega, hg j h, Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt h64, show (2 : Nat) ^ (8 * 8) = 2 ^ 64 from rfl, Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h64]
  have hleft : ∀ j (h : j < F.length), (F ++ [n])[j]'(by omega) = F[j] := fun j h => List.getElem_append_left h
  have hlast : (Column.bitsAt B (F.length * 8) 8).toNat = n := by
    rw [hv _ (by omega)]; simp
  have hasc : ∀ i j, i < j → j ≤ F.length →
      (Column.bitsAt B (i * 8) 8).toNat < (Column.bitsAt B (j * 8) 8).toNat := fun i j hij hj => by
    rw [hv i (by omega), hv j (by omega)]
    exact List.pairwise_iff_getElem.1 hL i j (by omega) (by omega) hij
  have hrj : ∀ j (h : j < F.length), (Column.bitsAt B (j * 8) 8).toNat = F[j] := fun j h => by
    rw [hv j (by omega), hleft j h]
  have h00 : 0 < n → 0 < F.length ∧ (Column.bitsAt B (0 * 8) 8).toNat = 0 := fun h0 => by
    have h0m : 0 ∈ F := (hmem 0).2 ⟨h0, rfl⟩
    have hpos := List.length_pos_of_mem h0m
    obtain ⟨k, hk', hk0⟩ := List.getElem_of_mem h0m
    refine ⟨hpos, ?_⟩
    rw [hrj 0 hpos]
    rcases Nat.eq_zero_or_pos k with rfl | hk''
    · exact hk0
    · have := List.pairwise_iff_getElem.1 hF 0 k hpos hk' hk''; omega
  -- every row below `n` lies in some run: the runs start at `0` and end at `n`
  have hcov : ∀ s, s < n → ∃ j, j < F.length ∧
      (Column.bitsAt B (j * 8) 8).toNat ≤ s ∧ s < (Column.bitsAt B ((j + 1) * 8) 8).toNat := by
    intro s
    induction s with
    | zero =>
      intro hn0
      obtain ⟨hm, e⟩ := h00 hn0
      exact ⟨0, hm, by omega, by have := hasc 0 (0 + 1) (by omega) hm; omega⟩
    | succ s ih =>
      intro hn'
      obtain ⟨j, hj, h1, h2⟩ := ih (by omega)
      rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt h2) with h | h
      · exact ⟨j, hj, by omega, h⟩
      · have hj1 : j + 1 < F.length := by
          rcases Nat.lt_or_ge (j + 1) F.length with h' | h'
          · exact h'
          · have : j + 1 = F.length := by omega
            rw [this] at h; omega
        exact ⟨j + 1, hj1, by omega, by have := hasc (j + 1) (j + 1 + 1) (by omega) hj1; omega⟩
  have G := runs_group key (fun j => (Column.bitsAt B (j * 8) 8).toNat) hlast hasc
    (fun h0 => (h00 h0).2)
    (fun j hj => by
      show (Column.bitsAt B (j * 8) 8).toNat = 0 ∨ key (Column.bitsAt B (j * 8) 8).toNat ≠
        key ((Column.bitsAt B (j * 8) 8).toNat - 1)
      rw [hrj j hj]
      have hm := (hmem _).1 (List.getElem_mem hj)
      exact ((hp _).1 hm.2).imp id fun h e => h ((hk _ _ hm.1 (by omega)).1 e))
    (fun s hs' h => by
      have hps : p s = true := (hp s).2 (h.imp id fun h e => h ((hk _ _ hs' (by omega)).2 e))
      obtain ⟨j, hj, e⟩ := List.getElem_of_mem ((hmem s).2 ⟨hs', hps⟩)
      exact ⟨j, hj, by show (Column.bitsAt B (j * 8) 8).toNat = s; rw [hrj j hj, e]⟩)
    hcont
  exact ⟨F.length, by rw [hs, hlen]; omega, hlast, hasc, G.1, G.2, hcov⟩

/-- **`Code.runStarts` cuts a well-formed code whose equal codes stand together into its runs**, at every
    lane: `runStartsBits` at one bit, `runStarts` at a byte lane, `runStartsIds` at `2`/`4` bits (`runs_fold`).
    Hypotheses: the lane is one a `Code` takes, the payload holds exactly its `n` codes, equal codes contiguous. -/
theorem code_runs (c : Code) (hw : laneOK(c.w))
    (hs : c.b.size = (c.n.toNat * c.w + 7) / 8)
    (hcont : ∀ s t u, s ≤ t → t ≤ u → u < c.n.toNat → Column.idAt c.b c.w s = Column.idAt c.b c.w u →
      Column.idAt c.b c.w t = Column.idAt c.b c.w s) :
    ∃ m, c.runStarts.size = 8 * (m + 1) ∧ (Column.bitsAt c.runStarts (m * 8) 8).toNat = c.n.toNat ∧
      (∀ i j, i < j → j ≤ m →
        (Column.bitsAt c.runStarts (i * 8) 8).toNat < (Column.bitsAt c.runStarts (j * 8) 8).toNat) ∧
      (∀ j j', j < m → j' < m → Column.idAt c.b c.w (Column.bitsAt c.runStarts (j * 8) 8).toNat =
        Column.idAt c.b c.w (Column.bitsAt c.runStarts (j' * 8) 8).toNat → j = j') ∧
      (∀ s j, s < c.n.toNat → j < m →
        (Column.idAt c.b c.w s = Column.idAt c.b c.w (Column.bitsAt c.runStarts (j * 8) 8).toNat ↔
          (Column.bitsAt c.runStarts (j * 8) 8).toNat ≤ s ∧
            s < (Column.bitsAt c.runStarts ((j + 1) * 8) 8).toNat)) ∧
      (∀ s, s < c.n.toNat → ∃ j, j < m ∧ (Column.bitsAt c.runStarts (j * 8) 8).toNat ≤ s ∧
        s < (Column.bitsAt c.runStarts ((j + 1) * 8) 8).toNat) := by
  have hN : c.n.toUInt64.toNat = c.n.toNat := USize.toNat_toUInt64 c.n
  have h64 : c.w ≤ 64 := by omega
  unfold Code.runStarts Code.kind
  split
  next h =>
    obtain ⟨-, hw1⟩ := (laneKind_some h).resolve_right fun ⟨hne, _⟩ => hne rfl
    refine runs_fold (Column.bitAt c.b) c.n.toNat c.n.toUInt64 hN _ (fun i j _ _ => ?_) hcont _ rfl
    rw [hw1, idAt_one, idAt_one]
    cases Column.bitAt c.b i <;> cases Column.bitAt c.b j <;> simp
  next k hnb h =>
    obtain ⟨hne, hwk, hkw, hk⟩ := (laneKind_some h).resolve_left fun ⟨e, _⟩ => hnb e
    have hl : k.width.toUSize.toNat = k.width := lane_toNat (by omega)
    have hn : c.b.size / k.width.toUSize.toNat = c.n.toNat := by
      rw [hl, hs, hwk]; rcases hkw with e | e | e | e <;> rw [e] <;> omega
    have hlt : c.n.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le c.n.toNat_lt_size (by have := USize.size_le; omega)
    have e := runs_fold (Kernel.key k.width.toUSize.toNat false c.b) (c.b.size / k.width.toUSize.toNat)
      (c.b.size / k.width.toUSize.toNat).toUInt64
      (by rw [hn, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]) (Column.idAt c.b c.w)
      (fun i j _ _ => by rw [hl, key_eq_iff_keyAt hk, keyAt_iff_idAt h]) (by rw [hn]; exact hcont)
      (Kernel.runStarts k.width.toUSize false c.b) rfl
    rw [hn] at e
    exact e
  next h =>
    have hl : c.w.toUSize.toNat = c.w := lane_toNat h64
    exact runs_fold (Column.idAt c.b c.w.toUSize.toNat) c.n.toNat c.n.toUInt64 hN _
      (fun i j _ _ => by rw [hl]) hcont _ rfl

#print axioms runs_fold
#print axioms code_runs

end LeetQ.Rel.Alg
