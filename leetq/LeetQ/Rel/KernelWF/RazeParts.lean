/-
  The Frame-of-Reference join read back at any number of parts: each of `concatFoR`'s three answers — the blocks
  moved whole (`moveFoR`), the later parts' decodes written into the first part's last block (`appendFoR`), the
  parts decoded, joined and encoded again — lists the parts' elements one part after another, to their low `8w`
  bits, which is all `atomOfBits` reads.
-/
import LeetQ.Rel.KernelWF.AppendFoR

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Dep LeetQ.Rel LeetQ.Rel.Alg

/-- A `UInt64` cut to its low `8w` bits, `w ≤ 8`, keeps that value as a `Nat`. -/
theorem ofNat_mod_toNat {w : Nat} (hw8 : w ≤ 8) (v : UInt64) :
    (UInt64.ofNat (v.toNat % 2 ^ (8 * w))).toNat = v.toNat % 2 ^ (8 * w) := by
  have h : v.toNat % 2 ^ (8 * w) < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by omega))
  simp [Nat.mod_eq_of_lt h]

/-- A map over `range` of the parts' summed count is the parts' own maps laid end to end, when element
    `(counts before part k) + i` is part `k`'s element `i`. -/
theorem range_map_flatten {α β : Type} (n : α → Nat) (G : α → Nat → β) :
    ∀ (F : Nat → β) (l : List α), (∀ k (hk : k < l.length), ∀ i < n l[k], F (((l.take k).map n).sum + i) = G l[k] i) →
      (List.range (l.map n).sum).map F = (l.map fun q => (List.range (n q)).map (G q)).flatten
  | _, [], _ => rfl
  | F, q :: l, h => by
    rw [List.map_cons, List.sum_cons, List.range_add, List.map_append, List.map_cons, List.flatten_cons, List.map_map]
    congr 1
    · exact List.map_congr_left fun i hi => by simpa using h 0 (by simp) i (List.mem_range.1 hi)
    · exact range_map_flatten n G (fun i => F (n q + i)) l fun k hk i hi => by
        simpa [Nat.add_assoc] using h (k + 1) (by simpa using hk) i hi

theorem foldl_arr_size {α β : Type} (f : α → Array β) : ∀ (l : List α) (acc : Array β),
    (l.foldl (fun a p => a ++ f p) acc).size = acc.size + (l.map fun p => (f p).size).sum
  | [], _ => by simp
  | p :: l, acc => by
    rw [List.foldl_cons, foldl_arr_size f l, Array.size_append, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem foldl_arr_prefix {α β : Type} (f : α → Array β) : ∀ (l : List α) (acc : Array β) {x : Nat}, x < acc.size →
    (l.foldl (fun a p => a ++ f p) acc)[x]? = acc[x]?
  | [], _, _, _ => rfl
  | p :: l, acc, x, hx => by
    rw [List.foldl_cons, foldl_arr_prefix f l _ (by rw [Array.size_append]; omega), Array.getElem?_append_left hx]

/-- Entry `b` of part `k`'s array lies past `acc` and the arrays before it. -/
theorem foldl_arr_get {α β : Type} (f : α → Array β) : ∀ (l : List α) (acc : Array β) {k : Nat} (hk : k < l.length)
    {b : Nat}, b < (f l[k]).size →
    (l.foldl (fun a p => a ++ f p) acc)[acc.size + ((l.take k).map fun p => (f p).size).sum + b]? = (f l[k])[b]?
  | [], _, _, hk, _, _ => absurd hk (by simp)
  | p :: l, acc, 0, _, b, hb => by
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero, List.foldl_cons]
    rw [foldl_arr_prefix f l _ (by rw [Array.size_append]; exact Nat.add_lt_add_left hb _),
      Array.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    rfl
  | p :: l, acc, k + 1, hk, b, hb => by
    have ih := foldl_arr_get f l (acc ++ f p) (k := k) (by simpa using hk) hb
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.foldl_cons, List.getElem_cons_succ]
    rw [Array.size_append] at ih
    rw [← Nat.add_assoc acc.size, ih]

theorem foldl_arr_mem {α β : Type} (f : α → Array β) : ∀ (l : List α) (acc : Array β) (x : β),
    x ∈ l.foldl (fun a p => a ++ f p) acc → x ∈ acc ∨ ∃ p ∈ l, x ∈ f p
  | [], _, _, h => .inl h
  | p :: l, acc, x, h => by
    rcases foldl_arr_mem f l _ x h with h | ⟨q, hq, h⟩
    · rcases Array.mem_append.1 h with h | h
      · exact .inl h
      · exact .inr ⟨p, by simp, h⟩
    · exact .inr ⟨q, by simp [hq], h⟩

/-- What `moveFoR` claims: every part but the last fills its blocks, every part is in the writer's form with no
    patch list, the pack is the packs end to end, and the metadata is `foRMeta` of the parts' blocks in turn. -/
theorem moveFoR_list {l : List ((USize × ByteArray) × ByteArray)} {M P : ByteArray}
    (h : moveFoR l.toArray = some (M, P)) :
    (∀ q ∈ l.dropLast, q.1.1.toNat % Column.blk = 0) ∧
    (∀ q ∈ l, Coc.foRStd q.1.1 q.1.2 q.2 = true ∧ q.2.size ≤ Column.blockStart q.1.2 (Column.nblk q.1.2)) ∧
    P = concatBytes (l.map (·.2)).toArray ∧
    ∃ nul sumn, M = Coc.foRMeta nul sumn (l.foldl (fun a p => a ++ (Array.range (Column.nblk p.1.2)).map fun b =>
        (Column.baseAt p.1.2 b, Column.maxvAt p.1.2 b, Column.bsumAt p.1.2 b, Column.widthAt p.1.2 b)) #[]) := by
  unfold moveFoR at h
  split at h
  · cases h
  rename_i hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hM, hP⟩ := h
  simp only [List.foldl_toArray'] at hM
  simp at hc
  refine ⟨fun ⟨⟨a, b⟩, c⟩ hq => by simpa using hc.1 a b c hq,
    fun ⟨⟨a, b⟩, c⟩ hq => by have := hc.2 a b c hq; exact ⟨by simpa using this.1, by simpa using this.2⟩,
    by rw [← hP, List.map_toArray], _, _, hM.symm⟩

/-- **The moved join** lists every part's elements in turn: part `k`'s blocks follow the blocks before it, each
    block's base, width and residuals carried over (`foRMeta_reads`). `f` is `moveFoR`'s block table of a part. -/
theorem move_core (f : (USize × ByteArray) × ByteArray → Array (UInt64 × UInt64 × UInt64 × Nat))
    (hfs : ∀ p, (f p).size = Column.nblk p.1.2)
    (hfb : ∀ p b (hb : b < (f p).size), (f p)[b].1 = Column.baseAt p.1.2 b ∧ (f p)[b].2.2.2 = Column.widthAt p.1.2 b)
    {l : List ((USize × ByteArray) × ByteArray)} (hz : ∀ q ∈ l.dropLast, q.1.1.toNat % Column.blk = 0)
    (hs : ∀ q ∈ l, Coc.foRStd q.1.1 q.1.2 q.2 = true ∧ q.2.size ≤ Column.blockStart q.1.2 (Column.nblk q.1.2))
    (nul : UInt64) (sumn : Nat) :
    (List.range (l.map (·.1.1.toNat)).sum).map (fun i => Column.foRBits
      (Coc.foRMeta nul sumn (l.foldl (fun a p => a ++ f p) #[])) (concatBytes (l.map (·.2)).toArray)
      (Column.blockStarts (Coc.foRMeta nul sumn (l.foldl (fun a p => a ++ f p) #[]))) i) =
      (l.map fun q => (List.range q.1.1.toNat).map (Column.foRBits q.1.2 q.2 (Column.blockStarts q.1.2))).flatten := by
  generalize hT : l.foldl (fun a p => a ++ f p) #[] = T
  generalize hP : concatBytes (l.map (·.2)).toArray = P
  have hwT : ∀ c (hc : c < T.size), T[c].2.2.2 < 256 := by
    intro c hc
    rcases foldl_arr_mem f l #[] _ (by rw [hT]; exact Array.getElem_mem hc) with h | ⟨p, hp, hm⟩
    · simp at h
    · obtain ⟨b, hb, he⟩ := Array.mem_iff_getElem.1 hm
      rw [← he, (hfb p b hb).2]
      exact Nat.lt_of_le_of_lt ((Verify.foRStd_iff.1 (hs p hp).1).width b (by rw [← hfs p]; exact hb)) (by decide)
  obtain ⟨hnb, hRb⟩ := Verify.foRMeta_reads nul sumn T hwT
  generalize Coc.foRMeta nul sumn T = M at hnb hRb ⊢
  have hTB : ∀ k (hk : k < l.length) b, b < Column.nblk l[k].1.2 →
      Column.baseAt M (((l.take k).map fun p => Column.nblk p.1.2).sum + b) = Column.baseAt l[k].1.2 b ∧
      Column.widthAt M (((l.take k).map fun p => Column.nblk p.1.2).sum + b) = Column.widthAt l[k].1.2 b := by
    intro k hk b hb
    have hb' : b < (f l[k]).size := by rw [hfs]; exact hb
    have hg := foldl_arr_get f l #[] hk hb'
    rw [hT, Array.size_empty, Nat.zero_add, Array.getElem?_eq_getElem hb'] at hg
    simp only [hfs] at hg
    obtain ⟨hlt, he⟩ := Array.getElem?_eq_some_iff.1 hg
    obtain ⟨h1, h2⟩ := hfb l[k] b (by rw [hfs]; exact hb)
    exact ⟨by rw [(hRb _ hlt).1, he, h1], by rw [(hRb _ hlt).2, he, h2]⟩
  have he : ∀ q ∈ l, q.2.size = Column.blockStart q.1.2 (Column.nblk q.1.2) := fun q hq => by
    have z := (hs q hq).2
    rcases (Verify.foRStd_iff.1 (hs q hq).1).size with h | h
    · exact h
    · cases hT' : Coc.foRTail (Column.nblk q.1.2) q.2 (Column.blockStart q.1.2 (Column.nblk q.1.2)) <;>
        simp [hT'] at h <;> omega
  have hBS0 : ∀ k, k ≤ l.length → Column.blockStart M (((l.take k).map fun p => Column.nblk p.1.2).sum) =
      ((l.take k).map fun q => q.2.size).sum := by
    intro k; induction k with
    | zero => intro _; simp [Column.blockStart]
    | succ k ih =>
      intro hk
      rw [List.take_succ_eq_append_getElem (by omega), List.map_append, List.map_append, List.sum_append_nat,
        List.sum_append_nat]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      have hk' : k < l.length := by omega
      rw [blockStart_shift (M := M) (m := l[k].1.2) _ (Column.nblk l[k].1.2) (fun c hc => (hTB k hk' c hc).2),
        ih (by omega), he _ (List.getElem_mem hk')]
  have hBS : ∀ k (hk : k < l.length) b, b ≤ Column.nblk l[k].1.2 →
      Column.blockStart M (((l.take k).map fun p => Column.nblk p.1.2).sum + b) =
        ((l.take k).map fun q => q.2.size).sum + Column.blockStart l[k].1.2 b := fun k hk b hb => by
    rw [blockStart_shift (M := M) (m := l[k].1.2) _ b (fun c hc => (hTB k hk c (by omega)).2), hBS0 k (by omega)]
  have hba : ∀ (B : ByteArray) (x : Nat), B[x]? = B.data[x]? := fun B x => by
    by_cases h : x < B.size
    · rw [getElem?_pos B x h, getElem?_pos B.data x h]; rfl
    · rw [getElem?_neg B x h, getElem?_neg B.data x h]
  have hPk : ∀ k (hk : k < l.length) x, x < l[k].2.size →
      P[((l.take k).map fun q => q.2.size).sum + x]? = l[k].2[x]? := by
    intro k hk x hx
    have := foldl_append_get (l.map (·.2)) .empty (k := k) (by simpa using hk) (j := x) (by simpa using hx)
    rw [← hP, hba, hba]
    simp only [concatBytes, List.foldl_toArray']
    simpa [← List.map_take] using this
  have hPs : P.size ≤ Column.blockStart M (Column.nblk M) := by
    have h1 := hBS0 l.length (Nat.le_refl _)
    rw [List.take_of_length_le (Nat.le_refl _)] at h1
    rw [hnb, ← hT, foldl_arr_size, Array.size_empty, Nat.zero_add]
    simp only [hfs]
    rw [h1, ← hP, concatBytes_size]; simp [Function.comp_def]
  have hfull : ∀ k (hk : k + 1 < l.length), l[k].1.1.toNat = Column.blk * Column.nblk l[k].1.2 := by
    intro k hk
    have hk0 : k < l.length := by omega
    have hm := List.getElem_mem (l := l.dropLast) (by simp; omega : k < l.dropLast.length)
    rw [List.getElem_dropLast] at hm
    have hz' := hz _ hm
    have w := (Verify.foRStd_iff.1 (hs _ (List.getElem_mem hk0)).1).nblk
    rw [w]; unfold Column.blk at *; omega
  have hO : ∀ k, k < l.length → ((l.take k).map (·.1.1.toNat)).sum =
      Column.blk * ((l.take k).map fun p => Column.nblk p.1.2).sum := by
    intro k; induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [List.take_succ_eq_append_getElem (by omega), List.map_append, List.map_append, List.sum_append_nat,
        List.sum_append_nat, ih (by omega)]
      simp [Nat.mul_add, hfull k hk]
  refine range_map_flatten (·.1.1.toNat) (fun q => Column.foRBits q.1.2 q.2 (Column.blockStarts q.1.2)) _ l
    fun k hk i hi => ?_
  dsimp only at hi ⊢
  have hq := hs _ (List.getElem_mem hk)
  have w := Verify.foRStd_iff.1 hq.1
  have hib : i / Column.blk < Column.nblk l[k].1.2 := by have := w.nblk; unfold Column.blk at *; omega
  rw [hO k hk, foRBits_plain hPs, foRBits_plain hq.2]
  have hd : (Column.blk * ((l.take k).map fun p => Column.nblk p.1.2).sum + i) / Column.blk =
      ((l.take k).map fun p => Column.nblk p.1.2).sum + i / Column.blk := by unfold Column.blk; omega
  have hr : (Column.blk * ((l.take k).map fun p => Column.nblk p.1.2).sum + i) % Column.blk = i % Column.blk := by
    unfold Column.blk; omega
  rw [hd, hr, (hTB k hk _ hib).1, (hTB k hk _ hib).2, hBS k hk _ (Nat.le_of_lt hib)]
  congr 1
  apply resAt_congr; intro x hx
  have hr := resAt_reach (w := Column.widthAt l[k].1.2 (i / Column.blk)) (Nat.mod_lt i (by unfold Column.blk; decide))
  have hle := blockStart_mono l[k].1.2 (Nat.succ_le_of_lt hib)
  rw [blockStart_succ] at hle
  rw [Nat.add_assoc, hPk k hk _ (by rw [he _ (List.getElem_mem hk)]; omega)]

theorem move_list {l : List ((USize × ByteArray) × ByteArray)} {M P : ByteArray}
    (h : moveFoR l.toArray = some (M, P)) :
    (List.range (l.map (·.1.1.toNat)).sum).map (fun i => Column.foRBits M P (Column.blockStarts M) i) =
      (l.map fun q => (List.range q.1.1.toNat).map (Column.foRBits q.1.2 q.2 (Column.blockStarts q.1.2))).flatten := by
  obtain ⟨hz, hs, rfl, nul, sumn, rfl⟩ := moveFoR_list h
  exact move_core _ (fun p => by simp) (fun p b hb => by simp) hz hs nul sumn

/-- The `w`-byte elements of the parts' decodes end to end are each part's elements cut to `8w` bits. -/
theorem elemsW_decodes {w : Nat} (hw0 : 0 < w) (hw8 : w ≤ 8) (l : List ((USize × ByteArray) × ByteArray)) :
    Verify.elemsW w (concatBytes (l.map fun p => Coc.decode w.toUSize p.1.2 p.2 p.1.1).toArray) =
      (l.map fun p => (List.range p.1.1.toNat).map fun i =>
        UInt64.ofNat ((Column.foRBits p.1.2 p.2 (Column.blockStarts p.1.2) i).toNat % 2 ^ (8 * w))).flatten := by
  have hwu := toUSize_toNat_le8 hw8
  have hdw := fun (p : (USize × ByteArray) × ByteArray) =>
    Verify.decodeW w.toUSize (by rw [hwu]; exact hw8) p.1.2 p.2 p.1.1
  simp only [concatBytes, List.foldl_toArray']
  rw [Verify.elemsW_foldl_append w hw0 _ .empty rfl (fun b hb => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hb
    rw [(hdw p).1, hwu]; simp)]
  simp only [Verify.elemsW, ByteArray.size_empty, Nat.zero_div, List.range_zero, List.map_nil, List.nil_append,
    List.map_map]
  congr 1; apply List.map_congr_left; intro p _
  have := (hdw p).2
  rw [hwu] at this
  simp only [Function.comp_apply]
  rw [Verify.elemsW, (hdw p).1, hwu, Nat.mul_div_cancel_left _ hw0]
  exact List.map_congr_left fun i hi => this i (List.mem_range.1 hi)

/-- **The appended join** lists the first part's elements, then each later part's (`append_reads`). -/
theorem append_list {w : Nat} (hw8 : w ≤ 8) {q : (USize × ByteArray) × ByteArray}
    {l : List ((USize × ByteArray) × ByteArray)} {M P : ByteArray}
    (h : appendFoR q.1.1 q.1.2 q.2 (concatBytes (l.map fun p => Coc.decode (8 : Nat).toUSize p.1.2 p.2 p.1.1).toArray) =
      some (M, P)) :
    (List.range ((q :: l).map (·.1.1.toNat)).sum).map
        (fun i => (Column.foRBits M P (Column.blockStarts M) i).toNat % 2 ^ (8 * w)) =
      ((q :: l).map fun p => (List.range p.1.1.toNat).map fun i =>
        (Column.foRBits p.1.2 p.2 (Column.blockStarts p.1.2) i).toNat % 2 ^ (8 * w)).flatten := by
  have hE := elemsW_decodes (by decide) (Nat.le_refl 8) l
  generalize concatBytes (l.map fun p => Coc.decode (8 : Nat).toUSize p.1.2 p.2 p.1.1).toArray = D at h hE
  have hlen : D.size / 8 = (l.map (·.1.1.toNat)).sum := by
    simpa [Verify.elemsW, List.length_flatten, Function.comp_def] using congrArg List.length hE
  rw [List.map_cons, List.sum_cons, List.range_add, List.map_append, List.map_cons, List.flatten_cons, List.map_map]
  congr 1
  · apply List.map_congr_left; intro i hi
    have hi' := List.mem_range.1 hi
    rw [append_reads h hlen (by omega), if_pos hi']
  · have h2 : (List.range (l.map (·.1.1.toNat)).sum).map
        ((fun i => (Column.foRBits M P (Column.blockStarts M) i).toNat % 2 ^ (8 * w)) ∘ (q.1.1.toNat + ·)) =
        (Verify.elemsW 8 D).map fun v => v.toNat % 2 ^ (8 * w) := by
      rw [Verify.elemsW, List.map_map, hlen]; apply List.map_congr_left; intro j hj
      have hj' := List.mem_range.1 hj
      simp only [Function.comp_apply]
      rw [append_reads h hlen (by omega), if_neg (by omega), Nat.add_sub_cancel_left]
    rw [h2, hE, List.map_flatten, List.map_map]
    congr 1; apply List.map_congr_left; intro p _
    simp only [Function.comp_apply, List.map_map]; apply List.map_congr_left; intro i _
    simp only [Function.comp_apply, ofNat_mod_toNat (Nat.le_refl 8)]
    exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))

/-- **The re-encoded join** lists the parts' elements in turn: `Coc.encode` reads back the joined decodes
    (`foRBits_encode_bits`), and each decode is its part's elements cut to `8w` bits (`elemsW_decodes`). -/
theorem reencode_list {w : Nat} (hw1 : 1 < w) (hw8 : w ≤ 8) (l : List ((USize × ByteArray) × ByteArray))
    {M P : ByteArray}
    (hX : Coc.encode w.toUSize (concatBytes (l.map fun p => Coc.decode w.toUSize p.1.2 p.2 p.1.1).toArray) = (M, P)) :
    (List.range (l.map (·.1.1.toNat)).sum).map
        (fun i => (Column.foRBits M P (Column.blockStarts M) i).toNat % 2 ^ (8 * w)) =
      (l.map fun p => (List.range p.1.1.toNat).map fun i =>
        (Column.foRBits p.1.2 p.2 (Column.blockStarts p.1.2) i).toNat % 2 ^ (8 * w)).flatten := by
  have hw0 : 0 < w := by omega
  have hE := elemsW_decodes hw0 hw8 l
  generalize concatBytes (l.map fun p => Coc.decode w.toUSize p.1.2 p.2 p.1.1).toArray = X at hX hE
  have hlen : X.size / w = (l.map (·.1.1.toNat)).sum := by
    simpa [Verify.elemsW, List.length_flatten, Function.comp_def] using congrArg List.length hE
  have hR : ∀ i < X.size / w, (Column.foRBits M P (Column.blockStarts M) i).toNat % 2 ^ (8 * w) =
      (Column.bitsAt X (i * w) w).toNat := by
    intro i hi; have := Verify.foRBits_encode_bits w hw1 hw8 X i hi; simp only [hX] at this; exact this
  have h2 : (List.range (X.size / w)).map (fun i => (Column.foRBits M P (Column.blockStarts M) i).toNat % 2 ^ (8 * w)) =
      (Verify.elemsW w X).map (·.toNat) := by
    rw [Verify.elemsW, List.map_map]
    exact List.map_congr_left fun i hi => by simp only [Function.comp_apply, hR i (List.mem_range.1 hi)]
  rw [← hlen, h2, hE, List.map_flatten, List.map_map]
  congr 1; apply List.map_congr_left; intro p _
  simp only [Function.comp_apply, List.map_map]; apply List.map_congr_left; intro i _
  simp only [Function.comp_apply, ofNat_mod_toNat hw8]

/-- **`concatFoR` read back at any number of parts**, on each of its three answers: the parts' elements one part
    after another, to their low `8w` bits. -/
theorem concatFoR_reads {w : Nat} (hw1 : 1 < w) (hw8 : w ≤ 8) (q : (USize × ByteArray) × ByteArray)
    (r : List ((USize × ByteArray) × ByteArray)) {M P : ByteArray}
    (hX : concatFoR w.toUSize (countBytes ((q :: r).map (·.1.1)).toArray) ((q :: r).map (·.1.2)).toArray
      ((q :: r).map (·.2)).toArray = (M, P)) :
    (List.range ((q :: r).map (·.1.1.toNat)).sum).map
        (fun i => (Column.foRBits M P (Column.blockStarts M) i).toNat % 2 ^ (8 * w)) =
      ((q :: r).map fun p => (List.range p.1.1.toNat).map fun i =>
        (Column.foRBits p.1.2 p.2 (Column.blockStarts p.1.2) i).toNat % 2 ^ (8 * w)).flatten := by
  have hps : (Array.range (min ((countBytes ((q :: r).map (·.1.1)).toArray).size / 8)
      (min ((q :: r).map (·.1.2)).toArray.size ((q :: r).map (·.2)).toArray.size))).map (fun k =>
        (((Column.bitsAt (countBytes ((q :: r).map (·.1.1)).toArray) (8 * k) 8).toUSize,
          ((q :: r).map (·.1.2)).toArray[k]!), ((q :: r).map (·.2)).toArray[k]!)) = (q :: r).toArray := by
    generalize q :: r = l
    apply Array.ext (by simp [countBytes_size])
    intro k h1 h2
    have hk : k < l.length := by simpa using h2
    simp only [Array.getElem_map, Array.getElem_range]
    rw [countBytes_get _ k (by simpa using hk)]
    simp [getElem!_def, List.getElem?_map, List.getElem?_eq_getElem hk]
  unfold concatFoR at hX
  simp only [hps] at hX
  split at hX
  · rename_i out hm
    subst hX
    have := congrArg (List.map fun v : UInt64 => v.toNat % 2 ^ (8 * w)) (move_list hm)
    simpa only [List.map_map, List.map_flatten, Function.comp_def] using this
  · have h0 : (q :: r).toArray[0]! = q := rfl
    have hx : ((q :: r).toArray.extract 1 (q :: r).toArray.size) = r.toArray := by simp
    simp only [h0, hx, List.map_toArray] at hX
    split at hX
    · rename_i out ha
      subst hX
      exact append_list hw8 ha
    · exact reencode_list hw1 hw8 _ hX

end LeetQ.Rel.KernelWF
