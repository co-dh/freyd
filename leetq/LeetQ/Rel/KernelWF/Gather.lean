/-
  Totality of the kernels a `Rel` op reads a payload through, under the payload's `Enc.WF`: the facts
  that let `pick`, `longBytes` and `gens` drop their `Except`. Each hypothesis is one a
  caller holding an `Arr` already has: `x.wf`, an index `.bytes i` of `i.size / 8` longs.
-/
import QLean.Kernel.Structural
import QLean.Verify.Gather
import QLean.Verify.Raw
import QLean.Verify.Alp
import LeetQ.Rel.KernelWF.Raze

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Verify

/-- A `long` payload is dense bytes or Frame of Reference: `WF` admits no other layout at `long`. -/
theorem long_cases {n : USize} {e : Enc} (hw : Enc.WF .long n e) :
    (∃ b, e = .bytes b) ∨ ∃ M P, e = .foR M P := by
  cases e <;> simp_all [Enc.WF, QAtomicType.width]

/-- A general list's payload is a `gen` column of its `n` elements. -/
theorem general_cases {n : USize} {e : Enc} (hw : Enc.WF .general n e) :
    ∃ xs, e = .gen xs ∧ xs.size = n.toNat := by
  cases e <;> simp_all [Enc.WF, QAtomicType.width]

/-- **`x@i` answers** for every well-formed column but a general list, and every dense index of at
    least `m` longs. -/
theorem gatherColumn_isSome {t : QAtomicType} {n : USize} {e : Enc} (hw : Enc.WF t n e) (hg : t ≠ .general)
    {m : USize} (i : ByteArray) (hm : m.toNat * 8 ≤ i.size) : (gatherColumn t n e m (.bytes i)).isSome := by
  have hz : ¬ i.size < m.toNat * 8 := by omega
  unfold gatherColumn
  cases e <;> cases t <;>
    simp_all [-Nat.not_lt, Enc.WF, QAtomicType.width, denseWidth, rowWidth, foRColumn, Enc.bytesOf,
      Column.alpEncodes] <;> split <;> simp_all [-Nat.not_lt]

/-! ## The answer's size: what `Enc.WF` asks of each gather's payload -/

theorem gatherBits_size (n : USize) (b ix : ByteArray) : (gatherBits n b ix).size = (ix.size / 8 + 7) / 8 :=
  packOf_size ..

/-- `gatherBytes` writes `w` bytes an index element, hit or miss. -/
theorem gatherBytes_size (w : USize) (fill : UInt64) (src ix : ByteArray) :
    (gatherBytes w fill src ix).size = ix.size / 8 * w.toNat := by
  unfold gatherBytes
  rw [foldl_size ByteArray.size _ w.toNat, List.length_range]; · simp
  intro a j
  split
  · rename_i i hi
    have hlt : i < src.size / w.toNat := by
      unfold gatherAt at hi; dsimp only at hi; split at hi
      · cases hi; assumption
      · cases hi
    have hle : (i + 1) * w.toNat ≤ src.size := Nat.le_trans (Nat.mul_le_mul_right _ hlt) (Nat.div_mul_le_self _ _)
    rw [Nat.succ_mul] at hle
    split
    · exact Column.pushBits_size ..
    · simp only [ByteArray.size_append, ByteArray.size_extract]; omega
  · exact Column.pushBits_size ..

/-- A fold that pushes one offset a step pushes one per element. -/
theorem foldl_snd_size {α β γ : Type} (f : α × Array β → γ → α × Array β) (hf : ∀ p j, (f p j).2.size = p.2.size + 1)
    (l : List γ) (p : α × Array β) : (l.foldl f p).2.size = p.2.size + l.length := by
  induction l generalizing p with
  | nil => simp
  | cons j l ih => simp only [List.foldl, ih, hf, List.length_cons]; omega

theorem gatherSyms_size (blob : ByteArray) (offs : Array Nat) (ix : ByteArray) :
    (gatherSyms blob offs ix).2.size = ix.size / 8 + 1 := by
  unfold gatherSyms
  rw [foldl_snd_size _ (fun p j => by cases p; simp)]; simp; omega

/-- One symbol and its NUL appended, its end pushed as the last start: `gatherSyms`' step. -/
theorem symsWF_pushSym {b k : ByteArray} {o : Array Nat} (h : SymsWF b o) :
    SymsWF ((b ++ k).push 0) (o.push (b.size + k.size + 1)) := by
  have hs : ((b ++ k).push 0).size = b.size + k.size + 1 := by
    rw [show ((b ++ k).push 0).size = (b ++ k).size + 1 by simp only [ByteArray.size, ByteArray.push, Array.size_push],
      ByteArray.size_append]
  have := symsWF_push (b' := (b ++ k).push 0) h (by omega)
  rwa [hs] at this

theorem symsWF_empty : SymsWF ByteArray.empty #[0] := by decide

/-- A fold whose every step keeps the `syms` layout keeps it. -/
theorem symsWF_foldl {γ : Type} (f : ByteArray × Array Nat → γ → ByteArray × Array Nat)
    (hf : ∀ q j, SymsWF q.1 q.2 → SymsWF (f q j).1 (f q j).2) (l : List γ) :
    ∀ p : ByteArray × Array Nat, SymsWF p.1 p.2 → SymsWF (l.foldl f p).1 (l.foldl f p).2 := by
  induction l with
  | nil => exact fun _ h => h
  | cons j l ih => exact fun p h => ih _ (hf p j h)

/-- `gatherSyms` lays its answer out as `SymsWF` says, whatever the source. -/
theorem gatherSyms_wf (blob : ByteArray) (offs : Array Nat) (ix : ByteArray) :
    SymsWF (gatherSyms blob offs ix).1 (gatherSyms blob offs ix).2 := by
  unfold gatherSyms
  dsimp only
  exact symsWF_foldl _ (fun q j hq => by obtain ⟨b, o⟩ := q; exact symsWF_pushSym hq) _ _ symsWF_empty

/-- One symbol `k` and its NUL appended, its end pushed as the last start, keeps every entry valid where `k` is. -/
theorem pushSym_utf8 {b k : ByteArray} {o : Array Nat} (hw : SymsWF b o)
    (hu : ∀ t < o.size - 1, ∃ c : ByteArray, c.IsValidUTF8 ∧ (Verify.symBytes b o t).dropLast = c.data.toList)
    (hk : k.IsValidUTF8) :
    SymsWF ((b ++ k).push 0) (o.push (b.size + k.size + 1)) ∧ ∀ t < (o.push (b.size + k.size + 1)).size - 1,
      ∃ c : ByteArray, c.IsValidUTF8 ∧
        (Verify.symBytes ((b ++ k).push 0) (o.push (b.size + k.size + 1)) t).dropLast = c.data.toList := by
  have hs : ((b ++ k).push 0).size = b.size + k.size + 1 := by
    rw [show ((b ++ k).push 0).size = (b ++ k).size + 1 by simp only [ByteArray.size, ByteArray.push, Array.size_push],
      ByteArray.size_append]
  rw [← hs]
  exact utf8_push hw hu (Verify.append_push_toList b k) ⟨k, hk, List.dropLast_concat ..⟩

/-- `gatherSyms` copies the source's entry `i` for a hit and writes the empty symbol for a miss, so its answer
    holds only valid UTF-8 where the source does. -/
theorem gatherSyms_utf8 (blob : ByteArray) (offs : Array Nat) (ix : ByteArray) (hw : SymsWF blob offs)
    (hu : ∀ i < offs.size - 1, (Column.symKey blob offs i).IsValidUTF8) :
    ∀ j < (gatherSyms blob offs ix).2.size - 1,
      (Column.symKey (gatherSyms blob offs ix).1 (gatherSyms blob offs ix).2 j).IsValidUTF8 := by
  -- a hit's bytes, up to the byte before the next start, are the entry without its NUL
  have hkey : ∀ i, (blob.extract offs[i]! (offs[i + 1]! - 1)).data.toList = Verify.symAt blob offs i := fun i => by
    unfold Verify.symAt Column.symKey Column.symBytes
    simp only [Verify.extract_toList]
    congr 1; split <;> omega
  unfold gatherSyms
  dsimp only
  generalize hr : List.foldl _ (ByteArray.empty, #[0]) (List.range (ix.size / 8)) = r
  have H : SymsWF r.1 r.2 ∧ ∀ t < r.2.size - 1,
      ∃ c : ByteArray, c.IsValidUTF8 ∧ (Verify.symBytes r.1 r.2 t).dropLast = c.data.toList :=
    hr ▸ foldl_inv (fun p : ByteArray × Array Nat => SymsWF p.1 p.2 ∧ ∀ t < p.2.size - 1,
        ∃ c : ByteArray, c.IsValidUTF8 ∧ (Verify.symBytes p.1 p.2 t).dropLast = c.data.toList) _ (fun q j hq => by
      obtain ⟨b, o⟩ := q
      refine pushSym_utf8 hq.1 hq.2 ?_
      split
      · rename_i i hi
        have hlt : i < offs.size - 1 := by
          unfold gatherAt at hi; dsimp only at hi; split at hi
          · cases hi; assumption
          · cases hi
        exact utf8_congr (hkey i) (hu i hlt)
      · decide) _ _ ⟨by decide, fun t ht => by simp at ht⟩
  exact fun j hj => utf8_of_inv H.1 hj (H.2 j hj)

/-- An interned gather's dictionary holds only valid UTF-8 where the source's does: the empty symbol it may append
    is valid. -/
theorem gatherIds_utf8 {dict : ByteArray} {dof : Array Nat} {inRange : Unit → Bool}
    {g : USize → USize → UInt64 → ByteArray} (hd : SymsWF dict dof)
    (hu : ∀ i < dof.size - 1, (Column.symKey dict dof i).IsValidUTF8) :
    ∀ j < (gatherIds dict dof inRange g).2.1.size - 1,
      (Column.symKey (gatherIds dict dof inRange g).1 (gatherIds dict dof inRange g).2.1 j).IsValidUTF8 := by
  unfold gatherIds
  dsimp only
  split
  · exact hu
  · have hp : (dict.push 0).size = dict.size + 1 := by simp only [ByteArray.size, ByteArray.push, Array.size_push]
    have H := utf8_push (b' := dict.push 0) (s := [0]) hd (fun t ht => inv_of_utf8 hd ht (hu t ht))
      (Array.toList_push ..) ⟨ByteArray.empty, by decide, rfl⟩
    rw [hp] at H
    exact fun j hj => utf8_of_inv H.1 hj (H.2 j hj)

/-- An interned gather's ids are its answer's `m` elements packed at the answer dictionary's width, in exactly
    `⌈m·w/8⌉` bytes. -/
theorem gatherIds_wf {dict : ByteArray} {dof : Array Nat} {inRange : Unit → Bool} {n : USize} {ids ix : ByteArray}
    {db : ByteArray} {dbo : Array Nat} {nids : ByteArray}
    (hG : (gatherIds dict dof inRange fun w wo e => gatherPacked n w wo e ids ix) = (db, dbo, nids)) :
    nids.size = (ix.size / 8 * Column.idWidth dbo + 7) / 8 := by
  suffices key : (gatherIds dict dof inRange fun w wo e => gatherPacked n w wo e ids ix).2.2.size =
      (ix.size / 8 * Column.idWidth (gatherIds dict dof inRange fun w wo e => gatherPacked n w wo e ids ix).2.1 + 7) / 8
    by rw [hG] at key; exact key
  have hl := fun o : Array Nat => Verify.laneWidth_cases (Column.widthFor (o.size - 1 - 1))
  have hU : ∀ o : Array Nat, (Column.idWidth o).toUSize.toNat = Column.idWidth o := fun o =>
    USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by rcases hl o with h | h | h | h | h | h | h | h <;>
      simp only [Column.idWidth, Column.idWidthOf, h] <;> decide) USize.le_size)
  simp only [gatherIds, gatherPacked]
  split <;> (rw [hU]; exact packIds_size (hl _) _ _)

/-- An interned gather's dictionary is laid out as `SymsWF` says where the source's is: the empty symbol it
    may append is one NUL past the old end. -/
theorem gatherIds_dict {dict : ByteArray} {dof : Array Nat} {inRange : Unit → Bool}
    {g : USize → USize → UInt64 → ByteArray} (hd : SymsWF dict dof) :
    SymsWF (gatherIds dict dof inRange g).1 (gatherIds dict dof inRange g).2.1 := by
  unfold gatherIds
  dsimp only
  split
  · exact hd
  · have hp : (dict.push 0).size = dict.size + 1 := by simp only [ByteArray.size, ByteArray.push, Array.size_push]
    have := symsWF_push (b' := dict.push 0) hd (by omega)
    rwa [hp] at this

/-- An interned gather's dictionary holds no symbol twice where the source's does not: the empty symbol is
    appended only where `findSymScalar` does not find it, and appending it leaves every entry as it was. -/
theorem gatherIds_nodup {dict : ByteArray} {dof : Array Nat} {inRange : Unit → Bool}
    {g : USize → USize → UInt64 → ByteArray} (hd : SymsWF dict dof)
    (hn : ((List.range (dof.size - 1)).map (Verify.symAt dict dof)).Nodup) :
    ((List.range ((gatherIds dict dof inRange g).2.1.size - 1)).map
      (Verify.symAt (gatherIds dict dof inRange g).1 (gatherIds dict dof inRange g).2.1)).Nodup := by
  unfold gatherIds
  dsimp only
  split
  · exact hn
  · rename_i hc
    have hlt : ¬ (findSymScalar dict dof ByteArray.empty).toNat < dof.size - 1 := fun h => hc (by simp [h])
    have habs : ∀ j < dof.size - 1, Verify.symAt dict dof j ≠ [] := by
      intro j hj he
      apply hlt
      unfold findSymScalar
      dsimp only
      cases hf : (List.range (dof.size - 1)).find? (fun i => (Column.symKey dict dof i).data == ByteArray.empty.data) with
      | none =>
        exfalso
        refine List.find?_eq_none.1 hf j (List.mem_range.2 hj) ((Verify.arr_beq_iff _ _).2 ?_)
        exact Array.toList_inj.1 he
      | some j' =>
        have := List.mem_range.1 (List.mem_of_find?_eq_some hf)
        rw [Option.getD_some]
        exact Nat.lt_of_le_of_lt (by rw [show j'.toUSize = USize.ofNat j' from rfl, USize.toNat_ofNat']; exact Nat.mod_le _ _) this
    have hpz : (dict.push 0).size = dict.size + 1 := by simp only [ByteArray.size, ByteArray.push, Array.size_push]
    have hpos := hd.pos
    obtain ⟨g1, g2, g3, g4, g5⟩ := Verify.symBytes_push dict (dict.push 0) dof (dof.size - 1) [0] (by omega)
      hd.last (fun t ht => hd.le t (by omega)) (Array.toList_push ..)
    rw [hpz] at g1 g2 g3 g4 g5
    have hold : ∀ t < dof.size - 1, Verify.symAt (dict.push 0) (dof.push (dict.size + 1)) t = Verify.symAt dict dof t :=
      fun t ht => by
        rw [Verify.symAt_eq_dropLast _ _ _ (by rw [hpz]; exact g3 (t + 1) (by omega)), g5 t ht,
          ← Verify.symAt_eq_dropLast _ _ _ (hd.le (t + 1) (by omega))]
    have hnew : Verify.symAt (dict.push 0) (dof.push (dict.size + 1)) (dof.size - 1) = [] := by
      rw [Verify.symAt_eq_dropLast _ _ _ (by rw [hpz, g2]; exact Nat.le_refl _), g4]; rfl
    have hs : (dof.push (dict.size + 1)).size - 1 = (dof.size - 1) + 1 := by simp only [Array.size_push]; omega
    rw [hs, List.range_succ, List.map_append, List.map_singleton, hnew,
      List.map_congr_left (fun t ht => hold t (List.mem_range.1 ht))]
    refine List.pairwise_append.2 ⟨hn, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha
    rw [List.mem_singleton.1 hb]
    exact habs t (List.mem_range.1 ht)

/-- `findSymScalar` answers an entry below the count, or the count where it finds none. -/
theorem findSymScalar_le (dict : ByteArray) (dof : Array Nat) (k : ByteArray) :
    (findSymScalar dict dof k).toNat ≤ dof.size - 1 := by
  unfold findSymScalar
  dsimp only
  cases hf : (List.range (dof.size - 1)).find? (fun i => (Column.symKey dict dof i).data == k.data) with
  | none =>
    rw [Option.getD_none, show (dof.size - 1).toUSize = USize.ofNat (dof.size - 1) from rfl, USize.toNat_ofNat']
    exact Nat.mod_le _ _
  | some j =>
    have := List.mem_range.1 (List.mem_of_find?_eq_some hf)
    rw [Option.getD_some, show j.toUSize = USize.ofNat j from rfl, USize.toNat_ofNat']
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.le_of_lt this)

/-- A `Nat.all` that holds holds at every index. -/
theorem nat_all_true {N : Nat} {f : (i : Nat) → i < N → Bool} (h : Nat.all N f = true) :
    ∀ k (hk : k < N), f k hk = true := by
  induction N with
  | zero => intro k hk; omega
  | succ N ih =>
    rw [Nat.all_succ, Bool.and_eq_true] at h
    intro k hk
    by_cases hkN : k < N
    · exact ih (f := fun i h => f i (by omega)) h.1 k hkN
    · obtain rfl : k = N := by omega
      exact h.2

/-- **An interned gather's ids name entries of its dictionary**, where the source's ids do and an index that
    `inRange` passes misses nowhere: a hit is a source id, a miss the empty symbol, found or appended. -/
theorem gatherIds_lt {dict : ByteArray} {dof : Array Nat} {inRange : Unit → Bool} {n : USize} {ids ix : ByteArray}
    (hpos : 0 < dof.size) (hsrc : ∀ k < n.toNat, Column.idAt ids (Column.idWidth dof) k < dof.size - 1)
    (hin : inRange () = true → ∀ k < ix.size / 8, gatherAt n.toNat ix k ≠ none) :
    ∀ j < ix.size / 8,
      Column.idAt (gatherIds dict dof inRange fun w wo e => gatherPacked n w wo e ids ix).2.2
        (Column.idWidth (gatherIds dict dof inRange fun w wo e => gatherPacked n w wo e ids ix).2.1) j <
      (gatherIds dict dof inRange fun w wo e => gatherPacked n w wo e ids ix).2.1.size - 1 := by
  intro j hj
  have hW : ∀ o : Array Nat, Column.idWidth o ≤ 64 := fun o => by
    rcases Verify.laneWidth_cases (Column.widthFor (o.size - 1 - 1)) with h | h | h | h | h | h | h | h <;>
      simp only [Column.idWidth, Column.idWidthOf, h] <;> omega
  have hU : ∀ o : Array Nat, (Column.idWidth o).toUSize.toNat = Column.idWidth o := fun o =>
    USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (hW o) (by decide)) USize.le_size)
  have key : ∀ (o : Array Nat) (f : Nat → Nat), (∀ k < ix.size / 8, f k < o.size - 1) → (∀ k, f k < 2 ^ 64) →
      Column.idAt (Column.packIds (Column.idWidth o) (ix.size / 8) f) (Column.idWidth o) j < o.size - 1 := by
    intro o f hf h64
    have hl := lt_idWidthOf_64 (hf j hj) (h64 j)
    rw [Column.idWidth] at ⊢
    rw [Column.idWidthOf] at hl ⊢
    rw [Verify.idAt_packIds (Verify.laneWidth_cases _) hj hl]
    exact hf j hj
  have hit : ∀ k i, gatherAt n.toNat ix k = some i → i < n.toNat := fun k i h => by
    unfold gatherAt at h; dsimp only at h; split at h
    · cases h; assumption
    · cases h
  have hfill : ∀ x : Nat, x < 2 ^ 64 → x.toUInt64.toNat = x := fun x hx => by
    first
      | exact UInt64.toNat_ofNat_of_lt' hx
      | (simp only [Nat.toUInt64, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hx)
      | (simp [Nat.toUInt64]; omega)
  have he := findSymScalar_le dict dof ByteArray.empty
  have he64 := Verify.usize_lt (findSymScalar dict dof ByteArray.empty)
  have hsrc64 : ∀ i, Column.idAt ids (Column.idWidth dof) i < 2 ^ 64 := fun i =>
    Nat.lt_of_lt_of_le (Verify.idAt_lt _ _ _ (hW _)) (Nat.pow_le_pow_right (by decide) (hW _))
  simp only [gatherIds, gatherPacked]
  split
  · rename_i hc
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    simp only [hU]
    apply key
    · intro k hk
      dsimp only
      split
      · rename_i i hi; exact hsrc i (hit k i hi)
      · rename_i hmiss
        rw [hfill _ he64]
        rcases hc with hc | hc
        · exact hc
        · exact absurd hmiss (hin hc k hk)
    · intro k
      dsimp only
      split
      · exact hsrc64 _
      · rw [hfill _ he64]; exact he64
  · simp only [hU]
    apply key
    · intro k hk
      dsimp only
      rw [Array.size_push]
      split
      · rename_i i hi; exact Nat.lt_of_lt_of_le (hsrc i (hit k i hi)) (by omega)
      · rw [hfill _ he64]; omega
    · intro k
      dsimp only
      split
      · exact hsrc64 _
      · rw [hfill _ he64]; exact he64

theorem gatherAlp_size (fill : UInt64) (md pk a : ByteArray) (n : USize) (ix : ByteArray) :
    (gatherAlp fill md pk a n ix).size = ix.size / 8 * (if Column.alpF32 a then 4 else 8) := by
  unfold gatherAlp; rw [gatherBytes_size]; split <;> simp_all

theorem small_mod (k : Nat) (h : k ≤ 64) : k % 2 ^ System.Platform.numBits = k :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : k < 2 ^ 32)
    (Nat.pow_le_pow_right (by decide) (by rcases System.Platform.numBits_eq with h | h <;> simp [h])))

theorem toNat_small (k : Nat) (h : k ≤ 64) : (USize.ofNat k).toNat = k :=
  USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by omega) USize.le_size)

/-- **`x@i` answers `m` well-formed elements** of the source's type, for a dense index of `m` longs. -/
theorem gatherColumn_wf {t : QAtomicType} {n : USize} {e : Enc} (hw : Enc.WF t n e)
    (i : ByteArray) {m : USize} (hm : m.toNat = i.size / 8) {e' : Enc}
    (h : gatherColumn t n e m (.bytes i) = some e') : Enc.WF t m e' := by
  unfold gatherColumn at h
  have hz : ¬ i.size < m.toNat * 8 := by omega
  cases e with
  | foR M P =>
    by_cases hc : Column.encodes t = true ∧ M.isEmpty = false <;> cases t <;>
      simp_all [-Nat.not_lt, Enc.WF, QAtomicType.width, denseWidth, rowWidth, foRColumn, Enc.bytesOf,
        Column.encodes, gatherBytes_size, gatherFoR, toNat_small, small_mod] <;> obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := h <;>
      simp [gatherBytes_size, toNat_small, small_mod, hm]
  | enum d o ids =>
    cases t <;> try (exfalso; simp [Enc.WF] at hw; done)
    obtain ⟨-, hd, hi, hn, hu⟩ := id hw
    have key4 := gatherIds_utf8 (inRange := fun _ => allBelow n i)
      (g := fun w wo e => gatherPacked n w wo e ids i) hd hu
    have key := gatherIds_dict (inRange := fun _ => allBelow n i)
      (g := fun w wo e => gatherPacked n w wo e ids i) hd
    have key2 := gatherIds_nodup (inRange := fun _ => allBelow n i)
      (g := fun w wo e => gatherPacked n w wo e ids i) hd hn
    have key3 := gatherIds_lt (dict := d) (inRange := fun _ => allBelow n i) (ids := ids) (ix := i) hd.pos hi
      fun ha k hk => by
        simp only [allBelow] at ha
        have := nat_all_true ha k hk
        unfold gatherAt
        dsimp only
        rw [if_pos (of_decide_eq_true this)]
        exact Option.some_ne_none _
    have key3' : ∀ k < m.toNat, _ := fun k hk => key3 k (by omega)
    simp_all [-Nat.not_lt, Enc.WF, QAtomicType.width, foRColumn, Enc.bytesOf]
    split at h <;> cases h <;> simp only [Enc.WF] at *
    · exact ⟨by simp_all, symsWF_empty, fun j _ => utf8_congr (c := ByteArray.empty)
        (by simp [Column.symKey, Verify.extract_toList]) (by decide)⟩
    · exact ⟨gatherIds_wf (inRange := fun _ => allBelow n i) (n := n) (ids := ids)
        (db := (gatherIds d o (fun _ => allBelow n i) fun w wo e => gatherPacked n w wo e ids i).1) rfl, key,
        key3', key2, key4⟩
  | syms blob offs =>
    cases t <;> try (exfalso; simp [Enc.WF] at hw; done)
    obtain ⟨hs, hd, hu⟩ := id hw
    have hU := gatherSyms_utf8 blob offs i hd fun k hk => hu k (by omega)
    simp [-Nat.not_lt, hz, denseWidth, rowWidth, foRColumn, Enc.bytesOf, QAtomicType.width] at h
    subst h
    simp only [Enc.WF]
    exact ⟨by rw [gatherSyms_size]; omega, gatherSyms_wf .., fun j hj => hU j (by rw [gatherSyms_size]; omega)⟩
  | _ => cases t <;>
      simp_all [-Nat.not_lt, Enc.WF, QAtomicType.width, denseWidth, rowWidth, foRColumn, Enc.bytesOf,
        Column.alpEncodes, gatherBits_size, gatherBytes_size, gatherAlp_size, gatherSyms_size, gatherSyms_wf,
        gatherIds_wf, toNat_small, small_mod] <;> (try subst h) <;>
      simp_all [gatherBits_size, gatherBytes_size, gatherAlp_size, gatherSyms_size, gatherSyms_wf, gatherIds_wf,
        toNat_small, small_mod]

end LeetQ.Rel.KernelWF
