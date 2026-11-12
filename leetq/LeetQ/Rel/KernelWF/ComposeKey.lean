/-
  What `composeKey` CONTAINS: the chain it builds, read back stage by stage. First the program's stage
  count, for a build of any number of stages (qlean's `Verify.prog_one` is the build of none).
-/
import QLean.Verify.Chain

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify

/-- **A build's program holds its stages and the last one**: `Ew.chain` runs `stages.size + 1` stages. -/
theorem prog_count (b : Ew.Build) (last : Ew.Stage) :
    (b.prog last).size / Ew.stageBytes = b.stages.size + 1 := by
  have hL : ∀ x ∈ (b.stages.push last).toList.map Ew.Stage.bytes, x.size = Ew.stageBytes := fun x hx => by
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hx; exact stage_bytes_size s
  have hs := (foldl_append_get Ew.stageBytes _ hL ByteArray.empty).1
  have hp : b.prog last = ((b.stages.push last).toList.map Ew.Stage.bytes).foldl (· ++ ·) ByteArray.empty := by
    simp only [Ew.Build.prog, ← Array.foldl_toList, Array.toList_map]
  rw [hp, hs]
  simp only [ByteArray.size_empty, List.length_map, Array.length_toList, Array.size_push, Ew.stageBytes]
  omega

/-! ## `Ew.chain`'s fold: one answer pushed per stage, the earlier ones kept -/

/-- A fold that pushes one element per index holds one per index. -/
theorem foldl_push_size {α : Type} (g : Array α → Nat → α) :
    ∀ (j : Nat) (init : Array α), ((List.range j).foldl (fun o i => o.push (g o i)) init).size = init.size + j
  | 0, init => by simp
  | j + 1, init => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Array.size_push,
      foldl_push_size g j init]; omega

/-- **Index `k` of the fold is fixed once it is pushed**, and the element pushed at `j` is `g` of the fold
    before it. -/
theorem foldl_push_get {α : Type} [Inhabited α] (g : Array α → Nat → α) (init : Array α) (j : Nat) :
    (∀ k < init.size + j, ((List.range (j + 1)).foldl (fun o i => o.push (g o i)) init)[k]! =
      ((List.range j).foldl (fun o i => o.push (g o i)) init)[k]!) ∧
    ((List.range (j + 1)).foldl (fun o i => o.push (g o i)) init)[init.size + j]! =
      g ((List.range j).foldl (fun o i => o.push (g o i)) init) j := by
  have hs := foldl_push_size g j init
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [getElem!_pos _ k (by rw [Array.size_push, hs]; omega), getElem!_pos _ k (by rw [hs]; omega),
      Array.getElem_push, dif_pos (by rw [hs]; omega)]
  · rw [getElem!_pos _ _ (by rw [Array.size_push, hs]; omega), Array.getElem_push, dif_neg (by rw [hs]; omega)]

/-- **Element `k` of the fold is `g` of the fold of the first `k`**, once `k` is pushed, whatever was pushed
    after it. -/
theorem foldl_push_get_lt {α : Type} [Inhabited α] (g : Array α → Nat → α) (init : Array α) {k : Nat} :
    ∀ {j : Nat}, k < j → ((List.range j).foldl (fun o i => o.push (g o i)) init)[init.size + k]! =
      g ((List.range k).foldl (fun o i => o.push (g o i)) init) k
  | 0, h => absurd h (Nat.not_lt_zero _)
  | j + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · rw [(foldl_push_get g init j).1 _ (by omega)]; exact foldl_push_get_lt g init h
    · exact (foldl_push_get g init k).2

/-- **A build's run, stage by stage**: `Ew.chain`'s fold over its `stages.size + 1` stages, stage `j` read
    as the build's `j`-th (the last one after them) rather than decoded from the program. The step is
    `Ew.chain`'s own, restated because qlean writes it inline; `rfl` up to `stageAt_prog` checks the copy. -/
theorem run_fold (b : Ew.Build) (last : Ew.Stage) (n : USize) :
    b.run last n = ((List.range (b.stages.size + 1)).foldl (init := #[]) fun outs j =>
      let st := (b.stages.push last)[j]!
      let src (c : UInt8) : ByteArray :=
        if c < Ew.slot0 then b.inputs[c.toNat]! else outs[(c - Ew.slot0).toNat]!
      outs.push <|
       if st.engine == Ew.eVal then Ew.val st.op st.cls st.shape st.nul (src st.a) (src st.b) n
       else if st.engine == Ew.eCmp then Ew.cmp st.op st.cls st.shape (src st.a) (src st.b) n
       else if st.engine == Ew.eMon then Ew.mon st.op st.cls st.nul (src st.a) n
       else if st.engine == Ew.eWiden then Ew.widen st.cls st.shape st.nul st.nulOut (src st.a) n
       else if st.engine == Ew.eBit then Ew.bit st.op st.shape (src st.a) (src st.b) n
       else if st.engine == Ew.eFloor then Ew.floor st.cls (src st.a) n
       else if st.engine == Ew.eCast then Ew.castTo st.cls st.shape st.nul (src st.a) n
       else if st.engine == Ew.eTick then Ew.tick st.op st.cls st.shape st.nul st.nulOut (src st.a) n
       else if st.engine == Ew.eIds then
         Column.packIds (8 * Ew.width st.cls) n.toNat (Column.idAt (src st.a) st.shape.toNat)
       else if st.engine == Ew.ePack then
         Column.packIds st.shape.toNat n.toNat fun i => (Ew.elem st.cls (src st.a) i).toNat
       else if st.engine == Ew.eDecode then Coc.decode (Ew.width st.cls).toUSize (src st.a) (src st.b) n
       else if Column.alpF32 (src st.c) then Coc.alpDecode32 (src st.a) (src st.b) (src st.c) n
       else Coc.alpDecode64 (src st.a) (src st.b) (src st.c) n)[b.stages.size]! := by
  simp only [Ew.Build.run, Ew.chain, prog_count, Nat.add_sub_cancel]
  congr 1
  have hm : ∀ j ∈ List.range (b.stages.size + 1), j < b.stages.size + 1 := fun j hj => List.mem_range.1 hj
  generalize List.range (b.stages.size + 1) = l at hm ⊢
  generalize (#[] : Array ByteArray) = init
  induction l generalizing init with
  -- not `rfl`: the kernel would compare the two steps before reducing the empty fold, and time out
  | nil => rw [List.foldl_nil, List.foldl_nil]
  | cons j l ih =>
    simp only [List.foldl_cons]
    rw [stageAt_prog b last j (hm j (by simp)),
      getElem!_pos (b.stages.push last) j (by simpa using hm j (by simp))]
    exact ih (fun k hk => hm k (by simp [hk])) _

end LeetQ.Rel.Alg
