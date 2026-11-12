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

end LeetQ.Rel.Alg
