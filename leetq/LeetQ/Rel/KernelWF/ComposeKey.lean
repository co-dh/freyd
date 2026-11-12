/-
  What `composeKey` CONTAINS: the chain it builds, read back stage by stage. First the program's stage
  count, for a build of any number of stages (qlean's `Verify.prog_one` is the build of none).
-/
import QLean.Verify.Chain
import QLean.Verify.Where

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

/-! ## The guard: `overBytes`' extremes bound every element it does not skip -/

/-- `min/` and `max/` folded from `s`: at most (at least) `s` and every element. -/
theorem foldl_extreme (s : Int64) (xs : List Int64) :
    ((xs.foldl Coc.Over.lesser.step s).toInt ≤ s.toInt ∧ ∀ x ∈ xs, (xs.foldl Coc.Over.lesser.step s).toInt ≤ x.toInt) ∧
    (s.toInt ≤ (xs.foldl Coc.Over.greater.step s).toInt ∧ ∀ x ∈ xs, x.toInt ≤ (xs.foldl Coc.Over.greater.step s).toInt) := by
  induction xs generalizing s with
  | nil => simp
  | cons y ys ih =>
    obtain ⟨⟨hl, hlx⟩, ⟨hg, hgx⟩⟩ := ih (Coc.Over.lesser.step s y)
    obtain ⟨⟨-, -⟩, ⟨hg', hgx'⟩⟩ := ih (Coc.Over.greater.step s y)
    have e1 : (Coc.Over.lesser.step s y).toInt ≤ s.toInt ∧ (Coc.Over.lesser.step s y).toInt ≤ y.toInt := by
      simp only [Coc.Over.step]; by_cases h : s < y
      · rw [if_pos h]; have := Int64.lt_iff_toInt_lt.1 h; omega
      · rw [if_neg h]; have := mt Int64.lt_iff_toInt_lt.2 h; omega
    have e2 : s.toInt ≤ (Coc.Over.greater.step s y).toInt ∧ y.toInt ≤ (Coc.Over.greater.step s y).toInt := by
      simp only [Coc.Over.step]; by_cases h : y < s
      · rw [if_pos h]; have := Int64.lt_iff_toInt_lt.1 h; omega
      · rw [if_neg h]; have := mt Int64.lt_iff_toInt_lt.2 h; omega
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    refine ⟨⟨by omega, by omega, fun x hx => hlx x hx⟩, ⟨by omega, by omega, fun x hx => hgx' x hx⟩⟩

/-- **`overBytes`' minimum is at most every element but `nul`, its maximum at least every one.** -/
theorem overBytes_extreme (cls : UInt8) (nul : Int64) (b : ByteArray) {i : Nat} (hi : i < b.size / Ew.width cls)
    (hn : Ew.signed cls (Ew.elem cls b i) ≠ nul) :
    (overBytes .lesser cls nul b).toInt ≤ (Ew.signed cls (Ew.elem cls b i)).toInt ∧
      (Ew.signed cls (Ew.elem cls b i)).toInt ≤ (overBytes .greater cls nul b).toInt := by
  have hm : Ew.signed cls (Ew.elem cls b i) ∈ (denseElems cls b).filter fun x => x != nul := by
    simp only [List.mem_filter, denseElems, List.mem_map, List.mem_range, bne_iff_ne, ne_eq]
    exact ⟨⟨i, hi, rfl⟩, hn⟩
  rw [overBytes_eq, overBytes_eq, overList, overList]
  exact ⟨(foldl_extreme _ _).1.2 _ (by simpa [Coc.Over.boolCast] using hm),
    (foldl_extreme _ _).2.2 _ (by simpa [Coc.Over.boolCast] using hm)⟩

/-- **`keyOperand` on a dense column: every element is in `[0, hi]`** when it reports no negative code. -/
theorem keyOperand_bytes {t u : QAtomicType} {b : ByteArray} {hi : Int}
    (h : keyOperand t (.bytes b) = some (u, false, hi)) :
    u = t ∧ ∃ cls, clsOf t = some cls ∧ ∀ i < b.size / Ew.width cls,
      0 ≤ (Ew.signed cls (Ew.elem cls b i)).toInt ∧ (Ew.signed cls (Ew.elem cls b i)).toInt ≤ hi := by
  simp only [keyOperand, bind, Option.bind] at h
  split at h
  · simp at h
  rename_i hg
  cases hc : clsOf t with
  | none => simp [hc] at h
  | some cls =>
    simp only [hc, Option.some.injEq, Prod.mk.injEq, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    obtain ⟨rfl, ⟨h1, h2⟩, rfl⟩ := h
    refine ⟨rfl, cls, rfl, fun i hi => ?_⟩
    have hx := fun (nul : Int64) (hn : Ew.signed cls (Ew.elem cls b i) ≠ nul) => overBytes_extreme cls nul b hi hn
    have h1' := mt Int64.lt_iff_toInt_lt.2 h1
    have h2' := mt Int64.lt_iff_toInt_lt.2 h2
    simp only [Int64.toInt_zero] at h1' h2'
    have hnn : 0 ≤ (Ew.signed cls (Ew.elem cls b i)).toInt := by
      by_cases e : Ew.signed cls (Ew.elem cls b i) = -1
      · have := (hx (-2) (by rw [e]; decide)).1; rw [e] at this ⊢; simp at this; omega
      · have := (hx (-1) e).1; omega
    refine ⟨hnn, (hx Int64.minValue fun e => ?_).2⟩
    rw [e] at hnn; simp at hnn

end LeetQ.Rel.Alg
