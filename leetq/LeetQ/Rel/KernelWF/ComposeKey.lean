/-
  What `composeKey` CONTAINS: the chain it builds, read back stage by stage. First the program's stage
  count, for a build of any number of stages (qlean's `Verify.prog_one` is the build of none).
-/
import QLean.Verify.Chain
import QLean.Verify.Where
import QLean.Verify.Group
import QLean.Verify.Ids
import LeetQ.Rel.KernelWF.Lane
import LeetQ.Rel.KernelWF.CodesSpec

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

/-- **One stage's answer, its operands read by `src`**: the body of `Ew.chain`'s step, restated because
    qlean writes it inline. -/
def stageRun (st : Ew.Stage) (src : UInt8 → ByteArray) (n : USize) : ByteArray :=
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
  else Coc.alpDecode64 (src st.a) (src st.b) (src st.c) n

/-- `Ew.chain`'s step at stage `j` of a build (the last one after its stages), the answers so far `outs`. -/
def chainStep (b : Ew.Build) (last : Ew.Stage) (n : USize) (outs : Array ByteArray) (j : Nat) : ByteArray :=
  stageRun (b.stages.push last)[j]!
    (fun c => if c < Ew.slot0 then b.inputs[c.toNat]! else outs[(c - Ew.slot0).toNat]!) n

/-- **A build's run, stage by stage**: `Ew.chain`'s fold over its `stages.size + 1` stages, stage `j` read
    as the build's `j`-th (the last one after them) rather than decoded from the program. -/
theorem run_fold (b : Ew.Build) (last : Ew.Stage) (n : USize) :
    b.run last n =
      ((List.range (b.stages.size + 1)).foldl (fun o i => o.push (chainStep b last n o i)) #[])[b.stages.size]! := by
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
      ← getElem!_pos (b.stages.push last) j (by simpa using hm j (by simp))]
    exact ih (fun k hk => hm k (by simp [hk])) _

/-- Two push-folds over `range m` agree where their steps agree below `m`. -/
theorem foldl_range_congr {α : Type} (g g' : Array α → Nat → α) (init : Array α) :
    ∀ m, (∀ o, ∀ j < m, g o j = g' o j) →
      (List.range m).foldl (fun o i => o.push (g o i)) init = (List.range m).foldl (fun o i => o.push (g' o i)) init
  | 0, _ => by rw [List.range_zero, List.foldl_nil, List.foldl_nil]
  | m + 1, h => by
    rw [List.range_succ, List.foldl_append, List.foldl_append,
      foldl_range_congr g g' init m (fun o j hj => h o j (by omega)), List.foldl_cons, List.foldl_cons,
      List.foldl_nil, List.foldl_nil, h _ m (by omega)]

/-- The run as its last stage over the fold of the stages before it. -/
theorem run_eq (b : Ew.Build) (last : Ew.Stage) (n : USize) :
    b.run last n = stageRun last (fun c => if c < Ew.slot0 then b.inputs[c.toNat]! else
      ((List.range b.stages.size).foldl (fun o i => o.push (chainStep b last n o i)) #[])[(c - Ew.slot0).toNat]!) n := by
  have h := (foldl_push_get (chainStep b last n) #[] b.stages.size).2
  rw [Array.size_empty, Nat.zero_add] at h
  rw [run_fold, h, chainStep, getElem!_pos (b.stages.push last) b.stages.size (by simp), Array.getElem_push_eq]

theorem get_push_lt {α : Type} [Inhabited α] (xs : Array α) (x : α) {j : Nat} (h : j < xs.size) :
    (xs.push x)[j]! = xs[j]! := by
  rw [getElem!_pos _ j (by simp; omega), getElem!_pos xs j h, Array.getElem_push_lt]

theorem get_extract_lt {α : Type} [Inhabited α] (xs : Array α) {j m : Nat} (h : j < m) (hm : m ≤ xs.size) :
    (xs.extract 0 m)[j]! = xs[j]! := by
  rw [getElem!_pos _ j (by simp; omega), getElem!_pos xs j (by omega), Array.getElem_extract]; simp

/-- **What source `c` of a build reads**: input `c` below `slot0`; slot `m` is the run of the build's first `m`
    stages with its stage `m` last; past the stages, nothing. -/
def srcOf (b : Ew.Build) (n : USize) (c : UInt8) : ByteArray :=
  if c < Ew.slot0 then b.inputs[c.toNat]!
  else if (c - Ew.slot0).toNat < b.stages.size then
    Ew.Build.run { b with stages := b.stages.extract 0 (c - Ew.slot0).toNat } b.stages[(c - Ew.slot0).toNat]! n
  else default

/-- **The run of a build is its last stage's body**, each source read by `srcOf`. -/
theorem run_last (b : Ew.Build) (last : Ew.Stage) (n : USize) : b.run last n = stageRun last (srcOf b n) n := by
  rw [run_eq]
  congr 1
  funext c
  unfold srcOf
  by_cases hc : c < Ew.slot0
  · rw [if_pos hc, if_pos hc]
  rw [if_neg hc, if_neg hc]
  generalize (c - Ew.slot0).toNat = m
  have hs := foldl_push_size (chainStep b last n) b.stages.size #[]
  rw [Array.size_empty, Nat.zero_add] at hs
  by_cases hm : m < b.stages.size
  · rw [if_pos hm]
    have h1 := foldl_push_get_lt (chainStep b last n) #[] hm
    rw [Array.size_empty, Nat.zero_add] at h1
    have hx : (b.stages.extract 0 m).size = m := by simp; omega
    have hcg := foldl_range_congr (chainStep b last n) (chainStep { b with stages := b.stages.extract 0 m } b.stages[m]! n)
      #[] m (fun o j hj => by
        unfold chainStep
        rw [get_push_lt _ _ (by omega), get_push_lt _ _ (by rw [hx]; exact hj), get_extract_lt _ hj (by omega)])
    rw [h1, run_eq]
    dsimp only
    rw [hx, ← hcg]
    unfold chainStep
    rw [get_push_lt _ _ hm]
  · rw [if_neg hm, getElem!_neg _ _ (by rw [hs]; exact hm)]

theorem u8_ofNat {m : Nat} (hm : m < 256) : (UInt8.ofNat m).toNat = m := by
  first | exact UInt8.toNat_ofNat_of_lt' hm | exact UInt8.toNat_ofNat_of_lt hm | (simp; omega)

/-- A build's slot code `slot0 + m` names stage `m`. -/
theorem slot_code {m : Nat} (hm : m < 128) :
    ¬ (Ew.slot0 + m.toUInt8 < Ew.slot0) ∧ (Ew.slot0 + m.toUInt8 - Ew.slot0).toNat = m := by
  have h := u8_ofNat (m := m) (by omega)
  simp only [Ew.slot0, UInt8.lt_iff_toNat_lt, UInt8.toNat_add, UInt8.toNat_sub, Nat.toUInt8_eq, UInt8.toNat_ofNat, h]
  omega

/-- A build's input code `m` names input `m`. -/
theorem input_code {m : Nat} (hm : m < 128) : m.toUInt8 < Ew.slot0 ∧ m.toUInt8.toNat = m := by
  have h : m.toUInt8.toNat = m := u8_ofNat (by omega)
  refine ⟨?_, h⟩
  rw [UInt8.lt_iff_toNat_lt, h]; simp only [Ew.slot0, UInt8.toNat_ofNat]; omega

theorem srcOf_input (B : Ew.Build) (n : USize) {i : Nat} (h : i < 128) : srcOf B n i.toUInt8 = B.inputs[i]! := by
  obtain ⟨h1, h2⟩ := input_code h
  rw [srcOf, if_pos h1, h2]

theorem srcOf_slot (B : Ew.Build) (n : USize) {m : Nat} (hm : m < B.stages.size) (h128 : m < 128) :
    srcOf B n (Ew.slot0 + m.toUInt8) = stageRun B.stages[m]! (srcOf { B with stages := B.stages.extract 0 m } n) n := by
  obtain ⟨h1, h2⟩ := slot_code h128
  rw [srcOf, if_neg h1, h2, if_pos hm, run_last]

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

/-! ## The stages' element laws, at the classes `composeKey` runs them -/

/-- **`Ew.val`'s element `i`** is `valStep` on the two elements the shape reads, on the payload's bits. -/
theorem elem_val (op cls shape : UInt8) (nul : Int64) (a b : ByteArray) (n : USize) {i : Nat} (hi : i < n.toNat) :
    Ew.elem cls (Ew.val op cls shape nul a b n) i =
      UInt64.ofNat ((Ew.valStep op cls nul.toUInt64 (Ew.elem cls a (Ew.shapeIdx shape i).1)
        (Ew.elem cls b (Ew.shapeIdx shape i).2)).toNat % 2 ^ (8 * Ew.width cls)) := by
  obtain ⟨-, hw8⟩ := width_pos_le cls
  let g : Nat → UInt64 := fun i =>
    Ew.valStep op cls nul.toUInt64 (Ew.elem cls a (Ew.shapeIdx shape i).1) (Ew.elem cls b (Ew.shapeIdx shape i).2)
  have hf : Ew.val op cls shape nul a b n =
      (List.range n.toNat).foldl (fun acc i => Column.pushBits acc (g i) (Ew.width cls)) ByteArray.empty := rfl
  have h := (foldl_pushBits g (Ew.width cls) hw8 (List.range n.toNat) ByteArray.empty).2.2 i (by simpa using hi)
  rw [ByteArray.size_empty, Nat.zero_add, List.getElem_range] at h
  rw [Ew.elem, hf, Nat.mul_comm, h]

/-- **`Ew.widen` to `i64` with one null in and out carries every integral element**: element `i` is the
    source element `widenRead` reads, sign-extended (zero-extended at `u8`, a bit at `bits`). -/
theorem elem_widen_i64 {src : UInt8} (hs : src ≠ Ew.f32 ∧ src ≠ Ew.f64) (nul : Int64) (x : ByteArray) (n : USize)
    {i : Nat} (hi : i < n.toNat) :
    Ew.elem Ew.i64 (Ew.widen src Ew.i64 nul nul x n) i = (Ew.widenRead src x i).toUInt64 := by
  have hf : Ew.widen src Ew.i64 nul nul x n = (List.range n.toNat).foldl (fun acc i =>
      Column.pushBits acc (Ew.widenStep Ew.i64 nul nul (Ew.widenRead src x i)) (Ew.width Ew.i64)) ByteArray.empty := by
    simp [Ew.widen, hs.1, hs.2]
  have h := (foldl_pushBits (fun i => Ew.widenStep Ew.i64 nul nul (Ew.widenRead src x i)) (Ew.width Ew.i64)
    (by decide) (List.range n.toNat) ByteArray.empty).2.2 i (by simpa using hi)
  rw [ByteArray.size_empty, Nat.zero_add, List.getElem_range] at h
  rw [Ew.elem, hf, Nat.mul_comm, h, show 8 * Ew.width Ew.i64 = 64 by decide,
    Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  simp only [Ew.widenStep, show (Ew.i64 == Ew.f64) = false by decide, show (Ew.i64 == Ew.f32) = false by decide,
    Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i e; rw [eq_of_beq e]
  · rfl

/-- The element law of `Ew.eIds` at `i64` (qlean's `StructuralTest.eIds_idAt`, a test module, so restated):
    element `k` of the stage's answer is id `k` of the lane it read, whatever that lane's width. -/
theorem eIds_idAt (a : ByteArray) {w n k : Nat} (hk : k < n) :
    Column.idAt (Column.packIds (8 * Ew.width Ew.i64) n (Column.idAt a w)) 64 k = Column.idAt a w k := by
  rw [show 8 * Ew.width Ew.i64 = 64 by decide]
  exact idAt_packIds (by decide) hk (by unfold Column.idAt; exact UInt64.toNat_lt _)

/-- **The element law of `Ew.ePack` as `composeKey` runs it** (qlean's `StructuralTest.ePack_idAt`): the
    key `c₁·d₂ + c₂` an `i64` payload holds at `k` reads back from the lane `idWidthOf (d₁ * d₂)`. -/
theorem ePack_idAt (s : ByteArray) {d₁ d₂ c₁ c₂ n k : Nat} (hk : k < n) (h₁ : c₁ < d₁) (h₂ : c₂ < d₂)
    (hd : d₁ * d₂ ≤ 2 ^ 64) (hs : (Ew.elem Ew.i64 s k).toNat = c₁ * d₂ + c₂) :
    Column.idAt (Column.packIds (Column.idWidthOf (d₁ * d₂)) n fun i => (Ew.elem Ew.i64 s i).toNat)
      (Column.idWidthOf (d₁ * d₂)) k = c₁ * d₂ + c₂ := by
  have hlt : c₁ * d₂ + c₂ < d₁ * d₂ :=
    Nat.lt_of_lt_of_le (by rw [Nat.add_one_mul]; omega) (Nat.mul_le_mul_right d₂ (h₁ : c₁ + 1 ≤ d₁))
  exact (idAt_packIds (w := Column.idWidthOf (d₁ * d₂)) (laneWidth_cases _) hk
    (by simp only [hs]; exact lt_two_pow_idWidthOf hd hlt)).trans hs

/-- **The atom `composeKey` multiplies by**: element `0` of `atomBytes i64 v` is `v`. -/
theorem elem_atomBytes_i64 (v : UInt64) : Ew.elem Ew.i64 (atomBytes Ew.i64 v) 0 = v := by
  have hf : atomBytes Ew.i64 v = [()].foldl (fun acc _ => Column.pushBits acc v (Ew.width Ew.i64)) ByteArray.empty := rfl
  have h := (foldl_pushBits (fun _ : Unit => v) (Ew.width Ew.i64) (by decide) [()] ByteArray.empty).2.2 0 (by decide)
  rw [ByteArray.size_empty, Nat.zero_add, Nat.mul_zero] at h
  rw [Ew.elem, hf, Nat.zero_mul, h, show 8 * Ew.width Ew.i64 = 64 by decide,
    Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]

/-- An element below `2⁶³` is not `long`'s null. -/
theorem toInt64_ne_minValue {x : UInt64} (hx : x.toNat < 2 ^ 63) : x.toInt64 ≠ Int64.minValue := fun e => by
  have h := congrArg (fun v : Int64 => v.toUInt64.toNat) e
  simp only [UInt64.toUInt64_toInt64] at h
  rw [h] at hx; exact absurd hx (by decide)

/-- **`*` and `+` at `i64` with `long`'s null, below `2⁶³`, are the naturals' `*` and `+`**: no null is
    read and nothing wraps — the two arithmetic stages of `composeKey`. -/
theorem valStep_key (x y : UInt64) (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63) :
    (x.toNat * y.toNat < 2 ^ 63 →
      (Ew.valStep Ew.mul Ew.i64 Int64.minValue.toUInt64 x y).toNat = x.toNat * y.toNat) ∧
    (x.toNat + y.toNat < 2 ^ 63 →
      (Ew.valStep Ew.add Ew.i64 Int64.minValue.toUInt64 x y).toNat = x.toNat + y.toNat) := by
  have hs : ∀ v : UInt64, Ew.signed Ew.i64 v = v.toInt64 := fun v => by simp [Ew.signed, Ew.i64, Ew.u8, Ew.i16, Ew.i32]
  have hn : Ew.signed Ew.i64 Int64.minValue.toUInt64 = Int64.minValue := by rw [hs]; simp
  have hx' := toInt64_ne_minValue hx
  have hy' := toInt64_ne_minValue hy
  simp only [Ew.valStep, show (Ew.i64 == Ew.f64) = false by decide, show (Ew.i64 == Ew.f32) = false by decide,
    Bool.false_eq_true, ↓reduceIte, hs, hn, Ew.intStep, show (Ew.mul == Ew.add) = false by decide,
    show (Ew.mul == Ew.sub) = false by decide, beq_self_eq_true, beq_eq_false_iff_ne.2 hx',
    beq_eq_false_iff_ne.2 hy', Bool.or_false, Int64.toUInt64_mul, Int64.toUInt64_add, UInt64.toUInt64_toInt64]
  simp only [Int64.toInt64_toUInt64, beq_eq_false_iff_ne.2 hx', beq_eq_false_iff_ne.2 hy', Bool.or_false,
    Bool.false_eq_true, ↓reduceIte, Int64.toUInt64_mul, Int64.toUInt64_add, UInt64.toUInt64_toInt64]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [UInt64.toNat_mul, Nat.mod_eq_of_lt (by omega)]
  · rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]

/-! ## Reading a code back at `i64` -/

theorem toNat_toUInt64_of_nonneg (s : Int64) (h : 0 ≤ s.toInt) : s.toUInt64.toNat = s.toInt.toNat := by
  have e1 : s.toUInt64.toNat = s.toBitVec.toNat := rfl
  have e2 : s.toInt = s.toBitVec.toInt := rfl
  have := s.toBitVec.isLt
  rw [e1, e2, BitVec.toInt_eq_toNat_cond]; rw [e2, BitVec.toInt_eq_toNat_cond] at h
  split <;> split at h <;> omega

theorem bv_nonneg {w : Nat} (x : BitVec w) (h : 0 ≤ x.toInt) : x.toInt = x.toNat := by
  have := x.isLt
  rw [BitVec.toInt_eq_toNat_cond] at h ⊢
  split <;> split at h <;> omega

/-- **An integral element read signed and found non-negative is the element itself.** -/
theorem signed_nonneg {cls : UInt8} (hc : cls = Ew.u8 ∨ cls = Ew.i16 ∨ cls = Ew.i32 ∨ cls = Ew.i64) (v : UInt64)
    (hv : v.toNat < 2 ^ (8 * Ew.width cls)) (h : 0 ≤ (Ew.signed cls v).toInt) :
    (Ew.signed cls v).toInt = v.toNat := by
  rcases hc with rfl | rfl | rfl | rfl
  · simp only [Ew.signed, Ew.width, Ew.u8, if_pos, beq_self_eq_true, ↓reduceIte] at hv h ⊢
    have e : v.toUInt8.toUInt64.toInt64.toInt = v.toUInt8.toUInt64.toBitVec.toInt := rfl
    rw [e] at h ⊢; rw [bv_nonneg _ h]; simp; omega
  · simp only [Ew.signed, Ew.width, Ew.u8, Ew.i16, beq_self_eq_true, ↓reduceIte] at hv h ⊢
    simp at hv h ⊢
    have e : v.toUInt16.toInt16.toInt = v.toUInt16.toBitVec.toInt := rfl
    rw [e] at h ⊢; rw [bv_nonneg _ h]; simp; omega
  · simp only [Ew.signed, Ew.width, Ew.u8, Ew.i16, Ew.i32] at hv h ⊢
    simp at hv h ⊢
    have e : v.toUInt32.toInt32.toInt = v.toUInt32.toBitVec.toInt := rfl
    rw [e] at h ⊢; rw [bv_nonneg _ h]; simp; omega
  · simp only [Ew.signed, Ew.width, Ew.u8, Ew.i16, Ew.i32, Ew.i64] at hv h ⊢
    simp at h ⊢
    have e : v.toInt64.toInt = v.toBitVec.toInt := rfl
    rw [e] at h ⊢; rw [bv_nonneg _ h]; simp

/-- A dense element at `cls` is the code at the lane `8 · width cls`. -/
theorem elem_idAt (cls : UInt8) (x : ByteArray) (j : Nat) :
    (Ew.elem cls x j).toNat = Column.idAt x (8 * Ew.width cls) j := by
  rw [idAt_lane x (width_pos_le cls).2 j, Ew.elem]

/-- **A dense code read signed by `keyOperand`'s guard is the code**, at most `hi`. -/
theorem bytes_code {cls : UInt8} (hc : cls = Ew.u8 ∨ cls = Ew.i16 ∨ cls = Ew.i32 ∨ cls = Ew.i64) {x : ByteArray}
    {hi : Int} {j : Nat} (h : 0 ≤ (Ew.signed cls (Ew.elem cls x j)).toInt ∧ (Ew.signed cls (Ew.elem cls x j)).toInt ≤ hi) :
    (Ew.signed cls (Ew.elem cls x j)).toUInt64.toNat = Column.idAt x (8 * Ew.width cls) j ∧
      (Column.idAt x (8 * Ew.width cls) j : Int) ≤ hi := by
  have hv : (Ew.elem cls x j).toNat < 2 ^ (8 * Ew.width cls) := by
    rw [elem_idAt]; exact idAt_lt _ _ _ (by have := (width_pos_le cls).2; omega)
  have e := signed_nonneg hc _ hv h.1
  rw [toNat_toUInt64_of_nonneg _ h.1, e, ← elem_idAt]
  exact ⟨by simp, by have := h.2; omega⟩

/-- **A promoted dense code read at `i64` is the code**, at most `hi`. -/
theorem widen_code {cls : UInt8} (hc : cls = Ew.u8 ∨ cls = Ew.i16 ∨ cls = Ew.i32) {x : ByteArray} {n : USize}
    {hi : Int} {j : Nat} (hj : j < n.toNat)
    (h : 0 ≤ (Ew.signed cls (Ew.elem cls x j)).toInt ∧ (Ew.signed cls (Ew.elem cls x j)).toInt ≤ hi) :
    (Ew.elem Ew.i64 (Ew.widen cls Ew.i64 Int64.minValue Int64.minValue x n) j).toNat =
      Column.idAt x (8 * Ew.width cls) j ∧ (Column.idAt x (8 * Ew.width cls) j : Int) ≤ hi := by
  have hs : cls ≠ Ew.f32 ∧ cls ≠ Ew.f64 := by rcases hc with rfl | rfl | rfl <;> decide
  have hb : (cls == Ew.bits) = false := by rcases hc with rfl | rfl | rfl <;> decide
  rw [elem_widen_i64 hs _ _ _ hj, Ew.widenRead, hb]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact bytes_code (by rcases hc with h | h | h <;> simp [h]) h

/-- `keyOperand` on a dense column keeps the column's type. -/
theorem keyOperand_bytes_type {t u : QAtomicType} {b : ByteArray} {neg : Bool} {hi : Int}
    (h : keyOperand t (.bytes b) = some (u, neg, hi)) : u = t := by
  simp only [keyOperand, bind, Option.bind] at h
  split at h
  · simp at h
  cases hc : clsOf t with
  | none => simp [hc] at h
  | some cls => simp only [hc, Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm

theorem stageRun_widen {st : Ew.Stage} (h : st.engine = Ew.eWiden) (src : UInt8 → ByteArray) (n : USize) :
    stageRun st src n = Ew.widen st.cls st.shape st.nul st.nulOut (src st.a) n := by
  simp [stageRun, h, Ew.eVal, Ew.eCmp, Ew.eMon, Ew.eWiden]

theorem stageRun_ids {st : Ew.Stage} (h : st.engine = Ew.eIds) (src : UInt8 → ByteArray) (n : USize) :
    stageRun st src n = Column.packIds (8 * Ew.width st.cls) n.toNat (Column.idAt (src st.a) st.shape.toNat) := by
  simp [stageRun, h, Ew.eVal, Ew.eCmp, Ew.eMon, Ew.eWiden, Ew.eBit, Ew.eFloor, Ew.eCast, Ew.eTick, Ew.eIds]

theorem stageRun_pack {st : Ew.Stage} (h : st.engine = Ew.ePack) (src : UInt8 → ByteArray) (n : USize) :
    stageRun st src n = Column.packIds st.shape.toNat n.toNat fun i => (Ew.elem st.cls (src st.a) i).toNat := by
  simp [stageRun, h, Ew.eVal, Ew.eCmp, Ew.eMon, Ew.eWiden, Ew.eBit, Ew.eFloor, Ew.eCast, Ew.eTick, Ew.eIds, Ew.ePack]

theorem stageRun_val {st : Ew.Stage} (h : st.engine = Ew.eVal) (src : UInt8 → ByteArray) (n : USize) :
    stageRun st src n = Ew.val st.op st.cls st.shape st.nul (src st.a) (src st.b) n := by
  simp [stageRun, h]

theorem get_push_eq {α : Type} [Inhabited α] (xs : Array α) (x : α) : (xs.push x)[xs.size]! = x := by
  rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]

/-- **A one-stage operand**: slot `b.stages.size` of a build extending `b`'s with input `x` and stage `st`
    reading it is `st`'s body over sources answering `x` at `st.a`. -/
theorem srcOf_stage {b B : Ew.Build} {x : ByteArray} {st : Ew.Stage} (n : USize) (hb : b.inputs.size < 128)
    (hbs : b.stages.size < 128) (hst : st.a = b.inputs.size.toUInt8)
    (hBi : ∀ i < (b.inputs.push x).size, B.inputs[i]! = (b.inputs.push x)[i]!)
    (hBs : ∀ j < (b.stages.push st).size, B.stages[j]! = (b.stages.push st)[j]!)
    (hBz : (b.stages.push st).size ≤ B.stages.size) :
    ∃ src : UInt8 → ByteArray, src st.a = x ∧ srcOf B n (Ew.slot0 + b.stages.size.toUInt8) = stageRun st src n := by
  refine ⟨srcOf { B with stages := B.stages.extract 0 b.stages.size } n, ?_, ?_⟩
  · rw [hst, srcOf_input _ _ hb]; dsimp only; rw [hBi _ (by simp), get_push_eq]
  · rw [srcOf_slot B n (by simp at hBz; omega) hbs, hBs _ (by simp), get_push_eq]

/-- **`keySource` on a code's column**: one input, the code's payload, and at most one stage after `b`'s.
    Any build extending it reads, at `s`, element `j` as code `j` of `c`, below `d` where the guard passed. -/
theorem keySource_code (c : Code)
    (hw : laneOK(c.w))
    (hs : c.b.size = (c.n.toNat * c.w + 7) / 8)
    (hc : c.w < 8 → ∀ i < c.n.toNat, Column.idAt c.b c.w i < max c.card 2)
    {t : QAtomicType} {m : USize} {e : Enc} (hcol : c.column = some (t, (m, e)))
    {u : QAtomicType} {neg : Bool} {hi : Int} (hko : keyOperand t e = some (u, neg, hi))
    {d : Nat} (hd : c.n = 0 ∨ (neg = false ∧ hi < d)) (h2 : 2 ≤ d)
    {b b' : Ew.Build} {s : UInt8} (hks : keySource b u e c.n = some (b', s))
    (hb : b.inputs.size < 128) (hbs : b.stages.size < 128) :
    b'.inputs = b.inputs.push c.b ∧ b.stages.size ≤ b'.stages.size ∧ b'.stages.size ≤ b.stages.size + 1 ∧
      (∀ j < b.stages.size, b'.stages[j]! = b.stages[j]!) ∧
      ∀ B : Ew.Build, (∀ i < b'.inputs.size, B.inputs[i]! = b'.inputs[i]!) →
        (∀ j < b'.stages.size, B.stages[j]! = b'.stages[j]!) → b'.stages.size ≤ B.stages.size →
        ∀ j < c.n.toNat, (Ew.elem Ew.i64 (srcOf B c.n s) j).toNat = Column.idAt c.b c.w j ∧
          Column.idAt c.b c.w j < d := by
  obtain ⟨w, cn, card, cb⟩ := c
  have e8 : Ew.width Ew.u8 = 1 := by decide
  have e16 : Ew.width Ew.i16 = 2 := by decide
  have e32 : Ew.width Ew.i32 = 4 := by decide
  have e64 : Ew.width Ew.i64 = 8 := by decide
  dsimp only at hw hs hc hd hks ⊢
  have hstage : ∀ (st : Ew.Stage), st.a = b.inputs.size.toUInt8 →
      b' = { stages := b.stages.push st, inputs := b.inputs.push cb } → s = Ew.slot0 + b.stages.size.toUInt8 →
      (∀ j < cn.toNat, ∀ src : UInt8 → ByteArray, src st.a = cb → j < cn.toNat →
        (Ew.elem Ew.i64 (stageRun st src cn) j).toNat = Column.idAt cb w j ∧ Column.idAt cb w j < d) →
      b'.inputs = b.inputs.push cb ∧ b.stages.size ≤ b'.stages.size ∧ b'.stages.size ≤ b.stages.size + 1 ∧
      (∀ j < b.stages.size, b'.stages[j]! = b.stages[j]!) ∧
      ∀ B : Ew.Build, (∀ i < b'.inputs.size, B.inputs[i]! = b'.inputs[i]!) →
        (∀ j < b'.stages.size, B.stages[j]! = b'.stages[j]!) → b'.stages.size ≤ B.stages.size →
        ∀ j < cn.toNat, (Ew.elem Ew.i64 (srcOf B cn s) j).toNat = Column.idAt cb w j ∧ Column.idAt cb w j < d := by
    intro st hst hb' hs' hel
    subst hb' hs'
    refine ⟨rfl, by simp, by simp, fun j hj => get_push_lt _ _ hj, fun B hBi hBs hBz j hj => ?_⟩
    obtain ⟨src, hsrc, e⟩ := srcOf_stage (B := B) cn hb hbs hst hBi hBs hBz
    rw [e]; exact hel j hj src hsrc hj
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- a bitmap: input, then `eWiden` from `bits`
    simp [Code.column, Code.kind, laneKind] at hcol
    obtain ⟨rfl, rfl, rfl⟩ := hcol
    simp [keyOperand] at hko
    obtain ⟨rfl, rfl, rfl⟩ := hko
    simp [keySource, operandSource, clsOf, promotable, Ew.Build.input, Ew.Build.add] at hks
    obtain ⟨-, rfl, rfl⟩ := hks
    refine hstage _ rfl rfl rfl fun j _ src hsrc hj => ?_
    rw [stageRun_widen rfl]; dsimp only; rw [hsrc, elem_widen_i64 (by decide) _ _ _ hj]
    simp only [Ew.widenRead, beq_self_eq_true, ↓reduceIte, idAt_one]
    have hd' : (1 : Int) < d := by
      rcases hd with h0 | ⟨-, h⟩
      · subst h0; simp at hj
      · exact h
    split <;> exact ⟨by first | rfl | decide | simp, by omega⟩
  -- an interned lane of `2` or `4` bits: input, then `eIds` reading it where it lies
  iterate 2
    · simp [Code.column, Code.kind, laneKind] at hcol
      obtain ⟨hwc, rfl, rfl, rfl⟩ := hcol
      simp [keyOperand] at hko
      obtain ⟨rfl, rfl, rfl⟩ := hko
      simp [keySource, Ew.Build.input, Ew.Build.add, Column.idWidth, hwc] at hks
      obtain ⟨-, rfl, rfl⟩ := hks
      refine hstage _ rfl rfl rfl fun j _ src hsrc hj => ?_
      rw [stageRun_ids rfl]; dsimp only; rw [hsrc, elem_idAt]
      have h := eIds_idAt cb (w := Column.idWidthOf card) hj
      have hcj := hc (by omega) j hj
      rw [hwc] at h
      refine ⟨by simpa using h, ?_⟩
      rcases hd with h0 | ⟨-, hh⟩
      · subst h0; simp at hj
      · omega
  -- dense bytes at `u8`, `i16`, `i32`: input, then `eWiden` to `i64`
  iterate 3
    · simp [Code.column, Code.kind, laneKind] at hcol
      obtain ⟨rfl, rfl, rfl⟩ := hcol
      have hu := keyOperand_bytes_type hko
      subst hu
      simp [keySource, operandSource, clsOf, promotable, Ew.Build.input, Ew.Build.add, Ew.u8, Ew.i16, Ew.i32,
        Ew.i64, Ew.bits, Ew.f64] at hks
      obtain ⟨rfl, rfl⟩ := hks
      refine hstage _ rfl rfl rfl fun j _ src hsrc hj => ?_
      obtain ⟨rfl, hh⟩ : neg = false ∧ hi < d := by
        rcases hd with h0 | h
        · subst h0; simp at hj
        · exact h
      obtain ⟨-, cls, hcls, hall⟩ := keyOperand_bytes hko
      simp only [clsOf, Option.some.injEq] at hcls
      subst hcls
      rw [stageRun_widen rfl]; dsimp only; rw [hsrc]
      have hw := widen_code (by decide) (n := cn) hj (hall j (by rw [hs]; simp only [e8, e16, e32, e64]; omega))
      simp only [e8, e16, e32, Nat.reduceMul] at hw
      exact ⟨hw.1, by have := hw.2; omega⟩
  -- dense `i64`: the input itself
  · simp [Code.column, Code.kind, laneKind] at hcol
    obtain ⟨rfl, rfl, rfl⟩ := hcol
    have hu := keyOperand_bytes_type hko
    subst hu
    simp [keySource, operandSource, clsOf, Ew.Build.input] at hks
    obtain ⟨rfl, rfl⟩ := hks
    refine ⟨rfl, by simp, by simp, fun _ _ => rfl, fun B hBi _ _ j hj => ?_⟩
    obtain ⟨rfl, hh⟩ : neg = false ∧ hi < d := by
      rcases hd with h0 | h
      · subst h0; simp at hj
      · exact h
    obtain ⟨-, cls, hcls, hall⟩ := keyOperand_bytes hko
    simp only [clsOf, Option.some.injEq] at hcls
    subst hcls
    rw [show UInt8.ofNat b.inputs.size = b.inputs.size.toUInt8 from rfl, srcOf_input _ _ hb, hBi _ (by simp),
      get_push_eq]
    have hc := bytes_code (Or.inr (Or.inr (Or.inr rfl))) (hall j (by rw [hs]; simp only [e8, e16, e32, e64]; omega))
    have he : (Ew.signed Ew.i64 (Ew.elem Ew.i64 cb j)).toUInt64 = Ew.elem Ew.i64 cb j := by
      simp [Ew.signed, Ew.i64, Ew.u8, Ew.i16, Ew.i32]
    rw [he] at hc
    simp only [e64, Nat.reduceMul] at hc
    exact ⟨hc.1, by have := hc.2; omega⟩

/-! ## `composeKey`'s content -/

/-- `c.column` keeps the code's count. -/
theorem column_n {c : Code} {t : QAtomicType} {m : USize} {e : Enc} (h : c.column = some (t, (m, e))) : m = c.n := by
  unfold Code.column at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    exact h.2.1.symm

/-- **`composeKey`'s arithmetic**: element `i` of `s₁ · d₂ + s₂` at `i64`, codes below their bounds and the
    product below `2⁶³`, is the naturals' `c₁ · d₂ + c₂`. -/
theorem key_elem {S₁ S₂ : ByteArray} {d₁ d₂ : Nat} {n : USize} {i : Nat} (hi : i < n.toNat) (h63 : d₁ * d₂ < 2 ^ 63)
    (hA : (Ew.elem Ew.i64 S₁ i).toNat < d₁) (hB : (Ew.elem Ew.i64 S₂ i).toNat < d₂) :
    (Ew.elem Ew.i64 (Ew.val Ew.add Ew.i64 Ew.vv Int64.minValue
      (Ew.val Ew.mul Ew.i64 Ew.va Int64.minValue S₁ (atomBytes Ew.i64 d₂.toUInt64) n) S₂ n) i).toNat =
      (Ew.elem Ew.i64 S₁ i).toNat * d₂ + (Ew.elem Ew.i64 S₂ i).toNat := by
  have h64 : ∀ v : UInt64, UInt64.ofNat (v.toNat % 2 ^ (8 * Ew.width Ew.i64)) = v := fun v => by
    rw [show 8 * Ew.width Ew.i64 = 64 by decide, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  have hva : Ew.shapeIdx Ew.va i = (i, 0) := by simp [Ew.shapeIdx, Ew.va, Ew.vv]
  have hvv : Ew.shapeIdx Ew.vv i = (i, i) := by simp [Ew.shapeIdx]
  have hd₁ : d₁ ≤ d₁ * d₂ := Nat.le_mul_of_pos_right _ (by omega)
  have hd₂ : d₂ ≤ d₁ * d₂ := Nat.le_mul_of_pos_left _ (by omega)
  have hK : (Ew.elem Ew.i64 (atomBytes Ew.i64 d₂.toUInt64) 0).toNat = d₂ := by
    rw [elem_atomBytes_i64]; simp; omega
  have hAB : (Ew.elem Ew.i64 S₁ i).toNat * d₂ + d₂ ≤ d₁ * d₂ := by
    have := Nat.mul_le_mul_right d₂ (show (Ew.elem Ew.i64 S₁ i).toNat + 1 ≤ d₁ from hA)
    rwa [Nat.add_one_mul] at this
  have hM : (Ew.elem Ew.i64 (Ew.val Ew.mul Ew.i64 Ew.va Int64.minValue S₁ (atomBytes Ew.i64 d₂.toUInt64) n) i).toNat =
      (Ew.elem Ew.i64 S₁ i).toNat * d₂ := by
    rw [elem_val _ _ _ _ _ _ _ hi, h64, hva]
    dsimp only
    rw [(valStep_key _ _ (by omega) (by omega)).1 (by rw [hK]; omega), hK]
  rw [elem_val _ _ _ _ _ _ _ hi, h64, hvv]
  dsimp only
  rw [(valStep_key _ _ (by rw [hM]; omega) (by omega)).2 (by rw [hM]; omega), hM]

theorem srcOf_input' (B : Ew.Build) (n : USize) {i : Nat} (h : i < 128) :
    srcOf B n (UInt8.ofNat i) = B.inputs[i]! := srcOf_input B n h

theorem srcOf_slot' (B : Ew.Build) (n : USize) {m : Nat} (hm : m < B.stages.size) (h128 : m < 128) :
    srcOf B n (Ew.slot0 + UInt8.ofNat m) =
      stageRun B.stages[m]! (srcOf { B with stages := B.stages.extract 0 m } n) n := srcOf_slot B n hm h128

/-- **`composeKey`'s two arithmetic stages read back**: a build whose stages are the first operand's, the `mul`
    by the atom, the second operand's (`hS4`), the `add` stage over them reads, at element `i`, `c₁ · d₂ + c₂`. -/
theorem key_chain (B1 B4 : Ew.Build) (st : Ew.Stage) (s₁ s₂ : UInt8) (xb : ByteArray) {d₁ d₂ : Nat} {n : USize}
    (cA cB : Nat → Nat) (h63 : d₁ * d₂ < 2 ^ 63) (hs1 : B1.stages.size ≤ 1) (hi1 : B1.inputs.size = 1)
    (hI4 : B4.inputs = (B1.inputs.push (atomBytes Ew.i64 d₂.toUInt64)).push xb)
    (hS4z : B1.stages.size + 1 ≤ B4.stages.size) (hB4 : B4.stages.size < 128)
    (hS4 : ∀ j < B1.stages.size + 1, B4.stages[j]! = (B1.stages.push
      { engine := Ew.eVal, op := Ew.mul, cls := Ew.i64, shape := Ew.va, a := s₁, b := B1.inputs.size.toUInt8,
        nul := Int64.minValue })[j]!)
    (hB1 : ∀ B : Ew.Build, (∀ i < B1.inputs.size, B.inputs[i]! = B1.inputs[i]!) →
      (∀ j < B1.stages.size, B.stages[j]! = B1.stages[j]!) → B1.stages.size ≤ B.stages.size →
      ∀ j < n.toNat, (Ew.elem Ew.i64 (srcOf B n s₁) j).toNat = cA j ∧ cA j < d₁)
    (hB2 : ∀ B : Ew.Build, (∀ i < B4.inputs.size, B.inputs[i]! = B4.inputs[i]!) →
      (∀ j < B4.stages.size, B.stages[j]! = B4.stages[j]!) → B4.stages.size ≤ B.stages.size →
      ∀ j < n.toNat, (Ew.elem Ew.i64 (srcOf B n s₂) j).toNat = cB j ∧ cB j < d₂)
    {i : Nat} (hi : i < n.toNat) :
    (Ew.elem Ew.i64 (Ew.val Ew.add Ew.i64 Ew.vv Int64.minValue
      (srcOf { stages := (B4.stages.push st).extract 0 B4.stages.size, inputs := B4.inputs } n
        (Ew.slot0 + UInt8.ofNat B1.stages.size))
      (srcOf { stages := (B4.stages.push st).extract 0 B4.stages.size, inputs := B4.inputs } n s₂) n) i).toNat =
      cA i * d₂ + cB i ∧ cA i < d₁ ∧ cB i < d₂ := by
  have hx : ((B4.stages.push st).extract 0 B4.stages.size).size = B4.stages.size := by simp
  have hget : ∀ j < B4.stages.size, ((B4.stages.push st).extract 0 B4.stages.size)[j]! = B4.stages[j]! :=
    fun j hj => by rw [get_extract_lt _ hj (by simp), get_push_lt _ _ hj]
  obtain ⟨hb, hbd⟩ := hB2 { stages := (B4.stages.push st).extract 0 B4.stages.size, inputs := B4.inputs }
    (fun _ _ => rfl) hget (by simp) i hi
  have hat : (B1.inputs.push (atomBytes Ew.i64 d₂.toUInt64))[1]! = atomBytes Ew.i64 d₂.toUInt64 := by
    have := get_push_eq B1.inputs (atomBytes Ew.i64 d₂.toUInt64); rwa [hi1] at this
  rw [srcOf_slot' _ _ (by rw [hx]; omega) (by omega)]
  dsimp only
  rw [hget _ (by omega), hS4 _ (by omega), get_push_eq, stageRun_val rfl]
  dsimp only
  rw [show B1.inputs.size.toUInt8 = UInt8.ofNat 1 by rw [hi1], srcOf_input' _ _ (by omega)]
  dsimp only
  rw [show B4.inputs[1]! = atomBytes Ew.i64 d₂.toUInt64 by rw [hI4, get_push_lt _ _ (by simp [hi1]), hat]]
  obtain ⟨ha, had⟩ := hB1
    { stages := ((B4.stages.push st).extract 0 B4.stages.size).extract 0 B1.stages.size, inputs := B4.inputs }
    (fun i hi' => by dsimp only; rw [hI4, get_push_lt _ _ (by simp; omega), get_push_lt _ _ hi'])
    (fun j hj => by
      dsimp only
      rw [get_extract_lt _ hj (by rw [hx]; omega), hget _ (by omega), hS4 _ (by omega), get_push_lt _ _ hj])
    (by simp; omega) i hi
  rw [key_elem hi h63 (by rw [ha]; exact had) (by rw [hb]; exact hbd), ha, hb]
  exact ⟨rfl, had, hbd⟩

/-- **`composeKey` of two codes' columns**: where it answers, the counts agree, the bound is below `2⁶³`, the key
    has `⌈n·w/8⌉` bytes at the lane `w = idWidthOf (d₁ · d₂)`, and key `i` is `c₁ · d₂ + c₂`, `c₁ < d₁`,
    `c₂ < d₂`. -/
theorem composeKey_code (a b : Code)
    (ha : laneOK(a.w) ∧
      a.b.size = (a.n.toNat * a.w + 7) / 8 ∧ (a.w < 8 → ∀ i < a.n.toNat, Column.idAt a.b a.w i < max a.card 2))
    (hb : laneOK(b.w) ∧
      b.b.size = (b.n.toNat * b.w + 7) / 8 ∧ (b.w < 8 → ∀ i < b.n.toNat, Column.idAt b.b b.w i < max b.card 2))
    {t₁ t₂ : QAtomicType} {m₁ m₂ : USize} {e₁ e₂ : Enc} (h₁ : a.column = some (t₁, (m₁, e₁)))
    (h₂ : b.column = some (t₂, (m₂, e₂))) {d₁ d₂ : Nat} (h2₁ : 2 ≤ d₁) (h2₂ : 2 ≤ d₂) {k : ByteArray}
    (hk : composeKey t₁ m₁ e₁ d₁ d₂ t₂ m₂ e₂ = some k) :
    b.n = a.n ∧ d₁ * d₂ < 2 ^ 63 ∧ k.size = (a.n.toNat * Column.idWidthOf (d₁ * d₂) + 7) / 8 ∧
      ∀ i < a.n.toNat, Column.idAt k (Column.idWidthOf (d₁ * d₂)) i =
        Column.idAt a.b a.w i * d₂ + Column.idAt b.b b.w i ∧ Column.idAt a.b a.w i < d₁ ∧
          Column.idAt b.b b.w i < d₂ := by
  have hd : 2 ≤ d₁ * d₂ := Nat.le_trans h2₁ (Nat.le_mul_of_pos_right _ (by omega))
  obtain rfl := column_n h₁
  obtain rfl := column_n h₂
  simp only [composeKey, bind, Option.bind_eq_some_iff] at hk
  obtain ⟨⟨u₁, neg₁, hi₁⟩, hko₁, ⟨u₂, neg₂, hi₂⟩, hko₂, _, hg, ⟨B1, s₁⟩, hks₁, ⟨B4, s₂⟩, hks₂, hk⟩ := hk
  simp only [guard, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at hg
  split at hg
  case isFalse => exact absurd hg (by intro h; cases h)
  rename_i hp
  obtain ⟨⟨hn, h63⟩, hcond⟩ := hp
  have hd₁ : a.n = 0 ∨ (neg₁ = false ∧ hi₁ < d₁) := by
    rcases hcond with h | ⟨⟨⟨h1, h2⟩, -⟩, -⟩
    · exact .inl h
    · exact .inr ⟨h1, h2⟩
  have hd₂ : b.n = 0 ∨ (neg₂ = false ∧ hi₂ < d₂) := by
    rcases hcond with h | ⟨⟨-, h3⟩, h4⟩
    · exact .inl (hn.trans h)
    · exact .inr ⟨h3, h4⟩
  simp only [Ew.Build.input, Ew.Build.add] at hks₂ hk
  obtain ⟨hI1, -, hS1b, -, hB1⟩ := keySource_code a ha.1 ha.2.1 ha.2.2 h₁ hko₁ hd₁ h2₁ hks₁ (by simp) (by simp)
  rw [← hn] at hks₂
  obtain ⟨hI2, hS2a, hS2b, hS2c, hB2⟩ := keySource_code b hb.1 hb.2.1 hb.2.2 h₂ hko₂ hd₂ h2₂ hks₂
    (by simp [hI1]) (by simp at hS1b ⊢; omega)
  simp only [Option.some.injEq] at hk
  subst hk
  simp only [Array.size_push] at hS2a hS2b hS2c
  have hs1 : B1.stages.size ≤ 1 := by simpa using hS1b
  have hi1 : B1.inputs.size = 1 := by simp [hI1]
  have hw0 : Column.idWidthOf (d₁ * d₂) ≠ 0 := fun h0 => by
    have := lt_two_pow_idWidthOf (L := d₁ * d₂) (k := 1) (by omega) (by omega); rw [h0] at this; omega
  have hlane : laneOK(Column.idWidthOf (d₁ * d₂)) := by
    have := laneWidth_cases (Column.widthFor (d₁ * d₂ - 1)); unfold Column.idWidthOf at hw0 ⊢; omega
  have hw8 : (UInt8.ofNat (Column.idWidthOf (d₁ * d₂))).toNat = Column.idWidthOf (d₁ * d₂) := u8_ofNat (by omega)
  rw [run_last, stageRun_pack rfl]
  dsimp only
  simp only [Nat.toUInt8_eq, hw8]
  refine ⟨hn, h63, packIds_size hlane _ _, fun i hi => ?_⟩
  -- the add stage, then the mul stage, each read back by `srcOf_slot'`
  have hB4 : B4.stages.size < 128 := by omega
  rw [srcOf_slot' _ _ (by simp) hB4, get_push_eq, stageRun_val rfl]
  dsimp only
  obtain ⟨hk1, hA, hB⟩ := key_chain B1 B4
    { engine := Ew.eVal, op := Ew.add, cls := Ew.i64, shape := Ew.vv, a := Ew.slot0 + UInt8.ofNat B1.stages.size,
      b := s₂, nul := Int64.minValue } s₁ s₂ b.b (n := a.n)
    (fun j => Column.idAt a.b a.w j) (fun j => Column.idAt b.b b.w j) h63 hs1 hi1 hI2 (by omega) hB4 hS2c hB1
    (by rw [hn] at hB2; exact hB2) hi
  exact ⟨ePack_idAt _ hi hA hB (by omega) hk1, hA, hB⟩

end LeetQ.Rel.Alg
