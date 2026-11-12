/-
  What `composeKey` CONTAINS: the chain it builds, read back stage by stage. First the program's stage
  count, for a build of any number of stages (qlean's `Verify.prog_one` is the build of none).
-/
import QLean.Verify.Chain
import QLean.Verify.Where
import QLean.Verify.Group
import QLean.Verify.Ids

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

end LeetQ.Rel.Alg
