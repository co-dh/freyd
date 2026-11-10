/-
  Totality and well-formedness of the grade kernel behind `Ops.rank` (`gradeColumn`), and the count
  `razeColumn` answers (`raze_len`). Each `_isSome` names the weakest hypothesis under which the kernel
  body answers; each declining input is a hypothesis.
-/
import LeetQ.Rel.KernelWF.Raze
import QLean.Kernel.Scan
import QLean.Kernel.Search
import QLean.Dep.Table

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Kernel.Order LeetQ.Rel

private theorem toUSize_small {k : Nat} (h : k ≤ 64) : k.toUSize.toNat = k := by
  simp only [Nat.toUSize]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt h (by decide)) USize.le_size)

private theorem toUSize_lt {k : Nat} (h : k < USize.size) : k.toUSize.toNat = k := by
  simp only [Nat.toUSize]; exact Nat.mod_eq_of_lt h

/-! ## Sizes of the grade family -/

/-- `indices` writes one long per index. -/
theorem indices_size (is : List Nat) : (indices is).size = is.length * 8 := by
  simp only [indices]; rw [foldl_size ByteArray.size _ 8 (fun _ _ => Column.pushBits_size ..)]; simp

/-- `grade` answers one long per element it reads: `n` clamped to what the payload holds. -/
theorem grade_size (k : Scan.Kind) (desc : Bool) (n : USize) (b : ByteArray) :
    (grade k desc n b).size = min n.toNat (k.avail b) * 8 := by
  simp [grade, indices_size]

/-- `invert` answers one long per long of the permutation. -/
theorem invert_size (p : ByteArray) : (invert p).size = p.size / 8 * 8 := by
  simp [invert, indices_size]

theorem ranks_size (k : Scan.Kind) (n : USize) (b : ByteArray) :
    (ranks k n b).size = min n.toNat (k.avail b) * 8 := by
  simp only [ranks, invert_size, grade_size]; omega

theorem gradeSyms_size (desc : Bool) (blob : ByteArray) (offs : Array Nat) :
    (gradeSyms desc blob offs).size = (offs.size - 1) * 8 := by
  simp [gradeSyms, indices_size]

theorem gradeGuid_size (desc : Bool) (b : ByteArray) : (gradeGuid desc b).size = b.size / 16 * 8 := by
  simp [gradeGuid, indices_size]

/-- A kind other than the bitmap's holds a whole element in `width` bytes. -/
private theorem avail_of_ne_bit {k : Scan.Kind} (hk : k ≠ .bit) (b : ByteArray) :
    k.avail b = b.size / k.width := by
  cases k <;> simp_all [Scan.Kind.avail]

private theorem width_pos (k : Scan.Kind) : 0 < k.width ∧ k.width ≤ 8 := by
  cases k <;> simp [Scan.Kind.width]

/-- `n` elements of `width` bytes are all `grade` reads. -/
private theorem min_avail {k : Scan.Kind} (hk : k ≠ .bit) {n : Nat} {b : ByteArray}
    (hb : n * k.width ≤ b.size) : min n (k.avail b) = n := by
  rw [avail_of_ne_bit hk]
  have := (Nat.le_div_iff_mul_le (width_pos k).1).2 hb
  omega

theorem gradeIds_size (desc : Bool) (n : USize) (dict : ByteArray) (dof : Array Nat) (ids : ByteArray) :
    (gradeIds desc n dict dof ids).size = n.toNat * 8 := by
  simp only [gradeIds, grade_size]
  rw [min_avail (by decide)]
  rw [foldl_size ByteArray.size _ 4 (fun _ _ => Column.pushBits_size ..)]; simp [Scan.Kind.width]

/-- The decoded Frame-of-Reference column `gradeFoR`/`ranksFoR` read holds all `n` elements. -/
private theorem min_avail_decode {k : Scan.Kind} (hk : k ≠ .bit) {n : Nat} (hn : n < USize.size)
    (md pk : ByteArray) : min n.toUSize.toNat (k.avail (Coc.decode k.width.toUSize md pk n.toUSize)) = n := by
  rw [toUSize_lt hn]
  exact min_avail hk (by
    rw [decode_size, toUSize_lt hn, toUSize_small (by have := (width_pos k).2; omega)]; exact Nat.le_refl _)

/-! ## `gradeColumn`: `<x`, `>x`, `rank x` -/

/-- **`gradeColumn` answers `n` longs** on a well-formed payload whose count fits a `USize`. -/
theorem gradeColumn_wf {t : QAtomicType} {desc rank : Bool} {n : Nat} {e v : Enc}
    (hn : n < USize.size) (hw : Enc.WF t n e) (h : gradeColumn t desc n e rank = some v) :
    Enc.WF .long n v := by
  have key : ∀ b : ByteArray, b.size = n * 8 → Enc.WF .long n (.bytes b) :=
    fun b hb => wf_bytes (w := 8) (by decide) rfl hb
  have hu := toUSize_lt hn
  unfold gradeColumn at h
  cases rank <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> split at h
  all_goals first
    | (cases h; apply key; simp only [Enc.WF] at hw; simp only [invert_size, gradeSyms_size] <;> omega)
    | (cases h; apply key; simp only [invert_size, gradeIds_size, hu] <;> omega)
    | (cases h; apply key; simp only [Enc.WF] at hw
       simp only [ranks_size, grade_size, Scan.Kind.avail, hu] <;> omega)
    | (obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
       obtain ⟨b', hb', hs⟩ := bytesOf_size (w := 16) (by decide) rfl hw (countFits_of_lt hn)
       rw [hb] at hb'; cases hb'
       apply key; simp only [invert_size, gradeGuid_size, hs] <;> omega)
    | (split at h
       · cases h
       rename_i k hk
       split at h
       · cases h
       rename_i hbit
       have hk' : k ≠ .bit := fun e => by simp [e] at hbit
       split at h
       · cases h; apply key
         simp only [ranksFoR, gradeFoR, ranks_size, grade_size, min_avail_decode hk' hn]
       · split at h
         · rename_i b hb
           split at h
           · cases h
           rename_i hlt
           cases h; apply key
           simp only [ranks_size, grade_size, hu, min_avail hk' (Nat.le_of_not_lt hlt)]
         · cases h)

/-- **`gradeColumn` answers** every well-formed payload whose count fits a `USize`, except a general
    list's: `orderKind` has no key for it. -/
theorem gradeColumn_isSome {t : QAtomicType} {desc rank : Bool} {n : Nat} {e : Enc}
    (hn : n < USize.size) (hw : Enc.WF t n e) (hg : t ≠ .general) :
    (gradeColumn t desc n e rank).isSome := by
  unfold gradeColumn
  cases rank <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split
  all_goals first
    | rfl
    | (obtain ⟨b, hb, -⟩ := bytesOf_size (w := 16) (by decide) rfl hw (countFits_of_lt hn); simp [hb])
    | (split
       · rename_i hk
         rcases orderKind_eq_none.1 hk with rfl | rfl | rfl
         · cases e <;> simp_all [Enc.WF, QAtomicType.width]
         · simp_all
         · exact absurd rfl hg
       rename_i k hk
       split
       · rename_i hbit
         have : t = .boolean := by cases t <;> simp_all [orderKind]
         subst this
         cases e <;> simp_all [Enc.WF]
       rename_i hbit
       have hk' : k ≠ .bit := fun e => by simp [e] at hbit
       have hwk : t.width = some k.width := by
         cases t <;> simp [orderKind] at hk <;> subst hk <;> rfl
       have htb : t ≠ .boolean := by rintro rfl; simp [orderKind] at hk; exact hk' hk.symm
       split
       · rfl
       · obtain ⟨b, hb, hs⟩ := bytesOf_size htb hwk hw (countFits_of_lt hn)
         simp [hb, hs])

/-! ## `razeColumn`'s count: the sum of the parts' counts -/

/-- A fold that adds `f a` a step adds their sum. -/
private theorem foldl_add_sum {α σ : Type} (sz : σ → Nat) (f : α → Nat) (g : σ → α → σ)
    (hg : ∀ s a, sz (g s a) = sz s + f a) : ∀ (l : List α) (s : σ), sz (l.foldl g s) = sz s + (l.map f).sum
  | [], s => by simp
  | a :: l, s => by simp only [List.foldl, List.map_cons, List.sum_cons]; rw [foldl_add_sum sz f g hg l, hg]; omega

/-- An `Option` pass whose every answer measures `u` as its argument measures `v` keeps the sum. -/
private theorem mapM_sum {α β : Type} {f : α → Option β} (u : β → Nat) (v : α → Nat) :
    ∀ (l : List α) (qs : List β), (∀ a ∈ l, ∀ b, f a = some b → u b = v a) → l.mapM f = some qs →
      (qs.map u).sum = (l.map v).sum
  | [], qs, _, h => by simp at h; subst h; rfl
  | a :: l, qs, hf, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some x =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some xs =>
        simp [ha, hl] at h; subst h
        simp [hf a (by simp) x ha, mapM_sum u v l xs (fun a' ha' b hb => hf a' (by simp [ha']) b hb) hl]

private theorem mapM_sum_arr {α β : Type} {f : α → Option β} (u : β → Nat) (v : α → Nat) {cs : Array α}
    {qs : Array β} (hf : ∀ a ∈ cs, ∀ b, f a = some b → u b = v a) (h : cs.mapM f = some qs) :
    (qs.toList.map u).sum = (cs.toList.map v).sum := by
  rcases cs with ⟨l⟩
  rw [Array.mapM_eq_mapM_toList] at h
  cases hq : l.mapM f with
  | none => simp [hq] at h
  | some ql =>
    simp [hq] at h; subst h
    simpa using mapM_sum u v l ql (fun a ha => hf a (by simpa using ha)) hq

private theorem foldl_fst_sum {β : Type} (l : List (Nat × β)) (a : Nat) :
    l.foldl (fun s c => s + c.1) a = a + (l.map (·.1)).sum :=
  foldl_add_sum (σ := Nat) id (fun c : Nat × β => c.1) (fun s c => s + c.1) (fun _ _ => rfl) l a

private theorem sum_fst {β : Type} (cs : Array (Nat × β)) :
    cs.foldl (fun s c => s + c.1) 0 = (cs.toList.map (·.1)).sum := by
  rw [← Array.foldl_toList, foldl_fst_sum, Nat.zero_add]

/-- **`razeColumn` counts its answer as the sum of its parts' counts**, under `razeColumn_wf`'s
    hypothesis on the parts (`hN` is not needed). -/
theorem razeColumn_count {t : QAtomicType} {cs : Array (Nat × Enc)}
    (h : ∀ c ∈ cs, Enc.WF t c.1 c.2 ∧ c.1 < USize.size) {n : Nat} {e : Enc}
    (hv : razeColumn t cs = some (.vector t n e none)) : n = cs.foldl (fun s c => s + c.1) 0 := by
  rw [sum_fst]
  unfold razeColumn at hv
  split at hv
  · cases hv
  cases t
  case boolean =>
    dsimp only at hv
    split at hv
    · rename_i ps hps
      cases hv
      rw [sum_fst, mapM_sum_arr (·.1) (·.1) (fun a _ b hb => by
        rcases a with ⟨k, e'⟩; cases e' <;> simp at hb; subst hb; rfl) hps]
    · cases hv
  case symbol =>
    dsimp only at hv
    split at hv
    · rename_i ps hps
      simp only [concatSyms] at hv; cases hv
      rw [← Array.foldl_toList, foldl_add_sum (fun p : ByteArray × Array Nat => p.2.size) (fun p => p.2.size - 1) _
        (fun s a => by rcases s with ⟨blob, offs⟩; rcases a with ⟨b, o⟩; simp)]
      rw [mapM_sum_arr (fun p => p.2.size - 1) (·.1) (fun a ha b hb => by
        have hw := (h a ha).1; rcases a with ⟨k, e'⟩; cases e' <;> simp at hb; subst hb
        simp [Enc.WF] at hw; simp [hw]) hps]
      simp
    · split at hv
      · rename_i ps hps
        simp only [concatEnum] at hv; cases hv
        rw [← Array.foldl_toList, foldl_fst_sum]
        rw [← mapM_sum_arr (·.1) (·.1) (fun a _ b hb => by
          rcases a with ⟨k, e'⟩; dsimp only at hb; split at hb <;> first | (cases hb; rfl) | cases hb) hps]
        simp only [id, Nat.zero_add]
        congr 1
        apply List.ext_getElem (by simp)
        intro i h1 h2
        simp only [List.getElem_map, Array.getElem_toList, Array.getElem_mapIdx]
        split
        · rfl
        · split <;> rfl
      · cases hv
  all_goals
    dsimp only at hv
    generalize hE : encodedParts _ cs = E at hv
    rcases E with _ | ⟨alp, m, ns, ms, ps, as⟩
    all_goals
      try dsimp only [QAtomicType.width] at hv
      repeat' split at hv
      all_goals first
        | (cases hv; done)
        | (cases hv; exact sum_fst cs)
        | (cases hv; obtain ⟨-, rfl, rfl, -⟩ := encodedParts_spec hE; simp)
        | contradiction

end LeetQ.Rel.KernelWF

namespace LeetQ.Rel.Ops

open QLean QLean.Dep QLean.Kernel

variable {t : QAtomicType}

/-- The place of `i` in the stable ascending order of `R` (`Carrier.le`): the positions before it, each `j`
    whose value is at most `i`'s and either earlier or strictly smaller. -/
def rankAt {n : Nat} (R : Arr t n) (i : Fin n) : Int64 :=
  Int64.ofNat (Fin.foldl n (fun c j => if Table.Carrier.le (R.get j) (R.get i) &&
    (decide (j < i) || !Table.Carrier.le (R.get i) (R.get j)) then c + 1 else c) 0)

/-- `rank x` = `<<x`, key kept: the place of each element in the ascending order, on the domain
    `gradeColumn` orders by value (every atom but a general list, the witness `hg`). The kernel wherever the
    count fits the `USize` every kernel takes; past it, where no kernel runs, `rankAt` on the array. -/
def rank {n : Nat} (R : Arr t n) (hg : t ≠ .general) : Arr .long n :=
  if h : n < USize.size then
    Arr.mk ((gradeColumn t false n R.enc (rank := true)).get (KernelWF.gradeColumn_isSome h R.wf hg))
      (KernelWF.gradeColumn_wf h R.wf (Option.some_get _).symm)
  else colFn n (rankAt R)

end LeetQ.Rel.Ops
