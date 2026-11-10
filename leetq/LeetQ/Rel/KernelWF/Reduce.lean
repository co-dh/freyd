/-
  Totality and well-formedness of the kernels behind `Scan.lean`'s `Ops.*`: the grade (`grade`,
  `rank`, `permute`'s index, `sort`'s fallback, `xasc`), the folds (`over`, `lastBy`'s least size),
  the grouped fold (`overBy`), and the sizes `setIds` and `where` read. Each `_isSome` names the
  weakest hypothesis under which the kernel body answers; each declining input is a hypothesis.
-/
import LeetQ.Rel.KernelWF.Dyad
import QLean.Kernel.Scan
import QLean.Kernel.Search

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

/-! ## `where`, as `setIds` and `where` read it -/

/-- `whereBits` writes one long per set bit among the first `n`. -/
theorem whereBits_size_le (n : USize) (b : ByteArray) : (whereBits n b).size ≤ n.toNat * 8 := by
  simp only [whereBits]
  rw [foldl_size ByteArray.size _ 8 (fun _ _ => Column.pushBits_size ..)]
  simpa using Nat.mul_le_mul_right 8 (Nat.le_trans (List.length_filter_le _ _) (by simp))

/-! ## `overColumn`: `f/x` -/

/-- `Coc.narrowed` always answers: it wraps or clamps, never declines. -/
theorem narrowed_isSome (op : Coc.Over) (t : QAtomicType) (whole : Bool) (v : Int64) :
    (Coc.narrowed op t whole v).isSome := by
  unfold Coc.narrowed; repeat' split
  all_goals rfl

/-- **`overColumn` answers** a well-formed payload of a type with an integral null (any layout), a
    boolean (its bitmap), or a dense `byte`/`char` payload. It declines the float types at every
    layout (no `denseNul`, no `nullOf`), and `byte`/`char` encoded as Frame of Reference (no `nullOf`). -/
theorem overColumn_isSome {op : Coc.Over} {t : QAtomicType} {n : Nat} {e : Enc} (hw : Enc.WF t n e)
    (h : (Coc.nullOf t).isSome ∨ t = .boolean ∨ ((t = .byte ∨ t = .char) ∧ ∃ b, e = .bytes b)) :
    (overColumn op t n e).isSome := by
  rcases h with h | rfl | ⟨rfl | rfl, b, rfl⟩
  · cases t <;> simp [Coc.nullOf] at h <;> cases e <;>
      simp_all [overColumn, overFoR, Enc.WF, QAtomicType.width, Coc.nullOf, clsOf, Coc.denseNul, narrowed_isSome]
  · cases e <;> simp_all [overColumn, overFoR, Enc.WF, QAtomicType.width, Coc.nullOf]
    cases op <;> simp
  all_goals simp [overColumn, overFoR, clsOf, Coc.denseNul, narrowed_isSome]

/-- q's `f/` of a vector of atoms answers an atom: only a general list's fold is general. -/
theorem resultType_ne_general (op : Coc.Over) (avg : Bool) {t : QAtomicType} (ht : t ≠ .general) :
    (op.resultType avg t).all (· != .general) = true := by
  cases t <;> (try exact absurd rfl ht) <;> cases op <;> cases avg <;> decide

/-- **`overAtom` answers** wherever q types `f/` (`hr`) and `overColumn` reads the column (`overColumn_isSome`'s
    hypothesis): a type with an integral null at any layout, a boolean, a dense `byte`/`char`. No count bound. -/
theorem overAtom_isSome {op : Coc.Over} {t rt : QAtomicType} {n : Nat} {e : Enc} (hr : op.resultType false t = some rt)
    (hw : Enc.WF t n e)
    (h : (Coc.nullOf t).isSome ∨ t = .boolean ∨ ((t = .byte ∨ t = .char) ∧ ∃ b, e = .bytes b)) :
    (overAtom op t rt n e).isSome := by
  have hg : rt ≠ .general := by
    have ht : t ≠ .general := by rintro rfl; simp [Coc.nullOf] at h
    have := resultType_ne_general op false ht; rw [hr] at this; simpa using this
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (overColumn_isSome (op := op) hw h)
  simp [overAtom, hr, hg, hy]


/-! ## `groupedOver`: `select f x by k` -/

/-- Every type q answers `f/` of has a width: no fold answers a symbol, a guid or a general list. -/
theorem resultType_width (op : Coc.Over) (avg : Bool) {t : QAtomicType} (hg : t ≠ .general) :
    ((op.resultType avg t).bind QAtomicType.width).isSome = (op.resultType avg t).isSome := by
  cases t <;> (try exact absurd rfl hg) <;> cases op <;> cases avg <;> rfl

/-- A float fold answers its own type, or a boolean (`all`, `any`). -/
theorem resultType_float (op : Coc.Over) :
    (op.resultType false .float).all (fun r => r == .float || r == .boolean) = true ∧
    (op.resultType false .real).all (fun r => r == .real || r == .boolean) = true := by
  cases op <;> exact ⟨rfl, rfl⟩

/-- `groupCells` writes one cell per group number in `order`: `w` bytes wrapped or clamped, a float
    at four or eight bytes, an average at eight. -/
theorem groupCells_size (kind : GroupCell) (w ng : USize) (m order : ByteArray) :
    (groupCells kind w ng m order).size = order.size / 8 *
      (match kind with | .wrap | .clamp => w.toNat | .float => if w == 4 then 4 else 8 | _ => 8) := by
  simp only [groupCells]
  rw [foldl_size ByteArray.size _ (match kind with | .wrap | .clamp => w.toNat | .float => if w == 4 then 4 else 8 | _ => 8)
    (fun acc i => by cases kind <;> dsimp only <;> (repeat' split) <;> simp [Column.pushBits_size] <;> omega)]
  simp


/-- The float engine's cells: at a type ALP encodes and a verb with a float seed, `op/` answers a
    type four or eight bytes wide that is not a boolean. -/
theorem resultType_floatCells (op : Coc.Over) (t : QAtomicType) :
    (Column.alpEncodes t && op.floatSeed.isSome) = true →
      (op.resultType false t).all (fun r => r != .boolean && (r.width == some 4 || r.width == some 8)) = true := by
  cases op <;> cases t <;> decide

/-- `"b"$x` of a dense `byte` payload answers: one `≠ 0` pass. -/
theorem castByteBool_isSome (m : Nat) (c : ByteArray) : (castColumn .boolean .byte m (.bytes c)).isSome := by
  have hc : Prim.castable .boolean .byte = true := by decide
  have hu : Ew.u8 ≠ Ew.bits := by decide
  simp [castColumn, hc, hu, tickCode, clsOf, mapPass, operandSource]
  try (split <;> simp)

/-- `"b"$x` of a well-formed dense `byte` payload is a well-formed bitmap. -/
theorem castByteBool_wf {m : Nat} {c : ByteArray} {r : Enc} (hm : m < USize.size)
    (h : castColumn .boolean .byte m (.bytes c) = some r) : Enc.WF .boolean m r := by
  have hc : Prim.castable .boolean .byte = true := by decide
  simp [castColumn, hc, tickCode, clsOf] at h
  exact mapPass_wf hm (fun b sa => payload_bits_wf (run_cmp_size ..)) h

/-- `groupedOver`'s last step, the boolean cells packed into a bitmap, always answers. -/
theorem packBool_isSome {p : Prop} [Decidable p] (m : Nat) (c : ByteArray) :
    (if p then castColumn .boolean .byte m (.bytes c) else some (.bytes c)).isSome := by
  split
  · exact castByteBool_isSome m c
  · rfl

/-- **`groupedOver` answers** at every type q types `f/` of (`hr`) that has a fold engine: a type with an
    integral null, `byte`, `char`, or `float`/`real` under a verb with a float seed. A boolean answer
    (`all`/`any`) is packed into a bitmap, which always answers. -/
theorem groupedOver_isSome {op : Coc.Over} {whole : Bool} {t rt : QAtomicType} {gs : Groups} {n : Nat}
    {e : Enc} {ord : ByteArray} (hn : n < USize.size) (hw : Enc.WF t n e) (hr : op.resultType false t = some rt)
    (ht : (Coc.nullOf t).isSome ∨ t = .byte ∨ t = .char ∨ ((t = .float ∨ t = .real) ∧ op.floatSeed.isSome)) :
    (groupedOver op false whole t gs n e ord).isSome := by
  have hg : t ≠ .general := by rintro rfl; simp [Coc.nullOf] at ht
  obtain ⟨w, hrw⟩ : ∃ w, rt.width = some w := by
    have := resultType_width op false hg; rw [hr] at this; simpa [Option.isSome_iff_exists] using this
  obtain ⟨tw, htw, htb⟩ : ∃ w, t.width = some w ∧ t ≠ .boolean := by
    cases t <;> simp_all [Coc.nullOf, QAtomicType.width]
  obtain ⟨b, hb, -⟩ := bytesOf_size htb htw hw (countFits_of_lt hn)
  unfold groupedOver
  rcases ht with h | rfl | rfl | ⟨rfl | rfl, hs⟩
  · cases t <;> simp [Coc.nullOf] at h <;>
      simp_all [overGroupsColumn, clsOf, Coc.denseNul, Coc.nullOf, Column.alpEncodes, packBool_isSome]
  all_goals simp_all [overGroupsColumn, clsOf, Coc.denseNul, Coc.nullOf, guard, Column.alpEncodes, packBool_isSome]

theorem groupedOver_wf {op : Coc.Over} {whole : Bool} {t rt : QAtomicType} {gs : Groups} {n : Nat}
    {e : Enc} {ord : ByteArray} {s : Enc} (hr : op.resultType false t = some rt) (hm : ord.size / 8 < USize.size)
    (h : groupedOver op false whole t gs n e ord = some s) : Enc.WF rt (ord.size / 8) s := by
  unfold groupedOver at h
  rcases hrw : rt.width with _ | w
  · simp [hr, hrw] at h
  simp only [hr, hrw, Option.bind_eq_bind, Option.bind_some, Bool.false_eq_true, ↓reduceIte] at h
  have hwu : (USize.ofNat w).toNat = w :=
    toUSize_small (by cases rt <;> simp [QAtomicType.width] at hrw <;> omega)
  have fin : ∀ c : ByteArray, c.size = ord.size / 8 * w →
      (if rt == .boolean then castColumn .boolean .byte (ord.size / 8) (.bytes c) else some (.bytes c)) = some s →
      Enc.WF rt (ord.size / 8) s := by
    intro c hcs hfin
    split at hfin
    · rename_i hb
      obtain rfl : rt = .boolean := by simpa using hb
      exact castByteBool_wf hm hfin
    · rename_i hb
      cases hfin
      exact wf_bytes (by simpa using hb) hrw hcs
  -- every integral engine writes one `w`-byte cell per group number, wrapped or clamped
  have key : ∀ (t' : QAtomicType) (e' : Enc) (c' : ByteArray), ((overGroupsColumn op t' gs n e').bind fun m =>
      some (groupCells (if Coc.narrowed op t' whole 4294967301 == some (-2147483648) then .clamp else .wrap)
        (USize.ofNat w) gs.count m ord)) = some c' → c'.size = ord.size / 8 * w := by
    intro t' e' c' h'
    obtain ⟨m, -, hm'⟩ := Option.bind_eq_some_iff.1 h'
    cases hm'; rw [groupCells_size]
    by_cases hc : (Coc.narrowed op t' whole 4294967301 == some (-2147483648)) = true
    · rw [if_pos hc]; exact congrArg (ord.size / 8 * ·) hwu
    · rw [if_neg hc]; exact congrArg (ord.size / 8 * ·) hwu
  by_cases hf : (Column.alpEncodes t && op.floatSeed.isSome) = true
  · rw [if_pos hf] at h
    obtain ⟨c, hc, hfin⟩ := Option.bind_eq_some_iff.1 h
    refine fin c ?_ hfin
    have hfc := resultType_floatCells op t hf
    rw [hr] at hfc
    simp only [Option.all_some, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq, hrw,
      Option.some.injEq] at hfc
    obtain ⟨b, -, hb⟩ := Option.bind_eq_some_iff.1 hc
    cases hb
    rw [groupCells_size]; congr 1
    rcases hfc.2 with rfl | rfl
    · exact if_pos (beq_self_eq_true _)
    · have h4 : (4 : USize).toNat = 4 := toUSize_small (k := 4) (by decide)
      exact if_neg fun e => by have := congrArg USize.toNat (beq_iff_eq.1 e); rw [hwu, h4] at this; cases this
  · rw [if_neg hf] at h
    obtain ⟨c, hc, hfin⟩ := Option.bind_eq_some_iff.1 h
    refine fin c ?_ hfin
    unfold Option.orElse at hc
    split at hc
    · rename_i hx; cases hc; exact key t e _ hx
    · split at hc
      · obtain ⟨_, -, hb⟩ := Option.bind_eq_some_iff.1 hc
        exact key .byte _ c hb
      · cases hc

/-- `overBy`'s call: the order `til g` makes the answer `g` cells. -/
theorem groupedOver_tilLongs_wf {op : Coc.Over} {whole : Bool} {t rt : QAtomicType} {gs : Groups} {n : Nat}
    {e : Enc} {g : USize} {s : Enc} (hr : op.resultType false t = some rt)
    (h : groupedOver op false whole t gs n e (tilLongs g) = some s) : Enc.WF rt g.toNat s := by
  have hs : (tilLongs g).size = g.toNat * 8 := by simpa [Enc.WF, QAtomicType.width] using tilLongs_wf g
  have := groupedOver_wf hr (by rw [hs, Nat.mul_div_cancel _ (by decide)]; exact USize.toNat_lt_size g) h
  rwa [hs, Nat.mul_div_cancel _ (by decide)] at this


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

/-! ## Sizes of the scan family's payloads -/

private theorem toList_loop_length (bs : ByteArray) : ∀ (k i : Nat) (r : List UInt8), bs.size - i = k →
    (ByteArray.toList.loop bs i r).length = r.length + k
  | 0, i, r, h => by unfold ByteArray.toList.loop; split <;> first | omega | simp
  | k+1, i, r, h => by
    unfold ByteArray.toList.loop
    split
    · rw [toList_loop_length bs k (i+1) _ (by omega)]; simp only [List.length_cons]; omega
    · omega

theorem byteArray_length_toList (bs : ByteArray) : bs.toList.length = bs.size := by
  unfold ByteArray.toList; simpa using toList_loop_length bs bs.size 0 [] (by simp)

/-- `scan` answers one element per element it reads, at the verb's output width. -/
theorem scan_size (v : Scan.Verb) (k : Scan.Kind) (n : USize) (b : ByteArray) :
    (Scan.scan v k n b).size = min n.toNat (k.avail b) * (Scan.outKind v k).width := by
  cases k <;> cases v <;> simp [Scan.scan, Scan.intScan, Scan.fltScan, Scan.scanOf_size]

/-- `scanBits` packs `scan`'s bytes at `bit`, one bit an element. -/
theorem scanBits_size (v : Scan.Verb) (n : USize) (b : ByteArray) :
    (Scan.scanBits v n b).size = (min n.toNat (b.size * 8) * (Scan.outKind v .bit).width + 7) / 8 := by
  simp only [Scan.scanBits, Column.packBits_size, List.size_toArray, List.length_map, byteArray_length_toList,
    scan_size, Scan.Kind.avail]

/-- A fold that pushes `w` bytes per element of a list. -/
private theorem pushFold_size (w : Nat) (l : List UInt64) :
    (l.foldl (fun acc v => Column.pushBits acc v w) ByteArray.empty).size = l.length * w := by
  rw [foldl_size ByteArray.size _ w (fun _ _ => Column.pushBits_size ..)]; simp

/-- `scanFoR` reads its `n` decoded elements. -/
theorem scanFoR_size (v : Scan.Verb) {k : Scan.Kind} (hk : k ≠ .bit) (n : USize) (m p : ByteArray) :
    (Scan.scanFoR v k n m p).size = n.toNat * (Scan.outKind v k).width := by
  have h8 := width_pos k
  rw [Scan.scanFoR, scan_size, avail_of_ne_bit hk, decode_size, toUSize_small (by omega),
    Nat.mul_div_cancel _ h8.1, Nat.min_self]

/-- `scanAlp` reads its `n` decoded elements, at either float layout. -/
theorem scanAlp_size (v : Scan.Verb) {k : Scan.Kind} (hk : k = .f32 ∨ k = .f64) (n : USize) (m p a : ByteArray) :
    (Scan.scanAlp v k n m p a).size = n.toNat * (Scan.outKind v k).width := by
  rcases hk with rfl | rfl <;>
    simp [Scan.scanAlp, scan_size, Scan.Kind.avail, Coc.alpDecode32, Coc.alpDecode64, pushFold_size,
      Coc.alpElems, Scan.Kind.width]

/-- The window's extremes push `ow` bytes per element. -/
theorem mwinExt_size (keep : UInt64 → UInt64 → Bool) (seed : UInt64) (rd : Nat → UInt64) (w m ow : Nat) :
    (Scan.mwinExt keep seed rd w m ow).size = m * ow := by
  simp only [Scan.mwinExt]; rw [foldl_size ByteArray.size _ ow (fun _ _ => Column.pushBits_size ..)]; simp

/-- The window's integral totals push `ow` bytes per element. -/
theorem mwinSum_size (nl : Option Int64) (fit : Int64 → Int64) (val : Nat → Int64) (w m ow : Nat) :
    (Scan.mwinSum nl fit val w m ow).size = m * ow := by
  simp only [Scan.mwinSum]; rw [foldl_size ByteArray.size _ ow (fun _ _ => Column.pushBits_size ..)]; simp

/-- `mwinBits` answers one element per element it reads, at the verb's width. -/
theorem mwinBits_size (op : Scan.MOp) (k : Scan.Kind) (w n : Nat) (b : ByteArray) :
    (Scan.mwinBits op k w n b).size = min n (k.avail b) * op.width k := by
  unfold Scan.mwinBits
  split
  all_goals first
    | (simp only [Id.run_pure, mwinExt_size, mwinSum_size]; done)
    | (simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, map_pure,
        List.forIn_pure_yield_eq_foldl, pure_bind, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
       rw [show ∀ x : ByteArray, (pure x : Id ByteArray) = x from fun _ => rfl,
         foldl_size ByteArray.size _ (op.width k) ?hg]
       · simp [show ∀ c, (ByteArray.emptyWithCapacity c).size = 0 from fun _ => rfl]
       · intro acc i; dsimp only; (repeat' split) <;> simp [Column.pushBits_size])

theorem mwin_size (op : Scan.MOp) (k : Scan.Kind) (w n : USize) (b : ByteArray) :
    (Scan.mwin op k w n b).size = min n.toNat (k.avail b) * op.width k := mwinBits_size ..

theorem mwinBitmap_size (op : Scan.MOp) (w n : USize) (b : ByteArray) :
    (Scan.mwinBitmap op w n b).size = (min n.toNat (b.size * 8) * op.width .bit + 7) / 8 := by
  simp only [Scan.mwinBitmap, Column.packBits_size, List.size_toArray, List.length_map, byteArray_length_toList,
    mwin_size, Scan.Kind.avail]

theorem mwinFoR_size (op : Scan.MOp) {k : Scan.Kind} (hk : k ≠ .bit) (w n : USize) (m p : ByteArray) :
    (Scan.mwinFoR op k w n m p).size = n.toNat * op.width k := by
  have h8 := width_pos k
  rw [Scan.mwinFoR, mwin_size, avail_of_ne_bit hk, decode_size, toUSize_small (by omega),
    Nat.mul_div_cancel _ h8.1, Nat.min_self]

theorem mwinAlp_size (op : Scan.MOp) {k : Scan.Kind} (hk : k = .f32 ∨ k = .f64) (w n : USize) (m p a : ByteArray) :
    (Scan.mwinAlp op k w n m p a).size = n.toNat * op.width k := by
  rcases hk with rfl | rfl
  · show (Scan.mwin op .f32 w n (Coc.alpDecode32 m p a n)).size = _
    rw [mwin_size]; congr 1
    simp only [Scan.Kind.avail, Coc.alpDecode32, pushFold_size, Coc.alpElems, List.length_map, List.length_range,
      Scan.Kind.width]; omega
  · show (Scan.mwin op .f64 w n (Coc.alpDecode64 m p a n)).size = _
    rw [mwin_size]; congr 1
    simp only [Scan.Kind.avail, Coc.alpDecode64, pushFold_size, Coc.alpElems, List.length_map, List.length_range,
      Scan.Kind.width]; omega

/-! ## `scanKind`: the layout a type is read at -/

theorem scanKind_width {t : QAtomicType} {k : Scan.Kind} (h : scanKind t = some k) : t.width = some k.width := by
  cases t <;> simp [scanKind] at h <;> subst h <;> rfl

theorem scanKind_bit {t : QAtomicType} (h : scanKind t = some .bit) : t = .boolean := by
  cases t <;> simp [scanKind] at h <;> rfl

/-- A float payload's layout is a float one. -/
theorem scanKind_alp {t : QAtomicType} {k : Scan.Kind} {n : Nat} {m p a : ByteArray} (h : scanKind t = some k)
    (hw : Enc.WF t n (.alp m p a)) : k = .f32 ∨ k = .f64 := by
  simp only [Enc.WF] at hw
  rcases hw.1 with rfl | rfl | rfl <;> simp [scanKind] at h <;> simp [← h]

/-- Two types read at one layout have the same well-formed payloads. -/
theorem wf_of_scanKind {t u : QAtomicType} {k : Scan.Kind} {n : Nat} {e : Enc} (ht : scanKind t = some k)
    (hu : scanKind u = some k) (hw : Enc.WF t n e) : Enc.WF u n e := by
  cases t <;> simp [scanKind] at ht <;> subst ht <;> cases u <;> simp [scanKind] at hu <;>
    cases e <;> simp_all [Enc.WF, QAtomicType.width]

/-- A dense payload of `n` elements at `rt`'s own layout, `rt` not boolean, answers well formed. -/
private theorem answer_dense {rt : QAtomicType} {rk : Scan.Kind} {n : Nat} {s : ByteArray}
    (hn : n < USize.size) (hr : scanKind rt = some rk) (hb : rk ≠ .bit) (hs : s.size = n * rk.width) :
    Enc.WF rt n (Enc.answer rt n (.bytes s)) :=
  answer_wf (wf_bytes (fun e => hb (by subst e; simp [scanKind] at hr; simp [← hr])) (scanKind_width hr) hs) hn

/-- `outKind` keeps `bit` only at `bit`. -/
theorem outKind_bit {v : Scan.Verb} {k : Scan.Kind} (h : Scan.outKind v k = .bit) : k = .bit := by
  cases v <;> cases k <;> simp_all [Scan.outKind]

/-! ## `scanColumn`: `f\x` -/

/-- **`scanColumn` answers `n` well-formed elements of `rt`**, `n` fitting a `USize`. -/
theorem scanColumn_wf {v : Prim.Dyadic} {rt et : QAtomicType} {n : Nat} {e out : Enc}
    (hn : n < USize.size) (hw : Enc.WF et n e) (h : scanColumn v rt et n e = some out) : Enc.WF rt n out := by
  have hu := toUSize_lt hn
  unfold scanColumn scanWith at h
  rcases hv : scanVerb v with _ | sv
  · simp [hv] at h
  rcases hk : scanKind et with _ | ek
  · simp [hv, hk] at h
  rcases hr : scanKind rt with _ | rk
  · simp [hv, hk, hr] at h
  simp only [hv, hk, hr] at h
  split at h
  · cases h
  rename_i hg
  have hout : Scan.outKind sv ek = rk := by
    exact Decidable.byContradiction fun hc => hg (by simp [hc])
  split at h
  · cases h
    rename_i hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hf
    obtain ⟨rfl, -⟩ := hf
    have : rk = ek := by rw [← hout]; cases ek <;> rfl
    subst this
    exact wf_of_scanKind hk hr hw
  rw [scanKind_width hk, scanKind_width hr] at h
  by_cases hb : ek = .bit
  · subst hb
    have := scanKind_bit hk; subst this
    obtain ⟨b, rfl⟩ : ∃ b, e = .bits b := by cases e <;> simp [Enc.WF] at hw ⊢
    simp only [Enc.WF] at hw
    have hm : min n.toUSize.toNat (b.size * 8) = n := by rw [hu]; omega
    simp only at h
    split at h
    · cases h
      rename_i hc
      have : rk = .bit := by simpa using hc
      subst this
      have := scanKind_bit hr; subst this
      simp only [Enc.WF, scanBits_size, hm, hout, Scan.Kind.width, Nat.mul_one]
    · cases h
      rename_i hc
      rw [hu]
      refine answer_dense hn hr (by simpa using hc) ?_
      simp only [Scan.scanForm, scan_size, Scan.Kind.avail, hm, hout]
  have hrb : rk ≠ .bit := fun e => hb (outKind_bit (hout.trans e))
  have hbool : et ≠ .boolean := fun e => hb (by subst e; simp [scanKind] at hk; simp [← hk])
  obtain ⟨b', hb', hs⟩ := bytesOf_size hbool (scanKind_width hk) hw (countFits_of_lt hn)
  have fin : ∀ s : ByteArray, s.size = n * (Scan.outKind sv ek).width →
      Enc.WF rt n (Enc.answer rt n.toUSize.toNat (.bytes s)) := fun s hs => by
    rw [hu]; exact answer_dense hn hr hrb (hout ▸ hs)
  cases e
  all_goals first
    | (exfalso; cases et <;> simp [Enc.WF, scanKind] at hw hk hbool; done)
    | skip
  all_goals
    split at h
    all_goals first
      | (exact absurd rfl hb)
      | (exact absurd ‹_› hb)
      | (cases h; done)
      | (simp only at h; cases h; exact fin _ (by simp only [Scan.scanForm]; rw [scanFoR_size _ hb, hu]))
      | (simp only at h; cases h
         exact fin _ (by simp only [Scan.scanForm]; rw [scanAlp_size _ (scanKind_alp hk hw), hu]))
      | (simp only at h; rw [hb'] at h; simp only at h; split at h
         · cases h
         · cases h; exact fin _ (by
             simp only [Scan.scanForm]; rw [scan_size, hu, min_avail hb (Nat.le_of_eq hs.symm)]))

/-- **`scanColumn` answers** a well-formed payload of every type `scanKind` reads (all but symbol, guid,
    general), `n` fitting a `USize`, at a q scan dyad (`+ * & | ^`) and the accumulator type `outKind`
    names. It declines `+\`/`*\` over `char` (`hc`), which q types `'type`. -/
theorem scanColumn_isSome {v : Prim.Dyadic} {rt et : QAtomicType} {n : Nat} {e : Enc} {sv : Scan.Verb}
    {ek : Scan.Kind} (hn : n < USize.size) (hw : Enc.WF et n e) (hv : scanVerb v = some sv)
    (hk : scanKind et = some ek) (hr : scanKind rt = some (Scan.outKind sv ek))
    (hc : ¬(ek = .c8 ∧ (sv = .sums ∨ sv = .prds))) : (scanColumn v rt et n e).isSome := by
  unfold scanColumn scanWith
  simp only [hv, hk, hr, bne_self_eq_false, Bool.false_or]
  rw [if_neg (by simpa using hc)]
  split
  · rfl
  rw [scanKind_width hk, scanKind_width hr]
  by_cases hb : ek = .bit
  · subst hb
    have := scanKind_bit hk; subst this
    obtain ⟨b, rfl⟩ : ∃ b, e = .bits b := by cases e <;> simp [Enc.WF] at hw ⊢
    simp only; split <;> rfl
  have hbool : et ≠ .boolean := fun e => hb (by subst e; simp [scanKind] at hk; simp [← hk])
  obtain ⟨b', hb', hs⟩ := bytesOf_size hbool (scanKind_width hk) hw (countFits_of_lt hn)
  cases e
  all_goals first
    | (exfalso; cases et <;> simp [Enc.WF, scanKind] at hw hk hbool; done)
    | (cases ek <;> first | exact absurd rfl hb | simp [hb', hs])

/-! ## `avgColumn`: `avg x` -/

/-- **`avgColumn` answers** a well-formed payload of every type `scanKind` reads, `n` fitting a `USize`:
    it declines only symbol, guid and general, which have no numeric payload. -/
theorem avgColumn_isSome {t : QAtomicType} {n : Nat} {e : Enc} (hn : n < USize.size) (hw : Enc.WF t n e)
    (ht : (scanKind t).isSome) : (avgColumn t n e).isSome := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 ht
  have htw := scanKind_width hk
  unfold avgColumn
  split
  · rfl
  rw [htw, hk]
  cases k
  case bit =>
    have := scanKind_bit hk; subst this
    cases e <;> simp [Enc.WF, Scan.Kind.raw] at hw ⊢
  all_goals
    have hb : t ≠ .boolean := by rintro rfl; simp [scanKind] at hk
    obtain ⟨b, hb'⟩ := Option.isSome_iff_exists.1 (bytesOf_isSome hb (by simp [htw]) hw)
    cases e
    all_goals first
      | (simp [Scan.Kind.raw, hb']; done)
      | (simp only [Enc.WF] at hw; rcases hw.1 with rfl | rfl | rfl <;> simp [Column.alpEncodes])

/-- **`avgColumn`'s answer is a `float` atom**, so `Ops.avg`'s `Carrier.of? .float` reads it. -/
theorem avgColumn_wf {t : QAtomicType} {n : Nat} {e : Enc} {a : QAtom} (h : avgColumn t n e = some a) :
    (QLean.Dep.Carrier.of? .float (.atom a)).isSome := by
  rw [← avgColumn_type h]; exact QLean.Dep.Carrier.of?_type a

/-! ## `mwinColumn`: `w mop x` -/

theorem readKind_width (op : Scan.MOp) (k : Scan.Kind) : (op.readKind k).width = k.width := by
  cases op <;> cases k <;> rfl

theorem readKind_bit {op : Scan.MOp} {k : Scan.Kind} (h : op.readKind k = .bit) : k = .bit := by
  cases op <;> cases k <;> simp_all [Scan.MOp.readKind, Scan.Kind.raw]

theorem mwinType_boolean {op : Scan.MOp} {t : QAtomicType} (h : mwinType op t = some .boolean) : t = .boolean := by
  cases op <;> cases t <;> simp [mwinType, scanKind] at h ⊢

/-- Each type q answers a window at has a layout, and the verb writes at that layout's width. -/
theorem mwinType_layout {op : Scan.MOp} {t rt : QAtomicType} (h : mwinType op t = some rt) :
    ∃ k rk, scanKind t = some k ∧ scanKind rt = some rk ∧ op.width (op.readKind k) = rk.width := by
  cases op <;> cases t <;> simp [mwinType, scanKind] at h <;> subst h <;>
    simp [scanKind, Scan.MOp.width, Scan.MOp.readKind, Scan.outKind, Scan.Kind.raw, Scan.Kind.width]

/-- **`mwinColumn` answers** a well-formed payload, `n` fitting a `USize`, at every type q types the
    window verb at (`mwinType`: it has none for symbol, guid, general, nor `char` under
    `msum`/`mavg`/`mdev`) and every window of at least one; a window `0` is declined (`hw1`). -/
theorem mwinColumn_isSome {op : Scan.MOp} {t : QAtomicType} {w n : Nat} {e : Enc} (hn : n < USize.size)
    (hw : Enc.WF t n e) (hr : (mwinType op t).isSome) (hw1 : 1 ≤ w) : (mwinColumn op t w n e).isSome := by
  obtain ⟨rt, hrt⟩ := Option.isSome_iff_exists.1 hr
  obtain ⟨k, rk, hk, hrk, hwd⟩ := mwinType_layout hrt
  have htw := scanKind_width hk
  unfold mwinColumn
  simp only [hrt, hk, htw, Option.map_some, hrk]
  split
  · rename_i hc; simp [hwd] at hc <;> omega
  by_cases hb : t = .boolean
  · subst hb
    have : k = .bit := by simp [scanKind] at hk; simp [← hk]
    subst this
    obtain ⟨b, rfl⟩ : ∃ b, e = .bits b := by cases e <;> simp [Enc.WF] at hw ⊢
    have : op.readKind .bit = .bit := by cases op <;> rfl
    simp only [this]
    split <;> rfl
  have hK : op.readKind k ≠ .bit := fun e => hb (scanKind_bit ((readKind_bit e) ▸ hk))
  obtain ⟨b', hb', hs⟩ := bytesOf_size hb htw hw (countFits_of_lt hn)
  cases e
  all_goals first
    | (exfalso; cases t <;> simp [Enc.WF, scanKind] at hw hk hb; done)
    | (split
       all_goals first
         | exact absurd ‹_› hK
         | (simp [hb', hs]; done)
         | simp)

/-- **`mwinColumn` answers `n` well-formed elements** of the type `mwinType` names. -/
theorem mwinColumn_wf {op : Scan.MOp} {t rt : QAtomicType} {w n : Nat} {e out : Enc} (hn : n < USize.size)
    (hw : Enc.WF t n e) (h : mwinColumn op t w n e = some (rt, out)) :
    mwinType op t = some rt ∧ Enc.WF rt n out := by
  have hu := toUSize_lt hn
  unfold mwinColumn at h
  rcases hrt : mwinType op t with _ | rt'
  · simp [hrt] at h
  rcases hk : scanKind t with _ | k
  · simp [hrt, hk] at h
  have htw := scanKind_width hk
  rcases hrk : scanKind rt' with _ | rk
  · simp [hrt, hk, htw, hrk] at h
  simp only [hrt, hk, htw, hrk, Option.map_some] at h
  split at h
  · cases h
  rename_i hc
  have hwd : op.width (op.readKind k) = rk.width :=
    Decidable.byContradiction fun hne => hc (by simp [hne])
  by_cases hb : t = .boolean
  · subst hb
    have : k = .bit := by simp [scanKind] at hk; simp [← hk]
    subst this
    obtain ⟨b, rfl⟩ : ∃ b, e = .bits b := by cases e <;> simp [Enc.WF] at hw ⊢
    have hrb : op.readKind .bit = .bit := by cases op <;> rfl
    simp only [hrb] at h hwd
    simp only [Enc.WF] at hw
    have hm : min n.toUSize.toNat (b.size * 8) = n := by rw [hu]; omega
    split at h
    · cases h
      rename_i hc'
      have : rk = .bit := by simpa using hc'
      subst this
      have := scanKind_bit hrk; subst this
      refine ⟨rfl, ?_⟩
      simp only [Enc.WF, mwinBitmap_size, hm, hwd, Scan.Kind.width, Nat.mul_one]
    · cases h
      rename_i hc'
      refine ⟨rfl, ?_⟩
      refine answer_dense hn hrk (by simpa using hc') ?_
      simp only [mwin_size, Scan.Kind.avail, hm, hwd]
  have hK : op.readKind k ≠ .bit := fun e => hb (scanKind_bit ((readKind_bit e) ▸ hk))
  have hrb : rk ≠ .bit := fun e => by
    subst e; have := scanKind_bit hrk; subst this; exact hb (mwinType_boolean hrt)
  obtain ⟨b', hb', hsz⟩ := bytesOf_size hb htw hw (countFits_of_lt hn)
  cases e
  all_goals first
    | (exfalso; cases t <;> simp [Enc.WF, scanKind] at hw hk hb; done)
    | skip
  all_goals
    split at h
    all_goals first
      | exact absurd ‹_› hK
      | (cases h; done)
      | (obtain ⟨s, hs, hse⟩ := Option.map_eq_some_iff.1 h
         simp only [Prod.mk.injEq] at hse
         obtain ⟨rfl, rfl⟩ := hse
         refine ⟨rfl, answer_dense hn hrk hrb ?_⟩
         rw [← hwd]
         first
           | (simp only at hs; cases hs; rw [mwinFoR_size _ hK, hu])
           | (simp only at hs; cases hs
              rw [mwinAlp_size _ (by
                rcases scanKind_alp hk hw with rfl | rfl <;> cases op <;> simp [Scan.MOp.readKind, Scan.Kind.raw]), hu])
           | (simp only at hs; rw [hb'] at hs; simp only at hs; split at hs
              · cases hs
              · cases hs
                rw [mwin_size, hu, min_avail hK (Nat.le_of_eq (by rw [readKind_width, hsz]))]))
end LeetQ.Rel.KernelWF

