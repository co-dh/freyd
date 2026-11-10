/-
  Well-formedness of the payloads qlean's kernels answer, read off their Lean bodies, in the form
  `Arr.ofPart`/`ofCols` take (`Enc.WF t n e`), and the `isSome` facts that make `codes`/`arrDense`
  total. Gathering kernels (`gatherColumn`, `sliceColumn`, `bytesOf`, `longBytes`, `gens`) are in
  `KernelWF/Gather`.
-/
import QLean.Kernel.Structural
import QLean.Kernel.Sort
import QLean.Kernel.Reduce
import QLean.Kernel.Elementwise
import QLean.Verify.Group
import QLean.Verify.Raw
import QLean.Verify.Ids
import QLean.Verify.Alp
import QLean.Verify.EwEnc
import LeetQ.Rel.Core

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel LeetQ.Rel

/-! ## Sizes of the folds the kernels are written as -/

/-- A fold that appends `w` bytes a step answers `w` bytes per element. -/
private theorem foldl_size {α σ : Type} (sz : σ → Nat) (g : σ → α → σ) (w : Nat)
    (hg : ∀ acc a, sz (g acc a) = sz acc + w) :
    ∀ (l : List α) (b : σ), sz (l.foldl g b) = sz b + l.length * w
  | [], b => by simp
  | a :: l, b => by
    simp only [List.foldl, List.length_cons]; rw [foldl_size sz g w hg l, hg]; simp [Nat.succ_mul]; omega

/-- A dense payload of `n` elements of a type with a width, other than boolean, is well formed. -/
theorem wf_bytes {t : QAtomicType} {w n : Nat} {b : ByteArray} (hb : t ≠ .boolean) (hw : t.width = some w)
    (hs : b.size = n * w) : Enc.WF t n (.bytes b) := by
  cases t <;> simp_all [Enc.WF, QAtomicType.width]

/-! ## `orderKind`: which types have a sort layout -/

/-- `orderKind` has no sort layout exactly at symbol, guid and the general list. -/
theorem orderKind_eq_none {t : QAtomicType} :
    orderKind t = none ↔ t = .symbol ∨ t = .guid ∨ t = .general := by
  cases t <;> simp [orderKind]

/-- A well-formed payload of a type with a width, other than boolean, has a dense layout. -/
private theorem bytesOf_isSome {t : QAtomicType} {n : Nat} {e : Enc} (hb : t ≠ .boolean)
    (hw : t.width.isSome) (h : Enc.WF t n e) : (Enc.bytesOf t n e).isSome := by
  cases t <;> cases e <;> simp_all [Enc.WF, Enc.bytesOf, QAtomicType.width]

/-- `groupIdsColumn` codes every well-formed payload except a general list's. -/
theorem groupIdsColumn_isSome {t : QAtomicType} {n : Nat} {e : Enc} (hg : t ≠ .general)
    (h : Enc.WF t n e) : (groupIdsColumn t n e).isSome := by
  cases t <;> cases e <;> simp_all [Enc.WF, groupIdsColumn, orderKind, Enc.bytesOf, QAtomicType.width]

/-! ## Results of the producing kernels -/

/-- `packOf n f` holds `n` bits. -/
theorem packOf_size (n : Nat) (f : Nat → Bool) : (packOf n f).size = (n + 7) / 8 := by
  simp only [packOf]; rw [foldl_size ByteArray.size _ 1 (fun _ _ => by simp only [ByteArray.size, ByteArray.push, Array.size_push])]; simp

/-- The summed count of parts, as the kernels fold it. -/
private theorem foldl_add_fst {β : Type} : ∀ (a : Nat) (l : List (Nat × β)),
    l.foldl (fun s p => s + p.1) a = a + (l.map (·.1)).sum
  | a, [] => by simp
  | a, p :: l => by simp [foldl_add_fst _ l]; omega

/-- A property every step keeps holds of the fold. -/
private theorem foldl_inv {α σ : Type} (P : σ → Prop) (g : σ → α → σ) (hg : ∀ s a, P s → P (g s a)) :
    ∀ (l : List α) (s : σ), P s → P (l.foldl g s)
  | [], _, h => h
  | a :: l, s, h => foldl_inv P g hg l (g s a) (hg s a h)

/-- `concatBits` of parts `ps` holds their summed count, as `razeColumn` counts it. -/
theorem concatBits_wf (ps : Array (Nat × ByteArray)) :
    Enc.WF .boolean (ps.foldl (fun s p => s + p.1) 0) (.bits (concatBits (ps.map (·.1)) (ps.map (·.2)))) := by
  simp only [Enc.WF, concatBits, packOf_size]
  congr 2
  rcases ps with ⟨l⟩
  simp only [Array.zip]; simp only [Array.size_flatMap]
  simp [foldl_add_fst]

/-- `til n` as `tilLongs`: `n` longs. -/
theorem tilLongs_wf (n : USize) : Enc.WF .long n.toNat (.bytes (tilLongs n)) :=
  wf_bytes (w := 8) (by decide) rfl (by
    simp only [tilLongs]; rw [foldl_size ByteArray.size _ 8 (fun _ _ => Column.pushBits_size ..)]; simp)

/-- `Ew.val` answers `n` elements at its class's width. -/
theorem Ew.val_size (op cls shape : UInt8) (nul : Int64) (a b : ByteArray) (n : USize) :
    (Kernel.Ew.val op cls shape nul a b n).size = n.toNat * Kernel.Ew.width cls := by
  simp only [Kernel.Ew.val]; rw [foldl_size ByteArray.size _ _ (fun _ _ => Column.pushBits_size ..)]; simp

/-- `Ew.mon` answers `n` elements at its class's width. -/
theorem Ew.mon_size (op cls : UInt8) (nul : Int64) (x : ByteArray) (n : USize) :
    (Kernel.Ew.mon op cls nul x n).size = n.toNat * Kernel.Ew.width cls := by
  simp only [Kernel.Ew.mon]; rw [foldl_size ByteArray.size _ _ (fun _ _ => Column.pushBits_size ..)]; simp

/-- `Ew.val` at a type whose width is its class's is a well-formed payload of `n` elements. -/
theorem Ew.val_wf {t : QAtomicType} {op cls shape : UInt8} {nul : Int64} {a b : ByteArray} {n : USize}
    (hb : t ≠ .boolean) (hw : t.width = some (Kernel.Ew.width cls)) :
    Enc.WF t n.toNat (.bytes (Kernel.Ew.val op cls shape nul a b n)) :=
  wf_bytes hb hw (Ew.val_size ..)

/-- `Ew.mon` at a type whose width is its class's is a well-formed payload of `n` elements. -/
theorem Ew.mon_wf {t : QAtomicType} {op cls : UInt8} {nul : Int64} {x : ByteArray} {n : USize}
    (hb : t ≠ .boolean) (hw : t.width = some (Kernel.Ew.width cls)) :
    Enc.WF t n.toNat (.bytes (Kernel.Ew.mon op cls nul x n)) :=
  wf_bytes hb hw (Ew.mon_size ..)

/-- `overGroups` over `ng` groups answers `2·ng` longs: the folds, then the live counts. -/
theorem overGroups_wf (op : Coc.Over) (cls : UInt8) (nul : Int64) (ng w : USize) (n : Nat) (gid b : ByteArray) :
    Enc.WF .long (2 * ng.toNat) (.bytes (overGroups op cls nul ng w n gid b)) :=
  wf_bytes (w := 8) (by decide) rfl (by rw [(Verify.overGroups_spec op cls nul ng w n gid b).1]; omega)

/-- `rankSlices` answers one long per slice of `o` when `o` is non-decreasing offsets from at least `0`,
    its last within `v`'s ids at width `w ≤ 64`: the negation of the kernel's guard, term by term. -/
theorem rankSlices_size (w : USize) (v o : ByteArray) (hw : w.toNat ≤ 64) (ho : 8 ≤ o.size)
    (h0 : 0 ≤ (Column.bitsAt o 0 8).toInt64.toInt)
    (hcap : (Column.bitsAt o (8 * (o.size / 8 - 1)) 8).toInt64.toInt ≤
      (Column.idsCap v w.toNat (Column.bitsAt o (8 * (o.size / 8 - 1)) 8).toInt64.toInt.toNat : Int))
    (hasc : ∀ j, j < o.size / 8 - 1 →
      (Column.bitsAt o (8 * j) 8).toInt64.toInt ≤ (Column.bitsAt o (8 * (j + 1)) 8).toInt64.toInt) :
    (Order.rankSlices w v o).size = 8 * (o.size / 8 - 1) := by
  simp only [Order.rankSlices]
  rw [if_neg]
  · rw [← Array.foldl_toList]
    refine Eq.trans (foldl_size (fun p : ByteArray × _ => p.1.size) _ 8 ?_ _ _) ?_
    · intro acc j; rcases acc with ⟨ids, seen⟩; simp only; split <;> simp [Column.pushBits_size]
    · simp; omega
  · simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range, not_or,
      not_exists, not_and, Nat.mul_zero]
    exact ⟨⟨⟨⟨Nat.not_lt.2 hw, Nat.not_lt.2 ho⟩, Int.not_lt.2 h0⟩, Int.not_lt.2 hcap⟩, fun j hj => Int.not_lt.2 (hasc j hj)⟩

/-- `Parted.of?` answers `some` on dense offsets that are cuts: its run-time decision (`ascending`, the
    two ends) holds of every `Cuts`, so a caller holding the proof never meets its `none`. -/
theorem Parted.of?_isSome {v : QAtomicType} {g n : Nat} {o : Arr .long (g+1)} {b : ByteArray}
    (val : Arr v n) (hb : o.enc = .bytes b) (hg : g + 1 < USize.size) (co : Cuts o n) :
    (Parted.of? o val).isSome := by
  have hwf : Enc.WF .long (g+1) (.bytes b) := hb ▸ o.wf
  have hu : (g+1).toUSize.toNat = g + 1 := by simp only [Nat.toUSize]; exact Nat.mod_eq_of_lt hg
  have hget : ∀ i, (Arr.mk (t := .long) (n := g+1) (.bytes b) hwf o.attrCell).get i = o.get i := fun i => by
    rw [Arr.get_long_bytes _ rfl, Arr.get_long_bytes _ hb]
  have hasc : Order.ascending .i64 false false (g+1).toUSize b = true := by
    rw [Verify.ascending_i64_iff, List.pairwise_map]
    have hs : min (g+1).toUSize.toNat (b.size / 8) = g + 1 := by
      simp only [Enc.WF, QAtomicType.width] at hwf; omega
    rw [hs]
    refine (List.pairwise_lt_range (n := g+1)).imp_of_mem fun {i j} hi hj hij => ?_
    rw [List.mem_range] at hi hj
    have := co.1 ⟨i, hi⟩ ⟨j, hj⟩ (Fin.le_def.2 (Nat.le_of_lt hij))
    rw [Arr.get_long_bytes _ hb, Arr.get_long_bytes _ hb] at this
    simpa [Verify.ordRel] using this
  unfold Parted.of?
  rw [hb]
  simp only [longBytes, Option.bind_eq_bind, Option.bind_some]
  rw [dif_pos ⟨hwf, hg⟩, dif_pos ⟨hasc, (hget 0).trans co.2.1, by rw [hget]; exact co.2.2⟩]
  rfl

/-! ## `razeColumn` -/

/-- An `Option` pass that answers `some (g x)` at every element answers `some` of the mapped array. -/
private theorem mapM_some {α β : Type} {f : α → Option β} (g : α → β) :
    ∀ {cs : Array α}, (∀ x ∈ cs, f x = some (g x)) → cs.mapM f = some (cs.map g) := by
  intro cs h
  rcases cs with ⟨l⟩
  rw [Array.mapM_eq_mapM_toList]
  simp only [Array.mem_def] at h
  suffices hl : l.mapM f = some (l.map g) by simp [hl]
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.mapM_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- The dense layout of a well-formed payload of a type with a width, other than boolean, holds its `n`
    elements, `w` bytes each; `n` fits a `USize`, the count every decoding kernel reads. -/
theorem bytesOf_size {t : QAtomicType} {n w : Nat} {e : Enc} (hb : t ≠ .boolean) (hw : t.width = some w)
    (h : Enc.WF t n e) (hn : n < USize.size) :
    ∃ b, Enc.bytesOf t n e = some b ∧ b.size = n * w := by
  have hu : n.toUSize.toNat = n := by simp only [Nat.toUSize]; exact Nat.mod_eq_of_lt hn
  have hwu : w.toUSize.toNat = w := by
    simp only [Nat.toUSize]; apply Nat.mod_eq_of_lt
    have : w ≤ 16 := by cases t <;> simp [QAtomicType.width] at hw <;> omega
    rcases System.Platform.numBits_eq with h' | h' <;> rw [h'] <;> omega
  have hpush (k : Nat) (l : List UInt64) :
      (l.foldl (fun acc v => Column.pushBits acc v k) ByteArray.empty).size = l.length * k := by
    rw [foldl_size ByteArray.size _ k (fun _ _ => Column.pushBits_size ..)]; simp
  cases e
  case foR m p =>
    refine ⟨_, by simp [Enc.bytesOf, hw]; rfl, ?_⟩
    simp only [Coc.decode, hpush, Coc.elems, List.length_map, List.length_range, hu, hwu]
  case alp m p a =>
    refine ⟨_, by simp [Enc.bytesOf, hw]; rfl, ?_⟩
    have h4 : (w.toUSize == 4) = true → w = 4 := fun e => by rw [← hwu, beq_iff_eq.1 e]; rcases System.Platform.numBits_eq with h' | h' <;> simp [USize.toNat_ofNat, h']
    have h8 : (w.toUSize == 8) = true → w = 8 := fun e => by rw [← hwu, beq_iff_eq.1 e]; rcases System.Platform.numBits_eq with h' | h' <;> simp [USize.toNat_ofNat, h']
    simp only [Coc.alpDecode, Coc.alpDecode32, Coc.alpDecode64]
    split
    · rw [hpush, h4 ‹_›]; simp [Coc.alpElems, hu]
    · split
      · rw [hpush, h8 ‹_›]; simp [Coc.alpElems, hu]
      · rw [hpush]; simp [Coc.alpElems, hu, hwu]
  all_goals cases t <;> simp_all [Enc.WF, Enc.bytesOf, QAtomicType.width]

/-- `razeColumn` joins every non-empty array of well-formed parts of one type other than the general
    list, each count fitting a `USize`. Without that bound a `foR` or `alp` part past `2^64` elements is
    decoded at its count mod `2^64` and the dense size check answers `none`. -/
theorem razeColumn_isSome {t : QAtomicType} {cs : Array (Nat × Enc)} (hne : cs.size ≠ 0)
    (hg : t ≠ .general) (h : ∀ c ∈ cs, Enc.WF t c.1 c.2 ∧ c.1 < USize.size) :
    (razeColumn t cs).isSome := by
  have hdense : ∀ w, t.width = some w → t ≠ .boolean →
      ∃ ps, cs.mapM (fun c => Enc.bytesOf t c.1 c.2) = some ps ∧ ps.size = cs.size ∧
        ∀ i (hi : i < cs.size) (hp : i < ps.size), ps[i].size = cs[i].1 * w := by
    intro w hw hb
    refine ⟨cs.map fun c => (Enc.bytesOf t c.1 c.2).getD .empty, mapM_some _ fun c hc => ?_, by simp,
      fun i hi hp => ?_⟩
    · obtain ⟨b, hb', -⟩ := bytesOf_size hb hw (h c hc).1 (h c hc).2; simp [hb']
    · obtain ⟨b, hb', hs⟩ := bytesOf_size hb hw (h _ (Array.getElem_mem hi)).1 (h _ (Array.getElem_mem hi)).2
      simp [hb', hs]
  unfold razeColumn
  rw [if_neg (by simpa [Array.isEmpty] using hne)]
  cases t
  case general => exact absurd rfl hg
  case boolean =>
    rw [mapM_some (fun c => (c.1, match c.2 with | .bits b => b | _ => .empty)) fun c hc => ?_]
    · rfl
    · have := (h c hc).1; rcases c with ⟨n, e⟩; cases e <;> simp [Enc.WF] at this ⊢
  case symbol =>
    dsimp only
    split
    · rfl
    · rw [mapM_some (fun c => match Column.intern c.2 with
          | .enum d o i => (c.1, d, o, i) | _ => (c.1, .empty, #[], .empty)) fun c hc => ?_]
      · rfl
      · have := (h c hc).1; rcases c with ⟨n, e⟩; cases e <;> simp [Enc.WF, QAtomicType.width, Column.intern] at this ⊢
  all_goals
    obtain ⟨ps, hps, hsz, hps'⟩ := hdense _ rfl (by decide)
    dsimp only
    repeat' split
    all_goals try rfl
    all_goals first
      | (exfalso; rename_i hx; exact hx _ _ rfl hps)
      | (exfalso; rename_i hw hm hany
         rw [hps] at hm; injection hm with hm; subst hm
         simp only [QAtomicType.width, Option.some.injEq] at hw; subst hw
         rw [Array.any_eq_true] at hany; obtain ⟨i, hi, hc⟩ := hany
         simp only [Array.size_zip] at hi
         simp only [Array.getElem_zip, decide_eq_true_eq] at hc
         rw [hps' i (by omega) (by omega)] at hc; omega)

/-- `concatSyms` (the symbol branch on `syms` parts) answers a symbol vector whose offsets count it. -/
theorem concatSyms_wf (parts : Array (ByteArray × Array Nat)) :
    ∃ n e, concatSyms parts = .vector .symbol n e none ∧ Enc.WF .symbol n e := by
  refine ⟨_, _, rfl, ?_⟩
  simp only [Enc.WF]
  have : 1 ≤ (Array.foldl (fun x y => match x with | (blob, offs) => match y with
      | (b, o) => (blob ++ b, offs ++ Array.map (fun x => x + blob.size) (o.extract 1)))
      (ByteArray.empty, #[0]) parts).snd.size := by
    rw [← Array.foldl_toList]
    refine foldl_inv (fun p : ByteArray × Array Nat => 1 ≤ p.2.size) _ (fun s a hs => ?_) _ _ (by simp)
    rcases s with ⟨blob, offs⟩; rcases a with ⟨b, o⟩; simp only [Array.size_append] at hs ⊢; omega
  exact (Nat.sub_add_cancel this).symm

/-- The dense branch of `razeColumn`: parts of `cs.1 · w` bytes each, joined, hold the summed count. -/
theorem concatBytes_wf {t : QAtomicType} {w : Nat} {cs : Array (Nat × Enc)} {ps : Array ByteArray}
    (hb : t ≠ .boolean) (hw : t.width = some w) (hsz : ps.size = cs.size)
    (hps : ∀ i (hi : i < cs.size) (hp : i < ps.size), ps[i].size = cs[i].1 * w) :
    Enc.WF t (cs.foldl (fun x1 x2 => x1 + x2.1) 0) (.bytes (concatBytes ps)) := by
  refine wf_bytes hb hw ?_
  have happ : ∀ (l : List ByteArray) (b : ByteArray), (l.foldl (· ++ ·) b).size = b.size + (l.map (·.size)).sum := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => intro b; simp [ih, ByteArray.size_append]; omega
  have hmap : ps.toList.map (·.size) = cs.toList.map (·.1 * w) := by
    apply List.ext_getElem (by simp [hsz]); intro i h1 h2; simp at h1 h2; simp [hps i h2 h1]
  have hm : ∀ l : List (Nat × Enc), (l.map (·.1 * w)).sum = (l.map (·.1)).sum * w := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp [ih, Nat.add_mul]
  rw [concatBytes, ← Array.foldl_toList, happ, hmap, ← Array.foldl_toList, foldl_add_fst, hm]
  simp

/-! ## `Enc.answer` -/

private theorem toUSize_toNat {k : Nat} (h : k < USize.size) : k.toUSize.toNat = k := by
  simp only [Nat.toUSize]; exact Nat.mod_eq_of_lt h

private theorem lt_usize {k : Nat} (h : k ≤ 64) : k < USize.size :=
  Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt h (by decide)) USize.le_size

/-- `Coc.decode` answers `n` elements at `w` bytes. -/
theorem decode_size (w : USize) (M P : ByteArray) (n : USize) :
    (Coc.decode w M P n).size = n.toNat * w.toNat := by
  simp only [Coc.decode, Coc.elems]
  rw [foldl_size ByteArray.size _ w.toNat (fun _ _ => Column.pushBits_size ..)]; simp

/-- `encodeBelow`'s `some` is `encode`'s answer. -/
private theorem encodeBelow_eq {w : USize} {x : ByteArray} {mp : ByteArray × ByteArray}
    (h : Coc.encodeBelow w x = some mp) : mp = Coc.encode w x := by
  unfold Coc.encodeBelow at h
  generalize Coc.encode w x = q at h ⊢
  rcases q with ⟨m, p⟩
  simp only at h; split at h
  · cases h; rfl
  · cases h

/-- `Enc.answer` keeps a well-formed payload well formed at every type ALP does not encode: it keeps
    it, encodes dense bytes by `encodeBelow`, or decodes it to `n · w` bytes, `n` fitting a `USize`. -/
theorem answer_wf {t : QAtomicType} {n : Nat} {e : Enc} (hA : Column.alpEncodes t = false)
    (hwf : Enc.WF t n e) (hn : n < USize.size) : Enc.WF t n (Enc.answer t n e) := by
  have hfoR : ∀ {m p : ByteArray}, t.width.isSome → t ≠ .boolean → t ≠ .guid →
      n ≤ Column.blk * Column.nblk m → Enc.WF t n (.foR m p) := by
    intro m p h1 h2 h3 h4; cases t <;> simp_all [Enc.WF]
  have hdec : ∀ {w}, t.width = some w → ∀ {b}, Enc.bytesOf t n e = some b → Enc.WF t n (.bytes b) := by
    intro w hw b hbo
    by_cases hb : t = .boolean
    · subst hb; cases e <;> simp_all [Enc.WF, Enc.bytesOf]
    obtain ⟨b', hb', hs⟩ := bytesOf_size hb hw hwf hn
    rw [hbo] at hb'; cases hb'
    exact wf_bytes hb hw hs
  unfold Enc.answer
  split
  · exact hwf
  rcases hW : t.width with _ | w
  · exact hwf
  cases e
  case bytes b =>
    have hb : t ≠ .boolean := by rintro rfl; simp [Enc.WF] at hwf
    have hs : b.size = n * w := by simpa [Enc.WF, hW] using hwf
    simp only
    split
    · exact hwf
    simp only [hA, Bool.false_eq_true, if_false]
    split
    · rename_i hE
      split
      · rename_i m p heq
        have h0 : 0 < w ∧ w ≤ 8 ∧ t ≠ .guid := by
          cases t <;> simp_all [QAtomicType.width, Column.encodes] <;> omega
        have hk := Verify.nblk_encode w h0.1 h0.2.1 b
        rw [← encodeBelow_eq heq] at hk
        simp only [hs, Nat.mul_div_cancel _ h0.1] at hk
        refine hfoR (by simp [hW]) hb h0.2.2 ?_
        rw [hk]; simp only [Column.blk]; omega
      · exact hwf
    · exact hwf
  all_goals
    simp only
    split
    · exact hwf
    split
    · rename_i b hbo; exact hdec hW hbo
    · exact hwf

/-! ## The `enum` branch: `concatEnum` -/

/-- The widths an id pack takes: `laneWidth`'s answers. -/
private abbrev Lane (w : Nat) : Prop := w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64

private theorem lane_idWidth (offs : Array Nat) : Lane (Column.idWidth offs) := by
  simp only [Column.idWidth, Column.idWidthOf, Column.laneWidth]
  repeat' split
  all_goals omega

/-- A `Nat.fold` that pushes a byte a step answers one byte per step. -/
private theorem fold_push_size (g : Nat → UInt8) :
    ∀ (k : Nat) (b : ByteArray), (Nat.fold k (fun i _ acc => acc.push (g i)) b).size = b.size + k
  | 0, b => by simp
  | k + 1, b => by
    rw [Nat.fold_succ, ← Nat.add_assoc, ← fold_push_size g k b]
    simp only [ByteArray.size, ByteArray.push, Array.size_push]

/-- `packIds` at a lane width holds the `n` ids it was handed: `idsCap` reads all of them back. -/
theorem packIds_cap {w : Nat} (hw : Lane w) (n : Nat) (f : Nat → Nat) :
    Column.idsCap (Column.packIds w n f) w n = n := by
  have hbytes : ∀ c, 1 ≤ c → c ≤ 8 → Column.idsCap (Column.packIds (8 * c) n f) (8 * c) n = n := by
    intro c h1 h8
    rw [Column.idsCap, if_neg (by omega), (Verify.packIds_bytes c n f h1 h8).1]
    rw [show c * n * 8 / (8 * c) = n by
      rw [Nat.mul_comm c n, Nat.mul_assoc, Nat.mul_comm c 8]; exact Nat.mul_div_cancel _ (by omega)]
    exact Nat.min_self n
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [Column.idsCap]
  all_goals first
    | exact hbytes 1 (by decide) (by decide)
    | exact hbytes 2 (by decide) (by decide)
    | exact hbytes 4 (by decide) (by decide)
    | exact hbytes 8 (by decide) (by decide)
    | (unfold Column.idsCap Column.packIds
       rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), fold_push_size]
       simp only [ByteArray.emptyWithCapacity, ByteArray.size]; omega)

/-- `internConcat` answers its joined dictionary and `concatIds` over every part's count and ids. -/
private theorem internConcat_eq (qs : Array (Nat × ByteArray × Array Nat × ByteArray)) :
    ∃ db dbo ws maps, internConcat qs =
      (db, dbo, concatIds (Column.idWidth dbo).toUSize (qs.map (·.1)) ws maps (qs.map (·.2.2.2))) :=
  ⟨_, _, _, _, rfl⟩

private theorem hashConcat_ok {qs : Array (Nat × ByteArray × Array Nat × ByteArray)} {r}
    (h : hashConcat qs = .ok r) : r = internConcat qs := by
  simp only [hashConcat] at h
  repeat' split at h
  all_goals first | (injection h with h; exact h.symm) | simp at h

private theorem hashConcat_error {qs : Array (Nat × ByteArray × Array Nat × ByteArray)} {r}
    (h : hashConcat qs = .error r) : r = qs := by
  simp only [hashConcat] at h
  repeat' split at h
  all_goals first | (injection h with h; exact h.symm) | simp at h

/-- `internConcat` of parts holds their summed count. -/
theorem internConcat_wf (qs : Array (Nat × ByteArray × Array Nat × ByteArray)) :
    Enc.WF .symbol (qs.foldl (fun s p => s + p.1) 0)
      (.enum (internConcat qs).1 (internConcat qs).2.1 (internConcat qs).2.2) := by
  obtain ⟨db, dbo, ws, maps, h⟩ := internConcat_eq qs
  rw [h]
  simp only [Enc.WF, concatIds]
  rw [toUSize_toNat (lt_usize (by rcases lane_idWidth dbo with h | h | h | h | h | h | h | h <;> omega))]
  have hsz : ((Array.range (min (qs.map (·.1)).size (qs.map (·.2.2.2)).size)).flatMap fun k =>
      (Array.range (qs.map (·.1))[k]!).map fun i =>
        Column.idAt maps[k]! (Column.idWidth dbo) (Column.idAt (qs.map (·.2.2.2))[k]! ws[k]! i)).size =
      qs.foldl (fun s p => s + p.1) 0 := by
    rcases qs with ⟨l⟩
    simp only [Array.size_flatMap, Array.size_map, Array.size_range, Nat.min_self]
    rw [← Array.foldl_toList, foldl_add_fst, Nat.zero_add]
    have hl : (Array.range l.length).map (fun k => (Array.map (·.1) l.toArray)[k]!) = (l.map (·.1)).toArray := by
      apply Array.ext (by simp)
      intro i h1 h2
      simp only [Array.size_map, Array.size_range] at h1
      simp [h1]
    simp only [List.size_toArray] at hl ⊢
    rw [hl]; simp
  rw [← hsz]
  exact packIds_cap (lane_idWidth dbo) _ _

/-- The interned join `concatEnum` answers after `hashConcat`, whichever way that goes. -/
private theorem hashJoin_wf (qs : Array (Nat × ByteArray × Array Nat × ByteArray)) :
    Enc.WF .symbol (qs.foldl (fun s p => s + p.1) 0) (match hashConcat qs with
      | .ok (db, dbo, ids) => .enum db dbo ids
      | .error ps => match internConcat ps with | (db, dbo, ids) => .enum db dbo ids) := by
  split
  · rename_i db dbo ids heq
    have := internConcat_wf qs
    rw [← hashConcat_ok heq] at this
    exact this
  · rename_i r heq
    obtain rfl := hashConcat_error heq
    exact internConcat_wf r

/-- `concatEnum` answers an interned symbol vector whose ids count it. -/
theorem concatEnum_wf (ps : Array (Nat × ByteArray × Array Nat × ByteArray)) :
    ∃ n e, concatEnum ps = .vector .symbol n e none ∧ Enc.WF .symbol n e := by
  unfold concatEnum
  dsimp only
  generalize Array.mapIdx _ ps = qs
  exact ⟨_, _, rfl, hashJoin_wf qs⟩

end LeetQ.Rel.KernelWF
