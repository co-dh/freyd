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
import QLean.Verify.Gather
import LeetQ.Rel.Core

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel LeetQ.Rel

/-! ## Sizes of the folds the kernels are written as -/

/-- A fold that appends `w` bytes a step answers `w` bytes per element. -/
theorem foldl_size {α σ : Type} (sz : σ → Nat) (g : σ → α → σ) (w : Nat)
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
theorem bytesOf_isSome {t : QAtomicType} {n : Nat} {e : Enc} (hb : t ≠ .boolean)
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
    elements, `w` bytes each; an encoded `n` fits a `USize`, the count every decoding kernel reads. -/
theorem bytesOf_size {t : QAtomicType} {n w : Nat} {e : Enc} (hb : t ≠ .boolean) (hw : t.width = some w)
    (h : Enc.WF t n e) (hc : Verify.countFits n e) :
    ∃ b, Enc.bytesOf t n e = some b ∧ b.size = n * w := by
  have hu : n < USize.size → n.toUSize.toNat = n := fun hn => by simp only [Nat.toUSize]; exact Nat.mod_eq_of_lt hn
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
    simp only [Coc.decode, hpush, Coc.elems, List.length_map, List.length_range, hu hc, hwu]
  case alp m p a =>
    refine ⟨_, by simp [Enc.bytesOf, hw]; rfl, ?_⟩
    have h4 : (w.toUSize == 4) = true → w = 4 := fun e => by rw [← hwu, beq_iff_eq.1 e]; rcases System.Platform.numBits_eq with h' | h' <;> simp [USize.toNat_ofNat, h']
    have h8 : (w.toUSize == 8) = true → w = 8 := fun e => by rw [← hwu, beq_iff_eq.1 e]; rcases System.Platform.numBits_eq with h' | h' <;> simp [USize.toNat_ofNat, h']
    simp only [Coc.alpDecode, Coc.alpDecode32, Coc.alpDecode64]
    split
    · rw [hpush, h4 ‹_›]; simp [Coc.alpElems, hu hc]
    · split
      · rw [hpush, h8 ‹_›]; simp [Coc.alpElems, hu hc]
      · rw [hpush]; simp [Coc.alpElems, hu hc, hwu]
  all_goals cases t <;> simp_all [Enc.WF, Enc.bytesOf, QAtomicType.width]

theorem countFits_of_lt {n : Nat} {e : Enc} (h : n < USize.size) : Verify.countFits n e := by
  cases e <;> simp [Verify.countFits, h]

/-- The dense layouts of well-formed parts, each count fitting a `USize`: one per part, `n · w` bytes each. -/
private theorem dense_parts {t : QAtomicType} {cs : Array (Nat × Enc)} {w : Nat}
    (h : ∀ c ∈ cs, Enc.WF t c.1 c.2 ∧ c.1 < USize.size) (hw : t.width = some w) (hb : t ≠ .boolean) :
    ∃ ps, cs.mapM (fun c => Enc.bytesOf t c.1 c.2) = some ps ∧ ps.size = cs.size ∧
      ∀ i (hi : i < cs.size) (hp : i < ps.size), ps[i].size = cs[i].1 * w := by
  refine ⟨cs.map fun c => (Enc.bytesOf t c.1 c.2).getD .empty, mapM_some _ fun c hc => ?_, by simp,
    fun i hi hp => ?_⟩
  · obtain ⟨b, hb', -⟩ := bytesOf_size hb hw (h c hc).1 (countFits_of_lt (h c hc).2); simp [hb']
  · obtain ⟨b, hb', hs⟩ := bytesOf_size hb hw (h _ (Array.getElem_mem hi)).1 (countFits_of_lt (h _ (Array.getElem_mem hi)).2)
    simp [hb', hs]

/-- `razeColumn` joins every non-empty array of well-formed parts of one type other than the general
    list, each count fitting a `USize`. Without that bound a `foR` or `alp` part past `2^64` elements is
    decoded at its count mod `2^64` and the dense size check answers `none`. -/
theorem razeColumn_isSome {t : QAtomicType} {cs : Array (Nat × Enc)} (hne : cs.size ≠ 0)
    (hg : t ≠ .general) (h : ∀ c ∈ cs, Enc.WF t c.1 c.2 ∧ c.1 < USize.size) :
    (razeColumn t cs).isSome := by
  have hdense : ∀ w, t.width = some w → t ≠ .boolean →
      ∃ ps, cs.mapM (fun c => Enc.bytesOf t c.1 c.2) = some ps ∧ ps.size = cs.size ∧
        ∀ i (hi : i < cs.size) (hp : i < ps.size), ps[i].size = cs[i].1 * w :=
    fun _ hw hb => dense_parts h hw hb
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

/-- A Frame-of-Reference payload is well formed at a fixed-width type other than boolean and guid
    exactly when its blocks cover its count. -/
theorem wf_foR {t : QAtomicType} {n : Nat} {m p : ByteArray} (hw : t.width.isSome) (hb : t ≠ .boolean)
    (hg : t ≠ .guid) (h : n ≤ Column.blk * Column.nblk m) : Enc.WF t n (.foR m p) := by
  cases t <;> simp_all [Enc.WF]

/-- `encodeBelow`'s `some` is `encode`'s answer. -/
private theorem encodeBelow_eq {w : USize} {x : ByteArray} {mp : ByteArray × ByteArray}
    (h : Coc.encodeBelow w x = some mp) : mp = Coc.encode w x := by
  unfold Coc.encodeBelow at h
  generalize Coc.encode w x = q at h ⊢
  rcases q with ⟨m, p⟩
  simp only at h; split at h
  · cases h; rfl
  · cases h

/-! ## ALP payloads -/

/-- `alpBlob`'s header declares the width it was handed, at any count: byte 8 is the flag. -/
theorem alpF32_alpBlob (f32 : Bool) (w n : Nat) (x : ByteArray) (bs : Array (Nat × Array (Option UInt64))) :
    Column.alpF32 (Coc.alpBlob f32 w n x bs) = f32 := by
  obtain ⟨pad, hpg, hps, hA⟩ := Verify.alpBlob_eq f32 w n x bs _ rfl
  rw [hA]
  unfold Column.alpF32
  generalize hS : Column.pushBits ByteArray.empty _ 8 = S
  have hS8 : S.size = 8 := by rw [← hS, Column.pushBits_size]; rfl
  have h16 : (Column.pushBits S (if f32 then 1 else 0) 8).size = 16 := by rw [Column.pushBits_size, hS8]
  have hp : (pad (Column.pushBits S (if f32 then 1 else 0) 8)).size = 16 := by rw [hps, h16]
  rw [Column.bitsAt_congr (Column.pushBits S (if f32 then 1 else 0) 8) _ 8 8 (fun k hk => ?_)]
  · have hP := Column.bitsAt_pushBits S (if f32 then 1 else 0) 8 (by decide)
    rw [hS8] at hP; rw [hP]; cases f32 <;> decide
  · repeat rw [Verify.ba_append_left _ _ _ (by simp only [ByteArray.size_append, hp]; omega)]
    exact hpg _ _ (by omega)

/-- `alpEncodeAt` lays out a block for every `blk` of its elements: `Enc.WF`'s cover condition. -/
theorem nblk_alpEncodeAt (f32 : Bool) (x : ByteArray) :
    x.size / (if f32 then 4 else 8) ≤ Column.blk * Column.nblk (Coc.alpEncodeAt f32 x).1 := by
  unfold Coc.alpEncodeAt
  simp only []
  rw [show (8 : USize) = (8 : Nat).toUSize from rfl, Verify.nblk_encode 8 (by decide) (by decide),
    Verify.blocks_size]
  simp only [Array.toList_map, Array.toList_range, List.map_map, Function.comp_def, Coc.alpBlockOf,
    Array.size_map, Array.size_range]
  rw [Verify.sum_blocks]
  generalize x.size / (if f32 then 4 else 8) = n
  simp only [Column.blk] at *
  omega

/-- `Coc.alpDecode` holds `n` elements of `w` bytes, as `decodeW` says of `Coc.decode`. -/
theorem alpDecode_size (w : USize) (hw : w.toNat ≤ 8) (M P a : ByteArray) (n : USize) :
    (Coc.alpDecode w M P a n).size = w.toNat * n.toNat := by
  obtain ⟨hs, -, -⟩ := Verify.foldl_pushBits id w.toNat hw (Coc.alpElems M P a n) ByteArray.empty
  rw [Verify.alpDecode_eq]; simpa [Coc.alpElems] using hs

/-- `alpEncodeAt` at a float type's own width is a well-formed ALP payload of every count its input
    holds. -/
theorem alpEncodeAt_wf {t : QAtomicType} {n : Nat} (f32 : Bool) (ht : Column.alpEncodes t = true)
    (hf : t.width = some (if f32 then 4 else 8)) (x : ByteArray) (hn : n ≤ x.size / (if f32 then 4 else 8)) :
    Enc.WF t n (.alp (Coc.alpEncodeAt f32 x).1 (Coc.alpEncodeAt f32 x).2.1 (Coc.alpEncodeAt f32 x).2.2) := by
  have hF : Column.alpF32 (Coc.alpEncodeAt f32 x).2.2 = f32 := alpF32_alpBlob ..
  simp only [Enc.WF]
  refine ⟨by cases t <;> simp_all [Column.alpEncodes], Nat.le_trans hn (nblk_alpEncodeAt f32 x), ?_⟩
  rw [hF, hf]; cases f32 <;> decide

/-- `alpEncodeBelow`'s `some` is `alpEncodeAt`'s answer. -/
private theorem alpEncodeBelow_eq {f32 : Bool} {x m p a : ByteArray}
    (h : (if f32 = true then Coc.alpEncodeBelow32 x else Coc.alpEncodeBelow64 x) = some (m, p, a)) :
    m = (Coc.alpEncodeAt f32 x).1 ∧ p = (Coc.alpEncodeAt f32 x).2.1 ∧ a = (Coc.alpEncodeAt f32 x).2.2 := by
  cases f32 <;>
    simp only [Coc.alpEncodeBelow32, Coc.alpEncodeBelow64, Coc.alpEncode32, Coc.alpEncode64, if_true,
      Bool.false_eq_true, if_false] at h <;>
    (generalize Coc.alpEncodeAt _ x = q at h ⊢
     rcases q with ⟨m', p', a'⟩
     simp only at h
     split at h
     · obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
     · cases h)

/-- A float type's width is the one its ALP width flag names. -/
private theorem alp_width {t : QAtomicType} {w : Nat} (ht : Column.alpEncodes t = true) (hw : t.width = some w) :
    (if (w == 4) = true then 4 else 8) = w ∧ 0 < w := by
  cases t <;> simp_all [Column.alpEncodes, QAtomicType.width] <;> subst hw <;> decide

/-- `Enc.answer` keeps a well-formed payload well formed: it keeps it, encodes dense bytes by
    `alpEncodeBelow` or `encodeBelow`, or decodes it to `n · w` bytes, `n` fitting a `USize`. -/
theorem answer_wf {t : QAtomicType} {n : Nat} {e : Enc}
    (hwf : Enc.WF t n e) (hn : n < USize.size) : Enc.WF t n (Enc.answer t n e) := by
  have hdec : ∀ {w}, t.width = some w → ∀ {b}, Enc.bytesOf t n e = some b → Enc.WF t n (.bytes b) := by
    intro w hw b hbo
    by_cases hb : t = .boolean
    · subst hb; cases e <;> simp_all [Enc.WF, Enc.bytesOf]
    obtain ⟨b', hb', hs⟩ := bytesOf_size hb hw hwf (countFits_of_lt hn)
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
    by_cases hA : Column.alpEncodes t = true
    · rw [if_pos hA]
      obtain ⟨h48, h0⟩ := alp_width hA hW
      generalize hE : (if (w == 4) = true then Coc.alpEncodeBelow32 b else Coc.alpEncodeBelow64 b) = E
      rcases E with _ | ⟨m, p, a⟩
      · exact hwf
      obtain ⟨rfl, rfl, rfl⟩ := alpEncodeBelow_eq hE
      exact alpEncodeAt_wf _ hA (by rw [h48]; exact hW) b (by rw [h48, hs, Nat.mul_div_cancel _ h0]; exact Nat.le_refl _)
    rw [if_neg hA]
    split
    · rename_i hE
      split
      · rename_i m p heq
        have h0 : 0 < w ∧ w ≤ 8 ∧ t ≠ .guid := by
          cases t <;> simp_all [QAtomicType.width, Column.encodes] <;> omega
        have hk := Verify.nblk_encode w h0.1 h0.2.1 b
        rw [← encodeBelow_eq heq] at hk
        simp only [hs, Nat.mul_div_cancel _ h0.1] at hk
        refine wf_foR (by simp [hW]) hb h0.2.2 ?_
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

/-! ## The `foR` branch: `concatFoR` -/

private theorem sum_map_mul {β : Type} (f : β → Nat) (k : Nat) :
    ∀ l : List β, (l.map (fun x => f x * k)).sum = (l.map f).sum * k
  | [] => by simp
  | x :: l => by simp [sum_map_mul f k l, Nat.add_mul]

private theorem sum_le_mul {β : Type} (f g : β → Nat) (k : Nat) :
    ∀ l : List β, (∀ x ∈ l, f x ≤ k * g x) → (l.map f).sum ≤ k * (l.map g).sum
  | [], _ => by simp
  | x :: l, h => by
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    have h1 := sum_le_mul f g k l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have h2 := h x (by simp)
    omega

private theorem foldl_append_size {α β : Type} (g : β → Array α) :
    ∀ (l : List β) (a : Array α),
      (l.foldl (fun acc p => acc ++ g p) a).size = a.size + (l.map (fun p => (g p).size)).sum
  | [], a => by simp
  | p :: l, a => by
    simp only [List.foldl, foldl_append_size g l, Array.size_append, List.map_cons, List.sum_cons]; omega

/-- `concatBytes` holds every part's bytes. -/
theorem concatBytes_size (ps : Array ByteArray) : (concatBytes ps).size = (ps.toList.map (·.size)).sum := by
  have happ : ∀ (l : List ByteArray) (b : ByteArray), (l.foldl (· ++ ·) b).size = b.size + (l.map (·.size)).sum := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => intro b; simp [ih, ByteArray.size_append]; omega
  rw [concatBytes, ← Array.foldl_toList, happ]; simp

/-- `foRMeta` of `bs` blocks: four sections of eight bytes a block, the sixteen-byte trailer, a width
    byte a block. So `nblk` reads `bs.size` back. -/
theorem foRMeta_size (nul : UInt64) (sumn : Nat) (bs : Array (UInt64 × UInt64 × UInt64 × Nat)) :
    (Coc.foRMeta nul sumn bs).size = 33 * bs.size + 16 := by
  have hA : ∀ (f : (UInt64 × UInt64 × UInt64 × Nat) → UInt64) (l : List (UInt64 × UInt64 × UInt64 × Nat)),
      (l.foldl (fun acc b => Column.pushBits acc (f b) 8) ByteArray.empty).size = l.length * 8 := fun f l => by
    rw [foldl_size ByteArray.size _ 8 (fun _ _ => Column.pushBits_size ..)]; simp
  have hB : ∀ (l : List (UInt64 × UInt64 × UInt64 × Nat)),
      (l.foldl (fun acc b => acc.push b.2.2.2.toUInt8) ByteArray.empty).size = l.length := fun l => by
    rw [foldl_size ByteArray.size _ 1 (fun _ _ => by simp only [ByteArray.size, ByteArray.push, Array.size_push])]
    simp
  have hC : ∀ (l : List (UInt64 × UInt64 × UInt64 × Nat)) (g : ByteArray × Nat → _ → ByteArray × Nat),
      (∀ x b, (g x b).1.size = x.1.size + 8) → (l.foldl g (ByteArray.empty, 0)).1.size = l.length * 8 :=
    fun l g hg => by refine Eq.trans (foldl_size (fun p : ByteArray × Nat => p.1.size) g 8 hg l _) ?_; simp
  simp only [Coc.foRMeta, ByteArray.size_append, ← Array.foldl_toList, hA, hB]
  rw [hC _ _ (fun x b => by rcases x with ⟨acc, pos⟩; exact Column.pushBits_size ..)]
  simp [Column.pushBits_size]; omega

/-- `moveFoR` claims only parts in the writer's form, each `⌈n/blk⌉` blocks, and moves every block:
    the answer's blocks cover the summed count. -/
theorem moveFoR_nblk {ps : Array ((Nat × ByteArray) × ByteArray)} {m p : ByteArray}
    (h : moveFoR ps = some (m, p)) : (ps.toList.map (·.1.1)).sum ≤ Column.blk * Column.nblk m := by
  unfold moveFoR at h
  split at h
  · cases h
  rename_i hc
  injection h with h; injection h with hm
  subst hm
  have hall : ∀ x ∈ ps.toList, x.1.1 ≤ Column.blk * Column.nblk x.1.2 := by
    intro x hx
    have hs : Coc.foRStd x.1.1 x.1.2 x.2 = true := by
      cases hs : Coc.foRStd x.1.1 x.1.2 x.2
      · exfalso; apply hc
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
        rw [Bool.or_eq_true, Array.any_eq_true]; right
        refine ⟨i, by simpa using hi, ?_⟩
        simp only [Array.getElem_toList] at hs; simp [hs]
      · rfl
    rw [(Verify.foRStd_iff.1 hs).nblk]; simp only [Column.blk]; omega
  rw [Column.nblk, foRMeta_size, show ∀ k, (33 * k + 16) / 33 = k from fun k => by omega,
    ← Array.foldl_toList, foldl_append_size]
  simpa using sum_le_mul _ _ _ _ hall

/-- `appendFoR` keeps the first part's metadata and claims only where the appended elements fit its
    last, part-filled block. -/
theorem appendFoR_nblk {n : Nat} {md pk tail m p : ByteArray} (h : appendFoR n md pk tail = some (m, p)) :
    m = md ∧ n + tail.size / 8 ≤ Column.blk * Column.nblk md := by
  unfold appendFoR at h
  dsimp only at h
  split at h
  · cases h
  rename_i hc
  split at h
  · cases h
  injection h with h; injection h with hm
  refine ⟨hm.symm, ?_⟩
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', not_or] at hc
  obtain ⟨⟨⟨h0, hlt⟩, hs⟩, -⟩ := hc
  rw [(Verify.foRStd_iff.1 (by simpa using hs)).nblk]
  simp only [Column.blk] at *; omega

/-- `concatFoR` of parts of `ns` elements, each fitting a `USize`, answers blocks covering their sum,
    whichever of the move, the append and the re-encode it takes. -/
theorem concatFoR_nblk {w : Nat} (hw0 : 0 < w) (hw : w ≤ 8) {ns : Array Nat} {ms ps : Array ByteArray}
    (hm : ms.size = ns.size) (hp : ps.size = ns.size) (hn : ∀ k ∈ ns.toList, k < USize.size) :
    ns.toList.sum ≤ Column.blk * Column.nblk (concatFoR w.toUSize ns ms ps).1 := by
  have hq : ((ns.zip ms).zip ps).toList.map (·.1.1) = ns.toList := by
    rw [show (fun x : (Nat × ByteArray) × ByteArray => x.1.1) = Prod.fst ∘ Prod.fst from rfl, ← List.map_map,
      Array.toList_zip, List.map_fst_zip (by simp [hp, hm]), Array.toList_zip, List.map_fst_zip (by simp [hm])]
  have hwu : w.toUSize.toNat = w := toUSize_toNat (lt_usize (by omega))
  unfold concatFoR
  dsimp only
  generalize (ns.zip ms).zip ps = q at hq ⊢
  rw [← hq]
  rw [← hq] at hn
  have hb : ∀ x ∈ q.toList, x.1.1.toUSize.toNat = x.1.1 :=
    fun x hx => toUSize_toNat (hn _ (List.mem_map_of_mem hx))
  split
  · rename_i out heq; rcases out with ⟨m, p⟩; exact moveFoR_nblk heq
  rcases q with ⟨_ | ⟨⟨⟨n0, md0⟩, pk0⟩, rest⟩⟩
  · simp
  have hx : (List.toArray (((n0, md0), pk0) :: rest)).extract 1 (rest.length + 1) = rest.toArray := by simp
  simp only [List.size_toArray, List.length_cons, hx]
  rw [show (Array.mk (((n0, md0), pk0) :: rest)).get!Internal 0 = ((n0, md0), pk0) from rfl]
  dsimp only
  have hrest : ∀ x ∈ rest, x.1.1.toUSize.toNat = x.1.1 := fun x hx => hb x (List.mem_cons_of_mem _ hx)
  split
  · rename_i out heq; rcases out with ⟨m, p⟩
    obtain ⟨rfl, hk⟩ := appendFoR_nblk heq
    rw [concatBytes_size] at hk
    simp only [Array.toList_map, List.map_map, Function.comp_def, decode_size] at hk
    have h8 : USize.toNat 8 = 8 := toUSize_toNat (k := 8) (lt_usize (by decide))
    rw [List.map_congr_left (fun x hx => by rw [hrest x hx]), sum_map_mul, h8,
      Nat.mul_div_cancel _ (by decide : 0 < 8)] at hk
    simpa [Nat.add_comm] using hk
  · rw [Verify.nblk_encode w hw0 hw, concatBytes_size]
    simp only [Array.toList_map, List.map_map, Function.comp_def, decode_size, hwu]
    rw [List.map_congr_left (l := ((n0, md0), pk0) :: rest) (f := fun x => x.1.1.toUSize.toNat * w)
        (g := fun x => x.1.1 * w) (fun x hx => by dsimp only; rw [hb x hx]),
      sum_map_mul, Nat.mul_div_cancel _ hw0]
    simp only [Column.blk]; omega

/-- `concatEnum` answers an interned symbol vector whose ids count it. -/
theorem concatEnum_wf (ps : Array (Nat × ByteArray × Array Nat × ByteArray)) :
    ∃ n e, concatEnum ps = .vector .symbol n e none ∧ Enc.WF .symbol n e := by
  unfold concatEnum
  dsimp only
  generalize Array.mapIdx _ ps = qs
  exact ⟨_, _, rfl, hashJoin_wf qs⟩

/-- An `Option` pass whose every answer keeps its argument's key keeps the keys. -/
private theorem mapM_fst {α β : Type} {f : α → Option (Nat × β)} {key : α → Nat}
    (hf : ∀ a x, f a = some x → x.1 = key a) {cs : Array α} {qs : Array (Nat × β)}
    (h : cs.mapM f = some qs) : qs.map (·.1) = cs.map key := by
  have hl : ∀ (l : List α) (ql : List (Nat × β)), l.mapM f = some ql → ql.map (·.1) = l.map key := by
    intro l; induction l with
    | nil => intro ql h; simp at h; subst h; rfl
    | cons a l ih =>
      intro ql h
      rw [List.mapM_cons] at h
      cases ha : f a with
      | none => simp [ha] at h
      | some x =>
        cases hl : l.mapM f with
        | none => simp [ha, hl] at h
        | some xs => simp [ha, hl] at h; subst h; simp [hf _ _ ha, ih _ hl]
  rcases cs with ⟨l⟩
  rw [Array.mapM_eq_mapM_toList] at h
  cases hq : l.mapM f with
  | none => simp [hq] at h
  | some ql => simp [hq] at h; subst h; simp [hl l ql hq]

/-- `encodedParts` keeps every part's count, in order, and a lane per part; it claims only at a type
    one of the two encodings is for. -/
theorem encodedParts_spec {t : QAtomicType} {cs : Array (Nat × Enc)} {alp : Bool} {n : Nat} {ns : Array Nat}
    {ms ps as : Array ByteArray} (h : encodedParts t cs = some (alp, n, ns, ms, ps, as)) :
    alp = Column.alpEncodes t ∧ ns = cs.map (·.1) ∧ n = ns.toList.sum ∧ ms.size = ns.size ∧
      ps.size = ns.size ∧ as.size = ns.size ∧ (Column.alpEncodes t || Column.encodes t) = true := by
  unfold encodedParts at h
  dsimp only at h
  split at h
  · cases h
  rename_i hc
  simp only [bind, Option.bind] at h
  split at h
  · cases h
  rename_i qs hq
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  have hk := mapM_fst (key := (·.1)) (fun c x hx => by
    rcases c with ⟨k, e⟩
    cases e <;> simp only at hx <;> (repeat' split at hx) <;> first | (cases hx; rfl) | cases hx) hq
  refine ⟨rfl, hk, ?_, by simp, by simp, by simp, ?_⟩
  · rw [← Array.foldl_toList, foldl_add_fst]; simp
  · simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hc
    cases h1 : Column.alpEncodes t <;> cases h2 : Column.encodes t <;> simp_all

/-- `concatALP` of parts of `ns` elements, each fitting a `USize`, is a well-formed ALP payload of their
    sum at a float type: it decodes every part at the type's width and encodes the join once. -/
theorem concatALP_wf {t : QAtomicType} {w : Nat} (ht : Column.alpEncodes t = true) (hw : t.width = some w)
    {ns : Array Nat} {ms ps as : Array ByteArray} (hm : ms.size = ns.size) (hp : ps.size = ns.size)
    (ha : as.size = ns.size) (hn : ∀ k ∈ ns.toList, k < USize.size) :
    Enc.WF t ns.toList.sum (.alp (concatALP w.toUSize ns ms ps as).1 (concatALP w.toUSize ns ms ps as).2.1
      (concatALP w.toUSize ns ms ps as).2.2) := by
  obtain ⟨h48, h0⟩ := alp_width ht hw
  have hw8 : w ≤ 8 := by rw [← h48]; split <;> omega
  have hwu : w.toUSize.toNat = w := toUSize_toNat (lt_usize (by omega))
  have h4' : USize.toNat 4 = 4 := toUSize_toNat (k := 4) (lt_usize (by decide))
  have h8' : USize.toNat 8 = 8 := toUSize_toNat (k := 8) (lt_usize (by decide))
  have h4 : (w.toUSize == 4) = (w == 4) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← USize.toNat_inj, hwu, h4']
  have hW : (if (w == 4) = true then (4 : USize) else 8).toNat = w := by
    cases hc : (w == 4) <;> simp only [hc, Bool.false_eq_true, if_false, if_true] at h48 ⊢ <;> omega
  have hl : ((List.range ns.size).map fun k => w * (ns[k]!).toUSize.toNat) = ns.toList.map (fun x => x * w) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    have hk : ns[i] < 2 ^ System.Platform.numBits := hn _ (by simp)
    simp [h1, Nat.mul_comm, Nat.mod_eq_of_lt hk]
  have hsum : ∀ l : List Nat, (l.map (fun x => x * w)).sum = l.sum * w := fun l => by
    induction l <;> simp_all [Nat.add_mul]
  unfold concatALP
  rw [h4]
  refine alpEncodeAt_wf _ ht (by rw [h48]; exact hw) _ ?_
  rw [h48, concatBytes_size]
  simp only [Array.toList_map, Array.toList_range, List.map_map, Function.comp_def,
    alpDecode_size _ (by rw [hW]; exact hw8), hW, hm, hp, ha, Nat.min_self]
  rw [hl, hsum, Nat.mul_div_cancel _ h0]
  exact Nat.le_refl _

/-- `razeColumn` answers a well-formed vector on well-formed parts whose counts, and their sum, fit a
    `USize`: `Enc.answer` decodes an encoded join at its count as a `USize`. -/
theorem razeColumn_wf {t : QAtomicType} {cs : Array (Nat × Enc)}
    (h : ∀ c ∈ cs, Enc.WF t c.1 c.2 ∧ c.1 < USize.size) (hN : cs.foldl (fun s c => s + c.1) 0 < USize.size)
    {v : QValue} (hv : razeColumn t cs = some v) : ∃ n e, v = .vector t n e none ∧ Enc.WF t n e := by
  have hN' : (cs.map (·.1)).toList.sum < USize.size := by
    rw [← Array.foldl_toList, foldl_add_fst] at hN; simpa using hN
  have hn : ∀ k ∈ (cs.map (·.1)).toList, k < USize.size := by
    intro k hk; simp only [Array.toList_map, List.mem_map] at hk
    obtain ⟨c, hc, rfl⟩ := hk; exact (h c (Array.mem_def.2 hc)).2
  have hdense : ∀ w, t.width = some w → t ≠ .boolean →
      ∃ ps, cs.mapM (fun c => Enc.bytesOf t c.1 c.2) = some ps ∧ ps.size = cs.size ∧
        ∀ i (hi : i < cs.size) (hp : i < ps.size), ps[i].size = cs[i].1 * w :=
    fun _ hw hb => dense_parts h hw hb
  unfold razeColumn at hv
  split at hv
  · cases hv
  cases t
  case boolean =>
    dsimp only at hv
    split at hv
    · cases hv; exact ⟨_, _, rfl, concatBits_wf _⟩
    · cases hv
  case symbol =>
    dsimp only at hv
    split at hv
    · cases hv; exact concatSyms_wf _
    · split at hv
      · cases hv; exact concatEnum_wf _
      · cases hv
  case general =>
    dsimp only at hv
    generalize encodedParts _ cs = E at hv
    rcases E with _ | ⟨_, _, _, _, _, _⟩ <;> dsimp only [QAtomicType.width] at hv <;> try cases hv
  all_goals
    dsimp only at hv
    obtain ⟨ps', hps', hsz', hpz'⟩ := hdense _ rfl (by decide)
    generalize hE : encodedParts _ cs = E at hv
    rcases E with _ | ⟨alp, n, ns, ms, ps, as⟩
    · simp only [QAtomicType.width] at hv
      rw [hps'] at hv; simp only at hv
      split at hv
      · cases hv
      · cases hv; exact ⟨_, _, rfl, concatBytes_wf (by decide) rfl hsz' hpz'⟩
    obtain ⟨rfl, rfl, rfl, hms, hps, has, hen⟩ := encodedParts_spec hE
    try (simp [Column.encodes, Column.alpEncodes] at hen; done)
    all_goals
      simp only [QAtomicType.width, Column.alpEncodes, Bool.false_eq_true, if_false, if_true] at hv
      split at hv
      · rw [hps'] at hv; simp only at hv
        split at hv
        · cases hv
        · cases hv; exact ⟨_, _, rfl, concatBytes_wf (by decide) rfl hsz' hpz'⟩
      cases hv
      first
        | exact ⟨_, _, rfl, answer_wf (wf_foR rfl (by decide) (by decide)
            (concatFoR_nblk (by decide) (by decide) hms hps hn)) hN'⟩
        | exact ⟨_, _, rfl, answer_wf (concatALP_wf rfl rfl hms hps has hn) hN'⟩

end LeetQ.Rel.KernelWF
