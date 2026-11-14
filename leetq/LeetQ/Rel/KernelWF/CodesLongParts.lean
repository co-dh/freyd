/-
  An eight-byte integral side of several dense parts where `rangeOffsets` declines: its codes are those of
  its `raze`, grouped once and cut back, so faithful jointly across the parts and well formed.
-/
import LeetQ.Rel.KernelWF.CodesProd

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

/-! ## `enumIds`' failure index -/

/-- The first index below `n` a test flags, `n` when it flags none: `n` exactly when it flags none. -/
theorem find_getD_toUSize (P : Nat → Bool) (n : USize) :
    (((List.range n.toNat).find? P).getD n.toNat).toUSize = n ↔ ∀ i < n.toNat, P i = false := by
  cases hf : (List.range n.toNat).find? P with
  | none =>
    simp only [Option.getD_none]
    refine ⟨fun _ i hi => by simpa using List.find?_eq_none.1 hf i (List.mem_range.2 hi), fun _ => ?_⟩
    exact USize.toNat_inj.1 (USize.toNat_ofNat_of_lt' (USize.toNat_lt_size n))
  | some j =>
    have hj := List.mem_range.1 (List.mem_of_find?_eq_some hf)
    have hP := List.find?_some hf
    simp only [Option.getD_some]
    refine ⟨fun h => absurd (congrArg USize.toNat h) ?_, fun h => by rw [h j hj] at hP; cases hP⟩
    rw [USize.toNat_ofNat_of_lt' (Nat.lt_trans hj (USize.toNat_lt_size n))]; omega

/-- **`enumIds` reports no failure (`n`) exactly when each of its first `n` words is the null `0N` or an index
    below `d`.** -/
theorem enumIds_bad (n d nullId w : USize) (b : ByteArray) :
    (enumIds n d nullId w b).2 = n ↔ ∀ i < n.toNat, (Ew.elem Ew.i64 b i).toInt64 = Int64.minValue ∨
      (0 ≤ (Ew.elem Ew.i64 b i).toInt64 ∧ (Ew.elem Ew.i64 b i).toInt64.toInt.toNat < d.toNat) := by
  simp only [enumIds, Ew.elem, show Ew.width Ew.i64 = 8 from rfl]
  rw [find_getD_toUSize]
  refine forall_congr' fun i => imp_congr_right fun _ => ?_
  by_cases h1 : (Column.bitsAt b (i * 8) 8).toInt64 = Int64.minValue <;>
    by_cases h2 : (0 ≤ (Column.bitsAt b (i * 8) 8).toInt64) <;> simp [h1, h2]

/-! ## A dense long part rebased: each word is a function of the word read -/

/-- `one v`'s only word is `v`. -/
theorem elem_one (v : UInt64) : Ew.elem Ew.i64 (one v) 0 = v := elem_atomBytes_i64 v

/-- **`rangeOffsets`' rebasing of a dense part**: word `i` of the rebased payload is the rebasing of word `i`. -/
theorem elem_shift (b : ByteArray) (n : USize) (base : Int64) {i : Nat} (hi : i < n.toNat) :
    Ew.elem Ew.i64 (if base == 0 then b else Ew.val Ew.add Ew.i64 Ew.va nul b (one (-base).toUInt64) n) i =
      if base == 0 then Ew.elem Ew.i64 b i else
        Ew.valStep Ew.add Ew.i64 nul.toUInt64 (Ew.elem Ew.i64 b i) (-base).toUInt64 := by
  split
  · rfl
  · rw [elem_val _ _ _ _ _ _ _ hi, show 8 * Ew.width Ew.i64 = 64 from rfl, Nat.mod_eq_of_lt (UInt64.toNat_lt _),
      UInt64.ofNat_toNat]
    show Ew.valStep _ _ _ _ (Ew.elem Ew.i64 (one (-base).toUInt64) 0) = _
    rw [elem_one]; rfl

/-! ## Words of dense payloads laid end to end -/

theorem elem_append_left (a x : ByteArray) {A i : Nat} (ha : a.size = A * 8) (hi : i < A) :
    Ew.elem Ew.i64 (a ++ x) i = Ew.elem Ew.i64 a i := by
  show Column.bitsAt (a ++ x) (i * 8) 8 = Column.bitsAt a (i * 8) 8
  refine KernelWF.bitsAt_congr fun j hj => ?_
  rw [ByteArray.data_append, Array.getElem?_append_left (by rw [ByteArray.size_data]; omega)]

theorem elem_append_right (a x : ByteArray) {A : Nat} (ha : a.size = A * 8) (i : Nat) :
    Ew.elem Ew.i64 (a ++ x) (A + i) = Ew.elem Ew.i64 x i := by
  show Column.bitsAt (a ++ x) ((A + i) * 8) 8 = Column.bitsAt x (i * 8) 8
  refine KernelWF.bitsAt_congr fun j hj => ?_
  rw [ByteArray.data_append, Array.getElem?_append_right (by rw [ByteArray.size_data]; omega), ByteArray.size_data,
    ha]
  congr 1; omega

/-- The words of dense payloads appended to `acc` are `acc`'s words and each payload's. -/
theorem words_foldl {t : QAtomicType} (g : ((n : USize) × Arr t n) → ByteArray) :
    ∀ (l : List ((n : USize) × Arr t n)) (acc : ByteArray) (A : Nat), acc.size = A * 8 →
      (∀ c ∈ l, (g c).size = c.1.toNat * 8) → ∀ v,
      (∃ i < A + (l.map (·.1.toNat)).sum, Ew.elem Ew.i64 (l.foldl (fun a c => a ++ g c) acc) i = v) ↔
        (∃ i < A, Ew.elem Ew.i64 acc i = v) ∨ ∃ c ∈ l, ∃ i < c.1.toNat, Ew.elem Ew.i64 (g c) i = v
  | [], acc, A, _, _, v => by simp
  | c :: l, acc, A, ha, hl, v => by
    have hc := hl c (by simp)
    have ih := words_foldl g l (acc ++ g c) (A + c.1.toNat) (by rw [ByteArray.size_append, ha, hc, Nat.add_mul])
      (fun d hd => hl d (by simp [hd])) v
    simp only [List.map_cons, List.sum_cons, List.foldl_cons, ← Nat.add_assoc, ih, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (⟨i, hi, rfl⟩ | h)
      · by_cases h' : i < A
        · exact .inl ⟨i, h', (elem_append_left _ _ ha h').symm⟩
        · refine .inr (.inl ⟨i - A, by omega, ?_⟩)
          rw [← elem_append_right acc (g c) ha, Nat.add_sub_cancel' (by omega)]
      · exact .inr (.inr h)
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ | h)
      · exact .inl ⟨i, by omega, elem_append_left _ _ ha hi⟩
      · exact .inl ⟨A + i, by omega, elem_append_right _ _ ha i⟩
      · exact .inr h

/-- **The `raze` of dense long parts is dense, its words exactly its parts' words.** -/
theorem raze_words {t : QAtomicType} (ht : orderKind t = some .i64) (cs : Array ((n : USize) × Arr t n))
    (hcs : ∀ c ∈ cs, ∃ b, c.2.enc = .bytes b) (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (h0 : cs.size ≠ 0) :
    ∃ B, (raze t cs).2.enc = .bytes B ∧ ∀ v, (∃ i < (raze t cs).1.toNat, Ew.elem Ew.i64 B i = v) ↔
      ∃ c ∈ cs, ∃ b, c.2.enc = .bytes b ∧ ∃ i < c.1.toNat, Ew.elem Ew.i64 b i = v := by
  obtain ⟨hw, -, hg, -, -⟩ := long_facts ht
  have hbo : t ≠ .boolean := by rintro rfl; simp [orderKind] at ht
  rcases cs with ⟨l⟩
  simp only [List.mem_toArray] at hcs ⊢
  have hl0 : l ≠ [] := by rintro rfl; exact h0 rfl
  by_cases h1 : l.length = 1
  · obtain ⟨c, rfl⟩ := List.length_eq_one_iff.1 h1
    obtain ⟨b, hb⟩ := hcs c (by simp)
    have hr : raze t #[c] = c := by unfold raze; simp [hg]
    refine ⟨b, by rw [hr, hb], fun v => ?_⟩
    rw [hr]; simp [hb]
  unfold raze
  rw [dif_neg (by simpa using hl0), dif_neg hg, dif_neg (by simpa using h1)]
  dsimp only
  have key : ∀ (a : Nat) (l : List ((n : USize) × Arr t n)),
      (l.map fun x => (x.1, x.2.enc)).foldl (fun s c => s + c.1.toNat) a = a + (l.map (·.1.toNat)).sum := by
    intro a l; induction l generalizing a <;> simp_all [Nat.add_assoc]
  have hk : ((List.toArray l).map (·.2.part)).foldl (fun s c => s + c.1.toNat) 0 = (l.map (·.1.toNat)).sum := by
    simpa [Arr.part] using key 0 l
  have hf : ((List.toArray l).map (·.2.part)).foldl (fun s c => s + c.1.toNat) 0 < USize.size := by
    rw [hk]; simpa using hN
  unfold need; rw [dif_pos hf]
  have hps : ∀ c ∈ (List.toArray l).map (·.2.part), ∃ b, c.2 = .bytes b := by
    intro c hc; obtain ⟨d, hd, rfl⟩ := Array.mem_map.1 hc; exact hcs d (by simpa using hd)
  let gb : ((n : USize) × Arr t n) → ByteArray := fun c => (Enc.bytesOf t c.1 c.2.enc).getD .empty
  have hB : concatBytes (((List.toArray l).map (·.2.part)).map fun c => (Enc.bytesOf t c.1 c.2).getD .empty) =
      l.foldl (fun a c => a ++ gb c) .empty := by
    simp only [concatBytes, Array.foldl_map, List.foldl_toArray', Arr.part, gb]
  have hv : ∀ h, ((razeColumn t ((List.toArray l).map (·.2.part))).get h) =
      .vector t (((List.toArray l).map (·.2.part)).foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize
        (.bytes (l.foldl (fun a c => a ++ gb c) .empty)) none := fun h => by
    rw [← hB]; exact KernelWF.razeColumn_dense hw hbo (fun c hc => by
      obtain ⟨d, -, rfl⟩ := Array.mem_map.1 hc; exact d.2.wf)
      (fun r hr => by rw [KernelWF.encodedParts_bytes hps] at hr; cases hr) (Option.some_get h).symm
  have hgb : ∀ c ∈ l, c.2.enc = .bytes (gb c) := fun c hc => by
    obtain ⟨b, hb⟩ := hcs c hc; simp [gb, hb, Enc.bytesOf]
  have hsz : ∀ c ∈ l, (gb c).size = c.1.toNat * 8 := fun c hc => by
    obtain ⟨b, hb, hs⟩ := KernelWF.bytesOf_size hbo hw c.2.wf
    simp only [gb, hb, Option.getD_some]; exact hs
  have hN' : (((List.toArray l).map (·.2.part)).foldl (fun s (c : USize × Enc) => s + c.1.toNat) 0).toUSize.toNat =
      (l.map (·.1.toNat)).sum := by rw [USize.toNat_ofNat_of_lt' hf, hk]
  refine ⟨l.foldl (fun a c => a ++ gb c) .empty, by simp only [Arr.enc, hv], fun v => ?_⟩
  have hW := words_foldl gb l .empty 0 rfl hsz v
  rw [Nat.zero_add] at hW
  simp only [hN', hW, Nat.not_lt_zero, false_and, exists_false, false_or]
  constructor
  · rintro ⟨c, hc, i, hi, rfl⟩; exact ⟨c, hc, gb c, hgb c hc, i, hi, rfl⟩
  · rintro ⟨c, hc, b, hb, i, hi, rfl⟩
    rw [hgb c hc] at hb; cases hb; exact ⟨c, hc, i, hi, rfl⟩

/-! ## `mapM` in `Option` that declines: some element declines -/

theorem ite_none {β : Type} {c : Prop} [Decidable c] {x : β} : (if c then none else some x) = none ↔ c := by
  by_cases h : c <;> simp [h]

theorem list_mapM_none {α β : Type} {f : α → Option β} : ∀ {l : List α}, l.mapM f = none ↔ ∃ x ∈ l, f x = none
  | [] => by simp [pure]
  | a :: l => by
    have ih := list_mapM_none (f := f) (l := l)
    rw [List.mapM_cons]
    cases h : f a <;> cases h' : l.mapM f <;> simp_all [bind, pure]

theorem arr_mapM_none {α β : Type} {f : α → Option β} {xs : Array α} :
    xs.mapM f = none ↔ ∃ k, ∃ hk : k < xs.size, f (xs[k]'hk) = none := by
  rw [Array.mapM_eq_mapM_toList]
  cases hm : xs.toList.mapM f with
  | none =>
    obtain ⟨x, hx, hn⟩ := list_mapM_none.1 hm
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    exact ⟨fun _ => ⟨k, by simpa using hk, by simpa using hn⟩, fun _ => rfl⟩
  | some ys =>
    refine ⟨fun h => by simp at h, fun ⟨k, hk, hn⟩ => absurd hm ?_⟩
    rw [list_mapM_none.2 ⟨xs[k], by simp, hn⟩]; simp

theorem vec_mapM_none {α β : Type} {p : Nat} {f : α → Option β} {xs : Vector α p} :
    xs.mapM f = none ↔ ∃ k, ∃ hk : k < p, f (xs[k]'hk) = none := by
  have hl : xs.toArray.mapM f = none ↔ ∃ k, ∃ hk : k < p, f (xs[k]'hk) = none := by
    rw [arr_mapM_none]
    exact ⟨fun ⟨k, hk, hn⟩ => ⟨k, by simpa using hk, by simpa using hn⟩,
      fun ⟨k, hk, hn⟩ => ⟨k, by simpa using hk, by simpa using hn⟩⟩
  rw [← hl]
  cases h : xs.mapM f with
  | none => simp only [true_iff]; rw [← Vector.toArray_mapM, h]; rfl
  | some ys => simp only [reduceCtorEq, false_iff]; rw [← Vector.toArray_mapM, h]; simp

/-! ## The joint extremes of dense long parts -/

/-- A fold whose step answers one of its two operands answers its seed or an element. -/
theorem foldl_mem {g : Int64 → Int64 → Int64} (hg : ∀ a y, g a y = a ∨ g a y = y) :
    ∀ (l : List Int64) (s : Int64), l.foldl g s = s ∨ l.foldl g s ∈ l
  | [], s => .inl rfl
  | y :: l, s => by
    rw [List.foldl_cons]
    rcases foldl_mem hg l (g s y) with h | h
    · rcases hg s y with h' | h' <;> rw [h, h']
      · exact .inl rfl
      · exact .inr (by simp)
    · exact .inr (List.mem_cons_of_mem _ h)

theorem min_max_step (a y : Int64) : (min a y = a ∨ min a y = y) ∧ (min a y).toInt ≤ a.toInt ∧
    (min a y).toInt ≤ y.toInt ∧ (max a y = a ∨ max a y = y) ∧ a.toInt ≤ (max a y).toInt ∧ y.toInt ≤ (max a y).toInt := by
  rw [show min a y = if a ≤ y then a else y from rfl, show max a y = if a ≤ y then y else a from rfl]
  by_cases h : a ≤ y
  · have := Int64.le_iff_toInt_le.1 h; rw [if_pos h, if_pos h]
    exact ⟨.inl rfl, by omega, by omega, .inr rfl, by omega, by omega⟩
  · have := mt Int64.le_iff_toInt_le.2 h; rw [if_neg h, if_neg h]
    exact ⟨.inr rfl, by omega, by omega, .inl rfl, by omega, by omega⟩

/-- Two extremes of one set under one order, each the seed `m` or a member, are equal. -/
theorem extreme_unique {S : Int64 → Prop} {m r r' : Int64} (f : Int64 → Int) (hf : ∀ a b, f a = f b → a = b)
    (hr : (r = m ∨ S r) ∧ f r ≤ f m ∧ ∀ x, S x → f r ≤ f x)
    (hr' : (r' = m ∨ S r') ∧ f r' ≤ f m ∧ ∀ x, S x → f r' ≤ f x) : r = r' := by
  obtain ⟨h1, h2, h3⟩ := hr
  obtain ⟨h1', h2', h3'⟩ := hr'
  apply hf; apply Int.le_antisymm
  · rcases h1' with rfl | h
    · exact h2
    · exact h3 _ h
  · rcases h1 with rfl | h
    · exact h2'
    · exact h3' _ h

/-- **`rangeOffsets`' bounds over dense long parts**: the joint minimum is `0W` or a non-null word, at most
    every non-null word; the joint maximum is `-0W` or a non-null word, at least every one. `Wp` names the words. -/
theorem lo_hi {p : Nat} (cs : Vector (USize × Enc) p) (los his : Array Int64) (hs : los.size = p) (hs' : his.size = p)
    (hl : ∀ k (hk : k < p) b, (cs[k]'hk).2 = .bytes b → los[k]'(by rw [hs]; exact hk) = overBytes .lesser Ew.i64 nul b)
    (hh : ∀ k (hk : k < p) b, (cs[k]'hk).2 = .bytes b → his[k]'(by rw [hs']; exact hk) = overBytes .greater Ew.i64 nul b)
    (hd : ∀ k (hk : k < p), ∃ b, (cs[k]'hk).2 = .bytes b ∧ b.size = (cs[k]'hk).1.toNat * 8) (Wp : UInt64 → Prop)
    (hW : ∀ v, Wp v ↔ ∃ k, ∃ hk : k < p, ∃ b, (cs[k]'hk).2 = .bytes b ∧ ∃ i < (cs[k]'hk).1.toNat, Ew.elem Ew.i64 b i = v) :
    ((los.foldl min Int64.maxValue = Int64.maxValue ∨
        (los.foldl min Int64.maxValue ≠ nul ∧ ∃ v, Wp v ∧ v.toInt64 = los.foldl min Int64.maxValue)) ∧
      (los.foldl min Int64.maxValue).toInt ≤ Int64.maxValue.toInt ∧
      ∀ x, (x ≠ nul ∧ ∃ v, Wp v ∧ v.toInt64 = x) → (los.foldl min Int64.maxValue).toInt ≤ x.toInt) ∧
    ((his.foldl max (Int64.minValue + 1) = Int64.minValue + 1 ∨
        (his.foldl max (Int64.minValue + 1) ≠ nul ∧ ∃ v, Wp v ∧ v.toInt64 = his.foldl max (Int64.minValue + 1))) ∧
      -(his.foldl max (Int64.minValue + 1)).toInt ≤ -(Int64.minValue + 1).toInt ∧
      ∀ x, (x ≠ nul ∧ ∃ v, Wp v ∧ v.toInt64 = x) → -(his.foldl max (Int64.minValue + 1)).toInt ≤ -x.toInt) := by
  have hseed : Coc.Over.denseSeed .lesser Ew.i64 nul = Int64.maxValue ∧
      Coc.Over.denseSeed .greater Ew.i64 nul = Int64.minValue + 1 := by decide
  -- a part's extreme is the seed or one of its non-null words
  have hpart : ∀ (op : Coc.Over), op = .lesser ∨ op = .greater → ∀ b : ByteArray,
      overBytes op Ew.i64 nul b = op.denseSeed Ew.i64 nul ∨ (overBytes op Ew.i64 nul b ≠ nul ∧
        ∃ i < b.size / 8, (Ew.elem Ew.i64 b i).toInt64 = overBytes op Ew.i64 nul b) := by
    intro op hop b
    rw [overBytes_eq, overList]
    have hst : ∀ a y, op.step a y = a ∨ op.step a y = y := by
      intro a y; rcases hop with rfl | rfl <;> simp only [Coc.Over.step] <;> split <;> simp
    rcases foldl_mem hst _ (op.denseSeed Ew.i64 nul) with h | h
    · exact .inl h
    · right
      obtain ⟨hm, hn⟩ := List.mem_filter.1 h
      simp only [denseElems, List.mem_map, List.mem_range] at hm
      obtain ⟨i, hi, he⟩ := hm
      refine ⟨by rcases hop with rfl | rfl <;> simpa [Coc.Over.boolCast] using hn, i, hi, he⟩
  have hwd : ∀ k (hk : k < p) b, (cs[k]'hk).2 = .bytes b → b.size = (cs[k]'hk).1.toNat * 8 := fun k hk b hb => by
    obtain ⟨b', hb', hs⟩ := hd k hk; rw [hb] at hb'; cases hb'; exact hs
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  obtain ⟨hlS, hlx⟩ := foldl_le (fun a y => ⟨(min_max_step a y).2.1, (min_max_step a y).2.2.1⟩) los.toList Int64.maxValue
  obtain ⟨hhS, hhx⟩ := foldl_ge (fun a y => ⟨(min_max_step a y).2.2.2.2.1, (min_max_step a y).2.2.2.2.2⟩)
    his.toList (Int64.minValue + 1)
  refine ⟨⟨?_, hlS, ?_⟩, ⟨?_, by omega, ?_⟩⟩
  · rcases foldl_mem (fun a y => (min_max_step a y).1) los.toList Int64.maxValue with h | h
    · exact .inl h
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.1 h
    have hk' : k < p := by simpa [hs] using hk
    obtain ⟨b, hb, -⟩ := hd k hk'
    simp only [Array.getElem_toList] at he
    rw [← he, hl k hk' b hb]
    rcases hpart .lesser (.inl rfl) b with h' | ⟨hn, i, hi, hv⟩
    · exact .inl (h'.trans hseed.1)
    · refine .inr ⟨hn, _, (hW _).2 ⟨k, hk', b, hb, i, by rw [hwd k hk' b hb] at hi; omega, rfl⟩, hv⟩
  · rintro x ⟨hn, v, hv, rfl⟩
    obtain ⟨k, hk, b, hb, i, hi, rfl⟩ := (hW v).1 hv
    have h1 := hlx (los[k]'(by rw [hs]; exact hk)) (by simp)
    rw [hl k hk b hb] at h1
    have h2 := (overBytes_extreme Ew.i64 nul b (i := i)
      (by rw [show Ew.width Ew.i64 = 8 from rfl, hwd k hk b hb]; omega) hn).1
    exact Int.le_trans h1 h2
  · rcases foldl_mem (fun a y => (min_max_step a y).2.2.2.1) his.toList (Int64.minValue + 1) with h | h
    · exact .inl h
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.1 h
    have hk' : k < p := by simpa [hs'] using hk
    obtain ⟨b, hb, -⟩ := hd k hk'
    simp only [Array.getElem_toList] at he
    rw [← he, hh k hk' b hb]
    rcases hpart .greater (.inr rfl) b with h' | ⟨hn, i, hi, hv⟩
    · exact .inl (h'.trans hseed.2)
    · refine .inr ⟨hn, _, (hW _).2 ⟨k, hk', b, hb, i, by rw [hwd k hk' b hb] at hi; omega, rfl⟩, hv⟩
  · rintro x ⟨hn, v, hv, rfl⟩
    obtain ⟨k, hk, b, hb, i, hi, rfl⟩ := (hW v).1 hv
    have h1 := hhx (his[k]'(by rw [hs']; exact hk)) (by simp)
    rw [hh k hk b hb] at h1
    have h2 : (Ew.elem Ew.i64 b i).toInt64.toInt ≤ (overBytes .greater Ew.i64 nul b).toInt :=
      (overBytes_extreme Ew.i64 nul b (i := i) (by rw [show Ew.width Ew.i64 = 8 from rfl, hwd k hk b hb]; omega) hn).2
    omega

/-- **`rangeOffsets` over dense long parts reads only their words and the total**: two sides of dense parts
    holding the same words, at one total, decline together. -/
theorem rangeOffsets_dense_none {a : QAtomicType} {p p' : Nat} (cs : Vector (USize × Enc) p)
    (cs' : Vector (USize × Enc) p') (total : Nat)
    (hd : ∀ k (hk : k < p), ∃ b, (cs[k]'hk).2 = .bytes b ∧ b.size = (cs[k]'hk).1.toNat * 8)
    (hd' : ∀ k (hk : k < p'), ∃ b, (cs'[k]'hk).2 = .bytes b ∧ b.size = (cs'[k]'hk).1.toNat * 8)
    (hW : ∀ v, (∃ k, ∃ hk : k < p, ∃ b, (cs[k]'hk).2 = .bytes b ∧ ∃ i < (cs[k]'hk).1.toNat, Ew.elem Ew.i64 b i = v) ↔
      ∃ k, ∃ hk : k < p', ∃ b, (cs'[k]'hk).2 = .bytes b ∧ ∃ i < (cs'[k]'hk).1.toNat, Ew.elem Ew.i64 b i = v)
    (h : rangeOffsets a cs total = none) : rangeOffsets a cs' total = none := by
  unfold rangeOffsets at h ⊢
  split
  · rfl
  next g0 =>
  rw [if_neg g0] at h
  dsimp only at h ⊢
  split at h
  · next hn =>
    obtain ⟨k, hk, hf⟩ := arr_mapM_none.1 hn
    obtain ⟨b, hb, -⟩ := hd k (by simpa using hk)
    simp [hb] at hf
  next los hlos =>
  split at h
  · next hn =>
    obtain ⟨k, hk, hf⟩ := arr_mapM_none.1 hn
    obtain ⟨b, hb, -⟩ := hd k (by simpa using hk)
    simp [hb] at hf
  next his hhis =>
  split
  · rfl
  next los' hlos' =>
  split
  · rfl
  next his' hhis' =>
  obtain ⟨hls, hl⟩ := arr_mapM_some hlos
  obtain ⟨hhs, hh⟩ := arr_mapM_some hhis
  obtain ⟨hls', hl'⟩ := arr_mapM_some hlos'
  obtain ⟨hhs', hh'⟩ := arr_mapM_some hhis'
  obtain ⟨Wp, hWp⟩ : ∃ Wp : UInt64 → Prop, ∀ v, Wp v ↔ ∃ k, ∃ hk : k < p, ∃ b, (cs[k]'hk).2 = .bytes b ∧
      ∃ i < (cs[k]'hk).1.toNat, Ew.elem Ew.i64 b i = v := ⟨_, fun _ => Iff.rfl⟩
  have E := lo_hi cs los his (by simpa using hls) (by simpa using hhs)
    (fun k hk b hb => by have := hl k (by simpa using hk); simp [hb] at this; exact this.symm)
    (fun k hk b hb => by have := hh k (by simpa using hk); simp [hb] at this; exact this.symm) hd Wp hWp
  have E' := lo_hi cs' los' his' (by simpa using hls') (by simpa using hhs')
    (fun k hk b hb => by have := hl' k (by simpa using hk); simp [hb] at this; exact this.symm)
    (fun k hk b hb => by have := hh' k (by simpa using hk); simp [hb] at this; exact this.symm) hd' Wp
    (fun v => (hWp v).trans (hW v))
  have hL := extreme_unique (S := fun x => x ≠ nul ∧ ∃ v, Wp v ∧ v.toInt64 = x) Int64.toInt
    (fun a b e => Int64.toInt_inj.1 e) E'.1 E.1
  have hH := extreme_unique (S := fun x => x ≠ nul ∧ ∃ v, Wp v ∧ v.toInt64 = x) (fun x => -x.toInt)
    (fun a b e => Int64.toInt_inj.1 (Int.neg_inj.1 e)) E'.2 E.2
  rw [hL, hH]
  split
  · rfl
  next g1 =>
  rw [if_neg g1] at h
  split
  · rfl
  next g2 =>
  rw [if_neg g2] at h
  -- `split` meets the base `0` or `lo` first, then the last guard
  split <;> rename_i hb0
  all_goals first | rw [if_pos hb0] at h | rw [if_neg hb0] at h
  all_goals
    split
    · rfl
    rename_i g3
    rw [if_neg g3] at h
    -- a part of `cs` declines: one of its words rebases outside the codes; that word is a word of `cs'`
    obtain ⟨k, hk, hf⟩ := vec_mapM_none.1 h
    obtain ⟨b, hb, -⟩ := hd k hk
    simp only [hb, beq_self_eq_true, ite_true] at hf
    obtain ⟨i, hi⟩ := Classical.not_forall.1 (mt (enumIds_bad _ _ _ _ _).2 ((bne_iff_ne).1 (ite_none.1 hf)))
    obtain ⟨hi, hgi⟩ := Classical.not_imp.1 hi
    try rw [elem_shift _ _ _ hi] at hgi
    obtain ⟨k', hk', b', hb', i', hi', hv⟩ := (hW _).1 ⟨k, hk, b, hb, i, hi, rfl⟩
    refine vec_mapM_none.2 ⟨k', hk', ?_⟩
    simp only [hb', beq_self_eq_true, ite_true]
    refine ite_none.2 ((bne_iff_ne).2 fun hok => hgi ?_)
    have := (enumIds_bad _ _ _ _ _).1 hok i' hi'
    try rw [elem_shift _ _ _ hi'] at this
    rw [hv] at this
    exact this

/-- **`rangeOffsets` declines the `raze` of dense long parts where it declines the parts**: the razed column is
    dense, holds exactly the parts' words, and counts their total. -/
theorem rangeOffsets_raze_none {t : QAtomicType} (ht : orderKind t = some .i64) {p : Nat}
    (cs : Vector (Part (.atom t)) p) (hp : 0 < p) (hd : ∀ k (hk : k < p), ∃ b, (cs[k]'hk).2.enc = .bytes b)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hro : rangeOffsets t (cs.map (·.2.part)) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) = none) :
    rangeOffsets t (#v[raze t cs.toArray].map fun c => Arr.part c.2)
      ((#v[raze t cs.toArray].map (·.1)).foldl (fun s n => s + n.toNat) 0) = none := by
  obtain ⟨B, hB, hWB⟩ := raze_words ht cs.toArray (fun c hc => by
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hc; simpa using hd k (by simpa using hk))
    (by simpa using hN) (by simp; omega)
  have hX := raze_len t cs.toArray (by simpa using hN)
  have hBs : B.size = (raze t cs.toArray).1.toNat * 8 := by
    rcases long_enc ht (raze t cs.toArray).2.wf with ⟨b, hb, hs⟩ | ⟨md, pk, hb⟩ <;> rw [hB] at hb <;> cases hb
    exact hs
  have hf : ∀ (l : List USize) (a : Nat), l.foldl (fun s n => s + n.toNat) a = a + (l.map (·.toNat)).sum := by
    intro l; induction l <;> intro a <;> simp_all [Nat.add_assoc]
  have htot : (#v[raze t cs.toArray].map (·.1)).foldl (fun s n => s + n.toNat) 0 =
      (cs.map (·.1)).foldl (fun s n => s + n.toNat) 0 := by
    show (#v[raze t cs.toArray].map (·.1)).toArray.foldl _ 0 = (cs.map (·.1)).toArray.foldl _ 0
    rw [← Array.foldl_toList, ← Array.foldl_toList, hf, hf]
    simp [hX, Function.comp_def]
  rw [htot]
  refine rangeOffsets_dense_none _ _ _ (fun k hk => ?_) (fun k hk => ?_) (fun v => ?_) hro
  · obtain ⟨b, hb, hs⟩ := (long_enc ht (cs[k]'hk).2.wf).resolve_right (by
      rintro ⟨md, pk, he⟩; obtain ⟨b, hb⟩ := hd k hk; rw [hb] at he; cases he)
    exact ⟨b, by simp [Arr.part, hb], by simpa [Arr.part] using hs⟩
  · obtain rfl : k = 0 := by omega
    exact ⟨B, by simp [Arr.part, hB], by simpa [Arr.part] using hBs⟩
  · simp only [Vector.getElem_map, Arr.part]
    constructor
    · rintro ⟨k, hk, b, hb, i, hi, rfl⟩
      obtain ⟨i', hi', he⟩ := (hWB _).2 ⟨cs[k], by simp, b, hb, i, hi, rfl⟩
      exact ⟨0, by omega, B, by simpa using hB, i', by simpa using hi', he⟩
    · rintro ⟨k, hk, b, hb, i, hi, rfl⟩
      obtain rfl : k = 0 := by omega
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, hB, Enc.bytes.injEq] at hb hi
      subst hb
      obtain ⟨c, hc, b', hb', i', hi', he⟩ := (hWB _).1 ⟨i, hi, rfl⟩
      obtain ⟨k', hk', rfl⟩ := Array.mem_iff_getElem.1 hc
      exact ⟨k', by simpa using hk', b', by simpa using hb', i', by simpa using hi', he⟩

/-- **A long side of several dense parts, `rangeOffsets` declining the parts: its codes are those of the
    `raze`, cut back**, the parts' summed count a `USize`. -/
theorem codes_long_cut {t : QAtomicType} (ht : orderKind t = some .i64) {p : Nat} (cs : Vector (Part (.atom t)) p)
    (hp : 0 < p) (hd : ∀ k (hk : k < p), ∃ b, (cs[k]'hk).2.enc = .bytes b)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hro : rangeOffsets t (cs.map (·.2.part)) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) = none) :
    Obj.codes (.atom t) cs = (Obj.codes (.atom t) #v[raze t cs.toArray])[0].cut (cs.map (·.1)) := by
  have hroR := rangeOffsets_raze_none ht cs hp hd hN hro
  obtain ⟨-, -, hg, -, -⟩ := long_facts ht
  have hne : ∀ d o ids, Column.intern (raze t cs.toArray).2.enc ≠ .enum d o ids := fun d o ids he => by
    rcases long_enc ht (raze t cs.toArray).2.wf with ⟨b, hb, -⟩ | ⟨md, pk, hb⟩ <;> simp [hb, Column.intern] at he
  obtain ⟨q, hq, hc⟩ := codes_raze_cut hg cs hp (fun k hk b he => by
    obtain ⟨b', hb'⟩ := hd k hk; rw [hb'] at he; cases he) hro hne
  obtain ⟨q', hq', hc'⟩ := codes_long_group ht (raze t cs.toArray) hroR
  have hbt : KernelWF.bitsType t = t := by cases t <;> simp [orderKind] at ht <;> rfl
  rw [hbt] at hq
  rw [hc, hc', show q' = q from Option.some_inj.1 (hq'.symm.trans hq)]

/-- **A long side of several dense parts where `rangeOffsets` declines: its codes are faithful jointly
    across the parts**, the parts' summed count a `USize`. -/
theorem codes_long_parts_faithful {t : QAtomicType} (ht : orderKind t = some .i64) {p : Nat}
    (cs : Vector (Part (.atom t)) p) (hd : ∀ k (hk : k < p), ∃ b, (cs[k]'hk).2.enc = .bytes b)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hro : rangeOffsets t (cs.map (·.2.part)) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) = none)
    {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (cs[k]'hk).1.toNat) (hj : j < (cs[l]'hl).1.toNat) :
    Column.idAt ((Obj.codes (.atom t) cs)[k]'hk).b ((Obj.codes (.atom t) cs)[k]'hk).w i =
        Column.idAt ((Obj.codes (.atom t) cs)[l]'hl).b ((Obj.codes (.atom t) cs)[l]'hl).w j ↔
      Vals.row (cs[k]'hk).2 ⟨i, hi⟩ = Vals.row (cs[l]'hl).2 ⟨j, hj⟩ := by
  have hroR := rangeOffsets_raze_none ht cs (by omega) hd hN hro
  have hW : t.width = some 8 := by cases t <;> simp [orderKind] at ht <;> rfl
  have hB : t ≠ .boolean := by rintro rfl; simp [orderKind] at ht
  have hE := encodedParts_parts_bytes (t := t) cs hd
  have hX := raze_len t cs.toArray hN
  obtain ⟨hw, hn, -, -⟩ := codes_long_group_wf ht (raze t cs.toArray) hroR
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum = (Obj.codes (.atom t) #v[raze t cs.toArray])[0].n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hO : ∀ k, (((cs.map (·.1)).toList.take k).map (·.toNat)).sum = ((cs.toList.take k).map (·.1.toNat)).sum :=
    fun k => by rw [Vector.toList_map, ← List.map_take, List.map_map]; rfl
  have hlt : ∀ k (hk : k < p), ∀ i < (cs[k]'hk).1.toNat,
      ((cs.toList.take k).map (·.1.toNat)).sum + i < (raze t cs.toArray).1.toNat := fun k hk i hi => by
    have := take_sum_le (cs.toList.map (·.1.toNat)) (k := k) (by simpa using hk)
    simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take] at this
    rw [hX]; exact Nat.lt_of_lt_of_le (by omega) this
  rw [codes_long_cut ht cs (by omega) hd hN hro]
  obtain ⟨hwk, -, -, hck⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  obtain ⟨hwl, -, -, hcl⟩ := cut_get _ (cs.map (·.1)) hw hs hl
  rw [hwk, hwl, hck i (by simpa using hi), hcl j (by simpa using hj), hO, hO,
    codes_long_group_faithful ht _ hroR (hlt k hk i hi) (hlt l hl j hj), Vals.row_atom, Vals.row_atom,
    Vals.row_atom, Vals.row_atom, raze_get_bytes hW hB cs (fun r hr => by rw [hE] at hr; cases hr) hN hk hi,
    raze_get_bytes hW hB cs (fun r hr => by rw [hE] at hr; cases hr) hN hl hj]

/-- **A long side of several dense parts where `rangeOffsets` declines: each part's code is well formed**,
    the parts' summed count a `USize`. -/
theorem codes_long_parts_wf {t : QAtomicType} (ht : orderKind t = some .i64) {p : Nat}
    (cs : Vector (Part (.atom t)) p) (hd : ∀ k (hk : k < p), ∃ b, (cs[k]'hk).2.enc = .bytes b)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hro : rangeOffsets t (cs.map (·.2.part)) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) = none)
    {k : Nat} (hk : k < p) :
    let c := (Obj.codes (.atom t) cs)[k]'hk
    laneOK(c.w) ∧ c.n = (cs[k]'hk).1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  intro c
  have hroR := rangeOffsets_raze_none ht cs (by omega) hd hN hro
  have hX := raze_len t cs.toArray hN
  obtain ⟨hw, hn, hsz, hid⟩ := codes_long_group_wf ht (raze t cs.toArray) hroR
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum = (Obj.codes (.atom t) #v[raze t cs.toArray])[0].n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hle := take_sum_le ((cs.map (·.1)).toList.map (·.toNat)) (k := k) (by simpa using hk)
  simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take, hs] at hle
  have hc : c = ((Obj.codes (.atom t) #v[raze t cs.toArray])[0].cut (cs.map (·.1)))[k]'hk := by
    show (Obj.codes (.atom t) cs)[k] = _; rw [codes_long_cut ht cs (by omega) hd hN hro]
  obtain ⟨hwk, hnk, hck, hik⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  have hzk := cut_size _ (cs.map (·.1)) hw hs hsz hk
  rw [hc, hwk, hnk, hck, hzk]
  refine ⟨hw, by simp, rfl, fun h8 => ⟨(hid h8).1, fun i hi => ?_⟩⟩
  rw [hik i hi]; exact (hid h8).2 _ (by omega)

/-! ## Dense long parts, whichever branch `rangeOffsets` takes -/

/-- **A long side of several dense parts: its codes are faithful jointly across the parts**, `rangeOffsets`
    answering (`codes_long_faithful`) or declining; the parts' summed count a `USize`. -/
theorem codes_long_dense_faithful {t : QAtomicType} (ht : orderKind t = some .i64) {p : Nat}
    (cs : Vector (Part (.atom t)) p) (hd : ∀ k (hk : k < p), ∃ b, (cs[k]'hk).2.enc = .bytes b)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (cs[k]'hk).1.toNat) (hj : j < (cs[l]'hl).1.toNat) :
    Column.idAt ((Obj.codes (.atom t) cs)[k]'hk).b ((Obj.codes (.atom t) cs)[k]'hk).w i =
        Column.idAt ((Obj.codes (.atom t) cs)[l]'hl).b ((Obj.codes (.atom t) cs)[l]'hl).w j ↔
      Vals.row (cs[k]'hk).2 ⟨i, hi⟩ = Vals.row (cs[l]'hl).2 ⟨j, hj⟩ := by
  cases hro : rangeOffsets t (cs.map (·.2.part)) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) with
  | none => exact codes_long_parts_faithful ht cs hd hN hro hk hl hi hj
  | some os => exact codes_long_faithful ht cs hro hk hl hi hj

/-- **A long side of several dense parts: each part's code is well formed**, whichever branch `rangeOffsets`
    takes; the parts' summed count a `USize`. -/
theorem codes_long_dense_wf {t : QAtomicType} (ht : orderKind t = some .i64) {p : Nat}
    (cs : Vector (Part (.atom t)) p) (hd : ∀ k (hk : k < p), ∃ b, (cs[k]'hk).2.enc = .bytes b)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size) {k : Nat} (hk : k < p) :
    let c := (Obj.codes (.atom t) cs)[k]'hk
    laneOK(c.w) ∧ c.n = (cs[k]'hk).1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  cases hro : rangeOffsets t (cs.map (·.2.part)) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) with
  | none => exact codes_long_parts_wf ht cs hd hN hro hk
  | some os => exact codes_long_wf ht cs hro hk

#print axioms rangeOffsets_raze_none
#print axioms codes_long_dense_faithful
#print axioms codes_long_dense_wf

end LeetQ.Rel.Alg
