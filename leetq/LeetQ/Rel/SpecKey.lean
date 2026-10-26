import LeetQ.Rel.SpecStruct

/-!
The `keyCodes` path for one dense long key column per side: `rangeOffsets` rebases both columns'
words onto one lane and `enumIds` codes them injectively (`rangeOffsets_long`), which discharges the
code hypotheses of `ej_rel_lane` (`keyCodes_long`) and leaves `ej`'s law unconditional on the codes
(`ej_long`). Bytes and frame-of-reference encodings are covered alike, through `longWords`.
-/

namespace LeetQ.Rel.Verb

open QLean QLean.Dep
open Freyd Freyd.Alg Freyd.Alg.RelSet

/-- `min/` folded from any seed lies below the seed and below every element it reads. -/
theorem foldl_lesser (l : List Int64) : ∀ acc : Int64,
    (l.foldl (Kernel.Coc.Over.step .lesser) acc).toInt ≤ acc.toInt ∧
    ∀ x ∈ l, (l.foldl (Kernel.Coc.Over.step .lesser) acc).toInt ≤ x.toInt := by
  induction l with
  | nil => intro acc; exact ⟨Int.le_refl _, by simp⟩
  | cons y l ih =>
    intro acc
    obtain ⟨h1, h2⟩ := ih (Kernel.Coc.Over.step .lesser acc y)
    have hs : (Kernel.Coc.Over.step .lesser acc y).toInt ≤ acc.toInt ∧
        (Kernel.Coc.Over.step .lesser acc y).toInt ≤ y.toInt := by
      simp only [Kernel.Coc.Over.step]; split <;> rename_i h <;> rw [Int64.lt_iff_toInt_lt] at h <;>
        exact ⟨by omega, by omega⟩
    refine ⟨Int.le_trans h1 hs.1, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Int.le_trans h1 hs.2
    · exact h2 x hx

/-- `max/` folded from any seed lies above the seed and above every element it reads. -/
theorem foldl_greater (l : List Int64) : ∀ acc : Int64,
    acc.toInt ≤ (l.foldl (Kernel.Coc.Over.step .greater) acc).toInt ∧
    ∀ x ∈ l, x.toInt ≤ (l.foldl (Kernel.Coc.Over.step .greater) acc).toInt := by
  induction l with
  | nil => intro acc; exact ⟨Int.le_refl _, by simp⟩
  | cons y l ih =>
    intro acc
    obtain ⟨h1, h2⟩ := ih (Kernel.Coc.Over.step .greater acc y)
    have hs : acc.toInt ≤ (Kernel.Coc.Over.step .greater acc y).toInt ∧
        y.toInt ≤ (Kernel.Coc.Over.step .greater acc y).toInt := by
      simp only [Kernel.Coc.Over.step]; split <;> rename_i h <;> rw [Int64.lt_iff_toInt_lt] at h <;>
        exact ⟨by omega, by omega⟩
    refine ⟨Int.le_trans hs.1 h1, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Int.le_trans hs.2 h1
    · exact h2 x hx

/-- `mapM` of a partial function over a pair answers both images. -/
theorem mapM_pair_some {α β : Type} {f : α → Option β} {a b : α} {rs : Array β}
    (h : Array.mapM f #[a, b] = some rs) : ∃ x y, f a = some x ∧ f b = some y ∧ rs = #[x, y] := by
  cases ha : f a <;> cases hb : f b <;> simp [Array.mapM_eq_mapM_toList, ha, hb] at h ⊢ <;> exact h.symm

/-- `mapM id` of a pair of results answers both values. -/
theorem mapM_pair_ok {ε β : Type} {ra rb : Except ε β} {os : Array β} (h : Array.mapM id #[ra, rb] = .ok os) :
    ∃ x y, ra = .ok x ∧ rb = .ok y ∧ os = #[x, y] := by
  cases ra <;> cases rb <;> simp [Array.mapM_eq_mapM_toList, bind, Except.bind, Functor.map, Except.map,
    pure, Except.pure] at h ⊢ <;> exact h.symm

/-- `mapM` of a partial function over a pair, each image read through a property every image has. -/
theorem mapM_pair_P {α β : Type} {f : α → Option β} {a b : α} {rs : Array β} (P : α → β → Prop)
    (hP : ∀ c r, f c = some r → P c r) (h : Array.mapM f #[a, b] = some rs) :
    ∃ x y, rs = #[x, y] ∧ P a x ∧ P b y := by
  obtain ⟨x, y, hx, hy, rfl⟩ := mapM_pair_some h
  exact ⟨x, y, rfl, hP a x hx, hP b y hy⟩

/-- Two payloads listing the same words agree at each word. -/
theorem bitsAt_of_elemsW {A B : ByteArray} (h : Verify.elemsW 8 A = Verify.elemsW 8 B) {i : Nat}
    (hi : i < B.size / 8) : Column.bitsAt A (i * 8) 8 = Column.bitsAt B (i * 8) 8 := by
  have hl := congrArg List.length h
  simp only [Verify.elemsW, List.length_map, List.length_range] at hl
  have := congrArg (·[i]?) h
  simp only [Verify.elemsW, List.getElem?_map, hl] at this
  simpa [List.getElem?_range hi] using this

/-- `Ew.val add` of a long payload and an atom, at word `i`: `intStep add` of the word and the atom. -/
theorem val_add_word (D : ByteArray) (x : UInt64) {n i : Nat} (hn : n < USize.size) (hi : i < n) :
    Column.bitsAt (Kernel.Ew.val Kernel.Ew.add Kernel.Ew.i64 Kernel.Ew.va Alg.nul D (Find.one x) n.toUSize) (i * 8) 8 =
      (Kernel.Ew.intStep Kernel.Ew.add Alg.nul (Column.bitsAt D (i * 8) 8).toInt64 x.toInt64).toUInt64 := by
  have e : Verify.elemsW 8 (Kernel.Ew.val Kernel.Ew.add Kernel.Ew.i64 Kernel.Ew.va Alg.nul D (Find.one x) n.toUSize) =
      (List.range n).map fun i =>
        (Kernel.Ew.intStep Kernel.Ew.add Alg.nul (Column.bitsAt D (i * 8) 8).toInt64 x.toInt64).toUInt64 :=
    Verify.val_i64_va Kernel.Ew.add Alg.nul D x n hn
  have hl := congrArg List.length e
  simp only [Verify.elemsW, List.length_map, List.length_range] at hl
  have := congrArg (·[i]?) e
  simp only [Verify.elemsW, List.getElem?_map, hl] at this
  simpa [List.getElem?_range hi] using this

/-- The words a rebase by `-base` feeds `enumIds`: a payload `E` that is `D` itself at `base = 0`, or lists the
    words of `Ew.val add` of `D` and `-base`, holds at word `i` `intStep add` of `D`'s word and `-base`. -/
theorem rebase_word {D E : ByteArray} {n : Nat} (base : Int64) (hn : n < USize.size)
    (hE : (E = D ∧ base = 0) ∨ Verify.elemsW 8 E = Verify.elemsW 8
      (Kernel.Ew.val Kernel.Ew.add Kernel.Ew.i64 Kernel.Ew.va Alg.nul D (Find.one (-base).toUInt64) n.toUSize))
    {i : Nat} (hi : i < n) :
    (Column.bitsAt E (i * 8) 8).toInt64 =
      Kernel.Ew.intStep Kernel.Ew.add Alg.nul (Column.bitsAt D (i * 8) 8).toInt64 (-base) := by
  rcases hE with ⟨rfl, rfl⟩ | hE
  · unfold Kernel.Ew.intStep
    by_cases h : (Column.bitsAt E (i * 8) 8).toInt64 = Alg.nul
    · simp [h, Alg.nul]
    · simp [h, Alg.nul]
      rintro (hh | hh)
      · exact absurd hh (by simpa [Alg.nul] using h)
      · exact absurd hh (by decide)
  · have hs := (Verify.val_spec Kernel.Ew.add Kernel.Ew.i64 Kernel.Ew.va Alg.nul D (Find.one (-base).toUInt64) n.toUSize).1
    rw [bitsAt_of_elemsW hE (by rw [hs, USize.toNat_ofNat_of_lt' hn, show Kernel.Ew.width Kernel.Ew.i64 = 8 from rfl,
      Nat.mul_div_cancel_left _ (by decide)]; exact hi),
      val_add_word D _ hn hi]
    simp

/-- The narrowest code layout is one of the four byte lanes and holds its codes. -/
theorem codeKind_spec (m : Nat) :
    (Alg.codeKind m = .u8 ∨ Alg.codeKind m = .i16 ∨ Alg.codeKind m = .i32 ∨ Alg.codeKind m = .i64) ∧
    ((Alg.codeKind m).width ≤ 4 → m ≤ 2 ^ 32) ∧ (m ≤ 2 ^ 32 → m ≤ 2 ^ (8 * (Alg.codeKind m).width)) ∧
    (m ≤ 2 ^ 32 → (Alg.codeKind m).width ≤ 4) := by
  unfold Alg.codeKind
  split <;> (try split) <;> (try split) <;> simp [Kernel.Scan.Kind.width] <;> omega

/-- `enumIds` at a whole-byte lane `8c` where it reports every row in range: `c` bytes a row, row `i` read
    back as its offset and `nullId` at `0Nj`, every other row's offset in `[0, d)`. -/
theorem enumIds_bytes (c n : Nat) (d nullId : USize) (E : ByteArray) (hc : 1 ≤ c) (hc8 : c ≤ 8)
    (hn : n < USize.size) (hok : (Kernel.enumIds n.toUSize d nullId (8 * c).toUSize E).2 = n.toUSize)
    (hd : d.toNat ≤ 2 ^ (8 * c)) (hnull : nullId.toNat < 2 ^ (8 * c)) :
    (Kernel.enumIds n.toUSize d nullId (8 * c).toUSize E).1.size = c * n ∧
    ∀ i < n, Column.bitsAt (Kernel.enumIds n.toUSize d nullId (8 * c).toUSize E).1 (i * c) c =
      (if (Column.bitsAt E (i * 8) 8).toInt64 = Int64.minValue then nullId.toNat
        else (Column.bitsAt E (i * 8) 8).toInt64.toInt.toNat).toUInt64 ∧
      ((Column.bitsAt E (i * 8) 8).toInt64 ≠ Int64.minValue →
        0 ≤ (Column.bitsAt E (i * 8) 8).toInt64.toInt ∧
          (Column.bitsAt E (i * 8) 8).toInt64.toInt.toNat < d.toNat) := by
  have hN : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' hn
  have hW : (8 * c).toUSize.toNat = 8 * c :=
    USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by omega : 8 * c < 2 ^ 32) USize.le_size)
  have hall := Verify.find?_toUSize (n := n.toUSize) (by unfold Kernel.enumIds at hok; exact hok)
  rw [hN] at hall
  have hb : ∀ i < n, (Column.bitsAt E (i * 8) 8).toInt64 ≠ Int64.minValue →
      0 ≤ (Column.bitsAt E (i * 8) 8).toInt64.toInt ∧
        (Column.bitsAt E (i * 8) 8).toInt64.toInt.toNat < d.toNat := by
    intro i hi hne
    have := hall i hi
    simp [hne, Int64.le_iff_toInt_le] at this
    exact this
  have he : (Kernel.enumIds n.toUSize d nullId (8 * c).toUSize E).1 = Column.packIds (8 * c) n (fun i =>
      if (Column.bitsAt E (i * 8) 8).toInt64 == Int64.minValue then nullId.toNat
      else (Column.bitsAt E (i * 8) 8).toInt64.toInt.toNat) := by
    unfold Kernel.enumIds; rw [hN, hW]
  have hp := Verify.packIds_bytes c n (fun i =>
      if (Column.bitsAt E (i * 8) 8).toInt64 == Int64.minValue then nullId.toNat
      else (Column.bitsAt E (i * 8) 8).toInt64.toInt.toNat) hc hc8
  rw [he]
  refine ⟨hp.1, fun i hi => ⟨?_, hb i hi⟩⟩
  by_cases h : (Column.bitsAt E (i * 8) 8).toInt64 = Int64.minValue
  · rw [hp.2 i hi (by simp only [h, beq_self_eq_true, ↓reduceIte]; exact hnull)]; simp [h]
  · rw [hp.2 i hi (by simp only [h, beq_iff_eq, ↓reduceIte]; exact Nat.lt_of_lt_of_le (hb i hi h).2 hd)]
    simp [h]

/-- `min/` lies below every non-null element it folds. -/
theorem overList_lesser_le {nul s x : Int64} {xs : List Int64} (hx : x ∈ xs) (hne : x ≠ nul) :
    (Verify.overList .lesser nul s xs).toInt ≤ x.toInt := by
  unfold Verify.overList
  exact (foldl_lesser _ s).2 x (List.mem_filter.2 ⟨hx, by simp [Kernel.Coc.Over.boolCast, hne]⟩)

/-- `max/` lies above every non-null element it folds. -/
theorem overList_greater_ge {nul s x : Int64} {xs : List Int64} (hx : x ∈ xs) (hne : x ≠ nul) :
    x.toInt ≤ (Verify.overList .greater nul s xs).toInt := by
  unfold Verify.overList
  exact (foldl_greater _ s).2 x (List.mem_filter.2 ⟨hx, by simp [Kernel.Coc.Over.boolCast, hne]⟩)

/-- A long column's fold as `rangeOffsets` reads its bound — `overBytes` of a dense payload, `overFoR` of an
    encoded one — is `overList` over a list holding every word of the column, as a long. -/
theorem bound_overList (op : Kernel.Coc.Over) (c : Column) {ws : List UInt64} {x : Int64}
    (hw : longWords c = some ws) (hn : ws.length < USize.size)
    (hf : (match c.enc with
      | .bytes b => some (Kernel.overBytes op Kernel.Ew.i64 Alg.nul b)
      | .foR .. => Kernel.overFoR op .long c
      | _ => none) = some x) :
    ∃ s L, x = Verify.overList op Alg.nul s L ∧ ∀ u ∈ ws, u.toInt64 ∈ L := by
  obtain ⟨t, n, e, a⟩ := c
  cases e
  case bytes b =>
    simp only [longWords, Option.some.injEq] at hw hf
    subst hw hf
    refine ⟨_, _, Verify.overBytes_eq op Kernel.Ew.i64 Alg.nul b, fun u hu => ?_⟩
    have hd : Verify.denseElems Kernel.Ew.i64 b = (Verify.elemsW 8 b).map UInt64.toInt64 := by
      simp only [Verify.denseElems, Verify.elemsW, List.map_map]; rfl
    rw [hd]; exact List.mem_map_of_mem hu
  case foR md pk =>
    simp only [longWords, Option.some.injEq] at hw
    subst hw
    simp only [List.length_map, List.length_range] at hn
    simp only [Kernel.overFoR] at hf
    refine ⟨_, _, ((Option.some.inj hf).symm.trans (Verify.over_eq op _ md pk n.toUSize)), fun u hu => ?_⟩
    rw [USize.toNat_ofNat_of_lt' hn]
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hu
    exact List.mem_map.2 ⟨i, hi, rfl⟩
  all_goals simp [longWords] at hw

/-- A non-null long at or above `base`, within `2⁶³` of it, rebases by `-base` without wrapping. -/
theorem rebase_val {v base : Int64} (hv : v ≠ Alg.nul) (hb : base ≠ Alg.nul) (hle : base.toInt ≤ v.toInt)
    (hlt : v.toInt - base.toInt < 2 ^ 63) :
    Kernel.Ew.intStep Kernel.Ew.add Alg.nul v (-base) = v + -base ∧ (v + -base).toInt = v.toInt - base.toInt := by
  have hnb : -base ≠ Alg.nul := fun e => hb (by
    have := congrArg (- ·) e; simp only [Int64.neg_neg] at this; rw [this]; decide)
  refine ⟨by simp [Kernel.Ew.intStep, hv, hnb], ?_⟩
  have hbm : base.toInt ≠ -2 ^ 63 := fun e => hb (Int64.toInt_inj.1 (by rw [e, Alg.nul, Int64.toInt_minValue]))
  have := Int64.le_toInt v; have := Int64.toInt_lt v; have := Int64.le_toInt base; have := Int64.toInt_lt base
  rw [Int64.toInt_add, Int64.toInt_neg]
  unfold Int.bmod
  dsimp only
  simp only [show ((2 ^ 64 : Nat) : Int) = 18446744073709551616 from rfl] at *
  split <;> split <;> omega

/-- **`rangeOffsets` codes two long key columns injectively at one byte lane**, whichever encoding (`bytes`,
    `foR`) each arrives in: a lane `k` and a code `f` on words, one-to-one over both columns' words, such that
    each part holds `f` of its words at `k`. Restricted to `total ≤ 2³²` rows, where no rebase wraps. -/
theorem rangeOffsets_long {cl cr : Column} {total : Nat} {os : Array Alg.Code} {wl wr : List UInt64}
    (hwl : longWords cl = some wl) (hwr : longWords cr = some wr) (hl : wl.length < USize.size)
    (hr : wr.length < USize.size) (htot : total ≤ 2 ^ 32)
    (h : Alg.rangeOffsets .long #[cl, cr] total = .ok (some os)) :
    ∃ (k : Kernel.Scan.Kind) (f : UInt64 → UInt64), (k = .u8 ∨ k = .i16 ∨ k = .i32 ∨ k = .i64) ∧
      (∀ u ∈ wl ++ wr, ∀ u' ∈ wl ++ wr, (f u = f u' ↔ u = u')) ∧
      ∃ lc rc : Alg.Code, os = #[lc, rc] ∧
      lc.kind = some k ∧ lc.n = wl.length ∧ lc.b.size = k.width * wl.length ∧
        (∀ i (hi : i < wl.length), k.bitsAt lc.b i = f wl[i]) ∧
      rc.kind = some k ∧ rc.n = wr.length ∧ rc.b.size = k.width * wr.length ∧
        (∀ j (hj : j < wr.length), k.bitsAt rc.b j = f wr[j]) := by
  unfold Alg.rangeOffsets at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  rw [if_pos (by decide)] at h
  split at h
  rotate_left
  · cases h
  rename_i los hlos
  split at h
  rotate_left
  · cases h
  rename_i his hhis
  obtain ⟨l1, l2, rfl, hl1, hl2⟩ := mapM_pair_P (fun c x => ∀ ws, longWords c = some ws → ws.length < USize.size →
      ∃ s L, x = Verify.overList .lesser Alg.nul s L ∧ ∀ u ∈ ws, u.toInt64 ∈ L)
    (fun c x hf ws hw hn => bound_overList .lesser c hw hn hf) hlos
  obtain ⟨g1, g2, rfl, hg1, hg2⟩ := mapM_pair_P (fun c x => ∀ ws, longWords c = some ws → ws.length < USize.size →
      ∃ s L, x = Verify.overList .greater Alg.nul s L ∧ ∀ u ∈ ws, u.toInt64 ∈ L)
    (fun c x hf ws hw hn => bound_overList .greater c hw hn hf) hhis
  generalize hlo : Array.foldl min Int64.maxValue #[l1, l2] = lo at h
  generalize hhi : Array.foldl max (Int64.minValue + 1) #[g1, g2] = hi at h
  split at h
  · cases h
  rename_i hlh
  split at h
  rotate_left
  · cases h
  rename_i hwid
  generalize hk : Alg.codeKind ((hi.toInt - lo.toInt + 2).toNat) = k at h hwid
  generalize hbase : (if (decide (0 ≤ lo) && (Alg.codeKind ((hi.toInt - Int64.toInt 0 + 2).toNat)).width == k.width) = true
    then (0 : Int64) else lo) = base at h
  generalize hcard : (hi.toInt - base.toInt + 2).toNat = card at h
  split at h
  rotate_left
  · cases h
  rename_i rs hrs
  have hm : Array.mapM id rs = .ok os := by
    cases hm : Array.mapM id rs <;> rw [hm] at h <;> simp [Functor.map, Except.map] at h ⊢ <;> exact h
  -- the lane, the joint range `[lo, hi]` of the non-null words, and the rebase `base ≤ lo`
  have hk4 : k = .u8 ∨ k = .i16 ∨ k = .i32 ∨ k = .i64 := hk ▸ (codeKind_spec _).1
  have hk1 : 1 ≤ k.width ∧ k.width ≤ 8 := by rcases hk4 with rfl | rfl | rfl | rfl <;> decide
  have hw4 : k.width ≤ 4 := Nat.le_trans hwid ((codeKind_spec total).2.2.2 htot)
  have hs32 : (hi.toInt - lo.toInt + 2).toNat ≤ 2 ^ 32 := (codeKind_spec _).2.1 (by rw [hk]; exact hw4)
  have hlo0 : lo ≠ Alg.nul := fun e => hlh (by simp [e])
  have hlohi : lo.toInt ≤ hi.toInt := by
    have : ¬ hi < lo := fun e => hlh (by simp [e])
    rw [Int64.lt_iff_toInt_lt] at this; omega
  have hbase' : (base = 0 ∧ 0 ≤ lo.toInt ∧ (Alg.codeKind ((hi.toInt - Int64.toInt 0 + 2).toNat)).width = k.width) ∨
      base = lo := by
    split at hbase
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      exact .inl ⟨hbase.symm, by simpa using Int64.le_iff_toInt_le.1 hc.1, hc.2⟩
    · exact .inr hbase.symm
  have hbn : base ≠ Alg.nul := by rcases hbase' with ⟨rfl, -, -⟩ | rfl <;> first | decide | exact hlo0
  have hblo : base.toInt ≤ lo.toInt := by rcases hbase' with ⟨rfl, h0, -⟩ | rfl <;> simp_all
  have hc32 : card ≤ 2 ^ 32 := by
    rcases hbase' with ⟨rfl, -, e⟩ | rfl
    · rw [← hcard]; exact (codeKind_spec _).2.1 (by rw [e]; exact hw4)
    · rw [← hcard]; exact hs32
  have hcw : card ≤ 2 ^ (8 * k.width) := by
    rcases hbase' with ⟨rfl, -, e⟩ | rfl
    · have e' : (Alg.codeKind card).width = k.width := by rw [← hcard]; exact e
      rw [← e']; exact (codeKind_spec card).2.2.1 hc32
    · rw [← hk, hcard]; exact (codeKind_spec card).2.2.1 hc32
  have hc2 : (card : Int) = hi.toInt - base.toInt + 2 := by rw [← hcard]; omega
  have hd : card.toUSize.toNat ≤ 2 ^ (8 * k.width) := by
    rcases Nat.lt_or_ge card USize.size with hlt | hge
    · rw [USize.toNat_ofNat_of_lt' hlt]; exact hcw
    · exact Nat.le_trans (Nat.le_of_lt (USize.toNat_lt_size _)) (Nat.le_trans hge hcw)
  have hnull' : (card - 1).toUSize.toNat = card - 1 :=
    USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by omega) USize.le_size)
  have hnull : (card - 1).toUSize.toNat < 2 ^ (8 * k.width) := by rw [hnull']; omega
  -- each part holds, at the lane, the `enumIds` code of its rebased words
  obtain ⟨r1, r2, rfl, hp1, hp2⟩ := mapM_pair_P (fun c r => ∀ code, r = .ok code → ∀ ws, longWords c = some ws →
      ws.length < USize.size → code.w = 8 * k.width ∧ code.n = ws.length ∧ code.b.size = k.width * ws.length ∧
      ∀ i (hi : i < ws.length), Column.bitsAt code.b (i * k.width) k.width =
        (if Kernel.Ew.intStep Kernel.Ew.add Alg.nul ws[i].toInt64 (-base) = Int64.minValue then (card - 1).toUSize.toNat
          else (Kernel.Ew.intStep Kernel.Ew.add Alg.nul ws[i].toInt64 (-base)).toInt.toNat).toUInt64 ∧
        (Kernel.Ew.intStep Kernel.Ew.add Alg.nul ws[i].toInt64 (-base) ≠ Int64.minValue →
          0 ≤ (Kernel.Ew.intStep Kernel.Ew.add Alg.nul ws[i].toInt64 (-base)).toInt ∧
          (Kernel.Ew.intStep Kernel.Ew.add Alg.nul ws[i].toInt64 (-base)).toInt.toNat < card.toUSize.toNat))
    (fun c r hf code hcode ws hw hn => by
      obtain ⟨t, n, e, a⟩ := c
      cases e
      case bytes b =>
        simp only [longWords, Option.some.injEq] at hw; subst hw
        simp only [Option.some.injEq] at hf; subst hf
        have hn' : b.size / 8 < USize.size := by simpa [Verify.elemsW] using hn
        generalize hE : (if (base == 0) = true then b else Kernel.Ew.val Kernel.Ew.add Kernel.Ew.i64 Kernel.Ew.va Alg.nul b
          (Find.one (-base).toUInt64) (b.size / 8).toUSize) = E at hcode
        split at hcode
        · cases hcode
        rename_i hbad
        cases hcode
        have hok : (Kernel.enumIds (b.size / 8).toUSize card.toUSize (card - 1).toUSize (8 * k.width).toUSize E).2 =
            (b.size / 8).toUSize := by
          apply USize.toNat_inj.1; rw [USize.toNat_ofNat_of_lt' hn']; simpa using hbad
        obtain ⟨hsz, hbits⟩ := enumIds_bytes k.width (b.size / 8) card.toUSize (card - 1).toUSize E hk1.1 hk1.2 hn' hok
          hd hnull
        have hEw : ∀ i < b.size / 8, (Column.bitsAt E (i * 8) 8).toInt64 =
            Kernel.Ew.intStep Kernel.Ew.add Alg.nul (Column.bitsAt b (i * 8) 8).toInt64 (-base) :=
          fun i hi => rebase_word (D := b) (E := E) base hn' (by
            rw [← hE]; split
            · exact .inl ⟨rfl, beq_iff_eq.1 ‹_›⟩
            · exact .inr rfl) hi
        refine ⟨rfl, by simp [Verify.elemsW], by rw [hsz]; simp [Verify.elemsW], fun i hi => ?_⟩
        have hi' : i < b.size / 8 := by simpa [Verify.elemsW] using hi
        have hwi : (Verify.elemsW 8 b)[i] = Column.bitsAt b (i * 8) 8 := by simp [Verify.elemsW]
        rw [hwi, ← hEw i hi']
        exact hbits i hi'
      case foR md pk =>
        simp only [longWords, Option.some.injEq] at hw; subst hw
        have hn' : n < USize.size := by simpa using hn
        obtain ⟨⟨m', p'⟩, hsh, hf⟩ := Option.map_eq_some_iff.1 hf
        subst hf
        simp only [Kernel.enumIdsFoR] at hcode
        split at hcode
        · cases hcode
        rename_i hbad
        cases hcode
        have hok : (Kernel.enumIds n.toUSize card.toUSize (card - 1).toUSize (8 * k.width).toUSize
            (Kernel.Coc.decode 8 m' p' n.toUSize)).2 = n.toUSize := by
          apply USize.toNat_inj.1; rw [USize.toNat_ofNat_of_lt' hn']; simpa using hbad
        obtain ⟨hsz, hbits⟩ := enumIds_bytes k.width n card.toUSize (card - 1).toUSize _ hk1.1 hk1.2 hn' hok hd hnull
        have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
        have hD : ∀ i < n, Column.bitsAt (Kernel.Coc.decode 8 md pk n.toUSize) (i * 8) 8 =
            Column.foRBits md pk (Column.blockStarts md) i := fun i hi => by
          have := (Verify.decodeW (8 : Nat).toUSize (by rw [h8]; decide) md pk n.toUSize).2 i
            (by rw [USize.toNat_ofNat_of_lt' hn']; exact hi)
          rw [h8, Verify.ofNat_toNat_mod64] at this
          exact this
        have hEw : ∀ i < n, (Column.bitsAt (Kernel.Coc.decode 8 m' p' n.toUSize) (i * 8) 8).toInt64 =
            Kernel.Ew.intStep Kernel.Ew.add Alg.nul
              (Column.bitsAt (Kernel.Coc.decode 8 md pk n.toUSize) (i * 8) 8).toInt64 (-base) :=
          fun i hi => rebase_word (D := Kernel.Coc.decode 8 md pk n.toUSize) (E := Kernel.Coc.decode 8 m' p' n.toUSize)
            base hn' (by
              split at hsh
              · rename_i h0; cases hsh; exact .inl ⟨rfl, beq_iff_eq.1 h0⟩
              · have := Verify.foRShift_spec false (-base) md pk n.toUSize m' p' hsh
                simp only [Bool.false_eq_true, ↓reduceIte] at this
                exact .inr this) hi
        refine ⟨rfl, by simp, by rw [hsz]; simp, fun i hi => ?_⟩
        have hi' : i < n := by simpa using hi
        have hwi : ((List.range n).map (Column.foRBits md pk (Column.blockStarts md)))[i] =
            Column.bitsAt (Kernel.Coc.decode 8 md pk n.toUSize) (i * 8) 8 := by simp [hD i hi']
        rw [hwi, ← hEw i hi']
        exact hbits i hi'
      all_goals simp [longWords] at hw) hrs
  obtain ⟨c1, c2, rfl, rfl, rfl⟩ := mapM_pair_ok hm
  obtain ⟨w1, n1, s1, b1⟩ := hp1 c1 rfl wl hwl hl
  obtain ⟨w2, n2, s2, b2⟩ := hp2 c2 rfl wr hwr hr
  -- the code of a word: `card - 1` at the null, its offset from `base` elsewhere, at most `card - 2`
  have hW : ∀ u ∈ wl ++ wr, u.toInt64 ≠ Alg.nul → lo.toInt ≤ u.toInt64.toInt ∧ u.toInt64.toInt ≤ hi.toInt := by
    have m1 : ∀ a b : Int64, (min a b).toInt ≤ a.toInt ∧ (min a b).toInt ≤ b.toInt := fun a b => by
      show (if a ≤ b then a else b).toInt ≤ a.toInt ∧ (if a ≤ b then a else b).toInt ≤ b.toInt
      split <;> rename_i hab <;> rw [Int64.le_iff_toInt_le] at hab <;> exact ⟨by omega, by omega⟩
    have m2 : ∀ a b : Int64, a.toInt ≤ (max a b).toInt ∧ b.toInt ≤ (max a b).toInt := fun a b => by
      show a.toInt ≤ (if a ≤ b then b else a).toInt ∧ b.toInt ≤ (if a ≤ b then b else a).toInt
      split <;> rename_i hab <;> rw [Int64.le_iff_toInt_le] at hab <;> exact ⟨by omega, by omega⟩
    have elo : lo = min (min Int64.maxValue l1) l2 := by rw [← hlo]; rfl
    have ehi : hi = max (max (Int64.minValue + 1) g1) g2 := by rw [← hhi]; rfl
    obtain ⟨a1, a1'⟩ := m1 (min Int64.maxValue l1) l2
    obtain ⟨-, a2⟩ := m1 Int64.maxValue l1
    obtain ⟨b1', b1''⟩ := m2 (max (Int64.minValue + 1) g1) g2
    obtain ⟨-, b2'⟩ := m2 (Int64.minValue + 1) g1
    rw [← elo] at a1 a1'; rw [← ehi] at b1' b1''
    intro u hu hne
    rcases List.mem_append.1 hu with hu | hu
    · obtain ⟨s, L, e1, hL⟩ := hl1 wl hwl hl
      obtain ⟨s', L', e2, hL'⟩ := hg1 wl hwl hl
      have c1 := overList_lesser_le (s := s) (hL u hu) hne
      have c2 := overList_greater_ge (s := s') (hL' u hu) hne
      rw [← e1] at c1; rw [← e2] at c2
      exact ⟨by omega, by omega⟩
    · obtain ⟨s, L, e1, hL⟩ := hl2 wr hwr hr
      obtain ⟨s', L', e2, hL'⟩ := hg2 wr hwr hr
      have c1 := overList_lesser_le (s := s) (hL u hu) hne
      have c2 := overList_greater_ge (s := s') (hL' u hu) hne
      rw [← e1] at c1; rw [← e2] at c2
      exact ⟨by omega, by omega⟩
  have key : ∀ u ∈ wl ++ wr,
      (u.toInt64 = Alg.nul ∧ Kernel.Ew.intStep Kernel.Ew.add Alg.nul u.toInt64 (-base) = Int64.minValue) ∨
      (u.toInt64 ≠ Alg.nul ∧ Kernel.Ew.intStep Kernel.Ew.add Alg.nul u.toInt64 (-base) ≠ Int64.minValue ∧
        ((Kernel.Ew.intStep Kernel.Ew.add Alg.nul u.toInt64 (-base)).toInt.toNat : Int) =
          u.toInt64.toInt - base.toInt ∧
        (Kernel.Ew.intStep Kernel.Ew.add Alg.nul u.toInt64 (-base)).toInt.toNat + 2 ≤ card) := by
    intro u hu
    by_cases hv : u.toInt64 = Alg.nul
    · exact .inl ⟨hv, by simp [Kernel.Ew.intStep, hv, Alg.nul]⟩
    · obtain ⟨hlo', hhi'⟩ := hW u hu hv
      obtain ⟨e1, e2⟩ := rebase_val hv hbn (by omega) (by omega)
      rw [e1]
      refine .inr ⟨hv, fun e => ?_, by rw [e2]; omega, by rw [e2]; omega⟩
      have := congrArg Int64.toInt e
      rw [e2, Int64.toInt_minValue] at this
      omega
  have hkb : ∀ b i, k.bitsAt b i = Column.bitsAt b (i * k.width) k.width := fun b i => by
    rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hkind : ∀ c : Alg.Code, c.w = 8 * k.width → c.kind = some k := fun c hw => by
    simp only [Alg.Code.kind, hw]; rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  let F : UInt64 → Nat := fun u => if Kernel.Ew.intStep Kernel.Ew.add Alg.nul u.toInt64 (-base) = Int64.minValue
      then (card - 1).toUSize.toNat else (Kernel.Ew.intStep Kernel.Ew.add Alg.nul u.toInt64 (-base)).toInt.toNat
  have hinj : ∀ u ∈ wl ++ wr, ∀ u' ∈ wl ++ wr, (F u = F u' ↔ u = u') := by
    intro u hu u' hu'
    have toI : ∀ x y : UInt64, x.toInt64 = y.toInt64 → x = y := fun x y e => by
      have := congrArg Int64.toUInt64 e; simpa using this
    rcases key u hu with ⟨hv, hR⟩ | ⟨hv, hR, hR1, hR2⟩ <;>
      rcases key u' hu' with ⟨hv', hR'⟩ | ⟨hv', hR', hR1', hR2'⟩
    · dsimp only [F]; rw [if_pos hR, if_pos hR']
      exact ⟨fun _ => toI _ _ (hv.trans hv'.symm), fun _ => rfl⟩
    · dsimp only [F]; rw [if_pos hR, if_neg hR', hnull']
      exact ⟨fun e => by omega, fun e => absurd (e ▸ hv) hv'⟩
    · dsimp only [F]; rw [if_neg hR, if_pos hR', hnull']
      exact ⟨fun e => by omega, fun e => absurd hv' (e ▸ hv)⟩
    · dsimp only [F]; rw [if_neg hR, if_neg hR']
      exact ⟨fun e => toI _ _ (Int64.toInt_inj.1 (by omega)), fun e => by rw [e]⟩
  -- a lane value is an id below `USize.size` or a non-negative `Int64`, so `toUInt64` keeps it
  have fb : ∀ u, F u < 2 ^ 64 := fun u => by
    dsimp only [F]; split
    · exact Nat.lt_of_lt_of_le (USize.toNat_lt_size _)
        (by first | exact USize.size_le | (rcases USize.size_eq with h | h <;> omega))
    · have := Int64.toInt_lt (Kernel.Ew.intStep Kernel.Ew.add Alg.nul u.toInt64 (-base)); omega
  refine ⟨k, fun u => (F u).toUInt64, hk4, fun u hu u' hu' => ?_, c1, c2, rfl,
    hkind c1 w1, n1, s1, fun i hi => by rw [hkb]; exact (b1 i hi).1,
    hkind c2 w2, n2, s2, fun j hj => by rw [hkb]; exact (b2 j hj).1⟩
  show (F u).toUInt64 = (F u').toUInt64 ↔ u = u'
  rw [← hinj u hu u' hu']
  refine ⟨fun e => ?_, fun e => by rw [e]⟩
  have := congrArg UInt64.toNat e
  simpa [Nat.mod_eq_of_lt (fb u), Nat.mod_eq_of_lt (fb u')] using this

/-- The `keyCodes` of one dense long key column per side, when `rangeOffsets` codes them: both sides
at one lane `k`, the left one's size its row count, and equal lane words exactly at equal keys. -/
theorem keyCodes_long {verb : String} {cl cr : Column} {lc rc : Alg.Code} {wl wr : List UInt64}
    (hwl : longWords cl = some wl) (hwr : longWords cr = some wr) (hl : wl.length < USize.size)
    (hr : wr.length < USize.size) (htot : cl.n + cr.n ≤ 2 ^ 32)
    (hR : Alg.rangeOffsets .long #[cl, cr] (cl.n + cr.n) ≠ .ok none)
    (hc : Struct.keyCodes verb #[⟨.long, cl⟩] #[⟨.long, cr⟩] = .ok (lc, rc)) :
    ∃ k : Kernel.Scan.Kind, (k = .u8 ∨ k = .i16 ∨ k = .i32 ∨ k = .i64) ∧ lc.kind = some k ∧ rc.kind = some k ∧
      rc.n ≤ k.avail rc.b ∧ rc.n = wr.length ∧ lc.b.size / k.width = wl.length ∧
      ∀ i (hi : i < wl.length) j (hj : j < wr.length), (k.bitsAt rc.b j = k.bitsAt lc.b i ↔ wr[j] = wl[i]) := by
  obtain ⟨os, hro, h2⟩ : ∃ os, Alg.rangeOffsets .long #[cl, cr] (cl.n + cr.n) = .ok (some os) ∧
      Alg.two os = .ok (lc, rc) := by
    unfold Struct.keyCodes Alg.codes at hc
    rcases hro : Alg.rangeOffsets .long #[cl, cr] (cl.n + cr.n) with err | _ | os
    all_goals
      obtain ⟨t1, n1, e1, a1⟩ := cl
      obtain ⟨t2, n2, e2, a2⟩ := cr
      dsimp only at hro
      cases e1 <;> simp [longWords] at hwl <;> cases e2 <;> simp [longWords] at hwr <;>
        simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, Array.mapM_eq_mapM_toList,
          Alg.tuples, hro] at hc hR ⊢
    all_goals exact hc
  obtain ⟨k, f, hk4, hf, lc', rc', rfl, hlk, -, hls, hlb, hrk, hrn, hrs, hrb⟩ :=
    rangeOffsets_long hwl hwr hl hr htot hro
  have e2 : (lc', rc') = (lc, rc) := by simpa [Alg.two, pure, Except.pure] using h2
  cases e2
  have hw0 : 0 < k.width := by rcases hk4 with rfl | rfl | rfl | rfl <;> decide
  refine ⟨k, hk4, hlk, hrk, ?_, hrn, by rw [hls, Nat.mul_div_cancel_left _ hw0], fun i hi j hj => ?_⟩
  · rcases hk4 with rfl | rfl | rfl | rfl <;>
      simp only [Kernel.Scan.Kind.avail, hrs, hrn, Nat.mul_div_cancel_left _ hw0, Nat.le_refl]
  · rw [hrb j hj, hlb i hi]
    exact hf _ (List.mem_append_right _ (List.getElem_mem hj)) _ (List.mem_append_left _ (List.getElem_mem hi))

/-- `ej` on one dense long key column per side, unconditionally on the codes: its relation is the
key join `(ix tl)(ix tr)°` read at the row ids, wherever `rangeOffsets` codes the two columns. -/
theorem ej_long {cl cr : Column} {wl wr : List UInt64} {R : Rel .long .long}
    (hwl : longWords cl = some wl) (hwr : longWords cr = some wr) (htot : cl.n + cr.n ≤ 2 ^ 32)
    (hro : Alg.rangeOffsets .long #[cl, cr] (cl.n + cr.n) ≠ .ok none)
    (hU : wl.length * wr.length + wl.length + wr.length + wr.length + 1 < USize.size)
    (hB : wl.length * wr.length + wl.length + wr.length + wr.length < 2 ^ 63)
    (h : Struct.ej #[⟨.long, cl⟩] #[⟨.long, cr⟩] = .ok R) :
    (R.Holds : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) =
      (graph Int64.ofNat : Idx ⟶ (⟨Int64⟩ : RelSet.{0}))° ≫ ix (wl.map (fun u => [u.toInt64])) ≫
        (ix (wr.map (fun u => [u.toInt64])))° ≫ graph Int64.ofNat := by
  rcases hc : Struct.keyCodes "ej" #[⟨.long, cl⟩] #[⟨.long, cr⟩] with err | ⟨lc, rc⟩
  · simp [Struct.ej, hc, bind, Except.bind] at h
  obtain ⟨k, hk4, hlk, hrk, hav, hrn, hnl, hkey⟩ :=
    keyCodes_long hwl hwr (by omega) (by omega) htot hro hc
  refine ej_rel_lane hk4 hc hrk hlk hav (by simp [hrn]) (by simp [hnl]) (fun i hi j hj => ?_)
    (by simp only [List.length_map, hrn]; exact hU) (by simp only [List.length_map, hrn]; exact hB) h
  simp only [List.length_map] at hi hj
  rw [hkey i hi j hj, getElem!_pos _ _ (by simpa using hj), getElem!_pos _ _ (by simpa using hi)]
  simp only [List.getElem_map, List.cons.injEq, and_true]
  refine ⟨fun e => by rw [e], fun e => ?_⟩
  have := congrArg Int64.toUInt64 e; simpa using this

/-! ## `aj` and `wj`'s time edge: `binRows` is `binSpec` in each needle's group

  `Eval.groupEdge`, which both `aj` and `wjP` read their edges from, is one `Kernel.binRows` (over the time
  column where it lies, or decoded first by `foRBinRows`). Its halving `binStep` is `binSpec`'s
  `partitionAt` walk shifted to the group's start, element for element — not merely on a sorted group —
  so the law holds on any group, and `binSpec_sorted` reads it as "the last row at or before" where
  the times ascend. -/

/-- `binStep`'s test at position `m`: the element `order` names there (`m` itself where `order` is empty),
    its `ordKey` below `k` (`binr`) or at most `k` (`bin`). -/
def binTest (w : Nat) (float signed right : Bool) (hay order : ByteArray) (k : UInt64) (m : Nat) : Bool :=
  let v := Kernel.ordKey w float signed (Column.bitsAt hay ((if order.isEmpty then m else
    (Column.bitsAt order (m * 8) 8).toNat) * w) w)
  decide (if right then v < k else v ≤ k)

/-- `partitionAt`'s loop never answers past `hi`. -/
theorem partitionAt_go_le (below : Nat → Id Bool) : ∀ fuel lo hi, lo ≤ hi →
    Id.run (Eval.partitionAt.go below fuel lo hi) ≤ hi
  | 0, _, _, h => h
  | fuel + 1, lo, hi, h => by
    rw [Eval.partitionAt.go]
    by_cases hle : hi ≤ lo
    · rw [if_pos hle]; exact h
    · rw [if_neg hle]
      show Id.run (if Id.run (below (lo + (hi - lo) / 2)) = true then
          Eval.partitionAt.go below fuel (lo + (hi - lo) / 2 + 1) hi
        else Eval.partitionAt.go below fuel lo (lo + (hi - lo) / 2)) ≤ hi
      split
      · exact partitionAt_go_le below fuel _ hi (by omega)
      · exact Nat.le_trans (partitionAt_go_le below fuel lo _ (by omega)) (by omega)

/-- **`binStep` over `[lo+a, lo+b)` is `partitionAt`'s loop over `[a, b)` shifted by `lo`**, for any
    `below` that reads `binTest` at `lo + j`: the same walk, step for step. -/
theorem binStep_go (w : Nat) (float signed right : Bool) (hay order : ByteArray) (k : UInt64) (lo : Nat)
    (below : Nat → Id Bool) : ∀ fuel a b,
    (∀ j, a ≤ j → j < b → Id.run (below j) = binTest w float signed right hay order k (lo + j)) →
    Kernel.binStep w float signed right hay order k fuel (lo + a) (lo + b) =
      lo + Id.run (Eval.partitionAt.go below fuel a b)
  | 0, _, _, _ => rfl
  | fuel + 1, a, b, hb => by
    rw [Eval.partitionAt.go, Kernel.binStep]
    by_cases hle : b ≤ a
    · rw [if_pos (show lo + b ≤ lo + a by omega), if_pos hle]; rfl
    · rw [if_neg (show ¬ lo + b ≤ lo + a by omega), if_neg hle]
      show _ = lo + Id.run (if Id.run (below (a + (b - a) / 2)) = true then
          Eval.partitionAt.go below fuel (a + (b - a) / 2 + 1) b
        else Eval.partitionAt.go below fuel a (a + (b - a) / 2))
      have hm : lo + a + (lo + b - (lo + a)) / 2 = lo + (a + (b - a) / 2) := by omega
      have hv := hb (a + (b - a) / 2) (Nat.le_add_right ..) (by omega)
      simp only [hm]
      cases e : binTest w float signed right hay order k (lo + (a + (b - a) / 2))
      · rw [e] at hv; unfold binTest at e
        simp only [decide_eq_false_iff_not] at e
        simp only [e, hv, ↓reduceIte, Bool.false_eq_true]
        exact binStep_go w float signed right hay order k lo below fuel a (a + (b - a) / 2) fun j h1 h2 => hb j h1 (by omega)
      · rw [e] at hv; unfold binTest at e
        simp only [decide_eq_true_eq] at e
        simp only [e, hv, ↓reduceIte]
        rw [show lo + (a + (b - a) / 2) + 1 = lo + (a + (b - a) / 2 + 1) by omega]
        exact binStep_go w float signed right hay order k lo below fuel _ b fun j h1 h2 => hb j (by omega) h2

/-- **`binRows` answers `binSpec` in each needle's group**: needle `j` names group `g`, which spans
    `[lo, hi)` of `bounds`; where `G` lists that span's rows (`order` read there, the position itself
    where it is empty) and the test at each is `rt[G[i]] ≤ x`, word `j` is `binSpec rt G x`'s row,
    `miss` where the bisection lands at the group's start. Nothing is assumed about the times' order. -/
theorem bitsAt_binRows (w : USize) (float signed right : Bool) (hay keys order bounds gids : ByteArray)
    (miss : UInt64) {j g lo hi : Nat} (hj : j < keys.size / w.toNat) (hgi : (j + 1) * 8 ≤ gids.size)
    (hg : (Column.bitsAt gids (j * 8) 8).toNat = g) (hng : g < bounds.size / 8 - 1)
    (hlo : (Column.bitsAt bounds (g * 8) 8).toNat = lo) (hhi : (Column.bitsAt bounds (g * 8 + 8) 8).toNat = hi)
    (rt : List Int64) (G : List Nat) (x : Int64) (hlen : G.length = hi - lo)
    (hrow : ∀ i, i < G.length →
      G[i]! = if order.isEmpty then lo + i else (Column.bitsAt order ((lo + i) * 8) 8).toNat)
    (htest : ∀ i, i < G.length → binTest w.toNat float signed right hay order
      (Kernel.ordKey w.toNat float signed (Column.bitsAt keys (j * w.toNat) w.toNat)) (lo + i) =
        decide (rt[G[i]!]! ≤ x)) :
    Column.bitsAt (Kernel.binRows w float signed right hay keys order bounds gids miss) (8 * j) 8 =
      ((Struct.binSpec rt G x).map Nat.toUInt64).getD miss := by
  simp only [Kernel.binRows]
  rw [show 8 * j = ByteArray.empty.size + 8 * j by simp,
    (Verify.foldl_pushBits _ 8 (by decide) _ _).2.2 j (by simpa using hj),
    show 8 * 8 = 64 from rfl, Verify.ofNat_toNat_mod64, List.getElem_range, hg, hlo, hhi]
  obtain ⟨P, hP, hPe, hPle⟩ : ∃ P, Kernel.binStep w.toNat float signed right hay order
      (Kernel.ordKey w.toNat float signed (Column.bitsAt keys (j * w.toNat) w.toNat)) (hi - lo + 1) lo hi =
        lo + P ∧ Id.run (Eval.partitionAt (fun i => pure (decide (rt[G[i]!]! ≤ x))) G.length) = P ∧
        P ≤ G.length := by
    by_cases hle : hi ≤ lo
    · refine ⟨0, ?_, ?_, Nat.zero_le _⟩
      · rw [show hi - lo + 1 = 0 + 1 by omega, Kernel.binStep, if_pos hle]; rfl
      · rw [show G.length = 0 by omega]; rfl
    · refine ⟨_, ?_, rfl, partitionAt_go_le _ _ _ _ (Nat.zero_le _)⟩
      have := binStep_go w.toNat float signed right hay order _ lo (fun i => pure (decide (rt[G[i]!]! ≤ x)))
        (hi - lo + 1) 0 (hi - lo) fun i _ hi' => (htest i (by omega)).symm
      rw [Nat.add_sub_cancel' (by omega)] at this
      simp only [Nat.add_zero] at this
      rw [this, hlen]; rfl
  rw [hP]
  unfold Struct.binSpec
  rw [hPe]
  rcases P with _ | p
  · simp
  · have hr := hrow p (by omega)
    simp only [show ¬ gids.size < (j + 1) * 8 by omega, show ¬ bounds.size / 8 - 1 ≤ g by omega,
      Nat.add_sub_cancel, hr]
    by_cases ho : order.isEmpty = true <;> simp [ho]

/-- `binRows` at a needle whose id names no group answers the miss. -/
theorem bitsAt_binRows_miss (w : USize) (float signed right : Bool) (hay keys order bounds gids : ByteArray)
    (miss : UInt64) {j g : Nat} (hj : j < keys.size / w.toNat) (hg : (Column.bitsAt gids (j * 8) 8).toNat = g)
    (hng : bounds.size / 8 - 1 ≤ g) :
    Column.bitsAt (Kernel.binRows w float signed right hay keys order bounds gids miss) (8 * j) 8 = miss := by
  simp only [Kernel.binRows]
  rw [show 8 * j = ByteArray.empty.size + 8 * j by simp,
    (Verify.foldl_pushBits _ 8 (by decide) _ _).2.2 j (by simpa using hj),
    show 8 * 8 = 64 from rfl, Verify.ofNat_toNat_mod64, List.getElem_range, hg]
  simp [hng]

/-- A word read as `Int64` is its two's-complement value, `sx` at width 8. -/
theorem sx8_toInt64 (v : UInt64) : Verify.sx 8 v = v.toInt64.toInt := by
  have hv := v.toNat_lt
  rw [show v.toInt64.toInt = v.toBitVec.toInt from rfl, BitVec.toInt_eq_toNat_cond]
  simp only [Verify.sx, Nat.reducePow, Nat.reduceMul, Nat.reduceSub, UInt64.toNat_toBitVec] at hv ⊢
  rw [Nat.mod_eq_of_lt hv]
  split <;> split <;> omega

/-- At width 8, signed, `ordKey` carries `Int64` order onto unsigned order. -/
theorem ordKey8_le (a b : UInt64) :
    Kernel.ordKey 8 false true a ≤ Kernel.ordKey 8 false true b ↔ a.toInt64 ≤ b.toInt64 := by
  have ha := Verify.ordKey_signed (w := 8) (by decide) (by decide) a
  have hb := Verify.ordKey_signed (w := 8) (by decide) (by decide) b
  rw [sx8_toInt64] at ha hb
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub] at ha hb
  rw [UInt64.le_iff_toNat_le, Int64.le_iff_toInt_le]
  omega

/-- **`groupEdge` at `long` times is one `binRows`**, the right's time column read where it lies (its
    bytes, or its frame-of-reference decode — the payload `bytesOf` names either way), the groups' `rows`
    as the order and their `bounds` as longs, `nr` the miss. -/
theorem groupEdge_long (gs : Eval.Groups) (ids rc nc : Column) (nr : Nat) {hay keys gids : ByteArray}
    (hrt : rc.ty = .long) (hnt : nc.ty = .long) (hrb : Column.bytesOf rc = some hay)
    (hkb : Column.bytesOf nc = some keys) (hgb : Column.bytesOf ids = some gids)
    (hsz : keys.size / 8 = gids.size / 8) :
    Eval.groupEdge gs ids (.vector rc) (.vector nc) nr = Column.ofBytes .long
      (Kernel.binRows 8 false true false hay keys gs.rows (Kernel.longBytes gs.bounds) gids nr.toUInt64) := by
  obtain ⟨t, n, e, a⟩ := rc
  obtain ⟨u, m, f, b⟩ := nc
  simp only at hrt hnt
  subst hrt hnt
  have h1 : (QValue.vector ⟨.long, n, e, a⟩).bare = .vector ⟨.long, n, e, none⟩ := by
    rcases a with _ | ⟨_, _⟩ <;> rfl
  have h2 : (QValue.vector ⟨.long, m, f, b⟩).bare = .vector ⟨.long, m, f, none⟩ := by
    rcases b with _ | ⟨_, _⟩ <;> rfl
  have hrb' : Column.bytesOf ⟨.long, n, e, none⟩ = some hay := by rw [← hrb]; rfl
  have hkb' : Column.bytesOf ⟨.long, m, f, none⟩ = some keys := by rw [← hkb]; rfl
  unfold Eval.groupEdge
  simp only [h1, h2, Kernel.denseWidth, QAtomicType.width, hkb', hgb, hsz, Kernel.longColumn, bne_self_eq_false,
    beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, bind, Option.bind, Kernel.foldsZero, Kernel.ordSigned]
  cases e with
  | foR md pk =>
    have hd : Kernel.Coc.decode (USize.ofNat 8) md pk (USize.ofNat n) = hay := by
      simpa [Column.bytesOf, QAtomicType.width] using hrb'
    by_cases hm : md.isEmpty = true
    · simp [Kernel.foRColumn, hm, hrb'] <;> rfl
    · simp [Kernel.foRColumn, hm, Kernel.foRBinRows, Column.encodes, ← hd] <;> rfl
  | _ => simp [Kernel.foRColumn, hrb'] <;> rfl

/-- What `binSpec` names is a row of its group. -/
theorem binSpec_mem {rt : List Int64} {g : List Nat} {x : Int64} {r : Nat} (h : Struct.binSpec rt g x = some r) :
    r ∈ g := by
  unfold Struct.binSpec at h
  have hle : Id.run (Eval.partitionAt (fun j => (pure (decide (rt[g[j]!]! ≤ x)) : Id Bool)) g.length) ≤ g.length :=
    partitionAt_go_le _ _ _ _ (Nat.zero_le _)
  generalize Id.run (Eval.partitionAt (fun j => (pure (decide (rt[g[j]!]! ≤ x)) : Id Bool)) g.length) = P at h hle
  rcases P with _ | p
  · cases h
  · simp only [Option.some.injEq, Nat.add_sub_cancel] at h
    subst h
    rw [getElem!_pos g p (by omega)]; exact List.getElem_mem _

/-- **`aj` is `ajSpec` once its groups are known.** Where `keyGroups` answers groups `gs` and ids whose word
    `i` names a group spanning exactly `Struct.group rk lk[i]` (the right rows of left row `i`'s key, in row
    order, read through `gs.rows`), or no group where that is empty, `aj` over dense long times `keys`, `hay`
    answers `ajSpec`. Nothing is assumed about the times' order inside a group. -/
theorem aj_groups {κ : Type} [BEq κ] [Inhabited κ] {l r : Array Struct.KCol} {tl tr : Column} {m : Nat}
    {A : Arr .long m} {gs : Eval.Groups} {ids : Column} {keys hay gids : ByteArray} (lk rk : List κ)
    (htl : tl.ty = .long) (htr : tr.ty = .long) (hkb : Column.bytesOf tl = some keys)
    (hrb : Column.bytesOf tr = some hay) (hgb : Column.bytesOf ids = some gids)
    (hkn : keys.size / 8 = tl.n) (hgn : gids.size / 8 = tl.n) (hrn : hay.size / 8 = tr.n)
    (hlk : lk.length = tl.n) (hrk : rk.length = tr.n) (hU : tl.n < USize.size) (h63 : tr.n < 2 ^ 63)
    (hkg : Struct.keyGroups "aj" l r tl.n tr.n = .ok (gs, ids))
    (hgrp : ∀ i, i < tl.n →
      (Kernel.longBytes gs.bounds).size / 8 - 1 ≤ (Column.bitsAt gids (i * 8) 8).toNat ∧
        Struct.group rk lk[i]! = [] ∨
      (Column.bitsAt gids (i * 8) 8).toNat < (Kernel.longBytes gs.bounds).size / 8 - 1 ∧
        (Struct.group rk lk[i]!).length =
          (Column.bitsAt (Kernel.longBytes gs.bounds) ((Column.bitsAt gids (i * 8) 8).toNat * 8 + 8) 8).toNat -
          (Column.bitsAt (Kernel.longBytes gs.bounds) ((Column.bitsAt gids (i * 8) 8).toNat * 8) 8).toNat ∧
        ∀ p, p < (Struct.group rk lk[i]!).length → (Struct.group rk lk[i]!)[p]! =
          let lo := (Column.bitsAt (Kernel.longBytes gs.bounds) ((Column.bitsAt gids (i * 8) 8).toNat * 8) 8).toNat
          if gs.rows.isEmpty then lo + p else (Column.bitsAt gs.rows ((lo + p) * 8) 8).toNat)
    (h : Struct.aj l r ⟨.long, tl⟩ ⟨.long, tr⟩ = .ok ⟨m, A⟩) :
    A.toList = Struct.ajSpec lk ((nats keys).map Int64.ofNat) rk ((nats hay).map Int64.ofNat) := by
  have hE := groupEdge_long gs ids tr tl tr.n htr htl hrb hkb hgb (by omega)
  simp only [Struct.aj, Struct.colRows, Struct.colValue, hkg, hE, Find.dense, Column.ofBytes, Column.bytesOf,
    beq_self_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i A' hA
  simp only [Except.ok.injEq, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  obtain rfl := eq_of_heq h
  have hc := Struct.of_c hA
  rw [Arr.toList_long_bytes _ (by rw [hc]; rfl)]
  -- `^`'s word `i`: the atom where the word is the null `nr`, the word otherwise
  have hfill : ∀ (nul x y : Int64), Kernel.Ew.intStep Kernel.Ew.fill nul x y = if y == nul then x else y :=
    fun _ _ _ => rfl
  have key : ∀ (nul : Int64) (c : UInt64) (b : ByteArray) (i : Nat), i < tl.n →
      Column.bitsAt (Kernel.Ew.val Kernel.Ew.fill Kernel.Ew.i64 Kernel.Ew.av nul (Find.one c) b tl.n.toUSize)
        (i * 8) 8 = (Kernel.Ew.intStep Kernel.Ew.fill nul c.toInt64 (Column.bitsAt b (i * 8) 8).toInt64).toUInt64 := by
    intro nul c b i hi
    have hv := val_i64_av Kernel.Ew.fill nul c b tl.n hU
    have hl := congrArg List.length hv
    simp only [Verify.elemsW, List.length_map, List.length_range] at hl
    have := congrArg (fun L => L[i]?) hv
    simp only [Verify.elemsW, List.getElem?_map, List.getElem?_range, hl, hi, Option.map_some,
      Option.some.injEq] at this
    exact this
  have hnr : (UInt64.ofNat tr.n).toInt64 = Int64.ofNat tr.n := by
    rw [toInt64_eq_ofNat, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  rw [List.map_map]
  unfold Struct.ajSpec
  apply List.ext_getElem (by simp [nats_length, hlk, hkn])
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, List.getElem_zip, Function.comp_apply]
  rw [key _ _ _ i h1, show i * 8 = 8 * i from Nat.mul_comm ..]
  have h8 : (8 : USize).toNat = 8 := by simp
  have hx : (nats keys)[i]'(by rw [nats_length]; omega) = (Column.bitsAt keys (i * 8) 8).toNat := by
    rw [← getElem!_pos _ i (by rw [nats_length]; omega), nats_get _ (by omega)]
  rw [hx, ← toInt64_eq_ofNat, ← getElem!_pos lk i (by omega)]
  have hG : ∀ p, p < (Struct.group rk lk[i]!).length → (Struct.group rk lk[i]!)[p]! < tr.n := fun p hp => by
    rw [getElem!_pos _ p hp]
    have := List.mem_range.1 (List.mem_filter.1 (List.getElem_mem hp)).1
    omega
  rcases hgrp i h1 with ⟨hng, hG0⟩ | ⟨hng, hlen, hrow⟩
  · rw [bitsAt_binRows_miss 8 false true false hay keys gs.rows _ gids _ (by simp; omega) rfl hng, hG0]
    simp [Struct.binSpec, hfill, Nat.toUInt64_eq, hnr] <;> rfl
  · rw [bitsAt_binRows 8 false true false hay keys gs.rows _ gids _ (by simp; omega) (by omega) rfl hng rfl rfl
      ((nats hay).map Int64.ofNat) _ (Column.bitsAt keys (i * 8) 8).toInt64 hlen hrow fun p hp => by
        have hr := hrow p hp
        unfold binTest
        simp only [h8, Bool.false_eq_true, ↓reduceIte]
        rw [← hr, get!_map _ _ (by rw [nats_length]; have := hG p hp; omega), nats_get _ (by have := hG p hp; omega),
          ← toInt64_eq_ofNat]
        simp only [ordKey8_le]]
    cases hb : Struct.binSpec ((nats hay).map Int64.ofNat) (Struct.group rk lk[i]!) (Column.bitsAt keys (i * 8) 8).toInt64
    · simp [hfill, Nat.toUInt64_eq, hnr]
    · rename_i r
      have hrn : r < tr.n := by
        have := binSpec_mem hb
        simp only [Struct.group, List.mem_filter, List.mem_range] at this
        omega
      have hr' : (UInt64.ofNat r).toInt64 = Int64.ofNat r := by
        rw [toInt64_eq_ofNat, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      have hne : (UInt64.ofNat r).toInt64 ≠ Int64.ofNat tr.n := fun e => by
        rw [← hnr] at e
        have := congrArg Int64.toInt e
        rw [toInt_word (u := UInt64.ofNat r) (a := r) (by rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)])
          (by omega), toInt_word (u := UInt64.ofNat tr.n) (a := tr.n)
          (by rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]) h63] at this
        omega
      simp [hfill, Nat.toUInt64_eq, hr']
      exact fun e => absurd e (hr' ▸ hne)

/-! ## `keyMatch`'s `grouped` path: the right's buckets, and the left's `?` into its distinct words

  A right key column no mark claims takes `grouped`: `Kernel.groupColumn` answers `Order.group` — the first
  occurrences' words, the buckets laid end to end, their byte bounds — and `findColumn` places each left
  word among those words. The bucket a left word lands on is its `Struct.group`. -/

open QLean.Kernel in
/-- **The bucket at a needle's place among the first occurrences is the needle's `Struct.group`**; a needle
    past them all has an empty group. -/
theorem bucket_idxOf (B : ByteArray) (x : UInt64) :
    ((Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8)).length ≤
        ((Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8)).map fun f => Column.bitsAt B (f * 8) 8).idxOf x ∧
      Struct.group (Verify.elemsW 8 B) x = []) ∨
    ∃ h : ((Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8)).map fun f => Column.bitsAt B (f * 8) 8).idxOf x <
        (Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8)).length,
      Order.bucket .i64 (B.size / 8) B ((Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8))[
        ((Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8)).map fun f => Column.bitsAt B (f * 8) 8).idxOf x]'h) =
        Struct.group (Verify.elemsW 8 B) x := by
  have hw : ∀ i, i < B.size / 8 → (Verify.elemsW 8 B)[i]! = Column.bitsAt B (i * 8) 8 := fun i hi => by
    rw [getElem!_pos _ i (by simp [Verify.elemsW]; omega)]; simp [Verify.elemsW]
  have hlen : (Verify.elemsW 8 B).length = B.size / 8 := by simp [Verify.elemsW]
  have hkey : ∀ i j, Order.keyAt .i64 B i = Order.keyAt .i64 B j ↔
      Column.bitsAt B (i * 8) 8 = Column.bitsAt B (j * 8) 8 := fun i j => Verify.keyAt_eq_iff (by simp) B i j
  unfold Struct.group
  rw [hlen]
  by_cases hg : ((Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8)).map fun f => Column.bitsAt B (f * 8) 8).idxOf x <
      (Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8)).length
  · right
    refine ⟨hg, ?_⟩
    have hx : ((Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8)).map fun f => Column.bitsAt B (f * 8) 8)[
        ((Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8)).map fun f => Column.bitsAt B (f * 8) 8).idxOf x]'(by
          simpa using hg) = x := by
      have hlt : List.findIdx (fun y => y == x) ((Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8)).map
          fun f => Column.bitsAt B (f * 8) 8) < ((Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8)).map
          fun f => Column.bitsAt B (f * 8) 8).length := by rw [List.length_map]; exact hg
      exact beq_iff_eq.1 (List.findIdx_getElem (w := hlt))
    rw [List.getElem_map] at hx
    unfold Order.bucket
    apply List.filter_congr
    intro i hi
    rw [hw i (List.mem_range.1 hi)]
    apply Bool.eq_iff_iff.2
    rw [beq_iff_eq, beq_iff_eq, hkey, hx]
  · left
    refine ⟨by omega, List.filter_eq_nil_iff.2 fun i hi e => hg ?_⟩
    have hi := List.mem_range.1 hi
    rw [hw i hi, beq_iff_eq] at e
    obtain ⟨f, hf, ef⟩ := Verify.exists_first (g := Order.keyAt .i64 B) hi
    have hm : x ∈ (Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8)).map fun f => Column.bitsAt B (f * 8) 8 :=
      List.mem_map.2 ⟨f, hf, by rw [← e]; exact (hkey f i).1 ef⟩
    simpa using (Verify.idxOf_lt_length x _).2 hm

/-- `Order.bounds`' fold from any start: the start's entries, then `8·` each running total past `pos`. -/
theorem bounds_fold (lens : List Nat) : ∀ (acc : Array Nat) (pos : Nat),
    (lens.foldl (fun (x : Array Nat × Nat) len => (x.1.push (8 * (x.2 + len)), x.2 + len)) (acc, pos)).1.toList =
      acc.toList ++ (List.range lens.length).map fun k => 8 * (pos + (lens.take (k + 1)).sum) := by
  induction lens with
  | nil => intro acc pos; simp
  | cons len ls ih =>
    intro acc pos
    rw [List.foldl_cons]
    refine (ih (acc.push (8 * (pos + len))) (pos + len)).trans ?_
    simp [List.range_succ_eq_map, List.take_succ_cons, Nat.add_assoc]

/-- `Order.bounds` cut down to element counts: entry `k` is the lengths before bucket `k`. -/
theorem bounds_div (lens : List Nat) :
    ((Kernel.Order.bounds lens).map (· / 8)).toList = (List.range (lens.length + 1)).map fun k => (lens.take k).sum := by
  have e : (Kernel.Order.bounds lens).toList =
      #[0].toList ++ (List.range lens.length).map fun k => 8 * (0 + (lens.take (k + 1)).sum) := bounds_fold lens #[0] 0
  rw [Array.toList_map, e]
  simp [List.range_succ_eq_map, Function.comp_def]

/-- `longBytes` reads back, eight bytes a long, as the numbers it was built from. -/
theorem longBytes_ids (a : Array Nat) (h : ∀ x ∈ a.toList, x < 2 ^ 64) :
    Verify.ids (Kernel.longBytes a) = a.toList := by
  have : Kernel.longBytes a = Kernel.Order.indices a.toList := by
    rw [Kernel.longBytes, ← Array.foldl_toList]; rfl
  rw [this]; exact Verify.ids_indices _ h

/-- Position `p` of bucket `g` sits, in the buckets laid end to end, past the lengths before it. -/
theorem flatten_getElem? (bs : List (List Nat)) : ∀ g (hg : g < bs.length) p, p < bs[g].length →
    bs.flatten[((bs.take g).map List.length).sum + p]? = bs[g][p]? := by
  induction bs with
  | nil => intro g hg; simp at hg
  | cons l ls ih =>
    intro g hg p hp
    cases g with
    | zero =>
      simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatten_cons,
        List.getElem_cons_zero] at hp ⊢
      rw [List.getElem?_append_left hp]
    | succ g =>
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons,
        List.getElem_cons_succ] at hp ⊢
      rw [Nat.add_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact ih g (by simpa using hg) p hp

/-- The lengths of the first `k` buckets are at most all of them laid end to end. -/
theorem take_sum_le (bs : List (List Nat)) (k : Nat) :
    ((bs.map List.length).take k).sum ≤ bs.flatten.length := by
  rw [← List.map_take, ← List.length_flatten]
  have e : bs.flatten = (bs.take k).flatten ++ (bs.drop k).flatten := by
    rw [← List.flatten_append, List.take_append_drop]
  rw [e, List.length_append]; omega

/-- A strictly ascending list from `0` to its length less one is `0, 1, …`. -/
theorem ids_identity (L : List Nat) (hlt : ∀ i (h : i + 1 < L.length), L[i] < L[i + 1])
    (hl : ∀ h : 0 < L.length, L[L.length - 1] = L.length - 1) :
    ∀ q (h : q < L.length), L[q] = q := by
  have ge : ∀ q (h : q < L.length), q ≤ L[q] := by
    intro q
    induction q with
    | zero => intro _; omega
    | succ q ih => intro h; have := hlt q h; have := ih (by omega); omega
  have le : ∀ d q (h : q < L.length), q + d = L.length - 1 → L[q] + d ≤ L[L.length - 1] := by
    intro d
    induction d with
    | zero => intro q h e; obtain rfl : q = L.length - 1 := by omega
              simp
    | succ d ih => intro q h e; have := hlt q (by omega); have := ih (q + 1) (by omega) (by omega); omega
  intro q h
  have := ge q h; have := le (L.length - 1 - q) q h (by omega); have := hl (by omega); omega

open QLean.Kernel in
/-- `Order.ascending`, strict and at `i64`, over longs below `2^63`: each long is below the next. -/
theorem ascending_ids {b : ByteArray} {L : List Nat} (hL : Verify.ids b = L) (h63 : ∀ x ∈ L, x < 2 ^ 63)
    (ha : Order.ascending .i64 false true (b.size / 8).toUSize b = true) (hU : b.size / 8 < USize.size) :
    ∀ i (h : i + 1 < L.length), L[i] < L[i + 1] := by
  intro i h
  have hlen : L.length = b.size / 8 := by rw [← hL]; simp [Verify.ids]
  unfold Order.ascending at ha
  have := List.all_eq_true.1 ha i (List.mem_range.2 (by
    simp only [USize.toNat_ofNat_of_lt' hU, Scan.Kind.avail, Scan.Kind.width]; omega))
  simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq, Order.keyAt, Order.rank, Scan.Kind.bitsAt,
    Scan.Kind.width] at this
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_xor, UInt64.toNat_xor] at this
  have e1 := Verify.ids_get hL (j := i) (by omega)
  have e2 := Verify.ids_get hL (j := i + 1) h
  rw [e1, e2, show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl,
    xor_two_pow_of_lt (h63 _ (List.getElem_mem _)), xor_two_pow_of_lt (h63 _ (List.getElem_mem _))] at this
  omega

/-- **`Groups.of` over buckets laid end to end answers each bucket as one span**: there are as many groups as
    buckets, group `g`'s bounds read as longs are the lengths before bucket `g` and through it, and its rows
    read through `rows` — the position itself where `Groups.of` dropped `rows` as the identity — are the
    bucket. -/
theorem groups_of_buckets (bs : List (List Nat)) (h63 : ∀ r ∈ bs.flatten, r < 2 ^ 63)
    (hU : bs.flatten.length < USize.size) {gs : Eval.Groups}
    (hgs : gs = Eval.Groups.of (Kernel.Order.indices bs.flatten)
      ((Kernel.Order.bounds (bs.map List.length)).map (· / 8))) :
    (Kernel.longBytes gs.bounds).size / 8 - 1 = bs.length ∧
    ∀ g (hg : g < bs.length),
      (Column.bitsAt (Kernel.longBytes gs.bounds) (g * 8) 8).toNat = ((bs.map List.length).take g).sum ∧
      (Column.bitsAt (Kernel.longBytes gs.bounds) (g * 8 + 8) 8).toNat =
        ((bs.map List.length).take g).sum + bs[g].length ∧
      ∀ p, p < bs[g].length → bs[g][p]! =
        if gs.rows.isEmpty then ((bs.map List.length).take g).sum + p
        else (Column.bitsAt gs.rows ((((bs.map List.length).take g).sum + p) * 8) 8).toNat := by
  have hbd : gs.bounds = (Kernel.Order.bounds (bs.map List.length)).map (· / 8) := by
    rw [hgs]; unfold Eval.Groups.of; dsimp only; split <;> rfl
  have hB : gs.bounds.toList = (List.range (bs.length + 1)).map fun k => ((bs.map List.length).take k).sum := by
    rw [hbd, bounds_div, List.length_map]
  have h64 : USize.size ≤ 2 ^ 64 := USize.size_le
  have hBi : Verify.ids (Kernel.longBytes gs.bounds) = gs.bounds.toList := longBytes_ids _ (by
    rw [hB]; intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    have := take_sum_le bs k
    omega)
  have hlen : (Kernel.longBytes gs.bounds).size / 8 = bs.length + 1 := by
    have := congrArg List.length hBi
    simpa [Verify.ids, hB] using this
  have hat : ∀ k, k ≤ bs.length → (Column.bitsAt (Kernel.longBytes gs.bounds) (k * 8) 8).toNat =
      ((bs.map List.length).take k).sum := fun k hk => by
    rw [Verify.ids_get hBi (j := k) (by rw [hB]; simp; omega)]
    simp [hB]
  have hI : Verify.ids (Kernel.Order.indices bs.flatten) = bs.flatten :=
    Verify.ids_indices _ fun r hr => Nat.lt_trans (h63 r hr) (by decide)
  have hk : (Kernel.Order.indices bs.flatten).size / 8 = bs.flatten.length := by
    have := congrArg List.length hI; simpa [Verify.ids] using this
  have hrow : ∀ g (hg : g < bs.length) p (hp : p < bs[g].length),
      ((bs.map List.length).take g).sum + p < bs.flatten.length ∧
      (Column.bitsAt (Kernel.Order.indices bs.flatten) ((((bs.map List.length).take g).sum + p) * 8) 8).toNat =
        bs[g][p] := by
    intro g hg p hp
    have e := flatten_getElem? bs g hg p hp
    rw [List.map_take, List.getElem?_eq_getElem hp] at e
    obtain ⟨hq, e⟩ := List.getElem?_eq_some_iff.1 e
    exact ⟨hq, by rw [Verify.ids_get hI hq, e]⟩
  -- `Groups.of` keeps the rows, or drops them where they are `0, 1, …` (strictly ascending, first and last)
  have hcases : (gs.rows = ByteArray.empty ∧ ∀ q (h : q < bs.flatten.length), bs.flatten[q] = q) ∨
      gs.rows = Kernel.Order.indices bs.flatten := by
    rw [hgs]; unfold Eval.Groups.of; dsimp only
    split
    · rename_i hid
      left; refine ⟨rfl, ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hid
      exact ids_identity bs.flatten (ascending_ids hI h63 hid.2 (by rw [hk]; exact hU)) fun h => by
        have hl := hid.1.2; rw [hk] at hl; rw [← Verify.ids_get hI (by omega)]; exact hl
    · right; rfl
  refine ⟨by omega, fun g hg => ⟨hat g (by omega), ?_, fun p hp => ?_⟩⟩
  · rw [show g * 8 + 8 = (g + 1) * 8 by omega, hat (g + 1) (by omega), List.take_succ, List.sum_append_nat]
    simp [List.getElem?_map, List.getElem?_eq_getElem hg]
  · obtain ⟨hq, hr⟩ := hrow g hg p hp
    rw [getElem!_pos _ p hp, ← hr]
    rcases hcases with ⟨he, hid⟩ | he <;> rw [he]
    · rw [if_pos (by simp [ByteArray.isEmpty]), Verify.ids_get hI hq, hid _ hq]
    · have hne : (Kernel.Order.indices bs.flatten).isEmpty = false := by
        simp only [ByteArray.isEmpty, beq_eq_false_iff_ne]; omega
      simp only [hne, Bool.false_eq_true, ↓reduceIte]

open QLean.Kernel in
/-- **`groupColumn` at a long column is `Order.group` over its words**, laid out in bytes `B` — the column's
    own, or its frame-of-reference decode. -/
theorem groupColumn_long {c : Column} {ws : List UInt64} (ht : c.ty = .long) (hw : longWords c = some ws)
    (hn : ws.length = c.n) (hU : c.n < USize.size) :
    ∃ B, Verify.elemsW 8 B = ws ∧ B.size / 8 = c.n ∧ groupColumn .long c =
      some (.dict (.vector ⟨.long, (Order.group .i64 c.n.toUSize B).1.size / 8,
          .bytes (Order.group .i64 c.n.toUSize B).1, none⟩)
        (.slices ⟨.long, (Order.group .i64 c.n.toUSize B).2.1.size / 8,
          .bytes (Order.group .i64 c.n.toUSize B).2.1, none⟩ (Order.group .i64 c.n.toUSize B).2.2) false) := by
  obtain ⟨t, n, e, a⟩ := c
  simp only at ht hn hU ⊢
  subst ht
  cases e with
  | bytes b =>
    simp only [longWords, Option.some.injEq] at hw
    have hs : b.size / 8 = n := by rw [← hn, ← hw]; simp [Verify.elemsW]
    refine ⟨b, hw, hs, ?_⟩
    simp [groupColumn, orderKind, Column.bytesOf, hs, Scan.Kind.width]
  | foR md pk =>
    simp only [longWords, Option.some.injEq] at hw
    have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
    obtain ⟨hsz, hbits⟩ := Verify.decodeW (8 : Nat).toUSize (by rw [h8]; decide) md pk n.toUSize
    rw [h8, USize.toNat_ofNat_of_lt' hU] at hsz hbits
    refine ⟨Coc.decode (8 : Nat).toUSize md pk n.toUSize, ?_, by rw [hsz]; omega, ?_⟩
    · rw [← hw]
      apply List.ext_getElem (by simp [Verify.elemsW, hsz])
      intro i h1 h2
      simp only [Verify.elemsW, List.getElem_map, List.getElem_range]
      rw [hbits i (by simpa using h2), Verify.ofNat_toNat_mod64]
    · simp [groupColumn, orderKind, Order.groupFoR, Scan.Kind.width]
  | _ => simp [longWords] at hw

/-- Counting below `K + 1` is counting below `K` and at `K`. -/
theorem filter_lt_succ (f : Nat → Nat) (K : Nat) (L : List Nat) :
    (L.filter fun i => decide (f i < K + 1)).length =
      (L.filter fun i => decide (f i < K)).length + (L.filter fun i => f i == K).length := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    by_cases h1 : f i < K <;> by_cases h2 : f i = K <;> by_cases h3 : f i < K + 1 <;>
      simp [List.filter_cons, h1, h2, h3, ih] <;> omega

/-- **The buckets laid end to end hold every index once**: their lengths sum to `m`. -/
theorem buckets_length {α : Type} [DecidableEq α] (g : Nat → α) (m : Nat) :
    ((Verify.firstsOf g m).map (Verify.bucketOf g m)).flatten.length = m := by
  have hsum : ∀ K, ((List.range K).map fun j =>
      ((List.range m).filter fun i => Verify.groupOf g m i == j).length).sum =
      ((List.range m).filter fun i => decide (Verify.groupOf g m i < K)).length := by
    intro K
    induction K with
    | zero =>
      rw [show ((List.range m).filter fun i => decide (Verify.groupOf g m i < 0)) = [] from
        List.filter_eq_nil_iff.2 fun i _ => by simp]; rfl
    | succ K ih => rw [List.range_succ, List.map_append, List.sum_append_nat, ih, filter_lt_succ]; simp
  have hmap : (Verify.firstsOf g m).map (fun f => (Verify.bucketOf g m f).length) =
      (List.range (Verify.firstsOf g m).length).map fun j =>
        ((List.range m).filter fun i => Verify.groupOf g m i == j).length := by
    apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [Verify.rows_groupOf g m (by simpa using h1)]
  rw [List.length_flatten, List.map_map, Function.comp_def, hmap, hsum, List.filter_eq_self.2, List.length_range]
  intro i hi
  exact decide_eq_true (Verify.groupOf_lt (List.mem_range.1 hi))

/-- One long key column per side meets `keyMatch`'s kernels as itself, bare. -/
theorem keyColumns_long (cr cl : Column) (hrt : cr.ty = .long) (hlt : cl.ty = .long) :
    Eval.keyColumns #[.vector cr] #[.vector cl] =
      some (.long, { cr with attr := none }, .vector { cl with attr := none }) := by
  obtain ⟨t, n, e, a⟩ := cr
  obtain ⟨u, n', e', a'⟩ := cl
  simp only at hrt hlt
  subst hrt hlt
  -- `Array.mapM` and `Array.zip` recurse well-founded, so the literals are read through their lists
  rcases a with _ | ⟨_, _⟩ <;> rcases a' with _ | ⟨_, _⟩ <;>
    (unfold Eval.keyColumns; rw [Array.mapM_eq_mapM_toList, Array.toList_zip]; rfl)

/-- **What `keyMatch` must answer for a key join**: `ids` is a long payload with a word per left key, and
    word `i` names a group whose span (`bounds` read as longs, rows through `rows` or the position itself) lists
    `Struct.group rk lk[i]`, or names no group where that is empty — `aj_groups`' hypothesis. -/
def KeyAnswers {κ : Type} [BEq κ] [Inhabited κ] (rk lk : List κ) (gs : Eval.Groups) (ids : Column) : Prop :=
  ∃ gids, Column.bytesOf ids = some gids ∧ gids.size / 8 = lk.length ∧ ∀ i, i < lk.length →
    (Kernel.longBytes gs.bounds).size / 8 - 1 ≤ (Column.bitsAt gids (i * 8) 8).toNat ∧
        Struct.group rk lk[i]! = [] ∨
      (Column.bitsAt gids (i * 8) 8).toNat < (Kernel.longBytes gs.bounds).size / 8 - 1 ∧
        (Struct.group rk lk[i]!).length =
          (Column.bitsAt (Kernel.longBytes gs.bounds) ((Column.bitsAt gids (i * 8) 8).toNat * 8 + 8) 8).toNat -
          (Column.bitsAt (Kernel.longBytes gs.bounds) ((Column.bitsAt gids (i * 8) 8).toNat * 8) 8).toNat ∧
        ∀ p, p < (Struct.group rk lk[i]!).length → (Struct.group rk lk[i]!)[p]! =
          let lo := (Column.bitsAt (Kernel.longBytes gs.bounds) ((Column.bitsAt gids (i * 8) 8).toNat * 8) 8).toNat
          if gs.rows.isEmpty then lo + p else (Column.bitsAt gs.rows ((lo + p) * 8) 8).toNat

open QLean.Kernel in
/-- **`keyMatch`'s `grouped` path answers the key groups.** A right long key column no mark claims (`` `s ``,
    `` `u ``, `` `p ``, `` `g ``) is grouped by `Order.group` and each left word placed among the distinct words
    by `?`; the groups and ids it answers are `KeyAnswers` of the two sides' words, bytes or frame of
    reference alike. -/
theorem keyMatch_grouped {cr cl : Column} {wr wl : List UInt64} (nr nl : Nat) (hrt : cr.ty = .long)
    (hlt : cl.ty = .long) (hrw : longWords cr = some wr) (hrn : wr.length = cr.n) (h63 : cr.n < 2 ^ 63)
    (hU : cr.n < USize.size) (hlU : cl.n < USize.size) (hlwf : cl.WF) (hlR : Find.Readable .long cl)
    (hwl : longWords cl = some wl)
    (hattr : ∀ a cell, cr.attr = some (a, cell) → a ≠ 1 ∧ a ≠ 2 ∧ a ≠ 3 ∧ a ≠ 4) :
    KeyAnswers wr wl (Eval.keyMatch #[.vector cr] nr #[.vector cl] nl).1
      (Eval.keyMatch #[.vector cr] nr #[.vector cl] nl).2 := by
  obtain ⟨B, hBw, hBn, hG⟩ := groupColumn_long (c := { cr with attr := none }) hrt hrw hrn hU
  simp only at hBn hG
  have hm : min cr.n.toUSize.toNat (Scan.Kind.avail .i64 B) = B.size / 8 := by
    rw [USize.toNat_ofNat_of_lt' hU]; simp [Scan.Kind.avail, Scan.Kind.width, hBn]
  have hgroup : Order.group .i64 cr.n.toUSize B = (Order.distinct .i64 cr.n.toUSize B,
      Order.indices ((Order.firsts .i64 (B.size / 8) B).map (Order.bucket .i64 (B.size / 8) B)).flatten,
      Order.bounds (((Order.firsts .i64 (B.size / 8) B).map (Order.bucket .i64 (B.size / 8) B)).map List.length)) := by
    unfold Order.group; dsimp only; rw [hm]
  generalize hF : Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8) = F
  have hbs : (Order.firsts .i64 (B.size / 8) B).map (Order.bucket .i64 (B.size / 8) B) =
      F.map (Verify.bucketOf (Order.keyAt .i64 B) (B.size / 8)) := by rw [← hF]; rfl
  -- the distinct words, as a long column the probe reads
  have hkw : Verify.elemsW 8 (Order.distinct .i64 cr.n.toUSize B) = F.map fun f => Column.bitsAt B (f * 8) 8 := by
    have := Verify.distinct_spec .i64 cr.n.toUSize B
    rw [hm, hF] at this; exact this
  have hks : (Order.distinct .i64 cr.n.toUSize B).size = F.length * 8 := by
    have := congrArg List.length hkw
    simp only [Verify.elemsW, List.length_map, List.length_range] at this
    have h := (Verify.foldl_pushBits (Scan.Kind.bitsAt .i64 B) 8 (by decide)
      (Order.firsts .i64 (min cr.n.toUSize.toNat (Scan.Kind.avail .i64 B)) B) ByteArray.empty).1
    rw [hm, show Order.firsts .i64 (B.size / 8) B = F from hF] at h
    have e : (Order.distinct .i64 cr.n.toUSize B).size = ByteArray.empty.size + 8 * F.length := by
      rw [← h]; unfold Order.distinct; dsimp only; rw [hm, show Order.firsts .i64 (B.size / 8) B = F from hF]; rfl
    rw [e]; simp [Nat.mul_comm]
  have hFlen : F.length ≤ B.size / 8 := by
    rw [← hF]; exact Nat.le_trans (List.length_filter_le _ _) (by simp [Verify.firstsOf])
  let kx : Arr .long ((Order.distinct .i64 cr.n.toUSize B).size / 8) :=
    ⟨⟨.long, _, .bytes (Order.distinct .i64 cr.n.toUSize B), none⟩, rfl, rfl, by
      show _ = _ * 8; rw [hks, Nat.mul_div_cancel _ (by decide)]⟩
  let ly : Arr .long cl.n := ⟨{ cl with attr := none }, hlt, rfl, hlwf⟩
  obtain ⟨P, xs, ys, hP, hxs, hys, hmap⟩ := Find.probe_find kx ly trivial hlR
    (by rw [hks, Nat.mul_div_cancel _ (by decide)]; omega) hlU
  simp only [kx, longWords, Option.some.injEq] at hxs
  have hys' : ys = wl := by simp only [ly] at hys; rw [show longWords { cl with attr := none } = longWords cl from rfl, hwl] at hys; exact (Option.some.inj hys).symm
  subst hxs
  rw [hys'] at hmap
  -- `keyMatch` at an unmarked right column is `grouped`
  have hK : Eval.keyMatch #[.vector cr] nr #[.vector cl] nl =
      (Eval.Groups.of (Order.group .i64 cr.n.toUSize B).2.1 ((Order.group .i64 cr.n.toUSize B).2.2.map (· / 8)),
        ⟨.long, P.size / 8, .bytes P, none⟩) := by
    have hFc := Find.findColumn_long false ⟨.long, (Order.distinct .i64 cr.n.toUSize B).size / 8, .bytes (Order.distinct .i64 cr.n.toUSize B), none⟩
      { cl with attr := none } hlt
    simp only [kx, ly] at hP
    simp only [Bool.false_eq_true, false_and, ↓reduceIte, hP, Option.map_some] at hFc
    unfold Eval.keyMatch
    rw [keyColumns_long cr cl hrt hlt]
    have hg1 : (Order.group .i64 cr.n.toUSize B).1 = Order.distinct .i64 cr.n.toUSize B := by rw [hgroup]
    simp only [bind, Option.bind, hG, hg1, hFc]
    obtain ⟨t, n, e, a⟩ := cr
    simp only at hrt
    subst hrt
    rcases a with _ | ⟨a, cell⟩
    · simp [QValue.marking]
    · obtain ⟨h1, h2, h3, h4⟩ := hattr a cell rfl
      simp [QValue.marking, h1, h2, h3, h4]
  rw [hK, hgroup, hbs]
  dsimp only
  have hflat := buckets_length (Order.keyAt .i64 B) (B.size / 8)
  rw [hF] at hflat
  obtain ⟨hsz, hspan⟩ := groups_of_buckets (F.map (Verify.bucketOf (Order.keyAt .i64 B) (B.size / 8)))
    (fun r hr => by
      obtain ⟨l, hl, hrl⟩ := List.mem_flatten.1 hr
      obtain ⟨f, -, rfl⟩ := List.mem_map.1 hl
      have := List.mem_range.1 (List.mem_filter.1 hrl).1
      omega)
    (by rw [hflat]; omega) rfl
  have hPn : P.size / 8 = wl.length := by
    have := congrArg List.length hmap; simpa [Verify.elemsW] using this
  refine ⟨P, rfl, hPn, fun i hi => ?_⟩
  have hPi : (Column.bitsAt P (i * 8) 8).toNat =
      (F.map fun f => Column.bitsAt B (f * 8) 8).idxOf wl[i] := by
    have := congrArg (·[i]?) hmap
    rw [hkw] at this
    simp only [Verify.elemsW, List.map_map, List.getElem?_map, List.getElem?_range (by omega : i < P.size / 8),
      List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq, Function.comp_apply] at this
    exact this
  rw [getElem!_pos wl i hi, ← hBw, hPi]
  simp only [List.length_map] at hsz
  subst hF
  rcases bucket_idxOf B wl[i] with ⟨hge, hnil⟩ | ⟨hlt', hb⟩
  · exact Or.inl ⟨by omega, hnil⟩
  · obtain ⟨hlo, hhi, hrow⟩ := hspan _ (by simpa using hlt')
    simp only [List.getElem_map] at hlo hhi hrow
    change Verify.bucketOf _ _ _ = _ at hb
    simp only [hb] at hhi hrow
    refine Or.inr ⟨by omega, by rw [hhi, hlo]; omega, fun p hp => ?_⟩
    rw [hrow p hp, hlo]

/-- **`aj` at one long key column per side is `ajSpec`** of the two sides' key words: `aj_groups` with its
    group hypothesis answered by `keyMatch_grouped`. The right key column carries no `s#`/`u#`/`p#`/`g#` mark;
    key columns bytes or frame of reference, times dense long. -/
theorem aj_long {cl cr tl tr : Column} {wl wr : List UInt64} {m : Nat} {A : Arr .long m} {keys hay : ByteArray}
    (hlt : cl.ty = .long) (hrt : cr.ty = .long) (hwl : longWords cl = some wl) (hwr : longWords cr = some wr)
    (hln : wl.length = cl.n) (hrn : wr.length = cr.n) (hcl : cl.n = tl.n) (hcr : cr.n = tr.n)
    (hlwf : cl.WF) (hlR : Find.Readable .long cl)
    (hattr : ∀ a cell, cr.attr = some (a, cell) → a ≠ 1 ∧ a ≠ 2 ∧ a ≠ 3 ∧ a ≠ 4)
    (htl : tl.ty = .long) (htr : tr.ty = .long) (hkb : Column.bytesOf tl = some keys)
    (hrb : Column.bytesOf tr = some hay) (hkn : keys.size / 8 = tl.n) (hhn : hay.size / 8 = tr.n)
    (hU : tl.n < USize.size) (hrU : tr.n < USize.size) (h63 : tr.n < 2 ^ 63)
    (h : Struct.aj #[⟨.long, cl⟩] #[⟨.long, cr⟩] ⟨.long, tl⟩ ⟨.long, tr⟩ = .ok ⟨m, A⟩) :
    A.toList = Struct.ajSpec wl ((nats keys).map Int64.ofNat) wr ((nats hay).map Int64.ofNat) := by
  have hkg : Struct.keyGroups "aj" #[⟨.long, cl⟩] #[⟨.long, cr⟩] tl.n tr.n =
      .ok (Eval.keyMatch #[.vector cr] tr.n #[.vector cl] tl.n) := by
    simp [Struct.keyGroups, Struct.colRows, Struct.colValue, hcl, hcr]; rfl
  obtain ⟨gids, hgb, hgn, hgrp⟩ := keyMatch_grouped tr.n tl.n hrt hlt hwr hrn (by omega) (by omega) (by omega)
    hlwf hlR hwl hattr
  exact aj_groups wl wr htl htr hkb hrb hgb hkn (by omega) hhn (by omega) (by omega) hU h63 hkg
    (fun i hi => hgrp i (by omega)) h

#print axioms rangeOffsets_long
#print axioms keyCodes_long
#print axioms ej_long
#print axioms binStep_go
#print axioms bitsAt_binRows
#print axioms bitsAt_binRows_miss
#print axioms ordKey8_le
#print axioms groupEdge_long
#print axioms binSpec_mem
#print axioms aj_groups
#print axioms bucket_idxOf
#print axioms groups_of_buckets
#print axioms groupColumn_long
#print axioms keyColumns_long
#print axioms keyMatch_grouped
#print axioms aj_long

end LeetQ.Rel.Verb
