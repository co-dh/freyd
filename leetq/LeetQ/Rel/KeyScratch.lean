import LeetQ.Rel.SpecStruct

namespace LeetQ.Rel.Verb

open QLean QLean.Dep

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
    ∃ (k : Kernel.Scan.Kind) (f : UInt64 → Nat), (k = .u8 ∨ k = .i16 ∨ k = .i32 ∨ k = .i64) ∧
      (∀ u ∈ wl ++ wr, ∀ u' ∈ wl ++ wr, (f u = f u' ↔ u = u')) ∧
      ∃ lc rc : Alg.Code, os = #[lc, rc] ∧
      lc.kind = some k ∧ lc.n = wl.length ∧ lc.b.size = k.width * wl.length ∧
        (∀ i (hi : i < wl.length), k.bitsAt lc.b i = (f wl[i]).toUInt64) ∧
      rc.kind = some k ∧ rc.n = wr.length ∧ rc.b.size = k.width * wr.length ∧
        (∀ j (hj : j < wr.length), k.bitsAt rc.b j = (f wr[j]).toUInt64) := by
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
  refine ⟨k, fun u => if Kernel.Ew.intStep Kernel.Ew.add Alg.nul u.toInt64 (-base) = Int64.minValue
      then (card - 1).toUSize.toNat else (Kernel.Ew.intStep Kernel.Ew.add Alg.nul u.toInt64 (-base)).toInt.toNat,
    hk4, ?_, c1, c2, rfl,
    hkind c1 w1, n1, s1, fun i hi => by rw [hkb]; exact (b1 i hi).1,
    hkind c2 w2, n2, s2, fun j hj => by rw [hkb]; exact (b2 j hj).1⟩
  intro u hu u' hu'
  have toI : ∀ x y : UInt64, x.toInt64 = y.toInt64 → x = y := fun x y e => by
    have := congrArg Int64.toUInt64 e; simpa using this
  rcases key u hu with ⟨hv, hR⟩ | ⟨hv, hR, hR1, hR2⟩ <;>
    rcases key u' hu' with ⟨hv', hR'⟩ | ⟨hv', hR', hR1', hR2'⟩
  · dsimp only; rw [if_pos hR, if_pos hR']
    exact ⟨fun _ => toI _ _ (hv.trans hv'.symm), fun _ => rfl⟩
  · dsimp only; rw [if_pos hR, if_neg hR', hnull']
    exact ⟨fun e => by omega, fun e => absurd (e ▸ hv) hv'⟩
  · dsimp only; rw [if_neg hR, if_pos hR', hnull']
    exact ⟨fun e => by omega, fun e => absurd hv' (e ▸ hv)⟩
  · dsimp only; rw [if_neg hR, if_neg hR']
    exact ⟨fun e => toI _ _ (Int64.toInt_inj.1 (by omega)), fun e => by rw [e]⟩

end LeetQ.Rel.Verb
