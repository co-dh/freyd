import LeetQ.Rel.SpecStruct
import LeetQ.Rel.SpecScan
import LeetQ.Rel.QSort

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
theorem bound_overList (op : Kernel.Coc.Over) (c : Nat × Enc) {ws : List UInt64} {x : Int64}
    (hw : longWords c.1 c.2 = some ws) (hn : ws.length < USize.size)
    (hf : (match c.2 with
      | .bytes b => some (Kernel.overBytes op Kernel.Ew.i64 Alg.nul b)
      | .foR .. => Kernel.overFoR op .long c.1 c.2
      | _ => none) = some x) :
    ∃ s L, x = Verify.overList op Alg.nul s L ∧ ∀ u ∈ ws, u.toInt64 ∈ L := by
  obtain ⟨n, e⟩ := c
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
theorem rangeOffsets_long {cl cr : Nat × Enc} {total : Nat} {os : Array Alg.Code} {wl wr : List UInt64}
    (hwl : longWords cl.1 cl.2 = some wl) (hwr : longWords cr.1 cr.2 = some wr) (hl : wl.length < USize.size)
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
  obtain ⟨l1, l2, rfl, hl1, hl2⟩ := mapM_pair_P (fun c x => ∀ ws, longWords c.1 c.2 = some ws → ws.length < USize.size →
      ∃ s L, x = Verify.overList .lesser Alg.nul s L ∧ ∀ u ∈ ws, u.toInt64 ∈ L)
    (fun c x hf ws hw hn => bound_overList .lesser c hw hn hf) hlos
  obtain ⟨g1, g2, rfl, hg1, hg2⟩ := mapM_pair_P (fun c x => ∀ ws, longWords c.1 c.2 = some ws → ws.length < USize.size →
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
  obtain ⟨r1, r2, rfl, hp1, hp2⟩ := mapM_pair_P (fun c r => ∀ code, r = .ok code → ∀ ws, longWords c.1 c.2 = some ws →
      ws.length < USize.size → code.w = 8 * k.width ∧ code.n = ws.length ∧ code.b.size = k.width * ws.length ∧
      ∀ i (hi : i < ws.length), Column.bitsAt code.b (i * k.width) k.width =
        (if Kernel.Ew.intStep Kernel.Ew.add Alg.nul ws[i].toInt64 (-base) = Int64.minValue then (card - 1).toUSize.toNat
          else (Kernel.Ew.intStep Kernel.Ew.add Alg.nul ws[i].toInt64 (-base)).toInt.toNat).toUInt64 ∧
        (Kernel.Ew.intStep Kernel.Ew.add Alg.nul ws[i].toInt64 (-base) ≠ Int64.minValue →
          0 ≤ (Kernel.Ew.intStep Kernel.Ew.add Alg.nul ws[i].toInt64 (-base)).toInt ∧
          (Kernel.Ew.intStep Kernel.Ew.add Alg.nul ws[i].toInt64 (-base)).toInt.toNat < card.toUSize.toNat))
    (fun c r hf code hcode ws hw hn => by
      obtain ⟨n, e⟩ := c
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
theorem keyCodes_long {verb : String} {cl cr : Nat × Enc} {lc rc : Alg.Code} {wl wr : List UInt64}
    (hwl : longWords cl.1 cl.2 = some wl) (hwr : longWords cr.1 cr.2 = some wr) (hl : wl.length < USize.size)
    (hr : wr.length < USize.size) (htot : cl.1 + cr.1 ≤ 2 ^ 32)
    (hR : Alg.rangeOffsets .long #[cl, cr] (cl.1 + cr.1) ≠ .ok none)
    (hc : Struct.keyCodes verb #[⟨.long, cl⟩] #[⟨.long, cr⟩] = .ok (lc, rc)) :
    ∃ k : Kernel.Scan.Kind, (k = .u8 ∨ k = .i16 ∨ k = .i32 ∨ k = .i64) ∧ lc.kind = some k ∧ rc.kind = some k ∧
      rc.n ≤ k.avail rc.b ∧ rc.n = wr.length ∧ rc.b.size = k.width * wr.length ∧ lc.n = wl.length ∧
      lc.b.size / k.width = wl.length ∧
      ∀ i (hi : i < wl.length) j (hj : j < wr.length), (k.bitsAt rc.b j = k.bitsAt lc.b i ↔ wr[j] = wl[i]) := by
  obtain ⟨os, hro, h2⟩ : ∃ os, Alg.rangeOffsets .long #[cl, cr] (cl.1 + cr.1) = .ok (some os) ∧
      Alg.two os = .ok (lc, rc) := by
    unfold Struct.keyCodes Alg.codes at hc
    rcases hro : Alg.rangeOffsets .long #[cl, cr] (cl.1 + cr.1) with err | _ | os
    all_goals
      obtain ⟨n1, e1⟩ := cl
      obtain ⟨n2, e2⟩ := cr
      dsimp only at hro
      cases e1 <;> simp [longWords] at hwl <;> cases e2 <;> simp [longWords] at hwr <;>
        simp [bind, Except.bind, pure, Except.pure, Functor.map, Except.map, Array.mapM_eq_mapM_toList,
          Alg.tuples, hro] at hc hR ⊢
    all_goals exact hc
  obtain ⟨k, f, hk4, hf, lc', rc', rfl, hlk, hln, hls, hlb, hrk, hrn, hrs, hrb⟩ :=
    rangeOffsets_long hwl hwr hl hr htot hro
  have e2 : (lc', rc') = (lc, rc) := by simpa [Alg.two, pure, Except.pure] using h2
  cases e2
  have hw0 : 0 < k.width := by rcases hk4 with rfl | rfl | rfl | rfl <;> decide
  refine ⟨k, hk4, hlk, hrk, ?_, hrn, hrs, hln, by rw [hls, Nat.mul_div_cancel_left _ hw0], fun i hi j hj => ?_⟩
  · rcases hk4 with rfl | rfl | rfl | rfl <;>
      simp only [Kernel.Scan.Kind.avail, hrs, hrn, Nat.mul_div_cancel_left _ hw0, Nat.le_refl]
  · rw [hrb j hj, hlb i hi]
    exact hf _ (List.mem_append_right _ (List.getElem_mem hj)) _ (List.mem_append_left _ (List.getElem_mem hi))

/-- `ej` on one dense long key column per side, unconditionally on the codes: its relation is the
key join `(ix tl)(ix tr)°` read at the row ids, wherever `rangeOffsets` codes the two columns. -/
theorem ej_long {cl cr : Nat × Enc} {wl wr : List UInt64} {R : Rel .long .long}
    (hwl : longWords cl.1 cl.2 = some wl) (hwr : longWords cr.1 cr.2 = some wr) (htot : cl.1 + cr.1 ≤ 2 ^ 32)
    (hro : Alg.rangeOffsets .long #[cl, cr] (cl.1 + cr.1) ≠ .ok none)
    (hU : wl.length * wr.length + wl.length + wr.length + wr.length + 1 < USize.size)
    (hB : wl.length * wr.length + wl.length + wr.length + wr.length < 2 ^ 63)
    (h : Struct.ej #[⟨.long, cl⟩] #[⟨.long, cr⟩] = .ok R) :
    (R.Holds : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) =
      (graph Int64.ofNat : Idx ⟶ (⟨Int64⟩ : RelSet.{0}))° ≫ ix (wl.map (fun u => [u.toInt64])) ≫
        (ix (wr.map (fun u => [u.toInt64])))° ≫ graph Int64.ofNat := by
  rcases hc : Struct.keyCodes "ej" #[⟨.long, cl⟩] #[⟨.long, cr⟩] with err | ⟨lc, rc⟩
  · simp [Struct.ej, hc, bind, Except.bind] at h
  obtain ⟨k, hk4, hlk, hrk, hav, hrn, -, -, hnl, hkey⟩ :=
    keyCodes_long hwl hwr (by omega) (by omega) htot hro hc
  refine ej_rel_lane hk4 hc hrk hlk hav (by simp [hrn]) (by simp [hnl]) (fun i hi j hj => ?_)
    (by simp only [List.length_map, hrn]; exact hU) (by simp only [List.length_map, hrn]; exact hB) h
  simp only [List.length_map] at hi hj
  rw [hkey i hi j hj, getElem!_pos _ _ (by simpa using hj), getElem!_pos _ _ (by simpa using hi)]
  simp only [List.getElem_map, List.cons.injEq, and_true]
  refine ⟨fun e => by rw [e], fun e => ?_⟩
  have := congrArg Int64.toUInt64 e; simpa using this

/-- `ij` on one dense long key column per side, unconditionally on the codes: each left row with its first right
row of an equal key, `Λ((ix tl)(ix tr)°) ≫ est(≤)` read at the row ids, wherever `rangeOffsets` codes the two
columns — `ij_rel_codes` at the one byte lane `keyCodes_long` names. -/
theorem ij_long {cl cr : Nat × Enc} {wl wr : List UInt64} {R : Rel .long .long}
    (hwl : longWords cl.1 cl.2 = some wl) (hwr : longWords cr.1 cr.2 = some wr) (htot : cl.1 + cr.1 ≤ 2 ^ 32)
    (hro : Alg.rangeOffsets .long #[cl, cr] (cl.1 + cr.1) ≠ .ok none)
    (hU : 64 * wr.length < USize.size) (hLU : wl.length < USize.size) (hB : 64 * wr.length < 2 ^ 63)
    (h : Struct.ij #[⟨.long, cl⟩] #[⟨.long, cr⟩] = .ok R) :
    (R.Holds : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) =
      (graph Int64.ofNat : Idx ⟶ (⟨Int64⟩ : RelSet.{0}))° ≫
        (Λ (ix (wl.map (fun u => [u.toInt64])) ≫ (ix (wr.map (fun u => [u.toInt64])))°) ≫ est (· ≤ ·)) ≫
        graph Int64.ofNat := by
  rcases hc : Struct.keyCodes "ij" #[⟨.long, cl⟩] #[⟨.long, cr⟩] with err | ⟨lc, rc⟩
  · simp [Struct.ij, hc, bind, Except.bind] at h
  obtain ⟨k, hk4, hlk, hrk, hav, hrn, hrs, hln, hnl, hkey⟩ :=
    keyCodes_long hwl hwr hLU (by omega) htot hro hc
  have hrw := w_of_kind hk4 hrk
  have hlw := w_of_kind hk4 hlk
  have hlane : 8 * k.width = 8 ∨ 8 * k.width = 16 ∨ 8 * k.width = 32 ∨ 8 * k.width = 64 := by
    rcases hk4 with rfl | rfl | rfl | rfl <;> decide
  have hdiv : ∀ s, (s * 8 / (8 * k.width) : Nat) = s / k.width := fun s => by
    rw [Nat.mul_comm s 8, Nat.mul_div_mul_left _ _ (by decide)]
  have hava : k.avail rc.b = rc.b.size / k.width := by rcases hk4 with rfl | rfl | rfl | rfl <;> rfl
  have hsz8 : rc.b.size * 8 ≤ 64 * wr.length := by
    rw [hrs]; rcases hk4 with rfl | rfl | rfl | rfl <;> (dsimp only [Kernel.Scan.Kind.width]; omega)
  refine ij_rel_codes hc (by rw [hrw]; omega) (by rw [hlw]; omega) (by rw [hrw, hdiv, ← hava]; exact hav)
    (Nat.le_of_eq (by rw [hlw, hdiv, hnl, hln])) (by simp [hrn]) (by simp [hln]) (fun i hi j hj => ?_)
    (by omega) (by simpa using hLU) (by omega) h
  simp only [List.length_map] at hi hj
  rw [hrw, hlw, idAt_kind hk4, idAt_kind hk4, UInt64.toNat_inj, hkey i hi j hj,
    getElem!_pos _ _ (by simpa using hj), getElem!_pos _ _ (by simpa using hi)]
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
theorem groupEdge_long (gs : Eval.Groups) (ids rc nc : Nat × Enc) (nr : Nat) {hay keys gids : ByteArray}
    (hrb : Enc.bytesOf .long rc.1 rc.2 = some hay) (hkb : Enc.bytesOf .long nc.1 nc.2 = some keys)
    (hgb : Enc.bytesOf .long ids.1 ids.2 = some gids) (hsz : keys.size / 8 = gids.size / 8) :
    Eval.groupEdge gs ids (.vector .long rc.1 rc.2 none) (.vector .long nc.1 nc.2 none) nr =
      (ids.1, .bytes (Kernel.binRows 8 false true false hay keys gs.rows (Kernel.longBytes gs.bounds) gids
        nr.toUInt64)) := by
  obtain ⟨n, e⟩ := rc
  obtain ⟨m, f⟩ := nc
  have h1 : (QValue.vector .long n e none).bare = .vector .long n e none := rfl
  have h2 : (QValue.vector .long m f none).bare = .vector .long m f none := rfl
  dsimp only at hrb hkb
  unfold Eval.groupEdge
  simp only [h1, h2, Kernel.denseWidth, QAtomicType.width, hkb, hgb, hsz, bne_self_eq_false,
    beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, bind, Option.bind, Kernel.foldsZero, Kernel.ordSigned]
  cases e with
  | foR md pk =>
    have hd : Kernel.Coc.decode (USize.ofNat 8) md pk (USize.ofNat n) = hay := by
      simpa [Enc.bytesOf, QAtomicType.width] using hrb
    by_cases hm : md.isEmpty = true
    · simp [Kernel.foRColumn, hm, hrb] <;> rfl
    · simp [Kernel.foRColumn, hm, Kernel.foRBinRows, Column.encodes, ← hd] <;> rfl
  | _ => simp [Kernel.foRColumn, hrb] <;> rfl

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

/-- **What `keyMatch` must answer for a key join**: `ids` is a long payload with a word per left key, and
    word `i` names a group whose span (`bounds` read as longs, rows through `rows` or the position itself) lists
    `Struct.group rk lk[i]`, or names no group where that is empty; and `gs.firsts` gathered at the ids (`0`
    past them) is word `i` the head of that group, `0` where it is empty — `wj`'s start. -/
def KeyAnswers {κ : Type} [BEq κ] [Inhabited κ] (rk lk : List κ) (gs : Eval.Groups) (ids : Nat × Enc) : Prop :=
  ∃ gids, Enc.bytesOf .long ids.1 ids.2 = some gids ∧ gids.size / 8 = lk.length ∧
    nats (Alg.gather 8 (Kernel.longBytes (gs.firsts.push 0)) gids) =
      (List.range lk.length).map (fun i => (Struct.group rk lk[i]!).head?.getD 0) ∧ ∀ i, i < lk.length →
    (Kernel.longBytes gs.bounds).size / 8 - 1 ≤ (Column.bitsAt gids (i * 8) 8).toNat ∧
        Struct.group rk lk[i]! = [] ∨
      (Column.bitsAt gids (i * 8) 8).toNat < (Kernel.longBytes gs.bounds).size / 8 - 1 ∧
        (Struct.group rk lk[i]!).length =
          (Column.bitsAt (Kernel.longBytes gs.bounds) ((Column.bitsAt gids (i * 8) 8).toNat * 8 + 8) 8).toNat -
          (Column.bitsAt (Kernel.longBytes gs.bounds) ((Column.bitsAt gids (i * 8) 8).toNat * 8) 8).toNat ∧
        ∀ p, p < (Struct.group rk lk[i]!).length → (Struct.group rk lk[i]!)[p]! =
          let lo := (Column.bitsAt (Kernel.longBytes gs.bounds) ((Column.bitsAt gids (i * 8) 8).toNat * 8) 8).toNat
          if gs.rows.isEmpty then lo + p else (Column.bitsAt gs.rows ((lo + p) * 8) 8).toNat

/-- **`binRows` over answered key groups is `binSpec` in each left row's group**: word `i` is the right row
    `binSpec` names among the rows of left key `i`, the miss `nr` where it names none. -/
theorem binRows_group {κ : Type} [BEq κ] [Inhabited κ] {rk lk : List κ} {gs : Eval.Groups} {ids : Nat × Enc}
    {keys hay gids : ByteArray} {nr : Nat} (hk : KeyAnswers rk lk gs ids) (hgb : Enc.bytesOf .long ids.1 ids.2 = some gids)
    (hkn : keys.size / 8 = lk.length) (hrn : hay.size / 8 = nr) (hrk : rk.length = nr) {i : Nat} (hi : i < lk.length) :
    Column.bitsAt (Kernel.binRows 8 false true false hay keys gs.rows (Kernel.longBytes gs.bounds) gids nr.toUInt64)
        (8 * i) 8 =
      ((Struct.binSpec ((nats hay).map Int64.ofNat) (Struct.group rk lk[i]!)
        (Column.bitsAt keys (i * 8) 8).toInt64).map Nat.toUInt64).getD nr.toUInt64 := by
  obtain ⟨g', hg', hgn, -, hgrp⟩ := hk
  rw [Option.some.inj (hg'.symm.trans hgb)] at hgn hgrp
  have h8 : (8 : USize).toNat = 8 := by simp
  have hG : ∀ p, p < (Struct.group rk lk[i]!).length → (Struct.group rk lk[i]!)[p]! < nr := fun p hp => by
    rw [getElem!_pos _ p hp]
    have := List.mem_range.1 (List.mem_filter.1 (List.getElem_mem hp)).1
    omega
  rcases hgrp i hi with ⟨hng, hG0⟩ | ⟨hng, hlen, hrow⟩
  · rw [bitsAt_binRows_miss 8 false true false hay keys gs.rows _ gids _ (by simp; omega) rfl hng, hG0]
    simp [Struct.binSpec] <;> rfl
  · rw [bitsAt_binRows 8 false true false hay keys gs.rows _ gids _ (by simp; omega) (by omega) rfl hng rfl rfl
      ((nats hay).map Int64.ofNat) _ (Column.bitsAt keys (i * 8) 8).toInt64 hlen hrow fun p hp => by
        have hr := hrow p hp
        unfold binTest
        simp only [h8, Bool.false_eq_true, ↓reduceIte]
        rw [← hr, get!_map _ _ (by rw [nats_length]; have := hG p hp; omega), nats_get _ (by have := hG p hp; omega),
          ← toInt64_eq_ofNat]
        simp only [ordKey8_le]]

/-- **`aj` is `ajSpec` once its groups are known.** Where `keyGroups` answers groups `gs` and ids that
    `KeyAnswers` the two sides' keys, `aj` over dense long times `keys`, `hay` answers `ajSpec`. Nothing is
    assumed about the times' order inside a group. -/
theorem aj_groups {κ : Type} [BEq κ] [Inhabited κ] {l r : Array Struct.KCol} {tl tr : Nat × Enc} {m : Nat}
    {A : Arr .long m} {gs : Eval.Groups} {ids : Nat × Enc} {keys hay gids : ByteArray} (lk rk : List κ)
    (hkb : Enc.bytesOf .long tl.1 tl.2 = some keys)
    (hrb : Enc.bytesOf .long tr.1 tr.2 = some hay) (hgb : Enc.bytesOf .long ids.1 ids.2 = some gids)
    (hkn : keys.size / 8 = tl.1) (hrn : hay.size / 8 = tr.1)
    (hlk : lk.length = tl.1) (hrk : rk.length = tr.1) (hU : tl.1 < USize.size) (h63 : tr.1 < 2 ^ 63)
    (hkg : Struct.keyGroups "aj" l r tl.1 tr.1 = .ok (gs, ids)) (hk : KeyAnswers rk lk gs ids)
    (h : Struct.aj l r ⟨.long, tl⟩ ⟨.long, tr⟩ = .ok ⟨m, A⟩) :
    A.toList = Struct.ajSpec lk ((nats keys).map Int64.ofNat) rk ((nats hay).map Int64.ofNat) := by
  obtain ⟨g', hg', hgn, -⟩ := id hk
  rw [Option.some.inj (hg'.symm.trans hgb)] at hgn
  have hE := groupEdge_long gs ids tr tl tr.1 hrb hkb hgb (by omega)
  simp only [Struct.aj, Struct.colRows, Struct.colValue, hkg, hE, Find.dense, Enc.bytesOf,
    beq_self_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  rename_i A' hA
  simp only [Except.ok.injEq, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  obtain rfl := eq_of_heq h
  have hc := ofPart_enc hA
  rw [Arr.toList_long_bytes _ (by rw [hc]; rfl)]
  -- `^`'s word `i`: the atom where the word is the null `nr`, the word otherwise
  have hfill : ∀ (nul x y : Int64), Kernel.Ew.intStep Kernel.Ew.fill nul x y = if y == nul then x else y :=
    fun _ _ _ => rfl
  have key : ∀ (nul : Int64) (c : UInt64) (b : ByteArray) (i : Nat), i < tl.1 →
      Column.bitsAt (Kernel.Ew.val Kernel.Ew.fill Kernel.Ew.i64 Kernel.Ew.av nul (Find.one c) b tl.1.toUSize)
        (i * 8) 8 = (Kernel.Ew.intStep Kernel.Ew.fill nul c.toInt64 (Column.bitsAt b (i * 8) 8).toInt64).toUInt64 := by
    intro nul c b i hi
    have hv := val_i64_av Kernel.Ew.fill nul c b tl.1 hU
    have hl := congrArg List.length hv
    simp only [Verify.elemsW, List.length_map, List.length_range] at hl
    have := congrArg (fun L => L[i]?) hv
    simp only [Verify.elemsW, List.getElem?_map, List.getElem?_range, hl, hi, Option.map_some,
      Option.some.injEq] at this
    exact this
  have hnr : (UInt64.ofNat tr.1).toInt64 = Int64.ofNat tr.1 := by
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
  rw [hx, ← toInt64_eq_ofNat, ← getElem!_pos lk i (by omega), binRows_group hk hgb (by omega) hrn hrk (by omega)]
  cases hb : Struct.binSpec ((nats hay).map Int64.ofNat) (Struct.group rk lk[i]!) (Column.bitsAt keys (i * 8) 8).toInt64 with
    | none => simp [hfill, Nat.toUInt64_eq, hnr]
    | some r =>
      have hrn : r < tr.1 := by
        have := binSpec_mem hb
        simp only [Struct.group, List.mem_filter, List.mem_range] at this
        omega
      have hr' : (UInt64.ofNat r).toInt64 = Int64.ofNat r := by
        rw [toInt64_eq_ofNat, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      have hne : (UInt64.ofNat r).toInt64 ≠ Int64.ofNat tr.1 := fun e => by
        rw [← hnr] at e
        have := congrArg Int64.toInt e
        rw [toInt_word (u := UInt64.ofNat r) (a := r) (by rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)])
          (by omega), toInt_word (u := UInt64.ofNat tr.1) (a := tr.1)
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
    gs.bounds.toList = (List.range (bs.length + 1)).map (fun k => ((bs.map List.length).take k).sum) ∧
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
  refine ⟨hB, by omega, fun g hg => ⟨hat g (by omega), ?_, fun p hp => ?_⟩⟩
  · rw [show g * 8 + 8 = (g + 1) * 8 by omega, hat (g + 1) (by omega), List.take_succ, List.sum_append_nat]
    simp [List.getElem?_map, List.getElem?_eq_getElem hg]
  · obtain ⟨hq, hr⟩ := hrow g hg p hp
    rw [getElem!_pos _ p hp, ← hr]
    rcases hcases with ⟨he, hid⟩ | he <;> rw [he]
    · rw [if_pos (by simp [ByteArray.isEmpty]), Verify.ids_get hI hq, hid _ hq]
    · have hne : (Kernel.Order.indices bs.flatten).isEmpty = false := by
        simp only [ByteArray.isEmpty, beq_eq_false_iff_ne]; omega
      simp only [hne, Bool.false_eq_true, ↓reduceIte]

/-- **`Groups.firsts` over buckets laid end to end is each bucket's first row**, no bucket being empty. -/
theorem firsts_of_buckets (bs : List (List Nat)) (h63 : ∀ r ∈ bs.flatten, r < 2 ^ 63)
    (hU : bs.flatten.length < USize.size) (hne : ∀ b ∈ bs, b ≠ []) {gs : Eval.Groups}
    (hgs : gs = Eval.Groups.of (Kernel.Order.indices bs.flatten)
      ((Kernel.Order.bounds (bs.map List.length)).map (· / 8))) :
    gs.firsts.toList = bs.map fun b => b.head?.getD 0 := by
  obtain ⟨hB, -, hspan⟩ := groups_of_buckets bs h63 hU hgs
  have hsz : gs.bounds.size = bs.length + 1 := by rw [← Array.length_toList, hB]; simp
  unfold Eval.Groups.firsts
  apply List.ext_getElem (by simp [hsz])
  intro g h1 h2
  simp only [List.length_map] at h2
  simp only [Array.toList_map, Array.toList_range, List.getElem_map, List.getElem_range]
  have hb : gs.bounds[g]? = some ((bs.map List.length).take g).sum := by
    rw [← Array.getElem?_toList, hB, List.getElem?_map, List.getElem?_range (by omega)]; rfl
  obtain ⟨-, -, hrow⟩ := hspan g h2
  have hn := hne _ (List.getElem_mem h2)
  have hp := hrow 0 (List.length_pos_iff.2 hn)
  rw [Nat.add_zero] at hp
  simp only [Eval.Groups.span, Eval.Groups.row, hb, Option.getD_some]
  rw [← hp]
  generalize bs[g] = l at hn ⊢
  cases l with
  | nil => exact absurd rfl hn
  | cons a l => simp

open QLean.Kernel in
/-- **`groupColumn` at a long column is `Order.group` over its words**, laid out in bytes `B` — the column's
    own, or its frame-of-reference decode. -/
theorem groupColumn_long {n : Nat} {e : Enc} {ws : List UInt64} (hw : longWords n e = some ws)
    (hn : ws.length = n) (hU : n < USize.size) :
    ∃ B, Verify.elemsW 8 B = ws ∧ B.size / 8 = n ∧ groupColumn .long n e =
      some (.dict (.vector .long ((Order.group .i64 n.toUSize B).1.size / 8)
          (.bytes (Order.group .i64 n.toUSize B).1) none)
        (.slices .long ((Order.group .i64 n.toUSize B).2.1.size / 8)
          (.bytes (Order.group .i64 n.toUSize B).2.1) none (Order.group .i64 n.toUSize B).2.2) false) := by
  cases e with
  | bytes b =>
    simp only [longWords, Option.some.injEq] at hw
    have hs : b.size / 8 = n := by rw [← hn, ← hw]; simp [Verify.elemsW]
    refine ⟨b, hw, hs, ?_⟩
    simp [groupColumn, orderKind, Enc.bytesOf, hs, Scan.Kind.width]
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
theorem keyColumns_long (cr cl : Nat × Enc) (a a' : Option (UInt8 × IndexCell)) :
    Eval.keyColumns #[.vector .long cr.1 cr.2 a] #[.vector .long cl.1 cl.2 a'] =
      some (.long, cr, .vector .long cl.1 cl.2 none) := by
  obtain ⟨n, e⟩ := cr
  obtain ⟨n', e'⟩ := cl
  -- `Array.mapM` and `Array.zip` recurse well-founded, so the literals are read through their lists
  rcases a with _ | ⟨_, _⟩ <;> rcases a' with _ | ⟨_, _⟩ <;>
    (unfold Eval.keyColumns; rw [Array.mapM_eq_mapM_toList, Array.toList_zip]; rfl)


open QLean.Kernel in
/-- `runsColumn` at a long column is `runStarts` over its bytes: the column's own, or its decode. -/
theorem runsColumn_long (n : Nat) (e : Enc) :
    runsColumn .long n e = (Enc.bytesOf .long n e).map (runStarts 8 false) := by
  cases e with
  | foR md pk =>
    simp only [runsColumn, denseWidth, foRColumn, QAtomicType.width]
    split <;> simp_all [Enc.bytesOf, foRRunStarts, QAtomicType.width, foldsZero] <;> (subst_vars; rfl)
  | _ => simp [runsColumn, denseWidth, foRColumn, QAtomicType.width, foldsZero] <;> rfl

open QLean.Kernel in
/-- **`runStarts` read back as row numbers**: the positions that start a run of equal words, then the count. -/
theorem longRows_runStarts (B : ByteArray) (h63 : B.size / 8 < 2 ^ 63) :
    (longRows (runStarts 8 false B)).toList =
      (List.range (B.size / 8)).filter (fun i => i == 0 || Column.bitsAt B (i * 8) 8 != Column.bitsAt B ((i - 1) * 8) 8)
        ++ [B.size / 8] := by
  have h8 : (8 : USize).toNat = 8 := by simp
  have hf : ∀ (l : List Nat) (acc : ByteArray),
      l.foldl (fun acc i => if (i == 0 || key 8 false B i != key 8 false B (i - 1)) = true
        then Column.pushBits acc i.toUInt64 8 else acc) acc =
      (l.filter fun i => i == 0 || Column.bitsAt B (i * 8) 8 != Column.bitsAt B ((i - 1) * 8) 8).foldl
        (fun acc i => Column.pushBits acc i.toUInt64 8) acc := by
    intro l; induction l with
    | nil => intro _; rfl
    | cons a l ih =>
      intro acc
      simp only [List.foldl_cons, List.filter_cons]
      cases h : (a == 0 || Column.bitsAt B (a * 8) 8 != Column.bitsAt B ((a - 1) * 8) 8) <;>
        simp only [show ∀ i, Kernel.key 8 false B i = Column.bitsAt B (i * 8) 8 from fun _ => rfl, h, ite_true,
          Bool.false_eq_true, ite_false, List.foldl_cons] <;> exact ih _
  generalize hL : (List.range (B.size / 8)).filter
    (fun i => i == 0 || Column.bitsAt B (i * 8) 8 != Column.bitsAt B ((i - 1) * 8) 8) = L at hf ⊢
  have e : runStarts 8 false B = (L ++ [B.size / 8]).foldl (fun acc i => Column.pushBits acc i.toUInt64 8)
      ByteArray.empty := by
    simp only [runStarts, h8]; rw [List.foldl_append, ← hL, ← hf]; rfl
  have hle : ∀ x ∈ L ++ [B.size / 8], x ≤ B.size / 8 := fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · rw [← hL] at hx; exact Nat.le_of_lt (List.mem_range.1 (List.mem_filter.1 hx).1)
    · simp at hx; omega
  obtain ⟨hs, -, hb⟩ := Verify.foldl_pushBits Nat.toUInt64 8 (by decide) (L ++ [B.size / 8]) ByteArray.empty
  rw [e]
  apply List.ext_getElem (by
    simp only [longRows, Array.toList_map, Array.toList_range, List.length_map, List.length_range]; rw [hs]; simp)
  intro i h1 h2
  simp only [longRows, Array.toList_map, Array.toList_range, List.getElem_map, List.getElem_range]
  have := hb i h2
  simp only [ByteArray.size_empty, Nat.zero_add] at this
  have hle2 := hle _ (List.getElem_mem h2)
  have hx : (L ++ [B.size / 8])[i] < 2 ^ 64 := by omega
  have hx' : (L ++ [B.size / 8])[i] < 2 ^ (8 * 8) := hx
  rw [this, show (L ++ [B.size / 8])[i].toUInt64 = UInt64.ofNat (L ++ [B.size / 8])[i] from rfl,
    UInt64.toNat_ofNat_of_lt' hx, Nat.mod_eq_of_lt hx', UInt64.toNat_ofNat_of_lt' hx]

/-- **Each of the `n` words `w` occupies one run**: two equal words have only that word between them — what a
    sorted column gives (`s#`), and what `u#`/`p#` claim. -/
def OneRun (w : Nat → UInt64) (n : Nat) : Prop := ∀ i j k, i ≤ k → k ≤ j → j < n → w i = w j → w k = w i

open QLean.Kernel in
/-- **Where each word occupies one run, the first occurrences are the run starts.** -/
theorem firstsOf_runs {B : ByteArray} (hB : OneRun (fun i => Column.bitsAt B (i * 8) 8) (B.size / 8)) :
    Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8) =
      (List.range (B.size / 8)).filter (fun i => i == 0 || Column.bitsAt B (i * 8) 8 != Column.bitsAt B ((i - 1) * 8) 8) := by
  unfold Verify.firstsOf
  apply List.filter_congr
  intro i hi
  have hi := List.mem_range.1 hi
  have hkey : ∀ j, Order.keyAt .i64 B j = Order.keyAt .i64 B i ↔
      Column.bitsAt B (j * 8) 8 = Column.bitsAt B (i * 8) 8 := fun j => Verify.keyAt_eq_iff (by simp) B j i
  have L : ((List.range i).all fun j => !decide (Order.keyAt .i64 B j = Order.keyAt .i64 B i)) = true ↔
      ∀ j, j < i → Column.bitsAt B (j * 8) 8 ≠ Column.bitsAt B (i * 8) 8 := by simp [List.all_eq_true, hkey]
  have R : (i == 0 || Column.bitsAt B (i * 8) 8 != Column.bitsAt B ((i - 1) * 8) 8) = true ↔
      i = 0 ∨ Column.bitsAt B (i * 8) 8 ≠ Column.bitsAt B ((i - 1) * 8) 8 := by simp
  rw [Bool.eq_iff_iff, L, R]
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · exact Or.inl h0
    · exact Or.inr fun e => h (i - 1) (by omega) e.symm
  · rintro (h0 | hne) j hj e
    · omega
    · exact hne ((hB j i (i - 1) (by omega) (by omega) hi e).trans e).symm

/-- The numbers below `n` in `[a, b)` are `range' a`, cut at `n`. -/
theorem filter_range_interval (a b : Nat) : ∀ n,
    (List.range n).filter (fun i => decide (a ≤ i ∧ i < b)) = List.range' a (min b n - a) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, ih]
    by_cases h : a ≤ n ∧ n < b
    · rw [show min b (n + 1) - a = (min b n - a) + 1 by omega, List.range'_concat]
      simp [List.filter_cons, h]; omega
    · rw [show min b (n + 1) - a = min b n - a by omega]
      simp <;> omega

/-- Below the end of a run, a word equals the run's first exactly when no run starts in between. -/
theorem same_run {B : ByteArray} (hB : OneRun (fun i => Column.bitsAt B (i * 8) 8) (B.size / 8)) {a i : Nat} (hai : a ≤ i) (hi : i < B.size / 8) :
    Column.bitsAt B (i * 8) 8 = Column.bitsAt B (a * 8) 8 ↔
      ∀ r, a < r → r ≤ i → Column.bitsAt B (r * 8) 8 = Column.bitsAt B ((r - 1) * 8) 8 := by
  constructor
  · intro e r h1 h2
    rw [show Column.bitsAt B (r * 8) 8 = Column.bitsAt B (a * 8) 8 from hB a i r (by omega) h2 hi e.symm,
      show Column.bitsAt B ((r - 1) * 8) 8 = Column.bitsAt B (a * 8) 8 from hB a i (r - 1) (by omega) (by omega) hi e.symm]
  · intro h
    obtain ⟨d, rfl⟩ : ∃ d, i = a + d := ⟨i - a, by omega⟩
    clear hai
    induction d with
    | zero => rfl
    | succ d ih =>
      rw [h (a + (d + 1)) (by omega) (Nat.le_refl _), show a + (d + 1) - 1 = a + d by omega]
      exact ih (by omega) fun r h1 h2 => h r h1 (by omega)

open QLean.Kernel in
/-- **Where each word occupies one run, the bucket at run start `F[g]` is the run**: the rows from it to the next
    start, or to the count past the last. -/
theorem bucket_run {B : ByteArray} (hB : OneRun (fun i => Column.bitsAt B (i * 8) 8) (B.size / 8)) {F : List Nat}
    (hF : Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8) = F) {g : Nat} (hg : g < F.length) :
    Verify.bucketOf (Order.keyAt .i64 B) (B.size / 8) F[g] =
      List.range' F[g] ((F ++ [B.size / 8])[g + 1]! - F[g]) := by
  have hFs : F.Pairwise (· < ·) := by
    rw [← hF]; unfold Verify.firstsOf; exact (List.pairwise_lt_range ..).filter _
  have hmem : ∀ r, r ∈ F ↔ r < B.size / 8 ∧ (r = 0 ∨ Column.bitsAt B (r * 8) 8 ≠ Column.bitsAt B ((r - 1) * 8) 8) :=
    fun r => by rw [← hF, firstsOf_runs hB, List.mem_filter, List.mem_range]; simp
  have hlt : ∀ i j (hi : i < F.length) (hj : j < F.length), F[i] < F[j] → i < j := fun i j hi hj h =>
    Nat.lt_of_not_le fun hc => by
    rcases Nat.lt_or_eq_of_le hc with hc | rfl
    · have := List.pairwise_iff_getElem.1 hFs j i hj hi hc; omega
    · omega
  have hg0 := (hmem _).1 (List.getElem_mem hg)
  -- `hi` is the next start, or the count
  have hhi : (F ++ [B.size / 8])[g + 1]! = if h : g + 1 < F.length then F[g + 1] else B.size / 8 := by
    split
    · rename_i h; rw [getElem!_pos _ _ (by simp <;> omega), List.getElem_append_left h]
    · rename_i h; rw [getElem!_pos _ _ (by simp <;> omega), List.getElem_append_right (by omega)]; simp <;> omega
  have hgt : F[g] < (F ++ [B.size / 8])[g + 1]! ∧ (F ++ [B.size / 8])[g + 1]! ≤ B.size / 8 := by
    rw [hhi]; split
    · rename_i h
      exact ⟨List.pairwise_iff_getElem.1 hFs g (g + 1) hg h (by omega), Nat.le_of_lt ((hmem _).1 (List.getElem_mem h)).1⟩
    · exact ⟨hg0.1, Nat.le_refl _⟩
  rw [show (F ++ [B.size / 8])[g + 1]! - F[g] = min (F ++ [B.size / 8])[g + 1]! (B.size / 8) - F[g] by
    rw [Nat.min_eq_left hgt.2], ← filter_range_interval]
  unfold Verify.bucketOf
  apply List.filter_congr
  intro i hi
  have hi := List.mem_range.1 hi
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, Verify.keyAt_eq_iff (by simp) B i F[g]]
  change Column.bitsAt B (i * 8) 8 = Column.bitsAt B (F[g] * 8) 8 ↔ _
  by_cases hai : F[g] ≤ i
  · rw [same_run hB hai hi]
    constructor
    · intro h
      refine ⟨hai, Nat.lt_of_not_le fun hge => ?_⟩
      rw [hhi] at hge
      split at hge
      · rename_i h1
        have hs := ((hmem _).1 (List.getElem_mem h1)).2
        have hgt1 := List.pairwise_iff_getElem.1 hFs g (g + 1) hg h1 (by omega)
        rcases hs with hs | hs
        · omega
        · exact hs (h _ hgt1 hge)
      · omega
    · rintro ⟨-, hlt'⟩ r h1 h2
      refine Classical.byContradiction fun hne => ?_
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ((hmem r).2 ⟨by omega, Or.inr hne⟩)
      have hgk := hlt g k hg hk h1
      rw [hhi] at hlt'
      split at hlt'
      · rename_i h1'
        rcases Nat.lt_or_eq_of_le (show g + 1 ≤ k by omega) with h3 | h3
        · have := List.pairwise_iff_getElem.1 hFs (g + 1) k h1' hk h3; omega
        · subst h3; omega
      · omega
  · simp only [hai, false_and, iff_false]
    intro e
    rcases hg0.2 with h0 | hne
    · omega
    · exact hne ((hB i F[g] (F[g] - 1) (by omega) (by omega) hg0.1 e).trans e).symm

/-- The rows in the buckets of any first occurrences are rows of the column. -/
theorem buckets_lt {B : ByteArray} (F : List Nat) :
    ∀ r ∈ (F.map (Verify.bucketOf (Kernel.Order.keyAt .i64 B) (B.size / 8))).flatten, r < B.size / 8 := fun r hr => by
  obtain ⟨l, hl, hrl⟩ := List.mem_flatten.1 hr
  obtain ⟨f, -, rfl⟩ := List.mem_map.1 hl
  exact List.mem_range.1 (List.mem_filter.1 hrl).1

open QLean.Kernel in
/-- **`?` of the left words among the distinct right words answers the key groups** (`keyMatch`'s `ofKey`), on
    whichever path built them: groups `gs` holding each first occurrence's bucket as one span, the bucket's head as
    its `firsts`, and the distinct words `D` in first-occurrence order. -/
theorem ofKey_answers {B D : ByteArray} {k : Nat} {F : List Nat} {cl : Nat × Enc} {wl : List UInt64} {gs : Eval.Groups}
    (hlU : cl.1 < USize.size) (hlwf : Enc.WF .long cl.1 cl.2) (hlR : Find.Readable .long cl.1 cl.2)
    (hwl : longWords cl.1 cl.2 = some wl) (hBU : B.size / 8 < USize.size) (h63 : B.size / 8 < 2 ^ 63)
    (hF : Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8) = F)
    (hD : Verify.elemsW 8 D = F.map fun f => Column.bitsAt B (f * 8) 8) (hDs : D.size = k * 8)
    (hsz : (Kernel.longBytes gs.bounds).size / 8 - 1 = F.length)
    (hspan : ∀ g (hg : g < F.length),
      (Verify.bucketOf (Order.keyAt .i64 B) (B.size / 8) F[g]).length =
        (Column.bitsAt (Kernel.longBytes gs.bounds) (g * 8 + 8) 8).toNat -
          (Column.bitsAt (Kernel.longBytes gs.bounds) (g * 8) 8).toNat ∧
      ∀ p, p < (Verify.bucketOf (Order.keyAt .i64 B) (B.size / 8) F[g]).length →
        (Verify.bucketOf (Order.keyAt .i64 B) (B.size / 8) F[g])[p]! =
          if gs.rows.isEmpty then (Column.bitsAt (Kernel.longBytes gs.bounds) (g * 8) 8).toNat + p
          else (Column.bitsAt gs.rows (((Column.bitsAt (Kernel.longBytes gs.bounds) (g * 8) 8).toNat + p) * 8) 8).toNat)
    (hfi : gs.firsts.toList = (F.map (Verify.bucketOf (Order.keyAt .i64 B) (B.size / 8))).map fun b => b.head?.getD 0) :
    ∃ P, findColumn .long false k (.bytes D) (.vector .long cl.1 cl.2 none) =
        some (.vector .long (P.size / 8) (.bytes P) none) ∧
      KeyAnswers (Verify.elemsW 8 B) wl gs (P.size / 8, .bytes P) := by
  have hk : k = F.length := by
    have := congrArg List.length hD
    simp only [Verify.elemsW, List.length_map, List.length_range] at this; omega
  have hFlen : F.length ≤ B.size / 8 := by
    rw [← hF]; exact Nat.le_trans (List.length_filter_le _ _) (by simp [Verify.firstsOf])
  let kx : Arr .long k := Arr.mk (.bytes D) (by first | exact hDs | (simp [Enc.WF, QAtomicType.width]; omega))
  let ly : Arr .long cl.1 := Arr.mk cl.2 hlwf
  obtain ⟨P, xs, ys, hP, hxs, hys, hmap⟩ := Find.probe_find kx ly trivial hlR (by omega) hlU
  obtain rfl : xs = Verify.elemsW 8 D := (Option.some.inj (show some (Verify.elemsW 8 D) = some xs from hxs)).symm
  have hys' : ys = wl := Option.some.inj ((show longWords cl.1 cl.2 = some ys from hys).symm.trans hwl)
  rw [hys'] at hmap
  have hFc := Find.findColumn_long false k (.bytes D) cl.1 cl.2 none
  have hP' : probeColumns .long 8 false k (.bytes D) cl.1 cl.2 = some P := hP
  simp only [Bool.false_eq_true, false_and, ↓reduceIte, hP', Option.map_some] at hFc
  refine ⟨P, hFc, ?_⟩
  have hbs63 := buckets_lt (B := B) F
  have hPn : P.size / 8 = wl.length := by
    have := congrArg List.length hmap; simpa [Verify.elemsW] using this
  have hPi : ∀ i (hi : i < wl.length), (Column.bitsAt P (i * 8) 8).toNat =
      (F.map fun f => Column.bitsAt B (f * 8) 8).idxOf wl[i] := fun i hi => by
    have := congrArg (·[i]?) hmap
    rw [hD] at this
    simp only [Verify.elemsW, List.map_map, List.getElem?_map, List.getElem?_range (by omega : i < P.size / 8),
      List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq, Function.comp_apply] at this
    exact this
  refine ⟨P, rfl, hPn, ?_, fun i hi => ?_⟩
  · -- the starts: `firsts` is each bucket's head
    rw [nats_gather, nats_eq_ids (Kernel.longBytes _), longBytes_ids _ (by
      rw [Array.toList_push, hfi]
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
        cases b with
        | nil => simp
        | cons a l =>
          have := hbs63 a (List.mem_flatten.2 ⟨_, hb, List.mem_cons_self ..⟩)
          simp only [List.head?_cons, Option.getD_some]; omega
      · simp at hx; omega), Array.toList_push, hfi]
    apply List.ext_getElem (by simp [nats_length, hPn])
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1 h2
    rw [List.getElem_map, List.getElem_map, List.getElem_range, ← getElem!_pos (nats P) i h1,
      nats_get P (by omega), hPi i h2, getElem!_pos wl i h2]
    subst hF
    rcases bucket_idxOf B wl[i] with ⟨hge, hnil⟩ | ⟨hlt', hb⟩
    · rw [hnil, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
      rw [List.getElem?_singleton]; split <;> rfl
    · change Verify.bucketOf _ _ _ = _ at hb
      rw [← hb, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hlt')]
      simp [List.getElem?_map, List.getElem?_eq_getElem hlt']
  rw [getElem!_pos wl i hi, hPi i hi]
  subst hF
  rcases bucket_idxOf B wl[i] with ⟨hge, hnil⟩ | ⟨hlt', hb⟩
  · exact Or.inl ⟨by omega, hnil⟩
  · obtain ⟨hlen, hrow⟩ := hspan _ hlt'
    change Verify.bucketOf _ _ _ = _ at hb
    rw [hb] at hlen hrow
    exact Or.inr ⟨by omega, hlen, fun p hp => hrow p hp⟩

open QLean.Kernel in
/-- **`keyMatch`'s `grouped` path answers the key groups.** A right long key column marked neither `` `s ``,
    `` `u `` nor `` `p ``, and `` `g `` only with no index built (`cell.ready = none`, so `viaIndex` scans), is grouped by `Order.group` and each left word placed among the distinct words
    by `?`; the groups and ids it answers are `KeyAnswers` of the two sides' words, bytes or frame of
    reference alike. -/
theorem keyMatch_grouped {cr cl : Nat × Enc} {ar al : Option (UInt8 × IndexCell)} {wr wl : List UInt64}
    (nr nl : Nat) (hrw : longWords cr.1 cr.2 = some wr) (hrn : wr.length = cr.1) (h63 : cr.1 < 2 ^ 63)
    (hU : cr.1 < USize.size) (hlU : cl.1 < USize.size) (hlwf : Enc.WF .long cl.1 cl.2)
    (hlR : Find.Readable .long cl.1 cl.2) (hwl : longWords cl.1 cl.2 = some wl)
    (hattr : ∀ a cell, ar = some (a, cell) → a ≠ 1 ∧ a ≠ 2 ∧ a ≠ 3 ∧ (a = 4 → cell.ready = none)) :
    KeyAnswers wr wl (Eval.keyMatch #[.vector .long cr.1 cr.2 ar] nr #[.vector .long cl.1 cl.2 al] nl).1
      (Eval.keyMatch #[.vector .long cr.1 cr.2 ar] nr #[.vector .long cl.1 cl.2 al] nl).2 := by
  obtain ⟨B, hBw, hBn, hG⟩ := groupColumn_long hrw hrn hU
  have hm : min cr.1.toUSize.toNat (Scan.Kind.avail .i64 B) = B.size / 8 := by
    rw [USize.toNat_ofNat_of_lt' hU]; simp [Scan.Kind.avail, Scan.Kind.width, hBn]
  have hgroup : Order.group .i64 cr.1.toUSize B = (Order.distinct .i64 cr.1.toUSize B,
      Order.indices ((Order.firsts .i64 (B.size / 8) B).map (Order.bucket .i64 (B.size / 8) B)).flatten,
      Order.bounds (((Order.firsts .i64 (B.size / 8) B).map (Order.bucket .i64 (B.size / 8) B)).map List.length)) := by
    unfold Order.group; dsimp only; rw [hm]
  generalize hF : Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8) = F
  have hbs : (Order.firsts .i64 (B.size / 8) B).map (Order.bucket .i64 (B.size / 8) B) =
      F.map (Verify.bucketOf (Order.keyAt .i64 B) (B.size / 8)) := by rw [← hF]; rfl
  -- the distinct words, as a long column the probe reads
  have hkw : Verify.elemsW 8 (Order.distinct .i64 cr.1.toUSize B) = F.map fun f => Column.bitsAt B (f * 8) 8 := by
    have := Verify.distinct_spec .i64 cr.1.toUSize B
    rw [hm, hF] at this; exact this
  have hks : (Order.distinct .i64 cr.1.toUSize B).size = F.length * 8 := by
    have := congrArg List.length hkw
    simp only [Verify.elemsW, List.length_map, List.length_range] at this
    have h := (Verify.foldl_pushBits (Scan.Kind.bitsAt .i64 B) 8 (by decide)
      (Order.firsts .i64 (min cr.1.toUSize.toNat (Scan.Kind.avail .i64 B)) B) ByteArray.empty).1
    rw [hm, show Order.firsts .i64 (B.size / 8) B = F from hF] at h
    have e : (Order.distinct .i64 cr.1.toUSize B).size = ByteArray.empty.size + 8 * F.length := by
      rw [← h]; unfold Order.distinct; dsimp only; rw [hm, show Order.firsts .i64 (B.size / 8) B = F from hF]; rfl
    rw [e]; simp [Nat.mul_comm]
  have hflat := buckets_length (Order.keyAt .i64 B) (B.size / 8)
  rw [hF] at hflat
  have hbs63 : ∀ r ∈ (F.map (Verify.bucketOf (Order.keyAt .i64 B) (B.size / 8))).flatten, r < B.size / 8 :=
    buckets_lt F
  obtain ⟨-, hsz, hspan⟩ := groups_of_buckets (F.map (Verify.bucketOf (Order.keyAt .i64 B) (B.size / 8)))
    (fun r hr => by have := hbs63 r hr; omega) (by rw [hflat]; omega)
    (gs := Eval.Groups.of (Order.group .i64 cr.1.toUSize B).2.1 ((Order.group .i64 cr.1.toUSize B).2.2.map (· / 8)))
    (by rw [hgroup, hbs])
  have hne : ∀ b ∈ F.map (Verify.bucketOf (Order.keyAt .i64 B) (B.size / 8)), b ≠ [] := fun b hb => by
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hb
    rw [← hF] at hf
    unfold Verify.firstsOf at hf
    have hf' := List.mem_range.1 (List.mem_filter.1 hf).1
    exact List.ne_nil_of_mem (show f ∈ Verify.bucketOf _ _ f from List.mem_filter.2 ⟨List.mem_range.2 hf', by simp⟩)
  have hfi := firsts_of_buckets _ (fun r hr => by have := hbs63 r hr; omega) (by rw [hflat]; omega) hne
    (gs := Eval.Groups.of (Order.group .i64 cr.1.toUSize B).2.1 ((Order.group .i64 cr.1.toUSize B).2.2.map (· / 8)))
    (by rw [hgroup, hbs])
  obtain ⟨P, hFc, hKA⟩ := ofKey_answers (k := (Order.distinct .i64 cr.1.toUSize B).size / 8) hlU hlwf hlR hwl
    (by omega) (by omega) hF hkw (by rw [hks, Nat.mul_div_cancel _ (by decide)])
    (by simpa using hsz) (fun g hg => by
      obtain ⟨hlo, hhi, hrow⟩ := hspan g (by simpa using hg)
      simp only [List.getElem_map] at hlo hhi hrow
      exact ⟨by rw [hhi, hlo]; omega, fun p hp => by rw [hrow p hp, hlo]⟩) hfi
  -- `keyMatch` at an unmarked right column is `grouped`
  have hK : Eval.keyMatch #[.vector .long cr.1 cr.2 ar] nr #[.vector .long cl.1 cl.2 al] nl =
      (Eval.Groups.of (Order.group .i64 cr.1.toUSize B).2.1 ((Order.group .i64 cr.1.toUSize B).2.2.map (· / 8)),
        P.size / 8, .bytes P) := by
    unfold Eval.keyMatch
    rw [keyColumns_long cr cl ar al]
    have hg1 : (Order.group .i64 cr.1.toUSize B).1 = Order.distinct .i64 cr.1.toUSize B := by rw [hgroup]
    simp only [bind, Option.bind, hG, hg1, hFc]
    rcases ar with _ | ⟨a, cell⟩
    · simp [QValue.marking]
    · obtain ⟨h1, h2, h3, h4⟩ := hattr a cell rfl
      by_cases ha : a = 4
      · subst ha; simp [QValue.marking, Eval.viaIndex, h4 rfl]
      · simp [QValue.marking, h1, h2, h3, ha]
  rw [hK, ← hBw]; exact hKA

/-- A long column listing `ws` (`longWords`) hands a kernel a dense payload of those words: itself, or its `foR`
    decoded (`decodeW`). -/
theorem bytesOf_longWords {n : Nat} {e : Enc} {ws : List UInt64} (hn : n < USize.size)
    (h : longWords n e = some ws) (hl : ws.length = n) :
    ∃ B, Enc.bytesOf .long n e = some B ∧ Verify.elemsW 8 B = ws ∧ B.size / 8 = n := by
  have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  unfold longWords at h
  cases hc : e with
  | bytes b =>
    rw [hc] at h; cases h
    exact ⟨b, rfl, rfl, by simpa [Verify.elemsW] using hl⟩
  | foR md pk =>
    rw [hc] at h; cases h
    obtain ⟨hsz, hg⟩ := Verify.decodeW (8 : Nat).toUSize (by rw [h8]; decide) md pk n.toUSize
    rw [h8, USize.toNat_ofNat_of_lt' hn] at hsz hg
    refine ⟨_, by simp only [Enc.bytesOf, QAtomicType.width]; rfl,
      List.ext_getElem (by simp [Verify.elemsW, hsz]) fun i h1 _ => ?_, by rw [hsz]; omega⟩
    simp only [Verify.elemsW, List.getElem_map, List.getElem_range]
    rw [hg i (by simpa [Verify.elemsW, hsz] using h1), Verify.ofNat_toNat_mod64]
  | _ => all_goals (rw [hc] at h; cases h)

open QLean.Kernel in
/-- `gatherColumn` at a long source in bytes or frame of reference answers a vector, at any index it can read. -/
theorem gatherColumn_long_some {n m : Nat} {e ie : Enc} {ws : List UInt64} {ix : ByteArray}
    (hw : longWords n e = some ws) (hi : Enc.bytesOf .long m ie = some ix) (hm : m * 8 ≤ ix.size) :
    ∃ c, gatherColumn .long n e m ie = some c := by
  -- the index first: `gatherColumn` reads it at its own encoding, which `hi` names
  cases ie <;> simp only [Enc.bytesOf, QAtomicType.width, Option.map_some] at hi <;> (try cases hi) <;>
  cases e with
  | bytes b =>
    unfold gatherColumn
    split <;> simp_all [rowWidth, denseWidth, QAtomicType.width, foRColumn, Enc.bytesOf, hm]
  | foR md pk =>
    unfold gatherColumn
    split <;> simp_all [rowWidth, denseWidth, QAtomicType.width, foRColumn, Enc.bytesOf, hm] <;>
      (cases hmd : md.isEmpty <;> simp_all [Column.encodes, hm])
  | _ => simp [longWords] at hw

open QLean.Kernel in
/-- **`ofRuns`' answer is `KeyAnswers`** where each left row `i`'s run is its group: `none` where the group is
    empty, else `(a, z)` with the group the rows `[a, z)`, `ix[a]` a group `g` whose bounds are `a` and `z`. The ids
    are `gid i` or the group count; the groups' rows are their own index (`rows` empty). This is what the `s#`
    halving and the `u#`/`p#` gallop each leave to prove of their runs (`ofRuns` at `key = id`, every needle met). -/
theorem ofRuns_answers {wr wl : List UInt64} {run : Nat → Option (Nat × Nat)} {B : Array Nat}
    {ix : Std.HashMap Nat Nat} (h63 : ∀ x ∈ B.toList, x < 2 ^ 63) (hBU : B.size < 2 ^ 63) (hB0 : 0 < B.size)
    (hrun : ∀ i, i < wl.length → (run i = none ∧ Struct.group wr wl[i]! = []) ∨
      ∃ a z g, run i = some (a, z) ∧ a < z ∧ Struct.group wr wl[i]! = List.range' a (z - a) ∧ ix[a]? = some g ∧
        B[g]? = some a ∧ B[g + 1]? = some z) :
    KeyAnswers wr wl ⟨ByteArray.empty, B⟩
      (Eval.groupIds (B.size - 1) ((Array.range wl.length).map fun i => (run i).bind fun p => ix[p.1]?)) := by
  generalize hH : ((Array.range wl.length).map fun i => (run i).bind fun p => ix[p.1]?).map
    (·.getD (B.size - 1)) = H
  have hids : Eval.groupIds (B.size - 1) ((Array.range wl.length).map fun i => (run i).bind fun p => ix[p.1]?) =
      (H.size, .bytes (Kernel.longBytes H)) := by rw [← hH]; simp only [Eval.groupIds, Array.size_map]
  rw [hids]
  have hHs : H.size = wl.length := by rw [← hH]; simp
  -- each left row's id: its group, or the count where it has none
  have hHi : ∀ i (hi : i < wl.length), H[i]'(by omega) = ((run i).bind fun p => ix[p.1]?).getD (B.size - 1) := by
    intro i hi; subst hH; simp
  have hHg : ∀ i (hi : i < wl.length), H[i]'(by omega) < B.size := by
    intro i hi; rw [hHi i hi]
    rcases hrun i hi with ⟨hn, -⟩ | ⟨a, z, g, hs, -, -, hg, -, hz⟩
    · rw [hn]; show B.size - 1 < B.size; omega
    · rw [hs]; simp only [Option.bind_some, hg, Option.getD_some]
      have := (Array.getElem?_eq_some_iff.1 hz).1; omega
  have hH64 : ∀ x ∈ H.toList, x < 2 ^ 64 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [Array.length_toList] at hi
    have := hHg i (by omega); simp only [Array.getElem_toList]; omega
  have hLH : Verify.ids (Kernel.longBytes H) = H.toList := longBytes_ids H hH64
  have hLB : Verify.ids (Kernel.longBytes B) = B.toList := longBytes_ids B fun x hx => by have := h63 x hx; omega
  have hBn : (Kernel.longBytes B).size / 8 = B.size := by
    have := congrArg List.length hLB; simpa [Verify.ids] using this
  have hatB : ∀ q (hq : q < B.size), (Column.bitsAt (Kernel.longBytes B) (q * 8) 8).toNat = B[q] := fun q hq => by
    rw [Verify.ids_get hLB] <;> simp [hq]
  have hatH : ∀ q (hq : q < H.size), (Column.bitsAt (Kernel.longBytes H) (q * 8) 8).toNat = H[q] := fun q hq => by
    rw [Verify.ids_get hLH] <;> simp [hq]
  have hemp : (ByteArray.empty).isEmpty = true := by simp [ByteArray.isEmpty]
  have hBg : ∀ g : Nat, (B[g]?).getD 0 < 2 ^ 63 := fun g => by
    cases h : B[g]? with
    | none => simp
    | some x => exact h63 x (by simpa using Array.mem_of_getElem? h)
  have hfs : (Eval.Groups.firsts ⟨ByteArray.empty, B⟩).toList = (List.range (B.size - 1)).map fun g => (B[g]?).getD 0 := by
    simp [Eval.Groups.firsts, Eval.Groups.row, Eval.Groups.span, hemp]
  have hF64 : ∀ x ∈ ((Eval.Groups.firsts ⟨ByteArray.empty, B⟩).push 0).toList, x < 2 ^ 64 := by
    intro x hx
    rw [Array.toList_push, hfs] at hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx; have := hBg g; omega
    · simp at hx; omega
  refine ⟨Kernel.longBytes H, rfl, ?_, ?_, fun i hi => ?_⟩
  · have := congrArg List.length hLH; simp [Verify.ids] at this; omega
  · rw [nats_gather, nats_eq_ids (Kernel.longBytes H), hLH, nats_eq_ids, longBytes_ids _ hF64, Array.toList_push, hfs]
    apply List.ext_getElem (by simp [hHs])
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    rw [hHi i h2]
    rcases hrun i h2 with ⟨hn, hgr⟩ | ⟨a, z, g, hs, haz, hgr, hg, ha, hz⟩
    · rw [hn, hgr]
      simp [List.getD_eq_getElem?_getD]
    · have hg1 := (Array.getElem?_eq_some_iff.1 hz).1
      rw [hs, hgr]
      simp only [Option.bind_some, hg, Option.getD_some]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
      obtain ⟨d, hd⟩ : ∃ d, z - a = d + 1 := ⟨z - a - 1, by omega⟩
      simp [List.getElem?_range (show g < B.size - 1 by omega), ha, hd, List.range'_succ]
  rw [hatH i (by omega), hHi i hi]
  rcases hrun i hi with ⟨hn, hgr⟩ | ⟨a, z, g, hs, haz, hgr, hg, ha, hz⟩
  · left; rw [hn, hBn]; exact ⟨by simp, hgr⟩
  · right
    have hg1 := (Array.getElem?_eq_some_iff.1 hz).1
    obtain ⟨_, e0⟩ := Array.getElem?_eq_some_iff.1 ha
    obtain ⟨_, e1⟩ := Array.getElem?_eq_some_iff.1 hz
    simp only [hs, Option.bind_some, hg, Option.getD_some]
    rw [show g * 8 + 8 = (g + 1) * 8 by omega, hatB (g + 1) hg1, hatB g (by omega), hBn, hgr, e0, e1]
    refine ⟨by omega, by simp, fun p hp => ?_⟩
    simp only [List.length_range'] at hp
    simp [hemp, List.getElem!_eq_getElem?_getD, hp]

open QLean.Kernel in
/-- **The kernel's `ofRuns` at `key = id`, one key per needle, answers the key groups** (`KeyAnswers`) where
    each needle's run is its group: `none` where the group is empty, else `(a, z)` with the group the rows
    `[a, z)`, `z ≤ nr`. The statement carries `Eval.keyMatch`'s local `ofRuns` verbatim; the `s#` halving and the
    `u#`/`p#` gallop each call it so. -/
theorem ofRuns_kernel {wr wl : List UInt64} (nr nl : Nat) (run : Nat → Option (Nat × Nat)) (hnl : wl.length = nl)
    (hnr : nr < 2 ^ 63) (hnl2 : 2 * nl + 2 < 2 ^ 63)
    (hrun : ∀ i, i < nl → (run i = none ∧ Struct.group wr wl[i]! = []) ∨
      ∃ a z, run i = some (a, z) ∧ a < z ∧ z ≤ nr ∧ Struct.group wr wl[i]! = List.range' a (z - a)) :
    let ofRuns (nk : Nat) (key : Nat → Nat) (run : Nat → Option (Nat × Nat)) : Eval.Groups × Nat × Enc :=
      let met := if nk ≤ nl then Array.replicate nk true else
        (Array.range nl).foldl (init := Array.replicate nk false) fun m i =>
          if key i < nk then m.set! (key i) true else m
      let span : Std.HashMap Nat Nat := (Array.range nk).foldl (init := {}) fun m k =>
        if !met[k]! then m else match run k with
          | some (a, z) => m.insert a z
          | none => m
      let (bounds, ix) := ((span.toArray.map (·.1)).qsort (· < ·)).foldl
        (init := (#[0], ({} : Std.HashMap Nat Nat))) fun (bounds, ix) a =>
          let bounds := if bounds.back? == some a then bounds else bounds.push a
          (bounds.push (span.getD a a), ix.insert a (bounds.size - 1))
      let bounds := if bounds.back? == some nr then bounds else bounds.push nr
      let gid := (Array.range nk).map fun k => if met[k]! then (run k).bind (ix[·.1]?) else none
      (⟨ByteArray.empty, bounds⟩, Eval.groupIds (bounds.size - 1) ((Array.range nl).map fun i => gid.getD (key i) none))
    KeyAnswers wr wl (ofRuns nl id run).1 (ofRuns nl id run).2 := by
  intro ofRuns
  -- needles sharing a start share the end: both groups hold the start, so the two needles' words agree
  have hcons : ∀ k k' a z z', k < nl → k' < nl → run k = some (a, z) → run k' = some (a, z') → z = z' := by
    intro k k' a z z' hk hk' h1 h2
    rcases hrun k hk with ⟨h, -⟩ | ⟨a1, z1, e1, l1, -, g1⟩
    · rw [h] at h1; cases h1
    rcases hrun k' hk' with ⟨h, -⟩ | ⟨a2, z2, e2, l2, -, g2⟩
    · rw [h] at h2; cases h2
    rw [h1] at e1; rw [h2] at e2
    simp only [Option.some.injEq, Prod.mk.injEq] at e1 e2
    obtain ⟨rfl, rfl⟩ := e1; obtain ⟨rfl, rfl⟩ := e2
    have m1 : a ∈ Struct.group wr wl[k]! := by rw [g1]; simp; omega
    have m2 : a ∈ Struct.group wr wl[k']! := by rw [g2]; simp; omega
    simp only [Struct.group, List.mem_filter, beq_iff_eq] at m1 m2
    have hg : Struct.group wr wl[k]! = Struct.group wr wl[k']! := by rw [← m1.2, ← m2.2]
    rw [g1, g2] at hg
    have := congrArg List.length hg; simp at this; omega
  have hrep : ∀ k, k < nl → (Array.replicate nl true)[k]! = true := fun k hk => by
    rw [getElem!_pos _ k (by simpa using hk)]; simp
  dsimp only [ofRuns]
  generalize hS : (Array.range nl).foldl (β := Std.HashMap Nat Nat) _ {} = S
  generalize hP : ((S.toArray.map (·.1)).qsort (· < ·)).foldl (β := Array Nat × Std.HashMap Nat Nat) _ (#[0], {}) = P
  rcases P with ⟨B1, ix1⟩
  dsimp only
  rw [if_pos (Nat.le_refl nl)] at hS ⊢
  -- the span: each needle's start maps to its end, and nothing else is a start
  rw [← Array.foldl_toList, Array.toList_range] at hS
  have hsp : ∀ step, (∀ m k, k < nl → step m k = match run k with | some (a, z) => m.insert a z | none => m) →
      (List.range nl).foldl step ∅ = S →
      (∀ k, k < nl → ∀ a z, run k = some (a, z) → S[a]? = some z) ∧
      (∀ a, (∀ k, k < nl → ∀ z, run k ≠ some (a, z)) → S[a]? = none) ∧ S.size ≤ nl := fun step hst h => by
    have := QSort.ofRuns_span hst hcons nl (Nat.le_refl _) ∅
    have hsz : ∀ L : List Nat, (∀ k ∈ L, k < nl) → ∀ m : Std.HashMap Nat Nat, (L.foldl step m).size ≤ m.size + L.length := by
      intro L
      induction L with
      | nil => intro _ m; simp
      | cons k L ih =>
        intro hL m
        have h1 := ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) (step m k)
        have h2 : (step m k).size ≤ m.size + 1 := by
          rw [hst m k (hL k List.mem_cons_self)]
          split
          · exact Std.HashMap.size_insert_le
          · omega
        simp only [List.foldl_cons, List.length_cons]; omega
    have h3 := hsz (List.range nl) (fun k hk => List.mem_range.1 hk) ∅
    rw [h] at this h3
    exact ⟨this.1, fun a ha => by rw [this.2 a ha]; simp, by simpa using h3⟩
  obtain ⟨s1, s2, s3⟩ := hsp _ (fun m k hk => by
    simp only [hrep k hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]) hS
  have hSa : ∀ a z, S[a]? = some z → ∃ k, k < nl ∧ run k = some (a, z) := fun a z hz =>
    Classical.byContradiction fun hn => by
      rw [s2 a (fun k hk z' hr => hn ⟨k, hk, by
        have := s1 k hk a z' hr; rw [hz] at this; cases this; exact hr⟩)] at hz
      cases hz
  have hmem : ∀ a, a ∈ S → ∃ k z, k < nl ∧ run k = some (a, z) ∧ S.getD a a = z := fun a ha => by
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (Std.HashMap.mem_iff_isSome_getElem?.1 ha)
    obtain ⟨k, hk, hr⟩ := hSa a z hz
    exact ⟨k, z, hk, hr, by rw [Std.HashMap.getD_eq_getD_getElem?, hz]; rfl⟩
  -- the bounds fold over the sorted starts
  have hK := QSort.ofRuns_keys S
  rw [← Array.foldl_toList] at hP
  generalize hKdef : ((S.toArray.map (·.1)).qsort (· < ·)).toList = K at hP hK
  have hKle : ∀ a ∈ K, a ≤ nr ∧ S.getD a a ≤ nr := fun a ha => by
    obtain ⟨k, z, hk, hr, hg⟩ := hmem a ((hK.2.1 a).1 ha)
    rcases hrun k hk with ⟨h, -⟩ | ⟨a', z', e, l, hz, -⟩
    · rw [h] at hr; cases hr
    · rw [hr] at e; simp only [Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      omega
  have hKn : K.length ≤ nl := by
    rw [← hKdef, (QSort.qsort_nat _).1.length_eq]; simpa using s3
  have hb : ∀ F, K.foldl F (#[0], ∅) = (B1, ix1) → (∀ B ix a, F (B, ix) a =
      (let B' := if B.back? == some a then B else B.push a; (B'.push (S.getD a a), ix.insert a (B'.size - 1)))) →
      (∀ a ∈ K, ∃ g, ix1[a]? = some g ∧ B1[g]? = some a ∧ B1[g + 1]? = some (S.getD a a)) ∧ 0 < B1.size ∧
      (∀ x ∈ B1.toList, x ≤ nr) ∧ B1.size ≤ 1 + 2 * K.length := fun F h hF => by
    have b1 := QSort.ofRuns_bounds hF K #[0] ∅ hK.1 (by simp)
    have b2 := QSort.ofRuns_bounds_le hF nr K #[0] ∅ (by simp) hKle
    rw [h] at b1 b2
    exact ⟨b1.1, b1.2.2.2, b2.1, by simpa using b2.2⟩
  obtain ⟨b1, b2, b3, b4⟩ := hb _ hP (fun _ _ _ => rfl)
  -- the last bound `nr`
  generalize hBF : (if (B1.back? == some nr) = true then B1 else B1.push nr) = BF
  have f1 : ∀ g x, B1[g]? = some x → BF[g]? = some x := fun g x h => by
    rw [← hBF]; split
    · exact h
    · rw [Array.getElem?_push]; split
      · next he => subst he; simp at h
      · exact h
  have f2 : ∀ x ∈ BF.toList, x ≤ nr := fun x hx => by
    rw [← hBF] at hx; split at hx
    · exact b3 x hx
    · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact b3 x hx
      · exact Nat.le_refl _
  have f3 : 0 < BF.size ∧ BF.size ≤ B1.size + 1 := by rw [← hBF]; split <;> simp <;> omega
  -- the needles' ids
  generalize hG : Eval.groupIds (BF.size - 1) _ = Gc
  have hGc : Gc = Eval.groupIds (BF.size - 1) ((Array.range wl.length).map fun i => (run i).bind fun p => ix1[p.1]?) := by
    rw [← hG]; congr 1
    apply Array.ext (by simp [hnl])
    intro i h1 h2
    simp only [Array.size_map, Array.size_range] at h1
    simp [Array.getD_eq_getD_getElem?, h1]
  rw [hGc]
  refine ofRuns_answers (fun x hx => by have := f2 x hx; omega) (by omega) f3.1 fun i hi => ?_
  rcases hrun i (by omega) with h | ⟨a, z, hr, haz, hz, hgr⟩
  · exact Or.inl h
  · right
    have hS1 := s1 i (by omega) a z hr
    have haK : a ∈ K := (hK.2.1 a).2 (Std.HashMap.mem_iff_isSome_getElem?.2 (by rw [hS1]; rfl))
    obtain ⟨g, hg, hga, hgz⟩ := b1 a haK
    rw [Std.HashMap.getD_eq_getD_getElem?, hS1] at hgz
    exact ⟨a, z, g, hr, haz, hgr, hg, f1 _ _ hga, f1 _ _ hgz⟩

/-- `idxOf` names the first row holding `x`: none before it holds `x`, and it does where it is a row. -/
theorem idxOf_first {x : UInt64} : ∀ l : List UInt64,
    (∀ i, i < l.idxOf x → i < l.length → l[i]! ≠ x) ∧ (l.idxOf x < l.length → l[l.idxOf x]! = x)
  | [] => by simp
  | b :: l => by
    obtain ⟨h1, h2⟩ := idxOf_first l
    rw [List.idxOf_cons]
    by_cases hb : b = x
    · subst hb; simp
    · have e : (b == x) = false := by simpa using hb
      rw [e, cond_false]
      refine ⟨fun i hi hl => ?_, fun h => ?_⟩
      · cases i with
        | zero => simpa using hb
        | succ i => simpa using h1 i (by omega) (by simpa using hl)
      · simpa using h2 (by simpa using h)

/-- **One needle's state in `gallop`**, after `t` steps: a miss (`p` past the rows) sits at `lo = hi = n`;
    otherwise row `lo ≥ p` holds the needle `x`, `hi` is `n` or a row that does not, and the needle is done
    (`hi ≤ lo + 1`), galloping (stride `2^t`, `lo = p + 2^t - 1`), or halving a gap of at most `2^(126 - t)`. -/
def GallopInv (w : Nat → UInt64) (n : Nat) (x : UInt64) (p t lo hi st : Nat) : Prop :=
  (n ≤ p ∧ lo = n ∧ hi = n) ∨
  (p < n ∧ p ≤ lo ∧ lo < hi ∧ hi ≤ n ∧ w lo = x ∧ (hi = n ∨ w hi ≠ x) ∧
    (hi ≤ lo + 1 ∨ (st = 2 ^ t ∧ lo + 1 = p + 2 ^ t) ∨ (st = 0 ∧ hi - lo ≤ 2 ^ (126 - t))))

theorem gallopInv_start {w : Nat → UInt64} {n p : Nat} {x : UInt64} (hp : p ≤ n) (hx : p < n → w p = x) :
    GallopInv w n x p 0 (if p < n then p else n) n 1 := by
  unfold GallopInv
  by_cases h : p < n
  · right; rw [if_pos h]
    refine ⟨h, Nat.le_refl _, h, Nat.le_refl _, hx h, Or.inl rfl, ?_⟩
    by_cases h1 : n ≤ p + 1
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨by simp, by simp⟩)
  · left; rw [if_neg h]; exact ⟨by omega, rfl, rfl⟩

theorem gallopInv_idle {w : Nat → UInt64} {n p t lo hi st : Nat} {x : UInt64} (h : GallopInv w n x p t lo hi st)
    (hi1 : hi ≤ lo + 1) : GallopInv w n x p (t + 1) lo hi st := by
  unfold GallopInv at *
  rcases h with h | ⟨a, b, c, d, e, f, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, b, c, d, e, f, Or.inl hi1⟩

/-- **A `gallop` step** on an active needle probes a row strictly inside `(lo, hi)`; a hit moves `lo` there and
    doubles the stride, a miss moves `hi` there and halves from then on, and either keeps `GallopInv`. -/
theorem gallopInv_step {w : Nat → UInt64} {n p t lo hi st : Nat} {x : UInt64} (hn : n < 2 ^ 63)
    (h : GallopInv w n x p t lo hi st) (ha : lo + 1 < hi) :
    lo < (if st > 0 then min (lo + st) (hi - 1) else (lo + hi) / 2) ∧
    (if st > 0 then min (lo + st) (hi - 1) else (lo + hi) / 2) < hi ∧
    (w (if st > 0 then min (lo + st) (hi - 1) else (lo + hi) / 2) = x →
      GallopInv w n x p (t + 1) (if st > 0 then min (lo + st) (hi - 1) else (lo + hi) / 2) hi (2 * st)) ∧
    (w (if st > 0 then min (lo + st) (hi - 1) else (lo + hi) / 2) ≠ x →
      GallopInv w n x p (t + 1) lo (if st > 0 then min (lo + st) (hi - 1) else (lo + hi) / 2) 0) := by
  unfold GallopInv at h
  rcases h with ⟨-, rfl, rfl⟩ | ⟨hp, hpl, hlh, hhn, hw, hh, hpot⟩
  · omega
  rcases hpot with h1 | ⟨hst, hl⟩ | ⟨hst, hd⟩
  · omega
  · have h2 : 2 ^ t > 0 := Nat.two_pow_pos t
    have ht : t ≤ 62 := by
      rcases Nat.lt_or_ge t 63 with ht | ht
      · omega
      · have := Nat.pow_le_pow_right (show 2 > 0 by decide) ht; omega
    have hs : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [Nat.pow_succ]; omega
    have hm : 2 ^ t ≤ 2 ^ (126 - (t + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    subst hst
    rw [if_pos h2]
    refine ⟨by omega, by omega, fun hx => ?_, fun hx => ?_⟩
    · unfold GallopInv; right
      refine ⟨hp, by omega, by omega, hhn, hx, hh, ?_⟩
      by_cases hc : hi - 1 ≤ lo + 2 ^ t
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl ⟨hs.symm, by omega⟩)
    · unfold GallopInv; right
      exact ⟨hp, hpl, by omega, by omega, hw, Or.inr hx, Or.inr (Or.inr ⟨rfl, by omega⟩)⟩
  · subst hst
    have h0 : ¬ (0 > 0) := by decide
    rw [if_neg h0]
    have hk : 1 ≤ 126 - t := by
      rcases Nat.lt_or_ge t 126 with ht | ht
      · omega
      · rw [show 126 - t = 0 by omega] at hd; simp at hd; omega
    have hs : 2 ^ (126 - t) = 2 * 2 ^ (126 - (t + 1)) := by
      rw [show 126 - t = (126 - (t + 1)) + 1 by omega, Nat.pow_succ]; omega
    refine ⟨by omega, by omega, fun hx => ?_, fun hx => ?_⟩
    · unfold GallopInv; right
      exact ⟨hp, by omega, by omega, hhn, hx, hh, Or.inr (Or.inr ⟨rfl, by omega⟩)⟩
    · unfold GallopInv; right
      exact ⟨hp, hpl, by omega, by omega, hw, Or.inr hx, Or.inr (Or.inr ⟨rfl, by omega⟩)⟩

/-- After `2·64` steps every needle is done: a gallop cannot have reached a stride `2^128` below `n < 2^63`, and
    a halving's gap is down to `2^0`. -/
theorem gallopInv_done {w : Nat → UInt64} {n p lo hi st : Nat} {x : UInt64} (hn : n < 2 ^ 63)
    (h : GallopInv w n x p (2 * 64) lo hi st) : hi ≤ lo + 1 := by
  unfold GallopInv at h
  rcases h with ⟨-, rfl, rfl⟩ | ⟨hp, hpl, hlh, hhn, hw, hh, h1 | ⟨-, hl⟩ | ⟨-, hd⟩⟩
  · omega
  · exact h1
  · have := Nat.pow_le_pow_right (show 2 > 0 by decide) (show 63 ≤ 2 * 64 by decide); omega
  · simp at hd; omega

/-- **A done needle's run is its group**: with each value in one run, the rows holding `x` are `[p, hi)` from its
    first row `p`, or none where `p` is past the rows. -/
theorem gallop_group {wr : List UInt64} {x : UInt64} {t lo hi st : Nat} (hrun : OneRun (fun i => wr[i]!) wr.length)
    (h : GallopInv (fun i => wr[i]!) wr.length x (wr.idxOf x) t lo hi st) (hi1 : hi ≤ lo + 1) :
    (wr.length ≤ wr.idxOf x ∧ Struct.group wr x = []) ∨
    (wr.idxOf x < wr.length ∧ wr.idxOf x < hi ∧ hi ≤ wr.length ∧
      Struct.group wr x = List.range' (wr.idxOf x) (hi - wr.idxOf x)) := by
  obtain ⟨f1, f2⟩ := idxOf_first (x := x) wr
  unfold GallopInv at h
  rcases h with ⟨hp, -, -⟩ | ⟨hp, hpl, hlh, hhn, hw, hh, -⟩
  · left; refine ⟨hp, ?_⟩
    unfold Struct.group
    apply List.filter_eq_nil_iff.2
    intro i hi
    have := f1 i (by have := List.mem_range.1 hi; omega) (List.mem_range.1 hi)
    simpa using this
  · right
    refine ⟨hp, by omega, hhn, ?_⟩
    have hfx := f2 hp
    unfold Struct.group
    rw [← show min hi wr.length = hi from Nat.min_eq_left hhn, ← filter_range_interval]
    apply List.filter_congr
    intro i hmem
    have hin := List.mem_range.1 hmem
    show (wr[i]! == x) = decide (wr.idxOf x ≤ i ∧ i < hi)
    by_cases h1 : i < wr.idxOf x
    · have e1 : (wr[i]! == x) = false := by simpa using f1 i h1 hin
      rw [e1]; symm; simp; omega
    by_cases h2 : i ≤ lo
    · have := hrun (wr.idxOf x) lo i (by omega) h2 (by omega)
        (by show wr[wr.idxOf x]! = wr[lo]!; rw [hfx]; exact hw.symm)
      have e1 : (wr[i]! == x) = true := by
        simp only at this; rw [this, hfx]; simp
      rw [e1]; symm; simp; omega
    · have hne : wr[i]! ≠ x := fun e => by
        rcases hh with hh | hh
        · omega
        · exact hh (by
            have := hrun (wr.idxOf x) i hi (by omega) (by omega) hin
              (by show wr[wr.idxOf x]! = wr[i]!; rw [hfx, e])
            show wr[hi]! = x
            simp only at this; rw [this, hfx])
      have e1 : (wr[i]! == x) = false := by simpa using hne
      rw [e1]; symm; simp; omega

/-- **An invariant of a `for _ in [:n]` loop in `Option`**: each step from a state meeting `P t` either stops at
    a state meeting `Q` or goes on to one meeting `P (t+1)`, and `P n` gives `Q`; then the loop answers a `Q` state. -/
theorem forIn_range_inv {σ : Type} {n : Nat} {init : σ} {body : Nat → σ → Option (ForInStep σ)} {F : Option σ}
    (hF : forIn [:n] init body = F) (P : Nat → σ → Prop) (Q : σ → Prop) (h0 : P 0 init)
    (hstep : ∀ t s, t < n → P t s →
      (∃ s', body t s = some (.done s') ∧ Q s') ∨ (∃ s', body t s = some (.yield s') ∧ P (t + 1) s'))
    (hend : ∀ s, P n s → Q s) : ∃ s', F = some s' ∧ Q s' := by
  subst hF
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsz : ([:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  rw [hsz]
  have key : ∀ m b s, b + m = n → P b s → ∃ s', forIn (List.range' b m 1) s body = some s' ∧ Q s' := by
    intro m
    induction m with
    | zero => intro b s hb hP; exact ⟨s, rfl, hend s (by rw [← hb]; simpa using hP)⟩
    | succ m ih =>
      intro b s hb hP
      rw [List.range'_succ, List.forIn_cons]
      rcases hstep b s (by omega) hP with ⟨s', h, hq⟩ | ⟨s', h, hp⟩
      · rw [h]; exact ⟨s', rfl, hq⟩
      · rw [h]; exact ih (b + 1) s' (by omega) hp
  exact key n 0 init (by omega) h0

theorem getElem!_set! {a : Array Nat} {i j v : Nat} (hj : j < a.size) :
    (a.set! i v)[j]! = if i = j then v else a[j]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ j (by simpa using hj), Array.getElem_setIfInBounds hj,
    getElem!_pos a j hj]

open QLean.Kernel in
/-- **`gallop`'s loop** (`Eval.keyMatch`'s `u#`/`p#` pass, copied verbatim): every step's gather answering the
    right words at the probes, after `2·64` steps each needle `i` is done, its `hi` the end of the run that
    starts at `ps[i]`, the first row holding it (`GallopInv` with `hi ≤ lo + 1`). The continuation `k` is
    whatever the kernel does with `hi`. -/
theorem gallop_loop {α : Type} (k : Array Nat → α) (t : QAtomicType) (rn : Nat) (rc : Enc) (nd : ByteArray)
    (w nr nl : Nat) (ps : Array Nat) (wr wl : List UInt64) (hps : ps.size = nl) (hnr : wr.length = nr)
    (h63 : nr < 2 ^ 63)
    (hp : ∀ i, i < nl → ps[i]! = wr.idxOf wl[i]!) (hnd : ∀ i, i < nl → Column.bitsAt nd (i * w) w = wl[i]!)
    (hg : ∀ pr : Array Nat, (∀ k, k < pr.size → pr[k]! < nr) → ∃ ce g,
      gatherColumn t rn rc pr.size (.bytes (Kernel.longBytes pr)) = some ce ∧
      Enc.bytesOf t pr.size ce = some g ∧ ∀ k, k < pr.size → Column.bitsAt g (k * w) w = wr[pr[k]!]!) :
    ∃ H : Array Nat, (do
      let mut lo := ps.map fun p => if p < nr then p else nr
      let mut hi := ps.map fun _ => nr
      let mut st := ps.map fun _ => 1
      for _ in [0:2 * 64] do
        let act := (Array.range nl).filter fun i => lo[i]! + 1 < hi[i]!
        if act.isEmpty then break
        let pr := act.map fun i => if st[i]! > 0 then min (lo[i]! + st[i]!) (hi[i]! - 1) else (lo[i]! + hi[i]!) / 2
        let g ← Enc.bytesOf t pr.size (← Kernel.gatherColumn t rn rc pr.size (.bytes (Kernel.longBytes pr)))
        for k in [0:act.size] do
          let i := act[k]!
          if Column.bitsAt g (k * w) w == Column.bitsAt nd (i * w) w then
            lo := lo.set! i pr[k]!; st := st.set! i (2 * st[i]!)
          else hi := hi.set! i pr[k]!; st := st.set! i 0
      some (k hi) : Option α) = some (k H) ∧ H.size = nl ∧ ∀ i, i < nl →
      ∃ T lo st, GallopInv (fun j => wr[j]!) nr wl[i]! ps[i]! T lo H[i]! st ∧ H[i]! ≤ lo + 1 := by
  dsimp only
  generalize hF : forIn (m := Option) [:2 * 64] _ _ = F
  obtain ⟨s, hs, hQ1, hQ2⟩ := forIn_range_inv hF
    (fun t (s : MProd (Array Nat) (MProd (Array Nat) (Array Nat))) => s.fst.size = nl ∧ s.snd.fst.size = nl ∧
      s.snd.snd.size = nl ∧ ∀ i, i < nl →
        GallopInv (fun j => wr[j]!) nr wl[i]! ps[i]! t s.snd.fst[i]! s.fst[i]! s.snd.snd[i]!)
    (fun s => s.fst.size = nl ∧ ∀ i, i < nl →
      ∃ T lo st, GallopInv (fun j => wr[j]!) nr wl[i]! ps[i]! T lo s.fst[i]! st ∧ s.fst[i]! ≤ lo + 1)
    (by
      refine ⟨by simp [hps], by simp [hps], by simp [hps], fun i hi => ?_⟩
      obtain ⟨-, f2⟩ := idxOf_first (x := wl[i]!) wr
      have hip : i < ps.size := by omega
      have e1 : (ps.map fun _ => nr)[i]! = nr := by
        rw [getElem!_pos (ps.map fun _ => nr) i (by simpa using hip)]; simp
      have e2 : (ps.map fun p => if p < nr then p else nr)[i]! = if ps[i]! < nr then ps[i]! else nr := by
        rw [getElem!_pos (ps.map fun p => if p < nr then p else nr) i (by simpa using hip), getElem!_pos ps i hip]
        simp
      have e3 : (ps.map fun _ => 1)[i]! = 1 := by
        rw [getElem!_pos (ps.map fun _ => 1) i (by simpa using hip)]; simp
      dsimp only
      rw [e1, e2, e3, hp i hi]
      exact gallopInv_start (by rw [← hnr]; exact List.idxOf_le_length) (fun h => f2 (by omega)))
    (fun t s ht hP => by
      obtain ⟨H0, L0, S0⟩ := s
      obtain ⟨s1, s2, s3, hI⟩ := hP
      dsimp only at s1 s2 s3 hI ⊢
      generalize hA : Array.filter (fun i => decide (L0[i]! + 1 < H0[i]!)) (Array.range nl) = A
      have hAm : ∀ i, i ∈ A.toList ↔ i < nl ∧ L0[i]! + 1 < H0[i]! := fun i => by
        rw [← hA]; simp
      have hAs : A.toList.Pairwise (· < ·) := by
        rw [← hA, Array.toList_filter, Array.toList_range]; exact (List.pairwise_lt_range ..).filter _
      split
      · next hE =>
        left
        refine ⟨_, rfl, by simpa using s1, fun i hi => ⟨t, L0[i]!, S0[i]!, hI i hi, ?_⟩⟩
        have : A = #[] := by simpa using hE
        rcases Nat.lt_or_ge (L0[i]! + 1) H0[i]! with h | h
        · have := (hAm i).2 ⟨hi, h⟩; simp_all
        · exact h
      · next hE =>
        right
        obtain ⟨f, hf⟩ : ∃ f : Nat → Nat, ∀ i, f i =
            (if S0[i]! > 0 then min (L0[i]! + S0[i]!) (H0[i]! - 1) else (L0[i]! + H0[i]!) / 2) := ⟨_, fun _ => rfl⟩
        have hstp := fun i (hi : i < nl) (ha : L0[i]! + 1 < H0[i]!) => gallopInv_step h63 (hI i hi) ha
        generalize hpr : Array.map (fun i => if S0[i]! > 0 then min (L0[i]! + S0[i]!) (H0[i]! - 1)
          else (L0[i]! + H0[i]!) / 2) A = pr
        have hprs : pr.size = A.size := by rw [← hpr]; simp
        have hAk : ∀ k (hk : k < A.size), A[k]! < nl ∧ L0[A[k]!]! + 1 < H0[A[k]!]! := fun k hk =>
          (hAm _).1 (by rw [getElem!_pos A k hk]; simp)
        have hprk : ∀ k, k < A.size → pr[k]! = f A[k]! := fun k hk => by
          rw [← hpr, getElem!_pos _ k (by simpa using hk), Array.getElem_map, hf, getElem!_pos A k hk]
        obtain ⟨ce, g, hgc, hbg, hgw⟩ := hg pr (fun k hk => by
          rw [hprk k (by omega), hf]
          have := hstp _ (hAk k (by omega)).1 (hAk k (by omega)).2
          have := (hI _ (hAk k (by omega)).1)
          unfold GallopInv at this
          omega)
        simp only [hgc, hbg, bind, Option.bind]
        generalize hF2 : forIn (m := Option) [:A.size] _ _ = F2
        have hlt : ∀ k (hk : k < A.size) i, i ∈ A.toList.take k → i < A[k]! := by
          intro k hk i hi
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi
          simp only [List.length_take] at hj
          rw [List.getElem_take, getElem!_pos A k hk]
          have := List.pairwise_iff_getElem.1 hAs j k (by simp; omega) (by simpa using hk) (by omega)
          simpa using this
        have hTk : ∀ k (hk : k < A.size) i, i ∈ A.toList.take (k + 1) ↔ i ∈ A.toList.take k ∨ i = A[k]! := by
          intro k hk i
          rw [List.take_add_one, List.mem_append, getElem!_pos A k hk]
          simp [hk]
        obtain ⟨s2', hs2, z1, z2, z3, hz⟩ := forIn_range_inv hF2
          (fun k (s : MProd (Array Nat) (MProd (Array Nat) (Array Nat))) => s.fst.size = nl ∧ s.snd.fst.size = nl ∧
            s.snd.snd.size = nl ∧ ∀ i, i < nl →
              (i ∈ A.toList.take k → (wr[f i]! = wl[i]! → s.snd.fst[i]! = f i ∧ s.fst[i]! = H0[i]! ∧
                  s.snd.snd[i]! = 2 * S0[i]!) ∧
                (wr[f i]! ≠ wl[i]! → s.snd.fst[i]! = L0[i]! ∧ s.fst[i]! = f i ∧ s.snd.snd[i]! = 0)) ∧
              (i ∉ A.toList.take k → s.snd.fst[i]! = L0[i]! ∧ s.fst[i]! = H0[i]! ∧ s.snd.snd[i]! = S0[i]!))
          (fun s => s.fst.size = nl ∧ s.snd.fst.size = nl ∧ s.snd.snd.size = nl ∧ ∀ i, i < nl →
              (i ∈ A.toList.take A.size → (wr[f i]! = wl[i]! → s.snd.fst[i]! = f i ∧ s.fst[i]! = H0[i]! ∧
                  s.snd.snd[i]! = 2 * S0[i]!) ∧
                (wr[f i]! ≠ wl[i]! → s.snd.fst[i]! = L0[i]! ∧ s.fst[i]! = f i ∧ s.snd.snd[i]! = 0)) ∧
              (i ∉ A.toList.take A.size → s.snd.fst[i]! = L0[i]! ∧ s.fst[i]! = H0[i]! ∧ s.snd.snd[i]! = S0[i]!))
          ⟨s1, s2, s3, fun i hi => ⟨fun h => by simp at h, fun _ => ⟨rfl, rfl, rfl⟩⟩⟩
          (fun k s hk hP => by
            obtain ⟨H1, L1, S1⟩ := s
            obtain ⟨z1, z2, z3, hz⟩ := hP
            dsimp only at z1 z2 z3 hz ⊢
            right
            have ⟨hi0, ha0⟩ := hAk k hk
            have hn0 : A[k]! ∉ A.toList.take k := fun h => Nat.lt_irrefl _ (hlt k hk _ h)
            obtain ⟨hl1, hh1, hs1⟩ := (hz _ hi0).2 hn0
            have hc : (Column.bitsAt g (k * w) w == Column.bitsAt nd (A[k]! * w) w) =
                decide (wr[f A[k]!]! = wl[A[k]!]!) := by
              rw [hgw k (by omega), hnd _ hi0, hprk k hk]; exact Bool.eq_iff_iff.2 (by simp)
            rw [hc, hprk k hk]
            by_cases hh : wr[f A[k]!]! = wl[A[k]!]!
            · rw [if_pos (by simpa using hh)]
              refine ⟨_, rfl, by simpa using z1, by simpa using z2, by simpa using z3, fun i hi => ?_⟩
              dsimp only
              rw [getElem!_set! (by omega), getElem!_set! (by omega), hTk k hk]
              by_cases hii : A[k]! = i
              · subst hii
                simp only [hs1]
                exact ⟨fun _ => ⟨fun _ => ⟨rfl, hh1, rfl⟩, fun h => absurd hh h⟩, fun h => absurd (Or.inr trivial) h⟩
              · simp only [if_neg hii, Ne.symm hii, or_false]
                exact hz i hi
            · rw [if_neg (by simpa using hh)]
              refine ⟨_, rfl, by simpa using z1, by simpa using z2, by simpa using z3, fun i hi => ?_⟩
              dsimp only
              rw [getElem!_set! (by omega), getElem!_set! (by omega), hTk k hk]
              by_cases hii : A[k]! = i
              · subst hii
                simp only []
                exact ⟨fun _ => ⟨fun h => absurd h hh, fun _ => ⟨hl1, rfl, rfl⟩⟩, fun h => absurd (Or.inr trivial) h⟩
              · simp only [if_neg hii, Ne.symm hii, or_false]
                exact hz i hi)
          (fun s h => h)
        rw [hs2]
        refine ⟨_, rfl, by simpa using z1, by simpa using z2, by simpa using z3, fun i hi => ?_⟩
        dsimp only
        rw [List.take_of_length_le (by simp)] at hz
        obtain ⟨hz1, hz2⟩ := hz i hi
        by_cases ha : L0[i]! + 1 < H0[i]!
        · have hm := (hAm i).2 ⟨hi, ha⟩
          obtain ⟨-, -, e1, e2⟩ := hstp i hi ha
          rw [← hf] at e1 e2
          by_cases hh : wr[f i]! = wl[i]!
          · obtain ⟨a1, a2, a3⟩ := (hz1 hm).1 hh
            rw [a1, a2, a3]; exact e1 hh
          · obtain ⟨a1, a2, a3⟩ := (hz1 hm).2 hh
            rw [a1, a2, a3]; exact e2 hh
        · have hm : i ∉ A.toList := fun h => ha ((hAm i).1 h).2
          obtain ⟨a1, a2, a3⟩ := hz2 hm
          rw [a1, a2, a3]; exact gallopInv_idle (hI i hi) (by omega))
    (fun s hP => ⟨hP.1, fun i hi => ⟨2 * 64, s.snd.fst[i]!, s.snd.snd[i]!, hP.2.2.2 i hi,
      gallopInv_done h63 (hP.2.2.2 i hi)⟩⟩)
  rw [hs]
  exact ⟨s.fst, rfl, hQ1, hQ2⟩

open QLean.Kernel in
/-- Gathering a long column at rows `pr` inside it answers a long column whose words are the column's words at
    `pr`: `gallop_loop`'s gather hypothesis at the kernel's own right key column. -/
theorem gather_rows {n : Nat} {e : Enc} {wr : List UInt64} (hrw : longWords n e = some wr)
    (hrn : wr.length = n) (hU : n < USize.size) (pr : Array Nat) (hpr : ∀ k, k < pr.size → pr[k]! < n) :
    ∃ ce g, gatherColumn .long n e pr.size (.bytes (Kernel.longBytes pr)) = some ce ∧
      Enc.bytesOf .long pr.size ce = some g ∧ ∀ k, k < pr.size → Column.bitsAt g (k * 8) 8 = wr[pr[k]!]! := by
  obtain ⟨B, hBb, hBw, hBn⟩ := bytesOf_longWords hU hrw hrn
  have hw : ∀ i, i < B.size / 8 → wr[i]! = Column.bitsAt B (i * 8) 8 := fun i hi => by
    rw [← hBw, getElem!_pos _ i (by simp [Verify.elemsW]; omega)]; simp [Verify.elemsW]
  have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have h64 : ∀ x ∈ pr.toList, x < 2 ^ 64 := fun x hx => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have := hpr k (by simpa using hk); rw [getElem!_pos pr k (by simpa using hk)] at this
    simp at this ⊢; rcases USize.size_eq with h | h <;> omega
  have hLB := longBytes_ids pr h64
  have hLs : (Kernel.longBytes pr).size / 8 = pr.size := by
    have := congrArg List.length hLB; simpa [Verify.ids] using this
  have hix : Enc.bytesOf .long pr.size (.bytes (Kernel.longBytes pr)) = some (Kernel.longBytes pr) := rfl
  obtain ⟨c, hgc⟩ := gatherColumn_long_some hrw hix
    (by have := Nat.div_mul_le_self (Kernel.longBytes pr).size 8; rw [hLs] at this; exact this)
  obtain ⟨src, ix', hsrc, hix', hc⟩ := Verify.gatherColumn_fixed_shape (t := .long) (w := 8) rfl n e pr.size _ c
    (fun M P a he => by simp [longWords, he] at hrw) hgc
  have hsB : src = B := Option.some.inj (hsrc.symm.trans hBb)
  have hixe : ix' = Kernel.longBytes pr := Option.some.inj (hix'.symm.trans hix)
  rw [hsB, hixe] at hc
  subst hc
  refine ⟨_, _, hgc, rfl, fun k hk => ?_⟩
  obtain ⟨-, hg⟩ := Verify.gatherBytes_spec (8 : Nat).toUSize (by rw [h8]; exact Nat.le_refl 8)
    ((nullBits .long).getD 0) B (Kernel.longBytes pr)
  have hat : (Column.bitsAt (Kernel.longBytes pr) (k * 8) 8).toNat = pr[k]! := by
    rw [getElem!_pos pr k hk, ← Array.getElem_toList]
    exact Verify.ids_get hLB _
  have e := hg k (by omega)
  rw [h8, hat, if_pos (by have := hpr k hk; omega)] at e
  rw [e, hw _ (by have := hpr k hk; omega)]

open QLean.Kernel in
/-- **`keyMatch` at an `s#` right key column, where halving is not worth it, answers the key groups** through
    `byRuns`: the run starts cut the rows into the groups, read as their own row numbers, and `?` places each left
    word among the words at those starts. The kernel trusts the mark, so each value is assumed to occupy one run
    (`OneRun`), which is all `byRuns` needs of the order. -/
theorem keyMatch_runs {cr cl : Nat × Enc} {ar al : Option (UInt8 × IndexCell)} {wr wl : List UInt64}
    (nr nl : Nat) {cell : IndexCell} (hrw : longWords cr.1 cr.2 = some wr) (hrn : wr.length = cr.1)
    (h63 : cr.1 < 2 ^ 63) (hU : cr.1 < USize.size) (hlU : cl.1 < USize.size) (hlwf : Enc.WF .long cl.1 cl.2)
    (hlR : Find.Readable .long cl.1 cl.2) (hwl : longWords cl.1 cl.2 = some wl) (hs : ar = some (1, cell))
    (hh : worthHalving nr nl = false) (hrun : OneRun (fun i => wr[i]!) wr.length) :
    KeyAnswers wr wl (Eval.keyMatch #[.vector .long cr.1 cr.2 ar] nr #[.vector .long cl.1 cl.2 al] nl).1
      (Eval.keyMatch #[.vector .long cr.1 cr.2 ar] nr #[.vector .long cl.1 cl.2 al] nl).2 := by
  subst hs
  obtain ⟨B, hBb, hBw, hBn⟩ := bytesOf_longWords hU hrw hrn
  have hw : ∀ i, i < B.size / 8 → wr[i]! = Column.bitsAt B (i * 8) 8 := fun i hi => by
    rw [← hBw, getElem!_pos _ i (by simp [Verify.elemsW]; omega)]; simp [Verify.elemsW]
  have hwn : wr.length = B.size / 8 := by omega
  have hB1 : OneRun (fun i => Column.bitsAt B (i * 8) 8) (B.size / 8) := fun i j k h1 h2 h3 e => by
    change Column.bitsAt B (i * 8) 8 = Column.bitsAt B (j * 8) 8 at e
    change Column.bitsAt B (k * 8) 8 = Column.bitsAt B (i * 8) 8
    rw [← hw k (by omega), ← hw i (by omega)]
    rw [← hw i (by omega), ← hw j h3] at e
    exact hrun i j k h1 h2 (by omega) e
  generalize hF : Verify.firstsOf (Order.keyAt .i64 B) (B.size / 8) = F
  have hFs : F.Pairwise (· < ·) := by
    rw [← hF]; unfold Verify.firstsOf; exact (List.pairwise_lt_range ..).filter _
  have hFlt : ∀ f ∈ F, f < B.size / 8 := fun f hf => by
    rw [← hF] at hf; exact List.mem_range.1 (List.mem_filter.1 hf).1
  have hFlen : F.length ≤ B.size / 8 := by
    rw [← hF]; exact Nat.le_trans (List.length_filter_le _ _) (by simp [Verify.firstsOf])
  -- the bounds: the run starts, then the count
  have hR : (longRows (runStarts 8 false B)).toList = F ++ [B.size / 8] := by
    rw [longRows_runStarts B (by omega), ← firstsOf_runs hB1, hF]
  generalize hRdef : longRows (runStarts 8 false B) = R at hR
  have hRs : R.size = F.length + 1 := by rw [← Array.length_toList, hR]; simp
  have hR64 : ∀ x ∈ R.toList, x < 2 ^ 64 := fun x hx => by
    rw [hR] at hx; rcases List.mem_append.1 hx with hx | hx
    · have := hFlt x hx; omega
    · simp at hx; omega
  have hLB : Verify.ids (Kernel.longBytes R) = F ++ [B.size / 8] := by rw [longBytes_ids R hR64, hR]
  have hLBs : (Kernel.longBytes R).size / 8 = F.length + 1 := by
    have := congrArg List.length hLB; simpa [Verify.ids] using this
  have hat : ∀ q (hq : q < F.length + 1), (Column.bitsAt (Kernel.longBytes R) (q * 8) 8).toNat = (F ++ [B.size / 8])[q]'(by
      simp; omega) := fun q hq => Verify.ids_get hLB _
  have hnext : ∀ g (hg : g < F.length), F[g] < (F ++ [B.size / 8])[g + 1]'(by simp; omega) := fun g hg => by
    by_cases h : g + 1 < F.length
    · rw [List.getElem_append_left h]; exact List.pairwise_iff_getElem.1 hFs g (g + 1) hg h (by omega)
    · rw [List.getElem_append_right (by omega)]; simp only [List.getElem_singleton]
      exact hFlt _ (List.getElem_mem hg)
  -- the slice of all but the count: the run starts, the index the gather reads
  have hsl := Struct.sliceColumn_long R.size (Kernel.longBytes R) (by omega) 0 (R.size - 1)
  rw [if_neg (by omega)] at hsl
  generalize hS : cycleBytes (· * 8) R.size 0 (R.size - 1) (Kernel.longBytes R) = S at hsl
  have hSw : (Verify.elemsW 8 S).map UInt64.toNat = F := by
    have hE : (Verify.elemsW 8 (Kernel.longBytes R)).map UInt64.toNat = F ++ [B.size / 8] := by
      rw [← hLB]; simp [Verify.ids, Verify.elemsW]
    rw [← hS, show R.size = (Kernel.longBytes R).size / 8 by omega, Struct.elemsW_cycleBytes 8 (by decide) _ 0 _ (Or.inl (by omega)) (Or.inl (by omega))]
    apply List.ext_getElem (by simp; omega)
    intro q h1 h2
    simp only [List.getElem_map, List.getElem_range, Nat.zero_add]
    simp only [List.length_map, List.length_range] at h1
    rw [Nat.mod_eq_of_lt (by omega), getElem!_pos _ q (by simp [Verify.elemsW]; omega)]
    have e1 := List.getElem_of_eq hE (i := q) (by simp [Verify.elemsW]; omega)
    simp only [List.getElem_map] at e1
    rw [e1, List.getElem_append_left]
  have hSn : S.size / 8 = R.size - 1 := by
    have := congrArg List.length hSw; simp [Verify.elemsW] at this; omega
  have hAw := longWords_answer S hSn
  generalize hA : Enc.answer .long (R.size - 1) (.bytes S) = A at hsl hAw
  obtain ⟨ix, hix, hixw, hixn⟩ := bytesOf_longWords (by omega) hAw (by simp [Verify.elemsW]; omega)
  -- the gather: the words at the run starts, which are the distinct words in first-occurrence order
  obtain ⟨c, hgc⟩ := gatherColumn_long_some hrw hix (by have := Nat.div_mul_le_self ix.size 8; rw [hixn] at this; exact this)
  obtain ⟨src, ix', hsrc, hix', hc⟩ := Verify.gatherColumn_fixed_shape (t := .long) (w := 8) rfl cr.1 cr.2 _ A c
    (fun M P a he => by simp [longWords, he] at hrw) hgc
  have hsB : src = B := Option.some.inj (hsrc.symm.trans hBb)
  have hixe : ix' = ix := Option.some.inj (hix'.symm.trans hix)
  rw [hsB, hixe] at hc
  have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  generalize hDdef : gatherBytes (8 : Nat).toUSize ((nullBits .long).getD 0) B ix = D at hc
  have hD : Verify.elemsW 8 D = F.map fun f => Column.bitsAt B (f * 8) 8 := by
    have e := Verify.elemsW_gatherBytes (8 : Nat).toUSize (by rw [h8]; decide) (by rw [h8]; exact Nat.le_refl 8)
      ((nullBits .long).getD 0) B ix
    rw [h8, hDdef, hixw] at e
    rw [e, ← hSw, List.map_map]
    apply List.map_congr_left
    intro u hu
    have hu' : u.toNat < B.size / 8 := hFlt _ (by rw [← hSw]; exact List.mem_map_of_mem hu)
    simp only [Function.comp_apply]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [Verify.elemsW]; omega), Option.getD_some, Verify.ofNat_toNat_mod64]
    simp [Verify.elemsW]
  have hDs : D.size = (R.size - 1) * 8 := by
    have := (Verify.gatherBytes_spec (8 : Nat).toUSize (by rw [h8]; exact Nat.le_refl 8)
      ((nullBits .long).getD 0) B ix).1
    rw [h8, hDdef, hixn] at this; omega
  -- the groups: the bounds themselves, each group's rows its own positions
  have hgs : Eval.Groups.of ByteArray.empty R = ⟨ByteArray.empty, R⟩ := by
    unfold Eval.Groups.of; simp
  have hemp : (ByteArray.empty).isEmpty = true := by simp [ByteArray.isEmpty]
  have hbk : ∀ g (hg : g < F.length), Verify.bucketOf (Order.keyAt .i64 B) (B.size / 8) F[g] =
      List.range' F[g] ((F ++ [B.size / 8])[g + 1]'(by simp; omega) - F[g]) := fun g hg => by
    rw [bucket_run hB1 hF hg, getElem!_pos]
  obtain ⟨P, hFc, hKA⟩ := ofKey_answers (gs := ⟨ByteArray.empty, R⟩) (k := R.size - 1) hlU hlwf hlR hwl
    (by omega) (by omega) hF hD hDs (by show (Kernel.longBytes R).size / 8 - 1 = F.length; omega) (fun g hg => by
      dsimp only
      simp only [hemp, ↓reduceIte, hbk g hg, List.length_range']
      rw [show g * 8 + 8 = (g + 1) * 8 by omega, hat (g + 1) (by omega), hat g (by omega),
        List.getElem_append_left hg]
      exact ⟨by omega, fun p hp => by rw [getElem!_pos _ p (by simpa using hp), List.getElem_range']; simp⟩)
    (by
      apply List.ext_getElem (by simp [Eval.Groups.firsts, hRs])
      intro g h1 h2
      simp only [List.length_map] at h2
      have hRg : R[g]? = some F[g] := by
        rw [← Array.getElem?_toList, hR, List.getElem?_append_left h2, List.getElem?_eq_getElem h2]
      have hn := hnext g h2
      obtain ⟨d, hd⟩ : ∃ d, (F ++ [B.size / 8])[g + 1]'(by simp; omega) - F[g] = d + 1 :=
        ⟨(F ++ [B.size / 8])[g + 1]'(by simp; omega) - F[g] - 1, by omega⟩
      simp only [Eval.Groups.firsts, Array.toList_map, Array.toList_range, List.getElem_map, List.getElem_range,
        hbk g h2, hd, List.range'_succ]
      simp [Eval.Groups.row, Eval.Groups.span, hemp, hRg])
  -- `keyMatch` at `s#` not worth halving is `byRuns`
  have hK : Eval.keyMatch #[.vector .long cr.1 cr.2 (some (1, cell))] nr #[.vector .long cl.1 cl.2 al] nl =
      (Eval.Groups.of ByteArray.empty R, P.size / 8, .bytes P) := by
    have hrs : runsColumn .long cr.1 cr.2 = some (runStarts 8 false B) := by rw [runsColumn_long, hBb]; rfl
    unfold Eval.keyMatch
    rw [keyColumns_long cr cl _ al]
    simp only [bind, Option.bind, hrs, hRdef, hsl, hgc, hc, hFc]
    simp [QValue.marking, hh]
  rw [hK, hgs, ← hBw]; exact hKA

open QLean.Kernel in
/-- **`keyMatch` at a `u#`/`p#` right key column with no index built answers the key groups** through `gallop`:
    `?` gives each needle's first row, the loop gallops to the end of its run (`gallop_loop`, the gathers at the
    right key column by `gather_rows`), and `ofRuns` turns the runs into groups (`ofRuns_kernel`). The kernel
    trusts the mark, so each value is assumed to occupy one run (`OneRun`). -/
theorem keyMatch_gallop {cr cl : Nat × Enc} {ar al : Option (UInt8 × IndexCell)} {wr wl : List UInt64}
    (nr nl : Nat) {a : UInt8} {cell : IndexCell} (hrw : longWords cr.1 cr.2 = some wr) (hrn : wr.length = cr.1)
    (h63 : cr.1 < 2 ^ 63) (hU : cr.1 < USize.size) (hrwf : Enc.WF .long cr.1 cr.2)
    (hrR : Find.Readable .long cr.1 cr.2) (hlU : cl.1 < USize.size) (hlwf : Enc.WF .long cl.1 cl.2)
    (hlR : Find.Readable .long cl.1 cl.2) (hwl : longWords cl.1 cl.2 = some wl)
    (hln : wl.length = cl.1) (hnr : nr = cr.1) (hnl : wl.length = nl) (hnl2 : 2 * nl + 2 < 2 ^ 63)
    (hs : ar = some (a, cell)) (ha : a = 2 ∨ a = 3) (hc : cell.ready = none)
    (hrun : OneRun (fun i => wr[i]!) wr.length) :
    KeyAnswers wr wl (Eval.keyMatch #[.vector .long cr.1 cr.2 ar] nr #[.vector .long cl.1 cl.2 al] nl).1
      (Eval.keyMatch #[.vector .long cr.1 cr.2 ar] nr #[.vector .long cl.1 cl.2 al] nl).2 := by
  subst hnr hs
  -- `?`: each needle's first row
  obtain ⟨P, xs, ys, hP, hxs, hys, hmap⟩ := Find.probe_find (Arr.mk cr.2 hrwf) (Arr.mk cl.2 hlwf) hrR hlR hU hlU
  have hxs' : xs = wr := Option.some.inj ((show longWords cr.1 cr.2 = some xs from hxs).symm.trans hrw)
  have hys' : ys = wl := Option.some.inj ((show longWords cl.1 cl.2 = some ys from hys).symm.trans hwl)
  subst xs ys
  have hFc := Find.findColumn_long false cr.1 cr.2 cl.1 cl.2 none
  have hP' : probeColumns .long 8 false cr.1 cr.2 cl.1 cl.2 = some P := hP
  simp only [Bool.false_eq_true, false_and, ↓reduceIte, hP', Option.map_some] at hFc
  have hPl : P.size / 8 = wl.length := by
    have := congrArg List.length hmap; simpa [Verify.elemsW] using this
  have hpsz : (longRows P).size = nl := by simp [longRows]; omega
  have hpi : ∀ i, i < nl → (longRows P)[i]! = wr.idxOf wl[i]! := fun i hi => by
    have := congrArg (·[i]?) hmap
    simp only [Verify.elemsW, List.map_map, List.getElem?_map, List.getElem?_range (by omega : i < P.size / 8),
      List.getElem?_eq_getElem (by omega : i < wl.length), Option.map_some, Option.some.injEq,
      Function.comp_apply] at this
    rw [getElem!_pos _ i (by simp [longRows]; omega), getElem!_pos wl i (by omega)]
    simp only [longRows, Array.getElem_map, Array.getElem_range]
    rw [Nat.mul_comm]; exact this
  -- the needles' words
  obtain ⟨Bl, hBlb, hBlw, hBln⟩ := bytesOf_longWords hlU hwl hln
  have hnd : ∀ i, i < nl → Column.bitsAt Bl (i * 8) 8 = wl[i]! := fun i hi => by
    rw [← hBlw, getElem!_pos _ i (by simp [Verify.elemsW]; omega)]; simp [Verify.elemsW]
  -- the loop, its continuation `ofRuns` at the runs from each first row to the loop's `hi`
  obtain ⟨K, hKdef⟩ : ∃ K : Array Nat → Eval.Groups × Nat × Enc, K = fun hi =>
      let ofRuns (nk : Nat) (key : Nat → Nat) (run : Nat → Option (Nat × Nat)) : Eval.Groups × Nat × Enc :=
        let met := if nk ≤ nl then Array.replicate nk true else
          (Array.range nl).foldl (init := Array.replicate nk false) fun m i =>
            if key i < nk then m.set! (key i) true else m
        let span : Std.HashMap Nat Nat := (Array.range nk).foldl (init := {}) fun m k =>
          if !met[k]! then m else match run k with
            | some (a, z) => m.insert a z
            | none => m
        let (bounds, ix) := ((span.toArray.map (·.1)).qsort (· < ·)).foldl
          (init := (#[0], ({} : Std.HashMap Nat Nat))) fun (bounds, ix) a =>
            let bounds := if bounds.back? == some a then bounds else bounds.push a
            (bounds.push (span.getD a a), ix.insert a (bounds.size - 1))
        let bounds := if bounds.back? == some cr.1 then bounds else bounds.push cr.1
        let gid := (Array.range nk).map fun k => if met[k]! then (run k).bind (ix[·.1]?) else none
        (⟨ByteArray.empty, bounds⟩, Eval.groupIds (bounds.size - 1) ((Array.range nl).map fun i => gid.getD (key i) none))
      ofRuns nl id fun i => if (longRows P)[i]! < cr.1 then some ((longRows P)[i]!, hi[i]!) else none := ⟨_, rfl⟩
  obtain ⟨H, hL, hHs, hH⟩ := gallop_loop K .long cr.1 cr.2 Bl 8 cr.1 nl (longRows P) wr wl hpsz hrn
    h63 hpi hnd (fun pr hpr => gather_rows hrw hrn hU pr hpr)
  have hK : Eval.keyMatch #[.vector .long cr.1 cr.2 (some (a, cell))] cr.1 #[.vector .long cl.1 cl.2 al] nl = K H := by
    subst hKdef
    unfold Eval.keyMatch
    rw [keyColumns_long cr cl _ al]
    have hPb : Enc.bytesOf .long (P.size / 8) (.bytes P) = some P := rfl
    simp only [bind, Option.bind, hFc, hBlb, hPb] at hL ⊢
    rcases ha with rfl | rfl <;>
      simp [QValue.marking, Eval.viaIndex, hc, Kernel.foldsZero, QAtomicType.width, hPb, hpsz] at hL ⊢ <;>
      (generalize hF : forIn (m := Option) (List.range' 0 128) _ _ = F at hL
       -- the goal's loop is the same term up to the matchers' auxiliary names, which `erw` unfolds
       (try erw [hF])
       rcases F with _ | s
       · simp at hL
       · simp only [Option.some.injEq] at hL
         (try simp only)
         exact hL)
  -- each needle's run from its first row to the gallop's end is its group
  have hKA := ofRuns_kernel (wr := wr) (wl := wl) cr.1 nl
    (fun i => if (longRows P)[i]! < cr.1 then some ((longRows P)[i]!, H[i]!) else none) hnl h63 hnl2
    (fun i hi => by
      obtain ⟨T, lo, st, hG, h1⟩ := hH i hi
      rw [hpi i hi, ← hrn] at hG
      dsimp only
      rw [hpi i hi]
      rcases gallop_group hrun hG h1 with ⟨hp, hg⟩ | ⟨hp, hlt, hle, hg⟩
      · exact Or.inl ⟨by rw [if_neg (by omega)], hg⟩
      · exact Or.inr ⟨_, _, by rw [if_pos (by omega)], hlt, by omega, hg⟩)
  rw [hK, hKdef]; exact hKA

open QLean.Kernel in
/-- **The two halvings of an ascending column bound each needle's run**: `binr` answers the first row not under
    the needle, `bin` the last row not over it, so the rows holding it are `[binr, bin]`, empty where
    `bin = binr - 1`. -/
theorem binEdges_long {cr cl : Nat × Enc} {wr wl : List UInt64}
    (hrwf : Enc.WF .long cr.1 cr.2) (hrR : Find.Readable .long cr.1 cr.2) (hlwf : Enc.WF .long cl.1 cl.2)
    (hlR : Find.Readable .long cl.1 cl.2) (hU : cr.1 < USize.size) (hlU : cl.1 < USize.size) (h63 : cr.1 < 2 ^ 63)
    (hrw : longWords cr.1 cr.2 = some wr) (hwl : longWords cl.1 cl.2 = some wl)
    (hasc : ∀ i j, i ≤ j → j < wr.length → wr[i]!.toInt64 ≤ wr[j]!.toInt64) :
    ∃ lo hi : ByteArray,
      binColumn .long true cr.1 cr.2 (.vector .long cl.1 cl.2 none) = some (.vector .long cl.1 (.bytes lo) none) ∧
      binColumn .long false cr.1 cr.2 (.vector .long cl.1 cl.2 none) = some (.vector .long cl.1 (.bytes hi) none) ∧
      ∀ i, i < wl.length →
        0 ≤ (Column.bitsAt lo (i * 8) 8).toInt64.toInt ∧
        (Column.bitsAt lo (i * 8) 8).toInt64.toInt ≤ (Column.bitsAt hi (i * 8) 8).toInt64.toInt + 1 ∧
        (Column.bitsAt hi (i * 8) 8).toInt64.toInt < wr.length ∧
        Struct.group wr wl[i]! = List.range' (Column.bitsAt lo (i * 8) 8).toInt64.toInt.toNat
          ((Column.bitsAt hi (i * 8) 8).toInt64.toInt + 1 - (Column.bitsAt lo (i * 8) 8).toInt64.toInt).toNat := by
  obtain ⟨hk, hmd, hp, xs, hox, hwx, hbx, hlx⟩ := Find.operand_long (Arr.mk cr.2 hrwf) hrR hU
  obtain ⟨nk, nmd, np, ys, hoy, hwy, hby, hly⟩ := Find.operand_long (Arr.mk cl.2 hlwf) hlR hlU
  have hxs : xs = wr := Option.some.inj ((show longWords cr.1 cr.2 = some xs from hwx).symm.trans hrw)
  have hys : ys = wl := Option.some.inj ((show longWords cl.1 cl.2 = some ys from hwy).symm.trans hwl)
  rw [hxs] at hbx hlx; rw [hys] at hby hly
  refine ⟨binBytes 8 false true true (operandBytes 8 hmd hp hk.toUSize) (operandBytes 8 nmd np nk.toUSize),
    binBytes 8 false true false (operandBytes 8 hmd hp hk.toUSize) (operandBytes 8 nmd np nk.toUSize),
    by rw [Find.binColumn_long true cr.1 cr.2 cl.1 cl.2 none, show operand .long cr.1 cr.2 = _ from hox,
      show operand .long cl.1 cl.2 = _ from hoy]; rfl,
    by rw [Find.binColumn_long false cr.1 cr.2 cl.1 cl.2 none, show operand .long cr.1 cr.2 = _ from hox,
      show operand .long cl.1 cl.2 = _ from hoy]; rfl,
    fun i hi => ?_⟩
  generalize operandBytes 8 hmd hp hk.toUSize = Hb at hbx ⊢
  generalize operandBytes 8 nmd np nk.toUSize = Kb at hby ⊢
  obtain ⟨hHs, gH⟩ := Find.elemsW8_get hbx
  obtain ⟨hKs, gK⟩ := Find.elemsW8_get hby
  -- the words as integers, the needle `xv`
  have hle : ∀ j, j < wr.length → (ordKey 8 false true (Column.bitsAt Hb (j * 8) 8) ≤
      ordKey 8 false true (Column.bitsAt Kb (i * 8) 8) ↔ wr[j]!.toInt64.toInt ≤ wl[i]!.toInt64.toInt) :=
    fun j hj => by
      rw [ordKey8_le, gH j hj, gK i hi, getElem!_pos wr j hj, getElem!_pos wl i hi, Int64.le_iff_toInt_le]
  have hlt' : ∀ j, j < wr.length → (ordKey 8 false true (Column.bitsAt Hb (j * 8) 8) <
      ordKey 8 false true (Column.bitsAt Kb (i * 8) 8) ↔ wr[j]!.toInt64.toInt < wl[i]!.toInt64.toInt) :=
    fun j hj => by
      rw [← UInt64.not_le, ordKey8_le, gH j hj, gK i hi, getElem!_pos wr j hj, getElem!_pos wl i hi,
        Int64.le_iff_toInt_le]; omega
  have hsort : ∀ a b, a ≤ b → b < wr.length → ordKey 8 false true (Column.bitsAt Hb (a * 8) 8) ≤
      ordKey 8 false true (Column.bitsAt Hb (b * 8) 8) := fun a b hab hb => by
    rw [ordKey8_le, gH a (by omega), gH b hb, ← getElem!_pos wr a (by omega), ← getElem!_pos wr b hb]
    exact hasc a b hab hb
  have hkr := Verify.bitsAt_binBytes 8 false true true Hb Kb i (by rw [Find.usize_eight, hKs]; exact hi)
  have hkf := Verify.bitsAt_binBytes 8 false true false Hb Kb i (by rw [Find.usize_eight, hKs]; exact hi)
  obtain ⟨pr_le, hR1, hR2⟩ := Verify.binStep_spec 8 false true true Hb
    (ordKey 8 false true (Column.bitsAt Kb (i * 8) 8)) wr.length hsort
  obtain ⟨pf_le, hF1, hF2⟩ := Verify.binStep_spec 8 false true false Hb
    (ordKey 8 false true (Column.bitsAt Kb (i * 8) 8)) wr.length hsort
  simp only [Find.usize_eight, ↓reduceIte, Bool.false_eq_true, hHs, Nat.mul_comm 8 i] at hkr hkf hR1 hR2 hF1 hF2
  generalize binStep 8 false true true Hb ByteArray.empty (ordKey 8 false true (Column.bitsAt Kb (i * 8) 8))
    (wr.length + 1) 0 wr.length = pr at hkr pr_le hR1 hR2
  generalize binStep 8 false true false Hb ByteArray.empty (ordKey 8 false true (Column.bitsAt Kb (i * 8) 8))
    (wr.length + 1) 0 wr.length = pf at hkf pf_le hF1 hF2
  have hn63 : wr.length < 2 ^ 63 := by omega
  rw [hkr, hkf, Int64.toInt64_toUInt64, Int64.toInt64_toUInt64, Int.toInt64,
    Int64.toInt_ofInt_of_le (by omega) (by omega), Int64.toInt_ofInt_of_le (by omega) (by omega)]
  have r1 : ∀ j, j < pr → wr[j]!.toInt64.toInt < wl[i]!.toInt64.toInt := fun j hj =>
    (hlt' j (by omega)).1 (hR1 j hj)
  have r2 : ∀ j, pr ≤ j → j < wr.length → wl[i]!.toInt64.toInt ≤ wr[j]!.toInt64.toInt := fun j h1 h2 => by
    have := hR2 j h1 h2; rw [hlt' j h2] at this; omega
  have f1 : ∀ j, j < pf → wr[j]!.toInt64.toInt ≤ wl[i]!.toInt64.toInt := fun j hj => (hle j (by omega)).1 (hF1 j hj)
  have f2 : ∀ j, pf ≤ j → j < wr.length → wl[i]!.toInt64.toInt < wr[j]!.toInt64.toInt := fun j h1 h2 => by
    have := hF2 j h1 h2; rw [hle j h2] at this; omega
  have hpp : pr ≤ pf := Nat.le_of_not_lt fun h => by have := r1 pf h; have := f2 pf (Nat.le_refl _) (by omega); omega
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [show ((pr : Int)).toNat = pr by omega, show ((pf : Int) - 1 + 1 - (pr : Int)).toNat = pf - pr by omega]
  unfold Struct.group
  rw [show pf - pr = min pf wr.length - pr by omega, ← filter_range_interval]
  apply List.filter_congr
  intro j hmem
  have hj := List.mem_range.1 hmem
  have e : (wr[j]! == wl[i]!) = decide (wr[j]!.toInt64.toInt = wl[i]!.toInt64.toInt) := by
    apply Bool.eq_iff_iff.2; simp only [beq_iff_eq, decide_eq_true_eq]
    exact ⟨fun h => by rw [h], fun h => toInt64_inj (Int64.toInt_inj.1 h)⟩
  rw [e]
  apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq]
  constructor
  · intro h
    by_cases h1 : j < pr
    · have := r1 j h1; omega
    by_cases h2 : pf ≤ j
    · have := f2 j h2 hj; omega
    omega
  · intro ⟨h1, h2⟩; have := r2 j h1 hj; have := f1 j h2; omega

open QLean.Kernel in
/-- **`keyMatch` at an `s#` right key column, where halving is worth it, answers the key groups** through
    `halved`: `binr` and `bin` of each needle edge its run (`binEdges_long`), and `ofRuns` turns the runs into
    groups (`ofRuns_kernel`). The kernel trusts the mark, so the column is assumed ascending. -/
theorem keyMatch_halved {cr cl : Nat × Enc} {ar al : Option (UInt8 × IndexCell)} {wr wl : List UInt64}
    (nr nl : Nat) {cell : IndexCell} (hrw : longWords cr.1 cr.2 = some wr) (hrn : wr.length = cr.1)
    (h63 : cr.1 < 2 ^ 63) (hU : cr.1 < USize.size) (hrwf : Enc.WF .long cr.1 cr.2)
    (hrR : Find.Readable .long cr.1 cr.2) (hlU : cl.1 < USize.size) (hlwf : Enc.WF .long cl.1 cl.2)
    (hlR : Find.Readable .long cl.1 cl.2) (hwl : longWords cl.1 cl.2 = some wl)
    (hnr : nr = cr.1) (hnl : wl.length = nl) (hnl2 : 2 * nl + 2 < 2 ^ 63)
    (hs : ar = some (1, cell)) (hh : worthHalving nr nl = true)
    (hasc : ∀ i j, i ≤ j → j < wr.length → wr[i]!.toInt64 ≤ wr[j]!.toInt64) :
    KeyAnswers wr wl (Eval.keyMatch #[.vector .long cr.1 cr.2 ar] nr #[.vector .long cl.1 cl.2 al] nl).1
      (Eval.keyMatch #[.vector .long cr.1 cr.2 ar] nr #[.vector .long cl.1 cl.2 al] nl).2 := by
  subst hnr hs
  obtain ⟨lo, hi, hlo, hhi, hE⟩ := binEdges_long hrwf hrR hlwf hlR hU hlU h63 hrw hwl hasc
  have hKA := ofRuns_kernel (wr := wr) (wl := wl) cr.1 nl (fun i =>
      if (Column.bitsAt lo (i * 8) 8).toInt64.toInt ≤ (Column.bitsAt hi (i * 8) 8).toInt64.toInt then
        some ((Column.bitsAt lo (i * 8) 8).toInt64.toInt.toNat, (Column.bitsAt hi (i * 8) 8).toInt64.toInt.toNat + 1)
      else none) hnl h63 hnl2 (fun i hi' => by
        obtain ⟨h0, h1, h2, hg⟩ := hE i (by omega)
        dsimp only
        split
        · exact Or.inr ⟨_, _, rfl, by omega, by omega, by rw [hg]; congr 1; omega⟩
        · exact Or.inl ⟨rfl, by rw [hg, show ((Column.bitsAt hi (i * 8) 8).toInt64.toInt + 1 -
            (Column.bitsAt lo (i * 8) 8).toInt64.toInt).toNat = 0 by omega]; rfl⟩)
  unfold Eval.keyMatch
  rw [keyColumns_long cr cl _ al]
  simp only [bind, Option.bind, hlo, hhi]
  simp [QValue.marking, hh]
  simpa using hKA

/-- An ascending column (at the `Int64` order `s#` claims) holds each value in one run: a row between two equal
    rows is squeezed between them, and `Int64` order is antisymmetric. -/
theorem oneRun_of_ascending {wr : List UInt64}
    (hasc : ∀ i j, i ≤ j → j < wr.length → wr[i]!.toInt64 ≤ wr[j]!.toInt64) :
    OneRun (fun i => wr[i]!) wr.length := fun i j k hik hkj hj e => by
  have h1 := hasc i k hik (by omega)
  have h2 := hasc k j hkj hj
  simp only at e ⊢
  rw [e] at h1
  have h := congrArg Int64.toUInt64 (Int64.le_antisymm h2 h1)
  simpa [e] using h

-- gap: a ready index (`a ∈ {2,3,4}`, `cell.ready = some ix`; `s#` is `a = 1 < 2`, so `viaIndex` always scans it).
--   `viaIndex` runs `indexed ix` and scans only on `none`, so the scan half is the proofs above; the index half
--   needs, first, a predicate `Describes ix wr` tying `ix` to `cr`'s words — none can be stated, since
--   `IndexCell.ready` is opaque and no invariant links the cell to the column. From it:
--   * `a = 2, 3`: `Index.spans ix .long lcol = some (nk, key, run)` →
--     `∀ i < nl, (∃ a z, key i < nk ∧ run (key i) = some (a, z) ∧ a < z ∧ z ≤ nr ∧ group wr wl[i]! = range' a (z-a))
--       ∨ ((nk ≤ key i ∨ run (key i) = none) ∧ group wr wl[i]! = [])`
--     (via `Index.positions`, and `spans`' `.more` shift by `n`), and `ofRuns_kernel` generalised from
--     `nk = nl`, `key = id` to any `nk`, `key` (the `met` fold where `nk > nl`).
--   * `a = 4`: `partGroups nr nl leaf ix` answers `KeyAnswers` — specs of `Index.positions`, `Index.runRows`,
--     `binColumn` on the index's `keys`, the `walk` fold, the cached `(kv, offs, rows)` as `groupColumn`'s answer,
--     and `partGroups.join` merging two parts' groups under `.more`/`.edit`.

/-- **`keyMatch` answers the key groups** at an unmarked right key column, at `s#` on an ascending column (not
    worth halving: `keyMatch_runs` through `oneRun_of_ascending`; worth halving: `keyMatch_halved`), at `u#`/`p#`
    with no index built and each value in one run (`keyMatch_gallop`), and at `` `g `` with no index built
    (`keyMatch_grouped`). -/
theorem keyMatch_answers {cr cl : Nat × Enc} {ar al : Option (UInt8 × IndexCell)} {wr wl : List UInt64}
    (nr nl : Nat) (hrw : longWords cr.1 cr.2 = some wr) (hrn : wr.length = cr.1) (h63 : cr.1 < 2 ^ 63)
    (hU : cr.1 < USize.size) (hrwf : Enc.WF .long cr.1 cr.2) (hrR : Find.Readable .long cr.1 cr.2)
    (hlU : cl.1 < USize.size) (hlwf : Enc.WF .long cl.1 cl.2) (hlR : Find.Readable .long cl.1 cl.2)
    (hwl : longWords cl.1 cl.2 = some wl) (hln : wl.length = cl.1)
    (hnr : nr = cr.1) (hnl : wl.length = nl) (hnl2 : 2 * nl + 2 < 2 ^ 63)
    (hattr : ∀ a cell, ar = some (a, cell) →
      (a = 1 → ∀ i j, i ≤ j → j < wr.length → wr[i]!.toInt64 ≤ wr[j]!.toInt64) ∧
      (a = 2 ∨ a = 3 → OneRun (fun i => wr[i]!) wr.length) ∧
      (a = 2 ∨ a = 3 ∨ a = 4 → cell.ready = none)) :
    KeyAnswers wr wl (Eval.keyMatch #[.vector .long cr.1 cr.2 ar] nr #[.vector .long cl.1 cl.2 al] nl).1
      (Eval.keyMatch #[.vector .long cr.1 cr.2 ar] nr #[.vector .long cl.1 cl.2 al] nl).2 := by
  rcases hca : ar with _ | ⟨a, cell⟩
  · exact keyMatch_grouped nr nl hrw hrn h63 hU hlU hlwf hlR hwl (fun a cell h => by cases h)
  · obtain ⟨h1, h2, h3⟩ := hattr a cell hca
    by_cases ha : a = 1
    · subst ha
      cases hw : Kernel.worthHalving nr nl
      · exact keyMatch_runs nr nl hrw hrn h63 hU hlU hlwf hlR hwl rfl hw (oneRun_of_ascending (h1 rfl))
      · exact keyMatch_halved nr nl hrw hrn h63 hU hrwf hrR hlU hlwf hlR hwl hnr hnl hnl2 rfl hw (h1 rfl)
    by_cases hb : a = 2 ∨ a = 3
    · exact keyMatch_gallop nr nl hrw hrn h63 hU hrwf hrR hlU hlwf hlR hwl hln hnr hnl hnl2 rfl hb
        (h3 (hb.elim Or.inl fun e => Or.inr (Or.inl e))) (h2 hb)
    · exact keyMatch_grouped nr nl hrw hrn h63 hU hlU hlwf hlR hwl (fun a' cell' h => by
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨ha, fun e => hb (Or.inl e), fun e => hb (Or.inr e), fun e => h3 (Or.inr (Or.inr e))⟩)

/-- **`aj` at one long key column per side is `ajSpec`** of the two sides' key words: `aj_groups` with its
    group hypothesis answered by `keyMatch_answers`. The right key column's `s#` is taken ascending;
    `u#`/`p#` only unindexed with each value in one run, `g#` only unindexed;
    key columns bytes or frame of reference, times dense long. -/
theorem aj_long {cl cr tl tr : Nat × Enc} {wl wr : List UInt64} {m : Nat} {A : Arr .long m} {keys hay : ByteArray}
    (hwl : longWords cl.1 cl.2 = some wl) (hwr : longWords cr.1 cr.2 = some wr)
    (hln : wl.length = cl.1) (hrn : wr.length = cr.1) (hcl : cl.1 = tl.1) (hcr : cr.1 = tr.1)
    (hlwf : Enc.WF .long cl.1 cl.2) (hlR : Find.Readable .long cl.1 cl.2)
    (hrwf : Enc.WF .long cr.1 cr.2) (hrR : Find.Readable .long cr.1 cr.2)
    (hkb : Enc.bytesOf .long tl.1 tl.2 = some keys)
    (hrb : Enc.bytesOf .long tr.1 tr.2 = some hay) (hkn : keys.size / 8 = tl.1) (hhn : hay.size / 8 = tr.1)
    (hU : tl.1 < USize.size) (hrU : tr.1 < USize.size) (h63 : tr.1 < 2 ^ 63) (h2l : 2 * tl.1 + 2 < 2 ^ 63)
    (h : Struct.aj #[(.long, cl)] #[(.long, cr)] (.long, tl) (.long, tr) = .ok ⟨m, A⟩) :
    A.toList = Struct.ajSpec wl ((nats keys).map Int64.ofNat) wr ((nats hay).map Int64.ofNat) := by
  have hkg : Struct.keyGroups "aj" #[(.long, cl)] #[(.long, cr)] tl.1 tr.1 =
      .ok (Eval.keyMatch #[.vector .long cr.1 cr.2 none] tr.1 #[.vector .long cl.1 cl.2 none] tl.1) := by
    simp [Struct.keyGroups, Struct.colRows, Struct.colValue, hcl, hcr] <;> rfl
  -- a key column carries no attribute (`colValue` answers it bare), so the `none` arm of `hattr` is all there is
  have hk := keyMatch_answers tr.1 tl.1 hwr hrn (by omega) (by omega) hrwf hrR (by omega) hlwf hlR hwl
    hln hcr.symm (by omega) h2l (ar := none) (al := none) (fun _ _ h => by cases h)
  obtain ⟨gids, hgb, -⟩ := id hk
  exact aj_groups wl wr hkb hrb hgb hkn hhn (by omega) (by omega) hU h63 hkg hk h

/-! ## `wj`: each left row's two edges, clamped to its group's head, and the right rows between

  `wjP` reads `binRows` twice (`binRows_group`), fills the miss with `-1`, adds `off`, takes `|` with the
  group's head (`KeyAnswers`' starts), then `0 | hi - lo` counts and `expand` lays the rows `lo + j` out. -/

/-- A payload whose words are `f` below `n` reads `f i` at word `i`. -/
theorem bitsAt_elemsW {b : ByteArray} {n : Nat} {f : Nat → UInt64} (h : Verify.elemsW 8 b = (List.range n).map f)
    {i : Nat} (hi : i < n) : Column.bitsAt b (i * 8) 8 = f i := by
  have hl := congrArg List.length h
  simp only [Verify.elemsW, List.length_map, List.length_range] at hl
  have := congrArg (fun L => L[i]?) h
  simp only [Verify.elemsW, List.getElem?_map, List.getElem?_range, hl, hi, Option.map_some, Option.some.injEq] at this
  exact this

/-- A long below `2^63` is never the null. -/
theorem ofNat_ne_min {a : Nat} (h : a < 2 ^ 63) : (Int64.ofNat a == Int64.minValue) = false := by
  apply Bool.eq_false_iff.2; intro e
  have := congrArg Int64.toInt (beq_iff_eq.1 e)
  rw [Int64.toInt_ofNat_of_lt h] at this
  have hm : Int64.minValue.toInt = -2 ^ 63 := by decide
  omega

/-- A natural below `2^63`, as a word read as a long, is its `Int64.ofNat`. -/
theorem toUInt64_toInt64 {a : Nat} (h : a < 2 ^ 63) : a.toUInt64.toInt64 = Int64.ofNat a := by
  rw [toInt64_eq_ofNat, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

/-- `Int64.ofNat a`'s word is `a`, below `2^63`. -/
theorem ofNat_toUInt64_toNat {a : Nat} (h : a < 2 ^ 63) : (Int64.ofNat a).toUInt64.toNat = a := by
  have := toInt_toNat_word (u := (Int64.ofNat a).toUInt64) (by
    rw [Int64.toInt64_toUInt64, Int64.le_iff_toInt_le, Int64.toInt_ofNat_of_lt h]; simp)
  rw [Int64.toInt64_toUInt64, Int64.toInt_ofNat_of_lt h] at this
  simpa using this.symm

/-- **One edge word**: `bin`'s row `r` (the miss `nr` where `b` is none), `^` with `-1`, plus `off ≤ 1`, then
    `|` the head `s`, is `max s (r + off)`, and `s` at a miss. -/
theorem wj_edge_word (nr s off : Nat) (b : Option Nat) (hb : ∀ r, b = some r → r < nr) (hoff : off ≤ 1)
    (hs : s < 2 ^ 62) (hnr : nr < 2 ^ 62) :
    Kernel.Ew.intStep Kernel.Ew.greater Int64.minValue (Int64.ofNat s)
      (if off == 0 then
        Kernel.Ew.intStep Kernel.Ew.fill (Int64.ofNat nr) (-1) ((b.map Nat.toUInt64).getD nr.toUInt64).toInt64
       else Kernel.Ew.intStep Kernel.Ew.add Int64.minValue
        (Kernel.Ew.intStep Kernel.Ew.fill (Int64.ofNat nr) (-1) ((b.map Nat.toUInt64).getD nr.toUInt64).toInt64)
        (Int64.ofNat off)) =
      Int64.ofNat ((b.map (max s <| · + off)).getD s) := by
  have hfill : ∀ nul x y : Int64, Kernel.Ew.intStep Kernel.Ew.fill nul x y = if y == nul then x else y :=
    fun _ _ _ => rfl
  have hgr : ∀ nul x y : Int64, Kernel.Ew.intStep Kernel.Ew.greater nul x y = if y < x then x else y :=
    fun _ _ _ => rfl
  have hadd : ∀ nul x y : Int64,
      Kernel.Ew.intStep Kernel.Ew.add nul x y = if (x == nul || y == nul) then nul else x + y := fun _ _ _ => rfl
  have hmax : ∀ a, a < 2 ^ 63 → (if Int64.ofNat a < Int64.ofNat s then Int64.ofNat s else Int64.ofNat a) =
      Int64.ofNat (max s a) := fun a ha => by
    by_cases h : a < s
    · rw [if_pos ((Int64.ofNat_lt_iff_lt ha (by omega)).2 h)]; congr 1; omega
    · rw [if_neg (mt (Int64.ofNat_lt_iff_lt ha (by omega)).1 h)]; congr 1; omega
  have hm1 : ((-1 : Int64) == Int64.minValue) = false := by decide
  have hneg : (-1 : Int64) + Int64.ofNat 1 = Int64.ofNat 0 := by decide
  have hlt : (-1 : Int64) < Int64.ofNat s := by
    rw [Int64.lt_iff_toInt_lt, Int64.toInt_ofNat_of_lt (by omega)]
    have : (-1 : Int64).toInt = -1 := by decide
    omega
  have hne : ∀ r, r < nr → (Int64.ofNat r == Int64.ofNat nr) = false := fun r hr => by
    apply Bool.eq_false_iff.2; intro e
    have := congrArg Int64.toInt (beq_iff_eq.1 e)
    rw [Int64.toInt_ofNat_of_lt (by omega), Int64.toInt_ofNat_of_lt (by omega)] at this
    omega
  have hnn : (Int64.ofNat nr == Int64.ofNat nr) = true := by simp
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hoff with rfl | rfl
  · rw [show ((0 : Nat) == 0) = true from rfl, if_pos rfl, hgr]
    rcases b with _ | r
    · rw [Option.map_none, Option.getD_none, toUInt64_toInt64 (by omega), hfill, if_pos hnn, if_pos hlt,
        Option.map_none, Option.getD_none]
    · have hr := hb r rfl
      rw [Option.map_some, Option.getD_some, toUInt64_toInt64 (by omega), hfill, hne r hr, if_neg Bool.false_ne_true,
        Option.map_some, Option.getD_some, Nat.add_zero, hmax r (by omega)]
  · rw [show ((1 : Nat) == 0) = false from rfl, if_neg Bool.false_ne_true, hgr, hadd]
    rcases b with _ | r
    · rw [Option.map_none, Option.getD_none, toUInt64_toInt64 (by omega), hfill, if_pos hnn, hm1,
        ofNat_ne_min (by decide), Bool.or_false, if_neg Bool.false_ne_true, hneg, hmax 0 (by decide), Nat.max_zero,
        Option.map_none, Option.getD_none]
    · have hr := hb r rfl
      rw [Option.map_some, Option.getD_some, toUInt64_toInt64 (by omega), hfill, hne r hr, if_neg Bool.false_ne_true,
        ofNat_ne_min (by omega), ofNat_ne_min (by decide), Bool.or_false, if_neg Bool.false_ne_true,
        ← Int64.ofNat_add, hmax (r + 1) (by omega), Option.map_some, Option.getD_some]

/-- **`wjP`'s edge column**: `binRows`' words `E` (row or miss `nr`), `^ -1`, `+ off` where `off` is not `0`,
    then `starts |` it, is the natural `max (st i) (r + off)` at a hit and `st i` at a miss. -/
theorem wj_edge (E S : ByteArray) (n nr off : Nat) (bs : Nat → Option Nat) (st : Nat → Nat) (hn : n < USize.size)
    (hoff : off ≤ 1) (hnr : nr < 2 ^ 62) (hb : ∀ i r, i < n → bs i = some r → r < nr)
    (hst : ∀ i, i < n → st i < 2 ^ 62)
    (hE : ∀ i, i < n → Column.bitsAt E (i * 8) 8 = ((bs i).map Nat.toUInt64).getD nr.toUInt64)
    (hS : nats S = (List.range n).map st) :
    nats (Kernel.Ew.val Kernel.Ew.greater Kernel.Ew.i64 Kernel.Ew.vv Int64.minValue S
      (if off == 0 then
        Kernel.Ew.val Kernel.Ew.fill Kernel.Ew.i64 Kernel.Ew.av (Int64.ofNat nr) (Find.one (-1 : Int64).toUInt64) E
          n.toUSize
       else Kernel.Ew.val Kernel.Ew.add Kernel.Ew.i64 Kernel.Ew.va Int64.minValue
        (Kernel.Ew.val Kernel.Ew.fill Kernel.Ew.i64 Kernel.Ew.av (Int64.ofNat nr) (Find.one (-1 : Int64).toUInt64) E
          n.toUSize) (Find.one off.toUInt64) n.toUSize) n.toUSize) =
      (List.range n).map fun i => ((bs i).map (max (st i) <| · + off)).getD (st i) := by
  have hF : Verify.elemsW 8 (Kernel.Ew.val Kernel.Ew.fill Kernel.Ew.i64 Kernel.Ew.av (Int64.ofNat nr)
      (Find.one (-1 : Int64).toUInt64) E n.toUSize) = _ := val_i64_av Kernel.Ew.fill (Int64.ofNat nr) _ E n hn
  have hA : Verify.elemsW 8 (Kernel.Ew.val Kernel.Ew.add Kernel.Ew.i64 Kernel.Ew.va Int64.minValue
      (Kernel.Ew.val Kernel.Ew.fill Kernel.Ew.i64 Kernel.Ew.av (Int64.ofNat nr) (Find.one (-1 : Int64).toUInt64) E
        n.toUSize) (Find.one off.toUInt64) n.toUSize) = _ := Verify.val_i64_va Kernel.Ew.add Int64.minValue _ _ n hn
  unfold nats
  rw [Verify.val_i64_vv _ _ _ _ _ hn, List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.1 hi
  simp only [Function.comp_apply]
  have hSi : (Column.bitsAt S (i * 8) 8).toInt64 = Int64.ofNat (st i) := by
    have e := nats_get S (i := i) (by rw [← nats_length, hS]; simpa using hi)
    rw [hS, getElem!_range_map _ hi] at e
    rw [toInt64_eq_ofNat, ← e]
  have hFi := bitsAt_elemsW hF hi
  have hX : (Column.bitsAt (if off == 0 then
        Kernel.Ew.val Kernel.Ew.fill Kernel.Ew.i64 Kernel.Ew.av (Int64.ofNat nr) (Find.one (-1 : Int64).toUInt64) E
          n.toUSize
       else Kernel.Ew.val Kernel.Ew.add Kernel.Ew.i64 Kernel.Ew.va Int64.minValue
        (Kernel.Ew.val Kernel.Ew.fill Kernel.Ew.i64 Kernel.Ew.av (Int64.ofNat nr) (Find.one (-1 : Int64).toUInt64) E
          n.toUSize) (Find.one off.toUInt64) n.toUSize) (i * 8) 8).toInt64 =
      if off == 0 then
        Kernel.Ew.intStep Kernel.Ew.fill (Int64.ofNat nr) (-1) (((bs i).map Nat.toUInt64).getD nr.toUInt64).toInt64
      else Kernel.Ew.intStep Kernel.Ew.add Int64.minValue
        (Kernel.Ew.intStep Kernel.Ew.fill (Int64.ofNat nr) (-1) (((bs i).map Nat.toUInt64).getD nr.toUInt64).toInt64)
        (Int64.ofNat off) := by
    split
    · rw [hFi, Int64.toInt64_toUInt64, hE i hi]; rfl
    · rw [bitsAt_elemsW hA hi, Int64.toInt64_toUInt64, hFi, Int64.toInt64_toUInt64, hE i hi,
        toUInt64_toInt64 (by omega)]; rfl
  have hbi : ∀ r, bs i = some r → r < nr := fun r e => hb i r hi e
  rw [hSi, hX, wj_edge_word nr (st i) off (bs i) hbi hoff (hst i hi) hnr, ofNat_toUInt64_toNat]
  cases e : bs i with
  | none => have := hst i hi; simp only [Option.map_none, Option.getD_none]; omega
  | some r => have := hbi r e; have := hst i hi; simp only [Option.map_some, Option.getD_some]; omega

/-- **`wjP`'s counts `0 | hi - lo`** on naturals below `2^62`: `hi i - lo i`, `0` where `hi i < lo i`. -/
theorem wj_lens (H L : ByteArray) (n : Nat) (hi lo : Nat → Nat) (hn : n < USize.size)
    (hH : nats H = (List.range n).map hi) (hL : nats L = (List.range n).map lo)
    (hb : ∀ i, i < n → hi i < 2 ^ 62 ∧ lo i < 2 ^ 62) :
    nats (Kernel.Ew.val Kernel.Ew.greater Kernel.Ew.i64 Kernel.Ew.av Int64.minValue (Find.one 0)
      (Kernel.Ew.val Kernel.Ew.sub Kernel.Ew.i64 Kernel.Ew.vv Int64.minValue H L n.toUSize) n.toUSize) =
      (List.range n).map fun i => hi i - lo i := by
  have hv : Verify.elemsW 8 (Kernel.Ew.val Kernel.Ew.greater Kernel.Ew.i64 Kernel.Ew.av Int64.minValue (Find.one 0)
      (Kernel.Ew.val Kernel.Ew.sub Kernel.Ew.i64 Kernel.Ew.vv Int64.minValue H L n.toUSize) n.toUSize) = _ :=
    val_i64_av Kernel.Ew.greater Int64.minValue 0 _ n hn
  have hw : ∀ (B : ByteArray) (f : Nat → Nat), nats B = (List.range n).map f → ∀ i, i < n →
      (Column.bitsAt B (i * 8) 8).toInt64 = Int64.ofNat (f i) := fun B f hB i hi => by
    have e := nats_get B (i := i) (by rw [← nats_length, hB]; simpa using hi)
    rw [hB, getElem!_range_map _ hi] at e
    rw [toInt64_eq_ofNat, ← e]
  unfold nats
  rw [hv, List.map_map]
  apply List.map_congr_left
  intro i hi'
  have hi' := List.mem_range.1 hi'
  obtain ⟨h1, h2⟩ := hb i hi'
  simp only [Function.comp_apply]
  rw [bitsAt_elemsW (Verify.val_i64_vv Kernel.Ew.sub Int64.minValue H L n hn) hi', Int64.toInt64_toUInt64,
    hw H hi hH i hi', hw L lo hL i hi']
  have hsub : ∀ nul x y : Int64,
      Kernel.Ew.intStep Kernel.Ew.sub nul x y = if (x == nul || y == nul) then nul else x - y := fun _ _ _ => rfl
  have hgr : ∀ nul x y : Int64, Kernel.Ew.intStep Kernel.Ew.greater nul x y = if y < x then x else y :=
    fun _ _ _ => rfl
  rw [hsub, ofNat_ne_min (by omega), ofNat_ne_min (by omega), Bool.or_false, if_neg Bool.false_ne_true, hgr]
  have hd : (Int64.ofNat (hi i) - Int64.ofNat (lo i)).toInt = (hi i : Int) - lo i := by
    rw [Int64.toInt_sub, Int64.toInt_ofNat_of_lt (by omega), Int64.toInt_ofNat_of_lt (by omega), Int.bmod_def]
    split <;> omega
  have h0 : ({ toUInt64 := 0 } : Int64) = 0 := rfl
  have hz : (0 : Int64).toInt = 0 := rfl
  rw [Int64.toInt64_toUInt64, h0]
  split
  · rename_i hlt
    rw [Int64.lt_iff_toInt_lt, hd, hz] at hlt
    rw [show (0 : Int64).toUInt64.toNat = 0 from rfl]; omega
  · rename_i hge
    rw [Int64.lt_iff_toInt_lt, hd, hz] at hge
    have := toInt_toNat_word (u := (Int64.ofNat (hi i) - Int64.ofNat (lo i)).toUInt64) (by
      rw [Int64.toInt64_toUInt64, Int64.le_iff_toInt_le, hd, hz]; omega)
    rw [Int64.toInt64_toUInt64, hd] at this
    omega

/-- **`wjP`'s tail**: counts `c i` and starts `lo i`, `expand`ed, the rows `starts@I + W`, cut by
    `0, running sums`, are the runs `lo i + j`, `j < c i`. -/
theorem wj_tail {n N m : Nat} {los lens I W : ByteArray} {lo c : Nat → Nat} {A : Arr .long m} {P : Parted .long}
    (hlo : nats los = (List.range n).map lo) (hc : nats lens = (List.range n).map c)
    (hle : ∀ i, i < n → lo i + c i ≤ N) (hcN : ∀ i, c i ≤ N) (hU : n * N + n + N + 1 < USize.size)
    (hB : n * N + n + N < 2 ^ 63) (hIW : Find.expand lens = (I, W))
    (hA : A.enc = .bytes (Alg.add (Alg.gather 8 los I) W))
    (hP : Struct.partedP "wj" (Kernel.concatBytes #[Find.one 0, Alg.sums lens]) A = .ok P) :
    P.segs = (List.range n).map fun i => (List.range (c i)).map fun j => Int64.ofNat (lo i + j) := by
  obtain ⟨hIn, hWs, hWp⟩ := expand_nats lens c n N hc hcN hU hB
  rw [hIW] at hIn hWs hWp
  dsimp only at hIn hWs hWp
  have hSle : ((List.range n).map c).sum ≤ n * N := sum_range_le_mul c N hcN n
  have hIs : I.size / 8 = ((List.range n).map c).sum := by rw [← nats_length, hIn, List.length_flatMap]; simp
  have hpos : ∀ i w, i < n → w < c i → ((List.range i).map c).sum + w < I.size / 8 := fun i w hi hw => by
    have := sum_range_mono c (show i + 1 ≤ n by omega); rw [sum_range_succ] at this; omega
  have hIp : ∀ i w, i < n → w < c i → (nats I)[((List.range i).map c).sum + w]! = i := fun i w hi hw => by
    rw [hIn]
    exact get!_of_get? (by
      rw [blocks_get c (fun i => List.replicate (c i) i) (fun i => List.length_replicate ..) n hi hw,
        List.getElem?_replicate, if_pos hw])
  have hGs : (Alg.gather 8 los I).size / 8 = I.size / 8 := by
    rw [← nats_length, nats_gather, List.length_map, nats_length]
  have hG : ∀ i w, i < n → w < c i → (nats (Alg.gather 8 los I))[((List.range i).map c).sum + w]! = lo i :=
    fun i w hi hw => by
      rw [nats_gather, get!_map _ _ (by rw [nats_length]; exact hpos i w hi hw), hIp i w hi hw, hlo, getD_range_map,
        if_pos hi]
  have hX := nats_add (Alg.gather 8 los I) W (by rw [hGs]; omega) (by rw [hGs, hWs, hIs]) fun p hp => by
    rw [hGs, hIs] at hp
    obtain ⟨i, w, hi, hw, rfl⟩ := blocks_cover c n hp
    rw [hG i w hi hw, hWp i w hi hw]; have := hle i hi; omega
  rw [hGs, hIs] at hX
  have hrs : (Alg.add (Alg.gather 8 los I) W).size / 8 = ((List.range n).map c).sum := by
    rw [← nats_length, hX]; simp
  have hR : ∀ i w, i < n → w < c i →
      (nats (Alg.add (Alg.gather 8 los I) W))[((List.range i).map c).sum + w]! = lo i + w := fun i w hi hw => by
    rw [hX, getElem!_range_map _ (by have := hpos i w hi hw; omega), hG i w hi hw, hWp i w hi hw]
  -- the offsets `0, S 1, …, S n`
  have hss := nats_sums_range lens c n hc (by omega) (by omega)
  obtain ⟨g, o, co, hoB, rfl⟩ := Struct.parted_ok hP
  have hcat : nats (Kernel.concatBytes #[Find.one 0, Alg.sums lens]) =
      (List.range (n + 1)).map fun i => ((List.range i).map c).sum := by
    rw [show Kernel.concatBytes #[Find.one 0, Alg.sums lens] = (ByteArray.empty ++ Find.one 0) ++ Alg.sums lens from rfl,
      nats_append _ _ (by decide), nats_append _ _ (by decide), show nats ByteArray.empty = [] from rfl,
      show nats (Find.one 0) = [0] from rfl, hss, List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl
  have hg : g = n := by
    have := Arr.n_long_bytes o hoB
    rw [← nats_length, hcat] at this; simp at this; omega
  subst hg
  have hcR := cut_of_nats ⟨g, m, o, co, A⟩ hoB (f := fun i => ((List.range i).map c).sum) hcat
    fun r hr => by
      dsimp only at hr ⊢; have := sum_range_le_mul c N hcN r; have := Nat.mul_le_mul_right N hr; omega
  have hAt : A.toList = (Verify.elemsW 8 (Alg.add (Alg.gather 8 los I) W)).map UInt64.toInt64 :=
    Arr.toList_long A (by unfold longWords; rw [hA])
  rw [segs_cuts]
  apply List.ext_getElem (by simp)
  intro r h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range]
  rw [hcR r (by dsimp only; omega), hcR (r + 1) (by dsimp only; omega)]
  dsimp only
  rw [sum_range_succ, Nat.add_sub_cancel_left]
  refine List.map_congr_left fun w hw => ?_
  have hw := List.mem_range.1 hw
  have hp := hR r w h1 hw
  have hq := hpos r w h1 hw
  unfold nats at hp
  rw [get!_map _ _ (by simp [Verify.elemsW]; omega)] at hp
  rw [hAt, get!_map _ _ (by simp [Verify.elemsW]; omega), toInt64_eq_ofNat, hp]

/-- `wj1`'s lower bound `w₀ - 1` as `wjP` builds it on a dense long window: `dyadColumn .sub` against the atom
    `1` is the one-stage `eVal` chain, answered encoded or dense, and either way its words are `w₀[i] - 1` under
    q's null rule (`0N - 1 = 0N`). -/
theorem dyadColumn_sub_one {n : Nat} {b0 : ByteArray} (hn : n < USize.size) (hb : b0.size / 8 = n) :
    ∃ L bL, Kernel.dyadColumn .sub Kernel.Ew.va .long .long n (.bytes b0) 1 (.bytes (Find.one 1)) =
      some (.long, .vector .long n L none) ∧ Enc.bytesOf .long n L = some bL ∧ bL.size / 8 = n ∧
      ∀ i, i < n → (Column.bitsAt bL (i * 8) 8).toInt64 =
        Kernel.Ew.intStep Kernel.Ew.sub Int64.minValue (Column.bitsAt b0 (i * 8) 8).toInt64 1 := by
  rw [dyadColumn_long_va (v := .sub) rfl (by decide) rfl n b0 (Find.one 1)]
  have hN : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' hn
  have hrun := (Verify.run_val ({ inputs := #[b0, Find.one 1] } : Kernel.Ew.Build) rfl Kernel.Ew.sub Kernel.Ew.i64
    Kernel.Ew.va 0 1 (Kernel.nullPayload .long) (by decide) (by decide) n.toUSize).trans (show _ =
      Kernel.Ew.val Kernel.Ew.sub Kernel.Ew.i64 Kernel.Ew.va Int64.minValue b0 (Kernel.atomBytes Kernel.Ew.i64 1)
        n.toUSize from rfl)
  have hv := Verify.val_i64_va Kernel.Ew.sub Int64.minValue b0 1 n hn
  rw [← hrun] at hv
  have hs := congrArg List.length hv
  simp only [Verify.elemsW, List.length_map, List.length_range] at hs
  have he := Verify.runEnc_elems _ _ n.toUSize 8 (by decide) (by decide) n.toUSize (by rw [hN, hs])
  rw [hv] at he
  refine ⟨_, _, rfl, ?_, ?_, fun i hi => by rw [bitsAt_elemsW he hi, Int64.toInt64_toUInt64]; rfl⟩
  · have hp : ∀ x, Kernel.payload .long n.toUSize x = Enc.answer .long n
        (.foR (x.1.runEnc x.2 n.toUSize (8 : Nat).toUSize).1 (x.1.runEnc x.2 n.toUSize (8 : Nat).toUSize).2) :=
      fun x => by simp only [Kernel.payload, hN]; rfl
    rw [hp]
    rcases Verify.answer_foR .long 8 n _ _ rfl with e | e <;> rw [e] <;> rfl
  · have := congrArg List.length he
    simp only [Verify.elemsW, List.length_map, List.length_range] at this
    exact this

/-- `wj1`'s lower bound `w₀ - 1` on a `foR` long window: `dyadColumn .sub` against the atom `1` is `foRShift` of
    `-1`, or `foRValAtom`'s dense pass where that declines; either way its words are q's `w₀[i] - 1` over the
    decoded window. -/
theorem dyadColumn_sub_one_foR {n : Nat} {md pk : ByteArray} (hn : n < USize.size) :
    ∃ L bL, Kernel.dyadColumn .sub Kernel.Ew.va .long .long n (.foR md pk) 1 (.bytes (Find.one 1)) =
      some (.long, .vector .long n L none) ∧ Enc.bytesOf .long n L = some bL ∧ bL.size / 8 = n ∧
      ∀ i, i < n → (Column.bitsAt bL (i * 8) 8).toInt64 = Kernel.Ew.intStep Kernel.Ew.sub Int64.minValue
        (Column.bitsAt (Kernel.Coc.decode (8 : Nat).toUSize md pk n.toUSize) (i * 8) 8).toInt64 1 := by
  rw [dyadColumn_long_va_sub_foR n md pk (Find.one 1)]
  have h1 : (Kernel.Ew.elem Kernel.Ew.i64 (Find.one 1) 0).toInt64 = 1 := by decide
  have hN : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' hn
  have hadd : ∀ nul x y : Int64, Kernel.Ew.intStep Kernel.Ew.add nul x y = if (x == nul || y == nul) then nul else x + y :=
    fun _ _ _ => rfl
  have hsub : ∀ nul x y : Int64, Kernel.Ew.intStep Kernel.Ew.sub nul x y = if (x == nul || y == nul) then nul else x - y :=
    fun _ _ _ => rfl
  split
  · rename_i m p' heq
    have hs := Verify.foRShift_spec false _ md pk n.toUSize m p' heq
    simp only [Bool.false_eq_true, ↓reduceIte] at hs
    have hv := Verify.val_i64_va Kernel.Ew.add Int64.minValue (Kernel.Coc.decode 8 md pk n.toUSize)
      (-(Kernel.Ew.elem Kernel.Ew.i64 (Find.one 1) 0).toInt64).toUInt64 n hn
    rw [show Kernel.atomBytes Kernel.Ew.i64 (-(Kernel.Ew.elem Kernel.Ew.i64 (Find.one 1) 0).toInt64).toUInt64 =
      Column.pushBits ByteArray.empty (-(Kernel.Ew.elem Kernel.Ew.i64 (Find.one 1) 0).toInt64).toUInt64 8 from rfl,
      ← hs] at hv
    have hsz := (Verify.decodeW 8 (by simp) m p' n.toUSize).1
    rw [hN] at hsz
    refine ⟨_, Kernel.Coc.decode 8 m p' n.toUSize, rfl, ?_, ?_, fun i hi => ?_⟩
    · rcases Verify.answer_foR .long 8 n m p' rfl with e | e <;> rw [e] <;> rfl
    · rw [hsz]; simp
    · rw [bitsAt_elemsW hv hi, Int64.toInt64_toUInt64, Int64.toInt64_toUInt64, h1, hadd, hsub, Int64.sub_eq_add_neg]
      rfl
  · have hv : Verify.elemsW 8 (Kernel.Ew.foRValAtom Kernel.Ew.sub Kernel.Ew.i64 Kernel.Ew.va (Kernel.nullPayload .long)
        md pk n.toUSize (Kernel.atomBytes Kernel.Ew.i64 (Kernel.Ew.elem Kernel.Ew.i64 (Find.one 1) 0))) =
        (List.range n).map fun i => (Kernel.Ew.intStep Kernel.Ew.sub Int64.minValue
          (Column.bitsAt (Kernel.Coc.decode (8 : Nat).toUSize md pk n.toUSize) (i * 8) 8).toInt64
          (Kernel.Ew.elem Kernel.Ew.i64 (Find.one 1) 0).toInt64).toUInt64 :=
      Verify.val_i64_va Kernel.Ew.sub Int64.minValue _ _ n hn
    generalize Kernel.Ew.foRValAtom Kernel.Ew.sub Kernel.Ew.i64 Kernel.Ew.va (Kernel.nullPayload .long)
      md pk n.toUSize (Kernel.atomBytes Kernel.Ew.i64 (Kernel.Ew.elem Kernel.Ew.i64 (Find.one 1) 0)) = V at hv ⊢
    have hl := congrArg List.length hv
    simp only [Verify.elemsW, List.length_map, List.length_range] at hl
    obtain ⟨B, hB, hBw, hBn⟩ := bytesOf_longWords hn (longWords_answer V hl) (by simp [Verify.elemsW]; omega)
    refine ⟨_, B, rfl, hB, hBn, fun i hi => ?_⟩
    rw [bitsAt_elemsW (hBw.trans hv) hi, Int64.toInt64_toUInt64, h1]

/-- **`wj` and `wj1` are `wjSpec` once their groups are known**: where `keyGroups` answers groups `gs` and ids
    that `KeyAnswers` the two sides' keys, `wjP` over dense long windows `b0`, `b1` and times `hay` answers
    `wjSpec`'s runs. `L` is the column `wjP` bins the lower edge at — `t0` itself (`wj`) or its `dyadColumn`
    `- 1` (`wj1`), words `bL`. Nothing is assumed about the times' order inside a group. -/
theorem wj_groups {κ : Type} [BEq κ] [Inhabited κ] {l r : Array Struct.KCol} {t0 t1 tr L : Nat × Enc}
    {P : Parted .long} {gs : Eval.Groups} {ids : Nat × Enc} {b0 bL b1 hay gids : ByteArray} (prevailing : Bool)
    (lk rk : List κ)
    (hL : if prevailing then L = t0 else Kernel.dyadColumn .sub Kernel.Ew.va .long .long t0.1 t0.2 1
      (.bytes (Find.one 1)) = some (.long, .vector .long L.1 L.2 none))
    (hLb : Enc.bytesOf .long L.1 L.2 = some bL) (hLn : bL.size / 8 = t0.1)
    (hLw : ∀ i, i < t0.1 → (Column.bitsAt bL (i * 8) 8).toInt64 =
      if prevailing then (Column.bitsAt b0 (i * 8) 8).toInt64
      else Kernel.Ew.intStep Kernel.Ew.sub Int64.minValue (Column.bitsAt b0 (i * 8) 8).toInt64 1)
    (h1b : Enc.bytesOf .long t1.1 t1.2 = some b1) (hrb : Enc.bytesOf .long tr.1 tr.2 = some hay)
    (hgb : Enc.bytesOf .long ids.1 ids.2 = some gids) (h0n : b0.size / 8 = t0.1) (h1n : b1.size / 8 = t0.1)
    (hrn : hay.size / 8 = tr.1) (hlk : lk.length = t0.1) (hrk : rk.length = tr.1)
    (hU : t0.1 * tr.1 + t0.1 + tr.1 + 1 < USize.size) (h62 : t0.1 * tr.1 + t0.1 + tr.1 < 2 ^ 62)
    (hkg : Struct.keyGroups "wj" l r t0.1 tr.1 = .ok (gs, ids)) (hk : KeyAnswers rk lk gs ids)
    (h : Struct.wjP prevailing ⟨.long, t0⟩ ⟨.long, t1⟩ l r ⟨.long, tr⟩ = .ok P) :
    P.segs = Struct.wjRuns prevailing lk ((nats b0).map Int64.ofNat) ((nats b1).map Int64.ofNat) rk
      ((nats hay).map Int64.ofNat) := by
  obtain ⟨g', hg', hgn, hst, -⟩ := id hk
  rw [Option.some.inj (hg'.symm.trans hgb)] at hgn hst
  have hE0 := groupEdge_long gs ids tr L tr.1 hrb hLb hgb (by omega)
  have hE1 := groupEdge_long gs ids tr t1 tr.1 hrb h1b hgb (by omega)
  have hdo : ∀ X, Find.dense "wj" .long ids.1 (.bytes X) = .ok X := fun X => by
    simp [Find.dense, Enc.bytesOf]
  have hdi : Find.dense "wj" .long ids.1 ids.2 = .ok gids := by simp [Find.dense, hgb]
  have hN : tr.1 < 2 ^ 62 := by omega
  have hn : t0.1 < USize.size := by omega
  have hst' : nats (Alg.gather 8 (Kernel.longBytes (gs.firsts.push 0)) gids) =
      (List.range t0.1).map fun i => (Struct.group rk lk[i]!).head?.getD 0 := by rw [hst, hlk]
  have hgr : ∀ k s, s ∈ Struct.group rk k → s < tr.1 := fun k s hs => by
    simp only [Struct.group, List.mem_filter, List.mem_range] at hs; omega
  have hhd : ∀ k, (Struct.group rk k).head?.getD 0 ≤ tr.1 := fun k => by
    cases e : (Struct.group rk k).head? with
    | none => exact Nat.zero_le _
    | some s => have := hgr k s (List.mem_of_mem_head? e); exact Nat.le_of_lt this
  have hbin : ∀ (b : ByteArray) i r, Struct.binSpec ((nats hay).map Int64.ofNat) (Struct.group rk lk[i]!)
      (Column.bitsAt b (i * 8) 8).toInt64 = some r → r < tr.1 := fun b i r e => hgr _ r (binSpec_mem e)
  have hEw : ∀ (b : ByteArray), b.size / 8 = t0.1 → ∀ i, i < t0.1 →
      Column.bitsAt (Kernel.binRows 8 false true false hay b gs.rows (Kernel.longBytes gs.bounds) gids tr.1.toUInt64)
        (i * 8) 8 = ((Struct.binSpec ((nats hay).map Int64.ofNat) (Struct.group rk lk[i]!)
          (Column.bitsAt b (i * 8) 8).toInt64).map Nat.toUInt64).getD tr.1.toUInt64 := fun b hb i hi => by
    have := binRows_group (keys := b) hk hgb (by omega) hrn hrk (i := i) (by omega)
    rwa [Nat.mul_comm 8 i] at this
  -- an edge, `max s (r + off)` at a hit and `s` at a miss, is a right row or the end `nr`
  have hedge : ∀ (b : ByteArray) off i, off ≤ 1 → ((Struct.binSpec ((nats hay).map Int64.ofNat)
      (Struct.group rk lk[i]!) (Column.bitsAt b (i * 8) 8).toInt64).map
        (max ((Struct.group rk lk[i]!).head?.getD 0) <| · + off)).getD ((Struct.group rk lk[i]!).head?.getD 0) ≤ tr.1 :=
    fun b off i ho => by
      have := hhd lk[i]!
      cases e : Struct.binSpec ((nats hay).map Int64.ofNat) (Struct.group rk lk[i]!)
        (Column.bitsAt b (i * 8) 8).toInt64 with
      | none => simp only [Option.map_none, Option.getD_none]; exact this
      | some r => have := hbin b i r e; simp only [Option.map_some, Option.getD_some]; omega
  have e0 := wj_edge _ _ t0.1 tr.1 (if prevailing then 0 else 1)
    (fun i => Struct.binSpec ((nats hay).map Int64.ofNat) (Struct.group rk lk[i]!) (Column.bitsAt bL (i * 8) 8).toInt64)
    (fun i => (Struct.group rk lk[i]!).head?.getD 0) hn (by cases prevailing <;> decide) hN
    (fun i r _ e => hbin bL i r e) (fun i _ => by have := hhd lk[i]!; dsimp only; omega) (hEw bL hLn) hst'
  have e1 := wj_edge _ _ t0.1 tr.1 1
    (fun i => Struct.binSpec ((nats hay).map Int64.ofNat) (Struct.group rk lk[i]!) (Column.bitsAt b1 (i * 8) 8).toInt64)
    (fun i => (Struct.group rk lk[i]!).head?.getD 0) hn (by decide) hN (fun i r _ e => hbin b1 i r e)
    (fun i _ => by have := hhd lk[i]!; dsimp only; omega) (hEw b1 h1n) hst'
  have hc := wj_lens _ _ t0.1 _ _ hn e1 e0 fun i _ => by
    have := hedge bL (if prevailing then 0 else 1) i (by cases prevailing <;> decide)
    have := hedge b1 1 i (by decide); dsimp only; exact ⟨by omega, by omega⟩
  have hw : ∀ (b : ByteArray), b.size / 8 = t0.1 → ∀ i, i < t0.1 →
      ((nats b).map Int64.ofNat)[i]! = (Column.bitsAt b (i * 8) 8).toInt64 := fun b hb i hi => by
    rw [get!_map _ _ (by rw [nats_length]; omega), nats_get b (by omega), toInt64_eq_ofNat]
  -- the lower edge's bound: `t0` itself, or `wj1`'s `t0 - 1`, after which both cases run alike
  cases prevailing
  simp only [Bool.false_eq_true, ↓reduceIte] at hL hLw e0 hc
  simp only [Struct.wjP, Struct.colRows, Struct.colValue, hkg, hL, hE0, hE1, hdo, hdi,
    beq_self_eq_true, Bool.and_self, ↓reduceIte, Bool.false_eq_true, bind, Except.bind, pure, Except.pure] at h
  rotate_left
  simp only [↓reduceIte] at hL hLw e0 hc
  subst hL
  simp only [Struct.wjP, Struct.colRows, Struct.colValue, hkg, hE0, hE1, hdo, hdi,
    beq_self_eq_true, Bool.and_self, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
  rotate_left
  all_goals
    split at h
    · cases h
    rename_i v hv
    have hseg := wj_tail (N := tr.1) e0 hc (fun i _ => by
        have := hedge bL 0 i (by decide); have := hedge bL 1 i (by decide); have := hedge b1 1 i (by decide)
        try dsimp only
        omega)
      (fun i => by have := hedge b1 1 i (by decide); (try dsimp only); omega) hU (by omega) rfl (ofPart_enc hv) h
    rw [hseg, Struct.wjRuns, hlk]
    apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.1 hi
    unfold Struct.wjRun
    dsimp only
    rw [hLw i hi, hw b0 h0n i hi, hw b1 h1n i hi]
    cases e : (Struct.group rk lk[i]!).head? with
    | none =>
      have hg : Struct.group rk lk[i]! = [] := List.head?_eq_none_iff.1 e
      have hb : ∀ x, Struct.binSpec ((nats hay).map Int64.ofNat) (Struct.group rk lk[i]!) x = none := fun x => by
        cases e' : Struct.binSpec ((nats hay).map Int64.ofNat) (Struct.group rk lk[i]!) x with
        | none => rfl
        | some r => have := binSpec_mem e'; rw [hg] at this; cases this
      simp only [hb, Option.map_none, Option.getD_none, Nat.sub_self, List.range_zero, List.map_nil]
    | some s => simp only [Option.getD_some, ↓reduceIte, Bool.false_eq_true]

/-- **`wj` is `wjSpec`** at one long key column per side, the right one's mark as `aj_long` admits (`prevailing`,
    q's `wj`): the key side from `keyMatch_answers`, both edges from `binRows` inside the key group. -/
theorem wj_long {cl cr t0 t1 tr : Nat × Enc} {wl wr : List UInt64} {P : Parted .long} {b0 b1 hay : ByteArray}
    (hwl : longWords cl.1 cl.2 = some wl) (hwr : longWords cr.1 cr.2 = some wr)
    (hln : wl.length = cl.1) (hrn : wr.length = cr.1) (hcl : cl.1 = t0.1) (hcr : cr.1 = tr.1)
    (hlwf : Enc.WF .long cl.1 cl.2) (hlR : Find.Readable .long cl.1 cl.2)
    (hrwf : Enc.WF .long cr.1 cr.2) (hrR : Find.Readable .long cr.1 cr.2)
    (h0b : Enc.bytesOf .long t0.1 t0.2 = some b0) (h1b : Enc.bytesOf .long t1.1 t1.2 = some b1)
    (hrb : Enc.bytesOf .long tr.1 tr.2 = some hay)
    (h0n : b0.size / 8 = t0.1) (h1n : b1.size / 8 = t0.1) (hhn : hay.size / 8 = tr.1)
    (hU : t0.1 * tr.1 + t0.1 + tr.1 + 1 < USize.size) (h62 : t0.1 * tr.1 + t0.1 + tr.1 + 1 < 2 ^ 62)
    (h : Struct.wjP true ⟨.long, t0⟩ ⟨.long, t1⟩ #[⟨.long, cl⟩] #[⟨.long, cr⟩] ⟨.long, tr⟩ = .ok P) :
    P.segs = Struct.wjRuns true wl ((nats b0).map Int64.ofNat) ((nats b1).map Int64.ofNat) wr
      ((nats hay).map Int64.ofNat) := by
  have hkg : Struct.keyGroups "wj" #[⟨.long, cl⟩] #[⟨.long, cr⟩] t0.1 tr.1 =
      .ok (Eval.keyMatch #[.vector .long cr.1 cr.2 none] tr.1 #[.vector .long cl.1 cl.2 none] t0.1) := by
    simp [Struct.keyGroups, Struct.colRows, Struct.colValue, hcl, hcr] <;> rfl
  -- a key column carries no attribute (`colValue` answers it bare), so `hattr`'s `none` arm is all there is
  have hk := keyMatch_answers tr.1 t0.1 hwr hrn (by omega) (by omega) hrwf hrR (by omega) hlwf hlR hwl
    hln hcr.symm (by omega) (by omega) (ar := none) (al := none) (fun _ _ h => by cases h)
  obtain ⟨gids, hgb, -⟩ := id hk
  exact wj_groups (L := t0) (bL := b0) true wl wr rfl h0b h0n (fun _ _ => (if_pos rfl).symm) h1b hrb hgb h0n
    h1n hhn (by omega) (by omega) hU (by omega) hkg hk h

/-- **`wj1` is `wjSpec false`** at one long key column per side, the right one's mark as in `wj_long` (q's `wj1`): as `wj_long`,
    the lower edge binned at `w₀ - 1`, q's subtraction in both: `dyadColumn_sub_one` on a dense window,
    `dyadColumn_sub_one_foR` on a `foR` one, whose words `b0` are its decode (`hb0`). -/
theorem wj1_long {cl cr t0 t1 tr : Nat × Enc} {wl wr : List UInt64} {P : Parted .long} {b0 b1 hay : ByteArray}
    (hwl : longWords cl.1 cl.2 = some wl) (hwr : longWords cr.1 cr.2 = some wr)
    (hln : wl.length = cl.1) (hrn : wr.length = cr.1) (hcl : cl.1 = t0.1) (hcr : cr.1 = tr.1)
    (hlwf : Enc.WF .long cl.1 cl.2) (hlR : Find.Readable .long cl.1 cl.2)
    (hrwf : Enc.WF .long cr.1 cr.2) (hrR : Find.Readable .long cr.1 cr.2)
    (hb0 : t0.2 = .bytes b0 ∨ ∃ md pk, t0.2 = .foR md pk ∧ b0 = Kernel.Coc.decode (8 : Nat).toUSize md pk t0.1.toUSize)
    (h1b : Enc.bytesOf .long t1.1 t1.2 = some b1) (hrb : Enc.bytesOf .long tr.1 tr.2 = some hay)
    (h0n : b0.size / 8 = t0.1) (h1n : b1.size / 8 = t0.1) (hhn : hay.size / 8 = tr.1)
    (hU : t0.1 * tr.1 + t0.1 + tr.1 + 1 < USize.size) (h62 : t0.1 * tr.1 + t0.1 + tr.1 + 1 < 2 ^ 62)
    (h : Struct.wjP false ⟨.long, t0⟩ ⟨.long, t1⟩ #[⟨.long, cl⟩] #[⟨.long, cr⟩] ⟨.long, tr⟩ = .ok P) :
    P.segs = Struct.wjRuns false wl ((nats b0).map Int64.ofNat) ((nats b1).map Int64.ofNat) wr
      ((nats hay).map Int64.ofNat) := by
  have hkg : Struct.keyGroups "wj" #[⟨.long, cl⟩] #[⟨.long, cr⟩] t0.1 tr.1 =
      .ok (Eval.keyMatch #[.vector .long cr.1 cr.2 none] tr.1 #[.vector .long cl.1 cl.2 none] t0.1) := by
    simp [Struct.keyGroups, Struct.colRows, Struct.colValue, hcl, hcr] <;> rfl
  have hk := keyMatch_answers tr.1 t0.1 hwr hrn (by omega) (by omega) hrwf hrR (by omega) hlwf hlR hwl
    hln hcr.symm (by omega) (by omega) (ar := none) (al := none) (fun _ _ h => by cases h)
  obtain ⟨gids, hgb, -⟩ := id hk
  obtain ⟨Le, bL, hd, hLb, hLn, hLw⟩ : ∃ Le bL, Kernel.dyadColumn .sub Kernel.Ew.va .long .long t0.1 t0.2 1
      (.bytes (Find.one 1)) = some (.long, .vector .long t0.1 Le none) ∧ Enc.bytesOf .long t0.1 Le = some bL ∧
      bL.size / 8 = t0.1 ∧ ∀ i, i < t0.1 → (Column.bitsAt bL (i * 8) 8).toInt64 =
        Kernel.Ew.intStep Kernel.Ew.sub Int64.minValue (Column.bitsAt b0 (i * 8) 8).toInt64 1 := by
    have hn0 : t0.1 < USize.size := by omega
    obtain ⟨n, e⟩ := t0
    simp only at hb0 h0n hn0 ⊢
    rcases hb0 with rfl | ⟨md, pk, rfl, rfl⟩
    · exact dyadColumn_sub_one hn0 h0n
    · exact dyadColumn_sub_one_foR hn0
  refine wj_groups (L := (t0.1, Le)) false wl wr hd hLb hLn (fun i hi => ?_) h1b hrb hgb h0n h1n hhn
    (by omega) (by omega) hU (by omega) hkg hk h
  rw [hLw i hi, if_neg Bool.false_ne_true]

/-- `wj`'s window, `Wᵥ` with both ends moving: left row `i` to the right rows `j` with `lo i ≤ j < hi i`. -/
def winAt (lo hi : Nat → Nat) : Idx ⟶ Idx := fun i j => lo i ≤ j ∧ j < hi i

/-- The window aggregate read on a list `xs`: at `i < m`, `f` of the rows `[lo i, hi i)` of `xs`, is
    `corefl(<m) ≫ Λ(winAt lo hi) ≫ enum ≫ list(xs) ≫ f`. -/
theorem ix_winAt {α β : Type} (xs : List α) (m : Nat) (lo hi : Nat → Nat)
    (hb : ∀ i, i < m → lo i ≤ xs.length ∧ hi i ≤ xs.length) (f : CL.ConsList Unit α → β) :
    ix ((List.range m).map fun i => f (CL.ofList ((xs.drop (lo i)).take (hi i - lo i))))
      = corefl (· < m) ≫ Λ (winAt lo hi) ≫ enum ≫ ListRel.list (ix xs)
          ≫ (graph f : ListRel.dList α ⟶ (⟨β⟩ : RelSet.{0})) :=
  hom_ext fun (i : Nat) c => by
    show ((List.range m).map _)[i]? = some c ↔
      ∃ z, (i = z ∧ i < m) ∧ ∃ s, Λ (winAt lo hi) z s ∧ ∃ zs, enum s zs ∧ ∃ ws, ListRel.listP (ix xs) zs ws ∧ c = f ws
    by_cases him : i < m
    · have hl : lo i + (hi i - lo i) ≤ xs.length := by have := hb i him; omega
      have hW : ∀ ys, (Λ (winAt lo hi) ≫ enum) i ys ↔ ys = CL.ofList (List.range' (lo i) (hi i - lo i)) :=
        Λ_enum _ fun j => show lo i ≤ j ∧ j < hi i ↔ _ by omega
      rw [List.getElem?_map, List.getElem?_range him, Option.map_some, Option.some.injEq]
      constructor
      · intro e
        obtain ⟨s, hs, he⟩ := (hW _).2 rfl
        exact ⟨i, ⟨rfl, him⟩, s, hs, _, he, _, (listP_ix_range' xs _ _ hl _).2 rfl, e.symm⟩
      · rintro ⟨_, ⟨rfl, -⟩, s, hs, zs, hz, ws, hw, rfl⟩
        rw [(hW zs).1 ⟨s, hs, hz⟩] at hw
        rw [(listP_ix_range' xs _ _ hl ws).1 hw]
    · rw [List.getElem?_eq_none (by simp only [List.length_map, List.length_range]; omega)]
      exact ⟨(fun e => nomatch e), by rintro ⟨_, ⟨_, h⟩, -⟩; exact absurd h him⟩

/-- `wjSpec`'s edge of left row `i` at the bounds `w`: `max s (r + off)` where `bin` names the row `r` in the
    key's group, `s` (the group's first row) where it names none, `0` for a key with no right rows. -/
def wjEdge {κ : Type} [BEq κ] [Inhabited κ] (lk rk : List κ) (rt w : List Int64) (off i : Nat) : Nat :=
  match (Struct.group rk lk[i]!).head? with
  | none => 0
  | some s => ((Struct.binSpec rt (Struct.group rk lk[i]!) w[i]!).map (max s <| · + off)).getD s

/-- **`wjSpec` is a window per left row** (`prevailing`): row `i`'s run is the right rows `[lo i, hi i)` between
    its two `wjEdge`s, both inside `rk`, so the aggregate over it is `ix_winAt`'s
    `Λ(winAt lo hi) ≫ enum ≫ list(xs) ≫ f`. `wjEdge_est` reads the edges as `est(≥)` of the candidates. -/
theorem wjSpec_runs {κ : Type} [BEq κ] [Inhabited κ] (lk : List κ) (w₀ w₁ : List Int64) (rk : List κ)
    (rt : List Int64) :
    (∀ i, wjEdge lk rk rt w₀ 0 i ≤ rk.length ∧ wjEdge lk rk rt w₁ 1 i ≤ rk.length) ∧
      Struct.wjSpec true lk w₀ w₁ rk rt = Struct.runsSpec ((List.range lk.length).map fun i =>
        (List.range' (wjEdge lk rk rt w₀ 0 i) (wjEdge lk rk rt w₁ 1 i - wjEdge lk rk rt w₀ 0 i)).map Int64.ofNat) := by
  have hgr : ∀ k s, s ∈ Struct.group rk k → s < rk.length := fun k s hs => by
    simp only [Struct.group, List.mem_filter, List.mem_range] at hs; omega
  have hb : ∀ (w : List Int64) (off i : Nat), off ≤ 1 → wjEdge lk rk rt w off i ≤ rk.length :=
    fun w off i ho => by
      unfold wjEdge
      cases e : (Struct.group rk lk[i]!).head? with
      | none => exact Nat.zero_le _
      | some s =>
        have := hgr _ s (List.mem_of_mem_head? e)
        cases e' : Struct.binSpec rt (Struct.group rk lk[i]!) w[i]! with
        | none => simp only [Option.map_none, Option.getD_none]; omega
        | some r =>
          have := hgr _ r (binSpec_mem e'); simp only [Option.map_some, Option.getD_some]
          rw [Nat.max_def]; split <;> omega
  refine ⟨fun i => ⟨hb _ 0 i (by decide), hb _ 1 i (by decide)⟩, ?_⟩
  unfold Struct.wjSpec Struct.wjRuns wjEdge
  congr 1
  apply List.map_congr_left
  intro i _
  unfold Struct.wjRun
  dsimp only
  cases (Struct.group rk lk[i]!).head? with
  | none => rfl
  | some s =>
    simp only [↓reduceIte, List.range'_eq_map_range, List.map_map]
    try rfl

/-- Left row `i`'s candidates at the bounds `w`: the rows of its key's group whose time is at most `w[i]`. -/
def cand {κ : Type} [BEq κ] [Inhabited κ] (lk rk : List κ) (rt w : List Int64) : Idx ⟶ Idx :=
  fun i j => j ∈ Struct.group rk lk[i]! ∧ rt[j]! ≤ w[i]!

/-- On an ascending list the last element is the one at or above every element. -/
theorem getLast?_greatest {L : List Nat} (hp : L.Pairwise (· < ·)) (r : Nat) :
    L.getLast? = some r ↔ r ∈ L ∧ ∀ z, z ∈ L → r ≥ z := by
  have fwd : ∀ r, L.getLast? = some r → r ∈ L ∧ ∀ z, z ∈ L → r ≥ z := fun r h => by
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 h
    refine ⟨by simp, fun z hz => ?_⟩
    rcases List.mem_append.1 hz with hz | hz
    · exact Nat.le_of_lt ((List.pairwise_append.1 hp).2.2 z hz r (by simp))
    · simp only [List.mem_singleton] at hz; omega
  refine ⟨fwd r, fun ⟨hr, hm⟩ => ?_⟩
  cases h : L.getLast? with
  | none => rw [List.getLast?_eq_none_iff] at h; subst h; cases hr
  | some r' => obtain ⟨hr', hm'⟩ := fwd r' h; have := hm r' hr'; have := hm' r hr; congr 1; omega

/-- **`bin` in an ascending group is `est(≥)` of the candidates**: where the group's times ascend, `binSpec` at
    `w[i]` names `r` iff `r` is the greatest of left row `i`'s candidates, `Λ(cand) ≫ est(≥)`. -/
theorem binSpec_est {κ : Type} [BEq κ] [Inhabited κ] (lk rk : List κ) (rt w : List Int64) (i r : Nat)
    (hs : (Struct.group rk lk[i]!).Pairwise fun a b => rt[a]! ≤ rt[b]!) :
    Struct.binSpec rt (Struct.group rk lk[i]!) w[i]! = some r ↔ (Λ (cand lk rk rt w) ≫ est (· ≥ ·)) i r := by
  have hp : ((Struct.group rk lk[i]!).filter fun j => decide (rt[j]! ≤ w[i]!)).Pairwise (· < ·) :=
    ((List.pairwise_lt_range).filter _).filter _
  have hc : ∀ j, cand lk rk rt w i j ↔ j ∈ (Struct.group rk lk[i]!).filter fun j => decide (rt[j]! ≤ w[i]!) :=
    fun j => by simp only [cand, List.mem_filter, decide_eq_true_eq]
  rw [binSpec_sorted _ _ _ hs, RelSet.Λ_comp_est_apply, getLast?_greatest hp, hc]
  exact and_congr_right fun _ => forall_congr' fun z => by rw [hc]

/-- **`wj`'s edges are `est(≥)` of the candidates** where the key's group (first row `s`) ascends in time: the
    greatest candidate `r` gives the edge `max s (r + off)`, and no candidate gives `s`. -/
theorem wjEdge_est {κ : Type} [BEq κ] [Inhabited κ] (lk rk : List κ) (rt w : List Int64) (off i s : Nat)
    (hh : (Struct.group rk lk[i]!).head? = some s)
    (hs : (Struct.group rk lk[i]!).Pairwise fun a b => rt[a]! ≤ rt[b]!) :
    (∀ r, (Λ (cand lk rk rt w) ≫ est (· ≥ ·)) i r → wjEdge lk rk rt w off i = max s (r + off)) ∧
      ((∀ r, ¬ (Λ (cand lk rk rt w) ≫ est (· ≥ ·)) i r) → wjEdge lk rk rt w off i = s) := by
  unfold wjEdge
  simp only [hh]
  refine ⟨fun r h => by rw [(binSpec_est lk rk rt w i r hs).2 h]; rfl, fun h => ?_⟩
  cases e : Struct.binSpec rt (Struct.group rk lk[i]!) w[i]! with
  | none => rfl
  | some r => exact absurd ((binSpec_est lk rk rt w i r hs).1 e) (h r)

/-- **A window is a range of right rows, so a group that is not contiguous mixes keys**: left key `0`'s run
    `[0, 3)` holds row `1`, of key `1`. -/
theorem wjSpec_mixes : Struct.wjSpec true [0] [1] [3] [0, 1, 0] [1, 2, 3] = Struct.runsSpec [[0, 1, 2]] := by decide

/-- **On a contiguous group the window stays inside it**: where key `lk[i]`'s right rows are `[s, s + c)`, every
    row between `wj`'s two edges is in the group. -/
theorem wjEdge_contig {κ : Type} [BEq κ] [Inhabited κ] (lk rk : List κ) (rt w₀ w₁ : List Int64) (i s c j : Nat)
    (hc : 0 < c) (hg : Struct.group rk lk[i]! = List.range' s c) (h0 : wjEdge lk rk rt w₀ 0 i ≤ j)
    (h1 : j < wjEdge lk rk rt w₁ 1 i) : j ∈ Struct.group rk lk[i]! := by
  have hh : (Struct.group rk lk[i]!).head? = some s := by
    rw [hg]; obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩; simp [List.range'_succ]
  have key : ∀ (w : List Int64) off, off ≤ 1 → s ≤ wjEdge lk rk rt w off i ∧ wjEdge lk rk rt w off i ≤ s + c :=
    fun w off ho => by
      unfold wjEdge
      simp only [hh]
      cases e : Struct.binSpec rt (Struct.group rk lk[i]!) w[i]! with
      | none => simp only [Option.map_none, Option.getD_none]; omega
      | some r =>
        have := binSpec_mem e
        rw [hg, List.mem_range'_1] at this
        simp only [Option.map_some, Option.getD_some]
        rw [Nat.max_def]; split <;> omega
  have := key w₀ 0 (by decide); have := key w₁ 1 (by decide)
  rw [hg, List.mem_range'_1]; omega

/-! ## `wj` in the algebra

`wjSpec` takes a range of right rows per left row; the algebra takes the right rows of the left row's key whose
time lies in the window. They agree where each key's right rows are contiguous and their times ascend (q's
precondition for `wj`; `wjSpec_mixes` is what breaks without it). -/

/-- **In a contiguous group whose times ascend, the rows at or before `x` are a prefix `[s, e)`**, and `bin` at
    `x` names its last row: the edge `max s (r + off)` is `e - 1 + off`, `s` where the prefix is empty. -/
theorem bin_prefix (rt : List Int64) (s c : Nat) (hs : (List.range' s c).Pairwise fun a b => rt[a]! ≤ rt[b]!)
    (x : Int64) : ∃ e, s ≤ e ∧ e ≤ s + c ∧ (∀ j, (j ∈ List.range' s c ∧ rt[j]! ≤ x) ↔ s ≤ j ∧ j < e) ∧
      ∀ off, ((Struct.binSpec rt (List.range' s c) x).map (max s <| · + off)).getD s =
        if e = s then s else e - 1 + off := by
  have hp : ((List.range' s c).filter fun j => decide (rt[j]! ≤ x)).Pairwise (· < ·) :=
    List.Pairwise.filter _ List.pairwise_lt_range'
  have hmem : ∀ j, j ∈ (List.range' s c).filter (fun j => decide (rt[j]! ≤ x)) ↔ j ∈ List.range' s c ∧ rt[j]! ≤ x :=
    fun j => by simp only [List.mem_filter, decide_eq_true_eq]
  have mono : ∀ a b, a ∈ List.range' s c → b ∈ List.range' s c → a ≤ b → rt[a]! ≤ rt[b]! := fun a b ha hb hab => by
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · exact Int64.le_refl _
    · rw [List.mem_range'_1] at ha hb
      have := List.pairwise_iff_getElem.1 hs (a - s) (b - s) (by simp only [List.length_range']; omega)
        (by simp only [List.length_range']; omega) (by omega)
      simp only [List.getElem_range', Nat.one_mul] at this
      rwa [Nat.add_sub_cancel' ha.1, Nat.add_sub_cancel' hb.1] at this
  rw [binSpec_sorted rt _ x hs]
  cases h : ((List.range' s c).filter fun j => decide (rt[j]! ≤ x)).getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff] at h
    exact ⟨s, Nat.le_refl _, by omega, fun j => ⟨fun ⟨hj, hx⟩ => absurd (decide_eq_true hx) (h j hj),
      fun h' => by omega⟩, fun off => by simp⟩
  | some r =>
    obtain ⟨hr, hm⟩ := (getLast?_greatest hp r).1 h
    obtain ⟨hrg, hrx⟩ := (hmem r).1 hr
    have hrs := List.mem_range'_1.1 hrg
    refine ⟨r + 1, by omega, by omega, fun j => ⟨fun hj => ?_, fun hj => ?_⟩, fun off => ?_⟩
    · have := hm j ((hmem j).2 hj); have := List.mem_range'_1.1 hj.1; omega
    · have hjg : j ∈ List.range' s c := List.mem_range'_1.2 (by omega)
      exact ⟨hjg, Int64.le_trans (mono j r hjg hrg (by omega)) hrx⟩
    · simp only [Option.map_some, Option.getD_some, if_neg (show r + 1 ≠ s by omega), Nat.add_sub_cancel]
      rw [Nat.max_def]; split <;> omega

/-- `lk ≫ rk°` at a left row: the right rows of its key, `group`. -/
theorem key_iff {κ : Type} [BEq κ] [LawfulBEq κ] [Inhabited κ] (lk rk : List κ) (i j : Nat) (hi : i < lk.length) :
    (ix lk ≫ (ix rk)°) i j ↔ j ∈ Struct.group rk lk[i]! := by
  show (∃ k, lk[i]? = some k ∧ rk[j]? = some k) ↔ _
  simp only [Struct.group, List.mem_filter, List.mem_range, beq_iff_eq, List.getElem?_eq_getElem hi,
    Option.some.injEq]
  constructor
  · rintro ⟨k, rfl, h⟩
    obtain ⟨hj, e⟩ := List.getElem?_eq_some_iff.1 h
    exact ⟨hj, by rw [getElem!_pos rk j hj, e, getElem!_pos lk i hi]⟩
  · rintro ⟨hj, e⟩
    exact ⟨_, rfl, by rw [List.getElem?_eq_getElem hj, ← getElem!_pos rk j hj, e, getElem!_pos lk i hi]⟩

/-- `w ≫ ρ ≫ rt°` at rows inside both lists: `ρ` of the two values. -/
theorem cmp_iff (w rt : List Int64) (ρ : Int64 → Int64 → Prop) (i j : Nat) (hi : i < w.length) (hj : j < rt.length) :
    (ix w ≫ (ρ : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) ≫ (ix rt)°) i j ↔ ρ w[i]! rt[j]! := by
  show (∃ a, w[i]? = some a ∧ ∃ b, ρ a b ∧ rt[j]? = some b) ↔ _
  simp only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, getElem!_pos w i hi, getElem!_pos rt j hj,
    Option.some.injEq]
  exact ⟨fun ⟨_, e, _, h, e'⟩ => by subst e e'; exact h, fun h => ⟨_, rfl, _, h, rfl⟩⟩

/-- The right rows of left row `i`'s key whose time `ρ`-follows `w[i]`: `(lk ≫ rk°) ∩ (w ≫ ρ ≫ rt°)`. -/
theorem keyed_iff {κ : Type} [BEq κ] [LawfulBEq κ] [Inhabited κ] (lk rk : List κ) (w rt : List Int64)
    (ρ : Int64 → Int64 → Prop) (i j : Nat) (hi : i < lk.length) (hw : i < w.length) (hrt : rt.length = rk.length) :
    ((ix lk ≫ (ix rk)°) ∩ (ix w ≫ (ρ : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) ≫ (ix rt)°)) i j ↔
      j ∈ Struct.group rk lk[i]! ∧ ρ w[i]! rt[j]! := by
  have hj : j ∈ Struct.group rk lk[i]! → j < rt.length := fun h => by
    simp only [Struct.group, List.mem_filter, List.mem_range] at h; omega
  constructor
  · rintro ⟨hk, h⟩
    have hk := (key_iff lk rk i j hi).1 hk
    exact ⟨hk, (cmp_iff w rt ρ i j hw (hj hk)).1 h⟩
  · rintro ⟨hk, h⟩
    exact ⟨(key_iff lk rk i j hi).2 hk, (cmp_iff w rt ρ i j hw (hj hk)).2 h⟩

/-- `wj`'s window `W`, its lower bound `ρ`: left row `i` to the right rows of its key with
    `ρ w₀[i] rt[j]` and `rt[j] ≤ w₁[i]`, `(lk ≫ rk°) ∩ (w₀ ≫ ρ ≫ rt°) ∩ (w₁ ≫ (≥) ≫ rt°)`. -/
def wjWin {κ : Type} (lk rk : List κ) (w₀ w₁ rt : List Int64) (ρ : Int64 → Int64 → Prop) : Idx ⟶ Idx :=
  (ix lk ≫ (ix rk)°) ∩ (ix w₀ ≫ (ρ : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) ≫ (ix rt)°) ∩
    (ix w₁ ≫ ((· ≥ ·) : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) ≫ (ix rt)°)

theorem wjWin_iff {κ : Type} [BEq κ] [LawfulBEq κ] [Inhabited κ] (lk rk : List κ) (w₀ w₁ rt : List Int64)
    (ρ : Int64 → Int64 → Prop) (i j : Nat) (hi : i < lk.length) (h0 : i < w₀.length) (h1 : i < w₁.length)
    (hrt : rt.length = rk.length) :
    wjWin lk rk w₀ w₁ rt ρ i j ↔ j ∈ Struct.group rk lk[i]! ∧ ρ w₀[i]! rt[j]! ∧ rt[j]! ≤ w₁[i]! := by
  have hj : j ∈ Struct.group rk lk[i]! → j < rt.length := fun h => by
    simp only [Struct.group, List.mem_filter, List.mem_range] at h; omega
  constructor
  · rintro ⟨h, h'⟩
    obtain ⟨hk, h⟩ := (keyed_iff lk rk w₀ rt ρ i j hi h0 hrt).1 h
    exact ⟨hk, h, (cmp_iff w₁ rt (· ≥ ·) i j h1 (hj hk)).1 h'⟩
  · rintro ⟨hk, h, h'⟩
    exact ⟨(keyed_iff lk rk w₀ rt ρ i j hi h0 hrt).2 ⟨hk, h⟩, (cmp_iff w₁ rt (· ≥ ·) i j h1 (hj hk)).2 h'⟩

/-- **Runs that are windows read as `Λ(S) ≫ enum`**: where left row `i < m`'s run is the right rows `[lo, hi)`
    and `S` relates `i` to exactly those, the runs are `corefl(<m) ≫ Λ(S) ≫ enum ≫ list(til n)`. -/
theorem ix_wins (S : Idx ⟶ Idx) (m n : Nat) (F : Nat → List Int64)
    (h : ∀ i, i < m → ∃ lo hi, lo ≤ n ∧ hi ≤ n ∧ (∀ j, S i j ↔ lo ≤ j ∧ j < hi) ∧
      F i = (List.range (hi - lo)).map fun j => Int64.ofNat (lo + j)) :
    ix (((List.range m).map F).map CL.ofList) =
      corefl (· < m) ≫ Λ S ≫ enum ≫ ListRel.list (ix ((List.range n).map Int64.ofNat)) :=
  hom_ext fun (i : Nat) c => by
    change (((List.range m).map F).map CL.ofList)[i]? = some c ↔
      ∃ z, (i = z ∧ i < m) ∧ ∃ s, Λ S z s ∧ ∃ zs, enum s zs ∧ ListRel.listP (ix ((List.range n).map Int64.ofNat)) zs c
    by_cases him : i < m
    · obtain ⟨lo, hi, hlo, hhi, hS, hF⟩ := h i him
      have hW : ∀ ys, (Λ S ≫ enum) i ys ↔ ys = CL.ofList (List.range' lo (hi - lo)) :=
        Λ_enum S (i := i) (a := lo) (k := hi - lo) fun j =>
          (hS j).trans <| and_congr_right fun h1 => by
            by_cases hl : lo ≤ hi
            · rw [Nat.add_sub_cancel' hl]
            · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_le hl), Nat.add_zero]
              exact ⟨fun h2 => absurd (Nat.lt_trans h2 (Nat.lt_of_not_le hl)) (Nat.not_lt.2 h1),
                fun h2 => absurd h2 (Nat.not_lt.2 h1)⟩
      have hl : lo + (hi - lo) ≤ ((List.range n).map Int64.ofNat).length := by
        simp only [List.length_map, List.length_range]; omega
      have hd : (((List.range n).map Int64.ofNat).drop lo).take (hi - lo) =
          (List.range (hi - lo)).map fun j => Int64.ofNat (lo + j) :=
        List.ext_getElem (by simp only [List.length_take, List.length_drop, List.length_map, List.length_range]; omega)
          fun k _ _ => by simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
      rw [List.map_map, List.getElem?_map, List.getElem?_range him, Option.map_some, Option.some.injEq,
        Function.comp_apply, hF]
      constructor
      · intro e
        obtain ⟨s, hs, he⟩ := (hW _).2 rfl
        exact ⟨i, ⟨rfl, him⟩, s, hs, _, he, (listP_ix_range' _ (hi - lo) lo hl _).2 (by rw [hd, e])⟩
      · rintro ⟨_, ⟨rfl, -⟩, s, hs, zs, hz, hw⟩
        rw [(hW zs).1 ⟨s, hs, hz⟩] at hw
        rw [(listP_ix_range' _ (hi - lo) lo hl c).1 hw, hd]
    · rw [List.getElem?_eq_none (by simp only [List.length_map, List.length_range]; omega)]
      exact ⟨(fun e => nomatch e), by rintro ⟨_, ⟨_, h⟩, -⟩; exact absurd h him⟩

/-- q's `w - 1` off `0N` is `Int64`'s, and does not wrap. -/
theorem toInt_sub_one {w : Int64} (h : w ≠ Int64.minValue) : (w - 1).toInt = w.toInt - 1 := by
  have h1 : w.toInt ≠ Int64.minValue.toInt := fun e => h (Int64.toInt_inj.1 e)
  rw [Int64.toInt_minValue] at h1
  have := Int64.le_toInt w; have := Int64.toInt_lt w
  rw [Int64.toInt_sub, show (1 : Int64).toInt = 1 from rfl, Int.bmod_eq_of_le] <;> omega

theorem intStep_sub_one {w : Int64} (h : w ≠ Int64.minValue) :
    Kernel.Ew.intStep Kernel.Ew.sub Int64.minValue w 1 = w - 1 := by
  have : (w == Int64.minValue || (1 : Int64) == Int64.minValue) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; exact ⟨h, by decide⟩
  unfold Kernel.Ew.intStep
  rw [if_neg (by decide), if_pos (by decide), this]; rfl

/-- The hypotheses both laws read the right table under: each key's right rows are one contiguous block, their
    times ascending (q's `wj` precondition, a table sorted by key then time). -/
def WjSorted {κ : Type} [BEq κ] [Inhabited κ] (rk : List κ) (rt : List Int64) : Prop :=
  ∀ k, (∃ s c, Struct.group rk k = List.range' s c) ∧ (Struct.group rk k).Pairwise fun a b => rt[a]! ≤ rt[b]!

/-- Row `i`'s run read as a window, both edges from `bin_prefix`: `e₀`, `e₁` the ends of the prefixes at or before
    `x₀` and `w₁[i]`, the group `[s, s + c)`. The run is empty where the key has no right rows. -/
theorem wjRow {κ : Type} [BEq κ] [LawfulBEq κ] [Inhabited κ] (prevailing : Bool) (lk rk : List κ)
    (w₀ w₁ rt : List Int64) (hsrt : WjSorted rk rt) (i : Nat) (hi : i < lk.length) (x₀ : Int64)
    (hx₀ : (if prevailing then w₀[i]! else Kernel.Ew.intStep Kernel.Ew.sub Int64.minValue w₀[i]! 1) = x₀)
    (S : Idx ⟶ Idx)
    (hS : ∀ s c e₀ e₁, Struct.group rk lk[i]! = List.range' s c → 0 < c → s ≤ e₀ → e₀ ≤ s + c → s ≤ e₁ →
      e₁ ≤ s + c →
      (∀ j, (j ∈ List.range' s c ∧ rt[j]! ≤ x₀) ↔ s ≤ j ∧ j < e₀) →
      (∀ j, (j ∈ List.range' s c ∧ rt[j]! ≤ w₁[i]!) ↔ s ≤ j ∧ j < e₁) →
      ∀ j, S i j ↔ (if prevailing then (if e₀ = s then s else e₀ - 1) else e₀) ≤ j ∧ j < e₁)
    (hS0 : Struct.group rk lk[i]! = [] → ∀ j, ¬ S i j) :
    ∃ lo hi, lo ≤ rk.length ∧ hi ≤ rk.length ∧ (∀ j, S i j ↔ lo ≤ j ∧ j < hi) ∧
      Struct.wjRun prevailing lk w₀ w₁ rk rt i = (List.range (hi - lo)).map fun j => Int64.ofNat (lo + j) := by
  unfold Struct.wjRun
  obtain ⟨⟨s, c, hg⟩, hs⟩ := hsrt lk[i]!
  rw [hg] at hs
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · have hh : Struct.group rk lk[i]! = [] := hg
    refine ⟨0, 0, Nat.zero_le _, Nat.zero_le _, fun j => ⟨fun h => absurd h (hS0 hh j), fun h => absurd h.2 (Nat.not_lt_zero _)⟩, ?_⟩
    simp only [hh, List.head?_nil]; rfl
  · have hcn : s + c ≤ rk.length := by
      have : s + c - 1 ∈ Struct.group rk lk[i]! := by rw [hg, List.mem_range'_1]; omega
      simp only [Struct.group, List.mem_filter, List.mem_range] at this; omega
    have hh : (Struct.group rk lk[i]!).head? = some s := by
      rw [hg]; obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩; simp [List.range'_succ]
    obtain ⟨e₀, hs0, he0, hm0, hed0⟩ := bin_prefix rt s c hs x₀
    obtain ⟨e₁, hs1, he1, hm1, hed1⟩ := bin_prefix rt s c hs w₁[i]!
    have hS' := hS s c e₀ e₁ hg hc hs0 he0 hs1 he1 hm0 hm1
    have he : ∀ e, s ≤ e → (if e = s then s else e - 1 + 1) = e := fun e h => by split <;> omega
    refine ⟨if prevailing then (if e₀ = s then s else e₀ - 1) else e₀, e₁, by split <;> (try split) <;> omega,
      by omega, hS', ?_⟩
    simp only [hh]
    rw [hg]
    cases prevailing
    · simp only [Bool.false_eq_true, ↓reduceIte] at hx₀ ⊢
      rw [hx₀, hed0, hed1, he e₀ hs0, he e₁ hs1]
    · simp only [↓reduceIte] at hx₀ ⊢
      rw [hx₀, hed0, hed1, he e₁ hs1, Nat.add_zero]

/-- **`wj1` in the algebra**: left row `i`'s run is the right rows of its key whose time lies in
    `[w₀[i], w₁[i]]`, `Λ(W) ≫ enum` with `W = (lk ≫ rk°) ∩ (w₀ ≫ (≤) ≫ rt°) ∩ (w₁ ≫ (≥) ≫ rt°)`, read through
    `til |rk|`. Hypotheses: `WjSorted`, and no `0N` in `w₀`, where q's `0N - 1` is `0N` and the kernel's lower
    edge skips the right rows at `0N` that `W` keeps. -/
theorem wj1Spec_rel {κ : Type} [BEq κ] [LawfulBEq κ] [Inhabited κ] (lk rk : List κ) (w₀ w₁ rt : List Int64)
    (hsrt : WjSorted rk rt) (h0 : w₀.length = lk.length) (h1 : w₁.length = lk.length)
    (hrt : rt.length = rk.length) (hn : ∀ i, i < lk.length → w₀[i]! ≠ Int64.minValue) :
    ix ((Struct.wjRuns false lk w₀ w₁ rk rt).map CL.ofList) = corefl (· < lk.length) ≫ Λ (wjWin lk rk w₀ w₁ rt (· ≤ ·)) ≫
      enum ≫ ListRel.list (ix ((List.range rk.length).map Int64.ofNat)) := by
  refine ix_wins _ _ _ (Struct.wjRun false lk w₀ w₁ rk rt) fun i hi => wjRow false lk rk w₀ w₁ rt hsrt i hi (w₀[i]! - 1)
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact intStep_sub_one (hn i hi)) _ ?_ ?_
  · intro s c e₀ e₁ hg _ hs0 _ _ _ hm0 hm1 j
    rw [wjWin_iff lk rk w₀ w₁ rt _ i j hi (by omega) (by omega) hrt, hg]
    have := hm0 j; have := hm1 j; have := toInt_sub_one (hn i hi)
    simp only [List.mem_range'_1, Int64.le_iff_toInt_le, Bool.false_eq_true, ↓reduceIte] at *
    omega
  · intro hg j h
    have := ((wjWin_iff lk rk w₀ w₁ rt _ i j hi (by omega) (by omega) hrt).1 h).1
    rw [hg] at this; cases this

/-- **`wj` in the algebra**: left row `i`'s run is the right rows of its key strictly after `w₀[i]` up to `w₁[i]`,
    with the prevailing row added — the last of its key at or before `w₀[i]`, `est(≥)` of those:
    `Λ(W₍<₎ ∪ (Λ((lk ≫ rk°) ∩ (w₀ ≫ (≥) ≫ rt°)) ≫ est(≥))) ≫ enum`. Hypotheses: `WjSorted`, `w₀ ≤ w₁`. -/
theorem wjSpec_rel {κ : Type} [BEq κ] [LawfulBEq κ] [Inhabited κ] (lk rk : List κ) (w₀ w₁ rt : List Int64)
    (hsrt : WjSorted rk rt) (h0 : w₀.length = lk.length) (h1 : w₁.length = lk.length)
    (hrt : rt.length = rk.length) (hw : ∀ i, i < lk.length → w₀[i]! ≤ w₁[i]!) :
    ix ((Struct.wjRuns true lk w₀ w₁ rk rt).map CL.ofList) = corefl (· < lk.length) ≫
      Λ (wjWin lk rk w₀ w₁ rt (· < ·) ∪ (Λ ((ix lk ≫ (ix rk)°) ∩
        (ix w₀ ≫ ((· ≥ ·) : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) ≫ (ix rt)°)) ≫ est (· ≥ ·))) ≫
      enum ≫ ListRel.list (ix ((List.range rk.length).map Int64.ofNat)) := by
  refine ix_wins _ _ _ (Struct.wjRun true lk w₀ w₁ rk rt) fun i hi => wjRow true lk rk w₀ w₁ rt hsrt i hi w₀[i]! (by simp) _ ?_ ?_
  · intro s c e₀ e₁ hg _ hs0 _ _ _ hm0 hm1 j
    have hT : ∀ z, ((ix lk ≫ (ix rk)°) ∩ (ix w₀ ≫ ((· ≥ ·) : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) ≫ (ix rt)°)) i z ↔
        s ≤ z ∧ z < e₀ := fun z => by
      rw [keyed_iff lk rk w₀ rt _ i z hi (by omega) hrt, hg, ← hm0 z]
    have hP : (Λ ((ix lk ≫ (ix rk)°) ∩ (ix w₀ ≫ ((· ≥ ·) : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) ≫ (ix rt)°)) ≫
        est (· ≥ ·)) i j ↔ s < e₀ ∧ j = e₀ - 1 := by
      rw [RelSet.Λ_comp_est_apply]
      simp only [hT]
      constructor
      · rintro ⟨hj, hm⟩; have := hm (e₀ - 1) ⟨by omega, by omega⟩; exact ⟨by omega, by omega⟩
      · rintro ⟨_, rfl⟩; exact ⟨⟨by omega, by omega⟩, fun z hz => by omega⟩
    show wjWin lk rk w₀ w₁ rt (· < ·) i j ∨ _ ↔ _
    rw [hP, wjWin_iff lk rk w₀ w₁ rt _ i j hi (by omega) (by omega) hrt, hg]
    have := hm0 j; have := hm1 j; have := hm0 (e₀ - 1); have := hm1 (e₀ - 1); have := hw i hi
    simp only [List.mem_range'_1, Int64.le_iff_toInt_le, Int64.lt_iff_toInt_lt, ↓reduceIte] at *
    split <;> omega
  · intro hg j h
    rcases h with h | h
    · have := ((wjWin_iff lk rk w₀ w₁ rt _ i j hi (by omega) (by omega) hrt).1 h).1
      rw [hg] at this; cases this
    · have := ((keyed_iff lk rk w₀ rt _ i j hi (by omega) hrt).1 ((RelSet.Λ_comp_est_apply _ _ _ _).1 h).1).1
      rw [hg] at this; cases this

/-- **`wj`'s kernel answer is the algebra's** at one long key column per side (`wj_long`, then `wjSpec_rel`):
    `P.rel = corefl(<|t0|) ≫ Λ(W₍<₎ ∪ (Λ((lk ≫ rk°) ∩ (w₀ ≫ (≥) ≫ rt°)) ≫ est(≥))) ≫ enum ≫ list(til |tr|)`,
    where the right table is `WjSorted` and every window has `w₀ ≤ w₁`. -/
theorem wj_rel {cl cr t0 t1 tr : Nat × Enc} {wl wr : List UInt64} {P : Parted .long} {b0 b1 hay : ByteArray}
    (hwl : longWords cl.1 cl.2 = some wl) (hwr : longWords cr.1 cr.2 = some wr)
    (hln : wl.length = cl.1) (hrn : wr.length = cr.1) (hcl : cl.1 = t0.1) (hcr : cr.1 = tr.1)
    (hlwf : Enc.WF .long cl.1 cl.2) (hlR : Find.Readable .long cl.1 cl.2)
    (hrwf : Enc.WF .long cr.1 cr.2) (hrR : Find.Readable .long cr.1 cr.2)
    (h0b : Enc.bytesOf .long t0.1 t0.2 = some b0) (h1b : Enc.bytesOf .long t1.1 t1.2 = some b1)
    (hrb : Enc.bytesOf .long tr.1 tr.2 = some hay)
    (h0n : b0.size / 8 = t0.1) (h1n : b1.size / 8 = t0.1) (hhn : hay.size / 8 = tr.1)
    (hU : t0.1 * tr.1 + t0.1 + tr.1 + 1 < USize.size) (h62 : t0.1 * tr.1 + t0.1 + tr.1 + 1 < 2 ^ 62)
    (hsrt : WjSorted wr ((nats hay).map Int64.ofNat))
    (hw : ∀ i, i < t0.1 → ((nats b0).map Int64.ofNat)[i]! ≤ ((nats b1).map Int64.ofNat)[i]!)
    (h : Struct.wjP true ⟨.long, t0⟩ ⟨.long, t1⟩ #[⟨.long, cl⟩] #[⟨.long, cr⟩] ⟨.long, tr⟩ = .ok P) :
    P.rel = corefl (· < t0.1) ≫
      Λ (wjWin wl wr ((nats b0).map Int64.ofNat) ((nats b1).map Int64.ofNat) ((nats hay).map Int64.ofNat) (· < ·) ∪
        (Λ ((ix wl ≫ (ix wr)°) ∩ (ix ((nats b0).map Int64.ofNat) ≫ ((· ≥ ·) : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) ≫
          (ix ((nats hay).map Int64.ofNat))°)) ≫ est (· ≥ ·))) ≫
      enum ≫ ListRel.list (ix ((List.range tr.1).map Int64.ofNat)) := by
  show ix (P.segs.map CL.ofList) = _
  rw [wj_long hwl hwr hln hrn hcl hcr hlwf hlR hrwf hrR h0b h1b hrb h0n h1n hhn hU h62 h]
  have l0 : ((nats b0).map Int64.ofNat).length = wl.length := by rw [List.length_map, nats_length]; omega
  have l1 : ((nats b1).map Int64.ofNat).length = wl.length := by rw [List.length_map, nats_length]; omega
  have lr : ((nats hay).map Int64.ofNat).length = wr.length := by rw [List.length_map, nats_length]; omega
  rw [show t0.1 = wl.length by omega, show tr.1 = wr.length by omega]
  exact wjSpec_rel wl wr _ _ _ hsrt l0 l1 lr fun i hi => hw i (by omega)

/-- **`wj1`'s kernel answer is the algebra's** at one long key column per side (`wj1_long`, then `wj1Spec_rel`):
    `P.rel = corefl(<|t0|) ≫ Λ(W) ≫ enum ≫ list(til |tr|)`, `W = (lk ≫ rk°) ∩ (w₀ ≫ (≤) ≫ rt°) ∩ (w₁ ≫ (≥) ≫ rt°)`,
    where the right table is `WjSorted` and `w₀` holds no `0N`. -/
theorem wj1_rel {cl cr t0 t1 tr : Nat × Enc} {wl wr : List UInt64} {P : Parted .long} {b0 b1 hay : ByteArray}
    (hwl : longWords cl.1 cl.2 = some wl) (hwr : longWords cr.1 cr.2 = some wr)
    (hln : wl.length = cl.1) (hrn : wr.length = cr.1) (hcl : cl.1 = t0.1) (hcr : cr.1 = tr.1)
    (hlwf : Enc.WF .long cl.1 cl.2) (hlR : Find.Readable .long cl.1 cl.2)
    (hrwf : Enc.WF .long cr.1 cr.2) (hrR : Find.Readable .long cr.1 cr.2)
    (hb0 : t0.2 = .bytes b0 ∨ ∃ md pk, t0.2 = .foR md pk ∧ b0 = Kernel.Coc.decode (8 : Nat).toUSize md pk t0.1.toUSize)
    (h1b : Enc.bytesOf .long t1.1 t1.2 = some b1) (hrb : Enc.bytesOf .long tr.1 tr.2 = some hay)
    (h0n : b0.size / 8 = t0.1) (h1n : b1.size / 8 = t0.1) (hhn : hay.size / 8 = tr.1)
    (hU : t0.1 * tr.1 + t0.1 + tr.1 + 1 < USize.size) (h62 : t0.1 * tr.1 + t0.1 + tr.1 + 1 < 2 ^ 62)
    (hsrt : WjSorted wr ((nats hay).map Int64.ofNat))
    (hn : ∀ i, i < t0.1 → ((nats b0).map Int64.ofNat)[i]! ≠ Int64.minValue)
    (h : Struct.wjP false ⟨.long, t0⟩ ⟨.long, t1⟩ #[⟨.long, cl⟩] #[⟨.long, cr⟩] ⟨.long, tr⟩ = .ok P) :
    P.rel = corefl (· < t0.1) ≫
      Λ (wjWin wl wr ((nats b0).map Int64.ofNat) ((nats b1).map Int64.ofNat) ((nats hay).map Int64.ofNat) (· ≤ ·)) ≫
      enum ≫ ListRel.list (ix ((List.range tr.1).map Int64.ofNat)) := by
  show ix (P.segs.map CL.ofList) = _
  rw [wj1_long hwl hwr hln hrn hcl hcr hlwf hlR hrwf hrR hb0 h1b hrb h0n h1n hhn hU h62 h]
  have l0 : ((nats b0).map Int64.ofNat).length = wl.length := by rw [List.length_map, nats_length]; omega
  have l1 : ((nats b1).map Int64.ofNat).length = wl.length := by rw [List.length_map, nats_length]; omega
  have lr : ((nats hay).map Int64.ofNat).length = wr.length := by rw [List.length_map, nats_length]; omega
  rw [show t0.1 = wl.length by omega, show tr.1 = wr.length by omega]
  exact wj1Spec_rel wl wr _ _ _ hsrt l0 l1 lr fun i hi => hn i (by omega)

/-- `xs[j]? = some a` is `j` in range with `xs[j]! = a`, the form `group` and `cand` read positions in. -/
theorem getElem?_eq_some_iff! {α : Type} [Inhabited α] (xs : List α) (j : Nat) (a : α) :
    xs[j]? = some a ↔ j < xs.length ∧ xs[j]! = a :=
  ⟨fun e => let ⟨h, e⟩ := List.getElem?_eq_some_iff.1 e; ⟨h, by rw [getElem!_pos xs j h, e]⟩,
   fun ⟨h, e⟩ => List.getElem?_eq_some_iff.2 ⟨h, by rw [← getElem!_pos xs j h, e]⟩⟩

/-- **`aj` as the expression (design §11.3)**: `S = (lk ≫ rk°) ∩ (lt ≫ (≥) ≫ rt°)` relates a left row to the right
    rows of its key at or before its time, and `aj = miss(Λ(S) ≫ est(≥), 0N)` on the left's rows: the greatest of
    them, the last, since within a key the right times ascend (`binSpec` bisects, `binSpec_est`). -/
theorem ajSpec_rel {κ : Type} [BEq κ] [LawfulBEq κ] [Inhabited κ] (lk : List κ) (lt : List Int64) (rk : List κ)
    (rt : List Int64) (hl : lt.length = lk.length) (hr : rt.length = rk.length)
    (htime : ∀ i j, i ≤ j → j < rt.length → rk[i]! = rk[j]! → rt[i]! ≤ rt[j]!) :
    ix (Struct.ajSpec lk lt rk rt) = corefl (· < lk.length) ≫
      miss ((Λ ((ix lk ≫ (ix rk)°) ∩ (ix lt ≫ ((· ≥ ·) : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) ≫ (ix rt)°))
        ≫ est (· ≥ ·)) ≫ graph Int64.ofNat) Int64.minValue := by
  obtain ⟨S, hS⟩ : ∃ S : Idx ⟶ Idx,
      S = (ix lk ≫ (ix rk)°) ∩ (ix lt ≫ ((· ≥ ·) : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩) ≫ (ix rt)°) := ⟨_, rfl⟩
  rw [← hS]
  have key : ∀ i, i < lk.length → ∀ j, S i j ↔ cand lk rk rt lt i j := fun i hi j => by
    subst hS
    show ((∃ k, lk[i]? = some k ∧ rk[j]? = some k) ∧ ∃ a, lt[i]? = some a ∧ ∃ b, a ≥ b ∧ rt[j]? = some b) ↔
      j ∈ Struct.group rk lk[i]! ∧ rt[j]! ≤ lt[i]!
    constructor
    · rintro ⟨⟨k, hk1, hk2⟩, ⟨a, ha, b, hab, hb⟩⟩
      obtain ⟨-, rfl⟩ := (getElem?_eq_some_iff! lk i k).1 hk1
      obtain ⟨hj, e⟩ := (getElem?_eq_some_iff! rk j _).1 hk2
      obtain ⟨-, rfl⟩ := (getElem?_eq_some_iff! lt i a).1 ha
      obtain ⟨-, rfl⟩ := (getElem?_eq_some_iff! rt j b).1 hb
      exact ⟨List.mem_filter.2 ⟨List.mem_range.2 hj, beq_iff_eq.2 e⟩, hab⟩
    · rintro ⟨hm, hab⟩
      obtain ⟨hj, e⟩ := List.mem_filter.1 hm
      have hj := List.mem_range.1 hj
      exact ⟨⟨_, (getElem?_eq_some_iff! lk i _).2 ⟨hi, rfl⟩, (getElem?_eq_some_iff! rk j _).2 ⟨hj, beq_iff_eq.1 e⟩⟩,
        ⟨_, (getElem?_eq_some_iff! lt i _).2 ⟨by omega, rfl⟩, _, hab, (getElem?_eq_some_iff! rt j _).2 ⟨by omega, rfl⟩⟩⟩
  have hs : ∀ k, (Struct.group rk k).Pairwise fun a b => rt[a]! ≤ rt[b]! := fun k =>
    ((List.pairwise_lt_range (n := rk.length)).filter _).imp_of_mem fun ha hb hab => by
      obtain ⟨-, ha2⟩ := List.mem_filter.1 ha
      obtain ⟨hb1, hb2⟩ := List.mem_filter.1 hb
      have := List.mem_range.1 hb1
      exact htime _ _ (Nat.le_of_lt hab) (by omega) ((beq_iff_eq.1 ha2).trans (beq_iff_eq.1 hb2).symm)
  have hB : ∀ i, i < lk.length → ∀ r,
      (Λ S ≫ est (· ≥ ·)) i r ↔ Struct.binSpec rt (Struct.group rk lk[i]!) lt[i]! = some r := fun i hi r => by
    rw [binSpec_est lk rk rt lt i r (hs _), Λ_comp_est_apply, Λ_comp_est_apply]
    simp only [key i hi]
  have hR : ∀ i, i < lk.length → ∀ c, miss ((Λ S ≫ est (· ≥ ·)) ≫ graph Int64.ofNat) Int64.minValue i c ↔
      c = ((Struct.binSpec rt (Struct.group rk lk[i]!) lt[i]!).map Int64.ofNat).getD Int64.minValue := fun i hi c => by
    have hM : ∀ c, ((Λ S ≫ est (· ≥ ·)) ≫ graph Int64.ofNat) i c ↔
        ∃ r, Struct.binSpec rt (Struct.group rk lk[i]!) lt[i]! = some r ∧ c = Int64.ofNat r :=
      fun c => ⟨fun ⟨r, h, e⟩ => ⟨r, (hB i hi r).1 h, e⟩, fun ⟨r, h, e⟩ => ⟨r, (hB i hi r).2 h, e⟩⟩
    rw [miss_iff]
    simp only [hM]
    cases Struct.binSpec rt (Struct.group rk lk[i]!) lt[i]! <;> simp
  refine hom_ext fun (i : Nat) c => ?_
  show (Struct.ajSpec lk lt rk rt)[i]? = some c ↔
    ∃ i', (i = i' ∧ i < lk.length) ∧ miss ((Λ S ≫ est (· ≥ ·)) ≫ graph Int64.ofNat) Int64.minValue i' c
  by_cases hi : i < lk.length
  · have hv : (Struct.ajSpec lk lt rk rt)[i]? =
        some (((Struct.binSpec rt (Struct.group rk lk[i]!) lt[i]!).map Int64.ofNat).getD Int64.minValue) := by
      rw [getElem!_pos lk i hi, getElem!_pos lt i (by omega), Struct.ajSpec, List.getElem?_map,
        List.getElem?_eq_getElem (by rw [List.length_zip]; omega), List.getElem_zip]
      rfl
    rw [hv, Option.some.injEq, eq_comm, ← hR i hi c]
    exact ⟨fun h => ⟨i, ⟨rfl, hi⟩, h⟩, fun ⟨_, ⟨e, _⟩, h⟩ => by subst e; exact h⟩
  · rw [List.getElem?_eq_none (by simp only [Struct.ajSpec, List.length_map, List.length_zip]; omega)]
    exact ⟨(fun e => nomatch e), fun ⟨_, ⟨_, h⟩, _⟩ => absurd h hi⟩

/-- **The `aj` kernel computes the expression**: `aj_long`'s answer is `miss(Λ(S) ≫ est(≥), 0N)` (`ajSpec_rel`)
    on the key words and the times read as longs, where within each right key the times ascend. -/
theorem aj_rel {cl cr tl tr : Nat × Enc} {wl wr : List UInt64} {m : Nat} {A : Arr .long m} {keys hay : ByteArray}
    (hwl : longWords cl.1 cl.2 = some wl) (hwr : longWords cr.1 cr.2 = some wr)
    (hln : wl.length = cl.1) (hrn : wr.length = cr.1) (hcl : cl.1 = tl.1) (hcr : cr.1 = tr.1)
    (hlwf : Enc.WF .long cl.1 cl.2) (hlR : Find.Readable .long cl.1 cl.2)
    (hrwf : Enc.WF .long cr.1 cr.2) (hrR : Find.Readable .long cr.1 cr.2)
    (hkb : Enc.bytesOf .long tl.1 tl.2 = some keys) (hrb : Enc.bytesOf .long tr.1 tr.2 = some hay) (hkn : keys.size / 8 = tl.1) (hhn : hay.size / 8 = tr.1)
    (hU : tl.1 < USize.size) (hrU : tr.1 < USize.size) (h63 : tr.1 < 2 ^ 63) (h2l : 2 * tl.1 + 2 < 2 ^ 63)
    (htime : ∀ i j, i ≤ j → j < tr.1 → wr[i]! = wr[j]! →
      ((nats hay).map Int64.ofNat)[i]! ≤ ((nats hay).map Int64.ofNat)[j]!)
    (h : Struct.aj #[(.long, cl)] #[(.long, cr)] (.long, tl) (.long, tr) = .ok ⟨m, A⟩) :
    A.rel = corefl (· < m) ≫
      miss ((Λ ((ix wl ≫ (ix wr)°) ∩ (ix ((nats keys).map Int64.ofNat) ≫ ((· ≥ ·) : (⟨Int64⟩ : RelSet.{0}) ⟶ ⟨Int64⟩)
        ≫ (ix ((nats hay).map Int64.ofNat))°)) ≫ est (· ≥ ·)) ≫ graph Int64.ofNat) Int64.minValue := by
  have hA := aj_long hwl hwr hln hrn hcl hcr hlwf hlR hrwf hrR hkb hrb hkn hhn hU hrU h63 h2l h
  have hm : m = wl.length := by
    have := congrArg List.length hA
    rw [Arr.length_toList] at this
    rw [this]; simp only [Struct.ajSpec, List.length_map, List.length_zip, nats_length]; omega
  show ix A.toList = _
  rw [hA, hm]
  exact ajSpec_rel wl _ wr _ (by simp only [List.length_map, nats_length]; omega)
    (by simp only [List.length_map, nats_length]; omega)
    fun i j hij hj e => htime i j hij (by simp only [List.length_map, nats_length] at hj; omega) e

#print axioms rangeOffsets_long
#print axioms keyCodes_long
#print axioms ej_long
#print axioms ij_long
#print axioms binStep_go
#print axioms bitsAt_binRows
#print axioms bitsAt_binRows_miss
#print axioms ordKey8_le
#print axioms groupEdge_long
#print axioms binSpec_mem
#print axioms aj_groups
#print axioms bucket_idxOf
#print axioms groups_of_buckets
#print axioms firsts_of_buckets
#print axioms groupColumn_long
#print axioms keyColumns_long
#print axioms keyMatch_grouped
#print axioms runsColumn_long
#print axioms longRows_runStarts
#print axioms firstsOf_runs
#print axioms bucket_run
#print axioms ofKey_answers
#print axioms gatherColumn_long_some
#print axioms keyMatch_runs
#print axioms keyMatch_gallop
#print axioms binEdges_long
#print axioms keyMatch_halved
#print axioms oneRun_of_ascending
#print axioms keyMatch_answers
#print axioms ofRuns_answers
#print axioms ofRuns_kernel
#print axioms idxOf_first
#print axioms gallopInv_step
#print axioms gallop_group
#print axioms forIn_range_inv
#print axioms gallop_loop
#print axioms gather_rows
#print axioms aj_long
#print axioms binRows_group
#print axioms bitsAt_elemsW
#print axioms ofNat_ne_min
#print axioms toUInt64_toInt64
#print axioms ofNat_toUInt64_toNat
#print axioms wj_edge_word
#print axioms wj_edge
#print axioms wj_lens
#print axioms wj_tail
#print axioms wj_groups
#print axioms wj_long
#print axioms ix_winAt
#print axioms wjSpec_runs
#print axioms dyadColumn_sub_one
#print axioms wj1_long
#print axioms getLast?_greatest
#print axioms binSpec_est
#print axioms wjEdge_est
#print axioms wjSpec_mixes
#print axioms wjEdge_contig
#print axioms ajSpec_rel
#print axioms aj_rel
#print axioms bytesOf_longWords
#print axioms dyadColumn_sub_one_foR
#print axioms bin_prefix
#print axioms key_iff
#print axioms cmp_iff
#print axioms keyed_iff
#print axioms wjWin_iff
#print axioms ix_wins
#print axioms toInt_sub_one
#print axioms intStep_sub_one
#print axioms wjRow
#print axioms wj1Spec_rel
#print axioms wjSpec_rel
#print axioms wj_rel
#print axioms wj1_rel

end LeetQ.Rel.Verb
