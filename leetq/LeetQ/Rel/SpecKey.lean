import LeetQ.Rel.SpecStruct
import LeetQ.Rel.SpecScan

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

/-- **What `keyMatch` must answer for a key join**: `ids` is a long payload with a word per left key, and
    word `i` names a group whose span (`bounds` read as longs, rows through `rows` or the position itself) lists
    `Struct.group rk lk[i]`, or names no group where that is empty; and `gs.firsts` gathered at the ids (`0`
    past them) is word `i` the head of that group, `0` where it is empty — `wj`'s start. -/
def KeyAnswers {κ : Type} [BEq κ] [Inhabited κ] (rk lk : List κ) (gs : Eval.Groups) (ids : Column) : Prop :=
  ∃ gids, Column.bytesOf ids = some gids ∧ gids.size / 8 = lk.length ∧
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
theorem binRows_group {κ : Type} [BEq κ] [Inhabited κ] {rk lk : List κ} {gs : Eval.Groups} {ids : Column}
    {keys hay gids : ByteArray} {nr : Nat} (hk : KeyAnswers rk lk gs ids) (hgb : Column.bytesOf ids = some gids)
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
theorem aj_groups {κ : Type} [BEq κ] [Inhabited κ] {l r : Array Struct.KCol} {tl tr : Column} {m : Nat}
    {A : Arr .long m} {gs : Eval.Groups} {ids : Column} {keys hay gids : ByteArray} (lk rk : List κ)
    (htl : tl.ty = .long) (htr : tr.ty = .long) (hkb : Column.bytesOf tl = some keys)
    (hrb : Column.bytesOf tr = some hay) (hgb : Column.bytesOf ids = some gids)
    (hkn : keys.size / 8 = tl.n) (hrn : hay.size / 8 = tr.n)
    (hlk : lk.length = tl.n) (hrk : rk.length = tr.n) (hU : tl.n < USize.size) (h63 : tr.n < 2 ^ 63)
    (hkg : Struct.keyGroups "aj" l r tl.n tr.n = .ok (gs, ids)) (hk : KeyAnswers rk lk gs ids)
    (h : Struct.aj l r ⟨.long, tl⟩ ⟨.long, tr⟩ = .ok ⟨m, A⟩) :
    A.toList = Struct.ajSpec lk ((nats keys).map Int64.ofNat) rk ((nats hay).map Int64.ofNat) := by
  obtain ⟨g', hg', hgn, -⟩ := id hk
  rw [Option.some.inj (hg'.symm.trans hgb)] at hgn
  have hE :=groupEdge_long gs ids tr tl tr.n htr htl hrb hkb hgb (by omega)
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
  rw [hx, ← toInt64_eq_ofNat, ← getElem!_pos lk i (by omega), binRows_group hk hgb (by omega) hrn hrk (by omega)]
  cases hb : Struct.binSpec ((nats hay).map Int64.ofNat) (Struct.group rk lk[i]!) (Column.bitsAt keys (i * 8) 8).toInt64 with
    | none => simp [hfill, Nat.toUInt64_eq, hnr]
    | some r =>
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
  have hbs63 : ∀ r ∈ (F.map (Verify.bucketOf (Order.keyAt .i64 B) (B.size / 8))).flatten, r < B.size / 8 :=
    fun r hr => by
      obtain ⟨l, hl, hrl⟩ := List.mem_flatten.1 hr
      obtain ⟨f, -, rfl⟩ := List.mem_map.1 hl
      exact List.mem_range.1 (List.mem_filter.1 hrl).1
  obtain ⟨-, hsz, hspan⟩ := groups_of_buckets (F.map (Verify.bucketOf (Order.keyAt .i64 B) (B.size / 8)))
    (fun r hr => by have := hbs63 r hr; omega) (by rw [hflat]; omega) rfl
  have hPn : P.size / 8 = wl.length := by
    have := congrArg List.length hmap; simpa [Verify.elemsW] using this
  have hPi : ∀ i (hi : i < wl.length), (Column.bitsAt P (i * 8) 8).toNat =
      (F.map fun f => Column.bitsAt B (f * 8) 8).idxOf wl[i] := fun i hi => by
    have := congrArg (·[i]?) hmap
    rw [hkw] at this
    simp only [Verify.elemsW, List.map_map, List.getElem?_map, List.getElem?_range (by omega : i < P.size / 8),
      List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq, Function.comp_apply] at this
    exact this
  refine ⟨P, rfl, hPn, ?_, fun i hi => ?_⟩
  · -- the starts: each bucket holds its own first occurrence, so `firsts` is each bucket's head
    have hne : ∀ b ∈ F.map (Verify.bucketOf (Order.keyAt .i64 B) (B.size / 8)), b ≠ [] := fun b hb => by
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hb
      rw [← hF] at hf
      unfold Verify.firstsOf at hf
      have hf' := List.mem_range.1 (List.mem_filter.1 hf).1
      exact List.ne_nil_of_mem (show f ∈ Verify.bucketOf _ _ f from List.mem_filter.2 ⟨List.mem_range.2 hf', by simp⟩)
    have hfi := firsts_of_buckets _ (fun r hr => by have := hbs63 r hr; omega) (by rw [hflat]; omega) hne rfl
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
      nats_get P (by omega), hPi i h2, getElem!_pos wl i h2, ← hBw]
    subst hF
    rcases bucket_idxOf B wl[i] with ⟨hge, hnil⟩ | ⟨hlt', hb⟩
    · rw [hnil, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
      rw [List.getElem?_singleton]; split <;> rfl
    · change Verify.bucketOf _ _ _ = _ at hb
      rw [← hb, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hlt')]
      simp [List.getElem?_map, List.getElem?_eq_getElem hlt']
  rw [getElem!_pos wl i hi, ← hBw, hPi i hi]
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
  have hk := keyMatch_grouped tr.n tl.n hrt hlt hwr hrn (by omega) (by omega) (by omega) hlwf hlR hwl hattr
  obtain ⟨gids, hgb, -⟩ := id hk
  exact aj_groups wl wr htl htr hkb hrb hgb hkn hhn (by omega) (by omega) hU h63 hkg hk h

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
    (hA : A.c = Alg.longs (Alg.add (Alg.gather 8 los I) W))
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
    Arr.toList_long A (by unfold longWords; rw [hA]; rfl)
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
theorem dyadColumn_sub_one {n : Nat} {b0 : ByteArray} (p : Option (UInt8 × IndexCell)) (hn : n < USize.size)
    (hb : b0.size / 8 = n) :
    ∃ L bL, Kernel.dyadColumn .sub Kernel.Ew.va .long .long ⟨.long, n, .bytes b0, p⟩ (Alg.longs (Find.one 1)) =
      some (.long, L) ∧ L.ty = .long ∧ Column.bytesOf L = some bL ∧ bL.size / 8 = n ∧
      ∀ i, i < n → (Column.bitsAt bL (i * 8) 8).toInt64 =
        Kernel.Ew.intStep Kernel.Ew.sub Int64.minValue (Column.bitsAt b0 (i * 8) 8).toInt64 1 := by
  rw [show Alg.longs (Find.one 1) = ⟨.long, 1, .bytes (Find.one 1), none⟩ from rfl,
    dyadColumn_long_va (v := .sub) rfl (by decide) rfl n b0 (Find.one 1) p none]
  have hN : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' hn
  have hrun : ({ inputs := #[b0, Find.one 1] } : Kernel.Ew.Build).run ({ engine := Kernel.Ew.eVal, op := Kernel.Ew.sub,
      cls := Kernel.Ew.i64, shape := Kernel.Ew.va, a := 0, b := 1, nul := Kernel.nullPayload .long } : Kernel.Ew.Stage) n.toUSize =
      Kernel.Ew.val Kernel.Ew.sub Kernel.Ew.i64 Kernel.Ew.va Int64.minValue b0 (Kernel.atomBytes Kernel.Ew.i64 1)
        n.toUSize := by
    rw [Verify.run_val _ rfl _ _ _ 0 1 _ (by decide) (by decide)]; rfl
  have hv := Verify.val_i64_va Kernel.Ew.sub Int64.minValue b0 1 n hn
  rw [← hrun] at hv
  have hs := congrArg List.length hv
  simp only [Verify.elemsW, List.length_map, List.length_range] at hs
  have he := Verify.runEnc_elems _ _ n.toUSize 8 (by decide) (by decide) n.toUSize (by rw [hN, hs])
  rw [hv] at he
  refine ⟨_, _, rfl, by simp, ?_, ?_, fun i hi => by rw [bitsAt_elemsW he hi, Int64.toInt64_toUInt64]; rfl⟩
  · show Column.bytesOf (Kernel.payload .long n.toUSize _) = _
    have hp : ∀ x, Kernel.payload .long n.toUSize x = Column.answer ⟨.long, n,
        .foR (x.1.runEnc x.2 n.toUSize (8 : Nat).toUSize).1 (x.1.runEnc x.2 n.toUSize (8 : Nat).toUSize).2, none⟩ :=
      fun x => by simp only [Kernel.payload, hN]; rfl
    rw [hp]
    rcases Verify.answer_foR .long 8 n _ _ rfl (a := none) with e | e <;> rw [e] <;> rfl
  · have := congrArg List.length he
    simp only [Verify.elemsW, List.length_map, List.length_range] at this
    exact this

/-- **`wj` and `wj1` are `wjSpec` once their groups are known**: where `keyGroups` answers groups `gs` and ids
    that `KeyAnswers` the two sides' keys, `wjP` over dense long windows `b0`, `b1` and times `hay` answers
    `wjSpec`'s runs. `L` is the column `wjP` bins the lower edge at — `t0` itself (`wj`) or its `dyadColumn`
    `- 1` (`wj1`), words `bL`. Nothing is assumed about the times' order inside a group. -/
theorem wj_groups {κ : Type} [BEq κ] [Inhabited κ] {l r : Array Struct.KCol} {t0 t1 tr L : Column}
    {P : Parted .long} {gs : Eval.Groups} {ids : Column} {b0 bL b1 hay gids : ByteArray} (prevailing : Bool)
    (lk rk : List κ) (h0t : t0.ty = .long) (h1t : t1.ty = .long) (htr : tr.ty = .long)
    (hL : if prevailing then L = t0 else
      Kernel.dyadColumn .sub Kernel.Ew.va .long .long t0 (Alg.longs (Find.one 1)) = some (.long, L))
    (hLt : L.ty = .long) (hLb : Column.bytesOf L = some bL) (hLn : bL.size / 8 = t0.n)
    (hLw : ∀ i, i < t0.n → (Column.bitsAt bL (i * 8) 8).toInt64 =
      if prevailing then (Column.bitsAt b0 (i * 8) 8).toInt64 else (Column.bitsAt b0 (i * 8) 8).toInt64 - 1)
    (h1b : Column.bytesOf t1 = some b1) (hrb : Column.bytesOf tr = some hay)
    (hgb : Column.bytesOf ids = some gids) (h0n : b0.size / 8 = t0.n) (h1n : b1.size / 8 = t0.n)
    (hrn : hay.size / 8 = tr.n) (hlk : lk.length = t0.n) (hrk : rk.length = tr.n)
    (hU : t0.n * tr.n + t0.n + tr.n + 1 < USize.size) (h62 : t0.n * tr.n + t0.n + tr.n < 2 ^ 62)
    (hkg : Struct.keyGroups "wj" l r t0.n tr.n = .ok (gs, ids)) (hk : KeyAnswers rk lk gs ids)
    (h : Struct.wjP prevailing ⟨.long, t0⟩ ⟨.long, t1⟩ l r ⟨.long, tr⟩ = .ok P) :
    Struct.runsSpec P.segs = Struct.wjSpec prevailing lk ((nats b0).map Int64.ofNat) ((nats b1).map Int64.ofNat) rk
      ((nats hay).map Int64.ofNat) := by
  obtain ⟨g', hg', hgn, hst, -⟩ := id hk
  rw [Option.some.inj (hg'.symm.trans hgb)] at hgn hst
  have hE0 := groupEdge_long gs ids tr L tr.n htr hLt hrb hLb hgb (by omega)
  have hE1 := groupEdge_long gs ids tr t1 tr.n htr h1t hrb h1b hgb (by omega)
  have hdo : ∀ X, Find.dense "wj" .long (Column.ofBytes .long X) = .ok X := fun X => by
    simp [Find.dense, Column.ofBytes, Column.bytesOf]
  have hdi : Find.dense "wj" .long ids = .ok gids := by simp [Find.dense, hgb]
  have hdf : Find.dense "wj" .long (Kernel.longColumn (gs.firsts.push 0)) = .ok (Kernel.longBytes (gs.firsts.push 0)) := by
    simp [Find.dense, Kernel.longColumn, Column.bytesOf]
  have hN : tr.n < 2 ^ 62 := by omega
  have hn : t0.n < USize.size := by omega
  have hst' : nats (Alg.gather 8 (Kernel.longBytes (gs.firsts.push 0)) gids) =
      (List.range t0.n).map fun i => (Struct.group rk lk[i]!).head?.getD 0 := by rw [hst, hlk]
  have hgr : ∀ k s, s ∈ Struct.group rk k → s < tr.n := fun k s hs => by
    simp only [Struct.group, List.mem_filter, List.mem_range] at hs; omega
  have hhd : ∀ k, (Struct.group rk k).head?.getD 0 ≤ tr.n := fun k => by
    cases e : (Struct.group rk k).head? with
    | none => exact Nat.zero_le _
    | some s => have := hgr k s (List.mem_of_mem_head? e); exact Nat.le_of_lt this
  have hbin : ∀ (b : ByteArray) i r, Struct.binSpec ((nats hay).map Int64.ofNat) (Struct.group rk lk[i]!)
      (Column.bitsAt b (i * 8) 8).toInt64 = some r → r < tr.n := fun b i r e => hgr _ r (binSpec_mem e)
  have hEw : ∀ (b : ByteArray), b.size / 8 = t0.n → ∀ i, i < t0.n →
      Column.bitsAt (Kernel.binRows 8 false true false hay b gs.rows (Kernel.longBytes gs.bounds) gids tr.n.toUInt64)
        (i * 8) 8 = ((Struct.binSpec ((nats hay).map Int64.ofNat) (Struct.group rk lk[i]!)
          (Column.bitsAt b (i * 8) 8).toInt64).map Nat.toUInt64).getD tr.n.toUInt64 := fun b hb i hi => by
    have := binRows_group (keys := b) hk hgb (by omega) hrn hrk (i := i) (by omega)
    rwa [Nat.mul_comm 8 i] at this
  -- an edge, `max s (r + off)` at a hit and `s` at a miss, is a right row or the end `nr`
  have hedge : ∀ (b : ByteArray) off i, off ≤ 1 → ((Struct.binSpec ((nats hay).map Int64.ofNat)
      (Struct.group rk lk[i]!) (Column.bitsAt b (i * 8) 8).toInt64).map
        (max ((Struct.group rk lk[i]!).head?.getD 0) <| · + off)).getD ((Struct.group rk lk[i]!).head?.getD 0) ≤ tr.n :=
    fun b off i ho => by
      have := hhd lk[i]!
      cases e : Struct.binSpec ((nats hay).map Int64.ofNat) (Struct.group rk lk[i]!)
        (Column.bitsAt b (i * 8) 8).toInt64 with
      | none => simp only [Option.map_none, Option.getD_none]; exact this
      | some r => have := hbin b i r e; simp only [Option.map_some, Option.getD_some]; omega
  have e0 := wj_edge _ _ t0.n tr.n (if prevailing then 0 else 1)
    (fun i => Struct.binSpec ((nats hay).map Int64.ofNat) (Struct.group rk lk[i]!) (Column.bitsAt bL (i * 8) 8).toInt64)
    (fun i => (Struct.group rk lk[i]!).head?.getD 0) hn (by cases prevailing <;> decide) hN
    (fun i r _ e => hbin bL i r e) (fun i _ => by have := hhd lk[i]!; dsimp only; omega) (hEw bL hLn) hst'
  have e1 := wj_edge _ _ t0.n tr.n 1
    (fun i => Struct.binSpec ((nats hay).map Int64.ofNat) (Struct.group rk lk[i]!) (Column.bitsAt b1 (i * 8) 8).toInt64)
    (fun i => (Struct.group rk lk[i]!).head?.getD 0) hn (by decide) hN (fun i r _ e => hbin b1 i r e)
    (fun i _ => by have := hhd lk[i]!; dsimp only; omega) (hEw b1 h1n) hst'
  have hc := wj_lens _ _ t0.n _ _ hn e1 e0 fun i _ => by
    have := hedge bL (if prevailing then 0 else 1) i (by cases prevailing <;> decide)
    have := hedge b1 1 i (by decide); dsimp only; exact ⟨by omega, by omega⟩
  have hw : ∀ (b : ByteArray), b.size / 8 = t0.n → ∀ i, i < t0.n →
      ((nats b).map Int64.ofNat)[i]! = (Column.bitsAt b (i * 8) 8).toInt64 := fun b hb i hi => by
    rw [get!_map _ _ (by rw [nats_length]; omega), nats_get b (by omega), toInt64_eq_ofNat]
  -- the lower edge's bound: `t0` itself, or `wj1`'s `t0 - 1`, after which both cases run alike
  cases prevailing
  on_goal 1 =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hL hLw e0 hc
    simp only [Struct.wjP, Struct.colRows, Struct.colValue, hkg, hL, hE0, hE1, hdo, hdi, hdf, h0t, h1t, htr,
      beq_self_eq_true, Bool.and_self, ↓reduceIte, Bool.false_eq_true, bind, Except.bind, pure, Except.pure] at h
  on_goal 2 =>
    simp only [↓reduceIte] at hL hLw e0 hc
    subst hL
    simp only [Struct.wjP, Struct.colRows, Struct.colValue, hkg, hE0, hE1, hdo, hdi, hdf, h0t, h1t, htr,
      beq_self_eq_true, Bool.and_self, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
  all_goals
    split at h
    · cases h
    rename_i v hv
    have hseg := wj_tail (N := tr.n) e0 hc (fun i _ => by
        have := hedge bL 0 i (by decide); have := hedge bL 1 i (by decide); have := hedge b1 1 i (by decide)
        dsimp only; omega)
      (fun i => by have := hedge b1 1 i (by decide); dsimp only; omega) hU (by omega) rfl (Struct.of_c hv) h
    rw [hseg, Struct.wjSpec, hlk]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.1 hi
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

/-- **`wj` is `wjSpec`** at one long key column per side, the right one unmarked (`prevailing`, q's `wj`): the
    key side from `keyMatch_grouped`, both edges from `binRows` inside the key group. -/
theorem wj_long {cl cr t0 t1 tr : Column} {wl wr : List UInt64} {P : Parted .long} {b0 b1 hay : ByteArray}
    (hlt : cl.ty = .long) (hrt : cr.ty = .long) (hwl : longWords cl = some wl) (hwr : longWords cr = some wr)
    (hln : wl.length = cl.n) (hrn : wr.length = cr.n) (hcl : cl.n = t0.n) (hcr : cr.n = tr.n)
    (hlwf : cl.WF) (hlR : Find.Readable .long cl)
    (hattr : ∀ a cell, cr.attr = some (a, cell) → a ≠ 1 ∧ a ≠ 2 ∧ a ≠ 3 ∧ a ≠ 4)
    (h0t : t0.ty = .long) (h1t : t1.ty = .long) (htr : tr.ty = .long)
    (h0b : Column.bytesOf t0 = some b0) (h1b : Column.bytesOf t1 = some b1) (hrb : Column.bytesOf tr = some hay)
    (h0n : b0.size / 8 = t0.n) (h1n : b1.size / 8 = t0.n) (hhn : hay.size / 8 = tr.n)
    (hU : t0.n * tr.n + t0.n + tr.n + 1 < USize.size) (h62 : t0.n * tr.n + t0.n + tr.n < 2 ^ 62)
    (h : Struct.wjP true ⟨.long, t0⟩ ⟨.long, t1⟩ #[⟨.long, cl⟩] #[⟨.long, cr⟩] ⟨.long, tr⟩ = .ok P) :
    Struct.runsSpec P.segs = Struct.wjSpec true wl ((nats b0).map Int64.ofNat) ((nats b1).map Int64.ofNat) wr
      ((nats hay).map Int64.ofNat) := by
  have hkg : Struct.keyGroups "wj" #[⟨.long, cl⟩] #[⟨.long, cr⟩] t0.n tr.n =
      .ok (Eval.keyMatch #[.vector cr] tr.n #[.vector cl] t0.n) := by
    simp [Struct.keyGroups, Struct.colRows, Struct.colValue, hcl, hcr]; rfl
  have hk := keyMatch_grouped tr.n t0.n hrt hlt hwr hrn (by omega) (by omega) (by omega) hlwf hlR hwl hattr
  obtain ⟨gids, hgb, -⟩ := id hk
  exact wj_groups (L := t0) (bL := b0) true wl wr h0t h1t htr (if_pos rfl) h0t h0b h0n (fun _ _ => (if_pos rfl).symm) h1b hrb hgb h0n
    h1n hhn (by omega) (by omega) hU h62 hkg hk h

/-- **`wj1` is `wjSpec false`** at one long key column per side, the right one unmarked (q's `wj1`): as `wj_long`,
    the lower edge binned at `dyadColumn_sub_one`'s `w₀ - 1`. The window `t0` is dense (`hb0`), and no `w₀` is
    `0N` (`hnul`): q's `0N - 1` is `0N`, where `wjSpec`'s `Int64` subtraction wraps it to `0W`. -/
theorem wj1_long {cl cr t0 t1 tr : Column} {wl wr : List UInt64} {P : Parted .long} {b0 b1 hay : ByteArray}
    (hlt : cl.ty = .long) (hrt : cr.ty = .long) (hwl : longWords cl = some wl) (hwr : longWords cr = some wr)
    (hln : wl.length = cl.n) (hrn : wr.length = cr.n) (hcl : cl.n = t0.n) (hcr : cr.n = tr.n)
    (hlwf : cl.WF) (hlR : Find.Readable .long cl)
    (hattr : ∀ a cell, cr.attr = some (a, cell) → a ≠ 1 ∧ a ≠ 2 ∧ a ≠ 3 ∧ a ≠ 4)
    (h0t : t0.ty = .long) (h1t : t1.ty = .long) (htr : tr.ty = .long)
    (hb0 : t0.enc = .bytes b0) (h1b : Column.bytesOf t1 = some b1) (hrb : Column.bytesOf tr = some hay)
    (h0n : b0.size / 8 = t0.n) (h1n : b1.size / 8 = t0.n) (hhn : hay.size / 8 = tr.n)
    (hnul : ∀ i, i < t0.n → ((nats b0).map Int64.ofNat)[i]! ≠ Int64.minValue)
    (hU : t0.n * tr.n + t0.n + tr.n + 1 < USize.size) (h62 : t0.n * tr.n + t0.n + tr.n < 2 ^ 62)
    (h : Struct.wjP false ⟨.long, t0⟩ ⟨.long, t1⟩ #[⟨.long, cl⟩] #[⟨.long, cr⟩] ⟨.long, tr⟩ = .ok P) :
    Struct.runsSpec P.segs = Struct.wjSpec false wl ((nats b0).map Int64.ofNat) ((nats b1).map Int64.ofNat) wr
      ((nats hay).map Int64.ofNat) := by
  have hkg : Struct.keyGroups "wj" #[⟨.long, cl⟩] #[⟨.long, cr⟩] t0.n tr.n =
      .ok (Eval.keyMatch #[.vector cr] tr.n #[.vector cl] t0.n) := by
    simp [Struct.keyGroups, Struct.colRows, Struct.colValue, hcl, hcr]; rfl
  have hk := keyMatch_grouped tr.n t0.n hrt hlt hwr hrn (by omega) (by omega) (by omega) hlwf hlR hwl hattr
  obtain ⟨gids, hgb, -⟩ := id hk
  have ht0 : t0 = ⟨.long, t0.n, .bytes b0, t0.attr⟩ := by
    obtain ⟨t, n, e, a⟩ := t0; simp only at h0t hb0; subst h0t hb0; rfl
  obtain ⟨L, bL, hd, hLt, hLb, hLn, hLw⟩ := dyadColumn_sub_one (n := t0.n) t0.attr (by omega) h0n
  rw [← ht0] at hd
  refine wj_groups false wl wr h0t h1t htr hd hLt hLb hLn (fun i hi => ?_) h1b hrb hgb h0n h1n hhn
    (by omega) (by omega) hU h62 hkg hk h
  have hx := hnul i hi
  rw [get!_map _ _ (by rw [nats_length]; omega), nats_get b0 (by omega), ← toInt64_eq_ofNat] at hx
  rw [hLw i hi, if_neg Bool.false_ne_true]
  show (if ((Column.bitsAt b0 (i * 8) 8).toInt64 == Int64.minValue || (1 : Int64) == Int64.minValue) then
    Int64.minValue else (Column.bitsAt b0 (i * 8) 8).toInt64 - 1) = _
  rw [show ((1 : Int64) == Int64.minValue) = false from rfl, Bool.or_false, if_neg (by simpa using hx)]

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

/-- **`wjSpec` is a window per left row** (`prevailing`): row `i`'s run is the right rows `[lo i, hi i)`, both
    edges inside `rk`, so the aggregate over it is `ix_winAt`'s `Λ(winAt lo hi) ≫ enum ≫ list(xs) ≫ f`. -/
theorem wjSpec_runs {κ : Type} [BEq κ] [Inhabited κ] (lk : List κ) (w₀ w₁ : List Int64) (rk : List κ)
    (rt : List Int64) : ∃ lo hi : Nat → Nat, (∀ i, lo i ≤ rk.length ∧ hi i ≤ rk.length) ∧
      Struct.wjSpec true lk w₀ w₁ rk rt = Struct.runsSpec ((List.range lk.length).map fun i =>
        (List.range' (lo i) (hi i - lo i)).map Int64.ofNat) := by
  have hgr : ∀ k s, s ∈ Struct.group rk k → s < rk.length := fun k s hs => by
    simp only [Struct.group, List.mem_filter, List.mem_range] at hs; omega
  have hb : ∀ (i : Nat) (x : Int64) (off : Nat), off ≤ 1 → (match (Struct.group rk lk[i]!).head? with
      | none => 0
      | some s => ((Struct.binSpec rt (Struct.group rk lk[i]!) x).map (max s <| · + off)).getD s) ≤ rk.length :=
    fun i x off ho => by
      cases e : (Struct.group rk lk[i]!).head? with
      | none => exact Nat.zero_le _
      | some s =>
        have := hgr _ s (List.mem_of_mem_head? e)
        cases e' : Struct.binSpec rt (Struct.group rk lk[i]!) x with
        | none => simp only [Option.map_none, Option.getD_none]; omega
        | some r =>
          have := hgr _ r (binSpec_mem e'); simp only [Option.map_some, Option.getD_some]
          rw [Nat.max_def]; split <;> omega
  refine ⟨fun i => match (Struct.group rk lk[i]!).head? with
      | none => 0
      | some s => ((Struct.binSpec rt (Struct.group rk lk[i]!) w₀[i]!).map (max s <| · + 0)).getD s,
    fun i => match (Struct.group rk lk[i]!).head? with
      | none => 0
      | some s => ((Struct.binSpec rt (Struct.group rk lk[i]!) w₁[i]!).map (max s <| · + 1)).getD s,
    fun i => ⟨hb i _ 0 (by decide), hb i _ 1 (by decide)⟩, ?_⟩
  unfold Struct.wjSpec
  congr 1
  apply List.map_congr_left
  intro i _
  dsimp only
  cases (Struct.group rk lk[i]!).head? with
  | none => rfl
  | some s =>
    simp only [↓reduceIte, List.range'_eq_map_range, List.map_map]
    try rfl

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
#print axioms firsts_of_buckets
#print axioms groupColumn_long
#print axioms keyColumns_long
#print axioms keyMatch_grouped
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

end LeetQ.Rel.Verb
