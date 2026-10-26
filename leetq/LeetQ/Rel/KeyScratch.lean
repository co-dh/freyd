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

end LeetQ.Rel.Verb
