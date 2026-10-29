/-
  `Λ`'s carrier groups its relation: `transposeP R` answers keys one-to-one, each with the nonempty
  segment of `R`'s values at that key. Proved from the kernels' Lean bodies, encoding by encoding of the
  key's `codes`.
-/
import LeetQ.Rel.Prog
import LeetQ.Rel.SpecAmend
import QLean.Verify.Where
import QLean.Verify.Group

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel LeetQ.Rel
open LeetQ.Rel.Find (expand one)

/-- **`codeKind`'s lane holds its codes**: at a lane of at most four bytes, the `card` codes fit it. -/
theorem codeKind_fits (c : Nat) (h : (codeKind c).width ≤ 4) :
    c ≤ 2 ^ (8 * (codeKind c).width) ∧ ((codeKind c).width = 1 ∨ (codeKind c).width = 2 ∨ (codeKind c).width = 4) := by
  unfold codeKind at h ⊢
  split <;> rename_i h1
  · exact ⟨by simpa [Scan.Kind.width] using h1, by simp [Scan.Kind.width]⟩
  · split <;> rename_i h2
    · exact ⟨by simpa [Scan.Kind.width] using h2, by simp [Scan.Kind.width]⟩
    · split <;> rename_i h3
      · exact ⟨by simpa [Scan.Kind.width] using h3, by simp [Scan.Kind.width]⟩
      · simp [h1, h2, h3, Scan.Kind.width] at h

theorem codeKind_small {t : Nat} (ht : t ≤ 2 ^ 32) : (codeKind t).width ≤ 4 := by
  unfold codeKind; split
  · simp [Scan.Kind.width]
  · split
    · simp [Scan.Kind.width]
    · simp [Scan.Kind.width]

theorem nul_toInt : nul.toInt = -2 ^ 63 := by decide

theorem zero_ne_nul : (0 : Int64) ≠ nul := fun e => by
  have h1 := congrArg Int64.toInt e; rw [nul_toInt] at h1; simp at h1

/-- A checked `Except` step of one part, mapped into `some #[·]`, answered `ok` only where it passed. -/
theorem ok_of_map_ite {α : Type} {p : Prop} [Decidable p] {x : α} {e : String} {cs : Array α}
    (h : ((fun a => some #[a]) <$> (if p then pure x else throw e) : Except String (Option (Array α))) =
      .ok (some cs)) : p ∧ cs = #[x] := by
  by_cases hp : p
  · simp only [hp, if_true] at h
    exact ⟨hp, by cases h; rfl⟩
  · simp only [hp, if_false] at h; cases h

/-- **`rangeOffsets` codes one dense long part faithfully**: where it answers, it answers one code of the
    part's `b.size / 8` rows at a byte lane of at most four bytes, equal exactly where the longs are.
    `total ≤ 2³²` is genuine: past it the lane may be eight bytes, `card` past `2⁶³`, and a wrapped offset
    meets the null's code. -/
theorem rangeOffsets_bytes {b : ByteArray} {n total : Nat} {cs : Array Code} (hU : 2 ^ 32 < USize.size)
    (ht : total ≤ 2 ^ 32) (hn : b.size / 8 ≤ 2 ^ 32)
    (h : rangeOffsets .long #[(n, .bytes b)] total = .ok (some cs)) :
    ∃ c : Code, cs = #[c] ∧ c.n = b.size / 8 ∧ (c.w = 8 ∨ c.w = 16 ∨ c.w = 32) ∧ c.b.size = c.w / 8 * c.n ∧
      ∀ i j, i < b.size / 8 → j < b.size / 8 →
        (Column.idAt c.b c.w i = Column.idAt c.b c.w j ↔
          (Column.bitsAt b (i * 8) 8).toInt64 = (Column.bitsAt b (j * 8) 8).toInt64) := by
  have hnU : b.size / 8 < USize.size := by omega
  -- every non-null long lies between the two `overBytes` bounds
  have bnd : ∀ i, i < b.size / 8 → (Column.bitsAt b (i * 8) 8).toInt64 ≠ nul →
      overBytes .lesser Ew.i64 nul b ≤ (Column.bitsAt b (i * 8) 8).toInt64 ∧
        (Column.bitsAt b (i * 8) 8).toInt64 ≤ overBytes .greater Ew.i64 nul b := fun i hi hx => by
    have hw : Ew.width Ew.i64 = 8 := by decide
    have e : Ew.signed Ew.i64 (Ew.elem Ew.i64 b i) = (Column.bitsAt b (i * 8) 8).toInt64 := by
      simp only [Ew.signed, Ew.elem, hw]; rfl
    rw [← e] at hx ⊢; exact overBytes_bounds Ew.i64 nul b (by rw [hw]; exact hi) hx
  simp only [rangeOffsets, Array.mapM_eq_mapM_toList, List.mapM_cons, List.mapM_nil] at h
  generalize overBytes .lesser Ew.i64 nul b = L at h bnd
  generalize overBytes .greater Ew.i64 nul b = H at h bnd
  simp at h
  have hloL : (min Int64.maxValue L).toInt ≤ L.toInt := by
    show (if Int64.maxValue ≤ L then Int64.maxValue else L).toInt ≤ L.toInt
    split
    · exact Int64.le_iff_toInt_le.1 ‹_›
    · exact Int.le_refl _
  have hHhi : H.toInt ≤ (max (Int64.minValue + 1) H).toInt := by
    show H.toInt ≤ (if Int64.minValue + 1 ≤ H then H else Int64.minValue + 1).toInt
    split
    · exact Int.le_refl _
    · rename_i h'; have := mt Int64.le_iff_toInt_le.2 h'; omega
  generalize min Int64.maxValue L = lo at h hloL
  generalize max (Int64.minValue + 1) H = hi at h hHhi
  have xb : ∀ i, i < b.size / 8 → (Column.bitsAt b (i * 8) 8).toInt64 ≠ nul →
      lo.toInt ≤ (Column.bitsAt b (i * 8) 8).toInt64.toInt ∧ (Column.bitsAt b (i * 8) 8).toInt64.toInt ≤ hi.toInt :=
    fun i hi hx => by
      have := bnd i hi hx
      exact ⟨by have := Int64.le_iff_toInt_le.1 this.1; omega, by have := Int64.le_iff_toInt_le.1 this.2; omega⟩
  -- the shared tail: `offsets_faithful` at whichever base and payload the branch took
  have tail : ∀ (base : Int64) (b' : ByteArray) (card kw : Nat), base ≠ nul → kw ≤ 4 →
      (codeKind card).width = kw → 1 ≤ card →
      (∀ i, i < b.size / 8 → (Column.bitsAt b (i * 8) 8).toInt64 ≠ nul →
        base.toInt ≤ (Column.bitsAt b (i * 8) 8).toInt64.toInt ∧
          (Column.bitsAt b (i * 8) 8).toInt64.toInt - base.toInt + 2 ≤ card) →
      (∀ i, i < b.size / 8 → (Column.bitsAt b' (i * 8) 8).toInt64 =
        if (Column.bitsAt b (i * 8) 8).toInt64 = nul then nul else (Column.bitsAt b (i * 8) 8).toInt64 + -base) →
      (enumIds (USize.ofNat (b.size / 8)) (USize.ofNat card) (USize.ofNat (card - 1))
        (USize.ofNat 8 * USize.ofNat kw) b').snd.toNat = b.size / 8 →
      ∃ c : Code, #[(⟨8 * kw, b.size / 8, card, (enumIds (USize.ofNat (b.size / 8)) (USize.ofNat card)
          (USize.ofNat (card - 1)) (USize.ofNat 8 * USize.ofNat kw) b').fst⟩ : Code)] = #[c] ∧
        c.n = b.size / 8 ∧ (c.w = 8 ∨ c.w = 16 ∨ c.w = 32) ∧ c.b.size = c.w / 8 * c.n ∧
        ∀ i j, i < b.size / 8 → j < b.size / 8 →
          (Column.idAt c.b c.w i = Column.idAt c.b c.w j ↔
            (Column.bitsAt b (i * 8) 8).toInt64 = (Column.bitsAt b (j * 8) 8).toInt64) := by
    intro base b' card kw hb hk4 hkw hc1 hr hv hok
    obtain ⟨hfit, hw3⟩ := codeKind_fits card (by omega)
    rw [hkw] at hfit hw3
    have hmul : USize.ofNat 8 * USize.ofNat kw = (8 * kw).toUSize := by simp [USize.ofNat_mul]
    rw [hmul] at hok ⊢
    have hcU : card < USize.size := by
      have : 2 ^ (8 * kw) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hwu : (8 * kw).toUSize.toNat = 8 * kw := USize.toNat_ofNat_of_lt' (by omega)
    have hs : (enumIds (b.size / 8).toUSize card.toUSize (card - 1).toUSize (8 * kw).toUSize b').1.size =
        kw * (b.size / 8) := by
      simp only [enumIds]
      rw [hwu, USize.toNat_ofNat_of_lt' hnU]; exact (Verify.packIds_bytes kw _ _ (by omega) (by omega)).1
    refine ⟨_, rfl, rfl, by rcases hw3 with h | h | h <;> simp [h], by rw [hs, Nat.mul_div_cancel_left kw (by decide : 0 < 8)], fun i j hi hj => ?_⟩
    exact offsets_faithful (fun i => (Column.bitsAt b (i * 8) 8).toInt64) base hnU hcU hc1
      (by have : 2 ^ (8 * kw) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega); omega)
      (by rcases hw3 with h | h | h <;> simp [h]) hfit hb
      (USize.ofNat_toNat.symm.trans (congrArg USize.ofNat hok)) hv hr hi hj
  have hk4 : (codeKind total).width ≤ 4 := codeKind_small ht
  split at h
  · split at h
    · simp [pure, Except.pure] at h
    · rename_i hlh
      split at h
      · rename_i hwid
        have hlo : lo ≠ nul := fun e => hlh (.inl e)
        have hlohi : lo.toInt ≤ hi.toInt := by
          have := mt Int64.lt_iff_toInt_lt.2 (fun e => hlh (.inr e)); omega
        have h0 : (0 : Int64).toInt = 0 := by decide
        split at h
        · rename_i hP
          rw [if_pos (fun e => absurd hP.2 (e hP.1))] at h
          simp only [h0, Int.sub_zero] at h
          obtain ⟨hok, rfl⟩ := ok_of_map_ite h
          have hl0 := Int64.le_iff_toInt_le.1 hP.1
          rw [h0] at hl0
          refine tail 0 b (hi.toInt + 2).toNat (codeKind (hi.toInt - lo.toInt + 2).toNat).width zero_ne_nul
            (by omega) hP.2 (by omega) (fun i hi hx => ?_) (fun i hi => ?_) hok
          · have := xb i hi hx; rw [h0]; omega
          · split <;> simp_all
        · rename_i hP
          obtain ⟨hok, rfl⟩ := ok_of_map_ite h
          refine tail lo _ (hi.toInt - lo.toInt + 2).toNat (codeKind (hi.toInt - lo.toInt + 2).toNat).width hlo (by omega) rfl (by omega) (fun i hi hx => ?_) (fun i hi => ?_) hok
          · have := xb i hi hx; omega
          · by_cases hl0 : lo = 0
            · rw [if_pos (fun _ => hl0)]; subst hl0; split <;> simp_all
            · rw [if_neg (fun e => hl0 (e fun a b => hP ⟨a, b⟩))]
              have hneg : -lo ≠ nul := fun e => hlo (by rw [← Int64.neg_neg (a := lo), e]; decide)
              have := shift_elem b (-lo) hnU hi
              rw [Int64.toUInt64_neg] at this
              rw [this]; simp only [hneg, or_false]
      · simp [pure, Except.pure] at h
  · simp [pure, Except.pure] at h

/-- **A code at a byte lane, faithful to `x`, cuts a contiguous `x` into its runs** (items 3 and 6's
    core): `Code.runStarts` is `runStarts` at the lane's width, whose search key (`Kernel.key`) is the
    id `idAt` reads, so `runStarts_group` applies with the code's own count. -/
theorem code_runs {α : Type} (c : Code) (hw : c.w = 8 ∨ c.w = 16 ∨ c.w = 32) (hsz : c.b.size = c.w / 8 * c.n)
    (h63 : c.n < 2 ^ 63) (x : Nat → α)
    (hf : ∀ i j, i < c.n → j < c.n → (Column.idAt c.b c.w i = Column.idAt c.b c.w j ↔ x i = x j))
    (hcont : ∀ s t u, s ≤ t → t ≤ u → u < c.n → x s = x u → x t = x s) :
    let R := fun j => (Column.bitsAt c.runStarts (8 * j) 8).toInt64.toInt
    ∃ m, c.runStarts.size = 8 * (m + 1) ∧ (∀ j, j ≤ m → R j = ((R j).toNat : Int)) ∧ (R m).toNat = c.n ∧
      (∀ i j, i < j → j ≤ m → (R i).toNat < (R j).toNat) ∧
      (∀ j j', j < m → j' < m → x (R j).toNat = x (R j').toNat → j = j') ∧
      (∀ s j, s < c.n → j < m → (x s = x (R j).toNat ↔ (R j).toNat ≤ s ∧ s < (R (j + 1)).toNat)) := by
  intro R
  obtain ⟨kw, hkw, hw', hrs⟩ : ∃ kw : Nat, (kw = 1 ∨ kw = 2 ∨ kw = 4) ∧ c.w = 8 * kw ∧
      c.runStarts = Kernel.runStarts kw.toUSize false c.b := by
    rcases hw with h | h | h
    · exact ⟨1, by simp, by omega, by simp only [Code.runStarts, Code.kind, h, laneKind]; rfl⟩
    · exact ⟨2, by simp, by omega, by simp only [Code.runStarts, Code.kind, h, laneKind]; rfl⟩
    · exact ⟨4, by simp, by omega, by simp only [Code.runStarts, Code.kind, h, laneKind]; rfl⟩
  have hkU : kw.toUSize.toNat = kw :=
    USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by rcases hkw with rfl | rfl | rfl <;> decide) USize.le_size)
  have hn : c.b.size / kw.toUSize.toNat = c.n := by
    rw [hkU, hsz, hw']; rcases hkw with rfl | rfl | rfl <;> omega
  have G := runStarts_group kw.toUSize false c.b (by rw [hn]; exact h63) x (fun i j hi hj => by
      rw [hn] at hi hj
      rw [← hf i j hi hj, hw', Verb.idAt_bytes c.b i (by omega), Verb.idAt_bytes c.b j (by omega), hkU]
      simp only [Kernel.key, Kernel.normalise, Bool.not_false, if_true]
      exact ⟨fun h => UInt64.toNat_inj.1 h, fun h => congrArg _ h⟩)
    (by rw [hn]; exact hcont)
  rw [hn] at G
  simp only [R]; rw [hrs]; exact G

/-- **`codes` of one part that is not a bitmap answers `rangeOffsets`' codes, where those exist.** -/
theorem codes_range {n : Nat} {e : Enc} {os : Array Code} (hb : ∀ b, e ≠ .bits b)
    (hr : rangeOffsets .long #[(n, e)] n = .ok (some os)) : codes .long #[(n, e)] = .ok os := by
  cases e <;> simp_all [codes, Array.mapM_eq_mapM_toList] <;> rfl

/-- **A dense long column's `codes`, on `rangeOffsets`' branch, are one faithful code**: one code of its
    `m` rows at a lane of one, two or four bytes, equal exactly where the column's elements are. -/
theorem codes_long_bytes {m : Nat} (x : Arr .long m) {b : ByteArray} (hc : x.enc = .bytes b)
    (hU : 2 ^ 32 < USize.size) (hm : m ≤ 2 ^ 32) {os : Array Code}
    (hr : rangeOffsets .long #[x.part] m = .ok (some os)) :
    ∃ c : Code, os = #[c] ∧ codes .long #[x.part] = .ok #[c] ∧ c.n = m ∧ (c.w = 8 ∨ c.w = 16 ∨ c.w = 32) ∧
      c.b.size = c.w / 8 * c.n ∧
      ∀ i j : Fin m, (Column.idAt c.b c.w i = Column.idAt c.b c.w j ↔ x.get i = x.get j) := by
  have hs := Arr.n_long_bytes x hc
  have hp : x.part = (m, .bytes b) := by simp only [Arr.part, hc]
  rw [hp] at hr ⊢
  obtain ⟨c, rfl, hn, hw, hsz, hf⟩ := rangeOffsets_bytes hU hm (by omega) hr
  refine ⟨c, rfl, codes_range (fun _ e => by cases e) hr, by omega, hw, hsz, fun i j => ?_⟩
  rw [Arr.get_long_bytes x hc, Arr.get_long_bytes x hc]
  exact hf i j (by omega) (by omega)

/-- A word whose long reading is not negative reads the same as a natural. -/
theorem toInt64_toInt_of_nonneg (u : UInt64) (h : 0 ≤ u.toInt64.toInt) : u.toInt64.toInt = u.toNat := by
  have hl := u.toNat_lt
  have e : u.toInt64.toInt = if decide (2 ^ 63 ≤ u.toNat) = true then (u.toNat : Int) - (2 ^ 64 : Nat) else u.toNat := by
    rw [Int64.toInt, BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide]; rfl
  rw [e] at h ⊢
  by_cases hc : 2 ^ 63 ≤ u.toNat <;> simp [hc] at h ⊢ <;> omega

theorem runsP_long {v : QAtomicType} {n : Nat} (key : Arr .long n) {b : ByteArray} (hc : key.enc = .bytes b)
    (hU : 2 ^ 32 < USize.size) (hn : n ≤ 2 ^ 32) {os : Array Code}
    (hr : rangeOffsets .long #[key.part] n = .ok (some os))
    (hcont : ∀ s t u : Fin n, s ≤ t → t ≤ u → key.get s = key.get u → key.get t = key.get s)
    (val : Arr v n) {g : Nat} {keys : Arr .long g} {P : Parted v}
    (h : runsP .long key.part val = .ok ⟨g, keys, P⟩) :
    P.n = n ∧ P.g = g ∧ (∀ j j' : Fin g, keys.get j = keys.get j' → j = j') ∧
      ∀ (s : Fin n) (j : Fin g), (key.get s = keys.get j ↔ Parted.group P.o s = j) := by
  obtain ⟨c, -, hcodes, hcn, hw, hsz, hf⟩ := codes_long_bytes key hc hU hn hr
  let x : Nat → Int64 := fun i => if hi : i < n then key.get ⟨i, hi⟩ else 0
  have hf' : ∀ i j, i < c.n → j < c.n → (Column.idAt c.b c.w i = Column.idAt c.b c.w j ↔ x i = x j) :=
    fun i j hi hj => by
      rw [hcn] at hi hj; simp only [x, dif_pos hi, dif_pos hj]; exact hf ⟨i, hi⟩ ⟨j, hj⟩
  have hcont' : ∀ s t u, s ≤ t → t ≤ u → u < c.n → x s = x u → x t = x s := fun s t u h1 h2 hu e => by
    rw [hcn] at hu
    simp only [x, dif_pos (show s < n by omega), dif_pos (show t < n by omega), dif_pos hu] at e ⊢
    exact hcont ⟨s, by omega⟩ ⟨t, by omega⟩ ⟨u, hu⟩ h1 h2 e
  obtain ⟨m, hst, hnn, hlast, hasc, hinj, hgrp⟩ := code_runs c hw hsz (by omega) x hf' hcont'
  rw [hcn] at hlast hgrp
  simp only [runsP, hcodes, single, bind, Except.bind, pure, Except.pure] at h
  rw [dif_pos (show #[c].size = 1 from rfl)] at h
  dsimp only at h
  split at h
  · simp at h
  rename_i ds hp
  rcases ds with ⟨k, e⟩
  obtain ⟨src, hsrc, hk, he⟩ := Verb.pick_gather (t := .long) (w := 8) rfl (.inl rfl) key
    (fun _ _ _ e => by rw [hc] at e; cases e) _ hp
  simp only [groupedP, bind, Except.bind, pure, Except.pure, List.getElem_toArray, List.getElem_cons_zero] at h hp hk he
  split at h
  · simp at h
  rename_i o ho
  split at h
  · rename_i P' hP
    split at h
    · simp at h
    rename_i keys' hks
    cases h
    dsimp only at hnn hlast hasc hinj hgrp
    -- the count of keys is the count of starts
    have hgm : g = m := by
      rw [hk, ByteArray.size_extract, hst]; omega
    subst hgm
    -- the parted list's offsets are the starts the kernel wrote
    have hoe : o.enc = .bytes c.runStarts := Verb.ofPart_enc ho
    unfold Parted.of? at hP
    rw [hoe] at hP
    simp only [longBytes, Option.bind_eq_bind, Option.bind_some] at hP
    split at hP
    case isFalse => cases hP
    split at hP
    case isFalse => cases hP
    cases hP
    -- each key is the column's element at its run's start
    have hsrc' : src = b := by rw [hc] at hsrc; simp [Enc.bytesOf] at hsrc; exact hsrc.symm
    subst hsrc'
    have hbn := Arr.n_long_bytes key hc
    have hR : ∀ j, j < g → (Column.bitsAt c.runStarts (8 * j) 8).toInt64.toInt.toNat < n := fun j hj => by
      have := hasc j g hj (Nat.le_refl _); omega
    have hRn : ∀ j, j ≤ g → (Column.bitsAt c.runStarts (8 * j) 8).toNat =
        (Column.bitsAt c.runStarts (8 * j) 8).toInt64.toInt.toNat := fun j hj => by
      have := toInt64_toInt_of_nonneg _ (by rw [hnn j hj]; omega); omega
    have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
    have hkey : ∀ j : Fin g, keys.get j = x (Column.bitsAt c.runStarts (8 * j) 8).toInt64.toInt.toNat := fun j => by
      have hke : keys.enc = e := Verb.ofPart_enc hks
      rw [he] at hke
      rw [Arr.get_long_bytes keys hke]
      obtain ⟨-, hg⟩ := Verify.gatherBytes_spec (8 : Nat).toUSize (by rw [h8]; exact Nat.le_refl _) ((Kernel.nullBits .long).getD 0)
        src (c.runStarts.extract 0 (c.runStarts.size - 8))
      have hj : j.1 < (c.runStarts.extract 0 (c.runStarts.size - 8)).size / 8 := by
        rw [ByteArray.size_extract, hst]; omega
      have g1 := hg j hj
      rw [h8] at g1
      rw [g1, Verify.bitsAt_extract _ (by rw [hst]; omega), Nat.zero_add, Nat.mul_comm j.1 8, hRn j (by omega),
        if_pos (by rw [hbn]; exact hR j j.2)]
      simp only [x, dif_pos (hR j j.2)]
      rw [Arr.get_long_bytes key hc]
    refine ⟨rfl, rfl, fun j j' e => Fin.ext (hinj j j' j.2 j'.2 (by rw [← hkey, ← hkey, e])), fun s j => ?_⟩
    have hof : ∀ (a : Arr .long (g + 1)), a.enc = .bytes c.runStarts → ∀ i (hi : i ≤ g), (a.toList[i]!).toNatClampNeg =
        (Column.bitsAt c.runStarts (8 * i) 8).toInt64.toInt.toNat := fun a ha i hi => by
      rw [getElem!_pos _ i (by rw [Arr.length_toList]; omega), Arr.getElem_toList, Arr.get_long_bytes _ ha]
      simp only [Int64.toNatClampNeg, Nat.mul_comm i 8]
    rw [Verb.group_iff (Parted.co _) j.2, hof _ rfl j (by omega), hof _ rfl (j + 1) (by omega), hkey j, ← hgrp s j s.2 j.2]
    simp only [x, dif_pos s.2]
  · first | simp at h | simp [throw, throwThe, MonadExceptOf.throw] at h | cases h

/-- A code at a byte lane is read at an integral sort layout of one, two or four bytes. -/
theorem byteLane {c : Code} (hw : c.w = 8 ∨ c.w = 16 ∨ c.w = 32) :
    ∃ k : Scan.Kind, (k = .u8 ∨ k = .i16 ∨ k = .i32) ∧ c.w = 8 * k.width ∧ c.kind = some k := by
  rcases hw with h | h | h
  · exact ⟨.u8, .inl rfl, by rw [h]; rfl, by simp only [Code.kind, h, laneKind]⟩
  · exact ⟨.i16, .inr (.inl rfl), by rw [h]; rfl, by simp only [Code.kind, h, laneKind]⟩
  · exact ⟨.i32, .inr (.inr rfl), by rw [h]; rfl, by simp only [Code.kind, h, laneKind]⟩

/-- **A byte-lane code's `grade` is a permutation of its rows ascending by a key that agrees exactly where
    the codes do** (item 4): `Order.grade` at the lane's layout (`keyAt`), or `gradeLane` (the id itself)
    where an `i16`/`i32` code would read past the sign. -/
theorem code_grade (c : Code) (hw : c.w = 8 ∨ c.w = 16 ∨ c.w = 32) (hsz : c.b.size = c.w / 8 * c.n)
    (hnU : c.n < USize.size) :
    ∃ κ : Nat → UInt64, (Verify.ids c.grade).Perm (List.range c.n) ∧
      (Verify.ids c.grade).Pairwise (fun i j => κ i ≤ κ j) ∧
      ∀ i j, (κ i = κ j ↔ Column.idAt c.b c.w i = Column.idAt c.b c.w j) := by
  have hn : c.n.toUSize.toNat = c.n := USize.toNat_ofNat_of_lt' hnU
  obtain ⟨k, hk, hkw, hkind⟩ := byteLane hw
  have hkw8 : k.width ≤ 8 := by rcases hk with rfl | rfl | rfl <;> decide
  have hb : c.b.size = k.width * c.n := by
    rcases hk with rfl | rfl | rfl <;> simp only [Scan.Kind.width] at hkw ⊢ <;> rw [hsz, hkw] <;> omega
  have hid : ∀ i, Column.idAt c.b c.w i = (Column.bitsAt c.b (i * k.width) k.width).toNat := fun i => by
    rw [hkw]; exact Verb.idAt_bytes c.b i hkw8
  have heq : ∀ i j, (Column.bitsAt c.b (i * k.width) k.width = Column.bitsAt c.b (j * k.width) k.width ↔
      Column.idAt c.b c.w i = Column.idAt c.b c.w j) := fun i j => by
    rw [hid, hid]; exact ⟨congrArg _, UInt64.toNat_inj.1⟩
  simp only [Code.grade, hkind]
  split
  · obtain ⟨hp, hs⟩ := Verify.gradeLane_spec false c.n.toUSize c.w.toUSize c.b
    have hwU : c.w.toUSize.toNat = c.w :=
      USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by rcases hk with rfl | rfl | rfl <;> simp [hkw, Scan.Kind.width]) USize.le_size)
    have hcap : Column.idsCap c.b c.w c.n = c.n := by
      unfold Column.idsCap
      rcases hk with rfl | rfl | rfl <;> simp only [Scan.Kind.width] at hkw hb <;> rw [if_neg (by omega), hb, hkw] <;> omega
    rw [hwU, hn, hcap] at hp; rw [hwU] at hs
    refine ⟨fun i => Column.bitsAt c.b (i * k.width) k.width, hp, hs.imp fun h => ?_, heq⟩
    have := h.1; simp only [Bool.false_eq_true, if_false, hid] at this; exact UInt64.le_iff_toNat_le.2 this
  · obtain ⟨hp, hs⟩ := Verify.grade_spec k false c.n.toUSize c.b
    have hav : k.avail c.b = c.n := by
      rcases hk with rfl | rfl | rfl <;> simp only [Scan.Kind.avail, Scan.Kind.width] at hb ⊢ <;> omega
    rw [hn, hav, Nat.min_self] at hp
    refine ⟨Order.keyAt k c.b, hp, hs.imp fun h => by simpa [Verify.keyOrd] using h.1, fun i j => ?_⟩
    rw [Verify.keyAt_eq_iff (by rcases hk with rfl | rfl | rfl <;> simp) c.b i j]; exact heq i j

/-- The long read at row `s` of an index column, as a natural. -/
abbrev at8 (p : ByteArray) (s : Nat) : Nat := (Column.bitsAt p (s * 8) 8).toNat

theorem ids_eq_map (p : ByteArray) : Verify.ids p = (List.range (p.size / 8)).map (at8 p) := rfl

/-- **`gradeBy`'s step at a byte-lane code keeps a permutation, and sorts by the code** (item 4): `p` a
    permutation of the `c.n` rows, the grade of `c` gathered through `p`, composed with `p`, is again one,
    and along it the rows of any `x` the code is faithful to are contiguous. -/
theorem grade_step {α : Type} (c : Code) (hw : c.w = 8 ∨ c.w = 16 ∨ c.w = 32) (hsz : c.b.size = c.w / 8 * c.n)
    (hnU : c.n < USize.size) (p : ByteArray) (hpn : p.size / 8 = c.n) (hpp : (Verify.ids p).Perm (List.range c.n))
    (x : Nat → α) (hf : ∀ i j, i < c.n → j < c.n → (Column.idAt c.b c.w i = Column.idAt c.b c.w j ↔ x i = x j)) :
    (gather 8 p (c.gather p).grade).size = 8 * c.n ∧ (Verify.ids (gather 8 p (c.gather p).grade)).Perm (List.range c.n) ∧
      ∀ s t u, s ≤ t → t ≤ u → u < c.n → x (at8 (gather 8 p (c.gather p).grade) s) =
        x (at8 (gather 8 p (c.gather p).grade) u) →
        x (at8 (gather 8 p (c.gather p).grade) t) = x (at8 (gather 8 p (c.gather p).grade) s) := by
  obtain ⟨k, hk, hkw, hkind⟩ := byteLane hw
  have hkw8 : k.width ≤ 8 := by rcases hk with rfl | rfl | rfl <;> decide
  have hk0 : 0 < k.width := by rcases hk with rfl | rfl | rfl <;> decide
  have hkU : k.width.toUSize.toNat = k.width := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by omega) USize.le_size)
  have hb : c.b.size = k.width * c.n := by
    rcases hk with rfl | rfl | rfl <;> simp only [Scan.Kind.width] at hkw ⊢ <;> rw [hsz, hkw] <;> omega
  have hP : ∀ s, s < c.n → at8 p s < c.n := fun s hs => by
    have : at8 p s ∈ Verify.ids p := by rw [ids_eq_map, hpn]; exact List.mem_map_of_mem (List.mem_range.2 hs)
    exact List.mem_range.1 (hpp.mem_iff.1 this)
  -- the code gathered through `p`
  have hdb : (c.gather p).b = gatherBytes k.width.toUSize 0 c.b p := by
    simp only [Code.gather, hkind]; rcases hk with rfl | rfl | rfl <;> rfl
  obtain ⟨gs, ge⟩ := Verify.gatherBytes_spec k.width.toUSize (by rw [hkU]; exact hkw8) 0 c.b p
  rw [hkU] at gs ge
  have hdn : (c.gather p).n = c.n := by simp only [Code.gather, len]; exact hpn
  have hdw : (c.gather p).w = c.w := rfl
  have hid : ∀ (b : ByteArray) i, Column.idAt b c.w i = (Column.bitsAt b (i * k.width) k.width).toNat := fun b i => by
    rw [hkw]; exact Verb.idAt_bytes b i hkw8
  have hdat : ∀ s, s < c.n → Column.idAt (c.gather p).b c.w s = Column.idAt c.b c.w (at8 p s) := fun s hs => by
    rw [hid, hid, hdb, ge s (by omega), if_pos (by rw [hb, Nat.mul_div_cancel_left _ hk0]; exact hP s hs)]
  obtain ⟨κ, gp, gm, gk⟩ := code_grade (c.gather p) (by rw [hdw]; exact hw)
    (by rw [hdb, gs, hpn, hdw, hdn, ← hb]; exact hsz) (by rw [hdn]; exact hnU)
  rw [hdn] at gp
  generalize (c.gather p).grade = gr at gp gm
  have hgl : gr.size / 8 = c.n := by have := gp.length_eq; rw [ids_eq_map] at this; simpa using this
  have hG : ∀ s, s < c.n → at8 gr s < c.n := fun s hs => by
    have : at8 gr s ∈ Verify.ids gr := by rw [ids_eq_map, hgl]; exact List.mem_map_of_mem (List.mem_range.2 hs)
    exact List.mem_range.1 (gp.mem_iff.1 this)
  have h8 : (8 : Nat).toUSize.toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  obtain ⟨qs, qe⟩ := Verify.gatherBytes_spec (8 : Nat).toUSize (by rw [h8]; exact Nat.le_refl _) 0 p gr
  rw [h8] at qs qe
  have hq : ∀ s, s < c.n → at8 (gather 8 p gr) s = at8 p (at8 gr s) := fun s hs => by
    simp only [at8, gather]; rw [qe s (by omega), if_pos (by rw [hpn]; exact hG s hs)]
  have hqs : (gather 8 p gr).size = 8 * c.n := by simp only [gather]; rw [qs, hgl]
  refine ⟨hqs, ?_, ?_⟩
  · have e : Verify.ids (gather 8 p gr) = (Verify.ids gr).map (at8 p) := by
      rw [ids_eq_map, ids_eq_map, hqs, hgl, Nat.mul_div_cancel_left _ (by decide), List.map_map]
      exact List.map_congr_left fun s hs => hq s (List.mem_range.1 hs)
    rw [e]
    refine (gp.map _).trans ?_
    have e' := ids_eq_map p; rw [hpn] at e'; rw [← e']; exact hpp
  · intro s t u h1 h2 hu
    simp only [hq s (by omega), hq t (by omega), hq u hu]
    have hgi : ∀ s (hs : s < c.n), (Verify.ids gr)[s]'(by rw [gp.length_eq]; simpa using hs) = at8 gr s := fun s hs => by
      simp only [ids_eq_map, List.getElem_map, List.getElem_range]
    refine sorted_contig (fun s => x (at8 p (at8 gr s))) (fun s => κ (at8 gr s)) (fun s t hst ht => ?_)
      (fun s t hs ht => ?_) s t u h1 h2 hu
    · rcases Nat.lt_or_eq_of_le hst with h | rfl
      · have := List.pairwise_iff_getElem.1 gm s t (by rw [gp.length_eq]; simp; omega) (by rw [gp.length_eq]; simpa using ht) h
        rwa [hgi s (by omega), hgi t ht] at this
      · exact UInt64.le_refl _
    · rw [gk, hdw, hdat _ (hG s hs), hdat _ (hG t ht)]; exact hf _ _ (hP _ (hG s hs)) (hP _ (hG t ht))

theorem tilLongs_ids {n : Nat} (hn : n < USize.size) : Verify.ids (tilLongs n.toUSize) = List.range n := by
  have e : tilLongs n.toUSize = Order.indices (List.range n.toUSize.toNat) := rfl
  rw [e, Verify.ids_indices _ fun i hi => Nat.lt_trans (List.mem_range.1 hi) (Verify.usize_lt _),
    USize.toNat_ofNat_of_lt' hn]

/-- **`gradeBy` on (key code, value code) at byte lanes is a permutation of the rows along which the
    elements of any `x` the key code is faithful to are contiguous** (item 4). The value code's grade only
    has to be a permutation. -/
theorem gradeBy_contig {α : Type} {n : Nat} (hnU : n < USize.size) (kc vc : Code)
    (hkw : kc.w = 8 ∨ kc.w = 16 ∨ kc.w = 32) (hks : kc.b.size = kc.w / 8 * kc.n) (hkn : kc.n = n)
    (hvw : vc.w = 8 ∨ vc.w = 16 ∨ vc.w = 32) (hvs : vc.b.size = vc.w / 8 * vc.n) (hvn : vc.n = n)
    (x : Nat → α) (hf : ∀ i j, i < n → j < n → (Column.idAt kc.b kc.w i = Column.idAt kc.b kc.w j ↔ x i = x j)) :
    (gradeBy n #[kc, vc]).size = 8 * n ∧ (Verify.ids (gradeBy n #[kc, vc])).Perm (List.range n) ∧
      ∀ s t u, s ≤ t → t ≤ u → u < n → x (at8 (gradeBy n #[kc, vc]) s) = x (at8 (gradeBy n #[kc, vc]) u) →
        x (at8 (gradeBy n #[kc, vc]) t) = x (at8 (gradeBy n #[kc, vc]) s) := by
  subst hkn
  have e : gradeBy kc.n #[kc, vc] = gather 8 (gather 8 (tilLongs kc.n.toUSize) (vc.gather (tilLongs kc.n.toUSize)).grade)
      (kc.gather (gather 8 (tilLongs kc.n.toUSize) (vc.gather (tilLongs kc.n.toUSize)).grade)).grade := rfl
  have ht := tilLongs_ids hnU
  have hts : (tilLongs kc.n.toUSize).size / 8 = kc.n := by
    have := congrArg List.length ht; rw [ids_eq_map] at this; simpa using this
  obtain ⟨s1, p1, -⟩ := grade_step vc hvw hvs (by rw [hvn]; exact hnU) _ (by rw [hts, hvn]) (by rw [ht, hvn])
    (fun i => Column.idAt vc.b vc.w i) (fun _ _ _ _ => Iff.rfl)
  rw [e]
  rw [hvn] at s1 p1
  exact grade_step kc hkw hks hnU _ (by omega) p1 x hf

/-- **The `min`/`max` fold `overBytes` runs answers its seed or one of the non-null elements it read.** -/
theorem overFold_attained (op : Coc.Over) (hop : op = .lesser ∨ op = .greater) (x : Nat → Int64) :
    ∀ (l : List Nat) (acc : Int64),
      l.foldl (fun acc i => if (!op.boolCast && x i == nul) = true then acc else op.step acc (x i)) acc = acc ∨
      ∃ i ∈ l, x i ≠ nul ∧
        l.foldl (fun acc i => if (!op.boolCast && x i == nul) = true then acc else op.step acc (x i)) acc = x i
  | [], _ => .inl rfl
  | a :: l, acc => by
    have hb : op.boolCast = false := by rcases hop with rfl | rfl <;> rfl
    simp only [List.foldl_cons, hb, Bool.not_false, Bool.true_and, beq_iff_eq]
    have hs : ∀ y, op.step acc y = acc ∨ op.step acc y = y := fun y => by
      rcases hop with rfl | rfl <;> simp only [Coc.Over.step] <;> split <;> simp
    rcases overFold_attained op hop x l
        (if (!op.boolCast && x a == nul) = true then acc else op.step acc (x a)) with h | ⟨i, hi, hx, h⟩
    · simp only [hb, Bool.not_false, Bool.true_and, beq_iff_eq] at h
      rw [h]
      by_cases ha : x a = nul
      · exact .inl (by simp only [ha, if_true])
      · simp only [ha, if_false]
        rcases hs (x a) with e | e
        · exact .inl e
        · exact .inr ⟨a, List.mem_cons_self .., ha, e⟩
    · exact .inr ⟨i, List.mem_cons_of_mem _ hi, hx, by simpa only [hb, Bool.not_false, Bool.true_and, beq_iff_eq] using h⟩

/-- **`overBytes lesser`/`greater` of a long payload sees only the set of its non-null elements**: two
    payloads holding the same non-null longs have one least and one greatest. `rangeOffsets`' `lo`/`hi`
    are the same for a column and any permutation of its rows. -/
theorem overBytes_vals (op : Coc.Over) (hop : op = .lesser ∨ op = .greater) {b b' : ByteArray}
    (hv : ∀ i, i < b'.size / 8 → Ew.signed Ew.i64 (Ew.elem Ew.i64 b' i) ≠ nul →
      ∃ j, j < b.size / 8 ∧ Ew.signed Ew.i64 (Ew.elem Ew.i64 b j) = Ew.signed Ew.i64 (Ew.elem Ew.i64 b' i))
    (hv' : ∀ i, i < b.size / 8 → Ew.signed Ew.i64 (Ew.elem Ew.i64 b i) ≠ nul →
      ∃ j, j < b'.size / 8 ∧ Ew.signed Ew.i64 (Ew.elem Ew.i64 b' j) = Ew.signed Ew.i64 (Ew.elem Ew.i64 b i)) :
    overBytes op Ew.i64 nul b = overBytes op Ew.i64 nul b' := by
  have hw : Ew.width Ew.i64 = 8 := by decide
  -- `overBytes` is the fold `overFold_attained` reads, at the payload's own elements
  have att : ∀ c : ByteArray, overBytes op Ew.i64 nul c = Coc.Over.denseSeed op Ew.i64 nul ∨
      ∃ i, i < c.size / 8 ∧ Ew.signed Ew.i64 (Ew.elem Ew.i64 c i) ≠ nul ∧
        overBytes op Ew.i64 nul c = Ew.signed Ew.i64 (Ew.elem Ew.i64 c i) := fun c => by
    rcases overFold_attained op hop (fun i => Ew.signed Ew.i64 (Ew.elem Ew.i64 c i))
      (List.range (c.size / Ew.width Ew.i64)) (Coc.Over.denseSeed op Ew.i64 nul) with h | ⟨i, hi, hx, h⟩
    · exact .inl h
    · rw [hw] at hi; exact .inr ⟨i, List.mem_range.1 hi, hx, h⟩
  have hseed : Coc.Over.denseSeed op Ew.i64 nul = op.seed nul := by rcases hop with rfl | rfl <;> rfl
  have bnd : ∀ c : ByteArray, ∀ i, i < c.size / 8 → Ew.signed Ew.i64 (Ew.elem Ew.i64 c i) ≠ nul →
      overBytes .lesser Ew.i64 nul c ≤ Ew.signed Ew.i64 (Ew.elem Ew.i64 c i) ∧
        Ew.signed Ew.i64 (Ew.elem Ew.i64 c i) ≤ overBytes .greater Ew.i64 nul c := fun c i hi hx =>
    overBytes_bounds Ew.i64 nul c (by rw [hw]; exact hi) hx
  have nl : (nul + 1).toInt = -2 ^ 63 + 1 := by decide
  have mx : (~~~nul).toInt = 2 ^ 63 - 1 := by decide
  -- one inequality from each side's attained value; the seed is the extreme of the order
  have le : ∀ c c' : ByteArray, (∀ i, i < c'.size / 8 → Ew.signed Ew.i64 (Ew.elem Ew.i64 c' i) ≠ nul →
      ∃ j, j < c.size / 8 ∧ Ew.signed Ew.i64 (Ew.elem Ew.i64 c j) = Ew.signed Ew.i64 (Ew.elem Ew.i64 c' i)) →
      (op = .lesser → overBytes op Ew.i64 nul c ≤ overBytes op Ew.i64 nul c') ∧
        (op = .greater → overBytes op Ew.i64 nul c' ≤ overBytes op Ew.i64 nul c) := fun c c' h => by
    refine ⟨fun e => ?_, fun e => ?_⟩ <;> subst e
    · rcases att c' with s | ⟨i, hi, hx, s⟩
      · rw [s, hseed]; exact Int64.le_iff_toInt_le.2 (by simp only [Coc.Over.seed]; rw [mx]; have := Int64.toInt_lt (overBytes .lesser Ew.i64 nul c); omega)
      · obtain ⟨j, hj, ej⟩ := h i hi hx
        rw [s, ← ej]; exact (bnd c j hj (by rw [ej]; exact hx)).1
    · rcases att c' with s | ⟨i, hi, hx, s⟩
      · rcases att c with t | ⟨j, hj, hy, t⟩
        · rw [s, t]; exact Int64.le_refl _
        · rw [s, hseed, t]; simp only [Coc.Over.seed]
          refine Int64.le_iff_toInt_le.2 ?_
          rw [nl]; have := Int64.le_toInt (Ew.signed Ew.i64 (Ew.elem Ew.i64 c j))
          have : (Ew.signed Ew.i64 (Ew.elem Ew.i64 c j)).toInt ≠ -2 ^ 63 := fun e' => hy (Int64.toInt_inj.1 (by rw [e']; decide))
          omega
      · obtain ⟨j, hj, ej⟩ := h i hi hx
        rw [s, ← ej]; exact (bnd c j hj (by rw [ej]; exact hx)).2
  rcases hop with rfl | rfl
  · exact Int64.le_antisymm ((le b b' hv).1 rfl) ((le b' b hv').1 rfl)
  · exact Int64.le_antisymm ((le b' b hv').2 rfl) ((le b b' hv).2 rfl)

/-- **`enumIds` reports every row in range** when every non-null long of `b` is an offset below `d`. -/
theorem enumIds_all {n d nid w : USize} {b : ByteArray}
    (h : ∀ i, i < n.toNat → (Column.bitsAt b (i * 8) 8).toInt64 ≠ Int64.minValue →
      0 ≤ (Column.bitsAt b (i * 8) 8).toInt64 ∧ (Column.bitsAt b (i * 8) 8).toInt64.toInt.toNat < d.toNat) :
    (enumIds n d nid w b).2 = n := by
  simp only [enumIds]
  rw [List.find?_eq_none.2 fun i hi => by
    have := h i (List.mem_range.1 hi)
    by_cases hx : (Column.bitsAt b (i * 8) 8).toInt64 = Int64.minValue <;> simp_all]
  simp

/-- **`rangeOffsets` answers for a dense long part exactly when it answers for any part holding the same
    non-null longs, at the same `total`** (item 3): its decisions read only `lo`/`hi` (`overBytes_vals`)
    and `total`, and its kernel's range report is always full (`enumIds_all`, `overBytes_bounds`). So a
    column sorted, or cut to its distinct rows at the same count, is coded on the same branch. -/
theorem rangeOffsets_vals {b b' : ByteArray} {m m' total : Nat} {os : Array Code} (hU : 2 ^ 32 < USize.size)
    (ht : total ≤ 2 ^ 32) (hn' : b'.size / 8 ≤ 2 ^ 32)
    (hv : ∀ i, i < b'.size / 8 → (Column.bitsAt b' (i * 8) 8).toInt64 ≠ nul →
      ∃ j, j < b.size / 8 ∧ (Column.bitsAt b (j * 8) 8).toInt64 = (Column.bitsAt b' (i * 8) 8).toInt64)
    (hv' : ∀ i, i < b.size / 8 → (Column.bitsAt b (i * 8) 8).toInt64 ≠ nul →
      ∃ j, j < b'.size / 8 ∧ (Column.bitsAt b' (j * 8) 8).toInt64 = (Column.bitsAt b (i * 8) 8).toInt64)
    (h : rangeOffsets .long #[(m, .bytes b)] total = .ok (some os)) :
    ∃ os', rangeOffsets .long #[(m', .bytes b')] total = .ok (some os') := by
  have hnU : b'.size / 8 < USize.size := by omega
  have hw : Ew.width Ew.i64 = 8 := by decide
  have e : ∀ (c : ByteArray) i, Ew.signed Ew.i64 (Ew.elem Ew.i64 c i) = (Column.bitsAt c (i * 8) 8).toInt64 :=
    fun c i => by simp only [Ew.signed, Ew.elem, hw]; rfl
  have eL := overBytes_vals .lesser (.inl rfl) (b := b) (b' := b') (by simpa only [e] using hv) (by simpa only [e] using hv')
  have eH := overBytes_vals .greater (.inr rfl) (b := b) (b' := b') (by simpa only [e] using hv) (by simpa only [e] using hv')
  have bnd : ∀ i, i < b'.size / 8 → (Column.bitsAt b' (i * 8) 8).toInt64 ≠ nul →
      overBytes .lesser Ew.i64 nul b ≤ (Column.bitsAt b' (i * 8) 8).toInt64 ∧
        (Column.bitsAt b' (i * 8) 8).toInt64 ≤ overBytes .greater Ew.i64 nul b := fun i hi hx => by
    rw [eL, eH, ← e]; exact overBytes_bounds Ew.i64 nul b' (by rw [hw]; exact hi) (by rw [e]; exact hx)
  simp only [rangeOffsets, Array.mapM_eq_mapM_toList, List.mapM_cons, List.mapM_nil] at h ⊢
  rw [← eL, ← eH]
  generalize overBytes .lesser Ew.i64 nul b = L at h bnd ⊢
  generalize overBytes .greater Ew.i64 nul b = H at h bnd ⊢
  simp at h ⊢
  have hloL : (min Int64.maxValue L).toInt ≤ L.toInt := by
    show (if Int64.maxValue ≤ L then Int64.maxValue else L).toInt ≤ L.toInt
    split
    · exact Int64.le_iff_toInt_le.1 ‹_›
    · exact Int.le_refl _
  have hHhi : H.toInt ≤ (max (Int64.minValue + 1) H).toInt := by
    show H.toInt ≤ (if Int64.minValue + 1 ≤ H then H else Int64.minValue + 1).toInt
    split
    · exact Int.le_refl _
    · rename_i h'; have := mt Int64.le_iff_toInt_le.2 h'; omega
  generalize min Int64.maxValue L = lo at h hloL ⊢
  generalize max (Int64.minValue + 1) H = hi at h hHhi ⊢
  have xb : ∀ i, i < b'.size / 8 → (Column.bitsAt b' (i * 8) 8).toInt64 ≠ nul →
      lo.toInt ≤ (Column.bitsAt b' (i * 8) 8).toInt64.toInt ∧ (Column.bitsAt b' (i * 8) 8).toInt64.toInt ≤ hi.toInt :=
    fun i hi hx => by
      have := bnd i hi hx
      exact ⟨by have := Int64.le_iff_toInt_le.1 this.1; omega, by have := Int64.le_iff_toInt_le.1 this.2; omega⟩
  have h0 : (0 : Int64).toInt = 0 := by decide
  -- the kernel's report is full at whichever base and payload the branch took
  have tail : ∀ (base : Int64) (b'' : ByteArray) (card : Nat), base ≠ nul → (codeKind card).width ≤ 4 →
      (∀ i, i < b'.size / 8 → (Column.bitsAt b' (i * 8) 8).toInt64 ≠ nul →
        base.toInt ≤ (Column.bitsAt b' (i * 8) 8).toInt64.toInt ∧
          (Column.bitsAt b' (i * 8) 8).toInt64.toInt - base.toInt + 2 ≤ card) →
      (∀ i, i < b'.size / 8 → (Column.bitsAt b'' (i * 8) 8).toInt64 =
        if (Column.bitsAt b' (i * 8) 8).toInt64 = nul then nul else (Column.bitsAt b' (i * 8) 8).toInt64 + -base) →
      ∀ w, (enumIds (USize.ofNat (b'.size / 8)) (USize.ofNat card) (USize.ofNat (card - 1)) w b'').snd.toNat =
        b'.size / 8 := by
    intro base b'' card hb hk4 hr hv w
    obtain ⟨hfit, -⟩ := codeKind_fits card hk4
    have hc32 : card ≤ 2 ^ 32 := by
      have : 2 ^ (8 * (codeKind card).width) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hcU : card < USize.size := by omega
    have hnu : (USize.ofNat (b'.size / 8)).toNat = b'.size / 8 := USize.toNat_ofNat_of_lt' hnU
    rw [enumIds_all fun i hi hx => ?_, hnu]
    rw [hnu] at hi
    rw [hv i hi] at hx ⊢
    have hxn : (Column.bitsAt b' (i * 8) 8).toInt64 ≠ nul := fun e => hx (by rw [if_pos e]; rfl)
    rw [if_neg hxn] at hx ⊢
    obtain ⟨r1, r2⟩ := hr i hi hxn
    have hbl := Int64.le_toInt base; have hbu := Int64.toInt_lt base
    have hxl := Int64.le_toInt (Column.bitsAt b' (i * 8) 8).toInt64
    have hxu := Int64.toInt_lt (Column.bitsAt b' (i * 8) 8).toInt64
    have hbn : base.toInt ≠ -2 ^ 63 := fun h => hb (Int64.toInt_inj.1 (by rw [h]; decide))
    have hs : ((Column.bitsAt b' (i * 8) 8).toInt64 + -base).toInt =
        (Column.bitsAt b' (i * 8) 8).toInt64.toInt - base.toInt := by
      rw [Int64.toInt_add, Int64.toInt_neg]
      simp only [Int.bmod]; split <;> split <;> omega
    rw [USize.toNat_ofNat_of_lt' hcU]
    exact ⟨Int64.le_iff_toInt_le.2 (by rw [hs, h0]; omega), by rw [hs]; omega⟩
  have hk4 : (codeKind total).width ≤ 4 := codeKind_small ht
  split at h
  · rename_i hg; rw [if_pos hg]
    split at h
    · simp [pure, Except.pure] at h
    · rename_i hlh; rw [if_neg hlh]
      split at h
      · rename_i hwid; rw [if_pos hwid]
        have hlo : lo ≠ nul := fun e => hlh (.inl e)
        split
        · rename_i hP
          rw [if_pos (fun e => absurd hP.2 (e hP.1))]
          simp only [h0, Int.sub_zero]
          split
          · exact ⟨_, rfl⟩
          · rename_i hc
            have hl0 := Int64.le_iff_toInt_le.1 hP.1
            rw [h0] at hl0
            exact absurd (tail 0 b' _ zero_ne_nul (by rw [hP.2]; omega) (fun i hi hx => by
              have := xb i hi hx; rw [h0]; omega) (fun i hi => by split <;> simp_all) _) hc
        · rename_i hP
          split
          · rename_i hc0
            have hl0 : lo = 0 := hc0 fun a b => hP ⟨a, b⟩
            split
            · exact ⟨_, rfl⟩
            · rename_i hc
              exact absurd (tail lo b' _ hlo (by omega) (fun i hi hx => by have := xb i hi hx; omega)
                (fun i hi => by subst hl0; split <;> simp_all) _) hc
          · rename_i hc0
            have hl0 : lo ≠ 0 := fun e => hc0 fun _ => e
            split
            · exact ⟨_, rfl⟩
            · rename_i hc
              refine absurd (tail lo _ _ hlo (by omega) (fun i hi hx => by have := xb i hi hx; omega) (fun i hi => ?_) _) hc
              have hneg : -lo ≠ nul := fun e => hlo (by rw [← Int64.neg_neg (a := lo), e]; decide)
              have := shift_elem b' (-lo) hnU hi
              rw [Int64.toUInt64_neg] at this
              rw [this]; simp only [hneg, or_false]
      · simp [pure, Except.pure] at h
  · simp [pure, Except.pure] at h

#print axioms overBytes_vals
#print axioms enumIds_all
#print axioms rangeOffsets_vals
#print axioms code_grade
#print axioms grade_step
#print axioms gradeBy_contig
#print axioms rangeOffsets_bytes
#print axioms code_runs
#print axioms codes_long_bytes
#print axioms runsP_long

end LeetQ.Rel.Alg
