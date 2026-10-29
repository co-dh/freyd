/-
  `Λ`'s carrier groups its relation: `transposeP R` answers keys one-to-one, each with the nonempty
  segment of `R`'s values at that key. Proved from the kernels' Lean bodies, encoding by encoding of the
  key's `codes`.
-/
import LeetQ.Rel.Prog

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

#print axioms rangeOffsets_bytes
#print axioms code_runs

end LeetQ.Rel.Alg
