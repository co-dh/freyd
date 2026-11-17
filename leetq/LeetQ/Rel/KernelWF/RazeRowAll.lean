/-
  `Vals.RazeFits`, the size bounds under which two parts' `raze` reads back row by row, and `razeTo2_fits`, the
  atom read-back at the types and encodings proved here; `raze_row` (`RazeFoR`) composes the four constructor
  lemmas (`raze_row_atom`, `_prod`, `_arr`, `_sum`) along the side's shape once `hat_all` covers every atom.
-/
import LeetQ.Rel.KernelWF.RazeRowRec

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Dep LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep
open scoped LeetQ.Core.Rel
open LeetQ.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The size bounds under which two parts' `raze` reads back row by row (`raze_row`):
    - an atom: the parts' dictionaries, a blob counting its rows, fit a `USize` (`razeTo2_symbol`'s `hD`), and at
      a type ALP encodes the joined count is below `2 ^ 32`, where `concatALP` stores its exception offsets;
    - an array: its flat payloads' counts summed fit a `USize` and stay below `2 ^ 63` (`raze_row_arr`);
    - a sum: each side's held payload counts the same, and both parts' `held` picks fit (`raze_row_sum`). -/
def _root_.LeetQ.Rel.Vals.RazeFits : (A : Obj) → {n m : USize} → Vals A n → Vals A m → Prop
  | .atom t, n, m, x, y =>
      (match Arr.enc (t := t) (n := n) x with | .enum _ o _ => o.size - 1 | _ => n.toNat) +
        (match Arr.enc (t := t) (n := m) y with | .enum _ o _ => o.size - 1 | _ => m.toNat) < USize.size ∧
      (Column.alpEncodes t = true → n.toNat + m.toNat < 2 ^ 32)
  | .prod a b, _, _, x, y => Vals.RazeFits a x.1 y.1 ∧ Vals.RazeFits b x.2 y.2
  | .arr b, _, _, x, y => x.1.toNat + y.1.toNat < USize.size ∧ x.1.toNat + y.1.toNat < 2 ^ 63 ∧
      Vals.RazeFits b x.2.2.2 y.2.2.2
  | .sum a b, n, m, x, y =>
      x.held.1.toNat + y.held.1.toNat < USize.size ∧ x.held.2.1.toNat + y.held.2.1.toNat < USize.size ∧
      x.held.1.toNat + y.held.1.toNat < 2 ^ 63 ∧ x.held.2.1.toNat + y.held.2.1.toNat < 2 ^ 63 ∧
      Vals.PickFits (.sum a b) x (List.range n.toNat) ∧ Vals.PickFits (.sum a b) y (List.range m.toNat) ∧
      Vals.RazeFits a x.held.2.2.2.2.1 y.held.2.2.2.2.1 ∧ Vals.RazeFits b x.held.2.2.2.2.2 y.held.2.2.2.2.2

/-- **`Obj.razeC`'s bit is a fit** for two parts: each clause of `Vals.RazeFits` is a conjunct of the bit, a
    sum's picks by `pickFits_of_fitsN` at all its rows. -/
theorem _root_.LeetQ.Rel.Obj.razeC_fits : (A : Obj) → {n m : USize} → (x : Vals A n) → (y : Vals A m) →
    (cs : Array (Part A)) → cs.toList = [⟨n, x⟩, ⟨m, y⟩] →
    (hN : (cs.toList.map fun c : Part A => c.1.toNat).sum < USize.size) →
    (Obj.razeC A cs hN).2 = true → Vals.RazeFits A x y
  | .atom t, n, m, x, y, cs, hcs, hN, hb => by
    simp only [Obj.razeC, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hb
    rw [hcs] at hb
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hb
    unfold Vals.RazeFits
    refine ⟨hb.1, fun ha => ?_⟩
    rcases hb.2 with h | h
    · rw [ha] at h; cases h
    · exact h
  | .prod a b, n, m, x, y, cs, hcs, hN, hb => by
    simp only [Obj.razeC, Bool.and_eq_true] at hb
    unfold Vals.RazeFits
    exact ⟨Obj.razeC_fits a x.1 y.1 _ (by simp [hcs]) _ hb.1, Obj.razeC_fits b x.2 y.2 _ (by simp [hcs]) _ hb.2⟩
  | .arr b, n, m, x, y, cs, hcs, hN, hb => by
    simp only [Obj.razeC] at hb
    split at hb
    · rename_i hf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      have e : (cs.map fun c => (⟨c.2.1, c.2.2.2.2⟩ : Part b)).toList = [⟨x.1, x.2.2.2⟩, ⟨y.1, y.2.2.2⟩] := by
        simp [hcs]
      have hs : ((cs.map fun c => (⟨c.2.1, c.2.2.2.2⟩ : Part b)).toList.map (·.1.toNat)).sum =
          x.1.toNat + y.1.toNat := by rw [e]; simp
      unfold Vals.RazeFits
      exact ⟨by omega, by omega, Obj.razeC_fits b _ _ _ e _ hb.2⟩
    · simp at hb
  | .sum a b, n, m, x, y, cs₀, hcs, hN, hb => by
    simp only [Obj.razeC] at hb
    split at hb
    · rename_i hf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨⟨⟨⟨h1, h2⟩, hp⟩, ha⟩, hb⟩ := hb
      have el : ((cs₀.map fun c => (⟨c.1, c.2.held⟩ : Part (.sum a b))).map
          fun c => (⟨c.2.1, c.2.2.2.2.2.1⟩ : Part a)).toList =
          [⟨x.held.1, x.held.2.2.2.2.1⟩, ⟨y.held.1, y.held.2.2.2.2.1⟩] := by simp [hcs]
      have er : ((cs₀.map fun c => (⟨c.1, c.2.held⟩ : Part (.sum a b))).map
          fun c => (⟨c.2.2.1, c.2.2.2.2.2.2⟩ : Part b)).toList =
          [⟨x.held.2.1, x.held.2.2.2.2.2⟩, ⟨y.held.2.1, y.held.2.2.2.2.2⟩] := by simp [hcs]
      have sl : (((cs₀.map fun c => (⟨c.1, c.2.held⟩ : Part (.sum a b))).map
          fun c => (⟨c.2.1, c.2.2.2.2.2.1⟩ : Part a)).toList.map (·.1.toNat)).sum =
          x.held.1.toNat + y.held.1.toNat := by rw [el]; simp
      have sr : (((cs₀.map fun c => (⟨c.1, c.2.held⟩ : Part (.sum a b))).map
          fun c => (⟨c.2.2.1, c.2.2.2.2.2.2⟩ : Part b)).toList.map (·.1.toNat)).sum =
          x.held.2.1.toNat + y.held.2.1.toNat := by rw [er]; simp
      have hpk : ∀ c ∈ cs₀.toList, Vals.fitsN (.sum a b) c.2 c.1.toNat = true := fun c hc =>
        Array.all_eq_true_iff_forall_mem.1 hp c (Array.mem_def.2 hc)
      unfold Vals.RazeFits
      exact ⟨by rw [← sl]; exact hf.1, by rw [← sr]; exact hf.2, by rw [← sl]; exact h1, by rw [← sr]; exact h2,
        pickFits_of_fitsN (.sum a b) x _ (hpk ⟨n, x⟩ (by rw [hcs]; simp)) _ (by simp),
        pickFits_of_fitsN (.sum a b) y _ (hpk ⟨m, y⟩ (by rw [hcs]; simp)) _ (by simp),
        Obj.razeC_fits a _ _ _ el _ ha, Obj.razeC_fits b _ _ _ er _ hb⟩
    · simp at hb

/-- **Two atom parts fit on their summed row count alone** at a type that has no dictionary (`Enc.WF` admits
    `enum` only at `symbol`) and no ALP layout: the clause's other bounds are then about the counts themselves.
    At `symbol` the dictionaries, at `.arr`/`.sum` the payloads, are not bounded by the row counts. -/
theorem razeFits_atom_count {t : QAtomicType} {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : n.toNat + m.toNat < USize.size) (hs : t ≠ .symbol) (ha : Column.alpEncodes t = false) :
    Vals.RazeFits (.atom t) x y := by
  have no : ∀ {k : USize} (z : Arr t k) d o i, Arr.enc z ≠ .enum d o i := fun z d o i he => by
    have hw := z.wf; rw [he] at hw; cases t <;> simp_all [Enc.WF]
  unfold Vals.RazeFits
  refine ⟨?_, fun h => absurd h (by simp [ha])⟩
  split
  next d o i he => exact absurd he (no _ _ _ _)
  next =>
    split
    next d o i he => exact absurd he (no _ _ _ _)
    next => exact hN

/-- A guid column's payload is dense bytes: `Enc.WF` admits no other at `guid`. -/
theorem guid_bytes {n : USize} (x : Arr .guid n) : ∃ b, x.enc = .bytes b := by
  have hw := x.wf; revert hw
  cases x.enc <;> simp [Enc.WF, QAtomicType.width]

/-- **Two parts' `razeTo` list** at the types and encodings proved so far: `boolean`, `general`, `symbol` (under
    the dictionary bound of `Vals.RazeFits`), `guid`, and any type whose two parts are dense bytes. -/
theorem razeTo2_fits {t : QAtomicType} {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size)
    (hF : Vals.RazeFits (.atom t) x y)
    (ht : t = .boolean ∨ t = .general ∨ t = .symbol ∨ t = .guid ∨
      ((∃ b, x.enc = .bytes b) ∧ ∃ b, y.enc = .bytes b)) :
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList := by
  rcases ht with rfl | rfl | rfl | rfl | ⟨hx, hy⟩
  · exact razeTo2_boolean x y hN
  · exact razeTo2_general x y hN
  · exact razeTo2_symbol x y hN (by simpa using hF.1)
  · exact razeTo2_bytes x y hN (guid_bytes x) (guid_bytes y)
  · exact razeTo2_bytes x y hN hx hy

#print axioms razeTo2_fits

end LeetQ.Rel.KernelWF
