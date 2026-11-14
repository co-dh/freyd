/-
  `Obj.raze` of two parts read back at every shape of side: `raze_row` composes the four constructor lemmas
  (`raze_row_atom`, `_prod`, `_arr`, `_sum`) along the side's shape, under `Vals.RazeFits`, the size bounds the
  composition needs. The atom read-back enters as `hat`, the one statement `razeTo2_fits` proves at the types
  and encodings it covers.
-/
import LeetQ.Rel.KernelWF.RazeRowRec

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Dep LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep
open Freyd Freyd.Alg Freyd.Alg.RelSet

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

section
variable (hat : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size), Vals.RazeFits (.atom t) x y →
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
include hat

/-- **Row read-back of `raze` at every side**: row `k` of two razed parts is the first part's row below its count,
    the second's past it — the four constructor lemmas composed along `A`, under `Vals.RazeFits`; `hat`: the atom
    read-back (`razeTo2_fits` where it is proved). -/
theorem raze_row : (A : Obj) → {n m : USize} → (x : Vals A n) → (y : Vals A m) → Vals.RazeFits A x y →
    ∀ (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part A)).toList.map fun c : Part A => c.1.toNat).sum < USize.size)
      (k : Nat) (hk : k < ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part A)).toList.map
        fun c : Part A => c.1.toNat).sum.toUSize.toNat),
    Vals.row (A.raze #[⟨n, x⟩, ⟨m, y⟩] hN) ⟨k, hk⟩ =
      if h : k < n.toNat then Vals.row x ⟨k, h⟩
      else Vals.row y ⟨k - n.toNat, by have := raze2_cnt x y hN; omega⟩
  | .atom t, _, _, x, y, hF => fun hN k hk => raze_row_atom x y hN (hat t x y hN hF) k hk
  | .prod a b, _, _, x, y, hF => fun hN k hk =>
      raze_row_prod x y hN (raze_row a x.1 y.1 hF.1) (raze_row b x.2 y.2 hF.2) k hk
  | .arr b, _, _, x, y, hF => fun hN k hk =>
      raze_row_arr x y hN hF.1 hF.2.1 (raze_row b x.2.2.2 y.2.2.2 hF.2.2) k hk
  | .sum a b, _, _, x, y, hF => fun hN k hk =>
      raze_row_sum x y hN hF.1 hF.2.1 hF.2.2.1 hF.2.2.2.1 hF.2.2.2.2.1 hF.2.2.2.2.2.1
        (raze_row a _ _ hF.2.2.2.2.2.2.1) (raze_row b _ _ hF.2.2.2.2.2.2.2) k hk

end

#print axioms raze_row
#print axioms razeTo2_fits

end LeetQ.Rel.KernelWF
