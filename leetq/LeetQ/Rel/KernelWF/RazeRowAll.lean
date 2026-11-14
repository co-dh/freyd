/-
  `Obj.raze` of two parts read back at every shape of side: `raze_row` composes the four constructor lemmas
  (`raze_row_atom`, `_prod`, `_arr`, `_sum`) along the side's shape, under `Vals.RazeFits`, the size bounds the
  composition needs. The atom read-back enters as `hat`, the one statement `razeTo2_fits` proves at the types
  and encodings it covers; `rep_union_fits`, `rep_junc_fits` are `rep_union`, `rep_junc` with their read-back
  hypotheses replaced by `Vals.RazeFits`.
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

end LeetQ.Rel.KernelWF

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet

variable {A B C : Obj}

open RazeN

section
variable (hat : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size), Vals.RazeFits (.atom t) x y →
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
include hat

/-- **`rep (R ∪ S) = rep R ∪ rep S`** with `rep_union`'s read-backs `hA`, `hB` replaced by the size bounds
    `Vals.RazeFits` of the keys and of the values (`raze_row`); `hat`: the atom read-back. -/
theorem rep_union_fits (R S : Rel A B) (hN : R.n.toNat + S.n.toNat < USize.size)
    (hNk : ((#[⟨R.n, R.key⟩, ⟨S.n, S.key⟩] : Array (Part A)).toList.map fun c : Part A => c.1.toNat).sum <
      USize.size)
    (hNv : ((#[⟨R.n, R.val⟩, ⟨S.n, S.val⟩] : Array (Part B)).toList.map fun c : Part B => c.1.toNat).sum <
      USize.size)
    (hFk : Vals.RazeFits A R.key S.key) (hFv : Vals.RazeFits B R.val S.val)
    (hK : (∀ {i j : Nat} (hi : i < (Uc).n.toNat) (hj : j < (Uc).n.toNat),
        Column.idAt (kcU).b (kcU).w i = Column.idAt (kcU).b (kcU).w j ↔
          Vals.row (Uc).key ⟨i, hi⟩ = Vals.row (Uc).key ⟨j, hj⟩) ∧
      ((kcU).w = 1 ∨ (kcU).w = 2 ∨ (kcU).w = 4 ∨ (kcU).w = 8 ∨ (kcU).w = 16 ∨ (kcU).w = 32 ∨ (kcU).w = 64) ∧
        (kcU).n = (Uc).n ∧ (kcU).b.size = ((kcU).n.toNat * (kcU).w + 7) / 8 ∧
        ((kcU).w < 8 → (kcU).card < USize.size ∧ ∀ i < (kcU).n.toNat, Column.idAt (kcU).b (kcU).w i < (kcU).card))
    (hV : (∀ {i j : Nat} (hi : i < (Uc).n.toNat) (hj : j < (Uc).n.toNat),
        Column.idAt (vcU).b (vcU).w i = Column.idAt (vcU).b (vcU).w j ↔
          Vals.row (Uc).val ⟨i, hi⟩ = Vals.row (Uc).val ⟨j, hj⟩) ∧
      ((vcU).w = 1 ∨ (vcU).w = 2 ∨ (vcU).w = 4 ∨ (vcU).w = 8 ∨ (vcU).w = 16 ∨ (vcU).w = 32 ∨ (vcU).w = 64) ∧
        (vcU).n = (Uc).n ∧ (vcU).b.size = ((vcU).n.toNat * (vcU).w + 7) / 8 ∧
        ((vcU).w < 8 → (vcU).card < USize.size ∧ ∀ i < (vcU).n.toNat, Column.idAt (vcU).b (vcU).w i < (vcU).card))
    (hk : Vals.PickFits A (Uc).key (ids nubU)) (hv : Vals.PickFits B (Uc).val (ids nubU)) :
    rep (R ∪ S) = rep R ∪ rep S :=
  rep_union R S hN hNk hNv (raze_row hat A R.key S.key hFk hNk) (raze_row hat B R.val S.val hFv hNv) hK hV hk hv

/-- `rep_junc` with its read-back `hC` replaced by the size bounds `Vals.RazeFits` of the values (`raze_row`);
    `hat`: the atom read-back. -/
theorem rep_junc_fits (R : Rel A C) (S : Rel B C) (hN : R.n.toNat + S.n.toNat < USize.size)
    (h63 : R.n.toNat + S.n.toNat ≤ 2 ^ 63) (hF : Vals.RazeFits C R.val S.val) :
    rep (LeetQ.Rel.Alg.junc R S) = Freyd.Alg.junc (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩) (rep R) (rep S) :=
  rep_junc R S hN h63 (raze_row hat C R.val S.val hF)

end

#print axioms raze_row
#print axioms razeTo2_fits
#print axioms rep_union_fits
#print axioms rep_junc_fits

end LeetQ.Rel.Rep
