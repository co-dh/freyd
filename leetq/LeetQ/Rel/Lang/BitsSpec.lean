/-
  The bit-matrix plan (`Bits.lean`) read back. `TP.den` is the plan's relation in `Rel(Set)`; `rep_tableC` says the
  table side computes it under `tableC`'s one bit. The bit side is read at the codes: `Bits.Enc` says a matrix holds,
  at bit `i·w + j`, a relation between the elements `ua i`, `ub j`, and each bit rule maps encodings to encodings.
-/
import LeetQ.Rel.Lang.Bits
import LeetQ.Rel.CRelFold
import LeetQ.Rel.KernelWF.BitRows
import LeetQ.Rel.KernelWF.MemberSpec
import LeetQ.Rel.RepArith

namespace LeetQ.Rel.Lang.Bits

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep Freyd Freyd.Alg Freyd.Alg.RelSet

-- `unionC`'s `hat`, as `CRelEst`'s (local there): `razeTo`'s read-back of two atom parts
set_option quotPrecheck false in
local notation "hatOK" => ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
      (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
        USize.size), Vals.RazeFits (.atom t) x y →
      (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList

/-! ### The plan's relation -/

/-- The plan's relation in `Rel(Set)`: each node the set-theoretic op on its children's, a leaf its table's `rep`. -/
def TP.den : {A B : Obj} → TP A B → A.El → B.El → Prop
  | _, _, .leaf R => rep R
  | _, _, .comp R S => fun a c => ∃ b, R.den a b ∧ S.den b c
  | _, _, .conv R => fun b a => R.den a b
  | _, _, .meet R S => fun a b => R.den a b ∧ S.den a b
  | _, _, .join R S => fun a b => R.den a b ∨ S.den a b
  | _, _, .diff R S => fun a b => R.den a b ∧ ¬ S.den a b
  | _, _, .ldiv R S UB UC => fun b c =>
    (∀ a, R.den a b → S.den a c) ∧ ((∃ a, R.den a b) ∨ ((∃ p, UB.val.row p = b) ∧ ∃ j, UC.val.row j = c))

/-- **The table side**: under `tableC`'s bit the plan's table denotes `TP.den`, each node by its `CRel` op's
    read-back (`rep_comp`, `rep_inter`, `rep_union`, `rep_diffC`, `rep_leftDiv`, `rep_conv`). -/
theorem rep_tableC (hat : hatOK) : ∀ {A B : Obj} (p : TP A B), p.tableC.ok = true →
    ∀ a b, rep p.tableC.rel a b ↔ p.den a b
  | _, _, .leaf _, _, _, _ => Iff.rfl
  | _, _, .comp R S, hb, a, c => by
    unfold TP.tableC at hb ⊢
    by_cases hz : (R.tableC.rel.n == 0) = true
    · rw [if_pos hz] at hb ⊢
      have ih := rep_tableC hat R hb
      have h0 : R.tableC.rel.n.toNat = 0 := by simp [beq_iff_eq.1 hz]
      refine ⟨fun ⟨i, _⟩ => i.elim0, fun ⟨b, hR, _⟩ => ?_⟩
      obtain ⟨i, -⟩ := (ih a b).2 hR
      exact absurd i.2 (by omega)
    · rw [if_neg hz] at hb ⊢
      have h := hb
      simp only [CRel.comp, Bool.and_eq_true] at h
      rw [CRel.rep_comp _ _ hb]
      have ihR := rep_tableC hat R h.1.1
      have ihS := rep_tableC hat S h.1.2
      exact ⟨fun ⟨b, h1, h2⟩ => ⟨b, (ihR a b).1 h1, (ihS b c).1 h2⟩,
        fun ⟨b, h1, h2⟩ => ⟨b, (ihR a b).2 h1, (ihS b c).2 h2⟩⟩
  | _, _, .conv R, hb, b, a => by
    unfold TP.tableC at hb ⊢
    rw [rep_conv]; exact rep_tableC hat R hb a b
  | _, _, .meet R S, hb, a, b => by
    unfold TP.tableC at hb ⊢
    have h := hb
    simp only [CRel.inter, Bool.and_eq_true] at h
    rw [CRel.rep_inter _ _ hb]
    exact and_congr (rep_tableC hat R h.1.1 a b) (rep_tableC hat S h.1.2 a b)
  | _, _, .join R S, hb, a, b => by
    unfold TP.tableC at hb ⊢
    have h := hb
    simp only [CRel.union, Bool.and_eq_true] at h
    rw [CRel.rep_union hat _ _ hb]
    exact or_congr (rep_tableC hat R h.1.1 a b) (rep_tableC hat S h.1.2 a b)
  | _, _, .diff R S, hb, a, b => by
    unfold TP.tableC at hb ⊢
    simp only [Bool.and_eq_true] at hb
    rw [rep_diffC _ _ hb.2]
    exact and_congr (rep_tableC hat R hb.1.1 a b) (not_congr (rep_tableC hat S hb.1.2 a b))
  | _, _, .ldiv R S UB UC, hb, b, c => by
    unfold TP.tableC at hb ⊢
    have h := hb
    simp only [CRel.leftDiv, Bool.and_eq_true] at h
    rw [CRel.rep_leftDiv _ _ _ _ hb]
    have ihR := rep_tableC hat R h.1.1
    have ihS := rep_tableC hat S h.1.2
    simp only [TP.den, ihR, ihS]

/-- `TP.table` denotes `TP.den` under `tableC`'s bit. -/
theorem rep_table (hat : hatOK) {A B : Obj} (p : TP A B) (hb : p.tableC.ok = true) (a : A.El) (b : B.El) :
    rep p.table a b ↔ p.den a b := rep_tableC hat p hb a b

#print axioms rep_tableC

end LeetQ.Rel.Lang.Bits
