/-
  The executable relation algebra `Alg` read in the allegory of sets: `rep R` is the relation `R.Holds` as a
  `Rel(Set)` arrow, and each theorem says `rep` of an `Alg` op is the `Rel(Set)` op on the `rep`s.
-/
import LeetQ.Rel.Alg
import AOP.A6_1_RelSet

namespace LeetQ.Rel.Rep

open Freyd Freyd.Alg Freyd.Alg.RelSet LeetQ.Rel

variable {A B C : Obj}

/-- The `Rel(Set)` arrow a `Rel` denotes: `x` to `y` when some row holds `(x, y)`. -/
def rep (R : Rel A B) : (⟨A.El⟩ : RelSet.{0}) ⟶ ⟨B.El⟩ := R.Holds

/-- `rep R x y` is `R.Holds x y`, by definition. -/
theorem rep_apply (R : Rel A B) (x : A.El) (y : B.El) : rep R x y = R.Holds x y := rfl

section Ops

open LeetQ.Rel.Alg

/-- `rep (R°) = (rep R)°`: the converse swaps the two fields. -/
theorem rep_conv (R : Rel A B) : rep (R°) = (rep R)° :=
  hom_ext fun y x => convArr_holds R.key R.val x y

/-- `rep 𝟘 = 𝟘`: no row, no pair. -/
theorem rep_zero : rep (Alg.zero : Rel A B) = 𝟘 :=
  hom_ext fun _ _ => ⟨fun ⟨i, _⟩ => i.elim0, False.elim⟩

/-- `rep (idU U)` is the coreflexive on the elements `U` lists — not `𝟙`, which it is only when `U` lists every
    element of `A.El`. -/
theorem rep_idU {m : USize} (U : Vals A m) :
    rep (idU U) = corefl (A := (⟨A.El⟩ : RelSet.{0})) fun x => ∃ i, U.row i = x :=
  hom_ext fun x y => (idU_holds U x y).trans ⟨fun ⟨h, hx⟩ => ⟨h, hx⟩, fun ⟨h, hx⟩ => ⟨h, hx⟩⟩

/-- `rep (outl T) = rep T ≫ π₁`: `outl` on a relation into a product is that relation followed by the first
    projection, the graph of `Prod.fst` (`relProd`'s `π₁`). -/
theorem rep_outl (T : Rel A (.prod B C)) :
    rep (outl T) = rep T ≫ (graph Prod.fst : (⟨B.El × C.El⟩ : RelSet.{0}) ⟶ ⟨B.El⟩) :=
  hom_ext fun x y => (outl_holds T x y).trans
    ⟨fun ⟨z, h⟩ => ⟨(y, z), h, rfl⟩, fun ⟨⟨y', z⟩, h, e⟩ => ⟨z, (show y = y' from e) ▸ h⟩⟩

/-- `rep (outr T) = rep T ≫ π₂`: the second projection, the graph of `Prod.snd`. -/
theorem rep_outr (T : Rel A (.prod B C)) :
    rep (outr T) = rep T ≫ (graph Prod.snd : (⟨B.El × C.El⟩ : RelSet.{0}) ⟶ ⟨C.El⟩) :=
  hom_ext fun x z => (outr_holds T x z).trans
    ⟨fun ⟨y, h⟩ => ⟨(y, z), h, rfl⟩, fun ⟨⟨y, z'⟩, h, e⟩ => ⟨y, (show z = z' from e) ▸ h⟩⟩

end Ops

-- `Classical.choice` below comes with `Rel.Holds` itself (through qlean's `Carrier`), not from the proofs
#print axioms Rel.Holds
#print axioms rep_conv
#print axioms rep_zero
#print axioms rep_idU
#print axioms rep_outl
#print axioms rep_outr

end LeetQ.Rel.Rep
