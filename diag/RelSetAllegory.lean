/-
  `diag.RelSetAllegory` — the composite acceptance check for phases 4 and 5 (`diag/PLAN.md`).

  Phase 5 builds an `Allegory` out of any cartesian bicategory of relations; phase 4 shows `Rel(Set)`
  IS one.  Composing them gives a second `Allegory RelSet`, and this file checks it is the SAME one
  the repo already had (`AOP/A6_1_RelSet.lean`) — not merely an isomorphic copy.  Without this the
  bridge would be a theorem about a structure nobody uses.

  Both checks are phase 4's agreement theorems, `meet_eq_inter` and `conv_eq_recip`, read at
  the bridge's two operation fields.  The point is that they typecheck AS the bridge's fields: it is
  the composite `allegoryOfCartBicat ∘ (the RelSet instance)` being pinned down, not `meet`
  and `conv` in isolation.
-/
import diag.CB_Allegory
import diag.RelSetCB

universe u

namespace Freyd.Diag

open Freyd
open Freyd.Alg

/-- The bridge's `∩` on `Rel(Set)` is the allegory intersection the repo already had. -/
theorem allegoryOfCartBicat_inter {a b : RelSet.{u}} (R S : a ⟶ b) :
    (allegoryOfCartBicat RelSet.{u}).inter R S = R ∩ S := meet_eq_inter R S

/-- The bridge's `°` on `Rel(Set)` is the ordinary relational converse — so the wire-bending
    definition of the converse really did land on `Allegory.recip`. -/
theorem allegoryOfCartBicat_recip {a b : RelSet.{u}} (R : a ⟶ b) :
    (allegoryOfCartBicat RelSet.{u}).recip R = R° := conv_eq_recip R

end Freyd.Diag
