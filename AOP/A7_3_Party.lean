/-
  Bird & de Moor, *Algebra of Programming* §7.3  Planning a company party (book pp. 175-177).

  The party problem (Cormen–Leiserson–Rivest): the company is a tree of employees `tree A =
  node(A, list(tree A))`, each with a conviviality `rating`; choose a guest list maximising total
  rating such that no employee attends with their immediate supervisor.  Formally, maximise
  `max R · Λparty`, where `party = ⦇⟨include, exclude⟩⦈ : list A ← tree A` builds two candidate
  parties (root-in / root-out), `choose = outl ∪ outr` picks one, and `R = (sum·list rating)°·leq·
  (sum·list rating)` orders guest lists by total rating.  The moral (B&dM p.176): this looks like
  dynamic programming but is solved by a GREEDY algorithm.

  Given the two monotonicity claims B&dM leave as exercises — `choose` monotonic on `R`, and
  `⟨include, exclude⟩` monotonic on `R×R` — the greedy theorem (`A7_2.greedy_max`) yields the
  algorithm.  Here we prove the first claim concretely (`choose_monotonic`, a general product
  fact) and state the greedy conclusion as the instance of `greedy_max` it is; the concrete rose
  tree `tree A`, the algebra `⟨include, exclude⟩`, and its monotonicity are the section's remaining
  detail (rose-tree datatype not yet built — see atodo).
-/
module

public import AOP.A7_2
public import AOP.A5_2

universe u

namespace Freyd.Alg

/-! ## The `choose` relation and its monotonicity (B&dM p.177, first claim) -/

section Choose

variable {𝒜 : Type u} [TabularUnitaryDivisionAllegory 𝒜] {a : 𝒜}

/-- **B&dM p.176**: `choose = outl ∪ outr` — pick either component of a pair (either party). -/
@[expose] public def choose (P : RelProd a a) : P.p ⟶ a := P.outl ∪ P.outr

/-- **§7.3 (B&dM p.177), first monotonicity claim** ("left as a simple exercise"): `choose` is
    monotonic on `R`, i.e. `choose·(R×R) ⊆ R·choose` (mirrored `(R×R) ≫ choose ⊑ choose ≫ R`).
    Immediate from the product projection laws `prodMap ≫ outl ⊑ outl ≫ R` (and `outr`) and the
    distributivity of composition over `∪`. -/
public theorem choose_monotonic (P : RelProd a a) (R : a ⟶ a) :
    prodMap P P R R ≫ choose P ⊑ choose P ≫ R := by
  show prodMap P P R R ≫ (P.outl ∪ P.outr) ⊑ (P.outl ∪ P.outr) ≫ R
  rw [DistributiveAllegory.comp_union_distrib, union_comp_distrib]
  exact union_mono (prodMap_outl_le P P R R) (prodMap_outr_le P P R R)

end Choose

/-! ## The party problem is solved by the greedy theorem (B&dM p.177) -/

section Greedy

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {a : 𝒜}

/-- **§7.3 (B&dM p.176-177)**: the company-party optimisation `max R·Λparty` is solved by a
    GREEDY algorithm.  With `party = ⦇⟨include, exclude⟩⦈` a catamorphism over the employee tree
    and `S = ⟨include, exclude⟩` its algebra, once `S` is monotonic on the transitive rating order
    `R` (B&dM's second claim), the greedy recursion `⦇max R·ΛS⦈` refines the specification
    `max R·Λ⦇S⦈ = max R·Λparty`.  A direct instance of the greedy theorem
    (`A7_2.greedy_max`), whose hypotheses B&dM's monotonicity claims (via `choose_monotonic`
    above and the `⟨include,exclude⟩` calculation p.177) discharge for the concrete tree. -/
public theorem company_party_greedy (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {R : a ⟶ a} {S : F.obj a ⟶ a} (htrans : R ≫ R ⊑ R) (hmono : MonotonicAlg S R) :
    relCata I (Λ S ≫ maxRel R) ⊑ Λ (relCata I S) ≫ maxRel R :=
  greedy_max hFr I htrans hmono

end Greedy

end Freyd.Alg
