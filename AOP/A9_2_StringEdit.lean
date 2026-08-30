/-
  Bird & de Moor, *Algebra of Programming* §9.2  The string edit problem (book pp. 225-229).

  Compute a minimum-cost edit sequence (`mle`) transforming one list into another — the classic
  edit-distance dynamic program.  The specification is `min R · Λ(edits)` where the edit relation is
  built by unfolding both strings (copy / insert / delete / change) and `R` orders by total cost.
  This is exactly the DYNAMIC-PROGRAMMING setting of §9.1: the algebra `h` (an edit step) is
  monotonic on the transitive cost order `R`, and Theorem 9.1 gives the DP recursion refining the
  exhaustive search.  (B&dM additionally thin by `thin(Q₁+Q₂)` — a coproduct-split thinning needing
  Proposition 9.1, dropped from A9_1; here we give the underlying DP result.)  A direct instance of
  `A9_1.dynamic_programming`; the concrete two-list coalgebra and cost are the problem-specific detail.
-/
module

public import AOP.A9_1

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {a b : 𝒜}

/-- **§9.2 (B&dM pp.225-229)**: the string edit distance is computed by DYNAMIC PROGRAMMING —
    `μX. min R°·P(h·FX)·ΛT° ⊑ min R°·Λ⦇h⦈·⦇T⦈°`, for the edit-step algebra `h` monotonic on the
    transitive cost order `R°`.  A direct instance of `A9_1.dynamic_programming`. -/
theorem string_edit_dp (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {h : F.obj a ⟶ a} {T : F.obj b ⟶ b} {R : a ⟶ a}
    (hh : Map h) (hmono : MonotonicAlg h R°) (htrans : R° ≫ R° ⊑ R°) :
    mu (fun X : b ⟶ a => Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ ((relCata T)° ≫ relCata h) ≫ est R :=
  dynamic_programming hFr I hh hmono htrans

end Freyd.Alg
