/-
  Bird & de Moor, *Algebra of Programming* §9.3  Optimal bracketing (book pp. 230-237).

  Bracket `x₁ + x₂ + ⋯ + xₙ` to minimise total cost (e.g. matrix-chain multiplication).  Expressions
  are binary trees (`tip | bin(t,t)`); `cost` is a catamorphism, and (since cost depends on subtree
  sizes) `⟨cost, size⟩ = ⦇[opt, opb]⦈` is tupled.  The specification is `min R · Λ(bracketings)` with
  `R` the cost order.  B&dM solve it by DYNAMIC PROGRAMMING (Theorem 9.1) with the monotonicity-in-
  context (Proposition 9.3): the bracketing algebra `h` is monotonic on the transitive cost order `R`,
  and Theorem 9.1 gives the DP recursion `mct`, made efficient by tabulation.  The core is
  `A9_1.dynamic_programming`; the concrete binary-tree datatype, Proposition 9.1 (coproduct split,
  dropped from A9_1), `inits⁺`/`tails⁺`/`splits`, and the tabulation scheme are deferred (see atodo).
-/
module

public import AOP.A9_1

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {a b : 𝒜}

/-- **§9.3 (B&dM pp.230-237)**: the minimum-cost bracketing `mct` is computed by DYNAMIC PROGRAMMING —
    `μX. min R°·P(h·FX)·ΛT° ⊑ min R°·Λ⦇h⦈·⦇T⦈°`, for the bracketing algebra `h` monotonic on the
    transitive cost order `R°`.  A direct instance of `A9_1.dynamic_programming` (binary trees +
    Proposition 9.1 + tabulation deferred). -/
theorem bracketing_dp (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {h : F.obj a ⟶ a} {T : F.obj b ⟶ b} {R : a ⟶ a}
    (hh : Map h) (hmono : MonotonicAlg h R°) (htrans : R° ≫ R° ⊑ R°) :
    mu (fun X : b ⟶ a => Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ ((relCata I T)° ≫ relCata I h) ≫ est R :=
  dynamic_programming hFr I hh hmono htrans

end Freyd.Alg
