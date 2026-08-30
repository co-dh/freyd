/-
  Bird & de Moor, *Algebra of Programming* §9.4  Data compression (book pp. 238-243).

  Compress a list by choosing an optimal parse into codeable segments (e.g. an optimal prefix code /
  optimal parsing), minimising total encoded length.  The specification is `min R · Λ(codings)` where
  a coding unfolds the input into segments and `R` orders by total code length.  This is the
  DYNAMIC-PROGRAMMING setting of §9.1: the coding algebra `h` is monotonic on the transitive
  length order `R`, and Theorem 9.1 gives the DP recursion refining the exhaustive search over parses.
  A direct instance of `A9_1.dynamic_programming`; the concrete segment/code datatype and the length
  cost are the problem-specific detail.
-/
module

public import AOP.A9_1

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {a b : 𝒜}

/-- **§9.4 (B&dM pp.238-243)**: optimal data compression is computed by DYNAMIC PROGRAMMING —
    `μX. min R°·P(h·FX)·ΛT° ⊑ min R°·Λ⦇h⦈·⦇T⦈°`, for the coding algebra `h` monotonic on the
    transitive length order `R°`.  A direct instance of `A9_1.dynamic_programming`. -/
theorem compression_dp (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {h : F.obj a ⟶ a} {T : F.obj b ⟶ b} {R : a ⟶ a}
    (hh : Map h) (hmono : MonotonicAlg h R°) (htrans : R° ≫ R° ⊑ R°) :
    mu (fun X : b ⟶ a => Λ (T°) ≫ powerRel (F.map X ≫ h) ≫ est R)
      ⊑ Λ ((relCata I T)° ≫ relCata I h) ≫ est R :=
  dynamic_programming hFr I hh hmono htrans

end Freyd.Alg
