/-
  Bird & de Moor, *Algebra of Programming* §10.4  The TeX problem (book pp. 259-264).

  TeX's paragraph breaker: break a list of words into lines minimising total badness, where the cost
  is a catamorphism (`val`) on cons-lists.  The specification is `min R · Λ(breakings)` with `R`
  ordering by total badness.  B&dM solve it with a GREEDY algorithm (a variant of the paragraph
  problem in which all but one decomposition is weeded out at each step).  This is the greedy setting
  of §10.1: with the line-building algebra `h` monotonic on the transitive badness order `R` and a
  thinning preorder `Q` satisfying the compatibility condition, Theorem 10.1 gives the greedy
  recursion.  A direct instance of `A10_1.greedy_dp`; the concrete word/line datatype and the badness
  cost `val` are the problem-specific detail.
-/
module

public import AOP.A10_1

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {a b : 𝒜}

/-- **§10.4 (B&dM pp.259-264)**: TeX's line breaking is solved by a GREEDY algorithm —
    `μX. min Q°·ΛT° refolded through h ⊑ min R°·Λ⦇h⦈·⦇T⦈°`, for the line-building algebra `h` monotonic
    on the transitive badness order `R°` and the compatibility condition `hQ`.  A direct instance of
    `A10_1.greedy_dp`. -/
theorem tex_greedy (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {h : F.obj a ⟶ a} {T : F.obj b ⟶ b} {R : a ⟶ a} {Q : F.obj b ⟶ F.obj b}
    (hh : Map h) (hmono : MonotonicAlg h R°) (htrans : R° ≫ R° ⊑ R°)
    (hQ : Q ≫ F.map ((relCata I T)° ≫ relCata I h) ≫ h
        ⊑ F.map ((relCata I T)° ≫ relCata I h) ≫ h ≫ R) :
    mu (fun X : b ⟶ a => Λ (T°) ≫ est Q ≫ F.map X ≫ h)
      ⊑ Λ ((relCata I T)° ≫ relCata I h) ≫ est R :=
  greedy_dp hFr I hh hmono htrans hQ

end Freyd.Alg
