/-
  Bird & de Moor, *Algebra of Programming* §8.2  Paths in a layered network (book pp. 196-198).

  Find a least-cost path through a layered network (a path is a catamorphism over the layers; the
  cost is a sum over edges).  The specification is `min R · Λpaths` with `R = cost°·leq·cost`; the
  derivation applies the CorOLLARY to the thinning theorem (Cor 8.1): with the thinning preorder
  `Q` on partial paths (compatible with `R` through the cost), the path-extension algebra `S` is
  monotonic on `Q°`, and thinning refines the exhaustive `min R·Λ⦇S⦈` to an efficient program.
  The refinement is the thinning theorem `A8_1.thinning_min` instantiated; the concrete
  layer datatype and the monotonicity proof are the section's problem-specific detail.
-/
module

public import AOP.A8_1

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {a : 𝒜}

/-- **§8.2 (B&dM pp.196-198)**: a least-cost path in a layered network is found by THINNING —
    `⦇thin Q·Λ(S·F∈)⦈·min R ⊑ min R·Λ⦇S⦈`, for the path-extension algebra `S` monotonic on the
    thinning preorder `Q°` and `Q ⊑ R` the cost order.  A direct instance of `A8_1.thinning_min`. -/
theorem layered_network_thinning (hFr : F.PreservesRecip) (I : InitialAlgebra F) {Q R : a ⟶ a}
    {S : F.obj a ⟶ a} (hQR : Q ⊑ R) (hreflQ : Cat.id a ⊑ Q) (htransQ : Q ≫ Q ⊑ Q)
    (htransR : R ≫ R ⊑ R) (hmono : MonotonicAlg S Q) :
    relCata I (Λ (F.map (∋ a) ≫ S) ≫ thinRel Q) ≫ minRel R ⊑ Λ (relCata I S) ≫ minRel R :=
  thinning_min hFr I hQR hreflQ htransQ htransR hmono

end Freyd.Alg
