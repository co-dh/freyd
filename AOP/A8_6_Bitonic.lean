/-
  Bird & de Moor, *Algebra of Programming* §8.6  Bitonic tours (book pp. 212-215).

  A bitonic tour of a set of points (a generalisation of the closed-tour / travelling-salesman
  problem) of least length.  The final application of thinning in the chapter: the specification
  `min R · Λ(tours)` (tours built by a catamorphism, ordered by length `R`) is refined by THINNING
  with a preorder `Q` on partial tours.  Once the tour-extension algebra `S` is monotonic on `Q°`,
  the thinning theorem yields an efficient program.  The refinement is `A8_1.thinning_min`
  instantiated; the concrete point/tour datatype and the monotonicity proof are problem-specific.
-/
module

public import AOP.A8_1

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {a : 𝒜}

/-- **§8.6 (B&dM pp.212-215)**: least-length bitonic tours are found by THINNING —
    `⦇thin Q·Λ(S·F∈)⦈·min R ⊑ min R·Λ⦇S⦈`, for the tour-extension algebra `S` monotonic on the
    thinning preorder `Q°`.  A direct instance of `A8_1.thinning_min`. -/
theorem bitonic_thinning (hFr : F.PreservesRecip) (I : InitialAlgebra F) {Q R : a ⟶ a}
    {S : F.obj a ⟶ a} (hQR : Q ⊑ R) (hreflQ : Cat.id a ⊑ Q) (htransQ : Q ≫ Q ⊑ Q)
    (htransR : R ≫ R ⊑ R) (hmono : MonotonicAlg S Q°) :
    relCata I (Λ (F.map (∋ a) ≫ S) ≫ thinRel Q) ≫ minRel R ⊑ Λ (relCata I S) ≫ minRel R :=
  thinning_min hFr I hQR hreflQ htransQ htransR hmono

end Freyd.Alg
