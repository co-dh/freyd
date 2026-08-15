/-
  Bird & de Moor, *Algebra of Programming* §8.5  The paragraph problem (book pp. 207-211).

  Break a list of words into lines (a partition into contiguous segments) minimising total raggedness,
  each line fitting within the page width `w`.  The specification is `min R · Λ(fmt · within w ·
  partition)` (partition into lines, each `within w`, ordered by cost `R`); B&dM refine it by THINNING
  with a preorder `Q` combining the cost with the last-line width.  Once the line-building algebra `S`
  is monotonic on `Q°`, thinning gives an efficient program.  The refinement is `A8_1.thinning_min`
  instantiated; `partition` is `AOP.A5_6_ListCombinators.partition`, the concrete `within w`/`fmt`
  and the monotonicity proof are the problem-specific detail.
-/
module

public import AOP.A8_1

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {a : 𝒜}

/-- **§8.5 (B&dM pp.207-211)**: the paragraph problem (optimal line breaking) is solved by THINNING —
    `⦇thin Q·Λ(S·F∈)⦈·min R ⊑ min R·Λ⦇S⦈`, for the line-building algebra `S` monotonic on the
    thinning preorder `Q°`.  A direct instance of `A8_1.thinning_min`. -/
theorem paragraph_thinning (hFr : F.PreservesRecip) (I : InitialAlgebra F) {Q R : a ⟶ a}
    {S : F.obj a ⟶ a} (hQR : Q ⊑ R) (hreflQ : Cat.id a ⊑ Q) (htransQ : Q ≫ Q ⊑ Q)
    (htransR : R ≫ R ⊑ R) (hmono : MonotonicAlg S Q°) :
    relCata I (Λ (F.map (∋ a) ≫ S) ≫ thinRel Q) ≫ minRel R ⊑ Λ (relCata I S) ≫ minRel R :=
  thinning_min hFr I hQR hreflQ htransQ htransR hmono

end Freyd.Alg
