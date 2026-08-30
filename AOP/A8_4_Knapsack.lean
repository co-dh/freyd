/-
  Bird & de Moor, *Algebra of Programming* §8.4  The knapsack problem (book pp. 205-206) —
  the standard example of BINARY THINNING.

  Pack items of greatest total value into a knapsack of capacity `w`, from a `list Item`.  Selections
  are modelled as subsequences (`subseq = ⦇[nil,cons] ∪ [nil,outr]⦈`); `value = sum·list val`,
  `weight = sum·list wt`.  The specification is `knapsack w ⊆ min R·Λ(within w · subseq)` with
  `R = value°·geq·value` (order by descending value) and `within w x = (weight x ≤ w)`.  B&dM refine
  it by THINNING with the preorder `Q = R ∩ (weight°·leq·weight)` (sort by value, break ties by
  weight): the within-`w` selection algebra `S` is monotonic on `Q°` (the "easy to prove" fact),
  and — the cons-list base functor being linear — the thinning theorem applies, giving the
  binary-thinning program.  The refinement is exactly the thinning theorem (`A8_1.thinning_est`).
-/
module

public import AOP.A8_1

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {a : 𝒜}

/-- **§8.4 (B&dM pp.205-206)**: the knapsack problem is solved by BINARY THINNING.  With the
    subsequence-selection algebra `S`, the descending-value order `R`, and the thinning preorder
    `Q = R ∩ (weight-order)`, once `S` is monotonic on `Q°` the thinning DP
    `⦇thin Q · Λ(S·F∈)⦈ · min R°` refines the specification `min R°·Λ⦇S⦈ = min R°·Λ(within w·subseq)`.
    A direct instance of the thinning theorem `A8_1.thinning_est` (with `Q`, `R°`, `S`, and the
    monotonicity `hmono` supplied concretely by the knapsack data, per B&dM's derivation). -/
theorem knapsack_thinning (hFr : F.PreservesRecip) (I : InitialAlgebra F) {Q R : a ⟶ a}
    {S : F.obj a ⟶ a} (hQR : Q ⊑ R°) (hreflQ : Cat.id a ⊑ Q) (htransQ : Q ≫ Q ⊑ Q)
    (htransR : R° ≫ R° ⊑ R°) (hmono : MonotonicAlg S Q°) :
    relCata (Λ (F.map (∋ a) ≫ S) ≫ thinRel Q) ≫ est R ⊑ Λ (relCata S) ≫ est R :=
  thinning_est hFr I hQR hreflQ htransQ htransR hmono

end Freyd.Alg
