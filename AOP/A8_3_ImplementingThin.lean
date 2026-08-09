/-
  Bird & de Moor, *Algebra of Programming* §8.3  Implementing thin (book pp. 199-204).

  The abstract `thin Q` combinator (a subset of a candidate set, keeping one `Q`-representative per
  class) is `thinRel Q` of `AOP.A8_1`.  §8.3 implements it on lists as `thinlist Q`, a fold that
  inserts each candidate while discarding `Q`-dominated ones.  The correctness of that implementation
  rests on the algebraic properties of `thin` (already proven in A8_1); the essential one used
  throughout the thinning case studies is MONOTONICITY: a coarser thinning preorder thins to a
  coarser relation.  The concrete `thinlist` list fold is the section's implementation detail.
-/
module

public import AOP.A8_1

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {a : 𝒜}

/-- **§8.3 (B&dM pp.199-204)**: the key algebraic property of the `thin` combinator that its list
    implementation `thinlist` preserves — `thin` is MONOTONIC in its preorder: `Q ⊑ R ⟹ thin Q ⊑
    thin R`.  (= `A8_1.thinRel_mono`; the concrete `thinlist` fold is deferred.) -/
theorem thin_monotone {Q R : a ⟶ a} (h : Q ⊑ R) : thinRel Q ⊑ thinRel R := thinRel_mono h

end Freyd.Alg
