/-
  Bird & de Moor, *Algebra of Programming* §7.4  Shortest paths on a cylinder (book pp. 179-183).

  Thread a least-cost path through an `n × m` array rolled into a cylinder (from each square one may
  move to one of three adjacent squares in the next column).  The specification is `min R · paths`
  with `R = sum°·leq·sum`, `paths : PL Nat ← LN Nat` built from `generate` (a LAX NATURAL
  TRANSFORMATION, §5.7) over `moves`/`trans`/`zip`/`cp`.  B&dM note this is dynamic programming via
  the min-catamorphism (Theorem 7.1), not the greedy theorem.  The core refinement — the
  min-catamorphism `⦇min R·ΛS⦈ ⊑ min R·Λ⦇S⦈` for `S` monotonic on the cost order — is `A7_2.greedy`
  (Theorem 7.2); the concrete n-tuple/set machinery (`generate` as a lax natural transformation,
  `trans`/`zip`/`cp`) is the heavy problem-specific detail, deferred (see atodo).
-/
module

public import AOP.A7_2

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {a : 𝒜}

/-- **§7.4 (B&dM pp.179-183)**: the shortest cylinder path is found by dynamic programming over the
    min-catamorphism — `⦇min R·ΛS⦈ ⊑ min R·Λ⦇S⦈`, for the path-generation algebra `S` monotonic on
    `R°`.  A direct instance of the min-catamorphism theorem `A7_2.greedy` (the concrete lax-natural
    `generate` over n-tuples/sets is deferred). -/
theorem cylinder_paths_min (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {R : a ⟶ a} {S : F.obj a ⟶ a} (htrans : R ≫ R ⊑ R) (hmono : MonotonicAlg S R) :
    relCata I (Λ S ≫ est R) ⊑ Λ (relCata I S) ≫ est R :=
  greedy hFr I htrans hmono

end Freyd.Alg
