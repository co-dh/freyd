/-
  Bird & de Moor, *Algebra of Programming* §7.5  The security van problem (book pp. 184-189).

  Given a sequence of transactions, find a longest secure prefix-partition — `min R · Λ(list secure ·
  partition)` with `R = length°·leq·length`, `partition` from §5.6, and `secure` a prefix- and
  suffix-closed coreflexive.  B&dM refine it (after a fusion of `list secure · partition` into
  `⦇[nil, new∪old]⦈`) by a GREEDY algorithm, provided the monotonicity condition (7.14)
  `new·(id×R°) ⊆ R°·(new∪old)` holds (it does; (7.15) is false, needing the `H ; R` order
  refinement).  The core refinement — the min-catamorphism `⦇min R·ΛS⦈ ⊑ min R·Λ⦇S⦈` — is
  `A7_2.greedy`; `partition` is `AOP.A5_6_ListCombinators.partition`, and the concrete `secure`
  coreflexive + the (7.14) monotonicity are the problem-specific detail (deferred, see atodo).
-/
module

public import AOP.A7_2

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {a : 𝒜}

/-- **§7.5 (B&dM pp.184-189)**: the longest secure partition is found by a GREEDY algorithm over the
    min-catamorphism — `⦇min R·ΛS⦈ ⊑ min R·Λ⦇S⦈`, for the partition-building algebra `S` monotonic on
    `R°`.  A direct instance of `A7_2.greedy` (the concrete `secure` coreflexive + (7.14)
    monotonicity are deferred). -/
theorem security_van_greedy (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {R : a ⟶ a} {S : F.obj a ⟶ a} (htrans : R ≫ R ⊑ R) (hmono : MonotonicAlg S R) :
    relCata (Λ S ≫ est R) ⊑ Λ (relCata S) ≫ est R :=
  greedy hFr I htrans hmono

end Freyd.Alg
