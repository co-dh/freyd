/-
  Bird & de Moor, *Algebra of Programming* §10.3  The minimum tardiness problem (book pp. 253-258).

  Schedule jobs (each with a processing time and due date) to minimise total tardiness.  The
  specification is `min R · Λ(schedules)` where a schedule is an ordering of the jobs and `R` orders
  by total tardiness.  B&dM show a GREEDY algorithm succeeds: committing to a single locally-best job
  at each step (extreme dynamic programming) solves it.  This is the greedy setting of §10.1: with the
  job-appending algebra `h` monotonic on the transitive tardiness order `R` and a thinning preorder
  `Q` satisfying the compatibility condition, Theorem 10.1 gives the greedy recursion.  A direct
  instance of `A10_1.greedy_dp`; the concrete job/schedule datatype and the tardiness cost are the
  problem-specific detail.
-/
module

public import AOP.A10_1

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {a b : 𝒜}

/-- **§10.3 (B&dM pp.253-258)**: minimum tardiness is solved by a GREEDY algorithm —
    `μX. min Q°·ΛT° refolded through h ⊑ min R°·Λ⦇h⦈·⦇T⦈°`, for the scheduling algebra `h` monotonic on
    the transitive tardiness order `R°` and the compatibility condition `hQ`.  A direct instance of
    `A10_1.greedy_dp`. -/
theorem tardiness_greedy (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {h : F.obj a ⟶ a} {T : F.obj b ⟶ b} {R : a ⟶ a} {Q : F.obj b ⟶ F.obj b}
    (hh : Map h) (hmono : MonotonicAlg h R°) (htrans : R° ≫ R° ⊑ R°)
    (hQ : Q ≫ F.map ((relCata I T)° ≫ relCata I h) ≫ h
        ⊑ F.map ((relCata I T)° ≫ relCata I h) ≫ h ≫ R) :
    mu (fun X : b ⟶ a => Λ (T°) ≫ est Q ≫ F.map X ≫ h)
      ⊑ Λ ((relCata I T)° ≫ relCata I h) ≫ est R :=
  greedy_dp hFr I hh hmono htrans hQ

end Freyd.Alg
