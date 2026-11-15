import LeetQ.Aop.RelAop
import LeetQ.Rel.Programs.Mss
import AOP.A7_7_MSS

/-! `rel_aop mss` (`doc/rel-mss-proof-design.md` §4, option D): the program `Programs.mss` over the book's model, its
    four laws `toShape`, `toFused`, `toGreedy`, `toScan` proved from `AOP/A7_7_MSS.lean`, and `linear : mss = scan`
    the `calc` the program writes. These are theorems about B&dM's model (`Int`, cons lists, the power object), not
    about the executable `mss.rel.*`: the evidence between those is still the program's `check`. -/

namespace LeetQ.Rel.Aop.Mss

open Freyd Freyd.Alg Freyd.Alg.RelSet Freyd.Alg.RelSet.CL PowerAllegory

/-! ### The bridges: the RelSet term a Rel body names is the one `MSS` states -/

/-- `⊤zero = ⊸ zero`: `⊤` into the one-point object discards its argument. -/
theorem top_zero {X : RelSet.{0}} : (topHom X (dL Unit) ≫ MSS.zero : X ⟶ ⟨Int⟩) = graph fun _ => MSS.zeroVal :=
  hom_ext fun x _ => ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨(), topMor_eq_topHom X (dL Unit) ▸ topMor_apply x (), h⟩⟩

/-- `k`, the algebra of `scan`'s fold in Rel's spelling (`w ≜ (𝟙×π₁)oplus`, `oplus` already `MSS.oplus`), is
    `MSS.k`: `⟨R,S⟩ = rpair R S`, `R×S = rprodMap R S`, and Rel's left-nested juxtaposition. -/
theorem k_eq :
    let zero := MSS.zero; let NN := relProd (⟨Int⟩ : RelSet.{0}) ⟨Int⟩
    let Nα := relProd (⟨Int⟩ : RelSet.{0}) (P ⟨Int⟩); let NNα := relProd (⟨Int⟩ : RelSet.{0}) Nα.p
    let L : Coproduct ((F Unit Int).obj Nα.p) (dL Unit) NNα.p := sumCop _ _
    let oplus := MSS.oplus; let w : NNα.p ⟶ ⟨Int⟩ := rel((𝟙×π₁)oplus)
    (rel([zero⟨𝟙,Λ(𝟙)⟩, ⟨w,Λ(w ∪ (π₂π₂∋))⟩]) : (F Unit Int).obj Nα.p ⟶ Nα.p) = MSS.k := by
  intro zero NN Nα NNα L oplus w
  simp only [zero, NN, Nα, NNα, oplus, w, prodMap_eq_rprodMap, pair_eq_rpair, Cat.assoc]; rfl

open LeetQ.Rel.Programs

rel_aop mss
  model N := (⟨Int⟩ : RelSet.{0}), zero := MSS.zero, «≥» := MSS.geq, suffix := ListRel.suffix (A := Int),
    «prefix» := ListRel.«prefix» (A := Int),
    K : Coproduct ((F Unit Int).obj ⟨Int⟩) (dL Unit) (relProd (⟨Int⟩ : RelSet.{0}) ⟨Int⟩).p := sumCop _ _,
    NN := relProd (⟨Int⟩ : RelSet.{0}) ⟨Int⟩, Nα := relProd (⟨Int⟩ : RelSet.{0}) (P ⟨Int⟩),
    NNα := relProd (⟨Int⟩ : RelSet.{0}) Nα.p, L : Coproduct ((F Unit Int).obj Nα.p) (dL Unit) NNα.p := sumCop _ _
  proof
    toShape := (by
      calc mss
          = ((suffix ≫ «prefix») ≫ ListRel.sum)%∋ ≫ est(MSS.geq) := rfl                -- ≜ mss, ≜ segment
        _ = MSS.mss := by rw [← ListRel.segment_eq]; rfl                                 -- segment = suffix prefix
        _ = suffix%∋ ≫ existsImage MSS.mssPre ≫ est(MSS.geq) := MSS.mss_shape            -- mss-shape
        _ = (suffix%∋ ≫ existsImage MSS.mssPre) ≫ est(MSS.geq) := (Cat.assoc _ _ _).symm
        _ = shape := rfl),                                                               -- ≜ mssPre, ≜ shape
    toFused := (by
      calc shape
          = (suffix%∋ ≫ existsImage ((«prefix» ≫ ListRel.sum)%∋ ≫ est(MSS.geq))) ≫ est(MSS.geq) := rfl  -- ≜ shape
        _ = (suffix%∋ ≫ existsImage ((cataR MSS.Salg)%∋ ≫ est(MSS.geq))) ≫ est(MSS.geq) := by
          rw [MSS.mss_prefix_sum]                                                                     -- prefix sum = ⦇S⦈
        _ = (suffix%∋ ≫ existsImage ((relCata MSS.Salg)%∋ ≫ est(MSS.geq))) ≫ est(MSS.geq) := by
          rw [cataR_eq_relCata]                                                                       -- ⦇S⦈ in RelSet
        _ = fused := by                                                                               -- ⊤zero = ⊸ zero
          show _ = Programs.mss.fused.aop; delta Programs.mss.fused.aop; rw [top_zero]; rfl),
    toGreedy := (by
      calc fused
          = (suffix%∋ ≫ existsImage ((relCata MSS.Salg)%∋ ≫ est(MSS.geq))) ≫ est(MSS.geq) := by
            show Programs.mss.fused.aop = _; delta Programs.mss.fused.aop; rw [top_zero]; rfl         -- ⊤zero = ⊸ zero
        _ = (suffix%∋ ≫ existsImage ((cataR MSS.Salg)%∋ ≫ est(MSS.geq))) ≫ est(MSS.geq) := by
          rw [cataR_eq_relCata]                                                                       -- ⦇S⦈ in RelSet
        _ = (suffix%∋ ≫ existsImage (cataR (MSS.Salg%∋ ≫ est(MSS.geq)))) ≫ est(MSS.geq) := by
          rw [MSS.mss_greedy_eq]                                                                      -- Λ(⦇S⦈)est(≥) = ⦇Λ(S)est(≥)⦈
        _ = (suffix%∋ ≫ existsImage (cataR (junc (sumCop _ _) MSS.zero MSS.oplus))) ≫ est(MSS.geq) := by
          rw [MSS.mss_step]                                                                           -- Λ(S)est(≥) = [zero,⊕]
        _ = (suffix%∋ ≫ existsImage (relCata (I := initial Unit Int) (junc (sumCop _ _) MSS.zero MSS.oplus)))
              ≫ est(MSS.geq) := by rw [cataR_eq_relCata]                                             -- ⦇S⦈ in RelSet
        _ = greedy := by                                                                              -- ≜ g, ≜ oplus
          show _ = Programs.mss.greedy.aop
          delta Programs.mss.greedy.aop Programs.mss.g.aop Programs.mss.oplus.aop; rw [top_zero]; rfl),
    toScan := (by
      calc greedy
          = (suffix%∋ ≫ existsImage (relCata (I := initial Unit Int) (junc (sumCop _ _) MSS.zero MSS.oplus)))
              ≫ est(MSS.geq) := by                                                                   -- ≜ g, ≜ oplus
            show Programs.mss.greedy.aop = _
            delta Programs.mss.greedy.aop Programs.mss.g.aop Programs.mss.oplus.aop; rw [top_zero]; rfl
        _ = (suffix%∋ ≫ existsImage (cataR (junc (sumCop _ _) MSS.zero MSS.oplus))) ≫ est(MSS.geq) := by
          rw [cataR_eq_relCata]                                                                       -- ⦇S⦈ in RelSet
        _ = (⦇MSS.k⦈ ≫ (graph (fun p : Int × (Int → Prop) => p.2) : (⟨Int × (Int → Prop)⟩ : RelSet.{0}) ⟶ P ⟨Int⟩))
              ≫ est(MSS.geq) := by rw [MSS.Kalg_snd_eq]                                              -- ⦇k⦈π₂ = Λ(suffix)E(g)
        _ = scan := by                                                                                -- ≜ k, ≜ scan
          show _ = Programs.mss.scan.aop
          delta Programs.mss.scan.aop Programs.mss.oplus.aop; rw [top_zero, ← k_eq]; rfl)

#print axioms Programs.mss.toShape.aop
#print axioms Programs.mss.toFused.aop
#print axioms Programs.mss.toGreedy.aop
#print axioms Programs.mss.toScan.aop
#print axioms Programs.mss.linear.aop
#print axioms k_eq
#print axioms MSS.mss_eq_scan

end LeetQ.Rel.Aop.Mss
