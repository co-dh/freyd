import LeetQ.Aop.RelAop
import LeetQ.Aop.CalcMssTest
import LeetQ.Rel.Programs.Mss

/-! `rel_aop` on S2's chain (`doc/rel-mss-proof-design.md` §4): `linear : mss = scan` as a Rel `calc` over the
    versions of `Programs.mss`, its four laws given Lean proofs by the `proof` block; then a step that is no instance
    of its law, and a theorem with no proof. -/

namespace LeetQ.Rel.Lang.RelAopTest

open Freyd Freyd.Alg Freyd.Alg.RelSet Freyd.Alg.RelSet.CL PowerAllegory LeetQ.Rel.Programs

rel_program mssLinear after Programs.mss where
    theorem toShape : mss = shape
    theorem toFused : shape = fused
    theorem toGreedy : fused = greedy
    theorem toScan : greedy = scan
    theorem linear : mss = scan := calc
      _ = shape := toShape
      _ = fused := toFused
      _ = greedy := toGreedy
      _ = scan := toScan

rel_aop mssLinear
  model N := (⟨Int⟩ : RelSet.{0}), zero := MSS.zero, «≥» := MSS.geq, suffix := ListRel.suffix (A := Int),
    «prefix» := ListRel.«prefix» (A := Int),
    K : Coproduct ((F Unit Int).obj ⟨Int⟩) (dL Unit) (relProd (⟨Int⟩ : RelSet.{0}) ⟨Int⟩).p := sumCop _ _,
    NN := relProd (⟨Int⟩ : RelSet.{0}) ⟨Int⟩, Nα := relProd (⟨Int⟩ : RelSet.{0}) (P ⟨Int⟩),
    NNα := relProd (⟨Int⟩ : RelSet.{0}) Nα.p, L : Coproduct ((F Unit Int).obj Nα.p) (dL Unit) NNα.p := sumCop _ _
  proof toShape := CalcMssTest.toShape, toFused := CalcMssTest.toFused, toGreedy := CalcMssTest.toGreedy,
    toScan := CalcMssTest.toScan

#print axioms mssLinear.linear.aop

/-- A step that is no instance of the law it cites fails at its Rel line. -/
rel_program mssBad after mssLinear where
    theorem bad : mss = fused := calc
      _ = fused := toShape

/--
error: line 38, col 7: the step `_ = fused` is not an instance of `toShape` : Programs.mss.mss.aop = Programs.mss.shape.aop
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  Programs.mss.shape.aop
in the target expression
  mss = fused

mss : dCL Unit Int ⟶ Int := Programs.mss.mss.aop
fused : dCL Unit Int ⟶ Int := Programs.mss.fused.aop
h'✝ : Programs.mss.mss.aop = Programs.mss.shape.aop
⊢ mss = fused
-/
#guard_msgs in
rel_aop mssBad

/-- A theorem with neither a calc nor a `proof` item is listed, and nothing is declared. -/
rel_program mssOwed after mssLinear where
    theorem owedA : greedy = mss
    theorem owedB : scan ⊑ mss

/--
error: owed: 2 theorem(s) of `LeetQ.Rel.Lang.RelAopTest.mssOwed` with no calc and no `proof` item:
  line 57, col 5: owedA : greedy = mss
  line 58, col 5: owedB : scan ⊑ mss
-/
#guard_msgs in
rel_aop mssOwed

end LeetQ.Rel.Lang.RelAopTest
