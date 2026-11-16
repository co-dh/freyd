import LeetQ.Aop.Mss

/-! `rel_aop` on programs read after `Programs.mss` (whose `rel_aop` is `LeetQ.Aop.Mss`,
    `doc/rel-mss-proof-design.md` §4): a step that is no instance of its law, a theorem with no proof, laws with
    parameters and hypotheses cited applied, and a cited law's hypothesis nothing discharges. -/

namespace LeetQ.Rel.Lang.RelAopTest

open Freyd Freyd.Alg Freyd.Alg.RelSet Freyd.Alg.RelSet.CL PowerAllegory LeetQ.Rel.Programs

open LeetQ.Rel.Programs.prelude Programs.mss in
/-- A step that is no instance of the law it cites fails at its Rel line. -/
rel_program mssBad where
    theorem bad : mss = fused := calc
      _ = fused := toShape

/--
error: line 15, col 7: the step `_ = fused` is not an instance of `toShape` : Programs.mss.mss.aop = Programs.mss.shape.aop
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  Programs.mss.mss.aop
in the target expression
  mss = fused

mss : dCL Unit Int ⟶ Int := Programs.mss.mss.aop
fused : dCL Unit Int ⟶ Int := Programs.mss.fused.aop
⊢ mss = fused
-/
#guard_msgs in
rel_aop mssBad

open LeetQ.Rel.Programs.prelude Programs.mss in
/-- A theorem with neither a calc nor a `proof` item is listed, and nothing is declared. -/
rel_program mssOwed where
    theorem owedA : greedy = mss
    theorem owedB : scan ⊑ mss

/--
error: owed: 2 theorem(s) of `LeetQ.Rel.Lang.RelAopTest.mssOwed` with no calc and no `proof` item:
  line 34, col 5: owedA : greedy = mss
  line 35, col 5: owedB : scan ⊑ mss
-/
#guard_msgs in
rel_aop mssOwed

open LeetQ.Rel.Programs.prelude Programs.mss in
/-- Steps citing the prelude's laws, which have parameters, quantified objects and hypotheses, applied; two of them
    put a composite in place inside a longer composite, and `estMap`'s hypotheses are the opened `mss`'s facts. -/
rel_program laws where
    theorem union : Λ(suffix)E(prefix sum)est(≥) = Λ(suffix)E(Λ(prefix sum))E(∋)est(≥) := calc
      _ = Λ(suffix)E(Λ(prefix sum))E(∋)est(≥) := Eunion(prefix sum)
    theorem comp : Λ(suffix)E(Λ(prefix sum))E(est(≥))est(≥) = Λ(suffix)E(Λ(prefix sum)est(≥))est(≥) := calc
      _ = Λ(suffix)E(Λ(prefix sum)est(≥))est(≥) := Ecomp(Λ(prefix sum), est(≥))
    theorem point : ⦇[Λ(zero)est(≥), oplus]⦈ = g := calc
      _ = ⦇[zero, oplus]⦈ := estMap(zero, ≥)
      _ = g := ≜ g

rel_aop laws
  model N := (⟨Int⟩ : RelSet.{0}), zero := MSS.zero, «≥» := MSS.geq, suffix := ListRel.suffix (A := Int),
    «prefix» := ListRel.«prefix» (A := Int),
    K : Coproduct ((F Unit Int).obj ⟨Int⟩) (dL Unit) (relProd (⟨Int⟩ : RelSet.{0}) ⟨Int⟩).p := sumCop _ _

open LeetQ.Rel.Programs.prelude Programs.mss in
/-- A second program declaring `geqRefl`, as `mss` does, so that a bare citation of it is ambiguous below. -/
rel_program lawsTwin where
    theorem geqRefl : 𝟙 ⊑ ≥

-- a bare citation two opened programs declare is ambiguous, and the error names both
/-- error: line 73, col 16: ambiguous name `geqRefl`: it is [LeetQ.Rel.Programs.mss.geqRefl, LeetQ.Rel.Lang.RelAopTest.lawsTwin.geqRefl] -/
#guard_msgs in
open LeetQ.Rel.Programs.prelude Programs.mss lawsTwin in
rel_program lawsAmbiguous where
    theorem twice : 𝟙 ⊑ ≥ := calc
      _ ⊑ ≥ := geqRefl

open LeetQ.Rel.Programs.prelude Programs.mss in
/-- A cited law whose hypothesis nothing discharges: `prelude.estMap` at `oplus` needs `dom(oplus) = 𝟙`, which no
    hypothesis of `bad` and no theorem of an opened program states. The program-qualified name resolves too. -/
rel_program lawsBad where
    theorem bad : Λ(oplus)est(≥) = oplus := calc
      _ = oplus := prelude.estMap(oplus, ≥)

/--
error: line 80, col 7: the step `_ … oplus` cites `prelude.estMap`, whose hypothesis
  dom oplus = 𝟙(Int × Int)
no hypothesis of `bad` and no theorem proved before it that takes no parameters discharges
Tactic `assumption` failed

N : RelSet := ⋯
zero : 𝟏 ⟶ Int := MSS.zero
«≥» : Int ⟶ Int := «≥»
oplus : Int × Int ⟶ Int := mss.oplus.aop
⊢ dom oplus = 𝟙(Int × Int)
-/
#guard_msgs in
rel_aop lawsBad
  model N := (⟨Int⟩ : RelSet.{0}), zero := MSS.zero, «≥» := MSS.geq

end LeetQ.Rel.Lang.RelAopTest
