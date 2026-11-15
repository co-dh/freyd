import LeetQ.Aop.Mss

/-! `rel_aop`'s failures, on programs read after `Programs.mss` (whose `rel_aop` is `LeetQ.Aop.Mss`,
    `doc/rel-mss-proof-design.md` §4): a step that is no instance of its law, and a theorem with no proof. -/

namespace LeetQ.Rel.Lang.RelAopTest

open Freyd Freyd.Alg Freyd.Alg.RelSet Freyd.Alg.RelSet.CL PowerAllegory LeetQ.Rel.Programs

open LeetQ.Rel.Programs.prelude Programs.mss in
/-- A step that is no instance of the law it cites fails at its Rel line. -/
rel_program mssBad where
    theorem bad : mss = fused := calc
      _ = fused := toShape

/--
error: line 14, col 7: the step `_ = fused` is not an instance of `toShape` : Programs.mss.mss.aop = Programs.mss.shape.aop
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

end LeetQ.Rel.Lang.RelAopTest
