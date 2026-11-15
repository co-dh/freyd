import LeetQ.Aop.RelAop
import LeetQ.Rel.Programs.Prelude
import AOP.A4_6
import AOP.A7_1

/-! `rel_aop prelude`: the prelude's laws, stated for any relations, proved in the AOP allegory. -/

namespace LeetQ.Rel.Aop.Prelude

open Freyd Freyd.Alg Freyd.Alg.RelSet Freyd.Alg.RelSet.CL PowerAllegory
open LeetQ.Rel.Programs

rel_aop prelude
  proof
    absorption := Λ_absorption S R,
    Eunion := existsImage_eq_Λ_bigUnion R,
    Ecomp := existsImage_comp R S,
    estMap := Λ_map_comp_est ⟨h₁, h₂⟩ h₃

#print axioms Programs.prelude.absorption.aop
#print axioms Programs.prelude.Eunion.aop
#print axioms Programs.prelude.Ecomp.aop
#print axioms Programs.prelude.estMap.aop

end LeetQ.Rel.Aop.Prelude
