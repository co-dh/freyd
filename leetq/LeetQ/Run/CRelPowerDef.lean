import LeetQ.Run.CRelDef

section
namespace LeetQ.Rel
namespace CRel
open QLean QLean.Kernel LeetQ.Rel.Alg
variable {A B : Obj}

/-- `τ` on `X`, ok where `τC` ran within capacity. -/
def τ {n : USize} (X : Vals A n) : CRel A (.arr A) := ofC (τC X)

/-- `Λ(R)` total on `U`, ok where `R` is and `lamOnC` ran within capacity. -/
def lamOn {m : USize} (R : CRel A B) (U : Vals A m) : CRel A (.arr B) :=
  guard R.ok fun _ => ofC (lamOnC R.rel U)

/-- `setify` on `X`, ok where `setifyC` ran within capacity. -/
def setify {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := ofC (setifyC X)

/-- `distinct` on `X`, ok where `distinctC` ran within capacity. -/
def distinct {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := ofC (distinctC X)

/-- `E(R)` on `X`, ok where `R` is and `EC` ran within capacity. -/
def E {n : USize} (R : CRel A B) (X : Vals (.arr A) n) : CRel (.arr A) (.arr B) :=
  guard R.ok fun _ => ofC (EC R.rel X)

end CRel
end LeetQ.Rel
end
