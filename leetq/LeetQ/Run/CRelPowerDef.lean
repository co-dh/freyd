import LeetQ.Run.CRelDef

section
namespace LeetQ.Rel
namespace CRel
open QLean QLean.Kernel LeetQ.Rel.Alg
variable {A B : Obj}

/-- `τ` on `X`, ok where `τC` ran within capacity. -/
def τ {n : USize} (X : Vals A n) : CRel A (.arr A) := let r := τC X; ⟨r.1, r.2⟩

/-- `Λ(R)` total on `U`, ok where `R` is and `lamOnC` ran within capacity. -/
def lamOn {m : USize} (R : CRel A B) (U : Vals A m) : CRel A (.arr B) :=
  guard R.ok fun _ => let r := lamOnC R.rel U; ⟨r.1, r.2⟩

/-- `setify` on `X`, ok where `setifyC` ran within capacity. -/
def setify {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := let r := setifyC X; ⟨r.1, r.2⟩

/-- `E(R)` on `X`, ok where `R` is and `EC` ran within capacity. -/
def E {n : USize} (R : CRel A B) (X : Vals (.arr A) n) : CRel (.arr A) (.arr B) :=
  guard R.ok fun _ => let r := EC R.rel X; ⟨r.1, r.2⟩

/-- `union` on the arrays of arrays `X`, ok where `Arr.unionC` ran within capacity. -/
def Arr.union {n : USize} (X : Vals (.arr (.arr A)) n) : CRel (.arr (.arr A)) (.arr A) :=
  let r := Alg.Arr.unionC X; ⟨r.1, r.2⟩

/-- `P(R)` from `X` to `Y`, ok where `R` is and `PC` ran within capacity. -/
def P {n m : USize} (R : CRel A B) (X : Vals (.arr A) n) (Y : Vals (.arr B) m) : CRel (.arr A) (.arr B) :=
  guard R.ok fun _ => let r := PC R.rel X Y; ⟨r.1, r.2⟩

end CRel
end LeetQ.Rel
end
