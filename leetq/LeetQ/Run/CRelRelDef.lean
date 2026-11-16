import LeetQ.Run.CRelDef

section
namespace LeetQ.Rel
namespace CRel
open QLean QLean.Kernel LeetQ.Rel.Alg
variable {A B C D E : Obj}

/-- `R ≫ ¬ran(T)`, ok where both inputs are and `antiJoinC` ran within capacity. -/
def antiJoin (R : CRel A B) (T : CRel B B) : CRel A B :=
  guard (R.ok && T.ok) fun _ => ofC (antiJoinC R.rel T.rel)

/-- `⊤` on the universes `Ua`, `Ub`, ok where `topC` ran within capacity. -/
def top {ma mb : USize} (Ua : Vals A ma) (Ub : Vals B mb) : CRel A B := ofC (topC Ua Ub)

/-- The coreflexive on the distinct elements of `x`, ok where `distinctCoreflC` ran within capacity. -/
def distinctCorefl (t : Obj) {n : USize} (x : Vals t n) : CRel t t := ofC (distinctCoreflC t x)

/-- `dom R`, ok where `R` is and `domC` ran within capacity. -/
def dom (R : CRel A B) : CRel A A := guard R.ok fun _ => ofC (domC R.rel)

/-- `ran R`, ok where `R` is and `ranC` ran within capacity. -/
def ran (R : CRel A B) : CRel B B := guard R.ok fun _ => ofC (ranC R.rel)

/-- `Λ(R)`, ok where `R` is and `transposeC` ran within capacity. -/
def transpose (R : CRel A B) : CRel A (.arr B) := guard R.ok fun _ => ofC (transposeC R.rel)

/-- `∋` on the arrays `X`, ok where `memC` ran within capacity. -/
def mem {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) B := ofC (memC X)

/-- `⟨R, S⟩`, ok where both inputs are and `pairC` ran within capacity. -/
def pair (R : CRel A B) (S : CRel A C) : CRel A (.prod B C) :=
  guard (R.ok && S.ok) fun _ => ofC (pairC R.rel S.rel)

/-- The rows of `R` numbered from `k`, ok where `R` is and `numC` ran within capacity. -/
def num (R : CRel A B) (k : USize) : CRel .long B := guard R.ok fun _ => ofC (numC R.rel k)

/-- `R × S`, ok where both inputs are and `prodC` ran within capacity. -/
def prod (R : CRel A B) (S : CRel D E) : CRel (.prod A D) (.prod B E) :=
  guard (R.ok && S.ok) fun _ => ofC (prodC R.rel S.rel)

/-- `R \ S` on the universes `Ub`, `Uc`, ok where both inputs are and `leftDivC` ran within capacity. -/
def leftDiv {mb mc : USize} (R : CRel A B) (S : CRel A C) (Ub : Vals B mb) (Uc : Vals C mc) : CRel B C :=
  guard (R.ok && S.ok) fun _ => ofC (leftDivC R.rel S.rel Ub Uc)

/-- `R / S` on the universes `Ua`, `Ub`, ok where both inputs are and `rightDivC` ran within capacity. -/
def rightDiv {ma mb : USize} (R : CRel A C) (S : CRel B C) (Ua : Vals A ma) (Ub : Vals B mb) : CRel A B :=
  guard (R.ok && S.ok) fun _ => ofC (rightDivC R.rel S.rel Ua Ub)

/-- `R /ₛ S` on the universes `Ua`, `Ub`, ok where both inputs are and `symDivC` ran within capacity. -/
def symDiv {ma mb : USize} (R : CRel A C) (S : CRel B C) (Ua : Vals A ma) (Ub : Vals B mb) : CRel A B :=
  guard (R.ok && S.ok) fun _ => ofC (symDivC R.rel S.rel Ua Ub)

end CRel
end LeetQ.Rel
end
