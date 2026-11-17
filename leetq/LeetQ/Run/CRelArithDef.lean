import LeetQ.Run.CRelDef

section
namespace LeetQ.Rel
namespace CRel
open QLean QLean.Kernel LeetQ.Rel.Alg
variable {A B C D : Obj}

/-- `inl` on the universe `X`, ok where `inlC` ran within capacity. -/
def inl {n : USize} (X : Vals A n) : CRel A (.sum A B) := ofC (inlC X)

/-- `inr` on the universe `Y`, ok where `inrC` ran within capacity. -/
def inr {n : USize} (Y : Vals B n) : CRel B (.sum A B) := ofC (inrC Y)

/-- `[R, S]`, ok where both inputs are and `juncC` ran within capacity. -/
def junc (R : CRel A C) (S : CRel B C) : CRel (.sum A B) C :=
  guard (R.ok && S.ok) fun _ => ofC (juncC R.rel S.rel)

/-- `R + S`, ok where both inputs are and `sumC` ran within capacity. -/
def sum (R : CRel A C) (S : CRel B D) : CRel (.sum A B) (.sum C D) :=
  guard (R.ok && S.ok) fun _ => ofC (sumC R.rel S.rel)

/-- `<` on `U`, ok where `ltC` ran within capacity. -/
def lt {t : QAtomicType} {n : USize} (U : Vals (.atom t) n) (h : t ≠ .general := by decide)
    (hu : t ≠ .guid := by decide) :
    CRel (.atom t) (.atom t) := ofC (ltC U h hu)

/-- `≤` on `U`, ok where `leqC` ran within capacity. -/
def leq {t : QAtomicType} {n : USize} (U : Vals (.atom t) n) (h : t ≠ .general := by decide)
    (hu : t ≠ .guid := by decide) :
    CRel (.atom t) (.atom t) := ofC (leqC U h hu)

/-- `succ` on `U`, ok where `succC` ran within capacity. -/
def succ {n : USize} (U : Vals (.atom .long) n) : CRel (.atom .long) (.atom .long) := ofC (succC U)

/-- `asc` on the arrays `X`, ok where `ascC` ran within capacity. -/
def asc {B : Obj} {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := ofC (ascC X)

end CRel
end LeetQ.Rel
end
