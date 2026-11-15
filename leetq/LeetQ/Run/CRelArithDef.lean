import LeetQ.Run.CRelDef

section
namespace LeetQ.Rel
namespace CRel
open QLean QLean.Kernel LeetQ.Rel.Alg
variable {A B C D : Obj}

/-- `inl` on the universe `X`, ok where `inlC` ran within capacity. -/
def inl {n : USize} (X : Vals A n) : CRel A (.sum A B) := let r := inlC X; ⟨r.1, r.2⟩

/-- `inr` on the universe `Y`, ok where `inrC` ran within capacity. -/
def inr {n : USize} (Y : Vals B n) : CRel B (.sum A B) := let r := inrC Y; ⟨r.1, r.2⟩

/-- `[R, S]`, ok where both inputs are and `juncC` ran within capacity. -/
def junc (R : CRel A C) (S : CRel B C) : CRel (.sum A B) C :=
  guard (R.ok && S.ok) fun _ => let r := juncC R.rel S.rel; ⟨r.1, r.2⟩

/-- `R + S`, ok where both inputs are and `sumC` ran within capacity. -/
def sum (R : CRel A C) (S : CRel B D) : CRel (.sum A B) (.sum C D) :=
  guard (R.ok && S.ok) fun _ => let r := sumC R.rel S.rel; ⟨r.1, r.2⟩

/-- `<` on `U`, ok where `ltC` ran within capacity. -/
def lt {t : QAtomicType} {n : USize} (U : Vals (.atom t) n) (h : t ≠ .general := by decide) :
    CRel (.atom t) (.atom t) := let r := ltC U h; ⟨r.1, r.2⟩

/-- `≤` on `U`, ok where `leqC` ran within capacity. -/
def leq {t : QAtomicType} {n : USize} (U : Vals (.atom t) n) (h : t ≠ .general := by decide) :
    CRel (.atom t) (.atom t) := let r := leqC U h; ⟨r.1, r.2⟩

/-- `succ` on `U`, ok where `succC` ran within capacity. -/
def succ {n : USize} (U : Vals (.atom .long) n) : CRel (.atom .long) (.atom .long) := let r := succC U; ⟨r.1, r.2⟩

/-- `bagify` on the arrays `X`, ok where `bagifyC` ran within capacity. -/
def bagify {B : Obj} {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := let r := bagifyC X; ⟨r.1, r.2⟩

end CRel
end LeetQ.Rel
end
