import LeetQ.Run.CRelDef

section
namespace LeetQ.Rel
namespace CRel
open QLean QLean.Kernel LeetQ.Rel.Alg
variable {K A B : Obj} {n : USize}

/-- `cons°` on the arrays `X`, ok where `unconsC` ran within capacity. -/
def uncons (X : Vals (.arr B) n) : CRel (.arr B) (.prod B (.arr B)) := let r := unconsC X; ⟨r.1, r.2⟩

/-- `tail` on the arrays `X`, ok where `tailC` ran within capacity. -/
def tail (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := let r := tailC X; ⟨r.1, r.2⟩

/-- `at(k)` on the arrays `X`, ok where `atPosC` ran within capacity. -/
def atPos (k : Nat) (X : Vals (.arr B) n) : CRel (.arr B) B := let r := atPosC k X; ⟨r.1, r.2⟩

/-- `snoc°` on the arrays `X`, ok where `unsnocC` ran within capacity. -/
def unsnoc (X : Vals (.arr B) n) : CRel (.arr B) (.prod (.arr B) B) := let r := unsnocC X; ⟨r.1, r.2⟩

/-- `inits` on the arrays `X`, ok where `initsC` ran within capacity. -/
def inits (X : Vals (.arr B) n) : CRel (.arr B) (.arr (.arr B)) := let r := initsC X; ⟨r.1, r.2⟩

/-- `tails` on the arrays `X`, ok where `tailsC` ran within capacity. -/
def tails (X : Vals (.arr B) n) : CRel (.arr B) (.arr (.arr B)) := let r := tailsC X; ⟨r.1, r.2⟩

/-- `prefix` on the arrays `X`, ok where `prefixC` ran within capacity. -/
def «prefix» (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := let r := prefixC X; ⟨r.1, r.2⟩

/-- `suffix` on the arrays `X`, ok where `suffixC` ran within capacity. -/
def suffix (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := let r := suffixC X; ⟨r.1, r.2⟩

/-- `cat°` on the arrays `X`, ok where `uncatC` ran within capacity. -/
def uncat (X : Vals (.arr B) n) : CRel (.arr B) (.prod (.arr B) (.arr B)) := let r := uncatC X; ⟨r.1, r.2⟩

/-- `cons`, ok where `P` is and `consC` ran within capacity. -/
def cons (P : CRel K (.prod B (.arr B))) : CRel K (.arr B) := guard P.ok fun _ => let r := consC P.rel; ⟨r.1, r.2⟩

/-- `cat`, ok where `P` is and `catC` ran within capacity. -/
def cat (P : CRel K (.prod (.arr B) (.arr B))) : CRel K (.arr B) := guard P.ok fun _ => let r := catC P.rel; ⟨r.1, r.2⟩

/-- `snoc`, ok where `P` is and `snocC` ran within capacity. -/
def snoc (P : CRel K (.prod (.arr B) B)) : CRel K (.arr B) := guard P.ok fun _ => let r := snocC P.rel; ⟨r.1, r.2⟩

/-- `zip`, ok where `P` is and `zipC` ran within capacity. -/
def zip (P : CRel K (.prod (.arr A) (.arr B))) : CRel K (.arr (.prod A B)) :=
  guard P.ok fun _ => let r := zipC P.rel; ⟨r.1, r.2⟩

/-- `α ≜ [nil, cons]` on `I` and `P`, ok where `alphaC` ran within capacity. -/
def alpha (I : Vals K 1) (P : Vals (.prod B (.arr B)) n) : CRel (.sum K (.prod B (.arr B))) (.arr B) :=
  let r := alphaC I P; ⟨r.1, r.2⟩

end CRel
end LeetQ.Rel
end
