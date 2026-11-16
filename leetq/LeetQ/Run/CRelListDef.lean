import LeetQ.Run.CRelDef

section
namespace LeetQ.Rel
namespace CRel
open QLean QLean.Kernel LeetQ.Rel.Alg
variable {K A B : Obj} {n : USize}

/-- `cons°` on the arrays `X`, ok where `unconsC` ran within capacity. -/
def uncons (X : Vals (.arr B) n) : CRel (.arr B) (.prod B (.arr B)) := ofC (unconsC X)

/-- `tail` on the arrays `X`, ok where `tailC` ran within capacity. -/
def tail (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := ofC (tailC X)

/-- `at(k)` on the arrays `X`, ok where `atPosC` ran within capacity. -/
def atPos (k : Nat) (X : Vals (.arr B) n) : CRel (.arr B) B := ofC (atPosC k X)

/-- `snoc°` on the arrays `X`, ok where `unsnocC` ran within capacity. -/
def unsnoc (X : Vals (.arr B) n) : CRel (.arr B) (.prod (.arr B) B) := ofC (unsnocC X)

/-- `inits` on the arrays `X`, ok where `initsC` ran within capacity. -/
def inits (X : Vals (.arr B) n) : CRel (.arr B) (.arr (.arr B)) := ofC (initsC X)

/-- `tails` on the arrays `X`, ok where `tailsC` ran within capacity. -/
def tails (X : Vals (.arr B) n) : CRel (.arr B) (.arr (.arr B)) := ofC (tailsC X)

/-- `prefix` on the arrays `X`, ok where `prefixC` ran within capacity. -/
def «prefix» (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := ofC (prefixC X)

/-- `suffix` on the arrays `X`, ok where `suffixC` ran within capacity. -/
def suffix (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := ofC (suffixC X)
/-- `filter` of the keys of `P` on the arrays `X`, ok where `P` is and `filterC` ran within capacity. -/
def filter (P : CRel B B) (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := guard P.ok fun _ => ofC (filterC P.rel X)

/-- `takewhile` of the keys of `P` on the arrays `X`, ok where `P` is and `takewhileC` ran within capacity. -/
def takewhile (P : CRel B B) (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := guard P.ok fun _ => ofC (takewhileC P.rel X)
/-- `concat` on the arrays of arrays `X`, ok where `concatC` ran within capacity. -/
def concat (X : Vals (.arr (.arr B)) n) : CRel (.arr (.arr B)) (.arr B) := ofC (concatC X)

/-- `cat°` on the arrays `X`, ok where `uncatC` ran within capacity. -/
def uncat (X : Vals (.arr B) n) : CRel (.arr B) (.prod (.arr B) (.arr B)) := ofC (uncatC X)

/-- `cons`, ok where `P` is and `consC` ran within capacity. -/
def cons (P : CRel K (.prod B (.arr B))) : CRel K (.arr B) := guard P.ok fun _ => ofC (consC P.rel)

/-- `cat`, ok where `P` is and `catC` ran within capacity. -/
def cat (P : CRel K (.prod (.arr B) (.arr B))) : CRel K (.arr B) := guard P.ok fun _ => ofC (catC P.rel)

/-- `snoc`, ok where `P` is and `snocC` ran within capacity. -/
def snoc (P : CRel K (.prod (.arr B) B)) : CRel K (.arr B) := guard P.ok fun _ => ofC (snocC P.rel)

/-- `zip`, ok where `P` is and `zipC` ran within capacity. -/
def zip (P : CRel K (.prod (.arr A) (.arr B))) : CRel K (.arr (.prod A B)) :=
  guard P.ok fun _ => ofC (zipC P.rel)

/-- `α ≜ [nil, cons]` on `I` and `P`, ok where `alphaC` ran within capacity. -/
def alpha (I : Vals K 1) (P : Vals (.prod B (.arr B)) n) : CRel (.sum K (.prod B (.arr B))) (.arr B) :=
  ofC (alphaC I P)

end CRel
end LeetQ.Rel
end
