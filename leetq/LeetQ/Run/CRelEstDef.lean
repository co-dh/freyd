import LeetQ.Run.CRelDef

section
namespace LeetQ.Rel
open QLean QLean.Kernel LeetQ.Rel LeetQ.Rel.Alg
namespace Rep
variable {A B : Obj}

/-- The pairs `(y, z)` `orderedOn` compares on `X`, `y` heading a suffix of an array of `X` and `z` in its rest: the
    coreflexive its test runs on. -/
def ordPairs {n : USize} (X : Vals (.arr B) n) : Rel (.prod B B) (.prod B B) :=
  let D := ran (suffix X ≫ uncons (ran (suffix X)).val)
  ran (pair (outl D) (outr D ≫ mem (ran (outr D)).val))

end Rep
end LeetQ.Rel
end

section
namespace LeetQ.Rel
open QLean QLean.Kernel LeetQ.Rel LeetQ.Rel.Alg
namespace CRel
variable {A B : Obj}

/-- A test over `CRel`s as a twin's test: it sees its input as ok, whose bit is already in the op's. -/
def testC (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) :
    Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool :=
  fun D => let s := q ⟨D, true⟩; (s.rel, s.ok)

/-- `pairsIn Q D`, ok where `Q`, `D` are and `pairsInC` ran within capacity. -/
def pairsIn (Q : CRel B B) (D : CRel (.prod B B) (.prod B B)) : CRel (.prod B B) (.prod B B) :=
  guard (Q.ok && D.ok) fun _ => ofC (pairsInC Q.rel D.rel)

/-- `swapIn q D`, ok where `D` is, the test was and `swapInC` ran within capacity. -/
def swapIn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) (D : CRel (.prod B B) (.prod B B)) :
    CRel (.prod B B) (.prod B B) := guard D.ok fun _ => ofC (swapInC (testC q) D.rel)

/-- `estOn q G`, ok where `G` is, the test was and `estOnC` ran within capacity. -/
def estOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) (G : CRel A B) : CRel A B :=
  guard G.ok fun _ => ofC (estOnC (testC q) G.rel)

/-- `thinOn q G`, ok where `G` is, the test was and `thinOnC` ran within capacity. -/
def thinOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) (G : CRel A B) : CRel A B :=
  guard G.ok fun _ => ofC (thinOnC (testC q) G.rel)

/-- `est(Q)` on `G`, ok where `Q`, `G` are and `estC` ran within capacity. -/
def est (Q : CRel B B) (G : CRel A B) : CRel A B := guard (Q.ok && G.ok) fun _ => ofC (estC Q.rel G.rel)

/-- `thin(Q)` on `G`, ok where `Q`, `G` are and `thinC` ran within capacity. -/
def thin (Q : CRel B B) (G : CRel A B) : CRel A B :=
  guard (Q.ok && G.ok) fun _ => ofC (thinC Q.rel G.rel)

/-- `orderedOn q` on `X`, ok where the test was and `orderedOnC` ran within capacity. -/
def orderedOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) {n : USize} (X : Vals (.arr B) n) :
    CRel (.arr B) (.arr B) := ofC (orderedOnC (testC q) X)

/-- `ordered(Q)` on `X`, ok where `Q` is and `orderedC` ran within capacity. -/
def ordered (Q : CRel B B) {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) :=
  guard Q.ok fun _ => ofC (orderedC Q.rel X)

/-- `thinL(Q)` on `X`, ok where `Q` is and `thinLC` ran within capacity. -/
def thinL (Q : CRel B B) {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) :=
  guard Q.ok fun _ => ofC (thinLC Q.rel X)

/-- `sortSet(Q)` on `Y`, ok where `Q` is and `sortSetC` ran within capacity. -/
def sortSet (Q : CRel B B) {n : USize} (Y : Vals (.arr B) n) : CRel (.arr B) (.arr B) :=
  guard Q.ok fun _ => ofC (sortSetC Q.rel Y)

end CRel
end LeetQ.Rel
end
