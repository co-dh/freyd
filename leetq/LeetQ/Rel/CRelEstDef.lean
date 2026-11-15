import LeetQ.Rel.CRelDef

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
  guard (Q.ok && D.ok) fun _ => let r := pairsInC Q.rel D.rel; ⟨r.1, r.2⟩

/-- `swapIn q D`, ok where `D` is, the test was and `swapInC` ran within capacity. -/
def swapIn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) (D : CRel (.prod B B) (.prod B B)) :
    CRel (.prod B B) (.prod B B) := guard D.ok fun _ => let r := swapInC (testC q) D.rel; ⟨r.1, r.2⟩

/-- `estOn q G`, ok where `G` is, the test was and `estOnC` ran within capacity. -/
def estOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) (G : CRel A B) : CRel A B :=
  guard G.ok fun _ => let r := estOnC (testC q) G.rel; ⟨r.1, r.2⟩

/-- `thinOn q G`, ok where `G` is, the test was and `thinOnC` ran within capacity. -/
def thinOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) (G : CRel A B) : CRel A B :=
  guard G.ok fun _ => let r := thinOnC (testC q) G.rel; ⟨r.1, r.2⟩

/-- `est(Q)` on `G`, ok where `Q`, `G` are and `estC` ran within capacity. -/
def est (Q : CRel B B) (G : CRel A B) : CRel A B := guard (Q.ok && G.ok) fun _ => let r := estC Q.rel G.rel; ⟨r.1, r.2⟩

/-- `thin(Q)` on `G`, ok where `Q`, `G` are and `thinC` ran within capacity. -/
def thin (Q : CRel B B) (G : CRel A B) : CRel A B :=
  guard (Q.ok && G.ok) fun _ => let r := thinC Q.rel G.rel; ⟨r.1, r.2⟩

/-- `orderedOn q` on `X`, ok where the test was and `orderedOnC` ran within capacity. -/
def orderedOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) {n : USize} (X : Vals (.arr B) n) :
    CRel (.arr B) (.arr B) := let r := orderedOnC (testC q) X; ⟨r.1, r.2⟩

/-- `ordered(Q)` on `X`, ok where `Q` is and `orderedC` ran within capacity. -/
def ordered (Q : CRel B B) {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) :=
  guard Q.ok fun _ => let r := orderedC Q.rel X; ⟨r.1, r.2⟩

/-- `thinL(Q)` on `X`, ok where `Q` is and `thinLC` ran within capacity. -/
def thinL (Q : CRel B B) {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) :=
  guard Q.ok fun _ => let r := thinLC Q.rel X; ⟨r.1, r.2⟩

/-- `sortSet(Q)` on `Y`, ok where `Q` is and `sortSetC` ran within capacity. -/
def sortSet (Q : CRel B B) {n : USize} (Y : Vals (.arr B) n) : CRel (.arr B) (.arr B) :=
  guard Q.ok fun _ => let r := sortSetC Q.rel Y; ⟨r.1, r.2⟩

end CRel
end LeetQ.Rel
end
