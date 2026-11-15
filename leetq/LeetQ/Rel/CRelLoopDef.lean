import LeetQ.Rel.CRelDef

section
namespace LeetQ.Rel
open QLean QLean.Kernel LeetQ.Rel LeetQ.Rel.Alg
namespace Rep

/-- The pairs `(c, y)` a round of `loopOn` meets at its states `St`, whose `ran` its step sees. -/
def loopPairs {K X Y : Obj} (St : Rel K (.prod X (.arr Y))) : Rel (.prod X (.arr Y)) (.prod X Y) :=
  pair (outl (ran St)) (outl (outr (ran St) ≫ uncons (ran (outr (ran St))).val))

end Rep
end LeetQ.Rel
end

section
namespace LeetQ.Rel
open QLean QLean.Kernel LeetQ.Rel LeetQ.Rel.Alg
namespace CRel
variable {K X Y B : Obj}

/-- `tic`, ok where `P` is and `ticC` ran within capacity. -/
def tic (P : CRel K (.prod B (.arr B))) : CRel K (.arr (.arr B)) := guard P.ok fun _ => let r := ticC P.rel; ⟨r.1, r.2⟩

/-- `suffix` on the arrays `X`, ok where `suffixC` ran within capacity. -/
def suffix {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := let r := suffixC X; ⟨r.1, r.2⟩

/-- `loopOn` on a step over `CRel`s, ok where `P` is, every round's step was and `loopOnC` ran within capacity. The
    step sees its input as ok: its bit is already in the loop's. -/
def loopOn (F : CRel (.prod X Y) (.prod X Y) → CRel (.prod X Y) X) (P : CRel K (.prod X (.arr Y))) : CRel K X :=
  guard P.ok fun _ => let r := loopOnC (fun D => let s := F ⟨D, true⟩; (s.rel, s.ok)) P.rel; ⟨r.1, r.2⟩

/-- `loop(F)`, ok where `F` and `P` are and `loopC` ran within capacity. -/
def loop (F : CRel (.prod X Y) X) (P : CRel K (.prod X (.arr Y))) : CRel K X :=
  guard (F.ok && P.ok) fun _ => let r := loopC F.rel P.rel; ⟨r.1, r.2⟩

/-- `mergeOn` on a test over `CRel`s, ok where `P` is, every round's test was and `mergeOnC` ran within capacity.
    The test sees its input as ok: its bit is already in the merge's. -/
def mergeOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) (P : CRel K (.prod (.arr B) (.arr B))) :
    CRel K (.arr B) :=
  guard P.ok fun _ => let r := mergeOnC (fun D => let s := q ⟨D, true⟩; (s.rel, s.ok)) P.rel; ⟨r.1, r.2⟩

/-- `merge(Q)`, ok where `Q` and `P` are and `mergeC` ran within capacity. -/
def merge (Q : CRel B B) (P : CRel K (.prod (.arr B) (.arr B))) : CRel K (.arr B) :=
  guard (Q.ok && P.ok) fun _ => let r := mergeC Q.rel P.rel; ⟨r.1, r.2⟩

/-- `fixOn` on a step over `CRel`s, with the rounds run: ok where `X₀` is, every round's step was and `fixOnC` ran
    within capacity. The step sees its input as ok: its bit is already in the loop's. -/
def fixOn {A : Obj} (n : Nat) (φ : CRel A B → CRel A B) (X₀ : CRel A B) : CRel A B × Nat :=
  guard X₀.ok fun _ => let r := fixOnC n (fun D => let s := φ ⟨D, true⟩; (s.rel, s.ok)) X₀.rel; (⟨r.1.1, r.2⟩, r.1.2)

end CRel
end LeetQ.Rel
end
