import LeetQ.Run.CRelDef

section
namespace LeetQ.Rel
namespace CRel
open QLean QLean.Kernel LeetQ.Rel.Alg

/-- `foldBy` on a step over `CRel`s, ok where every round's step was and `foldByC` ran within capacity. The
    step sees its inputs as ok: their bits are already in the fold's. -/
def foldBy {E V : Obj} {n m : USize} (X : Vals (.arr E) n) (e : Vals V m)
    (step : CRel .long E → CRel .long V → CRel .long V) : CRel (.arr E) V :=
  ofC (foldByC X e fun el p => let s := step ⟨el, true⟩ ⟨p, true⟩; (s.rel, s.ok))

/-- `foldOn` on a family over `CRel`s, ok where every round's family member was and `foldOnC` ran within
    capacity. The family sees the round's pairs as ok: their bits are already in the fold's. -/
def foldOn {E V : Obj} {m n : USize} (e : Vals V m) (S : CRel (.prod E V) (.prod E V) → CRel (.prod E V) V)
    (X : Vals (.arr E) n) : CRel (.arr E) V :=
  ofC (foldOnC e (fun D => ((S ⟨D, true⟩).rel, (S ⟨D, true⟩).ok)) X)

/-- `fold` of one `CRel` step, ok where `S` is and `foldC` ran within capacity. -/
def fold {E V : Obj} {m n : USize} (e : Vals V m) (S : CRel (.prod E V) V) (X : Vals (.arr E) n) : CRel (.arr E) V :=
  guard S.ok fun _ => ofC (foldC e S.rel X)

/-- `sum` as a `CRel`, ok where `sumC` ran within capacity. -/
def Arr.sum {n : USize} (X : Vals (.arr .long) n) : CRel (.arr .long) .long :=
  ofC (Alg.Arr.sumC X)

/-- `length` as a `CRel`, ok where `lengthC` ran within capacity. -/
def length {E : Obj} {n : USize} (X : Vals (.arr E) n) : CRel (.arr E) .long :=
  ofC (lengthC X)

/-- `map` as a `CRel`, ok where `R` is and `mapC` ran within capacity. -/
def map {A B : Obj} {n : USize} (R : CRel A B) (X : Vals (.arr A) n) : CRel (.arr A) (.arr B) :=
  guard R.ok fun _ => ofC (mapC R.rel X)

/-- `perm` as a `CRel`, ok where `permC` ran within capacity. -/
def perm {B : Obj} {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) :=
  ofC (permC X)

/-- `subseq` as a `CRel`, ok where `subseqC` ran within capacity. -/
def subseq {B : Obj} {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) :=
  ofC (subseqC X)

/-- `thinLOn` on a test over `CRel`s, ok where every call of the test was and `thinLOnC` ran within capacity. The
    test sees the round's pairs as ok: their bits are already in the fold's. -/
def thinLOn {B : Obj} {n : USize} (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B))
    (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) :=
  ofC (thinLOnC (fun D => ((q ⟨D, true⟩).rel, (q ⟨D, true⟩).ok)) X)

/-- `R − S`, ok where both inputs are and `diffC` ran within capacity. Its rows are a subsequence of `R`'s, canonical
    where `R` is (`canon_diff`), so it skips `canonC`. -/
def diff {A B : Obj} (R S : CRel A B) : CRel A B := guard (R.ok && S.ok) fun _ => let r := diffC R.rel S.rel; ⟨r.1, r.2⟩

end CRel
end LeetQ.Rel
end
