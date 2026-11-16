import LeetQ.Run.Alg
import LeetQ.Run.Core

section
namespace LeetQ.Rel

/-- A relation and whether every op that built it ran within capacity. -/
structure CRel (k v : Obj) where
  rel : Rel k v
  ok : Bool

namespace Alg

open QLean QLean.Dep QLean.Kernel

/-- `R` in canonical form: its rows ascending by `Obj.lt` on `(key, val)` (`sortByC` of the pair side, the order
    `sortsAsc_all` proves the kernels keep), then the first of each run of equal rows (`nubC`). The bit `&&`s the
    sort's, `R`'s two sides fitting at all its rows (`fitsN`), and `nubC`'s. -/
def canonC {k v : Obj} (R : Rel k v) : Rel k v × Bool :=
  let s := (Obj.prod k v).sortByC (pairPart R).2 (tilLongs R.n)
  let N := nubC (R.rows s.1)
  (N.1, s.2 && Vals.fitsN k R.key R.n.toNat && Vals.fitsN v R.val R.n.toNat && N.2)

/-- A relation from its pairs of longs, in canonical form (`canonC`), so a literal is equal data to any op's
    answer with the same pairs; a `canonC` past capacity stops with its message, as `col` does. -/
def ofPairs (ps : List (Int64 × Int64)) : Rel .long .long :=
  let c := canonC (⟨ps.length.toUSize, List.length_map _ ▸ col (ps.map (·.1)), List.length_map _ ▸ col (ps.map (·.2))⟩ :
    Rel .long .long)
  need (c.2 = true) (fun _ => s!"ofPairs: canonC of {ps.length} pairs ran past capacity") (fun _ => zero) fun _ => c.1

end Alg

end LeetQ.Rel
end

section
namespace LeetQ.Rel
namespace CRel
open QLean QLean.Kernel LeetQ.Rel.Alg
variable {A B C : Obj}

/-- A twin's answer as a `CRel`, its rows in canonical form (`canonC`): ok where the twin's bit and `canonC`'s are. -/
def ofC (r : Rel A B × Bool) : CRel A B := let c := canonC r.1; ⟨c.1, r.2 && c.2⟩

/-- A stopped run: `𝟘`, its bit false. -/
instance : Inhabited (CRel A B) := ⟨⟨default, false⟩⟩

/-- Runs the op `k` only where its inputs' bits `b` are all set; otherwise stops at `default` (`𝟘`, bit false)
    without running it, since an op on a bad input answers nothing worth its cost. -/
def guard {α : Type} [Inhabited α] (b : Bool) (k : Unit → α) : α := if b then k () else default

/-- `R ≫ S`, ok where both inputs are and `compC` ran within capacity. -/
def comp (R : CRel A B) (S : CRel B C) : CRel A C := guard (R.ok && S.ok) fun _ => ofC (compC R.rel S.rel)

/-- `R ∩ S`, ok where both inputs are and `interC` ran within capacity. -/
def inter (R S : CRel A B) : CRel A B := guard (R.ok && S.ok) fun _ => ofC (interC R.rel S.rel)

/-- `R ∪ S`, ok where both inputs are and `unionC` ran within capacity. -/
def union (R S : CRel A B) : CRel A B := guard (R.ok && S.ok) fun _ => ofC (unionC R.rel S.rel)

end CRel
end LeetQ.Rel
end
