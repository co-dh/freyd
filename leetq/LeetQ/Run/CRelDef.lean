import LeetQ.Run.Alg
import LeetQ.Run.Core

section
namespace LeetQ.Rel

/-- A relation and whether every op that built it ran within capacity. -/
structure CRel (k v : Obj) where
  rel : Rel k v
  ok : Bool

end LeetQ.Rel
end

section
namespace LeetQ.Rel
namespace CRel
open QLean QLean.Kernel LeetQ.Rel.Alg
variable {A B C : Obj}

/-- A stopped run: `𝟘`, its bit false. -/
instance : Inhabited (CRel A B) := ⟨⟨default, false⟩⟩

/-- Runs the op `k` only where its inputs' bits `b` are all set; otherwise stops at `default` (`𝟘`, bit false)
    without running it, since an op on a bad input answers nothing worth its cost. -/
def guard {α : Type} [Inhabited α] (b : Bool) (k : Unit → α) : α := if b then k () else default

/-- `R ≫ S`, ok where both inputs are and `compC` ran within capacity. -/
def comp (R : CRel A B) (S : CRel B C) : CRel A C := guard (R.ok && S.ok) fun _ => let r := compC R.rel S.rel; ⟨r.1, r.2⟩

/-- `R ∩ S`, ok where both inputs are and `interC` ran within capacity. -/
def inter (R S : CRel A B) : CRel A B := guard (R.ok && S.ok) fun _ => let r := interC R.rel S.rel; ⟨r.1, r.2⟩

/-- `R ∪ S`, ok where both inputs are and `unionC` ran within capacity. -/
def union (R S : CRel A B) : CRel A B := guard (R.ok && S.ok) fun _ => let r := unionC R.rel S.rel; ⟨r.1, r.2⟩

end CRel
end LeetQ.Rel
end
