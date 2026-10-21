/-
  A q container is a span `K ←κ— ℕ —ν→ V` over the positions `0 … n-1`:
  * a list `xs`: `κ` the position itself, `ν = ix(xs)`;
  * a dict `k!v`: `κ = ix(k)`, `ν = ix(v)`;
  * a table: a list of rows, `ν : ℕ → row`, a column `ν ≫ π_c`;
  * a keyed table: a dict of rows, `κ` the key rows, `ν` the value rows.
  A verb acts on the apex `ℕ`, so one definition serves every container.
-/
import LeetQ.Rel.Basis

namespace LeetQ.Rel

open Freyd.Alg.RelSet (RelRep RelTest)
open scoped Freyd.Alg.RelSet.RelRep

/-- The key leg: the position itself (a list, a table) or a relation `κ : ℕ ⇸ K` (a dict, a keyed table).
    A position key is not stored, so a reindexing leaves it the new position, as q renumbers a list. -/
inductive Keys (K : Type) where
  | pos (h : Nat = K)
  | rel (κ : RelRep Nat K)

/-- A q container: the span `K ←κ— ℕ —ν→ V` over the positions `0 … n-1`; a position with an empty
    `ν`-fibre is null. -/
structure Q (K V : Type) where
  n : Nat
  keys : Keys K
  ν : RelRep Nat V

variable {K V W X : Type} [DecidableEq K] [DecidableEq V] [DecidableEq W] [DecidableEq X]

/-- The key relation `κ : ℕ ⇸ K`; a position key is the identity. -/
def Keys.κ : Keys K → RelRep Nat K
  | .pos h => .ofFn (cast h)
  | .rel κ => κ

/-- The keys after the apex is reindexed by `G`: a position key stays the position. -/
def Keys.pull (G : RelRep Nat Nat) : Keys K → Keys K
  | .pos h => .pos h
  | .rel κ => .rel (G ≫ κ)

/-- A list. -/
def list (xs : List V) : Q Nat V := ⟨xs.length, .pos rfl, ix xs⟩

/-- A list with nulls: a null is a position with no value. -/
def listN (xs : List (Option V)) : Q Nat V := ⟨xs.length, .pos rfl, ix xs ≫ .enum Option.toList⟩

/-- A dict `ks!vs`; a keyed table is a dict of rows. -/
def dict (ks : List K) (vs : List V) : Q K V := ⟨vs.length, .rel (ix ks), ix vs⟩

/-- The fibre at the point `0` of a relation, as a list: how a selection is renumbered. -/
def ofPt (R : RelRep Nat V) : Q Nat V := list (R.app 0)

namespace Q

/-- `κ : ℕ ⇸ K`. -/
abbrev κ (C : Q K V) : RelRep Nat K := C.keys.κ

/-- The values, in position order.  Read through `withApp`, so a `pairs` leg's fibre index is built once: passed
    as `C.ν.app`, the compiled `flatMap` calls `app` at each position and rebuilds it there. -/
def vals (C : Q K V) : List V := C.ν.withApp fun f => (List.range C.n).flatMap f

/-- The values with nulls. -/
def valsN (C : Q K V) : List (Option V) := C.ν.withApp fun f => (List.range C.n).map fun i => (f i).head?

/-- The keys, in position order. -/
def keyList (C : Q K V) : List K := C.κ.withApp fun f => (List.range C.n).flatMap f

/-- The same keys, a new value leg. -/
def put (C : Q K V) (R : RelRep Nat W) : Q K W := ⟨C.n, C.keys, R⟩

/-- Reindex the apex by `G : ℕ ⇸ ℕ` onto `0 … m-1`: both legs follow. -/
def pull (m : Nat) (G : RelRep Nat Nat) (C : Q K V) : Q K V := ⟨m, C.keys.pull G, G ≫ C.ν⟩

/-- The positions in `dom P`, renumbered: `C[where P]`. -/
def sel (C : Q K V) (P : RelRep Nat X) : Q K V := let ps := (top C.n ≫ P.dom).app 0; C.pull ps.length (ix ps)

end Q

end LeetQ.Rel
