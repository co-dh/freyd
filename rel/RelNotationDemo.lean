/-
  Four `.ralg` conversions, now as PROVABLE `rel⟦…⟧` Lean terms — one per relational "type".
  Each carries a THEOREM the matching `rel/examples/*.ralg` file could only print at runtime:
  an instance fact is a `by decide` theorem (not `IO.println`), and a law is proved GENERICALLY
  (all instances at once) through the allegory instances — which no external `.ralg` file can state.
-/
import rel.RelNotation
import rel.RelInterpDemo   -- the demo fixtures (DemoDivision / Demo121 / Demo207) used below

namespace Freyd.Alg.FinRel.Demo
open Freyd.Alg.FinRel

/-! ## Type 1 — CONVERSE.  LeetCode 206 Reverse Linked List (cf. rel/examples/L206.ralg).
    A singly linked list IS its successor relation; reversing it IS the converse `°`. -/

abbrev Node : FinObj := ⟨5⟩
/-- the list 0→1→2→3→4, as its successor relation. -/
def nextFn : Fin 5 → Fin 5 → Bool := fun i j => j.val == i.val + 1
def nextE : RE Node Node := .atom nextFn

/-- INSTANCE fact (a theorem, not printed): in the reversed list `next°`, node 4 points to node 3. -/
example : eval rel⟦ nextE° ⟧ 4 3 = true := by decide
example : eval rel⟦ nextE° ⟧ 3 4 = false := by decide
/-- GENERIC law — reversing ANY list twice is the original (`rev_rev`), proved once for all instances. -/
example : eval rel⟦ nextE°° ⟧ = eval rel⟦ nextE ⟧ := Allegory.recip_recip (eval nextE)

/-! ## Type 2 — DIVISION / for-all.  Students who solved a SUPERSET of another's problems
    (the classic division query; same "∀" shape as LeetCode 100 same-tree / 98 valid-BST).
    cf. rel/examples/division.ralg, L100.ralg. -/

open DemoDivision in
example : eval rel⟦ solvedE / solvedE ⟧ 3 0 = true := by decide   -- student 3 solved ⊇ student 0
open DemoDivision in
example : eval rel⟦ solvedE / solvedE ⟧ 2 0 = false := by decide  -- student 2 did not

/-! ## Type 3 — REACHABILITY / closure (join + comp).  LeetCode 322-style state graph
    (cf. rel/examples/L322_dp.ralg): 1-or-2-step reach is `edge ∪ (edge ≫ edge)`. -/

abbrev Nd : FinObj := ⟨4⟩
/-- the path 0→1→2→3. -/
def edgeFn : Fin 4 → Fin 4 → Bool :=
  fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 2) || (i.val == 2 && j.val == 3)
def edgeE : RE Nd Nd := .atom edgeFn

/-- node 0 reaches node 2 in ≤ 2 steps … -/
example : eval rel⟦ edgeE ∪ (edgeE ≫ edgeE) ⟧ 0 2 = true := by decide
/-- … but not node 3 (that needs 3 steps). -/
example : eval rel⟦ edgeE ∪ (edgeE ≫ edgeE) ⟧ 0 3 = false := by decide

/-! ## Type 4 — COREFLEXIVE FUSION.  `grep p ≫ grep q = grep (p ∩ q)` (the S2_1 allegory law),
    here on two partial-identity filters (cf. rel/examples/shell.ralg's grep-fusion). -/

/-- filter keeping {0,2}. -/
def txtE : RE Nd Nd := .atom (fun i j => (i == j) && (i.val == 0 || i.val == 2))
/-- filter keeping {0,1}. -/
def bigE : RE Nd Nd := .atom (fun i j => (i == j) && (i.val == 0 || i.val == 1))

/-- fusion holds as a theorem: composing the two filters = meeting them (both survive only {0}). -/
example :
    (List.ofFn fun i : Fin 4 => List.ofFn fun j : Fin 4 => eval rel⟦ txtE ≫ bigE ⟧ i j)
      = (List.ofFn fun i : Fin 4 => List.ofFn fun j : Fin 4 => eval rel⟦ txtE ∩ bigE ⟧ i j) := by
  decide

/-! ## Notation instance examples that use the moved fixtures (relocated from `RelNotation`). -/

-- the division query, in surface syntax, by `decide` (the classic `solved / solved`).
open DemoDivision in
example : (List.ofFn fun s : Fin 4 => eval rel⟦ solvedE / solvedE ⟧ s 0)
    = [true, true, false, true] := by decide

-- the LC121 spec shape in surface syntax = the certified `solveE` term, definitionally.
open Demo121 in
example {n M : Nat} (price : Fin n → Int) :
    eval rel⟦ Λ(!(RE.atom (specFn n M price))) ≫ est(!(RE.atom (geFn M))) ⟧
      = eval (solveE n M price) := rfl

-- id/eps in surface syntax (objects are named Lean constants).  `Demo207.edgeFn` is qualified
-- because this file's namespace already defines a local `edgeFn`.
example : eval rel⟦ eps(Demo207.Course) ⟧ = epsB Demo207.Course := rfl
example :
    eval rel⟦ !(Demo207.reachE (.atom (Demo207.edgeFn [(0,1)])) 3) ∩ id(Demo207.Course) ⟧
      = eval (.meet (Demo207.reachE (.atom (Demo207.edgeFn [(0,1)])) 3) (.id Demo207.Course)) := rfl

end Freyd.Alg.FinRel.Demo
