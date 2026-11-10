import LeetQ.Rel.Algebra

/-! The Wumpus world's knowledge base: a step appends to the percept tables, every other table is a view of them.
    A cell `[x,y]` is the long `10x + y`, and `∗`, the one value of the type `1`, is 0. -/

namespace LeetQ.Rel.Wumpus

open Alg QLean

abbrev LL := Rel .long .long
/-- The percept tables `V`, `B`, `S`, `G`, coreflexives on the cells: the only rows a step stores. -/
abbrev KB := LL × LL × LL × LL

def cor (xs : List Int64) : LL := ofPairs (xs.map fun x => (x, x))

def cellL : List Int64 := [11, 12, 13, 14, 21, 22, 23, 24, 31, 32, 33, 34, 41, 42, 43, 44]
/-- Codes differ by 1 along a column and by 10 along a row; `y ≤ 4` keeps two columns from differing by 1. -/
def near (a b : Int64) : Bool := [1, -1, 10, -10].contains (a - b)

/-- `uniq(R) ≜ R ∩ (R° \ 𝟙)`, the rows whose key has one value. The left universe is `R`'s own keys, because a key
    outside `R` would satisfy the division vacuously. -/
def uniq {m : Nat} (R : LL) (cells : Arr .long m) : Except String LL := do
  inter R (← leftDiv (← conv R) (idU cells) (← dom R).key cells)

/-- Every view, recomputed from the KB. `noWumpus` is the complement of `ran(wcand)`, not `noW`, because exactly one
    wumpus also clears each cell that `wmay` drops; `(S !) \ adj` ranges over all of `S`, unlike `S \ adj`. -/
def views {m : Nat} (cells : Arr .long m) (one : Arr .long 1) (adj : LL) (k : KB) :
    Except String (List (String × LL)) := do
  let (V, B, S, G) := k
  let noB ← antiJoin V B
  let noPit ← union V (← ran (← comp noB adj))
  let cand ← antiJoin (← comp B adj) noPit
  let pit ← ran (← uniq cand cells)
  let noS ← antiJoin V S
  let noW ← union V (← ran (← comp noS adj))
  let wmay ← leftDiv (← top S.key one) adj one cells
  let wcand ← antiJoin wmay noW
  let wumpus ← ran (← uniq wcand cells)
  let noWumpus ← antiJoin (idU cells) (← ran wcand)
  let safe ← inter noPit noWumpus
  let frontier ← antiJoin (← ran (← comp V adj)) V
  let next ← inter frontier safe
  pure [("V", V), ("B", B), ("S", S), ("G", G), ("noB", noB), ("noPit", noPit), ("cand", cand), ("pit", pit),
    ("noS", noS), ("noW", noW), ("wmay", wmay), ("wcand", wcand), ("wumpus", wumpus), ("noWumpus", noWumpus),
    ("safe", safe), ("frontier", frontier), ("next", next)]

/-- The percept step: `c` joins `V` and each table that fired. `∪` keeps one row per pair, so a revisit adds nothing. -/
def tell (k : KB) (c : Int64) (p : Bool × Bool × Bool) : Except String KB := do
  let (V, B, S, G) := k
  let d := cor [c]
  let add (X : LL) (f : Bool) : Except String LL := if f then union X d else pure X
  pure (← union V d, ← add B p.1, ← add S p.2.1, ← add G p.2.2)

/-- A world's percept at `c`: breeze beside a pit, stench beside the wumpus, glitter on the gold. -/
def world (pits : List Int64) (w g c : Int64) : Bool × Bool × Bool := (pits.any (near c), near c w, c == g)

/-- The agent walks a supplied route through a world, so a step back to a visited cell needs no choice among `next`;
    the result is every view after each step. -/
def agent (see : Int64 → Bool × Bool × Bool) (route : List Int64) : Except String (List (List (String × LL))) := do
  let cells := col cellL
  let one := col [0]
  let adj := ofPairs (cellL.flatMap fun a => (cellL.filter (near a)).map (a, ·))
  let e := cor []
  let mut k : KB := (e, e, e, e)
  let mut out := #[]
  for c in route do
    k ← tell k c (see c)
    out := out.push (← views cells one adj k)
  pure out.toList

section Checks

private def see := world [31, 33, 44] 13 23
private def route : List Int64 := [11, 21, 11, 12, 22, 23]

-- row order is not part of a table, so rows compare sorted
private def showT (X : LL) : String :=
  let rows := X.toList.map fun (a, b) => if a == b then s!"{a}" else s!"{a}:{b}"
  " ".intercalate (rows.mergeSort fun a b => !decide (b < a))
private def showS (t : List (String × LL)) : String :=
  "; ".intercalate (t.filterMap fun (n, X) => if X.n == 0 then none else some s!"{n} {showT X}")

-- the design page's non-empty tables after each step, a coreflexive's row as its one cell
private def page : List String := [
  "V 11; noB 11; noPit 11 12 21; noS 11; noW 11 12 21; wmay 0:11 0:12 0:13 0:14 0:21 0:22 0:23 0:24 0:31 \
   0:32 0:33 0:34 0:41 0:42 0:43 0:44; wcand 0:13 0:14 0:22 0:23 0:24 0:31 0:32 0:33 0:34 0:41 0:42 0:43 \
   0:44; noWumpus 11 12 21; safe 11 12 21; frontier 12 21; next 12 21",
  "V 11 21; B 21; noB 11; noPit 11 12 21; cand 21:22 21:31; noS 11 21; noW 11 12 21 22 31; wmay 0:11 0:12 \
   0:13 0:14 0:21 0:22 0:23 0:24 0:31 0:32 0:33 0:34 0:41 0:42 0:43 0:44; wcand 0:13 0:14 0:23 0:24 0:32 \
   0:33 0:34 0:41 0:42 0:43 0:44; noWumpus 11 12 21 22 31; safe 11 12 21; frontier 12 22 31; next 12",
  "V 11 21; B 21; noB 11; noPit 11 12 21; cand 21:22 21:31; noS 11 21; noW 11 12 21 22 31; wmay 0:11 0:12 \
   0:13 0:14 0:21 0:22 0:23 0:24 0:31 0:32 0:33 0:34 0:41 0:42 0:43 0:44; wcand 0:13 0:14 0:23 0:24 0:32 \
   0:33 0:34 0:41 0:42 0:43 0:44; noWumpus 11 12 21 22 31; safe 11 12 21; frontier 12 22 31; next 12",
  "V 11 12 21; B 21; S 12; noB 11 12; noPit 11 12 13 21 22; cand 21:31; pit 31; noS 11 21; noW 11 12 21 22 \
   31; wmay 0:11 0:13 0:22; wcand 0:13; wumpus 13; noWumpus 11 12 14 21 22 23 24 31 32 33 34 41 42 43 44; \
   safe 11 12 21 22; frontier 13 22 31; next 22",
  "V 11 12 21 22; B 21; S 12; noB 11 12 22; noPit 11 12 13 21 22 23 32; cand 21:31; pit 31; noS 11 21 22; \
   noW 11 12 21 22 23 31 32; wmay 0:11 0:13 0:22; wcand 0:13; wumpus 13; noWumpus 11 12 14 21 22 23 24 31 32 \
   33 34 41 42 43 44; safe 11 12 21 22 23 32; frontier 13 23 31 32; next 23 32",
  "V 11 12 21 22 23; B 21 23; S 12 23; G 23; noB 11 12 22; noPit 11 12 13 21 22 23 32; cand 21:31 23:24 \
   23:33; pit 31; noS 11 21 22; noW 11 12 21 22 23 31 32; wmay 0:13 0:22; wcand 0:13; wumpus 13; noWumpus 11 \
   12 14 21 22 23 24 31 32 33 34 41 42 43 44; safe 11 12 21 22 23 32; frontier 13 24 31 32 33; next 32"]

#guard (agent see route).toOption.map (·.map showS) == some page

/-- The literals true in every world that agrees with each prefix of the route. A percept splits into a breeze on the
    pits and a stench on the wumpus, so the worlds left are the product of `ms` and `ws`, and the agent lived at `c`. -/
private def entailed : List (List (String × List Int64)) := Id.run do
  let off := cellL.erase 11
  let mut ms : List (List Int64) := off.foldr (fun c ms => ms ++ ms.map (c :: ·)) [[]]
  let mut ws := off
  let mut out := #[]
  for c in route do
    ms := ms.filter fun m => !m.contains c && (world m 0 0 c).1 == (see c).1
    ws := ws.filter fun w => w != c && (world [] w 0 c).2.1 == (see c).2.1
    out := out.push [("pit", cellL.filter fun x => ms.all (·.contains x)),
      ("noPit", cellL.filter fun x => ms.all (!·.contains x)), ("wumpus", cellL.filter fun x => ws.all (· == x)),
      ("noWumpus", cellL.filter fun x => !ws.contains x)]
  pure out.toList

#guard (agent see route).toOption.any fun ts => ts.length == entailed.length && (ts.zip entailed).all fun (t, e) =>
  e.all fun (n, l) => (t.lookup n).map showT == some (" ".intercalate (l.map toString))

end Checks

#print axioms agent

end LeetQ.Rel.Wumpus
