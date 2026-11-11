import LeetQ.Rel.Lang.Test
import LeetQ.Rel.Wumpus

/-! The Rel language on the Wumpus world, read from `programs/wumpus.rel`: every view of the KB after each step of
    the route, against `Wumpus.agent` and against the literal tables `Wumpus.lean` states. -/

namespace LeetQ.Rel.Lang.TestWumpus

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Lang.Test LeetQ.Rel.Alg QLean

def wumpus : String := program_file "../../../programs/wumpus.rel"

/-- Each table: its name, the program's term for it, and whether its key is `∗ : 1` rather than a cell. -/
def tables : List (String × String × Bool) := [("V", "V", false), ("B", "B", false), ("S", "S", false),
  ("G", "G", false), ("noB", "noB(V,B)", false), ("noPit", "noPit(V,B)", false), ("cand", "cand(V,B)", false),
  ("pit", "pit(V,B)", false), ("noS", "noS(V,S)", false), ("noW", "noW(V,S)", false), ("wmay", "wmay(S)", true),
  ("wcand", "wcand(V,S)", true), ("wumpus", "wumpus(V,S)", false), ("noWumpus", "noWumpus(V,S)", false),
  ("safe", "safe(V,B,S)", false), ("frontier", "frontier(V)", false), ("next", "next(V,B,S)", false)]

/-- The program with one family `fₖ ≜ …` per table: `fₖ : N ⟶ C×C`, or `N ⟶ 1×C`. -/
def given : Except Err Out :=
  runText (wumpus ++ String.join (tables.zipIdx.map fun ((_, e, one), k) =>
    s!"f{k} : N ⟶ {if one then "1" else "C"}×C ≜ {e}\n"))

/-- A cell's code in `Wumpus.lean`: the element at its position among `C`'s named elements. -/
def cell (x : Int64) : Int64 := Wumpus.cellL.getD x.toInt.toNat 0

/-- The table `k` at step `i`, its cells coded as `Wumpus.lean` codes them. -/
def at? (o : Out) (k i : Nat) : Option Wumpus.LL := do
  let (_, _, one) ← tables[k]?
  let R ← get o s!"f{k}" .long XX
  pure (ofPairs ((R.toList.filter (·.1 == Int64.ofNat i)).map fun (_, a, b) => (if one then a else cell a, cell b))).nub

/-- The program's views after each step, as `Wumpus.views` lists them. -/
def views (o : Out) : List (List (String × Wumpus.LL)) :=
  (List.range 6).map fun i => tables.zipIdx.filterMap fun ((n, _, _), k) => (at? o k i).map (n, ·)

def see := Wumpus.world [31, 33, 44] 13 23
def route : List Int64 := [11, 21, 11, 12, 22, 23]

#guard given.isOk
-- the first `#guard` of `Wumpus.lean`: every table after every step, as sets, against the Lean views
#guard (views (ok given)).length == 6
#guard ((views (ok given)).zip (Wumpus.agent see route)).all fun (t, l) =>
  t.length == tables.length && (t.zip l).all fun ((n, R), (m, S)) => n == m && R == S

-- row order is not part of a table, so rows compare sorted (as `Wumpus.lean` prints them)
def showT (X : Wumpus.LL) : String :=
  let rows := X.toList.map fun (a, b) => if a == b then s!"{a}" else s!"{a}:{b}"
  " ".intercalate (rows.mergeSort fun a b => !decide (b < a))
def showS (t : List (String × Wumpus.LL)) : String :=
  "; ".intercalate (t.filterMap fun (n, X) => if X.n == 0 then none else some s!"{n} {showT X}")

-- the design page's non-empty tables after each step, as `Wumpus.lean` states them
def page : List String := [
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

#guard (views (ok given)).map showS == page

/-- The literals true in every world that agrees with each prefix of the route, as `Wumpus.lean` computes them
    (there `private`): the worlds left are the product of the pit sets `ms` and the wumpus cells `ws`. -/
def entailed : List (List (String × List Int64)) := Id.run do
  let off := Wumpus.cellL.erase 11
  let mut ms : List (List Int64) := off.foldr (fun c ms => ms ++ ms.map (c :: ·)) [[]]
  let mut ws := off
  let mut out := #[]
  for c in route do
    ms := ms.filter fun m => !m.contains c && (Wumpus.world m 0 0 c).1 == (see c).1
    ws := ws.filter fun w => w != c && (Wumpus.world [] w 0 c).2.1 == (see c).2.1
    out := out.push [("pit", Wumpus.cellL.filter fun x => ms.all (·.contains x)),
      ("noPit", Wumpus.cellL.filter fun x => ms.all (!·.contains x)),
      ("wumpus", Wumpus.cellL.filter fun x => ws.all (· == x)),
      ("noWumpus", Wumpus.cellL.filter fun x => !ws.contains x)]
  pure out.toList

-- the second `#guard` of `Wumpus.lean`: `pit`, `noPit`, `wumpus`, `noWumpus` are exactly the entailed literals
#guard views (ok given) |> fun ts => ts.length == entailed.length && (ts.zip entailed).all fun (t, e) =>
  e.all fun (n, l) => (t.lookup n).map showT == some (" ".intercalate (l.map toString))

-- the program's own `print`
#guard (ok given).prints == ["next(V, B, S) = {(0, (12, 12)), (0, (21, 21)), (1, (12, 12)), (2, (12, 12)), " ++
  "(3, (22, 22)), (4, (23, 23)), (4, (32, 32)), (5, (32, 32))}"]

/-! The parser on each line of `wumpus.rel`: every composite and infix term in parentheses (§c). -/

#guard match Parse.parse wumpus with
  | .error _ => false
  | .ok p => ((p.filterMap reading).drop 1).take 15 == [
    ("adj", "(a ∪ a°)"),
    ("uniq", "(R ∩ (R° \\ 𝟙))"),
    ("noB", "(V (𝟙 − B))"),
    ("noPit", "(V ∪ ran((noB(V, B) adj)))"),
    ("cand", "((B adj) (𝟙 − noPit(V, B)))"),
    ("pit", "ran(uniq(cand(V, B)))"),
    ("noS", "(V (𝟙 − S))"),
    ("noW", "(V ∪ ran((noS(V, S) adj)))"),
    ("wmay", "((S ⊤) \\ adj)"),
    ("wcand", "(wmay(S) (𝟙 − noW(V, S)))"),
    ("wumpus", "ran(uniq(wcand(V, S)))"),
    ("noWumpus", "(𝟙 − ran(wcand(V, S)))"),
    ("safe", "(noPit(V, B) ∩ noWumpus(V, S))"),
    ("frontier", "(ran((V adj)) (𝟙 − V))"),
    ("next", "(frontier(V) ∩ safe(V, B, S))")]

end LeetQ.Rel.Lang.TestWumpus
