import LeetQ.Rel.Lang.Test
import LeetQ.Rel.Programs.Wumpus

/-! The Rel language on the Wumpus world, the program `Programs.wumpus`: every view of the KB after each step
    of the route, against the literal tables of the design page. -/

namespace LeetQ.Rel.Lang.TestWumpus

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Lang.Test LeetQ.Rel.Alg QLean

/-- Each table: its name, the program's term for it, and whether its key is `∗ : 1` rather than a cell. -/
def tables : List (String × String × Bool) := [("V", "V", false), ("B", "B", false), ("S", "S", false),
  ("G", "G", false), ("noB", "noB(V,B)", false), ("noPit", "noPit(V,B)", false), ("cand", "cand(V,B)", false),
  ("pit", "pit(V,B)", false), ("noS", "noS(V,S)", false), ("noW", "noW(V,S)", false), ("wmay", "wmay(S)", true),
  ("wcand", "wcand(V,S)", true), ("wumpus", "wumpus(V,S)", false), ("noWumpus", "noWumpus(V,S)", false),
  ("safe", "safe(V,B,S)", false), ("frontier", "frontier(V)", false), ("next", "next(V,B,S)", false)]

/-- The program with one family `fₖ ≜ …` per table: `fₖ : N ⟶ C×C`, or `N ⟶ 1×C`. -/
def given : Except Err Out :=
  runExt Programs.wumpus (String.join (tables.zipIdx.map fun ((_, e, one), k) =>
    s!"f{k} : N ⟶ {if one then "1" else "C"}×C ≜ {e}\n"))

/-- A cell's code `10x + y`: the element at its position among `C`'s named elements. -/
def cell (x : Int64) : Int64 :=
  ([11, 12, 13, 14, 21, 22, 23, 24, 31, 32, 33, 34, 41, 42, 43, 44] : List Int64).getD x.toInt.toNat 0

/-- The table `k` at step `i`, its cells coded `10x + y`. -/
def at? (o : Out) (k i : Nat) : Option (Rel .long .long) := do
  let (_, _, one) ← tables[k]?
  let R ← get o s!"f{k}" .long XX
  pure (ofPairs ((R.toList.filter (·.1 == Int64.ofNat i)).map fun (_, a, b) => (if one then a else cell a, cell b))).nub

/-- The program's views after each step. -/
def views (o : Out) : List (List (String × Rel .long .long)) :=
  (List.range 6).map fun i => tables.zipIdx.filterMap fun ((n, _, _), k) => (at? o k i).map (n, ·)

#guard given.isOk
#guard (views (ok given)).length == 6 && (views (ok given)).all (·.length == tables.length)

-- row order is not part of a table, so rows compare sorted
def showT (X : Rel .long .long) : String :=
  let rows := X.toList.map fun (a, b) => if a == b then s!"{a}" else s!"{a}:{b}"
  " ".intercalate (rows.mergeSort fun a b => !decide (b < a))
def showS (t : List (String × Rel .long .long)) : String :=
  "; ".intercalate (t.filterMap fun (n, X) => if X.n == 0 then none else some s!"{n} {showT X}")

-- the design page's non-empty tables after each step
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

-- the program's own `check next(V,B,S) = …` holds (a failed one is an error) and it prints nothing; printed here,
-- `next(V,B,S)` is the table `page` states
#guard (ok given).prints == []
#guard (ok (runExt Programs.wumpus "print next(V,B,S)\n")).prints == ["next(V, B, S) = {(0, (12, 12)), (0, (21, 21)), " ++
  "(1, (12, 12)), (2, (12, 12)), (3, (22, 22)), (4, (23, 23)), (4, (32, 32)), (5, (32, 32))}"]

/-! The parser on each line of `Programs.wumpus`: every composite and infix term in parentheses (§c). -/

#guard ((Programs.wumpus.filterMap reading).drop 1).take 15 == [
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
