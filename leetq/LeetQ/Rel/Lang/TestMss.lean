import LeetQ.Rel.Lang.Test
import LeetQ.Rel.Programs.Mss

/-! The Rel language on B&dM Ex 7.40, the maximum segment sum, the program `Programs.mss`: the
    specification `Λ(segment sum) est(≥)` and the derived fold `⦇k⦈ π₂ est(≥)`, each against a direct `List` computation. -/

namespace LeetQ.Rel.Lang.TestMss

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Lang.Test LeetQ.Rel.Alg QLean

/-- The program text of the derived fold, as `Programs.mss` writes it. -/
def prog : String := "⦇ran(zero⟨𝟙,Λ(𝟙)⟩), ⟨w,Λ(w ∪ (π₂π₂∋))⟩⦈π₂est(≥)"

/-- The program with the specification and the fold on every array of `A`, named `s` and `p`. -/
def given : Except Err Out := runExt Programs.mss s!"s : [N] ⟶ N ≜ A mss\np : [N] ⟶ N ≜ A{prog}\n"

/-- The largest sum over the segments `drop i` then `take j`, the empty one included: no `Rel` operation. -/
def mssL (xs : List Int64) : Int64 :=
  let n := xs.length
  ((List.range (n + 1)).flatMap fun i => (List.range (n + 1 - i)).map fun j =>
    ((xs.drop i).take j).foldl (· + ·) 0).foldl max 0

/-- The arrays over `{-2,-1,3}` of length at most 3, as `A` builds them. -/
def arrays : List (List Int64) :=
  (List.range 4).flatMap fun n => (List.range n).foldl (fun xss _ => xss.flatMap fun xs => [-2, -1, 3].map (· :: xs)) [[]]

/-- Equal as sets of rows: row order is not part of a relation. -/
def seteq (a b : List (List Int64 × Int64)) : Bool := a.all b.contains && b.all a.contains

#guard given.isOk
#guard arrays.length == 40
-- the specification and the fold on all 40 arrays, against `mssL`
#guard [("s"), ("p")].all fun n => match get (ok given) n (.arr .long) .long with
  | some R => R.toList.length == 40 && seteq R.toList (arrays.map fun xs => (xs, mssL xs))
  | none => false

-- the prints: `x` is `a ↦ [3,1,4,1,5]`, `b ↦ [2,0,7]`, `c ↦ []`, `d ↦ [3,-4,2,-1,2]`, `e ↦ [-2,-1,-3]`
def rows : String := s!"\{(a, {mssL [3,1,4,1,5]}), (b, {mssL [2,0,7]}), (c, {mssL []}), " ++
  s!"(d, {mssL [3,-4,2,-1,2]}), (e, {mssL [-2,-1,-3]})}"
-- a list with a negative element sums less than its best segment; an all-negative one has the empty segment's 0
#guard mssL [3,-4,2,-1,2] == 3 && mssL [-2,-1,-3] == 0
#guard (arrays.filter fun xs => mssL xs < (xs.foldl (· + ·) 0)).isEmpty &&
  (arrays.any fun xs => mssL xs > (xs.foldl (· + ·) 0))
-- the program's two `check`s hold (a failed one is an error) and print nothing; printed here, `x mss` and `x` then the
-- fold are the rows `mssL` computes
#guard (runProgram Programs.mss).isOk && (ok (runProgram Programs.mss)).prints == []
#guard (ok (runExt Programs.mss s!"print x mss\nprint x{prog}\n")).prints == [s!"x mss = {rows}",
  s!"x ⦇ran(zero ⟨𝟙, Λ(𝟙)⟩), ⟨w, Λ(w ∪ (π₂ π₂ ∋))⟩⦈ π₂ est(≥) = {rows}"]

end LeetQ.Rel.Lang.TestMss
