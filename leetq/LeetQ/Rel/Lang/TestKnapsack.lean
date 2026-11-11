import LeetQ.Rel.Lang.Test

/-! The Rel language on B&dM's 0/1 knapsack (§8.4), read from `programs/knapsack.rel`: the specification `s` and
    its fold `p` against a brute force over `List.sublists` on the same items — the best value of each instance,
    and every printed packing within the capacity and of that value. -/

namespace LeetQ.Rel.Lang.TestKnapsack

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Lang.Test LeetQ.Rel.Alg QLean

def knapsack : String := include_str "../../../programs/knapsack.rel"

def given : Except Err Out := runText knapsack

/-- The instances of `X`, `K = {a,b,c,d}` coded `0 … 3`, each its items `(value, weight)`. -/
def items : List (Int64 × List (Int64 × Int64)) :=
  [(0, [(6,5),(5,4),(4,6),(3,3)]), (1, [(7,4),(2,2),(9,8)]), (2, [(1,9)]), (3, [(5,5),(5,6),(5,4)])]

def cap : Int64 := 10
def value (xs : List (Int64 × Int64)) : Int64 := (xs.map (·.1)).foldl (· + ·) 0
def weight (xs : List (Int64 × Int64)) : Int64 := (xs.map (·.2)).foldl (· + ·) 0

/-- Every sublist, each element kept or dropped (core has no `List.sublists`). -/
def sublists {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => let r := sublists xs; r.map (x :: ·) ++ r

/-- The best value of an instance: the greatest total value among its sublists within the capacity. -/
def best (xs : List (Int64 × Int64)) : Int64 :=
  (((sublists xs).filter (weight · ≤ cap)).map value).foldl max 0

/-- The packings `n` gives each instance. -/
def packs (o : Out) (n : String) : Option (List (Int64 × List (Int64 × Int64))) :=
  (get o n .long (.arr XX)).map (·.toList)

/-- Every instance has a packing, and every packing is a selection of its items, within the capacity, of the best
    value; the number of packings of each instance is the number of best sublists up to order. -/
def agrees (o : Out) (n : String) : Bool := match packs o n with
  | none => false
  | some ps => items.all fun (k, xs) =>
    let mine := (ps.filter (·.1 == k)).map (·.2)
    let bestL : List (List (Int64 × Int64)) :=
      ((sublists xs).filter fun ys => weight ys ≤ cap && value ys == best xs).map (·.mergeSort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2))
    !mine.isEmpty && mine.all (fun ys => weight ys ≤ cap && value ys == best xs && ys.all xs.contains) &&
      mine.length == bestL.eraseDups.length

#guard given.isOk
#guard items.map (best ·.2) == [11, 11, 1, 10]
#guard agrees (ok given) "s"
#guard agrees (ok given) "p"
-- instance d has two best packings: the specification is a relation
#guard (((packs (ok given) "s").getD []).filter (·.1 == 3)).length == 2
-- the derived program: one best packing of each instance, among the specification's
#guard ((packs (ok given) "knap").getD []).map (·.1) == [0, 1, 2, 3]
#guard ((packs (ok given) "knap").getD []).all ((packs (ok given) "s").getD []).contains
-- the program's own `print`s
#guard (ok given).prints == [
  "s = {(a, (5, 4) (6, 5)), (b, (2, 2) (9, 8)), (c, [(1, 9)]), (d, (5, 4) (5, 5)), (d, (5, 4) (5, 6))}",
  "p = {(a, (5, 4) (6, 5)), (b, (2, 2) (9, 8)), (c, [(1, 9)]), (d, (5, 4) (5, 5)), (d, (5, 4) (5, 6))}",
  "knap = {(a, (5, 4) (6, 5)), (b, (2, 2) (9, 8)), (c, [(1, 9)]), (d, (5, 4) (5, 5))}"]
-- a `check` that fails is an error: the guards above would not see a silently skipped one
#guard !(runText (knapsack ++ "check p = X subseq\n")).isOk

end LeetQ.Rel.Lang.TestKnapsack
