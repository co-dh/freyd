import LeetQ.Rel.Lang.Test
import LeetQ.Rel.Programs.Edit

/-! The Rel language on B&dM's string edit (§9.2), the program `Programs.edit`: the specification
    `Λ(edit°) est(R)` on every pair of strings of length ≤ 2 over `{a,b}`, its least lengths against the
    edit-distance recursion on `List` below. -/

namespace LeetQ.Rel.Lang.TestEdit

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Lang.Test

/-- The least length of an edit sequence of `(xs, ys)`, each of `cpy`, `del`, `ins` costing one: every
    operation that applies at the heads, the cheapest rest taken. A copy is one choice among three, not
    taken greedily, so this does not assume the note's derivation. -/
def cost : List Char → List Char → Nat
  | [], ys => ys.length
  | xs, [] => xs.length
  | a :: xs, b :: ys =>
    let d := 1 + min (cost xs (b :: ys)) (cost (a :: xs) ys)
    if a = b then min d (1 + cost xs ys) else d

/-- The strings of length ≤ 2 over `{a,b}`. -/
def strs : List (List Char) := [[]] ++ [['a'], ['b']] ++ [['a','a'], ['a','b'], ['b','a'], ['b','b']]

def word (s : List Char) : String := arrText false (s.map toString)

/-- `spec length 𝟙(N)` as the printer writes it, its rows in the printer's order: by element (`Eval.cmpEl`),
    an array lexicographically with a prefix first, which on strings is the order of `String`. -/
def expected (term : String) : String :=
  let key (p : List Char × List Char) := (String.ofList p.1, String.ofList p.2)
  let ps := (strs.flatMap fun x => strs.map (x, ·)).mergeSort fun p q =>
    (key p).1 < (key q).1 || ((key p).1 == (key q).1 && (key p).2 ≤ (key q).2)
  s!"{term} = \{" ++ ", ".intercalate (ps.map fun (x, y) => s!"(({word x}, {word y}), {cost x y})") ++ "}"

def given : Except Err Out := runProgram Programs.edit

#guard given.isOk
#guard (ok given).prints.head? == some (expected "spec length 𝟙(N)")
-- the second `print`, the shortest sequences of the pairs of two-letter strings, is for reading only
#guard (ok given).prints.length == 2
-- the tabulation: the program's `check D mle ⊑ spec` and `check D mle length 𝟙(N) = (spec length 𝟙(N))` hold (a failed
-- one is an error), and `mle`'s lengths printed here are the edit-distance recursion's, on the same 49 pairs
#guard (ok (runExt Programs.edit "print D mle length 𝟙(N)\n")).prints.getLast? == some (expected "D mle length 𝟙(N)")

end LeetQ.Rel.Lang.TestEdit
