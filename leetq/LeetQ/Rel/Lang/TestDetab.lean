import LeetQ.Rel.Lang.Test
import LeetQ.Rel.Programs.Detab

/-! The Rel language on B&dM §10.2 detab-entab, the program `Programs.detab`: `detab`, the specification
    `Λ(H)est(R)` (`H` = `detab°` on the candidates) and the derived program `entab`, against a direct `detab` on
    lists and a brute-force shortest preimage. -/

namespace LeetQ.Rel.Lang.TestDetab

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Lang.Test

/-- The tab width, the program's `m`. -/
def n : Nat := 4

/-- The column a string ends at: the characters since the last `NL`. -/
def col (xs : List String) : Nat := (xs.reverse.takeWhile (· ≠ "NL")).length

/-- `detab`, character by character from the left: a tab pads with blanks to the next multiple of `n`. -/
def detabL (xs : List String) : List String :=
  xs.foldl (fun out c => if c = "TB" then out ++ List.replicate (n - col out % n) "BL" else out ++ [c]) []

/-- Every string of length at most `k` over the characters `cs`. -/
def strings (cs : List String) : Nat → List (List String)
  | 0 => [[]]
  | k + 1 => [] :: (strings cs k).flatMap fun s => cs.map (s ++ [·])

/-- The shortest strings `detabL` takes to `y`, by trying every string no longer than `y` over `y`'s characters
    and the tab: `detab` never shortens and copies every character but the tab. -/
def shortest (y : List String) : List (List String) :=
  let ps := (strings (("TB" :: y).eraseDups) y.length).filter (detabL · == y)
  let k := (ps.map List.length).foldl min y.length
  ps.filter (·.length == k)

/-- A relation `1 ⟶ [Ch]` holding the strings `ss`, as the interpreter prints it (rows in `cmpEl`'s order: an
    array lexicographically by element name, a prefix first). -/
def shown (ss : List (List String)) : String :=
  "{" ++ ", ".intercalate ((ss.mergeSort fun a b => decide (a ≤ b)).map fun s => "(∗, " ++ arrText false s ++ ")") ++
    "}"

def x : List String := ["a", "b", "TB", "c", "BL", "d"]
def inputs : List (String × List String) :=
  [("p", ["a", "BL", "BL", "BL"]), ("q", ["a", "a", "a", "BL", "a"]), ("y", List.replicate 5 "BL")]

/-- The program's eight `check`s turned back into `print`s, one per line, so the values compared are Lean's below. -/
def asPrints : List String := ["x detab", "x detab entab", "p Λ(H)est(R)", "q Λ(H)est(R)", "y Λ(H)est(R)", "p entab",
  "q entab", "y entab"]

def out : Out := ok (runExt Programs.detab (String.join (asPrints.map fun e => s!"print {e}\n")))

-- every `check` holds (a failed one is an error), including entab ⊑ the specification and detab entab = 𝟙, on D;
-- the program prints nothing itself
#guard (runProgram Programs.detab).isOk
#guard (ok (runProgram Programs.detab)).prints == []
#guard out.prints.length == 8
-- the note's run: detab of ab, a tab, c d
#guard out.prints[0]! == s!"x detab = {shown [detabL x]}"
-- the specification is every shortest preimage; q has two
#guard (out.prints.drop 2).take 3 == inputs.map fun (v, y) => s!"{v} Λ(H) est(R) = {shown (shortest y)}"
#guard (shortest (inputs[1]!).2).length == 2
-- the program gives one shortest preimage
#guard (shortest (detabL x)).any fun s => out.prints[1]! == s!"x detab entab = {shown [s]}"
#guard (out.prints.drop 5).zip inputs |>.all fun (l, v, y) => (shortest y).any fun s => l == s!"{v} entab = {shown [s]}"

end LeetQ.Rel.Lang.TestDetab
