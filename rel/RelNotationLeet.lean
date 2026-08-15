/-
  Ten more LeetCode problems as PROVABLE `rel⟦…⟧` terms — one per relational structure.
  Each carries a theorem (a `by decide` instance fact, or a matrix-equality law that holds of the
  relation as written).  Contrast the `.ralg` files, which only print.  Atoms are small ground
  relations; the point is the STRUCTURE and that the answer is a theorem.
-/
import rel.RelNotation

namespace Freyd.Alg.FinRel.Leet
open Freyd.Alg.FinRel

/-! ### 1. L217 Contains Duplicate — EXISTENCE of an equal pair: `(e ≫ e°) ∩ lt`. -/
abbrev Pos217 : FinObj := ⟨4⟩
abbrev Val217 : FinObj := ⟨3⟩
-- nums = [1,2,3,1]: position ↦ value index.
def elem217 : RE Pos217 Val217 := .atom fun i j =>
  (i.val == 0 && j.val == 0) || (i.val == 1 && j.val == 1) ||
  (i.val == 2 && j.val == 2) || (i.val == 3 && j.val == 0)
def lt217 : RE Pos217 Pos217 := .atom fun i j => decide (i.val < j.val)
-- `(elem ≫ elem°) ∩ lt` relates i<j holding the SAME value — nonempty iff a duplicate exists.
example : eval rel⟦ (elem217 ≫ elem217°) ∩ lt217 ⟧ 0 3 = true  := by decide   -- nums[0]=nums[3]=1
example : eval rel⟦ (elem217 ≫ elem217°) ∩ lt217 ⟧ 1 2 = false := by decide

/-! ### 2. L1 Two Sum by CALCULATION — derive a FUNCTION from a relational SPEC.
    `specL1 : One → Ans` is the SPEC as a RELATION: input ↝ every valid answer-pair (the condition
    `nums i + nums j = target` is computed in the atom, from the real data).  The AoP construction
    `Λ(spec) ≫ max(le)` DERIVES a deterministic function from it — `Λ` transposes the spec to its
    answer-SET, `max(le)` selects one member.  The interpreter EVALUATES the derived term: it computes
    the answer FROM the spec, nothing supplied; and the derivation is PROVED correct (the function
    refines the spec, and is single-valued).  (Exponential spec side, `2^|Ans|` codes; the general
    derivation `solve = Λ spec ≫ maxRel D` for ARBITRARY inputs — via the thinning theorem, equal to
    the O(n) hash program — is `leet/L1.lean`.) -/
abbrev One1 : FinObj := ⟨1⟩
abbrev Ans1 : FinObj := ⟨6⟩   -- the 6 ordered index-pairs of positions [0..3]
def pairOf1 : Fin 6 → Nat × Nat
  | 0 => (0,1) | 1 => (0,2) | 2 => (0,3) | 3 => (1,2) | 4 => (1,3) | _ => (2,3)
def nums1   : Nat → Int | 0 => 2 | 1 => 7 | 2 => 11 | _ => 15
def target1 : Int := 9
-- THE SPEC (a relation, computed from the data), not an answer:
def specL1 : RE One1 Ans1 := .atom fun _ c => let p := pairOf1 c; decide (nums1 p.1 + nums1 p.2 = target1)
def leAns1 : RE Ans1 Ans1 := .atom fun i j => decide (i.val ≤ j.val)
-- DERIVE the function from the spec (the calculation): `solve = Λ(spec) ≫ max(le)`.
def solveL1 : RE One1 Ans1 := rel⟦ Λ(specL1) ≫ max(leAns1) ⟧
-- the interpreter COMPUTES the derived function's answer from the spec — prints [0] = pairOf 0 = (0,1):
#eval (List.finRange 6).filter fun c => eval solveL1 0 c
-- CALCULATION CORRECT: the derived function refines the spec — every answer it gives is valid …
example : ∀ c, eval solveL1 0 c = true → eval specL1 0 c = true := by decide
-- … and it is a FUNCTION: it selects at most one answer.
example : ∀ c c', eval solveL1 0 c = true → eval solveL1 0 c' = true → c = c' := by decide

/-! ### 3. L268 Missing Number — COMPLEMENT via division: `bot / present°` marks the absent value. -/
abbrev One268 : FinObj := ⟨1⟩
abbrev Num268 : FinObj := ⟨6⟩
def present268 : RE One268 Num268 := .atom fun _ j => j.val != 4   -- the set {0,1,2,3,5}
def bot268     : RE One268 One268 := .atom fun _ _ => false
-- `bot / present°` relates 0 to y iff (∀z, present° y z → false) = ¬present y = y is MISSING.
example : eval rel⟦ bot268 / present268° ⟧ 0 4 = true  := by decide
example : eval rel⟦ bot268 / present268° ⟧ 0 3 = false := by decide

/-! ### 4. L207 Course Schedule — CYCLE detection: `reach ∩ id` nonempty ⇔ a course reaches itself. -/
abbrev Course207 : FinObj := ⟨4⟩
def edge207 : RE Course207 Course207 := .atom fun i j =>
  (i.val==0 && j.val==1) || (i.val==1 && j.val==2) || (i.val==2 && j.val==3) || (i.val==3 && j.val==1)
-- the cycle 1→2→3→1 makes node 1 reach itself within 3 steps.
example :
    eval rel⟦ (edge207 ∪ (edge207 ≫ edge207) ∪ (edge207 ≫ edge207 ≫ edge207)) ∩ id(Course207) ⟧ 1 1
      = true := by decide
example :
    eval rel⟦ (edge207 ∪ (edge207 ≫ edge207) ∪ (edge207 ≫ edge207 ≫ edge207)) ∩ id(Course207) ⟧ 0 0
      = false := by decide

/-! ### 5. L55 Jump Game — REFLEXIVE-transitive reachability: `(id ∪ jump)^k`. -/
abbrev Pos55 : FinObj := ⟨5⟩
def nums55 : Nat → Nat | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 1 | _ => 4   -- [2,3,1,1,4]
def jump55 : RE Pos55 Pos55 := .atom fun i j =>
  decide (i.val < j.val) && decide (j.val - i.val ≤ nums55 i.val)
example :
    eval rel⟦ (id(Pos55) ∪ jump55) ≫ (id(Pos55) ∪ jump55) ≫ (id(Pos55) ∪ jump55) ≫ (id(Pos55) ∪ jump55) ⟧ 0 4
      = true := by decide   -- the last index is reachable

/-! ### 6. L190 Reverse Bits — INVOLUTION: `rev ≫ rev = id`, and `rev° = rev` (matrix laws). -/
abbrev Bit190 : FinObj := ⟨6⟩
def rev190 : RE Bit190 Bit190 := .atom fun i j => decide (j.val = 5 - i.val)
example : (List.ofFn fun i : Fin 6 => List.ofFn fun j : Fin 6 => eval rel⟦ rev190 ≫ rev190 ⟧ i j)
        = (List.ofFn fun i : Fin 6 => List.ofFn fun j : Fin 6 => eval rel⟦ id(Bit190) ⟧ i j) := by decide
example : (List.ofFn fun i : Fin 6 => List.ofFn fun j : Fin 6 => eval rel⟦ rev190° ⟧ i j)
        = (List.ofFn fun i : Fin 6 => List.ofFn fun j : Fin 6 => eval rel⟦ rev190 ⟧ i j) := by decide

/-! ### 7. L205 Isomorphic Strings — single-valued MAP: `m° ≫ m = id` (the mapping is a bijection). -/
abbrev SC205 : FinObj := ⟨2⟩
abbrev TC205 : FinObj := ⟨2⟩
def m205 : RE SC205 TC205 := .atom fun i j => i.val == j.val   -- e↦a, g↦d
example : (List.ofFn fun i : Fin 2 => List.ofFn fun j : Fin 2 => eval rel⟦ m205° ≫ m205 ⟧ i j)
        = (List.ofFn fun i : Fin 2 => List.ofFn fun j : Fin 2 => eval rel⟦ id(TC205) ⟧ i j) := by decide

/-! ### 8. L392 Is Subsequence — ORDERED composition chain: `matchA ≫ lt ≫ matchB`. -/
abbrev Pos392 : FinObj := ⟨3⟩   -- t = "acb": 0=a, 1=c, 2=b
def matchA392 : RE Pos392 Pos392 := .atom fun i j => (i == j) && (i.val == 0)
def matchB392 : RE Pos392 Pos392 := .atom fun i j => (i == j) && (i.val == 2)
def lt392     : RE Pos392 Pos392 := .atom fun i j => decide (i.val < j.val)
-- "ab" ⊑ "acb": an 'a' occurs before a 'b'.
example : eval rel⟦ matchA392 ≫ lt392 ≫ matchB392 ⟧ 0 2 = true  := by decide
example : eval rel⟦ matchA392 ≫ lt392 ≫ matchB392 ⟧ 2 0 = false := by decide

/-! ### 9. L49 Group Anagrams — EQUIVALENCE classes by mutual division: `(c / c) ∩ (c / c)°`. -/
abbrev Word49   : FinObj := ⟨6⟩   -- ["eat","tea","tan","ate","nat","bat"]
abbrev Letter49 : FinObj := ⟨5⟩   -- e,a,t,n,b ↦ 0,1,2,3,4
def chars49 : RE Word49 Letter49 := .atom fun w l =>
  match w.val, l.val with
  | 0, 0 | 0, 1 | 0, 2 => true   -- eat
  | 1, 0 | 1, 1 | 1, 2 => true   -- tea
  | 2, 1 | 2, 2 | 2, 3 => true   -- tan
  | 3, 0 | 3, 1 | 3, 2 => true   -- ate
  | 4, 1 | 4, 2 | 4, 3 => true   -- nat
  | 5, 1 | 5, 2 | 5, 4 => true   -- bat
  | _, _ => false
-- same-anagram = mutual letter-set containment.
example : eval rel⟦ (chars49 / chars49) ∩ (chars49 / chars49)° ⟧ 0 3 = true  := by decide  -- eat ~ ate
example : eval rel⟦ (chars49 / chars49) ∩ (chars49 / chars49)° ⟧ 0 2 = false := by decide  -- eat ≁ tan

/-! ### 10. Power-object EXTREMUM — `Λ(set) ≫ min(le)` picks the ≤-least member (the L121/sort shape). -/
abbrev One10 : FinObj := ⟨1⟩
abbrev Val10 : FinObj := ⟨4⟩
def elems10 : RE One10 Val10 := .atom fun _ j => j.val == 1 || j.val == 3   -- the set {1,3}
def le10    : RE Val10 Val10 := .atom fun i j => decide (i.val ≤ j.val)
-- `Λ(elems)` codes the set as a power-object point; `max(le)` picks the element `≤` all others
-- (B&dM's `max` over the `≤` preference), i.e. the minimum of {1,3} = 1.
example : eval rel⟦ Λ(elems10) ≫ max(le10) ⟧ 0 1 = true  := by decide
example : eval rel⟦ Λ(elems10) ≫ max(le10) ⟧ 0 3 = false := by decide

end Freyd.Alg.FinRel.Leet
