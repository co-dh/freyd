/-
  Demos and case-study fixtures for the RelInterp interpreter.  Moved out of rel/RelInterp.lean,
  which now holds only the interpreter machinery (FinRel, RE, eval, the derived vocabulary, the
  transport lemmas, and the ProgEval fold evaluator).  Namespaces are reopened here so every
  fully-qualified name (Freyd.Alg.FinRel.DemoDivision.solvedE, ...Demo121.solveE, ...ProgEval.prog121)
  is unchanged; importers see the same names.
-/
import rel.RelInterp

namespace Freyd.Alg.FinRel

open Freyd

/-! ## Demo 1 — relational DIVISION on ground data (the classic query)

  `solved : Student ⟶ Problem`; `solved/solved : Student ⟶ Student` relates `s` to `t` iff
  `s` solved EVERY problem `t` solved.  Column `t = Alice` answers "who solved everything
  Alice solved?". -/

namespace DemoDivision

abbrev Student : FinObj := ⟨4⟩
abbrev Problem : FinObj := ⟨4⟩

/-- Ground data: 0 = Alice solved {0,1}; 1 solved {0,1,2}; 2 solved {1}; 3 solved {0,1,3}. -/
def solvedFn : Fin 4 → Fin 4 → Bool := fun s p =>
  match s.val, p.val with
  | 0, 0 => true | 0, 1 => true
  | 1, 0 => true | 1, 1 => true | 1, 2 => true
  | 2, 1 => true
  | 3, 0 => true | 3, 1 => true | 3, 3 => true
  | _, _ => false

def solvedE : RE Student Problem := .atom solvedFn

-- Who solved everything Alice (student 0) solved? — students 0, 1, 3.
#eval List.ofFn fun s : Fin 4 => eval (.div solvedE solvedE) s 0

example : (List.ofFn fun s : Fin 4 => eval (.div solvedE solvedE) s 0)
    = [true, true, false, true] := by decide

end DemoDivision

/-! ## Demo 2 — LeetCode 207 (Course Schedule) run as a relation-algebra term

  `canFinish` iff the prerequisite graph has no cycle iff `reach ∩ id = 𝟘`, where
  `reach = R ∪ R≫R ∪ … ` (paths of length `1..n`) — a PURE term: one ground atom,
  then only comp/join/meet/id.  Polynomial; no powerset involved. -/

namespace Demo207

abbrev Course : FinObj := ⟨4⟩

/-- Paths of length `1..k+1` as a term: `reach 0 = R`, `reach (k+1) = R ∪ (R ≫ reach k)`. -/
def reachE (R : RE Course Course) : Nat → RE Course Course
  | 0 => R
  | k + 1 => .join R (.comp R (reachE R k))

def edgeFn (es : List (Nat × Nat)) : Fin 4 → Fin 4 → Bool := fun i j =>
  es.any fun e => e.1 == i.val && e.2 == j.val

/-- Nonemptiness of an evaluated relation, executably. -/
def nonemptyR {a b : FinObj} (R : a ⟶ b) : Bool :=
  anyFin a.card fun x => anyFin b.card fun y => R x y

/-- LC 207: no course reaches itself — `reach ∩ id = 𝟘`. -/
def canFinish (es : List (Nat × Nat)) : Bool :=
  !nonemptyR (eval (.meet (reachE (.atom (edgeFn es)) 3) (.id Course)))

-- `0→1→2→3` is acyclic (can finish); adding `3→1` creates the cycle `1→2→3→1`.
#eval (canFinish [(0,1),(1,2),(2,3)], canFinish [(0,1),(1,2),(2,3),(3,1)])

example : canFinish [(0,1),(1,2),(2,3)] = true := by decide
example : canFinish [(0,1),(1,2),(2,3),(3,1)] = false := by decide

end Demo207

/-! ## Demo 3 — LeetCode 121 (Best Time to Buy and Sell Stock) run as its SPEC TERM

  `leet.L121` proves `solve = A spec ≫ maxRel D` in `Rel(Set)` — a PROOF, never executed.
  Here the SAME shape `A spec ≫ max D` is a term the interpreter RUNS: `A spec` brute-forces
  the achievable-profit SET over all `2^|Val|` subset codes, `max D` picks its `≤`-greatest
  member.  Correct, and exponential in `|Val|` — the honest cost of running the spec.

  Bounding the infinite carrier `Int`: profits of an instance with prices in a known range
  live in `-M..M`; offset-encode as `Fin (2M+1)` (`v` codes profit `v - M`).  This bounded
  encoding is PROVED faithful: `specFn_iff`/`eval_solveE_iff` below decode the run pointwise,
  and `rel.AutoDeriveSearch.specFn_transport`/`specAnswer_eq` chain them to the abstract
  `L121.profit` and the certified `L121.solve_correct`. -/

namespace Demo121

abbrev One : FinObj := ⟨1⟩

/-- Achievable-profit spec of a fixed instance, offset-encoded: profit `0`, or
    `price j − price i` for day `i` before day `j`.  This is `leet.L121.profit`, bounded —
    PROVABLY so (`rel.AutoDeriveSearch.specFn_transport`), not just by transcription. -/
def specFn (n M : Nat) (price : Fin n → Int) : Fin 1 → Fin (2 * M + 1) → Bool := fun _ v =>
  (v.val == M) || anyFin n fun i => anyFin n fun j =>
    decide (i.val < j.val) && decide (price j - price i + M = (v.val : Int))

/-- L121's preference order `D w z := z ≤ w` (see `L121.solve_eq_maxRel`). -/
def geFn (M : Nat) : Fin (2 * M + 1) → Fin (2 * M + 1) → Bool := fun w z =>
  decide (z.val ≤ w.val)

/-- **The LeetCode solution as a runnable relation-algebra term**: `A spec ≫ max D`. -/
def solveE (n M : Nat) (price : Fin n → Int) : RE One ⟨2 * M + 1⟩ :=
  .comp (AE (.atom (specFn n M price))) (maxRelE (.atom (geFn M)))

/-- Decode the interpreter's answer column back to profits. -/
def answers (n M : Nat) (price : Fin n → Int) : List (Option Int) :=
  List.ofFn fun v : Fin (2 * M + 1) =>
    if eval (solveE n M price) 0 v then some ((v.val : Int) - M) else none

/-- `specFn` decoded to arithmetic: code `v` is accepted iff the profit it codes (`v − M`)
    is `0` (code `M`) or a price difference over an ordered day pair.  First leg of the
    spec-transport proof (`rel.AutoDeriveSearch.specFn_transport` matches this against the
    abstract `L121.profit`). -/
theorem specFn_iff {n M : Nat} {price : Fin n → Int} {x : Fin 1} {v : Fin (2 * M + 1)} :
    specFn n M price x v = true ↔
      (v.val = M ∨ ∃ i j : Fin n, i.val < j.val ∧ price j - price i + M = (v.val : Int)) := by
  show ((v.val == M) || anyFin n fun i => anyFin n fun j =>
    decide (i.val < j.val) && decide (price j - price i + M = (v.val : Int))) = true ↔ _
  constructor
  · intro h
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact Or.inl (beq_iff_eq.mp h)
    · obtain ⟨i, hi⟩ := anyFin_iff.mp h
      obtain ⟨j, hj⟩ := anyFin_iff.mp hi
      obtain ⟨hij, heq⟩ := Bool.and_eq_true_iff.mp hj
      exact Or.inr ⟨i, j, decide_eq_true_iff.mp hij, decide_eq_true_iff.mp heq⟩
  · intro h
    refine Bool.or_eq_true_iff.mpr (h.imp (fun h => beq_iff_eq.mpr h) ?_)
    rintro ⟨i, j, hij, heq⟩
    exact anyFin_iff.mpr ⟨i, anyFin_iff.mpr ⟨j, Bool.and_eq_true_iff.mpr
      ⟨decide_eq_true_iff.mpr hij, decide_eq_true_iff.mpr heq⟩⟩⟩

/-- The interpreted LC 121 spec term, decoded pointwise: `solveE` accepts code `v` iff the
    coded profit is achievable (`specFn`) and `≥` every achievable coded profit — the
    `A_comp_maxRel_apply` transport specialised to this problem's atoms.
    `rel.AutoDeriveSearch` chains this to the certified `L121.solve_correct`. -/
theorem eval_solveE_iff {n M : Nat} {price : Fin n → Int} {x : Fin 1} {v : Fin (2 * M + 1)} :
    eval (solveE n M price) x v = true ↔
      (specFn n M price x v = true ∧
       ∀ z : Fin (2 * M + 1), specFn n M price x z = true → z.val ≤ v.val) := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ :=
      (Λ_comp_maxRel_apply (.atom (specFn n M price)) (.atom (geFn M)) x v).mp h
    exact ⟨h1, fun z hz => decide_eq_true_iff.mp (h2 z hz)⟩
  · rintro ⟨h1, h2⟩
    exact (Λ_comp_maxRel_apply (.atom (specFn n M price)) (.atom (geFn M)) x v).mpr
      ⟨h1, fun z hz => decide_eq_true_iff.mpr (h2 z hz)⟩

/-- Tiny instance `[1,2]` (buy 1 sell 2, profit 1), kernel-checked end to end:
    the term's answer column is `{profit 1}` — brute force over `2^3 = 8` subsets. -/
example : answers 2 1 (fun i => match i.val with | 0 => 1 | _ => 2)
    = [none, none, some 1] := by decide

-- `[2,4,1]` → profit 2 (buy 2 sell 4), over `2^7 = 128` subsets.
#eval answers 3 3 (fun i => match i.val with | 0 => 2 | 1 => 4 | _ => 1)

-- LeetCode 121's own example `[7,1,5,3,6,4]` → profit 5 (buy 1 sell 6): the spec term runs
-- over `2^13 = 8192` subset codes.  (Cross-check: `L121.lean` `#eval`s `solveFn = 5`.)
#eval answers 6 6
  (fun i => match i.val with | 0 => 7 | 1 => 1 | 2 => 5 | 3 => 3 | 4 => 6 | _ => 4)

end Demo121

/-! ## ProgEval demos — LC 121 as a runnable fold, and a hylo run -/

namespace ProgEval
/-- Leaf `x ↦ (x, 0)` — `L121.algFn` on `Sum.inl`. -/
def base121 (x : Int) : Int × Int := (x, 0)
/-- Snoc `((m,b), p) ↦ (min m p, max b (p−m))` — `L121.algFn` on `Sum.inr`. -/
def step121 (st : Int × Int) (p : Int) : Int × Int := (imin st.1 p, imax st.2 (p - st.1))

/-- **LC 121's derived program as a term**: fold to `(minSoFar, bestProfit)`, then project the
    profit.  Exactly the fold the AoP derivation `solve = A spec ≫ max D` produces (its `foldFn`
    followed by `Prod.snd`, cf. `L121.solve_eq_cata`). -/
def prog121 : Prog (SL Int) Int := .comp (.cata base121 step121) (.fn Prod.snd)
-- LeetCode 121's own example `[7,1,5,3,6,4]`: run by FOLDING 6 prices → best profit 5.
-- NO `2^13` subset enumeration (contrast Demo 3, which enumerates 8192 subset codes).
#eval evalP prog121 (slOf 7 [1, 5, 3, 6, 4])

example : evalP prog121 (slOf 7 [1, 5, 3, 6, 4]) = 5 := by decide
example : evalP prog121 (slOf 7 [6, 4, 3, 1]) = 0 := by decide
example : evalP prog121 (slOf 2 [4, 1]) = 2 := by decide

/-- **Both evaluators agree on the instance `[1,2]`** (prices 1 then 2, profit 1): the POLYNOMIAL
    program-fold (`evalP prog121`) and the EXPONENTIAL spec-powerset (`Demo121.answers`, `A spec ≫
    max D` over all 8 subset codes) both return profit 1.  This is the AoP derivation
    `solve = A spec ≫ max D` (proven in `leet.L121`), now MECHANICALLY runnable on both sides.
    The agreement is also a THEOREM on EVERY instance, not just this kernel-checked one:
    `rel.AutoDeriveSearch.evaluators_agree`, via the spec-transport lemmas above. -/
example :
    evalP prog121 (slOf 1 [2]) = 1
    ∧ Demo121.answers 2 1 (fun i => match i.val with | 0 => 1 | _ => 2) = [none, none, some 1] := by
  decide

-- Sum `1..3` as a hylo: unfold `n+1 ↦ (n, n+1)` down to the leaf `0`, then fold with `+` → 6.
#eval hyloF (S := Nat) (fun n => match n with | 0 => .inl (0 : Int) | n + 1 => .inr (n, (n : Int) + 1))
  (fun a => a) (fun c a => c + a) 5 3

example :
    hyloF (S := Nat) (fun n => match n with | 0 => .inl (0 : Int) | n + 1 => .inr (n, (n : Int) + 1))
      (fun a => a) (fun c a => c + a) 5 3 = some 6 := by decide

end ProgEval

end Freyd.Alg.FinRel
