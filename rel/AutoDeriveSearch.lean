/-
  AUTO-DERIVE SEARCH — the PROPOSE → TEST → CERTIFY loop (proof of concept).

  Deriving an efficient program from a relational spec splits into (1) INVENTING the auxiliary
  fold state — undecidable in general — and (2) everything downstream, which is mechanical.
  For problems whose optimal state is a KNOWN shape, this file closes the loop automatically:

  * PROPOSE — a catalog of candidate programs, enumerated from standard state shapes:
    running scalars (`max`, `sum`), sixteen `(running, best)` pair combinations
    (2 seeds × 4 running-updates × 2 best-updates), and a memo-list fallback.  Each candidate
    is a `ProgEval.Prog` term, runnable by the structural-fold evaluator `evalP` (polynomial).

  * TEST — the differential tester runs the SPEC as the relation-algebra term
    `Λ spec ≫ max D` through the `FinRel` interpreter (`Demo121.answers`: exponential in the
    value range, exact — and PROVED equal to the certified maximum, `specAnswer_eq` below)
    and compares its decoded answer with each candidate's `evalP` output
    on an EXHAUSTIVELY ENUMERATED set of small instances (every price list of length ≤ 3 over
    `{1,2,3}`).  Candidates that disagree anywhere are REJECTED; survivors are ranked by
    state cost (catalog order).  Fully automatic, `#eval`-able, and kernel-checkable
    (`by decide`).  No human picks the state shape or the tests.

  * CERTIFY — the surviving shape instantiates the `AutoDerive.RunningBest` driver: its eight
    arithmetic side conditions are one-line `imin`/`imax`/`omega` facts (auto-dischargeable);
    the driver then emits full extremum correctness on ALL inputs and the §7.5 morphism
    headline `solve = max (≤) · Λ spec`.

  Demonstrated end-to-end on LeetCode 121 (best time to buy/sell stock): the loop REJECTS
  the plain running-max and 16 other wrong shapes and SELECTS the `(runningMin, best)` pair,
  which is then certified.  The tested candidate and the certified fold are proved to be the
  SAME program (`tested_eq_certified`), so the empirical selection and the proof talk about
  one object.

  HONEST BOUNDARY.  Certification is automatic EXCEPT the spec characterisation
  `gen_sound`/`spec_gen` ("the generator's search space is exactly the spec") — a genuinely
  problem-specific induction (~70 lines in `leet.L121`, reused here via `gen_eq`).  That
  proof is the residual creative obligation; nothing in this file synthesises it.  Also:
  the tester validates FUNCTIONAL agreement only — the correct-but-expensive memo-list
  candidate passes too, and is rejected only by the catalog's state-cost RANKING, not by
  testing.  The runnable spec (`Demo121.specFn`, offset-encoded over `Fin (2M+1)`) IS
  proved faithful to the abstract spec `LC121.profit` (`specFn_transport`, `profit_bounded`,
  `specAnswer_eq` below): the tester's oracle is a theorem, not a transcription.  What
  remains by construction is only the reading of the informal LeetCode prose as
  `LC121.profit`, and the fact that SELECTION checks survivors on finitely many instances
  (the oracle is exact everywhere; the winner's pass is even a theorem, `winner_passes`).

  Mathlib-free.  Certified parts Sorry-free; axioms ⊆ {propext, Classical.choice, Quot.sound}
  (inherited from `horner_correct` via `RunningBest`).
-/
import rel.RelInterpDemo   -- was rel.RelInterp; needs the moved Demo121/prog121 fixtures
import rel.AutoDerive
import leet.L121

set_option linter.unusedVariables false

namespace Freyd.Alg.Search

open Freyd
open Freyd.Alg.RelSet          -- graph, LC121.*
open Freyd.Alg.RelSet.SL       -- SnocList, dSL, cataFold, RunningBest, imin/imax
open Freyd.Alg.FinRel          -- Demo121.*, ProgEval.*

/-! ## PROPOSE — the catalog of candidate state shapes -/

/-- A catalog entry: a named runnable program over non-empty price lists. -/
structure Candidate where
  name : String
  prog : ProgEval.Prog (ProgEval.SL Int) Int

/-- Pair-state shape: fold to `(running e, best b)` with seed `base`, running update `s1`,
    best update `s2` (both given the OLD running value), answer `b`. -/
def pairProg (base : Int → Int × Int) (s1 : Int → Int → Int) (s2 : Int → Int → Int → Int) :
    ProgEval.Prog (ProgEval.SL Int) Int :=
  .comp (.cata base fun st p => (s1 st.1 p, s2 st.1 st.2 p)) (.fn Prod.snd)

/-- Memo-list shape: keep ALL elements, post-process by brute force.  Always functionally
    correct — included to show the tester cannot reject it; only the cost RANKING does. -/
def bruteBest : List Int → Int
  | [] => 0
  | p :: rest => rest.foldl (fun acc b => imax acc (p - b)) (bruteBest rest)

/-- Pair-shape ingredient lists: seeds, running updates, best updates.  The names encode the
    combination; the enumeration below is the PROPOSE step. -/
def seeds : List (String × (Int → Int × Int)) :=
  [("b0=0", fun x => (x, 0)), ("b0=x", fun x => (x, x))]
def runUpds : List (String × (Int → Int → Int)) :=
  [("min", fun e p => imin e p), ("max", fun e p => imax e p),
   ("keep", fun e _ => e), ("kad", fun e p => imax p (e + p))]
def bestUpds : List (String × (Int → Int → Int → Int)) :=
  [("sell", fun e b p => imax b (p - e)), ("kadb", fun e b p => imax b (imax p (e + p)))]

/-- The catalog, ranked by state cost: scalars, then pairs, then the memo list. -/
def catalog : List Candidate :=
  ⟨"scalar max", .cata (fun x => x) imax⟩ ::
  ⟨"scalar sum", .cata (fun x => x) (· + ·)⟩ ::
  (seeds.flatMap fun b => runUpds.flatMap fun s1 => bestUpds.map fun s2 =>
    ⟨s!"pair {b.1}·{s1.1}·{s2.1}", pairProg b.2 s1.2 s2.2⟩) ++
  [⟨"memo list", .comp (.cata (fun x => [x]) fun l a => a :: l) (.fn bruteBest)⟩]

/-! ## TEST — differential testing against the interpreted spec term -/

/-- A test instance: a non-empty day-ordered price list. -/
structure Inst where
  first : Int
  rest : List Int

def Inst.prices (i : Inst) : List Int := i.first :: i.rest
def Inst.n (i : Inst) : Nat := i.rest.length + 1
/-- Profit bound: `maxPrice − minPrice`; all achievable profits lie in `[-M, M]` (PROVED:
    `profit_bounded`), so the offset encoding over `Fin (2M+1)` is faithful (PROVED:
    `specFn_transport`).  Computed FROM the instance. -/
def Inst.bound (i : Inst) : Nat :=
  (i.rest.foldl imax i.first - i.rest.foldl imin i.first).toNat
def Inst.priceFn (i : Inst) : Fin i.n → Int := fun k => i.prices.getD k.val 0

/-- THE SPEC SIDE: run `Λ spec ≫ max D` through the `FinRel` interpreter (exponential —
    `2^(2M+1)` subset codes) and decode the answer column.  A singleton list on every
    well-formed instance (the `≤`-maximum is unique). -/
def specAnswer (i : Inst) : List Int :=
  (Demo121.answers i.n i.bound i.priceFn).filterMap id

/-- THE CANDIDATE SIDE: run the program by structural fold (polynomial). -/
def progAnswer (p : ProgEval.Prog (ProgEval.SL Int) Int) (i : Inst) : Int :=
  ProgEval.evalP p (ProgEval.slOf i.first i.rest)

/-- Differential test on one instance. -/
def agree (p : ProgEval.Prog (ProgEval.SL Int) Int) (i : Inst) : Bool :=
  specAnswer i == [progAnswer p i]

def passes (p : ProgEval.Prog (ProgEval.SL Int) Int) (insts : List Inst) : Bool :=
  insts.all (agree p)

/-- Candidates surviving differential testing, in catalog (cost) order. -/
def survivors (cs : List Candidate) (insts : List Inst) : List String :=
  (cs.filter fun c => passes c.prog insts).map (·.name)

/-- THE LOOP'S OUTPUT: the cheapest surviving candidate. -/
def select (cs : List Candidate) (insts : List Inst) : Option String :=
  (cs.find? fun c => passes c.prog insts).map (·.name)

/-- Exhaustive test-instance enumeration: EVERY price list of length 2 or 3 over `{1, 2, 3}`
    (36 instances) — no human picks the tests either.  Among them, `⟨2,[1]⟩` kills every
    `b0=x` seed (profit must start at 0), `⟨2,[1,2]⟩` kills every wrong running update (the
    buy must move to the later minimum), `⟨1,[2]⟩` kills the scalars. -/
def smallInsts : List Inst :=
  let vals : List Int := [1, 2, 3]
  (vals.flatMap fun a => vals.map fun b => Inst.mk a [b]) ++
  (vals.flatMap fun a => vals.flatMap fun b => vals.map fun c => Inst.mk a [b, c])

/-! ### Running the loop -/

-- The interpreted spec answers on a sample of instances:
#eval ([⟨1, [2]⟩, ⟨2, [1]⟩, ⟨2, [1, 2]⟩, ⟨3, [2, 4, 1]⟩] : List Inst).map specAnswer
-- Every candidate's verdict over all 36 enumerated instances:
#eval catalog.map fun c => (c.name, passes c.prog smallInsts)
-- The survivors and the selection:
#eval survivors catalog smallInsts
#eval select catalog smallInsts

/-! ### Kernel-checked rejection / acceptance (`by decide`)

  The named exhibits.  `runMaxProg` is the catalog's "scalar max" (plain running max — the
  shape that misses the pair); `fromFirstProg` is "pair b0=0·keep·sell" (running max of
  `p − p₀` — it never updates the buy price); `winnerProg` is "pair b0=0·min·sell". -/

def runMaxProg : ProgEval.Prog (ProgEval.SL Int) Int := .cata (fun x => x) imax
def fromFirstProg : ProgEval.Prog (ProgEval.SL Int) Int :=
  pairProg (fun x => (x, 0)) (fun e _ => e) (fun e b p => imax b (p - e))
def winnerProg : ProgEval.Prog (ProgEval.SL Int) Int :=
  pairProg (fun x => (x, 0)) (fun e p => imin e p) (fun e b p => imax b (p - e))

/-- The winner is literally `RelInterp`'s hand-written derived program. -/
theorem winner_eq_prog121 : winnerProg = ProgEval.prog121 := rfl

-- REJECTED (kernel-checked): plain running max returns 2 on prices [1,2]; the interpreted
-- spec's maximum profit is 1.
example : agree runMaxProg ⟨1, [2]⟩ = false := by decide
-- REJECTED (kernel-checked): the from-first pair returns 0 on [2,1,2]; the spec says 1
-- (buy the LATER minimum 1, sell 2) — the running coordinate must actually run.
example : agree fromFirstProg ⟨2, [1, 2]⟩ = false := by decide
-- ACCEPTED (kernel-checked): the (runningMin, best) pair agrees on the whole suite's
-- kernel-sized prefix.
example : passes winnerProg [⟨1, [2]⟩, ⟨2, [1]⟩, ⟨2, [1, 2]⟩] = true := by decide

/-- **THE SELECTION, kernel-checked**: on the `M = 1` instances the loop's verdict vector over
    the full 19-candidate catalog is exactly this — every scalar and every wrong pair
    combination rejected, the `(runningMin, best)` pair and the memo list accepted — and the
    cost ranking picks the pair.  No human chose the shape. -/
theorem loop_verdicts :
    (catalog.map fun c => passes c.prog [⟨1, [2]⟩, ⟨2, [1]⟩, ⟨2, [1, 2]⟩])
      = [false, false, true, false, false, false, false, false, false, false,
         false, false, false, false, false, false, false, false, true] := by decide

theorem loop_selects_winner :
    select catalog [⟨1, [2]⟩, ⟨2, [1]⟩, ⟨2, [1, 2]⟩] = some "pair b0=0·min·sell" := by decide

/-! ## CERTIFY — the selected shape through the `RunningBest` driver

  The winning catalog entry instantiates `AutoDerive.RunningBest`.  Everything below the
  bundle is MECHANICAL: the eight side-condition fields are one-line `imin`/`imax`/`omega`
  facts (this is the "auto-discharge" half of certification), and the driver then emits
  extremum correctness and the §7.5 morphism headline.

  The one CREATIVE input is the spec characterisation — the generator's search space equals
  the achievable-profit spec.  It is a problem-specific induction; here it is `leet.L121`'s
  `gen_sound`/`spec_gen` (~70 lines there), transported along `gen_eq` because the bundle's
  generator is definitionally L121's. -/

/-- The certification bundle for the selected shape.  Data fields = the winning catalog
    combination (`b0=0`, `min`, `sell`) plus its generator candidates and dominance order;
    proof fields = the eight one-line arithmetic facts (the auto-dischargeable part). -/
def l121 : RunningBest Int Int Int where
  base x := (x, 0)
  step1 e p := imin e p
  step2 e b p := imax b (p - e)
  cand1 e p w1 := w1 = e ∨ w1 = p
  cand2 e b p _ w2 := w2 = b ∨ w2 = p - e
  ord e e' := e ≤ e'
  ord_refl e := Int.le_refl e
  ord_trans h1 h2 := Int.le_trans h1 h2
  step1_mono p h := imin_mono h (Int.le_refl p)
  step2_mono p h1 h2 := imax_mono h2 (by omega)
  step1_cand e p := imin_eq_or e p
  step2_cand e b p := imax_eq_or b (p - e)
  cand1_le h := by
    rcases h with h | h <;> rw [h]
    · exact imin_le_left _ _
    · exact imin_le_right _ _
  cand2_le h1 h2 := by
    rcases h2 with h | h <;> rw [h]
    · exact imax_ge_left _ _
    · exact imax_ge_right _ _

/-- The bundle's generator IS `L121`'s generator. -/
theorem gen_eq : l121.gen = LC121.gen := by
  funext u w
  cases u with
  | inl x => rfl
  | inr q => obtain ⟨st, p⟩ := q; rfl

/-- Generator soundness for the bundle — `LC121.gen_sound` transported along `gen_eq`.
    THE RESIDUAL CREATIVE OBLIGATION lives behind this line: `LC121.gen_sound` is a
    problem-specific induction, not derivable from the catalog. -/
theorem gen_spec' (xs : SnocList Int Int) (w : Int × Int) (h : cataFold l121.gen xs w) :
    LC121.spec xs w.2 :=
  (LC121.gen_sound xs w (by rw [← gen_eq]; exact h)).2

/-- Generator completeness for the bundle — `LC121.spec_gen` transported along `gen_eq`. -/
theorem spec_gen' (xs : SnocList Int Int) (v : Int) (hv : LC121.spec xs v) :
    ∃ e, cataFold l121.gen xs (e, v) := by
  rw [gen_eq]; exact LC121.spec_gen xs v hv

/-- **CERTIFIED**: the selected fold's best component is an achievable profit and dominates
    every achievable profit — on ALL inputs, not just the tested ones.  Emitted by the
    `RunningBest` driver from the bundle + the spec characterisation. -/
theorem solve_correct (xs : SnocList Int Int) :
    LC121.profit xs (l121.foldFn xs).2 ∧ ∀ v, LC121.profit xs v → v ≤ (l121.foldFn xs).2 :=
  l121.correct LC121.spec gen_spec' spec_gen' xs

/-- **CERTIFIED §7.5 headline**: the selected program IS `max (≤) · Λ spec` as a morphism of
    `Rel(Set)`. -/
theorem solve_eq_est :
    (Freyd.Alg.RelSet.graph (fun xs => (l121.foldFn xs).2) : dSL Int Int ⟶ (⟨Int⟩ : RelSet.{0}))
      = Λ LC121.spec ≫ est (fun w z : Int => z ≤ w) :=
  l121.eq_est LC121.spec gen_spec' spec_gen'

/-! ### The tested candidate and the certified fold are the same program -/

/-- Convert the interpreter's snoc-lists to the derivation's. -/
def toSnoc : ProgEval.SL Int → SnocList Int Int
  | .wrap a => .wrap a
  | .snoc s a => .snoc (toSnoc s) a

/-- The pair-level bridge: the winner's structural fold is the bundle's fold. -/
theorem foldSL_eq_foldFn (s : ProgEval.SL Int) :
    ProgEval.foldSL ProgEval.base121 ProgEval.step121 s = l121.foldFn (toSnoc s) := by
  induction s with
  | wrap a => rfl
  | snoc s a ih =>
    show ProgEval.step121 (ProgEval.foldSL ProgEval.base121 ProgEval.step121 s) a
      = l121.foldFn (toSnoc (ProgEval.SL.snoc s a))
    rw [ih]; rfl

/-- What the tester RAN (`evalP winnerProg`) is what the driver CERTIFIED (`l121.foldFn`'s
    best component): the empirical selection and the proof are about one object. -/
theorem tested_eq_certified (s : ProgEval.SL Int) :
    ProgEval.evalP winnerProg s = (l121.foldFn (toSnoc s)).2 :=
  congrArg Prod.snd (foldSL_eq_foldFn s)

/-- The bundle's fold is `leet.L121`'s hand-derived fold — the loop reconstructed the
    existing certified program. -/
theorem foldFn_eq_L121 (xs : SnocList Int Int) : l121.foldFn xs = LC121.foldFn xs := by
  induction xs with
  | wrap x => rfl
  | snoc xs p ih =>
    show (imin (l121.foldFn xs).1 p, imax (l121.foldFn xs).2 (p - (l121.foldFn xs).1)) = _
    rw [ih]; rfl

/-- **END-TO-END**: the program the loop selected empirically is certified optimal on every
    input — the propose → test → certify loop, closed. -/
theorem selected_correct (s : ProgEval.SL Int) :
    LC121.profit (toSnoc s) (ProgEval.evalP winnerProg s) ∧
    ∀ v, LC121.profit (toSnoc s) v → v ≤ ProgEval.evalP winnerProg s := by
  rw [tested_eq_certified]; exact solve_correct (toSnoc s)

/-! ## SOUND ORACLE — the tester's spec leg is a THEOREM, not a transcription

  Everything above ran the hand-transcribed bounded atom `Demo121.specFn` and trusted it.
  This section CLOSES that spec-transport gap:

  * `specFn_transport` — the offset encoding is FAITHFUL: `specFn` accepts code `v` iff the
    abstract certified spec `LC121.profit` holds of the decoded profit `v − M`, with the
    day decoding (`Inst.priceFn` = positional lookup in `first :: rest`) proved against the
    snoc-list the derivation folds (`toList_ofList`).
  * `profit_bounded` — the bound `M = i.bound` HONESTLY contains every achievable profit,
    so the encoding loses nothing.
  * `specAnswer_eq` — chaining both through the interpreter semantics
    (`RelInterp.Λ_comp_est_apply`/`eval_solveE_iff`) and `L121.solve_correct`:
    the spec leg's decoded answer IS `[certified maximum profit]`, on EVERY instance.
  * `agree_iff` / `winner_passes` — the differential test therefore tests candidates against
    the certified optimum (a theorem), and the winner provably passes every instance.

  A transcription bug in `specFn`, the bound, or the decode would now be an unprovable
  lemma — not a silently wrong oracle. -/

/-- Day-ordered price list of a snoc-list — the decode the offset encoding is checked against. -/
def toList : SnocList Int Int → List Int
  | .wrap x => [x]
  | .snoc xs p => toList xs ++ [p]

theorem toList_foldl : ∀ (rest : List Int) (acc : SnocList Int Int),
    toList (rest.foldl SnocList.snoc acc) = toList acc ++ rest
  | [], _ => (List.append_nil _).symm
  | p :: rest, acc => by
    show toList (rest.foldl SnocList.snoc (SnocList.snoc acc p)) = toList acc ++ (p :: rest)
    rw [toList_foldl rest (SnocList.snoc acc p)]
    show (toList acc ++ [p]) ++ rest = toList acc ++ (p :: rest)
    rw [List.append_assoc]; rfl

/-- The day decoding, closed: the snoc-list built from `(first, rest)` reads back as the
    day-ordered price list `first :: rest`. -/
theorem toList_ofList (first : Int) (rest : List Int) :
    toList (LC121.ofList first rest) = first :: rest :=
  toList_foldl rest (SnocList.wrap first)

/-! ### `getD` facts for the positional decode (mathlib-free) -/

theorem getD_append_lt : ∀ (L : List Int) (p : Int) (k : Nat), k < L.length →
    (L ++ [p]).getD k 0 = L.getD k 0
  | _ :: _, _, 0, _ => rfl
  | _ :: L, p, k + 1, h => getD_append_lt L p k (Nat.lt_of_succ_lt_succ h)
  | [], _, k, h => absurd h (Nat.not_lt_zero k)

theorem getD_append_len : ∀ (L : List Int) (p : Int), (L ++ [p]).getD L.length 0 = p
  | [], _ => rfl
  | _ :: L, p => getD_append_len L p

theorem getD_mem : ∀ (l : List Int) (k : Nat), k < l.length → l.getD k 0 ∈ l
  | a :: l, 0, _ => List.mem_cons.mpr (Or.inl rfl)
  | _ :: l, k + 1, h => List.mem_cons.mpr (Or.inr (getD_mem l k (Nat.lt_of_succ_lt_succ h)))
  | [], k, h => absurd h (Nat.not_lt_zero k)

/-! ### `mem`/`Before`/`profit` in day-index form — the shape `specFn` quantifies over -/

/-- `LC121.mem`, positionally: `b` occurs in `xs` iff it is some day's price. -/
theorem mem_iff : ∀ (xs : SnocList Int Int) (b : Int),
    LC121.mem xs b ↔ ∃ k, k < (toList xs).length ∧ (toList xs).getD k 0 = b := by
  intro xs
  induction xs with
  | wrap x =>
    intro b
    constructor
    · intro h
      exact ⟨0, Nat.zero_lt_one, (show b = x from h).symm⟩
    · rintro ⟨k, hk, hget⟩
      have hlen : (toList (SnocList.wrap x)).length = 1 := rfl
      have hk0 : k = 0 := by omega
      subst hk0
      exact hget.symm
  | snoc xs p ih =>
    intro b
    have hlen : (toList (SnocList.snoc xs p)).length = (toList xs).length + 1 := by
      show (toList xs ++ [p]).length = _
      simp [List.length_append]
    constructor
    · intro h
      rcases (h : LC121.mem xs b ∨ b = p) with h | h
      · obtain ⟨k, hk, hget⟩ := (ih b).mp h
        refine ⟨k, by omega, ?_⟩
        show (toList xs ++ [p]).getD k 0 = b
        rw [getD_append_lt _ _ _ hk]; exact hget
      · refine ⟨(toList xs).length, by omega, ?_⟩
        show (toList xs ++ [p]).getD (toList xs).length 0 = b
        rw [getD_append_len]; exact h.symm
    · rintro ⟨k, hk, hget⟩
      rcases Nat.lt_or_ge k (toList xs).length with hlt | hge
      · refine Or.inl ((ih b).mpr ⟨k, hlt, ?_⟩)
        rw [← getD_append_lt (toList xs) p k hlt]; exact hget
      · have hkeq : k = (toList xs).length := by omega
        subst hkeq
        have hget' : (toList xs ++ [p]).getD (toList xs).length 0 = b := hget
        exact Or.inr ((getD_append_len (toList xs) p).symm.trans hget').symm

/-- `LC121.Before`, positionally: buy day strictly before sell day. -/
theorem before_iff : ∀ (xs : SnocList Int Int) (b s : Int),
    LC121.Before xs b s ↔ ∃ k l : Nat, k < l ∧ l < (toList xs).length ∧
      (toList xs).getD k 0 = b ∧ (toList xs).getD l 0 = s := by
  intro xs
  induction xs with
  | wrap x =>
    intro b s
    constructor
    · intro h; exact h.elim
    · rintro ⟨k, l, hkl, hl, -, -⟩
      have hlen : (toList (SnocList.wrap x)).length = 1 := rfl
      omega
  | snoc xs p ih =>
    intro b s
    have hlen : (toList (SnocList.snoc xs p)).length = (toList xs).length + 1 := by
      show (toList xs ++ [p]).length = _
      simp [List.length_append]
    constructor
    · intro h
      rcases (h : LC121.Before xs b s ∨ (LC121.mem xs b ∧ s = p)) with h | ⟨hm, hs⟩
      · obtain ⟨k, l, hkl, hl, hb, hsx⟩ := (ih b s).mp h
        refine ⟨k, l, hkl, by omega, ?_, ?_⟩
        · show (toList xs ++ [p]).getD k 0 = b
          rw [getD_append_lt _ _ _ (by omega)]; exact hb
        · show (toList xs ++ [p]).getD l 0 = s
          rw [getD_append_lt _ _ _ hl]; exact hsx
      · obtain ⟨k, hk, hb⟩ := (mem_iff xs b).mp hm
        refine ⟨k, (toList xs).length, hk, by omega, ?_, ?_⟩
        · show (toList xs ++ [p]).getD k 0 = b
          rw [getD_append_lt _ _ _ hk]; exact hb
        · show (toList xs ++ [p]).getD (toList xs).length 0 = s
          rw [getD_append_len]; exact hs.symm
    · rintro ⟨k, l, hkl, hl, hb, hs⟩
      rcases Nat.lt_or_ge l (toList xs).length with hlt | hge
      · refine Or.inl ((ih b s).mpr ⟨k, l, hkl, hlt, ?_, ?_⟩)
        · rw [← getD_append_lt (toList xs) p k (by omega)]; exact hb
        · rw [← getD_append_lt (toList xs) p l hlt]; exact hs
      · have hleq : l = (toList xs).length := by omega
        subst hleq
        have hs' : (toList xs ++ [p]).getD (toList xs).length 0 = s := hs
        refine Or.inr ⟨(mem_iff xs b).mpr ⟨k, by omega, ?_⟩,
          ((getD_append_len (toList xs) p).symm.trans hs').symm⟩
        rw [← getD_append_lt (toList xs) p k (by omega)]; exact hb

/-- `LC121.profit`, positionally: `0`, or a price difference over an ordered day pair —
    exactly the quantifier shape of the transcribed atom `Demo121.specFn`. -/
theorem profit_iff (xs : SnocList Int Int) (w : Int) :
    LC121.profit xs w ↔
      w = 0 ∨ ∃ k l : Nat, k < l ∧ l < (toList xs).length ∧
        w = (toList xs).getD l 0 - (toList xs).getD k 0 := by
  constructor
  · intro h
    rcases (h : w = 0 ∨ ∃ b s, LC121.Before xs b s ∧ w = s - b) with h0 | ⟨b, s, hbef, hw⟩
    · exact Or.inl h0
    · obtain ⟨k, l, hkl, hl, hb, hs⟩ := (before_iff xs b s).mp hbef
      exact Or.inr ⟨k, l, hkl, hl, by rw [hb, hs]; exact hw⟩
  · rintro (h0 | ⟨k, l, hkl, hl, hw⟩)
    · exact Or.inl h0
    · exact Or.inr ⟨_, _, (before_iff xs _ _).mpr ⟨k, l, hkl, hl, rfl, rfl⟩, hw⟩

/-! ### The bound is honest: every achievable profit fits in `[-M, M]` for `M = i.bound` -/

theorem foldl_imin_le : ∀ (l : List Int) (a : Int), l.foldl imin a ≤ a
  | [], a => Int.le_refl a
  | p :: l, a => Int.le_trans (foldl_imin_le l (imin a p)) (imin_le_left a p)

theorem le_foldl_imax : ∀ (l : List Int) (a : Int), a ≤ l.foldl imax a
  | [], a => Int.le_refl a
  | p :: l, a => Int.le_trans (imax_ge_left a p) (le_foldl_imax l (imax a p))

theorem foldl_imin_le_mem : ∀ (l : List Int) (a b : Int), b ∈ l → l.foldl imin a ≤ b := by
  intro l
  induction l with
  | nil => intro a b h; exact nomatch h
  | cons p l ih =>
    intro a b h
    rcases List.mem_cons.mp h with h | h
    · subst h; exact Int.le_trans (foldl_imin_le l (imin a b)) (imin_le_right a b)
    · exact ih (imin a p) b h

theorem mem_le_foldl_imax : ∀ (l : List Int) (a b : Int), b ∈ l → b ≤ l.foldl imax a := by
  intro l
  induction l with
  | nil => intro a b h; exact nomatch h
  | cons p l ih =>
    intro a b h
    rcases List.mem_cons.mp h with h | h
    · subst h; exact Int.le_trans (imax_ge_right a b) (le_foldl_imax l (imax a b))
    · exact ih (imax a p) b h

/-- **The bound `M = i.bound` actually contains every achievable profit** — the scoping
    half of the transport: nothing the abstract spec can achieve falls outside the code
    range `Fin (2M+1)`. -/
theorem profit_bounded (i : Inst) (w : Int)
    (h : LC121.profit (LC121.ofList i.first i.rest) w) :
    -(i.bound : Int) ≤ w ∧ w ≤ (i.bound : Int) := by
  have hmin : i.rest.foldl imin i.first ≤ i.first := foldl_imin_le i.rest i.first
  have hmax : i.first ≤ i.rest.foldl imax i.first := le_foldl_imax i.rest i.first
  have hbound : (i.bound : Int)
      = i.rest.foldl imax i.first - i.rest.foldl imin i.first := by
    show ((i.rest.foldl imax i.first - i.rest.foldl imin i.first).toNat : Int) = _
    omega
  have hub : ∀ b, b ∈ i.first :: i.rest → b ≤ i.rest.foldl imax i.first := by
    intro b hb
    rcases List.mem_cons.mp hb with hb | hb
    · subst hb; exact hmax
    · exact mem_le_foldl_imax i.rest i.first b hb
  have hlb : ∀ b, b ∈ i.first :: i.rest → i.rest.foldl imin i.first ≤ b := by
    intro b hb
    rcases List.mem_cons.mp hb with hb | hb
    · subst hb; exact hmin
    · exact foldl_imin_le_mem i.rest i.first b hb
  rcases (profit_iff _ w).mp h with h0 | ⟨k, l, hkl, hl, hw⟩
  · omega
  · rw [toList_ofList] at hl hw
    have h1 := hub _ (getD_mem (i.first :: i.rest) k (by omega))
    have h2 := hub _ (getD_mem (i.first :: i.rest) l hl)
    have h3 := hlb _ (getD_mem (i.first :: i.rest) k (by omega))
    have h4 := hlb _ (getD_mem (i.first :: i.rest) l hl)
    omega

/-! ### The transport theorem and the certified oracle -/

/-- **THE SPEC-TRANSPORT THEOREM**: the hand-transcribed bounded atom `Demo121.specFn` is a
    FAITHFUL offset encoding of the abstract certified spec — code `v` is accepted iff
    `LC121.profit` holds of the decoded profit `v − M` on the decoded instance.  With this,
    running `specFn` through the interpreter IS running the certified spec object; a
    transcription bug would make this lemma unprovable. -/
theorem specFn_transport (i : Inst) (x : Fin 1) (v : Fin (2 * i.bound + 1)) :
    Demo121.specFn i.n i.bound i.priceFn x v = true ↔
      LC121.profit (LC121.ofList i.first i.rest) ((v.val : Int) - i.bound) := by
  rw [Demo121.specFn_iff, profit_iff, toList_ofList]
  have hn : i.n = (i.first :: i.rest).length := rfl
  constructor
  · rintro (h | ⟨a, c, hac, heq⟩)
    · exact Or.inl (by omega)
    · have h1 : i.priceFn a = (i.first :: i.rest).getD a.val 0 := rfl
      have h2 : i.priceFn c = (i.first :: i.rest).getD c.val 0 := rfl
      have hc := c.isLt
      exact Or.inr ⟨a.val, c.val, hac, by omega, by omega⟩
  · rintro (h | ⟨k, l, hkl, hl, hw⟩)
    · exact Or.inl (by omega)
    · have hkn : k < i.n := by omega
      have hln : l < i.n := by omega
      have h1 : i.priceFn ⟨k, hkn⟩ = (i.first :: i.rest).getD k 0 := rfl
      have h2 : i.priceFn ⟨l, hln⟩ = (i.first :: i.rest).getD l 0 := rfl
      exact Or.inr ⟨⟨k, hkn⟩, ⟨l, hln⟩, hkl, by omega⟩

/-- The interpreted spec term, decoded END-TO-END: `solveE` accepts exactly the code of the
    CERTIFIED maximum profit.  Chain: `eval_solveE_iff` (interpreter semantics) →
    `specFn_transport` (encoding faithfulness) → `profit_bounded` (bound coverage) →
    `L121.solve_correct` (the certified extremum). -/
theorem eval_solveE_eq (i : Inst) (v : Fin (2 * i.bound + 1)) :
    eval (Demo121.solveE i.n i.bound i.priceFn) 0 v = true ↔
      (v.val : Int) = LC121.solveFn (LC121.ofList i.first i.rest) + i.bound := by
  have hcor := LC121.solve_correct (LC121.ofList i.first i.rest)
  have hbnd := profit_bounded i _ hcor.1
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Demo121.eval_solveE_iff.mp h
    have hle : (v.val : Int) - i.bound ≤ LC121.solveFn (LC121.ofList i.first i.rest) :=
      hcor.2 _ ((specFn_transport i 0 v).mp h1)
    have hv0 : (LC121.solveFn (LC121.ofList i.first i.rest) + i.bound).toNat
        < 2 * i.bound + 1 := by omega
    have henc : ((((LC121.solveFn (LC121.ofList i.first i.rest) + i.bound).toNat : Nat) : Int)
        - i.bound) = LC121.solveFn (LC121.ofList i.first i.rest) := by omega
    have hz : (LC121.solveFn (LC121.ofList i.first i.rest) + i.bound).toNat ≤ v.val :=
      h2 ⟨_, hv0⟩ ((specFn_transport i 0 ⟨_, hv0⟩).mpr (by rw [henc]; exact hcor.1))
    omega
  · intro hv
    refine Demo121.eval_solveE_iff.mpr ⟨(specFn_transport i 0 v).mpr ?_, fun z hz => ?_⟩
    · have hveq : (v.val : Int) - i.bound = LC121.solveFn (LC121.ofList i.first i.rest) := by
        omega
      rw [hveq]; exact hcor.1
    · have := hcor.2 _ ((specFn_transport i 0 z).mp hz)
      omega

/-! ### From the pointwise theorem to the answer column -/

theorem filterMap_ofFn_none {α : Type} : ∀ {n : Nat} (f : Fin n → Option α),
    (∀ v, f v = none) → (List.ofFn f).filterMap id = []
  | 0, _, _ => by rw [List.ofFn_zero]; rfl
  | n + 1, f, h => by
    rw [List.ofFn_succ, List.filterMap_cons_none (by exact h 0)]
    exact filterMap_ofFn_none (fun i => f i.succ) (fun i => h i.succ)

theorem filterMap_ofFn_singleton {α : Type} : ∀ {n : Nat} (f : Fin n → Option α)
    (k : Nat) (c : α), k < n →
    (∀ v : Fin n, v.val = k → f v = some c) → (∀ v : Fin n, v.val ≠ k → f v = none) →
    (List.ofFn f).filterMap id = [c] := by
  intro n
  induction n with
  | zero => intro f k c hk _ _; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    intro f k c hk hsome hnone
    cases k with
    | zero =>
      rw [List.ofFn_succ, List.filterMap_cons_some (by exact hsome 0 rfl)]
      show c :: (List.ofFn fun i => f i.succ).filterMap id = [c]
      rw [filterMap_ofFn_none (fun i => f i.succ)
        (fun i => hnone i.succ (Nat.succ_ne_zero i.val))]
    | succ k' =>
      rw [List.ofFn_succ,
        List.filterMap_cons_none (by exact hnone 0 (fun h => Nat.succ_ne_zero k' h.symm))]
      exact ih (fun i => f i.succ) k' c (Nat.lt_of_succ_lt_succ hk)
        (fun v hv => hsome v.succ (by show v.val + 1 = k' + 1; omega))
        (fun v hv => hnone v.succ (by show v.val + 1 ≠ k' + 1; omega))

/-- **THE ORACLE IS CERTIFIED**: on EVERY instance, the tester's spec leg — the exponential
    interpreted term `Λ spec ≫ max D`, decoded — answers exactly the singleton of the
    certified maximum profit of `L121.solve_correct`.  What used to be a per-instance numeric
    coincidence is now `transport ∘ solve_correct`. -/
theorem specAnswer_eq (i : Inst) :
    specAnswer i = [LC121.solveFn (LC121.ofList i.first i.rest)] := by
  have hcor := LC121.solve_correct (LC121.ofList i.first i.rest)
  have hbnd := profit_bounded i _ hcor.1
  show (List.ofFn fun v : Fin (2 * i.bound + 1) =>
    if eval (Demo121.solveE i.n i.bound i.priceFn) 0 v then some ((v.val : Int) - i.bound)
    else none).filterMap id = _
  refine filterMap_ofFn_singleton _
    ((LC121.solveFn (LC121.ofList i.first i.rest) + i.bound).toNat) _
    (by omega) (fun v hv => ?_) (fun v hv => ?_)
  · rw [if_pos ((eval_solveE_eq i v).mpr (by omega))]
    have hveq : (v.val : Int) - i.bound = LC121.solveFn (LC121.ofList i.first i.rest) := by
      omega
    rw [hveq]
  · have hne : ¬ (eval (Demo121.solveE i.n i.bound i.priceFn) 0 v = true) := by
      intro h
      have := (eval_solveE_eq i v).mp h
      omega
    rw [if_neg hne]

/-- The differential test is sound and complete AGAINST THE CERTIFIED OPTIMUM: a candidate
    agrees with the interpreted spec on `i` iff its answer is the certified maximum profit.
    The loop's test leg now rests on this theorem, not on the transcription of `specFn`. -/
theorem agree_iff (p : ProgEval.Prog (ProgEval.SL Int) Int) (i : Inst) :
    agree p i = true ↔ progAnswer p i = LC121.solveFn (LC121.ofList i.first i.rest) := by
  show (specAnswer i == [progAnswer p i]) = true ↔ _
  rw [specAnswer_eq]
  constructor
  · intro h
    have h2 := beq_iff_eq.mp h
    injection h2 with h3 _
    exact h3.symm
  · intro h
    rw [h]
    exact beq_iff_eq.mpr rfl

/-! ### The certified program provably passes — closing the loop's test leg -/

theorem toSnoc_foldl : ∀ (rest : List Int) (acc : ProgEval.SL Int),
    toSnoc (rest.foldl ProgEval.SL.snoc acc) = rest.foldl SnocList.snoc (toSnoc acc)
  | [], _ => rfl
  | p :: rest, acc => toSnoc_foldl rest (ProgEval.SL.snoc acc p)

theorem toSnoc_slOf (first : Int) (rest : List Int) :
    toSnoc (ProgEval.slOf first rest) = LC121.ofList first rest :=
  toSnoc_foldl rest (ProgEval.SL.wrap first)

/-- The derived program's answer IS the certified maximum, in the tester's own vocabulary. -/
theorem prog_answer_certified (i : Inst) :
    progAnswer ProgEval.prog121 i = LC121.solveFn (LC121.ofList i.first i.rest) := by
  show ProgEval.evalP ProgEval.prog121 (ProgEval.slOf i.first i.rest) = _
  rw [← winner_eq_prog121, tested_eq_certified, toSnoc_slOf, foldFn_eq_L121]
  rfl

/-- The winner provably passes the differential test on EVERY instance — the loop's
    acceptance of the certified shape is a theorem, not 36 numeric coincidences. -/
theorem winner_agree (i : Inst) : agree winnerProg i = true :=
  (agree_iff winnerProg i).mpr (by rw [winner_eq_prog121]; exact prog_answer_certified i)

theorem winner_passes (insts : List Inst) : passes winnerProg insts = true :=
  List.all_eq_true.mpr fun i _ => winner_agree i

/-- **Both evaluators agree — now a THEOREM on every instance** (upgrading `RelInterp`'s
    single kernel-checked example): the exponential interpreted spec `Λ spec ≫ max D` and the
    polynomial derived-program fold return the same answer, because both provably equal the
    certified maximum. -/
theorem evaluators_agree (i : Inst) : specAnswer i = [progAnswer ProgEval.prog121 i] := by
  rw [specAnswer_eq, prog_answer_certified]

-- The certified selected program, run on LeetCode 121's own example:
#eval ProgEval.evalP winnerProg (ProgEval.slOf 7 [1, 5, 3, 6, 4])   -- 5

#print axioms selected_correct
#print axioms solve_eq_est
#print axioms loop_verdicts
#print axioms specFn_transport
#print axioms specAnswer_eq
#print axioms agree_iff
#print axioms winner_passes
#print axioms evaluators_agree

end Freyd.Alg.Search
