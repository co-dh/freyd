/-
  LeetCode 205 — Isomorphic Strings — DERIVED as a HIGHER-ORDER (lockstep) cons-list catamorphism,
  now backed by TWO HASH MAPS for `O(n)` EXPECTED time (was `O(n²)` with association-list scans).

  `leet/L205.lean` writes the two-input scan `isoGo mapST mapTS s t : Bool` by hand, threading two
  ASSOCIATION LISTS `mapST`/`mapTS`; each `lookupL` is a linear scan, so the whole pass is `O(n²)`.
  Here we replace the two association lists with two `Freyd.HashMap.AHashMap Int` (`fwd : s→t`,
  `bwd : t→s`).  The scan `isoGoH fwd bwd s t` does the SAME control flow, but every step is one
  `find?` and (in the fresh case) two `insert`s — each `O(1)` EXPECTED (a chaining hash map, one
  bucket of expected `O(1)` length), so the whole pass is `O(n)` EXPECTED.

  The AOP story is unchanged.  A two-list, state-threading scan is not a catamorphism over one list —
  until you CURRY it.  Read `isoGoH fwd bwd s t` as `s ↦ (fwd bwd t ↦ …)`: folding the FIRST list `s`
  produces a RESIDUAL decision procedure

      `Resid := AHashMap Int → AHashMap Int → List Int → Bool`

  that still awaits the two maps and the second list `t`.  With this FUNCTION carrier the accumulator
  scan collapses to an ordinary front-to-back cons-list fold, exposed by the general-carrier
  fold-uniqueness law `CL.consFold_unique` (`AOP/A6_GenFold.lean`).  We reshape `s` onto
  `ConsList Unit Int` (`ofList`), mirror the curried scan as `foldCL : ConsList Unit Int → Resid`,
  and its two defining equations hold by `rfl`, so `CL.consFold_unique g step foldCL rfl rfl` PRODUCES
  the higher-order catamorphism `cataR (consScalarAlg g step)` and identifies it with `graph foldCL`
  (`iso_emerges`): the curried hash-map scan is not written, it emerges.

  CORRECTNESS is REUSED from `L205`, not re-proved.  The hash maps `find?`-MODEL the association lists
  exactly: `models_empty` says `mkHashMap` models `[]`, and `models_insert` says `insert m x y` models
  `(x,y) :: al` (both by `find?_insert_self`/`find?_insert_other`).  One induction (`isoGoH_eq`) then
  shows `isoGoH fwd bwd s t = isoGo mapST mapTS s t` whenever the maps model the lists, so at the
  initial empty maps `hashIso s t = isIsoFn s t` and `L205.iso_correct` (the two-way map-scan decision
  `iff`, NOT re-proved here) transports onto the emergent fold (`iso_derived_correct`).

  Mathlib-free; axioms of the headline ⊆ {propext, Quot.sound}.  We route through `cataFold` /
  `consFold_unique` only, never the `cataR_eq_relCata` bridge (which pulls `Classical.choice`), and
  the map lemmas use `beq_iff_eq` / `of_decide_eq_*` (never `beq_self_eq_true`) to stay constructive.
-/
import AOP.A6_GenFold
import AOP.A6_ConsList
import AOP.A6_HashMap
import leet.L205

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Freyd.Alg.RelSet.LC205D

open Freyd Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.LC205
open Freyd.HashMap (AHashMap mkHashMap find? find?_insert_self find?_insert_other find?_mkHashMap)

/-! ## The efficient program: the two-way consistency scan over TWO HASH MAPS

  Identical control flow to `L205.isoGo`, but `mapST`/`mapTS : List (Int × Int)` become
  `fwd`/`bwd : AHashMap Int` and `lookupL`/`(· :: ·)` become `find?`/`insert` — each `O(1)`
  expected instead of an `O(n)` list scan. -/

/-- `isoGoH fwd bwd s t` — the two-way consistency scan.  `fwd` maps each seen `s`-value to its
    paired `t`-value; `bwd` is the converse.  At a pair `(x, y)`: if both are seen, accept iff the
    recorded partners agree; if both fresh, `insert` the new pair in both maps and continue; any other
    combination rejects.  Every step is one `find?` + (fresh case) two `insert`s = `O(1)` expected. -/
def isoGoH (fwd bwd : AHashMap Int) : List Int → List Int → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    match find? fwd x, find? bwd y with
    | some y1, some x1 => decide (y1 = y) && decide (x1 = x) && isoGoH fwd bwd xs ys
    | none,    none    => isoGoH (Freyd.HashMap.insert fwd x y) (Freyd.HashMap.insert bwd y x) xs ys
    | some _,  none    => false
    | none,    some _  => false

/-! ## The maps `find?`-MODEL the association lists exactly -/

/-- A hash map MODELS an association list when `find?` and `lookupL` agree at every key. -/
def Models (m : AHashMap Int) (al : List (Int × Int)) : Prop :=
  ∀ k, find? m k = lookupL k al

/-- The empty hash map models the empty association list. -/
theorem models_empty (n : Nat) : Models (mkHashMap Int n) [] := by
  intro k; rw [find?_mkHashMap]; rfl

/-- `insert m x y` models `(x, y) :: al` whenever `m` models `al` — the model is maintained across the
    fresh-pair step.  Constructive case split via `of_decide_eq_*` (no classical choice). -/
theorem models_insert {m : AHashMap Int} {al : List (Int × Int)} {x y : Int}
    (h : Models m al) : Models (Freyd.HashMap.insert m x y) ((x, y) :: al) := by
  intro k
  cases hd : decide (k = x) with
  | true =>
    have hk : k = x := of_decide_eq_true hd
    subst hk
    rw [find?_insert_self,
        show lookupL k ((k, y) :: al) = if k = k then some y else lookupL k al from rfl,
        if_pos rfl]
  | false =>
    have hk : k ≠ x := of_decide_eq_false hd
    rw [find?_insert_other _ _ _ _ hk, h k]
    simp only [lookupL]
    rw [if_neg (fun he : x = k => hk he.symm)]

/-! ## Bridge: the hash scan equals the association-list scan whenever the maps model the lists -/

/-- **The hash-map scan computes the same decision as `L205.isoGo`.**  ONE induction on the first list
    `s`: at each pair the two maps `find?`-model the two association lists, so `find? fwd x` matches
    `lookupL x mapST` and `find? bwd y` matches `lookupL y mapTS`; the fresh step preserves the model
    (`models_insert`), the seen step keeps it. -/
theorem isoGoH_eq : ∀ (s : List Int) (fwd bwd : AHashMap Int)
    (mapST mapTS : List (Int × Int)) (t : List Int),
    Models fwd mapST → Models bwd mapTS →
    isoGoH fwd bwd s t = isoGo mapST mapTS s t := by
  intro s
  induction s with
  | nil =>
    intro fwd bwd mapST mapTS t hf hb
    cases t <;> rfl
  | cons x xs ih =>
    intro fwd bwd mapST mapTS t hf hb
    cases t with
    | nil => rfl
    | cons y ys =>
      have hfx := hf x
      have hby := hb y
      show isoGoH fwd bwd (x :: xs) (y :: ys) = isoGo mapST mapTS (x :: xs) (y :: ys)
      rcases hlx : lookupL x mapST with _ | y1 <;> rcases hly : lookupL y mapTS with _ | x1 <;>
        rw [hlx] at hfx <;> rw [hly] at hby
      · -- both fresh: push a new pair into both maps, model preserved by `models_insert`
        have e1 : isoGoH fwd bwd (x :: xs) (y :: ys)
            = isoGoH (Freyd.HashMap.insert fwd x y) (Freyd.HashMap.insert bwd y x) xs ys := by
          simp only [isoGoH, hfx, hby]
        have e2 : isoGo mapST mapTS (x :: xs) (y :: ys)
            = isoGo ((x, y) :: mapST) ((y, x) :: mapTS) xs ys := by
          simp only [isoGo, hlx, hly]
        rw [e1, e2]
        exact ih (Freyd.HashMap.insert fwd x y) (Freyd.HashMap.insert bwd y x)
          ((x, y) :: mapST) ((y, x) :: mapTS) ys (models_insert hf) (models_insert hb)
      · -- `x` fresh, `y` seen: both reject
        have e1 : isoGoH fwd bwd (x :: xs) (y :: ys) = false := by simp only [isoGoH, hfx, hby]
        have e2 : isoGo mapST mapTS (x :: xs) (y :: ys) = false := by simp only [isoGo, hlx, hly]
        rw [e1, e2]
      · -- `x` seen, `y` fresh: both reject
        have e1 : isoGoH fwd bwd (x :: xs) (y :: ys) = false := by simp only [isoGoH, hfx, hby]
        have e2 : isoGo mapST mapTS (x :: xs) (y :: ys) = false := by simp only [isoGo, hlx, hly]
        rw [e1, e2]
      · -- both seen: accept iff recorded partners agree, maps unchanged (model kept)
        have e1 : isoGoH fwd bwd (x :: xs) (y :: ys)
            = (decide (y1 = y) && decide (x1 = x) && isoGoH fwd bwd xs ys) := by
          simp only [isoGoH, hfx, hby]
        have e2 : isoGo mapST mapTS (x :: xs) (y :: ys)
            = (decide (y1 = y) && decide (x1 = x) && isoGo mapST mapTS xs ys) := by
          simp only [isoGo, hlx, hly]
        rw [e1, e2, ih fwd bwd mapST mapTS ys hf hb]

/-- **The `O(n)`-expected program**: run the two-hash-map scan from empty maps sized to the input
    (`s.length` buckets ⟹ `O(1)` expected per op ⟹ `O(n)` expected overall). -/
def hashIso (s t : List Int) : Bool :=
  isoGoH (mkHashMap Int s.length) (mkHashMap Int s.length) s t

/-- The hash scan decides EXACTLY as `L205.isIsoFn` — same decision, faster.  Empty maps model empty
    association lists (`models_empty`), so `isoGoH_eq` collapses `hashIso s t` to `isoGo [] [] s t`. -/
theorem hashIso_eq (s t : List Int) : hashIso s t = isIsoFn s t := by
  unfold hashIso isIsoFn
  exact isoGoH_eq s _ _ [] [] t (models_empty s.length) (models_empty s.length)

/-! ## The residual carrier and the base/step, READ OFF `isoGoH` (curried on the maps and `t`) -/

/-- The higher-order carrier: a decision procedure awaiting both hash maps and the second list. -/
abbrev Resid : Type := AHashMap Int → AHashMap Int → List Int → Bool

/-- The base of the emergent algebra: the residual after folding the EMPTY first list — accepts iff
    the second list is also empty (the maps are irrelevant at the base). -/
def g : Unit → Resid := fun _ fwd bwd t =>
  match t with
  | []     => true
  | _ :: _ => false

/-- The step of the emergent algebra: from the tail's residual `rec` and the current `s`-head `x`,
    the parent's residual answers `y :: ys` by the `isoGoH` head logic — `find? fwd x`, `find? bwd y`;
    both fresh ⟹ `insert` both maps and hand `ys` to `rec`; both seen ⟹ accept iff partners agree and
    hand `ys` to `rec`; any mismatch rejects; `[]` rejects. -/
def step : Int → Resid → Resid := fun x rec fwd bwd t =>
  match t with
  | []      => false
  | y :: ys =>
    match find? fwd x, find? bwd y with
    | some y1, some x1 => decide (y1 = y) && decide (x1 = x) && rec fwd bwd ys
    | none,    none    => rec (Freyd.HashMap.insert fwd x y) (Freyd.HashMap.insert bwd y x) ys
    | some _,  none    => false
    | none,    some _  => false

/-- The curried hash scan as a cons-list fold, defined FROM `g`/`step` so `consFold_unique` applies by
    `rfl`.  Folding `s` front-to-back into its residual decision procedure `foldCL (ofList s) : Resid`. -/
def foldCL : ConsList Unit Int → Resid
  | ConsList.wrap l    => g l
  | ConsList.cons x xs => step x (foldCL xs)

/-! ## The FORCED first-order recursion of the curried scan (both hold by `rfl`) -/

theorem hwrap : ∀ d, foldCL (ConsList.wrap d) = g d := fun _ => rfl

theorem hcons : ∀ (x : Int) (xs : ConsList Unit Int),
    foldCL (ConsList.cons x xs) = step x (foldCL xs) := fun _ _ => rfl

/-! ## The higher-order catamorphism EMERGES via the general-carrier law -/

/-- **The residual decision procedure EMERGES.**  `graph foldCL` equals the catamorphism of the
    scalar cons-list algebra `consScalarAlg g step` on the FUNCTION carrier `Resid`, PRODUCED by
    `CL.consFold_unique` from the forced base `g` and step `step`.  The two-hash-map accumulator scan
    is now a single catamorphism over the first list. -/
theorem iso_emerges :
    (graph foldCL : dCL Unit Int ⟶ ⟨Resid⟩) = cataR (consScalarAlg g step) :=
  CL.consFold_unique g step foldCL hwrap hcons

/-! ## Reshaping `List Int` onto the initial algebra, and the bridge back to `isoGoH` -/

/-- Reshape a raw list onto the front-to-back cons-list initial algebra. -/
def ofList : List Int → ConsList Unit Int
  | []      => ConsList.wrap ()
  | x :: xs => ConsList.cons x (ofList xs)

/-- **Bridge**: the emergent residual applied to the maps and the second list is exactly the concrete
    hash scan `isoGoH`.  Induction on `s`; the maps and `t` pass through unchanged in the recursive
    positions (`step` and `isoGoH` share the SAME `find?`/`insert` discriminants). -/
theorem foldCL_ofList (s : List Int) :
    ∀ (fwd bwd : AHashMap Int) (t : List Int),
      foldCL (ofList s) fwd bwd t = isoGoH fwd bwd s t := by
  induction s with
  | nil => intro fwd bwd t; cases t <;> rfl
  | cons x xs ih =>
    intro fwd bwd t
    cases t with
    | nil => rfl
    | cons y ys =>
      show step x (foldCL (ofList xs)) fwd bwd (y :: ys)
          = isoGoH fwd bwd (x :: xs) (y :: ys)
      rcases hfx : find? fwd x with _ | y1 <;> rcases hby : find? bwd y with _ | x1 <;>
        simp only [step, isoGoH, hfx, hby, ih]

/-! ## Connecting the emergent residual back to the two-input `solve` -/

/-- The derived solver: feed empty maps sized to `p.1` and the SECOND list `p.2` into the residual
    `foldCL (ofList p.1)` the emergent catamorphism produces from the first list `p.1`. -/
def derivedSolve : Input ⟶ dBool :=
  graph (fun p : List Int × List Int =>
    foldCL (ofList p.1) (mkHashMap Int p.1.length) (mkHashMap Int p.1.length) p.2)

/-- The derived solver IS `L205.solve`: fold the first list to a residual, apply it to the empty maps
    and the second list (`= isIsoFn` by the bridge and `isoGoH_eq` at the empty model). -/
theorem derivedSolve_eq_solve : derivedSolve = LC205.solve := by
  apply hom_ext; intro p b
  show (b = foldCL (ofList p.1) (mkHashMap Int p.1.length) (mkHashMap Int p.1.length) p.2)
      ↔ (b = isIsoFn p.1 p.2)
  rw [foldCL_ofList p.1 (mkHashMap Int p.1.length) (mkHashMap Int p.1.length) p.2,
      isoGoH_eq p.1 _ _ [] [] p.2 (models_empty p.1.length) (models_empty p.1.length)]
  exact Iff.rfl

/-! ## Correctness of the derived program, transported from `L205.iso_correct` -/

/-- **The Isomorphic-Strings program is the higher-order catamorphism, and it is correct.**  The
    honest headline bundles:

    * `iso_emerges` — `graph foldCL = cataR (consScalarAlg g step)`: the curried hash scan IS the
      higher-order catamorphism over the FUNCTION carrier `Resid`; and
    * the transported correctness — for ANY residual `f` the emergent fold relates the first list
      `ofList s` to, `f` fed the initial empty maps (sized to `s`) decides `IsIso` against every
      second list `t`.  Emergence pins `f = foldCL (ofList s)`; the bridge and `isoGoH_eq` reduce
      `f (mkHashMap …) (mkHashMap …) t` to `isoGo [] [] s t = isIsoFn s t`; and `L205.iso_correct`
      (the existing map-scan decision correctness, NOT re-proved here) supplies the `iff`. -/
theorem iso_derived_correct :
    ((graph foldCL : dCL Unit Int ⟶ ⟨Resid⟩) = cataR (consScalarAlg g step)) ∧
    (∀ (s : List Int) (f : Resid),
        cataFold (consScalarAlg g step) (ofList s) f →
        ∀ t : List Int,
          f (mkHashMap Int s.length) (mkHashMap Int s.length) t = true ↔ LC205.IsIso s t) := by
  refine ⟨iso_emerges, ?_⟩
  intro s f hf t
  have hgr : (graph foldCL : dCL Unit Int ⟶ ⟨Resid⟩) (ofList s) f := by
    rw [iso_emerges]; exact hf
  have hfeq : f = foldCL (ofList s) := hgr
  subst hfeq
  rw [foldCL_ofList s (mkHashMap Int s.length) (mkHashMap Int s.length) t,
      isoGoH_eq s _ _ [] [] t (models_empty s.length) (models_empty s.length)]
  exact iso_correct s t

/-! ## Running / cross-checking the emergent hash scan against `leet/L205.lean`

  `hashIso` runs the real hash-map code — `#eval` executes it via the compiled evaluator (below).
  For PROOF-level checks the kernel cannot reduce the `Array`-backed hash ops through `decide`, so we
  transport each check across `hashIso_eq` onto the kernel-reducible `isIsoFn` (`L205`) and `decide`
  THAT — establishing the SAME `Bool` value for `hashIso`.  The residual carrier is a FUNCTION type,
  so we never `decide` a residual; we separately PROVE the higher-order fold relates a first list to
  its residual. -/

-- `#eval` runs the actual O(n)-expected hash-map program:
#eval hashIso [101, 103, 103] [97, 100, 100]              -- true  ("egg" / "add")
#eval hashIso [102, 111, 111] [98, 97, 114]               -- false ("foo" / "bar")
#eval hashIso [112, 97, 112, 101, 114] [116, 105, 116, 108, 101]  -- true ("paper" / "title")

-- "egg" / "add" → true (pattern a,b,b both times)
example : hashIso [101, 103, 103] [97, 100, 100] = true := by rw [hashIso_eq]; decide
-- "foo" / "bar" → false (foo repeats, bar doesn't)
example : hashIso [102, 111, 111] [98, 97, 114] = false := by rw [hashIso_eq]; decide
-- "paper" / "title" → true (pattern a,b,a,c,d both times)
example : hashIso [112, 97, 112, 101, 114] [116, 105, 116, 108, 101] = true := by
  rw [hashIso_eq]; decide

/-- The emergent higher-order fold genuinely relates `ofList [101,103,103]` to its RESIDUAL decision
    procedure `foldCL (ofList [101,103,103]) : Resid`, proved via `iso_emerges` (no `decide` on the
    function carrier). -/
example : cataFold (consScalarAlg g step)
    (ofList [101, 103, 103]) (foldCL (ofList [101, 103, 103])) := by
  have h : (graph foldCL : dCL Unit Int ⟶ ⟨Resid⟩)
      (ofList [101, 103, 103]) (foldCL (ofList [101, 103, 103])) := rfl
  rw [iso_emerges] at h
  exact h

end Freyd.Alg.RelSet.LC205D
