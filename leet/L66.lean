/-
  LeetCode 66 — Plus One — as an ALLEGORY PROGRAM.

  Problem: a non-negative integer is given as a digit list `0..9`, MOST-significant digit first
  (big-endian), e.g. `[1,2,3]` denotes `123`.  Return the digit list of the integer plus one.

  1. **Value semantics.** `value : List Int → Int` reads a BIG-ENDIAN digit list back into the
     integer it denotes, via a left fold (Horner's method): `value xs := xs.foldl (fun acc d =>
     acc*10+d) 0`.  Internally the program works LITTLE-ENDIAN (least-significant digit first,
     matching `L2`'s `value`), where `valueLE (d :: ds) = d + 10 * valueLE ds` — the carry ripples
     by consing at the front, structural recursion, no fuel needed (contrast `L2`'s two-input
     carry-ripple, which genuinely needs fuel).

  2. **Program.** `plusOneRev : List Int → List Int` increments the REVERSED (little-endian)
     digits with carry: `[] ↦ [1]` (a fresh leading `1` past an empty number); `d :: ds ↦ if
     d + 1 = 10 then 0 :: plusOneRev ds else (d+1) :: ds` (roll over to `0` and carry into `ds`, or
     just bump the digit and stop).  `plusOneFn xs := (plusOneRev xs.reverse).reverse` undoes the
     endianness flip.

  3. **The bridge `value = valueLE ∘ reverse`.** Core `List.foldl_eq_foldr_reverse` turns the
     big-endian LEFT fold into a RIGHT fold over the reversed list with the flipped step
     `fun d acc => acc*10+d`; a one-line induction (`foldr_eq_valueLE`) then identifies that right
     fold with `valueLE`'s own (front-consing) recursion — no explicit powers of `10`, no append
     lemmas, since both sides recurse the SAME way (front-to-back on the little-endian list).

  4. **The carry lemma is UNCONDITIONAL.** `valueLE_plusOneRev : valueLE (plusOneRev ds) = valueLE
     ds + 1` needs NO digit-range hypothesis (`0 ≤ d ≤ 9`): the non-carry branch (`d+1 ≠ 10`) is a
     pure algebraic rearrangement for ANY `d`, and the carry branch consumes `d + 1 = 10` (from the
     `if`'s own condition) directly, so `0..9`-ness of the input digits is never needed for VALUE
     preservation — it only matters for reading the output as a conventional digit list (not
     claimed here, matching `L2`'s scope).

  Mathlib-free; fully constructive (no `Classical.choice` expected).
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC66

open Freyd

/-! ## Value semantics -/

/-- `value xs` reads a BIG-ENDIAN digit list (most-significant digit first) back into the integer
    it denotes, via a left fold (Horner's method): `value [1,2,3] = ((0*10+1)*10+2)*10+3 = 123`. -/
def value (xs : List Int) : Int := xs.foldl (fun acc d => acc * 10 + d) 0

/-- `valueLE ys` reads a LITTLE-ENDIAN digit list (least-significant digit first) back into the
    integer it denotes: `valueLE [] = 0`, `valueLE (d :: ds) = d + 10 * valueLE ds` — literally
    `L2.value`, restated here so this file stays self-contained (a different problem, not a
    wrapper around `L2`). -/
def valueLE : List Int → Int
  | [] => 0
  | d :: ds => d + 10 * valueLE ds

/-- **The bridge, crux half**: `value`'s left fold, once flipped to a right fold over the SAME
    (little-endian) list by `foldl_eq_foldr_reverse`, computes exactly `valueLE` — both recurse
    front-to-back on `ys`, so the step functions line up by one `omega` per cons, no powers. -/
theorem foldr_eq_valueLE : ∀ ys : List Int, ys.foldr (fun d acc => acc * 10 + d) 0 = valueLE ys
  | [] => rfl
  | d :: ds => by
      have ih := foldr_eq_valueLE ds
      show (ds.foldr (fun d acc => acc * 10 + d) 0) * 10 + d = valueLE (d :: ds)
      rw [ih]; simp only [valueLE]; omega

/-- **The bridge**: a big-endian value equals the little-endian value of the REVERSED list. -/
theorem value_eq_valueLE_reverse (xs : List Int) : value xs = valueLE xs.reverse := by
  show xs.foldl (fun acc d => acc * 10 + d) 0 = valueLE xs.reverse
  rw [List.foldl_eq_foldr_reverse]
  exact foldr_eq_valueLE xs.reverse

/-! ## Program: increment the little-endian (reversed) digits with carry, then flip back -/

/-- Increment a LITTLE-ENDIAN digit list by one, rippling a carry through leading (in this
    orientation) `9`s: `[] ↦ [1]`, `d :: ds ↦` roll to `0` and carry into `ds` if `d+1=10`, else
    just bump `d`. Plain structural recursion — no fuel (contrast `L2`'s two-input carry-ripple). -/
def plusOneRev : List Int → List Int
  | [] => [1]
  | d :: ds => if d + 1 = 10 then 0 :: plusOneRev ds else (d + 1) :: ds

/-- **The program**: increment a BIG-ENDIAN digit list by one — reverse to little-endian, ripple
    the carry, reverse back. -/
def plusOneFn (xs : List Int) : List Int := (plusOneRev xs.reverse).reverse

/-! ## Correctness: value preservation -/

/-- **The carry lemma, UNCONDITIONAL on digit range**: incrementing the little-endian list bumps
    its value by exactly `1`. The non-carry branch is algebra for any `d`; the carry branch
    consumes `d + 1 = 10` from the `if`'s own condition — no `0 ≤ d ≤ 9` hypothesis needed. -/
theorem valueLE_plusOneRev : ∀ ds : List Int, valueLE (plusOneRev ds) = valueLE ds + 1
  | [] => by simp only [plusOneRev, valueLE]; omega
  | d :: ds => by
      by_cases hd : d + 1 = 10
      · have ih := valueLE_plusOneRev ds
        simp only [plusOneRev, if_pos hd, valueLE] at ih ⊢
        omega
      · simp only [plusOneRev, if_neg hd, valueLE]
        omega

/-- **Correctness of the allegory program** (the headline theorem): `plusOneFn` preserves value
    plus one — the digit list of `value xs + 1`. Fully general, no digit-range hypothesis. -/
theorem plusOne_correct (xs : List Int) : value (plusOneFn xs) = value xs + 1 := by
  show value ((plusOneRev xs.reverse).reverse) = value xs + 1
  rw [value_eq_valueLE_reverse, List.reverse_reverse, valueLE_plusOneRev,
    ← value_eq_valueLE_reverse]

/-! ## `Rel(Set)` packaging -/

/-- The input/output object: big-endian digit lists. -/
abbrev dDigits : RelSet.{0} := ⟨List Int⟩

/-- **The allegory program**: LeetCode 66's plus-one as a morphism `dDigits ⟶ dDigits` in
    `Rel(Set)`. -/
def solve : dDigits ⟶ dDigits := graph plusOneFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map plusOneFn

/-! ## The morphism-equation headline: canonicity pins the digit list

  The value equation alone does NOT pin the output (`[1,2,4]` and `[0,1,2,4]` both denote `124`).
  A big-endian numeral is CANONICAL iff its little-endian reverse is `Canon` — digits in `[0,10)`
  and no most-significant zero.  A fixed value has a unique canonical little-endian list
  (`canon_unique`), and `plusOneRev` maps canonical inputs to canonical outputs, so on canonical
  inputs `solve` is pinned to the unique canonical digit list of `value + 1`. -/

/-- A little-endian digit list is `Canon`: digits in `[0,10)` and no most-significant (last) zero.
    (`getLast? = none` on `[]`, so the empty list — the canonical zero — counts as canonical.) -/
def Canon (ds : List Int) : Prop := (∀ d ∈ ds, 0 ≤ d ∧ d < 10) ∧ ds.getLast? ≠ some 0

/-- `plusOneRev` never returns the empty list — both branches emit at least one digit. -/
theorem plusOneRev_ne_nil : ∀ ds : List Int, plusOneRev ds ≠ []
  | [] => by simp [plusOneRev]
  | d :: ds => by rw [plusOneRev]; split <;> simp

/-- Consing onto a NONEMPTY list leaves the last digit unchanged. -/
theorem getLast?_cons_ne {a : Int} {l : List Int} (h : l ≠ []) : (a :: l).getLast? = l.getLast? := by
  cases l with
  | nil => exact absurd rfl h
  | cons b bs => rw [List.getLast?_cons_cons]

theorem canon_tail {d : Int} {ds : List Int} (h : Canon (d :: ds)) : Canon ds := by
  refine ⟨fun x hx => h.1 x (List.mem_cons_of_mem d hx), ?_⟩
  cases ds with
  | nil => simp
  | cons e es => have h2 := h.2; rw [List.getLast?_cons_cons] at h2; exact h2

/-- A nonempty `Canon` list denotes a strictly positive value — the top digit being nonzero rules
    out `0`. -/
theorem valueLE_pos {ds : List Int} (h : Canon ds) (hne : ds ≠ []) : 0 < valueLE ds := by
  induction ds with
  | nil => exact absurd rfl hne
  | cons d ds ih =>
    have hd := h.1 d List.mem_cons_self
    cases ds with
    | nil =>
      have hdz : d ≠ 0 := by intro hh; apply h.2; rw [hh]; rfl
      have : valueLE [d] = d := by simp [valueLE]
      omega
    | cons e es =>
      have hpos := ih (canon_tail h) (by simp)
      have hval : valueLE (d :: e :: es) = d + 10 * valueLE (e :: es) := rfl
      omega

/-- **Canonical uniqueness**: a fixed value has at most one canonical little-endian digit list —
    the low digit is `value % 10`, so both lists share a head and (by IH) a tail. -/
theorem canon_unique : ∀ (ds es : List Int), Canon ds → Canon es → valueLE ds = valueLE es → ds = es := by
  intro ds
  induction ds with
  | nil =>
    intro es _ hce hv
    cases es with
    | nil => rfl
    | cons e es' =>
      exfalso
      have hpos : 0 < valueLE (e :: es') := valueLE_pos hce (by simp)
      have hz : valueLE (e :: es') = 0 := hv.symm
      omega
  | cons d ds ih =>
    intro es hcd hce hv
    cases es with
    | nil =>
      exfalso
      have hpos : 0 < valueLE (d :: ds) := valueLE_pos hcd (by simp)
      have hz : valueLE (d :: ds) = 0 := hv
      omega
    | cons e es' =>
      have hd := hcd.1 d List.mem_cons_self
      have he := hce.1 e List.mem_cons_self
      have hvv : d + 10 * valueLE ds = e + 10 * valueLE es' := hv
      have hde : d = e := by omega
      have htail : valueLE ds = valueLE es' := by omega
      rw [hde, ih es' (canon_tail hcd) (canon_tail hce) htail]

/-- **`plusOneRev` preserves canonicity**: incrementing a canonical little-endian list yields a
    canonical one — the carry ripple never creates a most-significant zero (a top `9` rolls to
    `0` only with a fresh `1` above it). -/
theorem plusOneRev_canon : ∀ ds : List Int, Canon ds → Canon (plusOneRev ds)
  | [], _ => ⟨by intro x hx; rcases List.mem_singleton.mp hx with rfl; exact ⟨by omega, by omega⟩, by rw [plusOneRev]; simp⟩
  | d :: ds, h => by
      have hd := h.1 d List.mem_cons_self
      by_cases hc : d + 1 = 10
      · -- top `9` carries: `0 :: plusOneRev ds`
        have ihc := plusOneRev_canon ds (canon_tail h)
        rw [plusOneRev, if_pos hc]
        refine ⟨?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact ⟨by omega, by omega⟩
          · exact ihc.1 x hx'
        · rw [getLast?_cons_ne (plusOneRev_ne_nil ds)]; exact ihc.2
      · -- no carry at the top: `(d+1) :: ds`
        rw [plusOneRev, if_neg hc]
        refine ⟨?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact ⟨by omega, by omega⟩
          · exact h.1 x (List.mem_cons_of_mem d hx')
        · cases ds with
          | nil => simp only [List.getLast?_singleton, ne_eq, Option.some.injEq]; omega
          | cons e es => rw [List.getLast?_cons_cons]; exact (canon_tail h).2

/-- The precondition coreflexive: the sub-identity passing only canonical big-endian numerals
    (digits in `[0,10)`, no leading zero — LeetCode 66's input format, bar the degenerate `[0]`). -/
def pre : dDigits ⟶ dDigits := fun xs ys => xs = ys ∧ Canon xs.reverse

/-- **The specification** as a morphism `dDigits ⟶ dDigits`: on a canonical input, `out` is the
    canonical big-endian digit list (its reverse is `Canon`) whose value is `value xs + 1` — stated
    independently of `plusOneFn`. -/
def spec : dDigits ⟶ dDigits :=
  fun xs out => Canon xs.reverse ∧ Canon out.reverse ∧ value out = value xs + 1

/-- **The allegory-program headline**: `pre ≫ solve = spec` — on canonical inputs, `plusOneFn` is
    exactly the canonical digit list of `value + 1`, pinned by `canon_unique` (value + canonicity),
    not merely value-correct. -/
theorem pre_solve_eq_spec : pre ≫ solve = spec := by
  apply hom_ext; intro xs out
  constructor
  · rintro ⟨ys, ⟨rfl, hcin⟩, hv⟩
    have hv' : out = plusOneFn xs := hv
    refine ⟨hcin, ?_, ?_⟩
    · rw [hv']
      show Canon (plusOneRev xs.reverse).reverse.reverse
      rw [List.reverse_reverse]; exact plusOneRev_canon xs.reverse hcin
    · rw [hv']; exact plusOne_correct xs
  · rintro ⟨hcin, hcout, hval⟩
    refine ⟨xs, ⟨rfl, hcin⟩, ?_⟩
    show out = plusOneFn xs
    have hco : Canon (plusOneFn xs).reverse := by
      show Canon (plusOneRev xs.reverse).reverse.reverse
      rw [List.reverse_reverse]; exact plusOneRev_canon xs.reverse hcin
    have hveq : valueLE out.reverse = valueLE (plusOneFn xs).reverse := by
      rw [← value_eq_valueLE_reverse, ← value_eq_valueLE_reverse, hval, plusOne_correct]
    have heq := canon_unique out.reverse (plusOneFn xs).reverse hcout hco hveq
    have := congrArg List.reverse heq
    rwa [List.reverse_reverse, List.reverse_reverse] at this

/-! ## Running the program -/

example : plusOneFn ([1, 2, 3] : List Int) = [1, 2, 4] := by decide
example : plusOneFn ([9, 9] : List Int) = [1, 0, 0] := by decide

end Freyd.Alg.RelSet.LC66
