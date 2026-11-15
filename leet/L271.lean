/-
  LeetCode 271 — Encode and Decode Strings — as an ALLEGORY PROGRAM.

  Problem: encode a LIST of strings into a single flat string (here: `List Int`, char codes) so it
  can be decoded back unambiguously; the whole input is `List (List Int)`, the flat encoding a
  single `List Int`.

  Route: length-prefix encoding + a fuel parser (the S13/S30 playbook). `encode` is a plain
  structural fold (a `Map` `dStrs ⟶ dTokens` in `Rel(Set)`, `AOP.A6_1_RelSet`); `decodeFn` its
  retraction, and the headline theorem is a SECTION–RETRACTION identity —
  `graph encode ≫ graph decodeFn = graph Option.some` — i.e. `decodeFn` recovers exactly the list
  that was encoded.

  1. **Encode.** `encode1 s := s.length :: s` (emit the length as one `Int` token, then the chars);
     `encode strs := strs.flatMap encode1`. Positional decoding is unambiguous because the FIRST
     token of every string block is always a length (chars may be any `Int` — no delimiter or
     escaping is needed, unlike a comma/quote scheme).

  2. **Decode.** `decodeFuel` reads the head `n` as a length, `take`/`drop`s the next `n.toNat`
     chars off the tail as one string, and recurses on the drop, fuelled by an explicit `Nat` (the
     S13 trick) since `List.drop` of a computed length is not a structural subterm — genuine
     well-founded recursion in disguise. `[] ↦ some []` (nothing left to parse); fuel exhausted
     with tokens still pending, or a length exceeding the remaining tokens, `↦ none` (malformed).

  3. **Correctness — DELIBERATELY NOT an L297-style "any trailing `rest`" generalization.** Unlike
     `Tree`'s preorder listing, THIS encoding has no self-delimiting marker for "list of strings
     ends here": nothing stops a sufficiently-fuelled `decodeFuel` from treating trailing garbage
     appended after a valid `encode strs` as MORE strings. Concretely, `decodeFuel 1
     (encode [] ++ [0]) = some [[]]`, not `some []` — a fuel-slack-plus-arbitrary-trailing-tokens
     lemma of the L297 shape is FALSE here (verified by `#eval` before writing this proof). The
     honest, provable statement fixes the trailing content at `[]` throughout the induction:
     `decode_encode : ∀ strs fuel, (encode strs).length ≤ fuel → decodeFuel fuel (encode strs) =
     some strs`, by structural induction on `strs`. The `cons` case rewrites
     `encode (s :: rest') = s.length :: (s ++ encode rest')` (`flatMap_cons` + `cons_append`), so
     `take`/`drop` at `s.length` (`List.take_left`/`drop_left`) recover `s` and leave exactly
     `encode rest'` — no extra trailing tokens ever appear inside the recursion, so the leftover
     never needs to be threaded or generalized. `round_trip` specializes at
     `fuel := (encode strs).length + 1`, trivially sufficient (`n ≤ n + 1`) since `decodeFn`'s
     fuel choice already bounds `(encode strs).length` by construction.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC271

open Freyd

/-! ## The program, part 1: `encode` — a length-prefix listing, a plain structural fold -/

/-- One string, length-prefixed: `s.length :: s`. Chars may be any `Int`, so the length prefix is
    the only "delimiter" needed — there is nothing to escape. -/
def encode1 (s : List Int) : List Int := (s.length : Int) :: s

/-- **The allegory program's first half**: flatten a list of strings by length-prefixing each one
    and concatenating. A plain structural fold (`List.flatMap`). -/
def encode (strs : List (List Int)) : List Int := strs.flatMap encode1

/-! ## The program, part 2: `decodeFuel` — a length-prefix parse, needs FUEL (S13)

  `List.drop` of a computed length is not a structural subterm of the token list, so plain
  structural recursion does not see the recursive call as terminating. `decodeFuel` tames it with
  an explicit fuel bound, recursing structurally on `fuel` alone. -/

/-- `decodeFuel fuel ts` — parse a whole run of length-prefixed strings off the front of `ts`;
    `none` on malformed input (a claimed length exceeding the remaining tokens) or exhausted fuel
    with tokens still pending. `fuel` bounds the number of strings the parse is allowed to peel. -/
def decodeFuel : Nat → List Int → Option (List (List Int))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, n :: rest =>
    if n.toNat ≤ rest.length then
      match decodeFuel fuel (rest.drop n.toNat) with
      | none => none
      | some strs => some (rest.take n.toNat :: strs)
    else none

/-- **The allegory program's second half**: parse a whole token list, fuelled by its own length
    (always sufficient for a token list that came from `encode` — `round_trip` below). -/
def decodeFn (ts : List Int) : Option (List (List Int)) := decodeFuel (ts.length + 1) ts

/-! ## Correctness: the parser inverts the printer -/

/-- **The round-trip lemma**: given fuel at least `(encode strs).length`, `decodeFuel` applied to
    `encode strs` reconstructs `strs` exactly. Structural induction on `strs`; the `cons` case
    regroups `encode (s :: rest') = s.length :: (s ++ encode rest')` so `take`/`drop` at `s.length`
    recover `s` and leave exactly `encode rest'` — never any extra trailing content (see the file
    header on why an L297-style "any trailing `rest`" generalization is false here). -/
theorem decode_encode : ∀ (strs : List (List Int)) (fuel : Nat),
    (encode strs).length ≤ fuel → decodeFuel fuel (encode strs) = some strs
  | [], fuel, _ => by
    show decodeFuel fuel (encode ([] : List (List Int))) = some []
    simp only [encode, List.flatMap_nil]
    cases fuel <;> rfl
  | s :: rest', fuel, hf => by
    have heq : encode (s :: rest') = (s.length : Int) :: (s ++ encode rest') := by
      show List.flatMap encode1 (s :: rest') = _
      rw [List.flatMap_cons]
      show ((s.length : Int) :: s) ++ encode rest' = _
      rw [List.cons_append]
    have hlen : (encode (s :: rest')).length = 1 + s.length + (encode rest').length := by
      rw [heq]; simp only [List.length_cons, List.length_append]; omega
    cases fuel with
    | zero => exfalso; omega
    | succ fuel' =>
      have hfuel' : (encode rest').length ≤ fuel' := by omega
      have hcond : ((s.length : Int)).toNat ≤ (s ++ encode rest').length := by
        rw [Int.toNat_natCast]; simp only [List.length_append]; omega
      rw [heq]
      show (if ((s.length : Int)).toNat ≤ (s ++ encode rest').length then
              match decodeFuel fuel' ((s ++ encode rest').drop ((s.length : Int)).toNat) with
              | none => none
              | some strs => some ((s ++ encode rest').take ((s.length : Int)).toNat :: strs)
            else none) = some (s :: rest')
      rw [if_pos hcond, Int.toNat_natCast, List.take_left, List.drop_left,
        decode_encode rest' fuel' hfuel']

/-- **The headline theorem**: decoding the encoding of ANY list of strings recovers that list
    exactly. Specializes `decode_encode` at `fuel := (encode strs).length + 1`, which `decodeFn`
    always uses — trivially sufficient (`n ≤ n + 1`). -/
theorem round_trip (strs : List (List Int)) : decodeFn (encode strs) = some strs := by
  show decodeFuel ((encode strs).length + 1) (encode strs) = some strs
  exact decode_encode strs _ (Nat.le_succ _)

/-! ## `Rel(Set)` framing: `encode` is a section, `decodeFn` its retraction -/

abbrev dStrs : RelSet.{0} := ⟨List (List Int)⟩
abbrev dTokens : RelSet.{0} := ⟨List Int⟩
abbrev dOStrs : RelSet.{0} := ⟨Option (List (List Int))⟩

/-- **The allegory program's first half**: `encode` as a `Map` `dStrs ⟶ dTokens`. -/
def solveEnc : dStrs ⟶ dTokens := graph encode
/-- `solveEnc` is a `Map` (it is the graph of a function). -/
theorem solveEnc_map : Map solveEnc := graph_map encode

/-- **The allegory program's second half**: `decodeFn` as a `Map` `dTokens ⟶ dOStrs`. -/
def solveDec : dTokens ⟶ dOStrs := graph decodeFn
/-- `solveDec` is a `Map` (it is the graph of a function). -/
theorem solveDec_map : Map solveDec := graph_map decodeFn

/-- **Section–retraction identity**: composing `encode` then `decodeFn` is exactly
    `some : List (List Int) → Option (List (List Int))` — `decodeFn` recovers exactly the list
    that was encoded, no more, no less. The `Rel(Set)` restatement of `round_trip`. -/
theorem section_retraction : solveEnc ≫ solveDec = graph (fun strs => some strs) := by
  apply hom_ext; intro strs ostrs
  show (∃ ts, ts = encode strs ∧ ostrs = decodeFn ts) ↔ ostrs = some strs
  constructor
  · rintro ⟨ts, rfl, rfl⟩; exact round_trip strs
  · rintro rfl; exact ⟨encode strs, rfl, (round_trip strs).symm⟩

/-! ## Running the program -/

-- An empty string in the list exercises the `n = 0` case.
example : decodeFn (encode [[104, 105], []]) = some [[104, 105], []] := by decide
-- A single-string case.
example : decodeFn (encode [[72, 101, 108, 108, 111]]) = some [[72, 101, 108, 108, 111]] := by
  decide

end Freyd.Alg.RelSet.LC271
