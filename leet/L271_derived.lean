/-
  LeetCode 271 — Encode and Decode Strings — DERIVED as an ALGEBRA-OF-PROGRAMMING pair:
  the length-prefix ENCODER emerges as a `ConsList` CATAMORPHISM, its DECODER as a measured
  recursive-coalgebra HYLOMORPHISM, and together they satisfy a SECTION–RETRACTION identity.

  `leet/L271.lean` hand-writes `encode` (a `List.flatMap` length-prefix listing) and `decodeFn`
  (a FUELLED length-prefix parser) and proves the round-trip `decodeFn (encode strs) = some strs`.
  Here neither program is re-written; each is PRODUCED by a reusable uniqueness law and its
  correctness is REUSED from `L271.lean`.

  * **ENCODE — a catamorphism.**  `encode strs = strs.flatMap encode1` is the front-to-back fold of
    the initial algebra `ConsList Unit (List Int)` with carrier `C := List Int`, base `encG _ := []`
    and step `encSt s acc := encode1 s ++ acc` (length-prefix the head block, prepend to the encoded
    tail).  `CL.consFold_unique` emits `graph encodeCL = CL.cataR (CL.consScalarAlg encG encSt)`
    (`encode_emerges`).  Block-append fires once per block, so encode is O(N) total.

  * **DECODE — a hylomorphism.**  The parser is the DUAL of a fold: a recursive coalgebra
    `decC : List Int → Unit ⊕ (List Int × List Int)` (leaf `.inl ()` at the empty token list;
    otherwise read the head length `n` and split off the next `n.toNat` tokens as one block, recurse
    on the drop), whose unfolding is well-founded via the token-count measure `decμ := length`
    (`decdec`: the drop is strictly shorter — the length prefix consumed is ≥ 1 token).  Re-folded
    with algebra base `decG _ := []`, step `decSt block acc := block :: acc`, it is exactly the
    hand-written `decodeHylo`; `Hylo.hyloFold_unique` emits
    `graph decodeHylo = Hylo.hyloR decC decμ decdec decG decSt` (`decode_emerges`).  Each token is
    `take`/`drop`ped once, so decode is O(N) — the explicit fuel of `L271.decodeFn` is GONE, replaced
    by the measure.

  * **Correctness — SECTION–RETRACTION, reused not re-proved.**  `decodeFuel_some_hylo` bridges the
    two decoders (whenever the fuelled parser succeeds, the hylomorphism returns the same list), so
    `L271.round_trip` transfers verbatim to `decode_hylo_round_trip : decodeHylo (encode strs) = strs`.
    In `Rel(Set)` this is `graph encode ≫ graph decodeHylo = id` (`section_retraction_derived`):
    `encode` is a section of the decoder `decodeHylo` its retraction.

  Mathlib-free; headline axioms ⊆ {propext, Quot.sound}.
-/
import AOP.A6_GenHylo
import AOP.A6_GenFold
import AOP.A6_ConsList
import leet.L271

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC271D

open Freyd

/-! ## ENCODE — a `ConsList` catamorphism (carrier `List Int`) -/

/-- Base of the encode fold: the empty list of strings encodes to no tokens. -/
def encG : Unit → List Int := fun _ => []

/-- Step of the encode fold: length-prefix the head block and prepend it to the encoded tail
    (`encode1 s = s.length :: s`).  The `++` fires once per block, giving O(N) total. -/
def encSt : List Int → List Int → List Int := fun s acc => LC271.encode1 s ++ acc

/-- The encode fold on the initial algebra `ConsList Unit (List Int)`. -/
def encodeCL : CL.ConsList Unit (List Int) → List Int
  | CL.ConsList.wrap _    => []
  | CL.ConsList.cons s xs => LC271.encode1 s ++ encodeCL xs

theorem encodeCL_wrap (d : Unit) : encodeCL (CL.ConsList.wrap d) = encG d := rfl
theorem encodeCL_cons (s : List Int) (xs : CL.ConsList Unit (List Int)) :
    encodeCL (CL.ConsList.cons s xs) = encSt s (encodeCL xs) := rfl

/-- **Encode EMERGES as the fold**: the structural fold `encodeCL` IS the catamorphism of the
    scalar cons-list algebra `[encG, encSt]`, produced by the general uniqueness law. -/
theorem encode_emerges :
    (graph encodeCL : CL.dCL Unit (List Int) ⟶ ⟨List Int⟩)
      = CL.cataR (CL.consScalarAlg encG encSt) :=
  CL.consFold_unique encG encSt encodeCL encodeCL_wrap encodeCL_cons

/-- Bridge: the emerged fold over the reshaped `ConsList` computes exactly the raw `encode`. -/
theorem encodeCL_ofList (strs : List (List Int)) :
    encodeCL (CL.ofList strs) = LC271.encode strs := by
  induction strs with
  | nil => rfl
  | cons s rest ih =>
      simp only [CL.ofList_cons, encodeCL, ih, LC271.encode, List.flatMap_cons]

/-! ## DECODE — a measured recursive-coalgebra HYLOMORPHISM (carrier `List (List Int)`) -/

/-- The decode coalgebra: leaf `.inl ()` at the empty token list (or a malformed length exceeding the
    remaining tokens); otherwise read the head `n` as a length and split off the next `n.toNat`
    tokens as one block, recursing on the drop. -/
def decC : List Int → Sum Unit (List Int × List Int)
  | []       => Sum.inl ()
  | n :: rest =>
      if n.toNat ≤ rest.length then Sum.inr (rest.take n.toNat, rest.drop n.toNat)
      else Sum.inl ()

/-- The measure: number of remaining tokens. -/
def decμ : List Int → Nat := fun ts => ts.length

/-- Base of the re-fold: nothing left to parse. -/
def decG : Unit → List (List Int) := fun _ => []
/-- Step of the re-fold: prepend the parsed block to the decoded tail. -/
def decSt : List Int → List (List Int) → List (List Int) := fun block acc => block :: acc

/-- Every `.inr` step consumes at least the one length-prefix token, so the drop is strictly
    shorter — the well-foundedness witness the hylomorphism law demands. -/
theorem decdec : ∀ s e s', decC s = Sum.inr (e, s') → decμ s' < decμ s := by
  intro s e s' h
  cases s with
  | nil => simp only [decC] at h; nomatch h
  | cons n rest =>
      simp only [decC] at h
      split at h
      · injection h with h1; injection h1 with h2 h3; subst h3
        simp only [decμ, List.length_cons, List.length_drop]; omega
      · nomatch h

/-- The hand-written decoder, by well-founded recursion on the token count (the measure `decμ`);
    the explicit fuel of `L271.decodeFn` is replaced by the measure. -/
def decodeHylo : List Int → List (List Int)
  | []       => []
  | n :: rest =>
      if n.toNat ≤ rest.length then rest.take n.toNat :: decodeHylo (rest.drop n.toNat)
      else []
termination_by ts => ts.length
decreasing_by simp only [List.length_cons, List.length_drop]; omega

theorem decodeHylo_nil : decodeHylo [] = [] := by simp only [decodeHylo]
theorem decodeHylo_cons (n : Int) (rest : List Int) :
    decodeHylo (n :: rest)
      = if n.toNat ≤ rest.length then rest.take n.toNat :: decodeHylo (rest.drop n.toNat)
        else [] := by
  simp only [decodeHylo]

/-- **Decode EMERGES as the hylomorphism**: the hand-written `decodeHylo` IS the relational
    hylomorphism of the measured coalgebra `decC` with algebra `[decG, decSt]`.  Discharged by
    showing `decodeHylo` obeys the hylomorphism recurrence — one case split, in place. -/
theorem decode_emerges :
    (graph decodeHylo : (⟨List Int⟩ : RelSet.{0}) ⟶ ⟨List (List Int)⟩)
      = Hylo.hyloR decC decμ decdec decG decSt := by
  refine Hylo.hyloFold_unique decC decμ decdec decG decSt decodeHylo ?_
  intro s
  cases s with
  | nil => rw [decodeHylo_nil]; rfl
  | cons n rest =>
      rw [decodeHylo_cons]
      split
      · rename_i h; simp only [decC, if_pos h, decSt]
      · rename_i h; simp only [decC, if_neg h, decG]

/-! ## Correctness — the SECTION–RETRACTION identity, reusing `L271.round_trip` -/

/-- Bridge between the two decoders: whenever the fuelled parser `L271.decodeFuel` SUCCEEDS with
    `some result`, the hylomorphism `decodeHylo` returns exactly that `result`.  By induction on the
    fuel; the malformed / `none` branches never fire on a success.  This is what carries the solved
    file's correctness across to the derived decoder — no re-proof of the parse argument. -/
theorem decodeFuel_some_hylo : ∀ (fuel : Nat) (ts : List Int) (result : List (List Int)),
    LC271.decodeFuel fuel ts = some result → decodeHylo ts = result := by
  intro fuel
  induction fuel with
  | zero =>
      intro ts result h
      cases ts with
      | nil =>
          simp only [LC271.decodeFuel, Option.some.injEq] at h; subst h; exact decodeHylo_nil
      | cons n rest => simp only [LC271.decodeFuel] at h; nomatch h
  | succ k ih =>
      intro ts result h
      cases ts with
      | nil =>
          simp only [LC271.decodeFuel, Option.some.injEq] at h; subst h; exact decodeHylo_nil
      | cons n rest =>
          rw [decodeHylo_cons]
          simp only [LC271.decodeFuel] at h
          split at h
          · rename_i hcond
            rw [if_pos hcond]
            cases hdf : LC271.decodeFuel k (rest.drop n.toNat) with
            | none => rw [hdf] at h; nomatch h
            | some strs =>
                rw [hdf] at h; injection h with h'
                rw [ih (rest.drop n.toNat) strs hdf]; exact h'
          · nomatch h

/-- **The derived round-trip**: decoding the encoding of ANY list of strings recovers it — the
    `L271.round_trip` correctness, transferred to the hylomorphic decoder through the fuel bridge.
    (`L271.decodeFn` uses fuel `(encode strs).length + 1`, always sufficient.) -/
theorem decode_hylo_round_trip (strs : List (List Int)) :
    decodeHylo (LC271.encode strs) = strs :=
  decodeFuel_some_hylo _ _ _ (LC271.round_trip strs)

/-- **The headline — SECTION–RETRACTION in `Rel(Set)`**: composing the emerged encoder then the
    emerged decoder is the identity — `encode` is a section, `decodeHylo` its retraction.  The
    `Rel(Set)` restatement of `decode_hylo_round_trip`. -/
theorem section_retraction_derived :
    (graph LC271.encode : LC271.dStrs ⟶ LC271.dTokens) ≫ graph decodeHylo
      = Cat.id LC271.dStrs := by
  apply hom_ext; intro strs strs'
  show (∃ ts, ts = LC271.encode strs ∧ strs' = decodeHylo ts) ↔ strs = strs'
  constructor
  · rintro ⟨ts, rfl, rfl⟩; exact (decode_hylo_round_trip strs).symm
  · rintro rfl; exact ⟨LC271.encode strs, rfl, (decode_hylo_round_trip strs).symm⟩

/-- **The honest derivation bundle**: (1) the encoder emerges as a `ConsList` catamorphism; (2) the
    decoder emerges as a measured hylomorphism; (3) they form a section–retraction pair (correctness
    reused from `L271.round_trip`). -/
theorem encode_decode_derived :
    ((graph encodeCL : CL.dCL Unit (List Int) ⟶ ⟨List Int⟩)
        = CL.cataR (CL.consScalarAlg encG encSt))
    ∧ ((graph decodeHylo : (⟨List Int⟩ : RelSet.{0}) ⟶ ⟨List (List Int)⟩)
        = Hylo.hyloR decC decμ decdec decG decSt)
    ∧ ((graph LC271.encode : LC271.dStrs ⟶ LC271.dTokens) ≫ graph decodeHylo
        = Cat.id LC271.dStrs) :=
  ⟨encode_emerges, decode_emerges, section_retraction_derived⟩

/-! ## Running the certified program

  `decodeHylo` is WF-recursive (opaque to `decide`), so run it through the proven round-trip. -/

example : decodeHylo (LC271.encode [[104, 105], []]) = [[104, 105], []] :=
  decode_hylo_round_trip _
example : decodeHylo (LC271.encode [[72, 101, 108, 108, 111]]) = [[72, 101, 108, 108, 111]] :=
  decode_hylo_round_trip _

end Freyd.Alg.RelSet.LC271D
