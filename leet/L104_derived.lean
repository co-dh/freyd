/-
  LeetCode 104 — Maximum Depth of Binary Tree — DERIVED by extremum fusion (the GREEDY THEOREM),
  the FIRST tree derivation in the Algebra-of-Programming track.

  `leet.L104` writes the depth fold `[ () ↦ 0,  (dl,_,dr) ↦ 1 + imax dl dr ]` down and then verifies
  it against the spec `pathLen`.  HERE we do the opposite: we START from the extremum specification
  `maxRel (≤) · Λ pathLen` (the ≤-maximum of the achievable root-to-`nil` path lengths) and let the
  max-fold step `1 + imax dl dr` EMERGE as the unique monotone map that refines the greedy choice —
  it is not written first.

  The route (B&dM §7.2 greedy theorem, `A7_4_Horner.greedy_max_of_refinement`):

  * `S` — the NONDETERMINISTIC generator `[ () ↦ {0},  (rl,_,rr) ↦ {rl+1, rr+1} ]`; its
    catamorphism `⦇S⦈` is exactly `pathLen` (bridge `cataTreeFold_S`), the set of achievable path
    lengths.
  * `alg` (= `L104.alg`, the deterministic depth fold) is shown to (a) be MONOTONE on the reverse-`≤`
    order `R x y := y ≤ x` (`alg_mono`, from `imax` monotone) and (b) REFINE the greedy choice
    `Λ S ≫ maxRel R` (`alg_refines`: `alg ⊑ S` — every folded value is generatable — AND
    `S° ≫ alg ⊑ R°` — the folded value dominates every generatable value; both from `imax_eq_or`
    and `imax_ge_left/right`).  These two facts FORCE the node step to be `1 + imax dl dr`: it is the
    only monotone map that both lands in `{dl+1, dr+1}` and dominates it.
  * The greedy theorem then places `⦇alg⦈` inside the Pareto frontier `A ⦇S⦈ ≫ maxRel R`; the
    TreeBin bridge `cataR_eq_relCata` transports this from the abstract `relCata` to the structural
    `cataR`, and reading off the single greedy conclusion (membership + maximality) gives BOTH halves
    of correctness — achievability and domination — WITHOUT ever invoking `L104.pathLen_depth` /
    `pathLen_le_depth`.

  Mathlib-free.  Axioms of the headline `depth_derived_correct` ⊆ {propext, Classical.choice,
  Quot.sound}; the `Classical.choice` is the honest price of `greedy_max_of_refinement` / `relCata`'s
  universal property.
-/
import AOP.A6_TreeBin
import AOP.A7_4_Horner
import leet.L104

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.LC104D

open Freyd Freyd.Alg Freyd.Alg.RelSet Freyd.Alg.RelSet.TB Freyd.Alg.RelSet.LC104

variable {L : Type}

/-! ## The specification, as an extremum

`R` is the REVERSE `≤` so that `maxRel R` is the numeric maximum; `S` is the nondeterministic
generator whose catamorphism enumerates the achievable path lengths. -/

/-- Reverse `≤` on `ℕ`: `R x y := y ≤ x`, so `maxRel R` picks the numerically LARGEST member. -/
def R : (dNat : RelSet.{0}) ⟶ (dNat : RelSet.{0}) := fun x y => y ≤ x

/-- The nondeterministic generator `[ () ↦ {0},  (rl,_,rr) ↦ {rl+1, rr+1} ] : F(ℕ) → ℕ` — "extend
    a child's path by one".  Its catamorphism is exactly `pathLen` (see `cataTreeFold_S`). -/
def S : TFobj L (dNat : RelSet.{0}) ⟶ (dNat : RelSet.{0}) := fun u n => match u with
  | Sum.inl _           => n = 0
  | Sum.inr (rl, _, rr) => n = rl + 1 ∨ n = rr + 1

/-! ## Bridge: `⦇S⦈ = pathLen` (the generator computes the spec) -/

/-- Every tree has at least one achievable path length (the leftmost path). -/
theorem pathLen_total : ∀ t : Tree L, ∃ n, pathLen t n := by
  intro t
  induction t with
  | nil => exact ⟨0, rfl⟩
  | node l a r ihl ihr =>
    obtain ⟨m, hm⟩ := ihl
    exact ⟨m + 1, m, Or.inl hm, rfl⟩

/-- **The generator IS the spec**: the structural catamorphism of `S` relates a tree to `n` exactly
    when `n` is an achievable root-to-`nil` path length.  Tree analogue of the `gen_spec`/`spec_gen`
    characterisation in `A7_4_Horner.horner_correct`. -/
theorem cataTreeFold_S : ∀ (t : Tree L) (n : Nat), cataTreeFold S t n ↔ pathLen t n := by
  intro t
  induction t with
  | nil => intro n; exact Iff.rfl
  | node l a r ihl ihr =>
    intro n
    simp only [cataTreeFold_node]
    constructor
    · rintro ⟨rl, rr, hl, hr, hf⟩
      have hf' : n = rl + 1 ∨ n = rr + 1 := hf
      cases hf' with
      | inl h => exact ⟨rl, Or.inl ((ihl rl).mp hl), h⟩
      | inr h => exact ⟨rr, Or.inr ((ihr rr).mp hr), h⟩
    · rintro ⟨m, hm, hn⟩
      cases hm with
      | inl hml =>
        obtain ⟨rr, hrr⟩ := pathLen_total r
        exact ⟨m, rr, (ihl m).mpr hml, (ihr rr).mpr hrr, Or.inl hn⟩
      | inr hmr =>
        obtain ⟨rl, hrl⟩ := pathLen_total l
        exact ⟨rl, m, (ihl rl).mpr hrl, (ihr m).mpr hmr, Or.inr hn⟩

/-! ## The three greedy side conditions -/

/-- `R` (reverse `≤`) is transitive. -/
theorem R_trans : (R ≫ R : (dNat : RelSet.{0}) ⟶ dNat) ⊑ R := by
  rw [le_iff]; intro x z h
  obtain ⟨y, hxy, hyz⟩ := h
  have h1 : y ≤ x := hxy
  have h2 : z ≤ y := hyz
  show z ≤ x; simp only [dNat] at *; omega

/-- The depth fold `alg` is MONOTONE on `R`: `imax` is monotone, so a `≤`-larger pair of child
    depths yields a `≤`-larger node depth (mirrored through the reverse order `R`). -/
theorem alg_mono : MonotonicAlg (F := F L) alg R := by
  show (F L).map R ≫ alg ⊑ alg ≫ R
  rw [le_iff]; intro u m h
  obtain ⟨v, hFuv, hv⟩ := h
  refine ⟨algFn u, rfl, ?_⟩
  show m ≤ algFn u
  cases u with
  | inl x =>
    cases v with
    | inl y => have hm0 : m = 0 := hv; show m ≤ 0; simp only [dNat] at *; omega
    | inr q => exact hFuv.elim
  | inr p =>
    cases v with
    | inl y => exact hFuv.elim
    | inr q =>
      obtain ⟨rl, a, rr⟩ := p
      obtain ⟨rl', a', rr'⟩ := q
      obtain ⟨hRl, ha, hRr⟩ := (hFuv : R rl rl' ∧ a = a' ∧ R rr rr')
      have hRl' : rl' ≤ rl := hRl
      have hRr' : rr' ≤ rr := hRr
      have hm' : m = 1 + imax rl' rr' := hv
      have h1 := imax_eq_or rl' rr'
      have h2 := imax_ge_left rl rr
      have h3 := imax_ge_right rl rr
      show m ≤ 1 + imax rl rr; simp only [dNat] at *; omega

/-- The depth fold `alg` REFINES the greedy choice `Λ S ≫ maxRel R`.  Via `le_Λ_comp_maxRel_iff` this
    is two facts: `alg ⊑ S` (the folded value `1 + imax rl rr` is one of `{rl+1, rr+1}`, by
    `imax_eq_or`) and `S° ≫ alg ⊑ R°` (the folded value dominates every generatable value, by
    `imax_ge_left`/`imax_ge_right`).  These two force the node step to equal `1 + imax rl rr`. -/
theorem alg_refines : (alg : TFobj L dNat ⟶ dNat) ⊑ Λ S ≫ maxRel R := by
  apply le_Λ_comp_maxRel_iff.mpr
  refine ⟨?_, ?_⟩
  · -- alg ⊑ S : every folded value is generatable
    rw [le_iff]; intro u m h
    cases u with
    | inl x => exact h
    | inr p =>
      obtain ⟨rl, a, rr⟩ := p
      have hm : m = 1 + imax rl rr := h
      show m = rl + 1 ∨ m = rr + 1
      cases imax_eq_or rl rr with
      | inl he => exact Or.inl (by simp only [dNat] at *; omega)
      | inr he => exact Or.inr (by simp only [dNat] at *; omega)
  · -- S° ≫ alg ⊑ R° : the folded value dominates every generatable value
    rw [le_iff]; intro x m h
    obtain ⟨v, hSv, hv⟩ := h
    show x ≤ m
    cases v with
    | inl y =>
      have hx0 : x = 0 := hSv
      have hm0 : m = 0 := hv
      simp only [dNat] at *; omega
    | inr q =>
      obtain ⟨rl, a, rr⟩ := q
      have hxor : x = rl + 1 ∨ x = rr + 1 := hSv
      have hm' : m = 1 + imax rl rr := hv
      have h2 := imax_ge_left rl rr
      have h3 := imax_ge_right rl rr
      simp only [dNat] at *; omega

/-! ## The derivation: `1 + imax dl dr` emerges as the greedy choice -/

/-- **LeetCode 104, derived by extremum fusion.**  `depthFn t` is an achievable path length AND is
    the `≤`-greatest achievable path length — the SAME statement as `L104.solve_correct`, but here
    DERIVED: the load-bearing first line is the greedy theorem `greedy_max_of_refinement`, which
    fuses the maximum of the nondeterministic generator `S` into the deterministic fold `alg` whose
    node step `1 + imax dl dr` is forced (via `alg_mono` + `alg_refines`) as the unique monotone map
    refining the greedy choice.  No appeal to `pathLen_depth`/`pathLen_le_depth`. -/
theorem depth_derived_correct (t : Tree L) :
    pathLen t (depthFn t) ∧ ∀ n, pathLen t n → n ≤ depthFn t := by
  -- GREEDY THEOREM: `⦇alg⦈` lands inside the Pareto frontier `A ⦇S⦈ ≫ maxRel R`.
  have hmap : Map (alg : TFobj L dNat ⟶ dNat) := graph_map algFn
  have H1 : relCata (initial L) alg ⊑ Λ (relCata (initial L) S) ≫ maxRel R :=
    greedy_max_of_refinement (F_preservesRecip L) (initial L) hmap R_trans alg_mono alg_refines
  -- TreeBin bridge: transport from the abstract `relCata` to the structural `cataR`.
  have H2 : cataR (@alg L) ⊑ Λ (cataR (@S L)) ≫ maxRel R := by
    rw [← cataR_eq_relCata (@alg L), ← cataR_eq_relCata (@S L)] at H1; exact H1
  -- `depthFn t` is a member of `⦇alg⦈`; apply the frontier refinement there.
  have hmem : cataR alg t (depthFn t) := (cataTreeFold_alg t (depthFn t)).mpr rfl
  obtain ⟨P, hAP, hmax⟩ := (le_iff.mp H2) t (depthFn t) hmem
  rw [Λ_eq_classifier] at hAP
  have hPeq : P = fun w => (cataR S) t w := hAP
  subst hPeq
  obtain ⟨hmem_gen, hdom⟩ := (maxRel_apply R _ (depthFn t)).mp hmax
  -- membership → achievability; maximality + reverse-`≤` → domination.  Bridge `⦇S⦈ = pathLen`.
  refine ⟨(cataTreeFold_S t (depthFn t)).mp hmem_gen, ?_⟩
  intro n hn
  exact hdom n ((cataTreeFold_S t n).mpr hn)

/-! ## Running the derived program (same computations as `L104`) -/

example : depthFn (leaf (5 : Nat)) = 1 := by decide
example : depthFn (bal (1 : Nat) 2 3) = 2 := by decide
example : depthFn (Tree.nil : Tree Nat) = 0 := by decide
example : depthFn (Tree.node (leaf (1 : Nat)) 2 Tree.nil) = 2 := by decide

end Freyd.Alg.RelSet.LC104D
