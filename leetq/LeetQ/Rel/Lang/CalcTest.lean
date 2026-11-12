import LeetQ.Rel.Lang.Calc
import AOP.A4_1

/-! `rel(…)` (`Calc`): each construct against the AOP term written by hand, the closedness of the grammar, the
    errors of a construct outside the fragment, and three B&dM derivations as plain `calc`s over `rel(…)` terms. -/

namespace LeetQ.Rel.Lang.CalcTest

open Lean Freyd Freyd.Alg

universe v u

section Div

variable {𝒜 : Type u} [DivisionAllegory 𝒜] {A B C D : 𝒜}

/-! ### Each construct is the AOP term, syntactically -/

-- `guard_expr` elaborates its terms out of the linter's sight
set_option linter.unusedVariables false in
example (R : A ⟶ B) (S : B ⟶ C) (T : A ⟶ C) (U : A ⟶ B) : True := by
  guard_expr rel(R) =ₛ R
  guard_expr rel(R S) =ₛ R ≫ S
  guard_expr rel(RS) =ₛ R ≫ S
  guard_expr rel(R U°) =ₛ R ≫ U°
  guard_expr rel(R°°) =ₛ R°°
  guard_expr rel(R ∩ U) =ₛ R ∩ U
  guard_expr rel(R ∪ U) =ₛ R ∪ U
  guard_expr rel(T / S) =ₛ T / S
  guard_expr rel(R \ T) =ₛ R \ T
  guard_expr rel(R 𝟙) =ₛ R ≫ 𝟙 B
  guard_expr rel(R ∪ 𝟘) =ₛ R ∪ (𝟘 : A ⟶ B)
  -- one level, left to right: the right operand is a primary
  guard_expr rel(R S ∩ T) =ₛ (R ≫ S) ∩ T
  guard_expr rel(R ∩ (T S°) S) =ₛ (R ∩ T ≫ S°) ≫ S
  guard_expr rel(R
    S) =ₛ R ≫ S
  trivial

/-! ### Three derivations of B&dM ch. 4, each step one law -/

/-- B&dM 4.8, the symmetric modular law (`modular_sym`). -/
example (R : A ⟶ B) (S : B ⟶ C) (T : A ⟶ C) : rel(R S ∩ T) ⊑ rel((R ∩ (T S°))(S ∩ (R° T))) :=
  calc rel(R S ∩ T)
      ⊑ rel((R ∩ (T S°)) S ∩ T) := le_inter (modular_le R S T) (inter_lb_right _ _)
    _ ⊑ rel((R ∩ (T S°))(S ∩ ((R ∩ (T S°))° T))) := modular_le_right _ S T
    _ ⊑ rel((R ∩ (T S°))(S ∩ (R° T))) :=
        comp_mono_left _ (inter_mono (le_refl S) (comp_mono_right (recip_mono (inter_lb_left _ _)) T))

/-- B&dM 4.9 (`recip_comp_inter_id_le`): 4.8 at `(R°, S, 𝟙)`. -/
example (R S : A ⟶ B) : rel(R° S ∩ 𝟙) ⊑ rel((R ∩ S)°(R ∩ S)) :=
  calc rel(R° S ∩ 𝟙)
      ⊑ rel((R° ∩ (𝟙 S°))(S ∩ (R°° 𝟙))) := modular_sym R° S (𝟙 B)
    _ = rel((R° ∩ S°)(S ∩ (R°° 𝟙))) := by rw [Cat.id_comp]
    _ = rel((R° ∩ S°)(S ∩ R°°)) := by rw [Cat.comp_id]
    _ = rel((R° ∩ S°)(S ∩ R)) := by rw [Allegory.recip_recip]
    _ = rel((R ∩ S)°(S ∩ R)) := by rw [Allegory.recip_inter]
    _ = rel((R ∩ S)°(R ∩ S)) := by rw [Allegory.inter_comm S R]

/-- B&dM Ex 4.35 (`div_comp_recip_map`): the same chain of Galois steps, in Rel. -/
example {f : D ⟶ B} (hf : Map f) (R : A ⟶ C) (S : B ⟶ C) : rel(R / (f S)) = rel(R / S f°) := by
  apply antisymm_of_le_iff
  intro X
  calc rel(X) ⊑ rel(R / (f S)) ↔ rel(X (f S)) ⊑ rel(R) := le_div_iff _ _ _
    _ ↔ rel(X f S) ⊑ rel(R) := by rw [← Cat.assoc]
    _ ↔ rel(X f) ⊑ rel(R / S) := (le_div_iff _ _ _).symm
    _ ↔ rel(X) ⊑ rel(R / S f°) := map_shunt_right hf X (R / S)

/-! ### Outside the fragment: an error naming the construct -/

/-- error: a literal `{…}` has no AOP counterpart -/
#guard_msgs in example (R : A ⟶ B) : A ⟶ B := rel(R {(a,b)})
/-- error: `at(0)` has no AOP counterpart -/
#guard_msgs in example (R : A ⟶ B) : A ⟶ B := rel(R at(0))
/-- error: `dom` is outside the allegory fragment of rel(…) -/
#guard_msgs in example (R : A ⟶ B) : A ⟶ A := rel(dom(R))
/-- error: `⟨R,S⟩` differs in AOP: `RelProd.pair` takes an explicit product witness -/
#guard_msgs in example (R : A ⟶ B) : A ⟶ B := rel(⟨R,R⟩)
/-- error: `⦇e,S⦈` differs in AOP: `⦇R⦈` folds an `InitialAlgebra`, not a list from a seed -/
#guard_msgs in example (R : A ⟶ A) : A ⟶ A := rel(⦇R,R⦈)
/-- error: `∼R` differs in AOP: there `∼R` is the Heyting `R ⇨ 𝟘`, a complement only when Boolean -/
#guard_msgs in example (R : A ⟶ B) : A ⟶ B := rel(∼R)
/-- error: `R × S` differs in AOP: `prodMap` takes an explicit `RelProd` witness -/
#guard_msgs in example (R : A ⟶ B) : A ⟶ B := rel(R × R)
/-- error: `Q` is not a local variable: a name in rel(…) is a variable or hypothesis of the statement -/
#guard_msgs in example : A ⟶ B := rel(Q)

end Div

section Top

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜] {A B : 𝒜}

set_option linter.unusedVariables false in
example (R : A ⟶ B) : True := by
  guard_expr rel(R ∩ ⊤) =ₛ R ∩ topHom A B
  trivial

end Top

/-! ### Closedness: a Lean term inside `rel(…)` is a parse error, never a term elaborated -/

open Elab Command in
elab "#rel_term " s:str : command => do
  match Parser.runParserCategory (← getEnv) `term s.getString with
  | .ok t => logInfo m!"parsed {t}"
  | .error e => logInfo e

/-- info: parsed rel(R S°∩T) -/
#guard_msgs in #rel_term "rel(R S° ∩ T)"
/-- info: <input>:1:4: expected a name -/
#guard_msgs in #rel_term "rel(fun x => x)"
/-- info: <input>:1:4: expected a name -/
#guard_msgs in #rel_term "rel(1 + 1)"
/-- info: <input>:1:6: expected ')' -/
#guard_msgs in #rel_term "rel((R, S))"
/-- info: <input>:1:7: expected a name -/
#guard_msgs in #rel_term "rel(R (by simp))"

end LeetQ.Rel.Lang.CalcTest
