import LeetQ.Rel.Lang.Calc
import AOP.A4_1

/-! `rel(…)` (`Calc`): each construct against the AOP term written by hand, the closedness of the grammar, the
    errors of a construct outside the fragment, and B&dM derivations of ch. 4 and 5 as plain `calc`s over `rel(…)`
    terms. -/

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
/-- error: `⦇e,S⦈` differs in AOP: Rel folds lists from a start set `e : V ⟶ V`, AOP's `⦇R⦈` folds one algebra
of an `InitialAlgebra F`, and AOP has the list functor only in `RelSet` -/
#guard_msgs (whitespace := lax) in example (R : A ⟶ A) : A ⟶ A := rel(⦇R,R⦈)
/-- error: `Λ` differs in AOP: Rel reads a set `𝒫A` as an array `[α]`, AOP as the power object `P A` -/
#guard_msgs in example (R : A ⟶ A) : A ⟶ A := rel(Λ(R))
/-- error: `F(R)` differs in AOP: Rel's `F` is the list functor only, AOP's any relator -/
#guard_msgs in example (R : A ⟶ A) : A ⟶ A := rel(F(R))
/-- error: `Q` is not a local variable: a name in rel(…) is a variable or hypothesis of the statement -/
#guard_msgs in example : A ⟶ B := rel(Q)

end Div

section Prod

variable {𝒜 : Type u} [TabularUnitaryDivisionAllegory 𝒜] {A B C D A' B' : 𝒜}

set_option linter.unusedVariables false in
example [P : RelProd A B] [Q : RelProd A' B'] (R : C ⟶ A) (S : C ⟶ B) (U : A ⟶ A') (V : B ⟶ B') : True := by
  guard_expr rel(dom(R)) =ₛ dom R
  guard_expr rel(ran(R)) =ₛ ran R
  guard_expr rel(⟨R,S⟩) =ₛ P.pair R S
  guard_expr rel(⟨R,S⟩ π₁) =ₛ P.pair R S ≫ P.π₁
  guard_expr rel(⟨R,S⟩ π₂) =ₛ P.pair R S ≫ P.π₂
  guard_expr rel(U × V) =ₛ prodMap P Q U V
  guard_expr rel(⟨R,S⟩(U × V) π₁) =ₛ (P.pair R S ≫ prodMap P Q U V) ≫ Q.π₁
  trivial

/-- B&dM Ex 5.9 (`RelProd.map_comp_pair`): a map distributes over pairing. -/
example [P : RelProd A B] {f : D ⟶ C} (hf : Map f) (R : C ⟶ A) (S : C ⟶ B) : rel(f ⟨R,S⟩) = rel(⟨f R, f S⟩) :=
  calc rel(f ⟨R,S⟩)
      = rel(f ((R π₁°) ∩ (S π₂°))) := by rw [RelProd.pair]
    _ = rel((f (R π₁°)) ∩ (f (S π₂°))) := simple_dist_inter hf.2 _ _
    _ = rel((f R π₁°) ∩ (f (S π₂°))) := by rw [← Cat.assoc f R]
    _ = rel((f R π₁°) ∩ (f S π₂°)) := by rw [← Cat.assoc f S]
    _ = rel(⟨f R, f S⟩) := by rw [RelProd.pair]

/-- B&dM (5.3), absorption (`RelProd.pair_prodMap`), by the book's chain through a product `M` of `A'` and `B`. -/
example [P : RelProd A B] [Q : RelProd A' B'] [M : RelProd A' B] (X : C ⟶ A) (Y : C ⟶ B) (R : A ⟶ A')
    (S : B ⟶ B') : rel(⟨X,Y⟩(R × S)) = rel(⟨X R, Y S⟩) :=
  calc rel(⟨X,Y⟩(R × S))
      = rel(⟨X,Y⟩((R × 𝟙)(𝟙 × S))) := by rw [prodMap_factor P M Q R S]
    _ = rel(⟨X,Y⟩(R × 𝟙)(𝟙 × S)) := by rw [Cat.assoc]
    _ = rel(⟨X R, Y⟩(𝟙 × S)) := by rw [RelProd.pair_prodMap_fst]
    _ = rel(⟨X R, Y S⟩) := by rw [RelProd.pair_prodMap_snd]

/-- error: `π₁` needs an instance or hypothesis `RelProd A B`: rel(…) never writes the product -/
#guard_msgs in example (R : C ⟶ A) (S : C ⟶ B) : C ⟶ A := rel(⟨R,S⟩ π₁)

end Prod

section Sum

variable {𝒜 : Type u} [DistributiveAllegory 𝒜] {T A B C D : 𝒜}

set_option linter.unusedVariables false in
example (K : Coproduct T A B) (R : A ⟶ C) (S : B ⟶ C) : True := by
  guard_expr rel([R,S]) =ₛ junc K R S
  guard_expr rel(inl [R,S]) =ₛ K.u₁ ≫ junc K R S
  guard_expr rel(inr [R,S]) =ₛ K.u₂ ≫ junc K R S
  guard_expr rel([inl, inr]) =ₛ junc K K.u₁ K.u₂
  trivial

-- the objects of `inl` come from the other side of `=`, the elaboration of `rel(inl)` waiting for them
example (K : Coproduct T A B) : rel(inl) = K.u₁ := by guard_target =ₛ K.u₁ = K.u₁; rfl

/-- B&dM §5.3 (`junc_recip_junc`): `[U,V]°[R,S] = U°R ∪ V°S`. -/
example (K : Coproduct T A B) (U : A ⟶ D) (V : B ⟶ D) (R : A ⟶ C) (S : B ⟶ C) :
    rel([U,V]° [R,S]) = rel((U° R) ∪ (V° S)) :=
  calc rel([U,V]° [R,S])
      = rel(((U° inl) ∪ (V° inr)) [R,S]) := by rw [junc_recip]
    _ = rel((U° inl [R,S]) ∪ (V° inr [R,S])) := union_comp_distrib _ _ _
    _ = rel((U° (inl [R,S])) ∪ (V° inr [R,S])) := by rw [Cat.assoc U°]
    _ = rel((U° R) ∪ (V° inr [R,S])) := by rw [u₁_junc]
    _ = rel((U° R) ∪ (V° (inr [R,S]))) := by rw [Cat.assoc V°]
    _ = rel((U° R) ∪ (V° S)) := by rw [u₂_junc]

/-- error: `[R,S]` needs a hypothesis `Coproduct T A B`: rel(…) never writes it, and a structure is found by no
instance search -/
#guard_msgs (whitespace := lax) in example (R : A ⟶ C) (S : B ⟶ C) : T ⟶ C := rel([R,S])
/-- error: `[R,S]` has several hypotheses `Coproduct T A B`, K, L: rel(…) never writes it, and a structure is
found by no instance search -/
#guard_msgs (whitespace := lax) in
example (K L : Coproduct T A B) (R : A ⟶ C) (S : B ⟶ C) : T ⟶ C := rel([R,S])

end Sum

section Bool

variable {𝒜 : Type u} [BooleanAllegory 𝒜] {A B : 𝒜}

set_option linter.unusedVariables false in
example (R S : A ⟶ B) : True := by
  guard_expr rel(∼R) =ₛ ∼R
  guard_expr rel(R − S) =ₛ R − S
  guard_expr rel(R ∩ ∼S) =ₛ R ∩ ∼S
  trivial

end Bool

section Top

variable {𝒜 : Type u} [LocallyCompleteDistributiveAllegory 𝒜] {A B : 𝒜}

set_option linter.unusedVariables false in
example (R : A ⟶ B) : True := by
  guard_expr rel(R ∩ ⊤) =ₛ R ∩ topHom A B
  trivial

/-- error: `∼R` needs an instance `BooleanAllegory 𝒜`: AOP's `∼R` is the Heyting `R ⇨ 𝟘`, the complement only in
a Boolean allegory -/
#guard_msgs (whitespace := lax) in example (R : A ⟶ B) : A ⟶ B := rel(∼R)
/-- error: `R − S` needs an instance `BooleanAllegory 𝒜`: AOP's `∼R` is the Heyting `R ⇨ 𝟘`, the complement only
in a Boolean allegory -/
#guard_msgs (whitespace := lax) in example (R : A ⟶ B) : A ⟶ B := rel(R − R)

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
