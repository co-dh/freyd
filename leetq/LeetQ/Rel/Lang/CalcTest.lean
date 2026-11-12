import LeetQ.Rel.Lang.Calc
import AOP.A4_1
import AOP.A6_2

/-! `rel(…)` (`Calc`): each construct against the AOP term written by hand, the closedness of the grammar, the
    errors of a construct outside the fragment, and B&dM derivations of ch. 4–6 as plain `calc`s over `rel(…)`
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
/-- error: `⦇e,S⦈` is the program fold: its seed is a coreflexive `V ⟶ V`; write the book's `⦇[e,S]⦈` with
`e : 1 ⟶ V` instead -/
#guard_msgs (whitespace := lax) in example (R : A ⟶ A) : A ⟶ A := rel(⦇R,R⦈)
/-- error: `⊤` needs an instance `LocallyCompleteDistributiveAllegory` (AOP's `topHom`) or
`TabularUnitaryDivisionAllegory` (AOP's `topMor`): AOP's `⊤` is one of these -/
#guard_msgs (whitespace := lax) in example (R : A ⟶ B) : A ⟶ B := rel(R ∩ ⊤)
/-- error: `Λ(R)` needs an instance `PowerAllegory 𝒜`: AOP defines `Freyd.Alg.Λ` over it -/
#guard_msgs in example (R : A ⟶ B) : Prop := rel(Λ(R) ∋) = R
/-- error: `setify` has no AOP counterpart: Rel's list and set are both an array `[α]`, AOP's power object `P A`
is no list -/
#guard_msgs (whitespace := lax) in example (R : A ⟶ A) : A ⟶ A := rel(R setify)
/-- error: `F(R)` needs a hypothesis `Relator 𝒜 𝒜`: rel(…) never writes the relator
---
error: `F(R)` needs a hypothesis `Relator 𝒜 𝒜`: rel(…) never writes the relator -/
#guard_msgs in example (R : A ⟶ A) : Prop := rel(F(R)) = rel(F(R))
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
/-- error: `π₁` has several hypotheses `RelProd A B`, P, P': rel(…) never writes the product -/
#guard_msgs in
example [P : RelProd A B] [P' : RelProd A B] (R : C ⟶ A) (S : C ⟶ B) : C ⟶ A := rel(⟨R,S⟩ π₁)

set_option linter.unusedVariables false in
example (R : C ⟶ A) : True := by
  guard_expr rel(R ∩ ⊤) =ₛ R ∩ topMor C A
  trivial

/-- B&dM (5.6) (`RelProd.eq_topMor`): `⊤` here is the tabular unitary division allegory's `topMor`. -/
example [P : RelProd A B] : rel(π₁° π₂) = rel(⊤) := RelProd.eq_topMor P

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

section Fold

-- an LCDA as well, for the fold's prefixed-point bound (`relCata_le_of_prefixed`)
variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} [I : InitialAlgebra F]
  {A B C U W : 𝒜}

set_option linter.unusedVariables false in
example (R : F.obj A ⟶ A) (S : A ⟶ B) (K : Coproduct (F.obj A) U W) (e : U ⟶ A) (V : W ⟶ A) : True := by
  guard_expr rel(⦇R⦈) =ₛ relCata R
  guard_expr rel(⦇R⦈ S) =ₛ relCata R ≫ S
  guard_expr rel(α) =ₛ I.α
  guard_expr rel(F(S)) =ₛ F.map S
  guard_expr rel(α ⦇R⦈) =ₛ I.α ≫ relCata R
  guard_expr rel(F(⦇R⦈) R) =~ F.map (relCata R) ≫ R
  guard_expr rel(⦇[e,V]⦈) =ₛ relCata (junc K e V)
  trivial

/-- B&dM fold fusion (`relCata_fusion`): `⦇R⦈ S` satisfies the fold's equation at `Q`, then uniqueness. -/
example (R : F.obj B ⟶ B) (Q : F.obj C ⟶ C) (S : B ⟶ C) (h : rel(R S) = rel(F(S) Q)) :
    rel(⦇R⦈ S) = rel(⦇Q⦈) :=
  (relCata_UP I Q _).1 <|
  calc rel(α (⦇R⦈ S))
      = rel(α ⦇R⦈ S) := by rw [Cat.assoc]
    _ = rel(F(⦇R⦈) R S) := by rw [relCata_cancel I R]
    _ = rel(F(⦇R⦈) (R S)) := by rw [Cat.assoc]
    _ = rel(F(⦇R⦈) (F(S) Q)) := by rw [h]
    _ = rel(F(⦇R⦈) F(S) Q) := by rw [Cat.assoc]
    _ = rel(F(⦇R⦈ S) Q) := by rw [Freyd.Functor.map_comp]

/-- B&dM, the fold is monotonic (`relCata_mono`): `⦇S⦈` is a prefixed point of the fold's equation at `R`. -/
example (R S : F.obj C ⟶ C) (h : rel(R) ⊑ rel(S)) : rel(⦇R⦈) ⊑ rel(⦇S⦈) :=
  relCata_le_of_prefixed I <|
  calc rel(α° (F(⦇S⦈) R))
      ⊑ rel(α° (F(⦇S⦈) S)) := comp_mono_left _ (comp_mono_left _ h)
    _ = rel(α° (α ⦇S⦈)) := by rw [relCata_cancel I S]
    _ = rel(α° α ⦇S⦈) := by rw [Cat.assoc]
    _ = rel(𝟙 ⦇S⦈) := by rw [I.recip_alpha_alpha]
    _ = rel(⦇S⦈) := by rw [Cat.id_comp]

/-- B&dM, the fold of `α` is the identity (`relCata_alpha`): `𝟙` satisfies the fold's equation at `α`. -/
example : rel(⦇α⦈) = rel(𝟙) :=
  Eq.symm <| (relCata_UP I I.α (𝟙 _)).1 <|
  calc rel(α 𝟙)
      = rel(α) := by rw [Cat.comp_id]
    _ = rel(𝟙 α) := by rw [Cat.id_comp]
    _ = rel(F(𝟙) α) := by rw [Freyd.Functor.map_id]

-- each side of `=` is its own `rel(…)`, so each reports
/-- error: `⦇R⦈` needs an instance or hypothesis `InitialAlgebra G`: rel(…) never writes the initial algebra, nor
its relator
---
error: `⦇R⦈` needs an instance or hypothesis `InitialAlgebra G`: rel(…) never writes the initial algebra, nor
its relator -/
#guard_msgs (whitespace := lax) in
example (G : Relator 𝒜 𝒜) (R : G.obj A ⟶ A) : Prop := rel(⦇R⦈) = rel(⦇R⦈)
/-- error: `F(R)` has several hypotheses `Relator 𝒜 𝒜`, F, G: rel(…) never writes the relator
---
error: `F(R)` has several hypotheses `Relator 𝒜 𝒜`, F, G: rel(…) never writes the relator -/
#guard_msgs (whitespace := lax) in
example (G : Relator 𝒜 𝒜) (S : A ⟶ B) : Prop := rel(F(S)) = rel(F(S))
/-- error: `⦇R⦈` has several hypotheses `InitialAlgebra F`, I, J: rel(…) never writes the initial algebra, nor
its relator
---
error: `⦇R⦈` has several hypotheses `InitialAlgebra F`, I, J: rel(…) never writes the initial algebra, nor
its relator -/
#guard_msgs (whitespace := lax) in
example [J : InitialAlgebra F] (R : F.obj A ⟶ A) : Prop := rel(⦇R⦈) = rel(⦇R⦈)
/-- error: `⊤` is `topHom` (by `LocallyCompleteDistributiveAllegory`) and `topMor` (by
`TabularUnitaryDivisionAllegory`) here, and no theorem identifies them -/
#guard_msgs (whitespace := lax) in example (R : A ⟶ B) : A ⟶ B := rel(R ∩ ⊤)

end Fold

section Power

-- tabular as well, for `thin(Q)` (`AOP.A8_1`)
variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {A B C : 𝒜}
open PowerAllegory

set_option linter.unusedVariables false in
example (R : A ⟶ B) (S : C ⟶ A) (Q : A ⟶ A) (X : C ⟶ P (P A)) : True := by
  guard_expr rel(∋ R) =ₛ ∋ A ≫ R
  guard_expr rel(R ∈) =ₛ R ≫ (∋ B)°
  guard_expr rel(Λ(R)) =ₛ Λ R
  guard_expr rel(Λ(S) E(R)) =ₛ Λ S ≫ existsImage R
  guard_expr rel(P(R)) =ₛ P(R)
  guard_expr rel(est(Q)) =ₛ est(Q)
  guard_expr rel(thin(Q)) =ₛ thin(Q)
  guard_expr rel(X union) =ₛ X ≫ union
  guard_expr rel(S τ) =ₛ S ≫ singletonMap
  guard_expr rel(Λ(S) est(Q)) =ₛ Λ S ≫ est(Q)
  guard_expr rel(∈ \ Q°) =ₛ (∋ A)° \ Q°
  trivial

/-- B&dM (7.4) (`singletonMap_comp_est`): the `est` of a singleton, (7.5) at `S ≜ 𝟙`. -/
example (R : A ⟶ A) : rel(τ est(R)) = rel(𝟙 ∩ R°) :=
  calc rel(τ est(R))
      = rel(Λ(𝟙) est(R)) := rfl
    _ = rel(𝟙 ∩ (𝟙° \ R°)) := Λ_comp_est _ _
    _ = rel(𝟙 ∩ (𝟙 \ R°)) := by rw [recip_id]
    _ = rel(𝟙 ∩ R°) := by rw [leftDiv_id]

/-- B&dM (7.5) (`Λ_comp_est`): `Λ(S)` is a map, so it distributes over the meet that `est(R)` is. -/
example (S : B ⟶ A) (R : A ⟶ A) : rel(Λ(S) est(R)) = rel(S ∩ (S° \ R°)) :=
  calc rel(Λ(S) est(R))
      = rel(Λ(S) (∋ ∩ (∈ \ R°))) := rfl
    _ = rel(Λ(S) ∋ ∩ (Λ(S) (∈ \ R°))) := simple_dist_inter (Λ_is_map' S).2 _ _
    _ = rel(S ∩ (Λ(S) (∈ \ R°))) := by rw [Λ_eps_eq']
    _ = rel(S ∩ (S° \ R°)) := by rw [Λ_comp_lb]

/-- B&dM §8.1 (`thinRel_comp_eps_le`): thinning only shrinks, `thin(Q)` being below `⊇ ≜ ∋/∋`. -/
example (Q : A ⟶ A) : rel(thin(Q) ∋) ⊑ rel(∋) :=
  calc rel(thin(Q) ∋)
      = rel(((∋ / ∋) ∩ (∈ \ (Q° ∈))) ∋) := rfl
    _ ⊑ rel((∋ / ∋) ∋) := comp_mono_right (inter_lb_left _ _) _
    _ ⊑ rel(∋) := div_self_comp_le _

-- no arrow in the context names the allegory: the instances are left to Lean, which finds them by unification
example : rel(τ ∋) = 𝟙 A := singletonMap_comp_eps

end Power

section PowerOnly

variable {𝒜 : Type u} [PowerAllegory 𝒜] {A B : 𝒜}

/-- error: `est(R)` needs an instance `UnguardedPowerLCDA 𝒜`: AOP defines `Freyd.Alg.est` over it -/
#guard_msgs (whitespace := lax) in example (R : A ⟶ A) : Prop := rel(Λ(R) est(R)) = R

end PowerOnly

/-- error: line 347, col 7: one-argument fold is for rel(…) proofs: a program folds a list with `⦇e,S⦈` -/
#guard_msgs (whitespace := lax) in
rel_program oneFold where
  r ≜ ⦇𝟙⦈

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
