/-
  **Generic polynomial (bi)functors in `Rel(Set)`** — a port of AoPA's `Data.Generic.Core`.

  A `PolyF` code names a polynomial bifunctor `⟦F⟧ A X` built from constants (`zer`, `one`), the two
  arguments (`arg₁`, `arg₂`) and pointwise sum/product (`oplus`, `otimes`).  `sem F A X` is its
  action on Lean types; `bimap`/`fmap` its action on functions; `bimapR`/`fmapR` its action on
  `Rel(Set)` morphisms (the *relator*); `bimapP`/`fmapP` the lifting of predicates.  `Mu F A` is the
  initial algebra, with `In : ⟦F⟧ A (Mu F A) → Mu F A`.

  This layer is GENERIC OVER A FUNCTOR CODE, unlike the repo's existing `A6_GenFold`/`A6_SnocList`/
  `A6_ConsList`/`A6_TreeBin`, which fix one carrier each.  The list functor is `oplus one (otimes
  arg₁ arg₂)`; `A6_SnocList`/`A6_ConsList`'s `wrap`/`snoc`/`cons`/`nil` and `TreeBin`'s `nil`/`node`
  are the constructor forms of `In` for that code and for `oplus one (otimes (otimes arg₂ arg₁)
  arg₂)`.  The relator laws below (`bimapR_functor`, `bimapR_monotonic`, `bimapR_recip`, …) are the
  functor-independent facts those files re-establish per datatype; `A6_Poly_List.lean` gives the
  formal specialization to the list code as a sanity check.

  aopa → repo dictionary (see `Freyd.Alg.RelSet`): `X ○ Y ↦ Y ≫ X`, `R ˘ ↦ R°`, `fun f ↦ graph f`,
  `idR ↦ 𝟙`, `R ⊑ S` unchanged, `R ≑ S ↦ R = S` (the hom order is antisymmetric).  aopa's `A ← B`
  (output-first) becomes `B ⟶ A` here, so pointwise relations read input-first.
-/
module

public import AOP.A6_1_RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.Poly

open Freyd Freyd.Alg.RelSet

/-! ## Codes and their action on types (`PolyF`, `⟦F⟧` = `sem`) -/

/-- Codes for polynomial bifunctors (aopa `PolyF`). -/
public inductive PolyF where
  | zer                              -- constant `0`
  | one                              -- constant `1`
  | arg₁                             -- first argument
  | arg₂                             -- second argument
  | oplus  : PolyF → PolyF → PolyF   -- aopa `_⊕_`
  | otimes : PolyF → PolyF → PolyF   -- aopa `_⊗_`

/-- Action on types, aopa `⟦_⟧`.  `reducible` so the `Body`/`sem` round-trip stays transparent. -/
@[reducible, expose] public def sem : PolyF → Type → Type → Type
  | .zer,       _, _ => Empty
  | .one,       _, _ => PUnit
  | .arg₁,      a, _ => a
  | .arg₂,      _, x => x
  | .oplus  l r, a, x => sem l a x ⊕ sem r a x
  | .otimes l r, a, x => sem l a x × sem r a x

/-- The bundled `Rel(Set)` object `⟨⟦F⟧ A X⟩`. -/
@[reducible, expose] public def Fo (F : PolyF) (a x : RelSet.{0}) : RelSet.{0} := ⟨sem F a.carrier x.carrier⟩

/-! ## The initial algebra `μ F A`

  Lean's kernel rejects the direct `inductive Mu | In : sem F A (Mu F A) → Mu F A` (it does not
  unfold `sem` in the positivity check).  We instead spell the functor value out as an inductive
  FAMILY `Body F A G ≅ ⟦G⟧ A (Mu F A)`, mutually with `Mu`; the isomorphism `toSem`/`ofSem` then
  recovers the public `In : ⟦F⟧ A (Mu F A) → Mu F A`. -/

mutual
/-- The initial algebra `μ F A` (aopa `μ`). -/
public inductive Mu (F : PolyF) (A : Type) : Type where
  | In : Body F A F → Mu F A
/-- `Body F A G ≅ ⟦G⟧ A (Mu F A)`: the functor value spelled out constructor-by-constructor so the
    recursive occurrence `Mu F A` (at `arg₂`) is manifestly strictly positive. -/
public inductive Body (F : PolyF) (A : Type) : PolyF → Type where
  | unit : Body F A .one
  | fst  : A → Body F A .arg₁
  | snd  : Mu F A → Body F A .arg₂
  | inl  : {l r : PolyF} → Body F A l → Body F A (.oplus l r)
  | inr  : {l r : PolyF} → Body F A r → Body F A (.oplus l r)
  | pair : {l r : PolyF} → Body F A l → Body F A r → Body F A (.otimes l r)
end

/-- `Body F A G → ⟦G⟧ A (Mu F A)`. -/
@[expose] public def toSem {F A} : (G : PolyF) → Body F A G → sem G A (Mu F A)
  | .one,        .unit     => PUnit.unit
  | .arg₁,       .fst a    => a
  | .arg₂,       .snd m    => m
  | .oplus _ _,  .inl b    => Sum.inl (toSem _ b)
  | .oplus _ _,  .inr b    => Sum.inr (toSem _ b)
  | .otimes _ _, .pair x y => (toSem _ x, toSem _ y)

/-- `⟦G⟧ A (Mu F A) → Body F A G`. -/
@[expose] public def ofSem {F A} : (G : PolyF) → sem G A (Mu F A) → Body F A G
  | .zer,        e           => e.elim
  | .one,        _           => .unit
  | .arg₁,       a           => .fst a
  | .arg₂,       m           => .snd m
  | .oplus _ _,  Sum.inl x   => .inl (ofSem _ x)
  | .oplus _ _,  Sum.inr x   => .inr (ofSem _ x)
  | .otimes _ _, (x, y)      => .pair (ofSem _ x) (ofSem _ y)

public theorem ofSem_toSem {F A} : (G : PolyF) → (b : Body F A G) → ofSem G (toSem G b) = b
  | .one,        .unit     => rfl
  | .arg₁,       .fst _    => rfl
  | .arg₂,       .snd _    => rfl
  | .oplus _ _,  .inl b    => congrArg Body.inl (ofSem_toSem _ b)
  | .oplus _ _,  .inr b    => congrArg Body.inr (ofSem_toSem _ b)
  | .otimes _ _, .pair x y => by rw [toSem, ofSem, ofSem_toSem _ x, ofSem_toSem _ y]

public theorem toSem_ofSem {F A} : (G : PolyF) → (s : sem G A (Mu F A)) → toSem G (ofSem G s) = s
  | .zer,        e         => e.elim
  | .one,        _         => rfl
  | .arg₁,       _         => rfl
  | .arg₂,       _         => rfl
  | .oplus _ _,  Sum.inl x => congrArg Sum.inl (toSem_ofSem _ x)
  | .oplus _ _,  Sum.inr x => congrArg Sum.inr (toSem_ofSem _ x)
  | .otimes _ _, (x, y)    => by rw [ofSem, toSem, toSem_ofSem _ x, toSem_ofSem _ y]

/-- The public initial-algebra map `In : ⟦F⟧ A (μ F A) → μ F A` (aopa `In`). -/
@[expose] public def In {F A} (s : sem F A (Mu F A)) : Mu F A := Mu.In (ofSem F s)

/-- Its inverse `out : μ F A → ⟦F⟧ A (μ F A)`. -/
@[expose] public def out {F A} : Mu F A → sem F A (Mu F A) | Mu.In b => toSem F b

theorem out_In {F A} (s : sem F A (Mu F A)) : out (In s) = s := toSem_ofSem F s
public theorem In_out {F A} (m : Mu F A) : In (out m) = m := by
  cases m with | In b => show Mu.In (ofSem F (toSem F b)) = Mu.In b; rw [ofSem_toSem]

/-- `graph In`, with its `Rel(Set)` object types pinned at level `0`. -/
@[expose] public def inGraph (F : PolyF) (A : Type) : Fo F ⟨A⟩ ⟨Mu F A⟩ ⟶ (⟨Mu F A⟩ : RelSet.{0}) := graph In

/-- `In` is surjective (aopa `In-surjective`): `𝟙 ⊑ In° ≫ In` (as a `Mu ⟶ Mu` relation). -/
theorem In_surjective {F} {A : Type} :
    (Cat.id (⟨Mu F A⟩ : RelSet.{0})) ⊑ (inGraph F A)° ≫ inGraph F A := by
  rw [le_iff]; intro m m' h
  have hmm : m = m' := h
  refine ⟨out m, (In_out m).symm, ?_⟩
  rw [← hmm]; exact (In_out m).symm

/-- `In` is injective (aopa `In-injective`): `In ≫ In° ⊑ 𝟙` (as a `⟦F⟧ ⟶ ⟦F⟧` relation). -/
theorem In_injective {F} {A : Type} :
    inGraph F A ≫ (inGraph F A)° ⊑ Cat.id (Fo F ⟨A⟩ ⟨Mu F A⟩) := by
  rw [le_iff]; intro s s' h
  obtain ⟨m, hs, hs'⟩ := h
  have hs2 : m = In s' := hs'
  have heq : In s = In s' := hs.symm.trans hs2
  calc s = out (In s)  := (out_In s).symm
    _ = out (In s')    := by rw [heq]
    _ = s'             := out_In s'

/-! ## Action on functions (`bimap`, `fmap`) -/

/-- aopa `bimap`. -/
@[expose] public def bimap : (F : PolyF) → {A₁ A₂ B₁ B₂ : Type} → (A₁ → A₂) → (B₁ → B₂) →
    sem F A₁ B₁ → sem F A₂ B₂
  | .zer,        _, _, _, _, _, _ => fun e => e.elim
  | .one,        _, _, _, _, _, _ => fun _ => PUnit.unit
  | .arg₁,       _, _, _, _, f, _ => fun a => f a
  | .arg₂,       _, _, _, _, _, g => fun b => g b
  | .oplus l r,  _, _, _, _, f, g => fun u => match u with
      | Sum.inl x => Sum.inl (bimap l f g x)
      | Sum.inr y => Sum.inr (bimap r f g y)
  | .otimes l r, _, _, _, _, f, g => fun u => (bimap l f g u.1, bimap r f g u.2)

/-- aopa `fmap F = bimap F id`. -/
@[expose] public def fmap (F : PolyF) {A B₁ B₂ : Type} (g : B₁ → B₂) : sem F A B₁ → sem F A B₂ := bimap F id g

/-- aopa `bimap-comp`: `bimap (f∘h) (g∘k) = bimap f g ∘ bimap h k`. -/
public theorem bimap_comp (F : PolyF) {A₁ A₂ A₃ B₁ B₂ B₃ : Type}
    (f : A₂ → A₃) (g : B₂ → B₃) (h : A₁ → A₂) (k : B₁ → B₂) :
    ∀ x, bimap F (f ∘ h) (g ∘ k) x = bimap F f g (bimap F h k x) := by
  induction F with
  | zer => intro e; exact e.elim
  | one => intro _; rfl
  | arg₁ => intro _; rfl
  | arg₂ => intro _; rfl
  | oplus l r ihl ihr =>
      intro u; cases u with
      | inl x => exact congrArg Sum.inl (ihl x)
      | inr y => exact congrArg Sum.inr (ihr y)
  | otimes l r ihl ihr =>
      intro u; exact Prod.ext (ihl u.1) (ihr u.2)

/-! ## Predicate lifting (`bimapP`, `fmapP`) and coreflexives -/

/-- aopa `bimapP`. -/
@[expose] public def bimapP : (F : PolyF) → {A B : Type} → (A → Prop) → (B → Prop) → sem F A B → Prop
  | .zer,        _, _, _, _ => fun e => e.elim
  | .one,        _, _, _, _ => fun _ => True
  | .arg₁,       _, _, P, _ => fun a => P a
  | .arg₂,       _, _, _, Q => fun b => Q b
  | .oplus l r,  _, _, P, Q => fun u => match u with
      | Sum.inl x => bimapP l P Q x
      | Sum.inr y => bimapP r P Q y
  | .otimes l r, _, _, P, Q => fun u => bimapP l P Q u.1 ∧ bimapP r P Q u.2

/-- aopa `fmapP F P = bimapP F (const ⊤) P`. -/
@[expose] public def fmapP (F : PolyF) {A B : Type} (Q : B → Prop) : sem F A B → Prop :=
  bimapP F (fun _ => True) Q

/-- The coreflexive (partial identity) `P¿` of a predicate `P` (aopa `_¿`). -/
def corefl {b : RelSet.{0}} (P : b.carrier → Prop) : b ⟶ b := fun x y => x = y ∧ P x

/-! ## Action on relations — the relator (`bimapR`, `fmapR`) -/

/-- aopa `bimapR`: the polynomial functor's action on `Rel(Set)` morphisms. -/
@[expose] public def bimapR : (F : PolyF) → {a₁ a₂ b₁ b₂ : RelSet.{0}} → (a₁ ⟶ a₂) → (b₁ ⟶ b₂) →
    (Fo F a₁ b₁ ⟶ Fo F a₂ b₂)
  | .zer,        _, _, _, _, _, _ => fun e _ => e.elim
  | .one,        _, _, _, _, _, _ => fun _ _ => True
  | .arg₁,       _, _, _, _, R, _ => fun x y => R x y
  | .arg₂,       _, _, _, _, _, S => fun x y => S x y
  | .oplus l r,  _, _, _, _, R, S => fun u v => match u, v with
      | Sum.inl x, Sum.inl y => bimapR l R S x y
      | Sum.inr x, Sum.inr y => bimapR r R S x y
      | _,         _         => False
  | .otimes l r, _, _, _, _, R, S => fun u v => bimapR l R S u.1 v.1 ∧ bimapR r R S u.2 v.2

/-- aopa `fmapR F R = bimapR F idR R`. -/
@[expose] public def fmapR (F : PolyF) {a b₁ b₂ : RelSet.{0}} (R : b₁ ⟶ b₂) : Fo F a b₁ ⟶ Fo F a b₂ :=
  bimapR F (Cat.id a) R

/-- aopa `bimapR-functor-⊑`: `⟦F⟧R ≫ ⟦F⟧R' ⊑ ⟦F⟧(R≫R')`. -/
public theorem bimapR_functor_le (F : PolyF) {a₁ a₂ a₃ b₁ b₂ b₃ : RelSet.{0}}
    (R : a₁ ⟶ a₂) (R' : a₂ ⟶ a₃) (S : b₁ ⟶ b₂) (S' : b₂ ⟶ b₃) :
    bimapR F R S ≫ bimapR F R' S' ⊑ bimapR F (R ≫ R') (S ≫ S') := by
  induction F with
  | zer => rw [le_iff]; intro e _ _; exact e.elim
  | one => rw [le_iff]; intro _ _ _; trivial
  | arg₁ => rw [le_iff]; intro x z h; exact h
  | arg₂ => rw [le_iff]; intro x z h; exact h
  | oplus l r ihl ihr =>
      rw [le_iff]; intro u w h; obtain ⟨v, h1, h2⟩ := h
      cases u with
      | inl x => cases v with
        | inl y => cases w with
          | inl z => exact le_iff.mp ihl x z ⟨y, h1, h2⟩
          | inr z => exact (h2 : False).elim
        | inr y => exact (h1 : False).elim
      | inr x => cases v with
        | inr y => cases w with
          | inr z => exact le_iff.mp ihr x z ⟨y, h1, h2⟩
          | inl z => exact (h2 : False).elim
        | inl y => exact (h1 : False).elim
  | otimes l r ihl ihr =>
      rw [le_iff]; intro u w h; obtain ⟨v, h1, h2⟩ := h
      exact ⟨le_iff.mp ihl u.1 w.1 ⟨v.1, h1.1, h2.1⟩, le_iff.mp ihr u.2 w.2 ⟨v.2, h1.2, h2.2⟩⟩

/-- aopa `bimapR-functor-⊒`: `⟦F⟧(R≫R') ⊑ ⟦F⟧R ≫ ⟦F⟧R'`. -/
public theorem bimapR_functor_ge (F : PolyF) {a₁ a₂ a₃ b₁ b₂ b₃ : RelSet.{0}}
    (R : a₁ ⟶ a₂) (R' : a₂ ⟶ a₃) (S : b₁ ⟶ b₂) (S' : b₂ ⟶ b₃) :
    bimapR F (R ≫ R') (S ≫ S') ⊑ bimapR F R S ≫ bimapR F R' S' := by
  induction F with
  | zer => rw [le_iff]; intro e _ _; exact e.elim
  | one => rw [le_iff]; intro _ _ _; exact ⟨PUnit.unit, trivial, trivial⟩
  | arg₁ => rw [le_iff]; intro x z h; exact h
  | arg₂ => rw [le_iff]; intro x z h; exact h
  | oplus l r ihl ihr =>
      rw [le_iff]; intro u w h
      cases u with
      | inl x => cases w with
        | inl z => obtain ⟨y, hxy, hyz⟩ := le_iff.mp ihl x z h; exact ⟨Sum.inl y, hxy, hyz⟩
        | inr z => exact (h : False).elim
      | inr x => cases w with
        | inr z => obtain ⟨y, hxy, hyz⟩ := le_iff.mp ihr x z h; exact ⟨Sum.inr y, hxy, hyz⟩
        | inl z => exact (h : False).elim
  | otimes l r ihl ihr =>
      rw [le_iff]; intro u w h
      obtain ⟨y1, hxy1, hyz1⟩ := le_iff.mp ihl u.1 w.1 h.1
      obtain ⟨y2, hxy2, hyz2⟩ := le_iff.mp ihr u.2 w.2 h.2
      exact ⟨(y1, y2), ⟨hxy1, hxy2⟩, ⟨hyz1, hyz2⟩⟩

/-- aopa `bimapR-functor`: `⟦F⟧R ≫ ⟦F⟧R' = ⟦F⟧(R≫R')`. -/
public theorem bimapR_functor (F : PolyF) {a₁ a₂ a₃ b₁ b₂ b₃ : RelSet.{0}}
    (R : a₁ ⟶ a₂) (R' : a₂ ⟶ a₃) (S : b₁ ⟶ b₂) (S' : b₂ ⟶ b₃) :
    bimapR F R S ≫ bimapR F R' S' = bimapR F (R ≫ R') (S ≫ S') :=
  le_antisymm (bimapR_functor_le F R R' S S') (bimapR_functor_ge F R R' S S')

/-- aopa `bimapR-monotonic`. -/
theorem bimapR_monotonic (F : PolyF) {a₁ a₂ b₁ b₂ : RelSet.{0}} {R S : a₁ ⟶ a₂} {T U : b₁ ⟶ b₂}
    (hRS : R ⊑ S) (hTU : T ⊑ U) : bimapR F R T ⊑ bimapR F S U := by
  induction F with
  | zer => rw [le_iff]; intro e _ _; exact e.elim
  | one => rw [le_iff]; intro _ _ _; trivial
  | arg₁ => rw [le_iff]; intro x y h; exact le_iff.mp hRS x y h
  | arg₂ => rw [le_iff]; intro x y h; exact le_iff.mp hTU x y h
  | oplus l r ihl ihr =>
      rw [le_iff]; intro u v h
      cases u with
      | inl x => cases v with
        | inl y => exact le_iff.mp ihl x y h
        | inr y => exact (h : False).elim
      | inr x => cases v with
        | inr y => exact le_iff.mp ihr x y h
        | inl y => exact (h : False).elim
  | otimes l r ihl ihr =>
      rw [le_iff]; intro u v h; exact ⟨le_iff.mp ihl u.1 v.1 h.1, le_iff.mp ihr u.2 v.2 h.2⟩

/-- aopa `bimapR-cong` (with `≑` as `=`). -/
theorem bimapR_cong (F : PolyF) {a₁ a₂ b₁ b₂ : RelSet.{0}} {R S : a₁ ⟶ a₂} {T U : b₁ ⟶ b₂}
    (hRS : R = S) (hTU : T = U) : bimapR F R T = bimapR F S U := by rw [hRS, hTU]

/-- `(𝟙)° = 𝟙` in `Rel(Set)`. -/
public theorem recip_id {a : RelSet.{0}} : (Cat.id a)° = Cat.id a := hom_ext fun x y => eq_comm

/-- aopa `fmapR-functor`: `⟦F⟧R ≫ ⟦F⟧S = ⟦F⟧(R≫S)`. -/
public theorem fmapR_functor (F : PolyF) (a : RelSet.{0}) {b₁ b₂ b₃ : RelSet.{0}}
    (R : b₁ ⟶ b₂) (S : b₂ ⟶ b₃) :
    (fmapR F R : Fo F a b₁ ⟶ Fo F a b₂) ≫ fmapR F S = fmapR F (R ≫ S) := by
  show bimapR F (Cat.id a) R ≫ bimapR F (Cat.id a) S = bimapR F (Cat.id a) (R ≫ S)
  rw [bimapR_functor, Cat.id_comp]

/-- aopa `fmapR-monotonic`. -/
theorem fmapR_monotonic (F : PolyF) {a b₁ b₂ : RelSet.{0}} {R S : b₁ ⟶ b₂} (h : R ⊑ S) :
    (fmapR F R : Fo F a b₁ ⟶ Fo F a b₂) ⊑ fmapR F S :=
  bimapR_monotonic F (le_refl (Cat.id a)) h

/-- aopa `fmapR-cong`. -/
theorem fmapR_cong (F : PolyF) {a b₁ b₂ : RelSet.{0}} {R S : b₁ ⟶ b₂} (h : R = S) :
    (fmapR F R : Fo F a b₁ ⟶ Fo F a b₂) = fmapR F S := by rw [h]

/-- aopa `bimapR-˘-preservation`: `(⟦F⟧R S)° = ⟦F⟧R° S°`. -/
public theorem bimapR_recip (F : PolyF) {a₁ a₂ b₁ b₂ : RelSet.{0}} (R : a₁ ⟶ a₂) (S : b₁ ⟶ b₂) :
    (bimapR F R S)° = bimapR F R° S° := by
  induction F with
  | zer => apply hom_ext; intro u v; exact (u : Empty).elim
  | one => apply hom_ext; intro _ _; exact ⟨fun _ => trivial, fun _ => trivial⟩
  | arg₁ => apply hom_ext; intro _ _; exact Iff.rfl
  | arg₂ => apply hom_ext; intro _ _; exact Iff.rfl
  | oplus l r ihl ihr =>
      apply hom_ext; intro u v
      cases u with
      | inl x => cases v with
        | inl y => exact iff_of_eq (congrFun (congrFun ihl x) y)
        | inr y => exact Iff.rfl
      | inr x => cases v with
        | inl y => exact Iff.rfl
        | inr y => exact iff_of_eq (congrFun (congrFun ihr x) y)
  | otimes l r ihl ihr =>
      apply hom_ext; intro u v
      have el := iff_of_eq (congrFun (congrFun ihl u.1) v.1)
      have er := iff_of_eq (congrFun (congrFun ihr u.2) v.2)
      exact ⟨fun h => ⟨el.mp h.1, er.mp h.2⟩, fun h => ⟨el.mpr h.1, er.mpr h.2⟩⟩

/-- aopa `fmapR-˘-preservation`: `(⟦F⟧R)° = ⟦F⟧R°`. -/
public theorem fmapR_recip (F : PolyF) {a b₁ b₂ : RelSet.{0}} (R : b₁ ⟶ b₂) :
    (fmapR F R : Fo F a b₁ ⟶ Fo F a b₂)° = fmapR F R° := by
  show (bimapR F (Cat.id a) R)° = bimapR F (Cat.id a) R°
  rw [bimapR_recip, recip_id]

/-- aopa `bimap-bimapR`: `graph (bimap F f g) = ⟦F⟧ (graph f) (graph g)`. -/
public theorem bimap_bimapR (F : PolyF) {A₁ A₂ B₁ B₂ : Type} (f : A₁ → A₂) (g : B₁ → B₂) :
    (graph (bimap F f g) : Fo F ⟨A₁⟩ ⟨B₁⟩ ⟶ Fo F ⟨A₂⟩ ⟨B₂⟩)
      = bimapR F (graph f) (graph g) := by
  induction F with
  | zer => apply hom_ext; intro u v; exact (u : Empty).elim
  | one => apply hom_ext; intro u v; exact ⟨fun _ => trivial, fun _ => Subsingleton.elim _ _⟩
  | arg₁ => apply hom_ext; intro _ _; exact Iff.rfl
  | arg₂ => apply hom_ext; intro _ _; exact Iff.rfl
  | oplus l r ihl ihr =>
      apply hom_ext; intro u v
      cases u with
      | inl x => cases v with
        | inl y =>
            have this' := iff_of_eq (congrFun (congrFun ihl x) y)
            exact ⟨fun h => this'.mp (Sum.inl.inj h), fun h => congrArg Sum.inl (this'.mpr h)⟩
        | inr y =>
            constructor
            · intro h; change Sum.inr y = Sum.inl (bimap l f g x) at h; contradiction
            · intro h; exact (h : False).elim
      | inr x => cases v with
        | inl y =>
            constructor
            · intro h; change Sum.inl y = Sum.inr (bimap r f g x) at h; contradiction
            · intro h; exact (h : False).elim
        | inr y =>
            have this' := iff_of_eq (congrFun (congrFun ihr x) y)
            exact ⟨fun h => this'.mp (Sum.inr.inj h), fun h => congrArg Sum.inr (this'.mpr h)⟩
  | otimes l r ihl ihr =>
      apply hom_ext; intro u v
      have el := iff_of_eq (congrFun (congrFun ihl u.1) v.1)
      have er := iff_of_eq (congrFun (congrFun ihr u.2) v.2)
      constructor
      · intro h
        have hp : v = (bimap l f g u.1, bimap r f g u.2) := h
        exact ⟨el.mp (congrArg Prod.fst hp), er.mp (congrArg Prod.snd hp)⟩
      · intro h
        have h1 : v.1 = bimap l f g u.1 := el.mpr h.1
        have h2 : v.2 = bimap r f g u.2 := er.mpr h.2
        show v = (bimap l f g u.1, bimap r f g u.2)
        rw [← h1, ← h2]

/-- aopa `fmap-fmapR`: `graph (fmap F g) = ⟦F⟧ (graph g)`. -/
public theorem fmap_fmapR (F : PolyF) {A B₁ B₂ : Type} (g : B₁ → B₂) :
    (graph (fmap F g) : Fo F ⟨A⟩ ⟨B₁⟩ ⟶ Fo F ⟨A⟩ ⟨B₂⟩) = fmapR F (graph g) := by
  have h := bimap_bimapR F (id : A → A) g
  show (graph (bimap F id g) : Fo F ⟨A⟩ ⟨B₁⟩ ⟶ Fo F ⟨A⟩ ⟨B₂⟩) = bimapR F (Cat.id ⟨A⟩) (graph g)
  rw [h]; congr 1
  exact hom_ext fun x y => by
    show (y = id x) ↔ (x = y); exact ⟨fun e => e.symm, fun e => e.symm⟩

end Freyd.Alg.RelSet.Poly
