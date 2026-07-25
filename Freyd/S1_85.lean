/-
  Freyd & Scedrov, *Categories and Allegories* §1.85
  Exponential categories (cartesian closed).

  §1.85  EXPONENTIAL CATEGORY: binary products + for each A,
         the functor A × - has a right adjoint (-)^A.
  §1.852 Poset exponential ↔ binary meets + Heyting arrow
  §1.853 B^A as a bifunctor (covariant in B, contravariant in A)
  §1.854 Σ ⊣ Δ adjunction and Π dependent products
  §1.857 EXPONENTIAL IDEAL, REPLETE SUBCATEGORY; theorems
  §1.858 KURATOWSKI INTERIOR, LAWVERE-TIERNEY CLOSURE; theorem
  §1.859 BASEABLE objects, inclusion preserves equalizers
-/

import Freyd.S1_10
import Freyd.S1_18
import Freyd.S1_41
import Freyd.S1_42
import Freyd.S1_31
import Freyd.S1_34
import Freyd.S1_43
import Freyd.S1_80
import Freyd.S1_44


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-! ### Product functor A × -

  For each object A, the endofunctor A × - sends X ↦ A × X, f ↦ A × f. -/

section ProductFunctor

variable [hp' : HasBinaryProducts 𝒞]

/-- A × f : A × X → A × Y, with (A×f)≫fst = fst, (A×f)≫snd = snd≫f. -/
def prodMap (A X Y : 𝒞) (f : X ⟶ Y) : prod A X ⟶ prod A Y :=
  pair (X := prod A X) (A := A) (B := Y) fst (snd ≫ f)

theorem prodMap_fst (A X Y : 𝒞) (f : X ⟶ Y) : prodMap A X Y f ≫ fst (A := A) (B := Y) = fst := by
  dsimp [prodMap]; rw [fst_pair]

theorem prodMap_snd (A X Y : 𝒞) (f : X ⟶ Y) : prodMap A X Y f ≫ snd = snd ≫ f := by
  dsimp [prodMap]; rw [snd_pair]

-- (pair_fst_snd is defined canonically in S1_42 §1.423; reused here via import.)

theorem prodMap_id (A X : 𝒞) : prodMap A X X (Cat.id X) = Cat.id (prod A X) := by
  dsimp [prodMap]; rw [Cat.comp_id, pair_fst_snd]

theorem prodMap_comp (A X Y Z : 𝒞) (f : X ⟶ Y) (g : Y ⟶ Z) :
    prodMap A X Z (f ≫ g) = prodMap A X Y f ≫ prodMap A Y Z g := by
  dsimp [prodMap]
  let RHS := pair (X := prod A X) (A := A) (B := Y) fst (snd ≫ f) ≫
             pair (X := prod A Y) (A := A) (B := Z) fst (snd ≫ g)
  have h_fst : RHS ≫ fst (A := A) (B := Z) = fst := by
    dsimp [RHS]; rw [Cat.assoc, fst_pair, fst_pair]
  have h_snd : RHS ≫ snd = snd ≫ (f ≫ g) := by
    dsimp [RHS]
    rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair, Cat.assoc]
  apply (pair_uniq (X := prod A X) (A := A) (B := Z) fst (snd ≫ (f ≫ g)) RHS h_fst h_snd).symm

/-- Functor instance for A × -. -/
def prodFunctor (A : 𝒞) : Functor 𝒞 𝒞 where
  obj := λ X => prod A X
  map {X Y} f := prodMap A X Y f
  map_id X := prodMap_id A X
  map_comp f g := prodMap_comp A _ _ _ f g

end ProductFunctor

/-! ## §1.85  Exponential categories

  A category with binary products is EXPONENTIAL if each functor
  A × - has a right adjoint.  The counit is the EVALUATION MAP e,
  the adjoint transpose is CARRYING (curry). -/

class HasExponentials (𝒞 : Type u) [Cat.{v} 𝒞] extends HasBinaryProducts 𝒞 where
  exp_obj : 𝒞 → 𝒞 → 𝒞
  eval_map {A B : 𝒞} : prod A (exp_obj A B) ⟶ B
  curry_map {A B X : 𝒞} (f : prod A X ⟶ B) : X ⟶ exp_obj A B
  curry_eval {A B X : 𝒞} (f : prod A X ⟶ B) :
    prodMap A X (exp_obj A B) (curry_map f) ≫ eval_map = f
  curry_unique {A B X : 𝒞} {f : prod A X ⟶ B} {g : X ⟶ exp_obj A B}
    (h_eq : prodMap A X (exp_obj A B) g ≫ eval_map = f) : g = curry_map f

variable [HasExponentials 𝒞]

/-- The exponential object B^A (§1.85). -/
def exp (A B : 𝒞) : 𝒞 := HasExponentials.exp_obj A B

notation:30 B " ^^ " A:30 => exp A B

/-- The EVALUATION MAP e : A × B^A → B (§1.85). -/
def eval_exp (A B : 𝒞) : prod A (B ^^ A) ⟶ B := HasExponentials.eval_map (A := A) (B := B)

/-- The EXPONENTIAL TRANSPOSE (curry): f : A × X → B gives Λf : X → B^A. -/
def curry {A B X : 𝒞} (f : prod A X ⟶ B) : X ⟶ B ^^ A := HasExponentials.curry_map f

/-- The characteristic equation: (A × curry f) ≫ eval = f. -/
@[simp] theorem curry_eval_eq {A B X : 𝒞} (f : prod A X ⟶ B) :
    prodMap A X (B ^^ A) (curry f) ≫ eval_exp A B = f :=
  HasExponentials.curry_eval f

/-- curry is unique: if (A × g) ≫ eval = f then g = curry f. -/
theorem curry_unique_eq {A B X : 𝒞} {f : prod A X ⟶ B} {g : X ⟶ B ^^ A}
    (h : prodMap A X (B ^^ A) g ≫ eval_exp A B = f) : g = curry f :=
  HasExponentials.curry_unique h

/-- curry is injective. -/
theorem curry_inj {A B X : 𝒞} {f₁ f₂ : prod A X ⟶ B}
    (h : curry f₁ = curry f₂) : f₁ = f₂ := by
  rw [← curry_eval_eq f₁, ← curry_eval_eq f₂, h]

/-- `curry` commutes with precomposition in the parameter variable. -/
theorem curry_precomp {A B X Y : 𝒞} (u : X ⟶ Y) (g : prod A Y ⟶ B) :
    u ≫ curry g = curry (prodMap A X Y u ≫ g) := by
  apply curry_unique_eq
  rw [prodMap_comp, Cat.assoc, curry_eval_eq]

/-- The identity on `B^A` is `curry eval`. -/
theorem id_eq_curry_eval (A B : 𝒞) : Cat.id (B ^^ A) = curry (eval_exp A B) := by
  apply curry_unique_eq; rw [prodMap_id, Cat.id_comp]

/-! ## §1.853  Covariant exponential map f^A : B^A → C^A

  In an exponential category, B^A is a bifunctor: covariant in B and
  contravariant in A.  The covariant action sends f : B → C to
  f^A : B^A → C^A, defined as the unique map such that
  (A × f^A) ≫ eval_C = eval_B ≫ f.

  The *contravariant* action g ↦ B^g for g : A₁ → A₂ is in §1.95 as
  `expMap` (S1_95.lean); we name the covariant action `expCovMap`
  to avoid a clash. -/

section ExpBifunctor

/-- Covariant exponential map: given f : B → C, the map f^A : B^A → C^A is
    the unique map with (A × f^A) ≫ eval_C = eval_B ≫ f  (§1.853).
    Concretely: curry(eval_B ≫ f). -/
def expCovMap (A : 𝒞) {B C : 𝒞} (f : B ⟶ C) : B ^^ A ⟶ C ^^ A :=
  curry (eval_exp A B ≫ f)

/-- Defining equation: (A × expCovMap f) ≫ eval = eval ≫ f. -/
theorem expCovMap_eval (A : 𝒞) {B C : 𝒞} (f : B ⟶ C) :
    prodMap A (B ^^ A) (C ^^ A) (expCovMap A f) ≫ eval_exp A C = eval_exp A B ≫ f :=
  curry_eval_eq (eval_exp A B ≫ f)

/-- expCovMap preserves identity: id^A = id. -/
theorem expCovMap_id (A B : 𝒞) : expCovMap A (Cat.id B) = Cat.id (B ^^ A) := by
  symm; apply curry_unique_eq
  rw [Cat.comp_id, prodMap_id, Cat.id_comp]

/-- expCovMap preserves composition: (f ≫ g)^A = f^A ≫ g^A. -/
theorem expCovMap_comp (A : 𝒞) {B C D : 𝒞} (f : B ⟶ C) (g : C ⟶ D) :
    expCovMap A (f ≫ g) = expCovMap A f ≫ expCovMap A g := by
  symm; apply curry_unique_eq
  rw [prodMap_comp, Cat.assoc, expCovMap_eval, ← Cat.assoc, expCovMap_eval, Cat.assoc]

/-- The covariant exponential (-)^A as a Functor instance (covariant in B). -/
def expCovFunctor (A : 𝒞) : Functor 𝒞 𝒞 where
  obj := fun B => B ^^ A
  map f := expCovMap A f
  map_id B := expCovMap_id A B
  map_comp f g := expCovMap_comp A f g

end ExpBifunctor

/-! ## §1.852  Poset exponential characterization

  A poset, viewed as a category, is exponential iff it has binary meets
  (∧) and for every a, b there exists b^a satisfying
      x ≤ b^a  ↔  a ∧ x ≤ b.
  The element b^a is precisely the Heyting arrow a → b [§1.72].

  Here we represent a poset-as-category via a type `P` with a preorder
  `le` such that hom-sets are propositions (thin category).  Binary meets
  are represented as a `HasBinaryMeets` predicate; the Heyting arrow is
  the right adjoint to meets. -/

/-- A POSET (or preorder) viewed as a thin category:
    objects are elements, at most one morphism between any two. -/
class ThinCategory (P : Type u) [Cat.{v} P] : Prop where
  thin : ∀ {A B : P} (f g : A ⟶ B), f = g

/-- The HEYTING ARROW a → b in a thin category with binary meets.
    By §1.72: x ≤ (a → b) iff a ∧ x ≤ b (§1.852).

    ONE concept (§1.72), THREE carriers — separate because the carrier's equality
    differs: here the carrier is the objects of a thin category, a preorder via
    `Nonempty (· ⟶ ·)` with meet = categorical product (no `=`-laws). Cf.
    `HeytingAlgebra` (S1_72) on the subobject preorder `Sub(A)`, and `HeytingLattice`
    (below) on an honest `le_antisymm` `Type` (a real poset with `=`-laws). -/
class HasHeytingArrow (P : Type u) [Cat.{v} P] [HasBinaryProducts P] where
  imp : P → P → P
  /-- Adjunction: a map x → (a→b) exists iff a∧x → b exists. -/
  imp_adj : ∀ (a b x : P), Nonempty (x ⟶ imp a b) ↔ Nonempty (prod a x ⟶ b)

/-- §1.852: A poset (thin category) is exponential iff it has binary meets
    and a Heyting arrow. -/
theorem poset_exponential_iff_meets_heytingArrow
    (P : Type u) [Cat.{v} P] [ThinCategory P] :
    Nonempty (HasExponentials P) ↔
    ∃ (hm : HasBinaryProducts P), Nonempty (@HasHeytingArrow P _ hm) := by
  constructor
  · -- (→) An exponential thin category has products and a Heyting arrow.
    rintro ⟨he⟩
    refine ⟨he.toHasBinaryProducts, ⟨?_⟩⟩
    refine
      { imp := fun a b => he.exp_obj a b
        imp_adj := fun a b x => ?_ }
    constructor
    · -- x ⟶ b^a  ↦  prodMap a x b^a g ≫ eval : a×x ⟶ b
      rintro ⟨g⟩
      exact ⟨@prodMap P _ he.toHasBinaryProducts a x (he.exp_obj a b) g ≫ he.eval_map⟩
    · -- a×x ⟶ b  ↦  curry : x ⟶ b^a
      rintro ⟨f⟩
      exact ⟨he.curry_map f⟩
  · -- (←) Products + Heyting arrow give exponentials (curry equations are free in a thin cat).
    rintro ⟨hm, ⟨ha⟩⟩
    refine ⟨?_⟩
    refine
      { toHasBinaryProducts := hm
        exp_obj := fun a b => ha.imp a b
        eval_map := fun {A B} => Classical.choice ((ha.imp_adj A B (ha.imp A B)).mp ⟨Cat.id _⟩)
        curry_map := fun {A B X} f => Classical.choice ((ha.imp_adj A B X).mpr ⟨f⟩)
        curry_eval := fun {A B X} f => ThinCategory.thin _ _
        curry_unique := fun {A B X f g} _ => ThinCategory.thin _ _ }

/-! ## §1.854  Σ ⊣ Δ adjunction; Π dependent products

  For any object B in a category A with binary products, the forgetful
  functor Σ : A/B → A has a right adjoint Δ : A → A/B defined by
      Δ(Y) = ⟨Y × B, snd⟩  (the slice object over B with projection snd).
  The adjunction bijection is natural: Hom_{A/B}(X, Δ Y) ≅ Hom_A(Σ X, Y).

  When A also has exponentials, Δ : A → A/B has a further right adjoint
  Π : A/B → A with Π(⟨A, h : A→B⟩) = A^B  (§1.854). -/

section SigmaDeltaAdj

/-- The DIAGONAL functor Δ : 𝒞 → Over B.  Sends Y ↦ ⟨Y × B, snd⟩ (§1.854). -/
def deltaObj (B Y : 𝒞) : Over B := ⟨prod Y B, snd⟩

/-- Δ on morphisms: given f : Y → Z, Δ(f) = pair (fst ≫ f) snd : Y×B → Z×B. -/
def deltaMap (B : 𝒞) {Y Z : 𝒞} (f : Y ⟶ Z) : OverHom (deltaObj B Y) (deltaObj B Z) :=
  ⟨pair (fst ≫ f) snd, snd_pair _ _⟩

/-- The DIAGONAL FUNCTOR Δ B : 𝒞 → Over B. -/
def deltaFunctor (B : 𝒞) : Functor 𝒞 (Over B) where
  obj := fun Y => deltaObj B Y
  map f := deltaMap B f
  map_id _Y := by
    apply OverHom.ext
    simp only [deltaMap]
    rw [Cat.comp_id]
    exact pair_fst_snd
  map_comp {_X _Y _Z} f g := by
    apply OverHom.ext
    simp only [deltaMap]
    -- goal: pair (fst ≫ f ≫ g) snd = (deltaMap B f ≫ deltaMap B g).f
    -- (deltaMap B f ≫ deltaMap B g).f = pair (fst ≫ f) snd ≫ pair (fst ≫ g) snd  (definitionally)
    change pair (fst ≫ f ≫ g) snd = pair (fst ≫ f) snd ≫ pair (fst ≫ g) snd
    exact (pair_uniq _ _ _
      (by rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair, Cat.assoc])
      (by rw [Cat.assoc, snd_pair, snd_pair])).symm

/-- Forward direction of the Σ ⊣ Δ bijection:
    f : Σ X → Y  ↦  ⟨pair f X.hom, ...⟩ : X → Δ Y in Over B. -/
def sigmaToOver {B : 𝒞} (X : Over B) {Y : 𝒞} (f : X.dom ⟶ Y) : OverHom X (deltaObj B Y) :=
  ⟨pair f X.hom, snd_pair _ _⟩

/-- Backward direction of the Σ ⊣ Δ bijection:
    h : X → Δ Y in Over B  ↦  h.f ≫ fst : Σ X → Y. -/
def overToSigma {B : 𝒞} (X : Over B) {Y : 𝒞} (h : OverHom X (deltaObj B Y)) : X.dom ⟶ Y :=
  h.f ≫ fst

/-- The bijection is a left inverse. -/
theorem sigmaToOver_overToSigma {B : 𝒞} (X : Over B) {Y : 𝒞}
    (h : OverHom X (deltaObj B Y)) :
    sigmaToOver X (overToSigma X h) = h := by
  apply OverHom.ext
  simp only [sigmaToOver, overToSigma]
  rw [← h.w]
  exact (pair_uniq _ _ h.f rfl rfl).symm

/-- The bijection is a right inverse. -/
theorem overToSigma_sigmaToOver {B : 𝒞} (X : Over B) {Y : 𝒞} (f : X.dom ⟶ Y) :
    overToSigma X (sigmaToOver X f) = f := by
  simp [overToSigma, sigmaToOver, fst_pair]

/-- §1.854: The forgetful functor Σ : A/B → A (= SliceForget B) is left adjoint
    to the diagonal functor Δ : A → A/B (sending Y ↦ ⟨Y×B, snd⟩).
    Adjunction: Hom_A(Σ X, Y) ≅ Hom_{A/B}(X, Δ Y), i.e., φ : (X.dom→Y) → OverHom X (ΔY). -/
def sigma_adj_delta (B : 𝒞) :
    @Adjunction (Over B) _ 𝒞 _ (sliceForgetFunctor B) (deltaFunctor B) :=
  { φ  := fun {X _Y} f => sigmaToOver X f      -- φ : X.dom → Y  ↦  OverHom X (Δ Y)
    ψ  := fun {X _Y} h => overToSigma X h      -- ψ : OverHom X (Δ Y)  ↦  X.dom → Y
    φψ := fun {X _Y} h => sigmaToOver_overToSigma X h
    ψφ := fun {X _Y} f => overToSigma_sigmaToOver X f
    φ_nat_left  := fun {_X' X _Y} a f => by
      apply OverHom.ext
      -- Functor.map a = a.f (sliceForgetFunctor); (a ≫ k).f = a.f ≫ k.f (OverHom.comp)
      change pair (a.f ≫ f) _X'.hom = a.f ≫ pair f X.hom
      exact (pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]) (by rw [Cat.assoc, snd_pair]; exact a.w)).symm
    φ_nat_right := fun {X _Y _Y'} f b => by
      apply OverHom.ext
      -- (k ≫ deltaMap B b).f = k.f ≫ pair (fst ≫ b) snd
      change pair (f ≫ b) X.hom = pair f X.hom ≫ pair (fst ≫ b) snd
      exact (pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair, ← Cat.assoc, fst_pair])
               (by rw [Cat.assoc, snd_pair, snd_pair])).symm }

/-! ### Π : A/B → A as right adjoint of Δ

  When 𝒞 has exponentials, Δ : A → A/B has a right adjoint Π given by
  Π(f : A → B) = A^B.  The adjunction bijection:
      Hom_{A/B}(Δ C, f)  ≅  Hom_A(C, A^B)
  sends k : C×B → A (with k ≫ f.hom = snd) to curry k : C → A^B. -/

/-- The DEPENDENT PRODUCT functor on objects: Π(f : A → B) = A^B (§1.854). -/
def piObj {B : 𝒞} (f : Over B) : 𝒞 := f.dom ^^ B

/-- Π on morphisms: given h : f → g in Over B, h^B : f.dom^B → g.dom^B. -/
def piMap {B : 𝒞} {f g : Over B} (h : OverHom f g) : piObj f ⟶ piObj g :=
  expCovMap B h.f

/-- Π is a functor Over B → 𝒞. -/
def piFunctor (B : 𝒞) : Functor (Over B) 𝒞 where
  obj := fun f : Over B => piObj f
  map h := piMap h
  map_id f := expCovMap_id B f.dom
  map_comp h k := expCovMap_comp B h.f k.f

/-- §1.854: When 𝒞 has exponentials, Δ : 𝒞 → Over B has a right adjoint
    Π : Over B → 𝒞 sending f : A → B to A^B (§1.854).
    One direction of the bijection Hom_{Over B}(Δ C, f) ≅ Hom_𝒞(C, f.dom^B):
    any over-map h : C×B → f.dom (with h ≫ f.hom = snd) gives
    curry(prodSwap ≫ h) : C → f.dom^B = piObj f.
    (The full bijection requires showing this is an isomorphism; here we give
    just the map direction OverHom(ΔC, f) → Hom(C, piObj f).) -/
theorem delta_adj_pi_overToExp (B : 𝒞) (C : 𝒞) (f : Over B) :
    Nonempty (OverHom (deltaObj B C) f) → Nonempty (C ⟶ piObj f) := by
  rintro ⟨h⟩
  -- h.f : prod C B → f.dom, h.w : h.f ≫ f.hom = snd
  -- curry (prodSwap C B ≫ h.f) : C → f.dom ^^ B = piObj f
  -- prodSwap B C : prod B C → prod C B; compose with h.f : prod C B → f.dom
  exact ⟨curry (prodSwap B C ≫ h.f)⟩

/-- §1.854(a): If for every object `A` the functor `(prod A -)` has a right adjoint `G A`,
    then the category has exponentials with `B^A := G A B`.
    BECAUSE (Freyd §1.854): `Hom(A×C, B) ≅ Hom(C, G A B)` witnesses `G A B = B^A`.
    In the book's language: taking `G A B = Π_A(Δ_A B) = Π_A(⟨B×A, snd⟩)`, the chain
    `Hom(A×C, B) ≅ OverHom(Δ_A C, Δ_A B) ≅ Hom(C, Π_A(Δ_A B))` gives `B^A = Π_A(Δ_A B)`. -/
theorem pi_implies_exponentials_854
    {𝒟 : Type u'} [Cat.{v} 𝒟] [hp : HasBinaryProducts 𝒟]
    (G : 𝒟 → Functor 𝒟 𝒟)
    (adj_G : ∀ (A : 𝒟), @Adjunction 𝒟 _ 𝒟 _ (@prodFunctor 𝒟 _ hp A) (G A)) :
    Nonempty (HasExponentials 𝒟) :=
  Nonempty.intro
    { toHasBinaryProducts := hp
      exp_obj A B := (G A).obj B
      eval_map {A B} := (adj_G A).ψ (Cat.id ((G A).obj B))
      curry_map {A B X} f := (adj_G A).φ f
      curry_eval {A B X} f := by
        have h := ψ_nat_left (adj_G A) ((adj_G A).φ f) (Cat.id ((G A).obj B))
        rw [Cat.comp_id] at h
        have : @prodMap 𝒟 _ hp A X ((G A).obj B) ((adj_G A).φ f) =
               (@prodFunctor 𝒟 _ hp A).map ((adj_G A).φ f) := rfl
        rw [this, ← h, (adj_G A).ψφ]
      curry_unique {A B X f g} h := by
        have hh := ψ_nat_left (adj_G A) g (Cat.id ((G A).obj B))
        rw [Cat.comp_id] at hh
        have : @prodMap 𝒟 _ hp A X ((G A).obj B) g =
               (@prodFunctor 𝒟 _ hp A).map g := rfl
        rw [this, ← hh] at h; rw [← (adj_G A).φψ g, h] }

/-! ### §1.854(b)  The TRUE dependent product Π_B ⊣ Δ_B (needs HasEqualizers)

  `piObj f = f.dom^^B` above is NOT Freyd's right adjoint of Δ for a general
  `f : Over B`; it only sees the domain, forgetting the structure map `f.hom`.
  The correct dependent product is

      Π(f) := equalizer of  ( expCovMap B f.hom , curry (fst : B×(f.dom^B) → B) ) : f.dom^B ⇉ B^B.

  Intuitively a "global section" `k : C → f.dom^B` lands in Π(f) exactly when its
  transpose `B×C → f.dom` is a section of `f.hom` (lands in the fibre), i.e. the
  square `eval ≫ f.hom = fst` holds — which is what equalizing the two maps says.
  This requires `HasEqualizers`; with it `Δ_B ⊣ Π_B` is a genuine adjunction. -/

section RealPi

variable [HasEqualizers 𝒞]

/-- §1.854(b): Freyd's dependent product `Π(f)`, the equalizer of `expCovMap B f.hom`
    and `curry (fst : B×(f.dom^B) → B)`. -/
def realPiObj {B : 𝒞} (f : Over B) : 𝒞 :=
  eqObj (expCovMap B f.hom) (curry (fst : prod B (f.dom ^^ B) ⟶ B))

/-- The equalizing condition for the forward transpose:
    `curry(prodSwap ≫ h.f)` equalizes the two parallel maps because both legs
    collapse to `curry (fst : B×C → B)` (one via `h.w : h.f ≫ f.hom = snd`). -/
theorem realPi_phi_cond {B C : 𝒞} (f : Over B) (h : OverHom (deltaObj B C) f) :
    curry (prodSwap B C ≫ h.f) ≫ expCovMap B f.hom
      = curry (prodSwap B C ≫ h.f) ≫ curry (fst : prod B (f.dom ^^ B) ⟶ B) := by
  have hL : curry (prodSwap B C ≫ h.f) ≫ expCovMap B f.hom = curry (fst : prod B C ⟶ B) := by
    unfold expCovMap
    rw [curry_precomp]; congr 1
    rw [← Cat.assoc, curry_eval_eq, Cat.assoc, show h.f ≫ f.hom = snd from h.w,
      show prodSwap B C ≫ snd = fst (A := B) (B := C) from snd_pair _ _]
  have hR : curry (prodSwap B C ≫ h.f) ≫ curry (fst : prod B (f.dom ^^ B) ⟶ B)
      = curry (fst : prod B C ⟶ B) := by rw [curry_precomp, prodMap_fst]
  rw [hL, hR]

/-- Forward transpose `φ : OverHom (Δ_B C) f → (C ⟶ Π(f))`. -/
def realPhi {B C : 𝒞} (f : Over B) (h : OverHom (deltaObj B C) f) : C ⟶ realPiObj f :=
  eqLift _ _ (curry (prodSwap B C ≫ h.f)) (realPi_phi_cond f h)

/-- The underlying arrow of the backward transpose is a section of `f.hom`
    (so it is a legitimate `OverHom` into `f`).  Uses `eqMap_eq` to see that
    `k ≫ eqMap` lands in the fibre. -/
theorem realPsi_w {B C : 𝒞} (f : Over B) (k : C ⟶ realPiObj f) :
    (prodSwap C B ≫ prodMap B C (f.dom ^^ B)
        (k ≫ eqMap (expCovMap B f.hom) (curry (fst : prod B (f.dom ^^ B) ⟶ B)))
        ≫ eval_exp B f.dom) ≫ f.hom = (deltaObj B C).hom := by
  show (prodSwap C B ≫ _) ≫ f.hom = (snd : prod C B ⟶ B)
  have key : eqMap (expCovMap B f.hom) (curry (fst : prod B (f.dom ^^ B) ⟶ B)) ≫ expCovMap B f.hom
      = eqMap (expCovMap B f.hom) (curry (fst : prod B (f.dom ^^ B) ⟶ B))
          ≫ curry (fst : prod B (f.dom ^^ B) ⟶ B) := eqMap_eq _ _
  have hcomp : prodMap B C (f.dom ^^ B)
      (k ≫ eqMap (expCovMap B f.hom) (curry (fst : prod B (f.dom ^^ B) ⟶ B)))
      ≫ eval_exp B f.dom ≫ f.hom = (fst : prod B C ⟶ B) := by
    apply curry_inj
    rw [← curry_precomp]
    show (k ≫ eqMap (expCovMap B f.hom) (curry (fst : prod B (f.dom ^^ B) ⟶ B)))
        ≫ expCovMap B f.hom = curry (fst : prod B C ⟶ B)
    rw [Cat.assoc, key, ← Cat.assoc, curry_precomp, prodMap_fst]
  rw [Cat.assoc, Cat.assoc, hcomp, show prodSwap C B ≫ fst = snd (A := C) (B := B) from fst_pair _ _]

/-- Backward transpose `ψ : (C ⟶ Π(f)) → OverHom (Δ_B C) f`. -/
def realPsi {B C : 𝒞} (f : Over B) (k : C ⟶ realPiObj f) : OverHom (deltaObj B C) f :=
  ⟨prodSwap C B ≫ prodMap B C (f.dom ^^ B)
      (k ≫ eqMap (expCovMap B f.hom) (curry (fst : prod B (f.dom ^^ B) ⟶ B)))
      ≫ eval_exp B f.dom, realPsi_w f k⟩

theorem realPsi_realPhi {B C : 𝒞} (f : Over B) (h : OverHom (deltaObj B C) f) :
    realPsi f (realPhi f h) = h := by
  apply OverHom.ext
  show prodSwap C B ≫ prodMap B C (f.dom ^^ B)
      (realPhi f h ≫ eqMap (expCovMap B f.hom) (curry (fst : prod B (f.dom ^^ B) ⟶ B)))
      ≫ eval_exp B f.dom = h.f
  rw [realPhi, eqLift_fac, curry_eval_eq, ← Cat.assoc, prodSwap_prodSwap, Cat.id_comp]

theorem realPhi_realPsi {B C : 𝒞} (f : Over B) (k : C ⟶ realPiObj f) :
    realPhi f (realPsi f k) = k := by
  show eqLift _ _ (curry (prodSwap B C ≫ (realPsi f k).f)) (realPi_phi_cond f (realPsi f k)) = k
  symm
  apply eqLift_uniq
  show k ≫ eqMap (expCovMap B f.hom) (curry (fst : prod B (f.dom ^^ B) ⟶ B))
      = curry (prodSwap B C ≫ (realPsi f k).f)
  rw [show (realPsi f k).f = prodSwap C B ≫ prodMap B C (f.dom ^^ B)
      (k ≫ eqMap (expCovMap B f.hom) (curry (fst : prod B (f.dom ^^ B) ⟶ B)))
      ≫ eval_exp B f.dom from rfl,
      ← Cat.assoc, prodSwap_prodSwap, Cat.id_comp]
  exact curry_unique_eq rfl

/-- The equalizing condition for `Π` on morphisms: `b : f → g` lifts to
    `eqMap_f ≫ expCovMap B b.f`, which equalizes the `g`-maps because
    `expCovMap` is functorial and `b.w : b.f ≫ g.hom = f.hom`. -/
theorem realPiMap_cond {B : 𝒞} {f g : Over B} (b : OverHom f g) :
    (eqMap (expCovMap B f.hom) (curry (fst : prod B (f.dom ^^ B) ⟶ B)) ≫ expCovMap B b.f)
        ≫ expCovMap B g.hom
      = (eqMap (expCovMap B f.hom) (curry (fst : prod B (f.dom ^^ B) ⟶ B)) ≫ expCovMap B b.f)
          ≫ curry (fst : prod B (g.dom ^^ B) ⟶ B) := by
  rw [Cat.assoc, ← expCovMap_comp, show b.f ≫ g.hom = f.hom from b.w, eqMap_eq, Cat.assoc]
  congr 1
  rw [curry_precomp, prodMap_fst]

/-- `Π` on morphisms: `b : f → g` gives `Π(b) : Π(f) → Π(g)`. -/
def realPiMap {B : 𝒞} {f g : Over B} (b : OverHom f g) : realPiObj f ⟶ realPiObj g :=
  eqLift _ _ (eqMap (expCovMap B f.hom) (curry (fst : prod B (f.dom ^^ B) ⟶ B)) ≫ expCovMap B b.f)
    (realPiMap_cond b)

theorem realPiMap_id {B : 𝒞} (f : Over B) : realPiMap (Cat.id f) = Cat.id (realPiObj f) := by
  symm; apply eqLift_uniq
  show Cat.id (realPiObj f) ≫ eqMap _ _ = eqMap _ _ ≫ expCovMap B (Cat.id f.dom)
  rw [Cat.id_comp, expCovMap_id, Cat.comp_id]

theorem realPiMap_comp {B : 𝒞} {f g h : Over B} (b : OverHom f g) (c : OverHom g h) :
    realPiMap (b ⊚ c) = realPiMap b ≫ realPiMap c := by
  symm; apply eqLift_uniq
  show (realPiMap b ≫ realPiMap c) ≫ eqMap _ _ = eqMap _ _ ≫ expCovMap B (b.f ≫ c.f)
  simp only [realPiMap]
  rw [Cat.assoc, eqLift_fac, ← Cat.assoc, eqLift_fac, Cat.assoc, ← expCovMap_comp]

/-- The TRUE dependent-product functor `Π_B : Over B → 𝒞` (§1.854(b)). -/
def realPiFunctor (B : 𝒞) : Functor (Over B) 𝒞 where
  obj := fun f : Over B => realPiObj f
  map b := realPiMap b
  map_id f := realPiMap_id f
  map_comp b c := realPiMap_comp b c

theorem realPhi_nat_left {B C' C : 𝒞} (f : Over B) (a : C' ⟶ C) (h : OverHom (deltaObj B C) f) :
    realPhi f (deltaMap B a ⊚ h) = a ≫ realPhi f h := by
  symm
  show a ≫ realPhi f h = eqLift _ _ (curry (prodSwap B C' ≫ (deltaMap B a ⊚ h).f)) _
  apply eqLift_uniq
  rw [Cat.assoc]
  show a ≫ (realPhi f h ≫ eqMap _ _) = curry (prodSwap B C' ≫ (deltaMap B a ⊚ h).f)
  rw [realPhi, eqLift_fac, curry_precomp]
  congr 1
  show prodMap B C' C a ≫ prodSwap B C ≫ h.f = prodSwap B C' ≫ (pair (fst ≫ a) snd ≫ h.f)
  rw [← Cat.assoc, ← Cat.assoc]
  congr 1
  rw [pair_uniq _ _ (prodMap B C' C a ≫ prodSwap B C) rfl rfl,
      pair_uniq _ _ (prodSwap B C' ≫ pair (fst ≫ a) snd) rfl rfl]
  congr 1
  · rw [Cat.assoc, show prodSwap B C ≫ fst = snd (A := B) (B := C) from fst_pair _ _,
      prodMap_snd, Cat.assoc, fst_pair, ← Cat.assoc,
      show prodSwap B C' ≫ fst = snd (A := B) (B := C') from fst_pair _ _]
  · rw [Cat.assoc, show prodSwap B C ≫ snd = fst (A := B) (B := C) from snd_pair _ _,
      prodMap_fst, Cat.assoc, snd_pair,
      show prodSwap B C' ≫ snd = fst (A := B) (B := C') from snd_pair _ _]

theorem realPhi_nat_right {B C : 𝒞} {f g : Over B}
    (h : OverHom (deltaObj B C) f) (b : OverHom f g) :
    realPhi g (h ⊚ b) = realPhi f h ≫ realPiMap b := by
  symm
  show realPhi f h ≫ realPiMap b = eqLift _ _ (curry (prodSwap B C ≫ (h ⊚ b).f)) _
  apply eqLift_uniq
  rw [Cat.assoc]
  show realPhi f h ≫ (realPiMap b ≫ eqMap _ _) = curry (prodSwap B C ≫ (h ⊚ b).f)
  rw [realPiMap, eqLift_fac, ← Cat.assoc, realPhi, eqLift_fac]
  show curry (prodSwap B C ≫ h.f) ≫ expCovMap B b.f = curry (prodSwap B C ≫ (h.f ≫ b.f))
  unfold expCovMap
  rw [curry_precomp, ← Cat.assoc, curry_eval_eq, Cat.assoc]

/-- §1.854(b): When `𝒞` has exponentials and equalizers, the diagonal
    `Δ_B : 𝒞 → Over B` has a right adjoint `Π_B : Over B → 𝒞`, the genuine
    dependent-product functor `Π(f) = eqObj (expCovMap B f.hom) (curry fst)`.
    Adjunction bijection `OverHom (Δ_B C) f ≅ (C ⟶ Π(f))`. -/
def delta_adj_realPi (B : 𝒞) :
    @Adjunction 𝒞 _ (Over B) _ (deltaFunctor B) (realPiFunctor B) :=
  { φ  := fun {_C _f} h => realPhi _f h
    ψ  := fun {_C _f} k => realPsi _f k
    φψ := fun {_C _f} k => realPhi_realPsi _f k
    ψφ := fun {_C _f} h => realPsi_realPhi _f h
    φ_nat_left  := fun {_C' _C _f} a h => realPhi_nat_left _f a h
    φ_nat_right := fun {_C _f _g} h b => realPhi_nat_right h b }

end RealPi

end SigmaDeltaAdj

/-! ## §1.857  Exponential ideal and replete subcategory

  If 𝒜 is an exponential category and 𝒜' is a FULL SUBCATEGORY, we call
  𝒜' an EXPONENTIAL IDEAL if for every A ∈ |𝒜| and B ∈ |𝒜'| the
  exponential B^A lies in 𝒜'.

  A REPLETE SUBCATEGORY is a subcategory closed under isomorphism type:
  if B ∈ 𝒜' and A ≅ B in 𝒜 then A ∈ 𝒜'.

  Theorems (§1.857):
  1. A full coreflective subcategory closed under binary products is
     exponential.
  2. A full replete reflective subcategory of an exponential category is
     an exponential ideal iff its reflections preserve products. -/

section ExponentialIdeal

variable {𝒜 : Type u} [Cat.{v} 𝒜] [HasExponentials 𝒜]
variable {𝒜' : Type u} [Cat.{v} 𝒜']

/-- YONEDA COROLLARY (object iso from a natural iso of representables).
    If post-composition `(· ≫ g) : (T ⟶ X) → (T ⟶ Y)` is a bijection for EVERY
    test object `T`, then `g` is an isomorphism.

    "Bijection of representables" is spelled out constructively (mathlib-free) as:
      * SURJECTIVE: every `k : T ⟶ Y` factors as `h ≫ g` for some `h : T ⟶ X`;
      * INJECTIVE: `h₁ ≫ g = h₂ ≫ g ⟹ h₁ = h₂`.
    This is exactly the data of a natural iso `Hom(-,X) ≅ Hom(-,Y)` induced by `g`.

    The inverse is the literal preimage `r : Y ⟶ X` of `id_Y` under `(· ≫ g)`
    (so `r ≫ g = id_Y`, no choice).  The other unit equation `g ≫ r = id_X`
    follows from injectivity at `T = X`:
      `(g ≫ r) ≫ g = g ≫ (r ≫ g) = g = id_X ≫ g`. -/
theorem iso_of_natural_hom_bijection {𝒟 : Type u} [Cat.{v} 𝒟] {X Y : 𝒟}
    (g : X ⟶ Y)
    (hsurj : ∀ {T : 𝒟} (k : T ⟶ Y), ∃ h : T ⟶ X, h ≫ g = k)
    (hinj : ∀ {T : 𝒟} {h₁ h₂ : T ⟶ X}, h₁ ≫ g = h₂ ≫ g → h₁ = h₂) :
    IsIso g := by
  -- Section r : Y ⟶ X with r ≫ g = id_Y, from surjectivity of (· ≫ g) at T = Y.
  obtain ⟨r, hr⟩ := hsurj (Cat.id Y)
  -- g ≫ r is the inverse on the other side too, by injectivity at T = X.
  refine ⟨r, ?_, hr⟩
  apply hinj
  show (g ≫ r) ≫ g = Cat.id X ≫ g
  rw [Cat.assoc, hr, Cat.comp_id, Cat.id_comp]

/-- DUAL YONEDA COROLLARY (object iso from a natural iso of *co*representables).
    If PREcomposition `(g ≫ ·) : (Y ⟶ T) → (X ⟶ T)` is a bijection for EVERY test
    object `T`, then `g` is an isomorphism.  Dual to `iso_of_natural_hom_bijection`. -/
theorem iso_of_natural_hom_bijection_op {𝒟 : Type u} [Cat.{v} 𝒟] {X Y : 𝒟}
    (g : X ⟶ Y)
    (hsurj : ∀ {T : 𝒟} (k : X ⟶ T), ∃ h : Y ⟶ T, g ≫ h = k)
    (hinj : ∀ {T : 𝒟} {h₁ h₂ : Y ⟶ T}, g ≫ h₁ = g ≫ h₂ → h₁ = h₂) :
    IsIso g := by
  obtain ⟨r, hr⟩ := hsurj (Cat.id X)
  refine ⟨r, hr, ?_⟩
  apply hinj
  show g ≫ (r ≫ g) = g ≫ Cat.id Y
  rw [← Cat.assoc, hr, Cat.id_comp, Cat.comp_id]

/-- A full subcategory (via inclusion I : 𝒜' → 𝒜) is an EXPONENTIAL IDEAL of 𝒜
    if for all A ∈ |𝒜| and B ∈ |𝒜'|, the exponential B^A lies in 𝒜' (§1.857). -/
def ExponentialIdeal (I : Functor 𝒜' 𝒜) : Prop :=
  Full I ∧
  ∀ (A : 𝒜) (B : 𝒜'), ∃ (E : 𝒜'), Isomorphic (I.obj E) (exp A (I.obj B))

/-- A subcategory (via inclusion I : 𝒜' → 𝒜) is REPLETE if it is closed under
    isomorphism type: if B ∈ |𝒜'| and I.obj B ≅ X in 𝒜 then X ∈ |𝒜'| (§1.857). -/
def RepleteSubcategory (I : Functor 𝒜' 𝒜) : Prop :=
  ∀ (B : 𝒜') (X : 𝒜), Isomorphic (I.obj B) X → ∃ (B' : 𝒜'), I.obj B' = X

/-- §1.857, Part 1: A full coreflective subcategory of an exponential category
    that is closed under binary products is itself exponential.
    (The coreflection G : 𝒜 → 𝒜' witnesses exponentials via G(B^A).) -/
theorem coreflective_closed_products_is_exponential
    (I : Functor 𝒜' 𝒜)
    [HasBinaryProducts 𝒜']
    (hFull : Full I)
    (hEmb : Embedding I)
    (hCorfl : CoreflectiveSubcategory I)
    -- `hProd` is Freyd's actual hypothesis "I preserves binary products": the CANONICAL
    -- comparison map `⟨I fst, I snd⟩ : I(B₁×B₂) → I.obj B₁ × I.obj B₂` is an isomorphism.
    -- Stating it canonically (compatible with the projections) is what makes the comparison
    -- iso NATURAL in each variable — the strong product-preservation the curry equations need.
    (hProd : ∀ (B₁ B₂ : 𝒜'),
      IsIso (pair (I.map (fst : prod B₁ B₂ ⟶ B₁)) (I.map (snd : prod B₁ B₂ ⟶ B₂)))) :
    Nonempty (HasExponentials 𝒜') := by
  -- adj0 : I ⊣ G where G = hCorfl.coreflection.
  let adj0 := hCorfl.adj.adj
  let G := hCorfl.coreflection
  -- The CANONICAL comparison map ip B₁ B₂ : I(B₁×B₂) → I.obj B₁ × I.obj B₂, and its inverse ip'.
  let ip  := fun (B₁ B₂ : 𝒜') =>
    pair (I.map (fst : prod B₁ B₂ ⟶ B₁)) (I.map (snd : prod B₁ B₂ ⟶ B₂))
  let ip' := fun (B₁ B₂ : 𝒜') => Classical.choose (hProd B₁ B₂)
  have ip_inv := fun (B₁ B₂ : 𝒜') => Classical.choose_spec (hProd B₁ B₂)
  -- ip ≫ ip' = id (inverse on the left) and ip' ≫ ip = id (inverse on the right).
  have ip_ip' : ∀ B₁ B₂, ip B₁ B₂ ≫ ip' B₁ B₂ = Cat.id _ := fun B₁ B₂ => (ip_inv B₁ B₂).1
  have ip'_ip : ∀ B₁ B₂, ip' B₁ B₂ ≫ ip B₁ B₂ = Cat.id _ := fun B₁ B₂ => (ip_inv B₁ B₂).2
  -- Projection identities for ip (definitional, from fst_pair / snd_pair).
  have ip_fst : ∀ B₁ B₂, ip B₁ B₂ ≫ fst = I.map (fst : prod B₁ B₂ ⟶ B₁) :=
    fun B₁ B₂ => fst_pair _ _
  have ip_snd : ∀ B₁ B₂, ip B₁ B₂ ≫ snd = I.map (snd : prod B₁ B₂ ⟶ B₂) :=
    fun B₁ B₂ => snd_pair _ _
  -- The counit ε_X : I(G X) → X (in 𝒜).
  let ε := fun (X : 𝒜) => counit adj0 X
  -- curry_map: given f : prod A X → B in 𝒜', produce X → G(exp(I.obj A)(I.obj B)) via:
  --   curry(ip'(A,X) ≫ I.map f) : I.obj X → exp(I.obj A)(I.obj B), then adj0.φ to land in 𝒜'.
  let curry' := fun {A B X : 𝒜'} (f : prod A X ⟶ B) =>
    adj0.φ (curry (ip' A X ≫ I.map f))
  -- eval_map: prod A (G(exp(I.obj A)(I.obj B))) → B in 𝒜'.  Built in 𝒜 then pulled back by Full I:
  --   I(prod A (GE)) --[ip A (GE)]→ I.obj A × I(GE) --[prodMap ε]→ I.obj A × E --[eval]→ I.obj B.
  let eval_A := fun (A B : 𝒜') =>
    ip A (G.obj (exp (I.obj A) (I.obj B))) ≫
    prodMap (I.obj A) (I.obj (G.obj (exp (I.obj A) (I.obj B)))) (exp (I.obj A) (I.obj B)) (ε (exp (I.obj A) (I.obj B))) ≫
    eval_exp (I.obj A) (I.obj B)
  let eval' := fun (A B : 𝒜') => Classical.choose (hFull (eval_A A B))
  have eval'_spec : ∀ A B, I.map (eval' A B) = eval_A A B :=
    fun A B => Classical.choose_spec (hFull (eval_A A B))
  -- NATURALITY of ip in the second variable: for u : X ⟶ Y in 𝒜',
  --   I.map(prodMap A X Y u) ≫ ip A Y = ip A X ≫ prodMap (I.obj A) (I.obj X) (I.obj Y) (I.map u).
  -- (Both legs land in I.obj A × I.obj Y; check after ≫ fst and ≫ snd via the projection laws.)
  have ip_nat : ∀ (A : 𝒜') {X Y : 𝒜'} (u : X ⟶ Y),
      I.map (prodMap A X Y u) ≫ ip A Y =
        ip A X ≫ prodMap (I.obj A) (I.obj X) (I.obj Y) (I.map u) := by
    intro A X Y u
    -- Both maps land in `I.obj A × I.obj Y`; equate by their `≫ fst` and `≫ snd` legs.
    have hfst : (I.map (prodMap A X Y u) ≫ ip A Y) ≫ fst =
                (ip A X ≫ prodMap (I.obj A) (I.obj X) (I.obj Y) (I.map u)) ≫ fst := by
      rw [Cat.assoc, ip_fst, ← I.map_comp, prodMap_fst,
          Cat.assoc, prodMap_fst, ip_fst]
    have hsnd : (I.map (prodMap A X Y u) ≫ ip A Y) ≫ snd =
                (ip A X ≫ prodMap (I.obj A) (I.obj X) (I.obj Y) (I.map u)) ≫ snd := by
      rw [Cat.assoc, ip_snd, ← I.map_comp, prodMap_snd, I.map_comp,
          Cat.assoc, prodMap_snd, ← Cat.assoc, ip_snd]
    rw [pair_uniq _ _ (I.map (prodMap A X Y u) ≫ ip A Y) rfl rfl,
        pair_uniq _ _ (ip A X ≫ prodMap (I.obj A) (I.obj X) (I.obj Y) (I.map u)) rfl rfl,
        hfst, hsnd]
  -- KEY: ε absorbs the φ-transpose.  I.map(curry' f) ≫ ε E = curry (ip' A X ≫ I.map f).
  --   I.map(adj0.φ h) ≫ ε E = adj0.ψ (adj0.φ h) = h   (ψ_eq + ψφ).
  have curry'_eps : ∀ {A B X : 𝒜'} (f : prod A X ⟶ B),
      I.map (curry' f) ≫ ε (exp (I.obj A) (I.obj B)) = curry (ip' A X ≫ I.map f) := by
    intro A B X f
    show I.map (adj0.φ _) ≫ counit adj0 _ = _
    rw [← ψ_eq adj0 (adj0.φ (curry (ip' A X ≫ I.map f))), adj0.ψφ]
  -- CORE COMPUTATION (shared by curry_eval and curry_unique).  For ANY g : X ⟶ GE,
  --   I.map (prodMap A X GE g) ≫ eval_A A B
  --     = ip A X ≫ prodMap (I.obj A) (I.obj X) E (I.map g ≫ ε E) ≫ eval_exp (I.obj A) (I.obj B).
  have core : ∀ {A B X : 𝒜'} (g : X ⟶ G.obj (exp (I.obj A) (I.obj B))),
      I.map (prodMap A X (G.obj (exp (I.obj A) (I.obj B))) g) ≫ eval_A A B =
        ip A X ≫ prodMap (I.obj A) (I.obj X) (exp (I.obj A) (I.obj B)) (I.map g ≫ ε (exp (I.obj A) (I.obj B))) ≫
          eval_exp (I.obj A) (I.obj B) := by
    intro A B X g
    -- eval_A = ip A (GE) ≫ prodMap ε ≫ eval.  Pull I.map(prodMap g) through ip A (GE) by ip_nat,
    -- then fuse the two prodMaps with prodMap_comp.
    show I.map (prodMap A X _ g) ≫ ip A _ ≫ _ ≫ eval_exp (I.obj A) (I.obj B) = _
    rw [← Cat.assoc, ip_nat A g, Cat.assoc, ← Cat.assoc (prodMap _ _ _ (I.map g)),
        ← prodMap_comp]
  refine ⟨?_⟩
  refine
    { toHasBinaryProducts := inferInstance
      exp_obj := fun A B => G.obj (exp (I.obj A) (I.obj B))
      eval_map := fun {A B} => eval' A B
      curry_map := fun {A B X} f => curry' f
      curry_eval := fun {A B X} f => by
        -- Cancel I.obj (Embedding), rewrite I.map(eval') = eval_A, run the core computation,
        -- absorb ε via curry'_eps, fire curry_eval_eq, then collapse ip ≫ ip' = id.
        apply hEmb
        rw [I.map_comp, eval'_spec, core (curry' f), curry'_eps f,
            curry_eval_eq, ← Cat.assoc, ip_ip', Cat.id_comp]
      curry_unique := fun {A B X f g} h => by
        -- Suffices adj0.ψ g = curry (ip' A X ≫ I.map f); then apply adj0.φ (φ bijective).
        -- adj0.ψ g = I.map g ≫ ε E (ψ_eq).  Establish it via curry_unique_eq from the core eqn.
        show g = adj0.φ (curry (ip' A X ≫ I.map f))
        have hgψ : g = adj0.φ (adj0.ψ g) := (adj0.φψ g).symm
        rw [hgψ]; congr 1
        rw [ψ_eq adj0 g]
        apply curry_unique_eq
        -- From h: I.map(prodMap A X _ g) ≫ eval_A = I.map f.  Run core, cancel ip via ip'.
        have hI : I.map (prodMap A X (G.obj (exp (I.obj A) (I.obj B))) g) ≫ eval_A A B = I.map f := by
          rw [← eval'_spec, ← I.map_comp, h]
        rw [core g] at hI
        -- ip A X ≫ (prodMap … ≫ eval) = I.map f  ⟹  prodMap … ≫ eval = ip' A X ≫ I.map f.
        rw [← hI, ← Cat.assoc, ip'_ip, Cat.id_comp] }

/-- For a full-and-faithful reflective inclusion `I` (`refl ⊣ I`), the counit
    `ε_C : refl (I.obj C) → C` is an isomorphism for every `C : 𝒜'`.  This is the
    constructive heart of "the reflection is idempotent on the subcategory":
    Freyd's standing assumption that the subcategory is FULL (here `Full I` +
    `Embedding I`) forces the counit to be invertible.

    Proof.  `triangle_two` gives `η_{I.obj C} ≫ I(ε_C) = id_{I.obj C}`.  By `Full I`
    pick `e' : C ⟶ refl (I.obj C)` with `I(e') = η_{I.obj C}`.  Then `e'` is a
    two-sided inverse of `ε_C`:  `e' ≫ ε_C = id_C` follows by faithfulness from
    `triangle_two`; `ε_C ≫ e' = id` follows from `φ`-injectivity, computing
    `φ(ε_C ≫ e') = η_{I.obj C} ≫ I(ε_C) ≫ η_{I.obj C} = η_{I.obj C} = φ(id)` via `φ_eq`. -/
theorem reflective_counit_iso
    (I : Functor 𝒜' 𝒜)
    (hFull : Full I) (hEmb : Embedding I)
    (hRefl : ReflectiveSubcategory I) (C : 𝒜') :
    IsIso (counit hRefl.adj.adj C) := by
  let adjR := hRefl.adj.adj
  -- e' : C ⟶ refl (I.obj C) with I(e') = η_{I.obj C}.
  obtain ⟨e', he'⟩ := hFull (unit adjR (I.obj C))
  refine ⟨e', ?_, ?_⟩
  · -- ε_C ≫ e' = id_{refl (I.obj C)}.  Apply the (injective) bijection `φ`:
    --   φ(ε_C ≫ e') = η_{I.obj C} ≫ I(ε_C ≫ e') = η_{I.obj C} ≫ I(ε_C) ≫ I(e')
    --              = η_{I.obj C} ≫ I(ε_C) ≫ η_{I.obj C} = id ≫ η_{I.obj C} = η_{I.obj C} = φ(id).
    apply φ_inj adjR
    rw [φ_eq adjR (counit adjR C ≫ e'), I.map_comp, he',
        ← Cat.assoc, triangle_two adjR C, Cat.id_comp]
    -- RHS: φ(id) = η_{I.obj C} = unit.
    show unit adjR (I.obj C) = adjR.φ (Cat.id (hRefl.reflection.obj (I.obj C)))
    rfl
  · -- e' ≫ ε_C = id_C, by faithfulness from triangle_two.
    apply hEmb
    rw [I.map_comp, he', I.map_id]
    exact triangle_two adjR C

/-- A RIGHT ADJOINT preserves binary products.  Given `adj : L ⊣ I` and `B₁ B₂ : 𝒜'`,
    the canonical comparison `⟨I(fst), I(snd)⟩ : I(B₁×B₂) → I.obj B₁ × I.obj B₂` is an iso. -/
theorem right_adjoint_preserves_prod
    {L : Functor 𝒜 𝒜'} {I : Functor 𝒜' 𝒜} (adj : L ⊣ I)
    [HasBinaryProducts 𝒜'] (B₁ B₂ : 𝒜') :
    IsIso (pair (I.map (fst : prod B₁ B₂ ⟶ B₁))
                (I.map (snd : prod B₁ B₂ ⟶ B₂))) := by
  let ip := pair (I.map (fst : prod B₁ B₂ ⟶ B₁))
                 (I.map (snd : prod B₁ B₂ ⟶ B₂))
  show IsIso ip
  have ip_fst : ip ≫ fst = I.map (fst : prod B₁ B₂ ⟶ B₁) := fst_pair _ _
  have ip_snd : ip ≫ snd = I.map (snd : prod B₁ B₂ ⟶ B₂) := snd_pair _ _
  let inv := adj.φ (pair (adj.ψ (fst : prod (I.obj B₁) (I.obj B₂) ⟶ I.obj B₁))
                         (adj.ψ (snd : prod (I.obj B₁) (I.obj B₂) ⟶ I.obj B₂)))
  have inv_ip : inv ≫ ip = Cat.id _ := by
    have hf : (inv ≫ ip) ≫ fst = fst := by
      rw [Cat.assoc, ip_fst]
      show adj.φ _ ≫ I.map (fst : prod B₁ B₂ ⟶ B₁) = _
      rw [← adj.φ_nat_right, fst_pair, adj.φψ]
    have hs : (inv ≫ ip) ≫ snd = snd := by
      rw [Cat.assoc, ip_snd]
      show adj.φ _ ≫ I.map (snd : prod B₁ B₂ ⟶ B₂) = _
      rw [← adj.φ_nat_right, snd_pair, adj.φψ]
    exact (pair_uniq _ _ _ hf hs).trans pair_fst_snd
  apply iso_of_natural_hom_bijection ip
  · intro T k
    exact ⟨k ≫ inv, by rw [Cat.assoc, inv_ip, Cat.comp_id]⟩
  · intro T h₁ h₂ hh
    have key : ∀ h : T ⟶ I.obj (prod B₁ B₂), h = adj.φ (adj.ψ h) := fun h => (adj.φψ h).symm
    have legfst : adj.ψ h₁ ≫ fst = adj.ψ h₂ ≫ fst := by
      apply φ_inj adj
      rw [adj.φ_nat_right, adj.φ_nat_right, adj.φψ, adj.φψ, ← ip_fst, ← Cat.assoc, ← Cat.assoc, hh]
    have legsnd : adj.ψ h₁ ≫ snd = adj.ψ h₂ ≫ snd := by
      apply φ_inj adj
      rw [adj.φ_nat_right, adj.φ_nat_right, adj.φψ, adj.φψ, ← ip_snd, ← Cat.assoc, ← Cat.assoc, hh]
    rw [key h₁, key h₂]
    congr 1
    rw [pair_uniq _ _ (adj.ψ h₁) rfl rfl, pair_uniq _ _ (adj.ψ h₂) rfl rfl, legfst, legsnd]

/-- For a full-faithful right adjoint `I` (`adj : L ⊣ I`), precomposition by the
    unit `η_A : A ⟶ I(L.obj A)` is a bijection `(I(L.obj A) ⟶ I.obj Z) ≅ (A ⟶ I.obj Z)` for `Z : 𝒜'`. -/
theorem unit_precomp_bij
    {L : Functor 𝒜 𝒜'} {I : Functor 𝒜' 𝒜} (adj : L ⊣ I)
    (hFull : Full I) (A : 𝒜) (Z : 𝒜') :
    (∀ p : A ⟶ I.obj Z, ∃ f : I.obj (L.obj A) ⟶ I.obj Z, unit adj A ≫ f = p) ∧
    (∀ {f₁ f₂ : I.obj (L.obj A) ⟶ I.obj Z}, unit adj A ≫ f₁ = unit adj A ≫ f₂ → f₁ = f₂) := by
  constructor
  · intro p
    refine ⟨I.map (adj.ψ p), ?_⟩
    rw [← φ_eq adj (adj.ψ p), adj.φψ]
  · intro f₁ f₂ hf
    obtain ⟨f₁', hf₁⟩ := hFull f₁
    obtain ⟨f₂', hf₂⟩ := hFull f₂
    rw [← hf₁, ← hf₂] at hf ⊢
    rw [← φ_eq adj f₁', ← φ_eq adj f₂'] at hf
    rw [φ_inj adj hf]


/-- The unit `η_A : A ⟶ I(L.obj A)` of a full-faithful reflection is "left-orthogonal
    to the exponential ideal" even after producting with a fixed object `W`:
    precomposition by `(η_A × 1_W) : A × W ⟶ I(L.obj A) × W` is a bijection on maps to
    `I.obj Z`.  This is the engine of the (⇒) direction (§1.857, Part 2).

    Proof: swap so `W` is the first product factor, curry over `W` (landing in
    `exp W (I.obj Z)`), use the exponential ideal `exp W (I.obj Z) ≅ I.obj Z''` to bring the
    codomain into the subcategory, then apply the *single-object* unit bijection
    `unit_precomp_bij` at `A`. -/
theorem unit_left_bij
    {L : Functor 𝒜 𝒜'} {I : Functor 𝒜' 𝒜} (adj : L ⊣ I)
    (hFull : Full I)
    (hExpId : ∀ (A : 𝒜) (B : 𝒜'), ∃ (E : 𝒜'), Isomorphic (I.obj E) (exp A (I.obj B)))
    (A W : 𝒜) (Z : 𝒜') :
    (∀ k : prod A W ⟶ I.obj Z,
        ∃ g : prod (I.obj (L.obj A)) W ⟶ I.obj Z, pair (fst ≫ unit adj A) snd ≫ g = k) ∧
    (∀ {g₁ g₂ : prod (I.obj (L.obj A)) W ⟶ I.obj Z},
        pair (fst ≫ unit adj A) snd ≫ g₁ = pair (fst ≫ unit adj A) snd ≫ g₂ → g₁ = g₂) := by
  obtain ⟨Z'', j, j', jl, jr⟩ := hExpId W Z
  obtain ⟨usurj, uinj⟩ := unit_precomp_bij adj hFull A Z''
  -- `pml` = the unit-on-left product map.
  let pml : prod A W ⟶ prod (I.obj (L.obj A)) W := pair (fst ≫ unit adj A) snd
  have hpml : pml = pair (fst ≫ unit adj A) snd := rfl
  -- pml ≫ prodSwap = pair snd (fst ≫ η_A).
  have pml_swap : pml ≫ prodSwap (I.obj (L.obj A)) W = pair snd (fst ≫ unit adj A) := by
    rw [hpml, pair_uniq _ _ (pair (fst ≫ unit adj A) snd ≫ prodSwap (I.obj (L.obj A)) W) rfl rfl]
    congr 1
    · rw [Cat.assoc,
        show prodSwap (I.obj (L.obj A)) W ≫ fst = snd (A := I.obj (L.obj A)) (B := W) from fst_pair _ _, snd_pair]
    · rw [Cat.assoc,
        show prodSwap (I.obj (L.obj A)) W ≫ snd = fst (A := I.obj (L.obj A)) (B := W) from snd_pair _ _, fst_pair]
  constructor
  · -- SURJECTIVE.
    intro k
    let pW := curry (prodSwap W A ≫ k)
    obtain ⟨f, hf⟩ := usurj (pW ≫ j')
    refine ⟨prodSwap (I.obj (L.obj A)) W ≫ prodMap W (I.obj (L.obj A)) (exp W (I.obj Z)) (f ≫ j) ≫ eval_exp W (I.obj Z), ?_⟩
    -- Rewrite pml ≫ (swap ≫ prodMap ≫ eval).
    rw [← Cat.assoc, ← Cat.assoc, pml_swap]
    -- pair snd (fst≫η) ≫ prodMap W (ILA)(exp) (f≫j) = pair snd (fst≫η≫(f≫j)).
    have step1 : pair snd (fst ≫ unit adj A) ≫ prodMap W (I.obj (L.obj A)) (exp W (I.obj Z)) (f ≫ j) =
        pair snd (fst ≫ unit adj A ≫ (f ≫ j)) := by
      rw [pair_uniq _ _
        (pair snd (fst ≫ unit adj A) ≫ prodMap W (I.obj (L.obj A)) (exp W (I.obj Z)) (f ≫ j)) rfl rfl]
      congr 1
      · rw [Cat.assoc, prodMap_fst, fst_pair]
      · rw [Cat.assoc, prodMap_snd, ← Cat.assoc, snd_pair, Cat.assoc]
    rw [step1]
    -- η ≫ (f ≫ j) = (η ≫ f) ≫ j = (pW ≫ j') ≫ j = pW.
    rw [show unit adj A ≫ (f ≫ j) = pW by rw [← Cat.assoc, hf, Cat.assoc, jr, Cat.comp_id]]
    -- pair snd (fst≫pW) ≫ eval = prodSwap A W ≫ (prodMap W A (exp) pW ≫ eval) = prodSwap ≫ prodSwap ≫ k.
    have step2 : pair snd (fst ≫ pW) =
        prodSwap A W ≫ prodMap W A (exp W (I.obj Z)) pW := by
      rw [pair_uniq _ _ (prodSwap A W ≫ prodMap W A (exp W (I.obj Z)) pW) rfl rfl]
      congr 1
      · rw [Cat.assoc, prodMap_fst,
          show prodSwap A W ≫ fst = snd (A := A) (B := W) from fst_pair _ _]
      · rw [Cat.assoc, prodMap_snd, ← Cat.assoc,
          show prodSwap A W ≫ snd = fst (A := A) (B := W) from snd_pair _ _]
    rw [step2, Cat.assoc]
    show prodSwap A W ≫ prodMap W A (exp W (I.obj Z)) pW ≫ eval_exp W (I.obj Z) = k
    rw [curry_eval_eq, ← Cat.assoc, prodSwap_prodSwap, Cat.id_comp]
  · -- INJECTIVE.
    intro g₁ g₂ hg
    -- G g := curry (prodSwap W (ILA) ≫ g) : I.obj L.obj A ⟶ exp W IZ ; injective in g.
    let G := fun (g : prod (I.obj (L.obj A)) W ⟶ I.obj Z) => curry (prodSwap W (I.obj (L.obj A)) ≫ g)
    have G_inj : ∀ {g₁ g₂ : prod (I.obj (L.obj A)) W ⟶ I.obj Z}, G g₁ = G g₂ → g₁ = g₂ := by
      intro g₁ g₂ h
      have := curry_inj h
      have h2 : prodSwap (I.obj (L.obj A)) W ≫ prodSwap W (I.obj (L.obj A)) ≫ g₁ =
                prodSwap (I.obj (L.obj A)) W ≫ prodSwap W (I.obj (L.obj A)) ≫ g₂ := by rw [this]
      rwa [← Cat.assoc, prodSwap_prodSwap, Cat.id_comp, ← Cat.assoc, prodSwap_prodSwap,
           Cat.id_comp] at h2
    -- KEY: curry (prodSwap W A ≫ (pml ≫ g)) = η_A ≫ G g.
    have key : ∀ g : prod (I.obj (L.obj A)) W ⟶ I.obj Z,
        curry (prodSwap W A ≫ (pml ≫ g)) = unit adj A ≫ G g := by
      intro g
      show curry (prodSwap W A ≫ pml ≫ g) = unit adj A ≫ curry (prodSwap W (I.obj (L.obj A)) ≫ g)
      rw [curry_precomp]
      congr 1
      have hswap : prodSwap W A ≫ pml =
          prodMap W A (I.obj (L.obj A)) (unit adj A) ≫ prodSwap W (I.obj (L.obj A)) := by
        rw [pair_uniq _ _ (prodSwap W A ≫ pml) rfl rfl,
            pair_uniq _ _ (prodMap W A (I.obj (L.obj A)) (unit adj A) ≫ prodSwap W (I.obj (L.obj A))) rfl rfl]
        congr 1
        · -- LHS ≫ fst = snd ≫ η = RHS ≫ fst
          rw [hpml, Cat.assoc, fst_pair, ← Cat.assoc,
              show prodSwap W A ≫ fst = snd (A := W) (B := A) from fst_pair _ _,
              Cat.assoc, show prodSwap W (I.obj (L.obj A)) ≫ fst = snd (A := W) (B := I.obj (L.obj A))
                from fst_pair _ _, prodMap_snd]
        · -- LHS ≫ snd = fst = RHS ≫ snd
          rw [hpml, Cat.assoc, snd_pair,
              show prodSwap W A ≫ snd = fst (A := W) (B := A) from snd_pair _ _,
              Cat.assoc, show prodSwap W (I.obj (L.obj A)) ≫ snd = fst (A := W) (B := I.obj (L.obj A))
                from snd_pair _ _, prodMap_fst]
      rw [← Cat.assoc, hswap, Cat.assoc]
    apply G_inj
    -- η_A ≫ G g₁ = η_A ≫ G g₂ via key + hg ; then strip η via j' and uinj.
    have hηG : unit adj A ≫ G g₁ = unit adj A ≫ G g₂ := by
      rw [← key, ← key, hg]
    have hj : unit adj A ≫ (G g₁ ≫ j') = unit adj A ≫ (G g₂ ≫ j') := by
      rw [← Cat.assoc, ← Cat.assoc, hηG]
    have := uinj hj
    -- G g₁ ≫ j' = G g₂ ≫ j' ⟹ G g₁ = G g₂ by ≫ j.
    calc G g₁ = (G g₁ ≫ j') ≫ j := by rw [Cat.assoc, jr, Cat.comp_id]
      _ = (G g₂ ≫ j') ≫ j := by rw [this]
      _ = G g₂ := by rw [Cat.assoc, jr, Cat.comp_id]

/-- Dual of `unit_left_bij`: precomposition by `(1_V × η_A)` is a bijection on maps
    to `I.obj Z`.  Obtained from `unit_left_bij` by conjugating with `prodSwap`. -/
theorem unit_right_bij
    {L : Functor 𝒜 𝒜'} {I : Functor 𝒜' 𝒜} (adj : L ⊣ I)
    (hFull : Full I)
    (hExpId : ∀ (A : 𝒜) (B : 𝒜'), ∃ (E : 𝒜'), Isomorphic (I.obj E) (exp A (I.obj B)))
    (V A : 𝒜) (Z : 𝒜') :
    (∀ k : prod V A ⟶ I.obj Z,
        ∃ g : prod V (I.obj (L.obj A)) ⟶ I.obj Z, pair fst (snd ≫ unit adj A) ≫ g = k) ∧
    (∀ {g₁ g₂ : prod V (I.obj (L.obj A)) ⟶ I.obj Z},
        pair fst (snd ≫ unit adj A) ≫ g₁ = pair fst (snd ≫ unit adj A) ≫ g₂ → g₁ = g₂) := by
  obtain ⟨lsurj, linj⟩ := unit_left_bij adj hFull hExpId A V Z
  have swapcancel : ∀ {X Y : 𝒜} {W : 𝒜} (t : prod Y X ⟶ W),
      prodSwap Y X ≫ prodSwap X Y ≫ t = t := by
    intro X Y W t; rw [← Cat.assoc, prodSwap_prodSwap, Cat.id_comp]
  -- prm = prodSwap V A ≫ pml ≫ prodSwap (ILA) V, where pml = pair (fst≫η) snd.
  have hconj : pair fst (snd ≫ unit adj A) =
      prodSwap V A ≫ pair (fst ≫ unit adj A) snd ≫ prodSwap (I.obj (L.obj A)) V := by
    rw [pair_uniq _ _
      (prodSwap V A ≫ pair (fst ≫ unit adj A) snd ≫ prodSwap (I.obj (L.obj A)) V) rfl rfl]
    congr 1
    · rw [Cat.assoc, Cat.assoc,
        show prodSwap (I.obj (L.obj A)) V ≫ fst = snd (A := I.obj (L.obj A)) (B := V) from fst_pair _ _,
        snd_pair, show prodSwap V A ≫ snd = fst (A := V) (B := A) from snd_pair _ _]
    · rw [Cat.assoc, Cat.assoc,
        show prodSwap (I.obj (L.obj A)) V ≫ snd = fst (A := I.obj (L.obj A)) (B := V) from snd_pair _ _,
        fst_pair, ← Cat.assoc,
        show prodSwap V A ≫ fst = snd (A := V) (B := A) from fst_pair _ _]
  constructor
  · intro k
    obtain ⟨g', hg'⟩ := lsurj (prodSwap A V ≫ k)
    refine ⟨prodSwap V (I.obj (L.obj A)) ≫ g', ?_⟩
    rw [hconj]
    simp only [Cat.assoc]
    rw [swapcancel g', hg', swapcancel k]
  · intro g₁ g₂ hg
    rw [hconj] at hg
    have hg2 : pair (fst ≫ unit adj A) snd ≫ (prodSwap (I.obj (L.obj A)) V ≫ g₁) =
               pair (fst ≫ unit adj A) snd ≫ (prodSwap (I.obj (L.obj A)) V ≫ g₂) := by
      have e := congrArg (fun t => prodSwap A V ≫ t) hg
      simp only [Cat.assoc] at e
      rwa [swapcancel, swapcancel] at e
    have hcore := linj hg2
    have e2 := congrArg (fun t => prodSwap V (I.obj (L.obj A)) ≫ t) hcore
    simp only [] at e2
    rwa [swapcancel, swapcancel] at e2

/-- The kernel of the (⇒) direction: precomposition by the two-unit comparison
    `w = (η_{A₁} × η_{A₂}) : A₁ × A₂ ⟶ I(L.obj A₁) × I(L.obj A₂)` is a bijection on maps to
    `I.obj Z`.  Factor `w = (η₁ × 1) ≫ (1 × η₂)` and apply `unit_left_bij`, `unit_right_bij`. -/
theorem wbij_kernel
    {L : Functor 𝒜 𝒜'} {I : Functor 𝒜' 𝒜} (adj : L ⊣ I)
    (hFull : Full I)
    (hExpId : ∀ (A : 𝒜) (B : 𝒜'), ∃ (E : 𝒜'), Isomorphic (I.obj E) (exp A (I.obj B)))
    (A₁ A₂ : 𝒜) (Z : 𝒜') :
    (∀ k : prod A₁ A₂ ⟶ I.obj Z,
        ∃ g : prod (I.obj (L.obj A₁)) (I.obj (L.obj A₂)) ⟶ I.obj Z,
          pair (fst ≫ unit adj A₁) (snd ≫ unit adj A₂) ≫ g = k) ∧
    (∀ {g₁ g₂ : prod (I.obj (L.obj A₁)) (I.obj (L.obj A₂)) ⟶ I.obj Z},
        pair (fst ≫ unit adj A₁) (snd ≫ unit adj A₂) ≫ g₁ =
          pair (fst ≫ unit adj A₁) (snd ≫ unit adj A₂) ≫ g₂ → g₁ = g₂) := by
  obtain ⟨lsurj, linj⟩ := unit_left_bij adj hFull hExpId A₁ A₂ Z
  obtain ⟨rsurj, rinj⟩ := unit_right_bij adj hFull hExpId (I.obj (L.obj A₁)) A₂ Z
  -- w = pml₁ ≫ prm₂ : pml₁ = pair (fst≫η₁) snd, prm₂ = pair fst (snd≫η₂).
  have hw : pair (fst ≫ unit adj A₁) (snd ≫ unit adj A₂) =
      pair (fst ≫ unit adj A₁) snd ≫ pair fst (snd ≫ unit adj A₂) := by
    rw [pair_uniq _ _ (pair (fst ≫ unit adj A₁) snd ≫ pair fst (snd ≫ unit adj A₂)) rfl rfl]
    congr 1
    · rw [Cat.assoc, fst_pair, fst_pair]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair]
  constructor
  · intro k
    obtain ⟨g₁, hg₁⟩ := lsurj k
    obtain ⟨g, hg⟩ := rsurj g₁
    exact ⟨g, by rw [hw, Cat.assoc, hg, hg₁]⟩
  · intro ga gb hgab
    rw [hw, Cat.assoc, Cat.assoc] at hgab
    exact rinj (linj hgab)

/-- §1.857, Part 2: A full replete reflective subcategory of an exponential
    category is an exponential ideal iff its reflections preserve products.
    "Reflections preserve products" means: for A₁, A₂ ∈ |𝒜|, the image
    I(Ā₁ × Ā₂) ≅ I(Ā₁×A₂) in 𝒜, i.e. I preserves the product of the
    reflections; equivalently, Ā₁×A₂ ≅ Ā₁×Ā₂ in 𝒜. -/
theorem reflective_exponential_ideal_iff_refl_preserve_products
    [HasBinaryProducts 𝒜']
    (I : Functor 𝒜' 𝒜)
    (hFull : Full I) (hEmb : Embedding I)

    (hRefl : ReflectiveSubcategory I) :
    ExponentialIdeal I ↔
    ∀ (A₁ A₂ : 𝒜),
      @IsIso 𝒜' _ (hRefl.reflection.obj (prod A₁ A₂))
        (prod (hRefl.reflection.obj A₁) (hRefl.reflection.obj A₂))
        (pair (hRefl.reflection.map (fst : prod A₁ A₂ ⟶ A₁))
              (hRefl.reflection.map (snd : prod A₁ A₂ ⟶ A₂))) := by
  let L := hRefl.reflection
  let adjR := hRefl.adj.adj
  -- The canonical comparison map `c A₁ A₂ : L(A₁×A₂) ⟶ L.obj A₁ × L.obj A₂` (in 𝒜'),
  -- ALWAYS available from the universal property of the product in 𝒜' applied to
  -- `L fst`, `L snd`.  "L preserves products" is precisely "`c` is an isomorphism".
  let c := fun (A₁ A₂ : 𝒜) =>
    pair (L.map (fst : prod A₁ A₂ ⟶ A₁))
         (L.map (snd : prod A₁ A₂ ⟶ A₂))
  show ExponentialIdeal I ↔ ∀ (A₁ A₂ : 𝒜), IsIso (c A₁ A₂)
  constructor
  · -- (⇒) Exponential ideal  ⟹  L preserves products.
    --
    -- The genuine content: for every test object `Z : 𝒜'` the comparison map induces a bijection
    --   Hom(L.obj A₁ × L.obj A₂, Z) ≅ Hom(A₁, (I.obj Z)^{A₂})  [via adjunction + product + currying]
    --   Hom(L(A₁×A₂), Z)   ≅ Hom(A₁×A₂, I.obj Z) ≅ Hom(A₁, (I.obj Z)^{A₂})  [exp ideal puts (I.obj Z)^{A₂} in 𝒜']
    -- agreeing under `c`, so `c` is a natural iso of representables, hence an iso of objects
    -- via the YONEDA corollary `iso_of_natural_hom_bijection`.
    intro hIdeal A₁ A₂
    obtain ⟨hFull', hExpId⟩ := hIdeal
    obtain ⟨ip_inv, ip_l, ip_r⟩ := right_adjoint_preserves_prod adjR (L.obj A₁) (L.obj A₂)
    let ip := pair (I.map (fst : prod (L.obj A₁) (L.obj A₂) ⟶ L.obj A₁))
                   (I.map (snd : prod (L.obj A₁) (L.obj A₂) ⟶ L.obj A₂))
    have ip_fst : ip ≫ fst = I.map (fst : prod (L.obj A₁) (L.obj A₂) ⟶ L.obj A₁) := fst_pair _ _
    have ip_snd : ip ≫ snd = I.map (snd : prod (L.obj A₁) (L.obj A₂) ⟶ L.obj A₂) := snd_pair _ _
    have ip_ii : ip ≫ ip_inv = Cat.id _ := ip_l
    have ip_ii' : ip_inv ≫ ip = Cat.id _ := ip_r
    let w := pair (fst ≫ unit adjR A₁) (snd ≫ unit adjR A₂)
    let d := unit adjR (prod A₁ A₂) ≫ I.map (c A₁ A₂)
    have c_fst : c A₁ A₂ ≫ fst = L.map (fst : prod A₁ A₂ ⟶ A₁) := fst_pair _ _
    have c_snd : c A₁ A₂ ≫ snd = L.map (snd : prod A₁ A₂ ⟶ A₂) := snd_pair _ _
    have d_ip : d ≫ ip = w := by
      have hf : (d ≫ ip) ≫ fst = w ≫ fst := by
        show ((unit adjR (prod A₁ A₂) ≫ I.map (c A₁ A₂)) ≫ ip) ≫ fst =
             pair _ _ ≫ fst
        rw [Cat.assoc, Cat.assoc, ip_fst, ← I.map_comp, c_fst,
            ← unit_naturality adjR (fst : prod A₁ A₂ ⟶ A₁), fst_pair]
      have hs : (d ≫ ip) ≫ snd = w ≫ snd := by
        show ((unit adjR (prod A₁ A₂) ≫ I.map (c A₁ A₂)) ≫ ip) ≫ snd =
             pair _ _ ≫ snd
        rw [Cat.assoc, Cat.assoc, ip_snd, ← I.map_comp, c_snd,
            ← unit_naturality adjR (snd : prod A₁ A₂ ⟶ A₂), snd_pair]
      rw [pair_uniq _ _ (d ≫ ip) rfl rfl, pair_uniq _ _ w rfl rfl, hf, hs]
    have phi_c : ∀ {Z : 𝒜'} (h : prod (L.obj A₁) (L.obj A₂) ⟶ Z),
        adjR.φ (c A₁ A₂ ≫ h) = d ≫ I.map h := by
      intro Z h
      rw [φ_eq adjR (c A₁ A₂ ≫ h), I.map_comp, ← Cat.assoc]
    -- THE KERNEL: `(w ≫ ·)` is a bijection onto `Hom(A₁×A₂, I.obj Z)`, for every `Z : 𝒜'`.
    have wbij : ∀ (Z : 𝒜'),
        (∀ k : prod A₁ A₂ ⟶ I.obj Z, ∃ g : prod (I.obj (L.obj A₁)) (I.obj (L.obj A₂)) ⟶ I.obj Z, w ≫ g = k) ∧
        (∀ {g₁ g₂ : prod (I.obj (L.obj A₁)) (I.obj (L.obj A₂)) ⟶ I.obj Z}, w ≫ g₁ = w ≫ g₂ → g₁ = g₂) :=
      wbij_kernel adjR hFull hExpId A₁ A₂
    apply iso_of_natural_hom_bijection_op (c A₁ A₂)
    · intro Z k
      obtain ⟨g, hg⟩ := (wbij Z).1 (adjR.φ k)
      obtain ⟨h, hh⟩ := hFull' (ip ≫ g)
      refine ⟨h, ?_⟩
      apply φ_inj adjR
      rw [phi_c h, hh, ← Cat.assoc, d_ip]
      exact hg
    · intro Z h₁ h₂ hh
      have e : d ≫ I.map h₁ = d ≫ I.map h₂ := by
        rw [← phi_c h₁, ← phi_c h₂, hh]
      have e2 : I.map h₁ = I.map h₂ := by
        have collapse : ∀ X : I.obj (prod (L.obj A₁) (L.obj A₂)) ⟶ I.obj Z,
            w ≫ (ip_inv ≫ X) = d ≫ X := by
          intro X
          rw [← d_ip, Cat.assoc, ← Cat.assoc ip, ip_ii, Cat.id_comp]
        have hw : w ≫ (ip_inv ≫ I.map h₁) =
                  w ≫ (ip_inv ≫ I.map h₂) := by
          rw [collapse, collapse]; exact e
        have hii := (wbij Z).2 hw
        calc I.map h₁
            = (ip ≫ ip_inv) ≫ I.map h₁ := by rw [ip_ii, Cat.id_comp]
          _ = ip ≫ ip_inv ≫ I.map h₁ := by rw [Cat.assoc]
          _ = ip ≫ ip_inv ≫ I.map h₂ := by rw [hii]
          _ = (ip ≫ ip_inv) ≫ I.map h₂ := by rw [Cat.assoc]
          _ = I.map h₂ := by rw [ip_ii, Cat.id_comp]
      exact hEmb h₁ h₂ e2
  · -- (⇐) L preserves products  ⟹  exponential ideal.
    intro hPres
    refine ⟨hFull, ?_⟩
    intro A B
    -- Want `E : 𝒜'` with `I.obj E ≅ exp A (I.obj B)`.  Standard proof: `exp A (I.obj B)` already lies in
    -- the subcategory because the unit `η_{exp A (I.obj B)} : exp A (I.obj B) → I(L(exp A (I.obj B)))` is an
    -- isomorphism; take `E := L(exp A (I.obj B))` and invert `η` (then repleteness/`hRepl`).
    -- Showing `η_{exp A (I.obj B)}` is iso needs the retraction
    --   `r : I(L(exp A (I.obj B))) → exp A (I.obj B)`
    -- obtained by transposing along `A × (-) ⊣ (-)^A` the map
    --   `A × I(L(exp A (I.obj B))) → I.obj B`
    -- built from `hPres` (so that `A × η` becomes invertible after reflection) and `eval`.
    -- This retraction's two unit equations reduce to the Yoneda corollary
    -- `iso_of_natural_hom_bijection` (proved above): `η_E` is iso once `(· ≫ η_E)` is a natural
    -- bijection of representables, which `hPres` (product-preservation) makes true via the
    -- `A × (-) ⊣ (-)^A` currying transpose.  Building that explicit bijection is the remaining
    -- algebra; the statement `IsIso (unit adjR (exp A (I.obj B)))` is true under `hPres`.
    refine ⟨L.obj (exp A (I.obj B)), ?_⟩
    -- `I.obj (L.obj (exp A (I.obj B))) ≅ exp A (I.obj B)` ⟸ `IsIso (unit adjR (exp A (I.obj B)))` (then `isomorphic_symm`).
    suffices hη : IsIso (unit adjR (exp A (I.obj B))) by
      exact isomorphic_symm ⟨unit adjR (exp A (I.obj B)), hη⟩
    -- NATURALITY of c in the second variable (dual to the sister theorem's `ip_nat`).
    have c_fst : ∀ A₁ A₂ : 𝒜, c A₁ A₂ ≫ fst = L.map (fst : prod A₁ A₂ ⟶ A₁) :=
      fun A₁ A₂ => fst_pair _ _
    have c_snd : ∀ A₁ A₂ : 𝒜, c A₁ A₂ ≫ snd = L.map (snd : prod A₁ A₂ ⟶ A₂) :=
      fun A₁ A₂ => snd_pair _ _
    have c_nat : ∀ (A : 𝒜) {X Y : 𝒜} (u : X ⟶ Y),
        L.map (prodMap A X Y u) ≫ c A Y =
          c A X ≫ prodMap (L.obj A) (L.obj X) (L.obj Y) (L.map u) := by
      intro A X Y u
      have hfst : (L.map (prodMap A X Y u) ≫ c A Y) ≫ fst =
                  (c A X ≫ prodMap (L.obj A) (L.obj X) (L.obj Y) (L.map u)) ≫ fst := by
        rw [Cat.assoc, c_fst, ← L.map_comp, prodMap_fst,
            Cat.assoc, prodMap_fst, c_fst]
      have hsnd : (L.map (prodMap A X Y u) ≫ c A Y) ≫ snd =
                  (c A X ≫ prodMap (L.obj A) (L.obj X) (L.obj Y) (L.map u)) ≫ snd := by
        rw [Cat.assoc, c_snd, ← L.map_comp, prodMap_snd, L.map_comp,
            Cat.assoc, prodMap_snd, ← Cat.assoc, c_snd]
      rw [pair_uniq _ _ (L.map (prodMap A X Y u) ≫ c A Y) rfl rfl,
          pair_uniq _ _ (c A X ≫ prodMap (L.obj A) (L.obj X) (L.obj Y) (L.map u)) rfl rfl,
          hfst, hsnd]
    let EX := exp A (I.obj B)
    show IsIso (unit adjR EX)
    obtain ⟨cAE_inv, cAE_l, cAE_r⟩ := hPres A EX
    obtain ⟨cILE_inv, cILE_l, cILE_r⟩ := hPres A (I.obj (L.obj EX))
    obtain ⟨εLE_inv, εLE_l, εLE_r⟩ := reflective_counit_iso I hFull hEmb hRefl (L.obj EX)
    let t : prod (L.obj A) (L.obj EX) ⟶ B := cAE_inv ≫ adjR.ψ (eval_exp A (I.obj B))
    let s : prod (L.obj A) (L.obj (I.obj (L.obj EX))) ⟶ B :=
      prodMap (L.obj A) (L.obj (I.obj (L.obj EX))) (L.obj EX) (counit adjR (L.obj EX)) ≫ t
    let q : L.obj (prod A (I.obj (L.obj EX))) ⟶ B := c A (I.obj (L.obj EX)) ≫ s
    let m : prod A (I.obj (L.obj EX)) ⟶ I.obj B := adjR.φ q
    let r : I.obj (L.obj EX) ⟶ EX := curry m
    have hηr : unit adjR EX ≫ r = Cat.id EX := by
      show unit adjR EX ≫ curry m = _
      rw [curry_precomp, id_eq_curry_eval A (I.obj B)]
      congr 1
      show prodMap A EX (I.obj (L.obj EX)) (unit adjR EX) ≫ adjR.φ q = eval_exp A (I.obj B)
      rw [← adjR.φ_nat_left, ← adjR.φψ (eval_exp A (I.obj B))]
      congr 1
      show L.map (prodMap A EX (I.obj (L.obj EX)) (unit adjR EX)) ≫
            c A (I.obj (L.obj EX)) ≫ s = _
      rw [← Cat.assoc, c_nat A (unit adjR EX), Cat.assoc]
      show c A EX ≫ prodMap (L.obj A) (L.obj EX) (L.obj (I.obj (L.obj EX))) (L.map (unit adjR EX)) ≫
            prodMap (L.obj A) (L.obj (I.obj (L.obj EX))) (L.obj EX) (counit adjR (L.obj EX)) ≫ t = _
      rw [← Cat.assoc (prodMap (L.obj A) (L.obj EX) (L.obj (I.obj (L.obj EX))) (L.map (unit adjR EX))),
          ← prodMap_comp, triangle_one adjR EX, prodMap_id, Cat.id_comp,
          ← Cat.assoc, cAE_l, Cat.id_comp]
    have hLη : L.map (unit adjR EX) = εLE_inv := by
      have h1 : L.map (unit adjR EX) ≫ counit adjR (L.obj EX) = Cat.id (L.obj EX) :=
        triangle_one adjR EX
      calc L.map (unit adjR EX)
          = L.map (unit adjR EX) ≫ counit adjR (L.obj EX) ≫ εLE_inv := by
            rw [εLE_l, Cat.comp_id]
        _ = (L.map (unit adjR EX) ≫ counit adjR (L.obj EX)) ≫ εLE_inv := by rw [Cat.assoc]
        _ = εLE_inv := by rw [h1, Cat.id_comp]
    have hLηr : L.map (unit adjR EX) ≫ L.map r = Cat.id (L.obj EX) := by
      rw [← L.map_comp, hηr, L.map_id]
    have hLr : L.map r = counit adjR (L.obj EX) := by
      have e : εLE_inv ≫ L.map r = εLE_inv ≫ counit adjR (L.obj EX) := by
        rw [εLE_r, ← hLη, hLηr]
      calc L.map r
          = (counit adjR (L.obj EX) ≫ εLE_inv) ≫ L.map r := by rw [εLE_l, Cat.id_comp]
        _ = counit adjR (L.obj EX) ≫ εLE_inv ≫ L.map r := by rw [Cat.assoc]
        _ = counit adjR (L.obj EX) ≫ εLE_inv ≫ counit adjR (L.obj EX) := by rw [e]
        _ = (counit adjR (L.obj EX) ≫ εLE_inv) ≫ counit adjR (L.obj EX) := by rw [Cat.assoc]
        _ = counit adjR (L.obj EX) := by rw [εLE_l, Cat.id_comp]
    have hrη : r ≫ unit adjR EX = Cat.id (I.obj (L.obj EX)) := by
      rw [unit_naturality adjR r, hLr]
      exact triangle_two adjR (L.obj EX)
    exact ⟨r, hηr, hrη⟩

end ExponentialIdeal

/-! ## §1.858  Kuratowski interior and Lawvere-Tierney closure

  On a lattice L.obj (with meets ∧ and order ≤):

  A KURATOWSKI INTERIOR OPERATION is an operation (-)° satisfying:
    x° ≤ x          (deflationary)
    (x°)° = x°      (idempotent)
    (x ∧ y)° = x° ∧ y°  (preserves meets)
  Its fixed points are the OPEN ELEMENTS.

  A LAWVERE-TIERNEY CLOSURE OPERATION j satisfies:
    x ≤ j x           (inflationary)
    j(j x) = j x       (idempotent)
    j(x ∧ y) = j x ∧ j y  (preserves meets)
  Its fixed points are the CLOSED ELEMENTS.

  Theorem: The closed elements of an L-T closure on a Heyting algebra form
  an exponential ideal: if b is closed then (a → b) is closed. -/

section ClosureOnLattice

/-- A lattice L with meets and order, as a type with operations.
    We use a raw-type presentation to stay independent of the
    subobject-based HeytingAlgebra in §1.72. -/
structure MeetLattice where
  carrier   : Type u
  le        : carrier → carrier → Prop
  le_refl   : ∀ x, le x x
  le_trans  : ∀ {x y z}, le x y → le y z → le x z
  le_antisymm : ∀ {x y}, le x y → le y x → x = y
  meet      : carrier → carrier → carrier
  meet_le_left  : ∀ x y, le (meet x y) x
  meet_le_right : ∀ x y, le (meet x y) y
  le_meet   : ∀ {z x y}, le z x → le z y → le z (meet x y)

/-- Every `MeetLattice` satisfies `PosetOrder` — unifies the poset-based closure
    operators (§1.815) with the lattice-based ones (§1.858). -/
instance MeetLattice.toPosetOrder (L : MeetLattice) : PosetOrder L.carrier where
  le := L.le
  le_refl := L.le_refl
  le_trans := @L.le_trans
  le_antisymm := @L.le_antisymm

/-- A HEYTING LATTICE: a bounded lattice (meet-lattice + top, bottom, join)
    with a Heyting implication arrow (§1.72, §1.852).

    ONE concept (§1.72), THREE carriers — separate because the carrier's equality
    differs: this one is an honest carrier `Type` WITH `le_antisymm` (via `MeetLattice`),
    a real poset where the lattice `=`-laws hold. Cf. `HeytingAlgebra` (S1_72) on the
    subobject preorder `Sub(A)` and `HasHeytingArrow` (above) on thin-category homs —
    both preorders with NO antisymmetry, so their laws are stated as mutual `.le`. -/
structure HeytingLattice extends MeetLattice where
  imp       : carrier → carrier → carrier
  imp_adj   : ∀ {x a b}, le (meet a x) b ↔ le x (imp a b)
  top       : carrier
  le_top    : ∀ a, le a top
  bot       : carrier
  bot_le    : ∀ a, le bot a
  join      : carrier → carrier → carrier
  le_join_left  : ∀ a b, le a (join a b)
  le_join_right : ∀ a b, le b (join a b)
  join_le   : ∀ {a b c}, le a c → le b c → le (join a b) c

/-- A KURATOWSKI INTERIOR OPERATION on a meet-lattice (§1.858):
    deflationary, idempotent, and meet-preserving. -/
structure KuratowskiInterior (L : MeetLattice) where
  op      : L.carrier → L.carrier
  deflat  : ∀ x, L.le (op x) x
  idem    : ∀ x, op (op x) = op x
  meet_pres : ∀ x y, op (L.meet x y) = L.meet (op x) (op y)

/-- OPEN ELEMENTS of a Kuratowski interior: the fixed points. -/
def KuratowskiInterior.isOpen {L : MeetLattice} (ki : KuratowskiInterior L) (x : L.carrier) : Prop :=
  ki.op x = x

/- A `KuratowskiInterior` is a closure on the DUAL order.  We don't provide a direct
    `ClosureOpPoset` bridge because the dual order needs its own `PosetOrder` instance;
    users dualizing should create a `PosetOrder` on the `≥` order explicitly. -/

/-- A LAWVERE-TIERNEY CLOSURE OPERATION on a meet-lattice (§1.858):
    order-preserving, inflationary, idempotent, and meet-preserving.
    Extends `ClosureOpPoset` (§1.815) — monotonicity is required as a
    field (per the book's definition); it is also derivable from
    `meet_pres` but that is a theorem, not the definition. -/
structure LawvereTierneyClosure (L : MeetLattice) extends ClosureOpPoset L.carrier where
  meet_pres : ∀ x y, op (L.meet x y) = L.meet (op x) (op y)

/-- CLOSED ELEMENTS of an L-T closure: the fixed points. -/
def LawvereTierneyClosure.isClosed {L : MeetLattice} (j : LawvereTierneyClosure L) (x : L.carrier) : Prop :=
  j.op x = x

/-- §1.858: The closed elements of an L-T closure on a Heyting lattice form
    an exponential ideal: if b is closed then (a → b) is closed. -/
theorem lt_closure_closed_elements_exponential_ideal
    (L : HeytingLattice) (j : LawvereTierneyClosure L.toMeetLattice)
    (a b : L.carrier)
    (hb : j.isClosed b) :
    j.isClosed (L.imp a b) := by
  -- isClosed: j.op x = x; need j.op (imp a b) = imp a b.
  apply L.le_antisymm _ (j.isClosureOp.inflationary _)
  rw [← L.imp_adj]
  have step1 : L.le (L.meet a (j.op (L.imp a b))) (j.op (L.meet a (L.imp a b))) := by
    rw [j.meet_pres]
    exact L.le_meet (L.le_trans (L.meet_le_left _ _) (j.isClosureOp.inflationary a)) (L.meet_le_right _ _)
  have step2 : L.le (j.op (L.meet a (L.imp a b))) (j.op b) :=
    j.isClosureOp.monotone (L.imp_adj.mpr (L.le_refl _))
  have step3 : L.le (j.op b) b := by rw [hb]; exact L.le_refl b
  exact L.le_trans step1 (L.le_trans step2 step3)

/-- A PROTOclosure is an order-preserving, inflationary, idempotent operation
    (§1.815, §1.858).  Extends `ClosureOpPoset` directly — the only addition is
    the equality form of idempotence (which is derivable but kept as a field for
    convenience). -/
structure ProtoClosure (L : MeetLattice) extends ClosureOpPoset L.carrier where
  /-- Idempotence as equality: op(op x) = op x (follows from `idempotent` + `inflationary`). -/
  idem_eq : ∀ x, op (op x) = op x

/-- Fixed points of a ProtoClosure. -/
def ProtoClosure.isClosed {L : MeetLattice} (j : ProtoClosure L) (x : L.carrier) : Prop :=
  j.op x = x

/-- Converse of §1.858: If the closed elements of a `ProtoClosure` (already
    order-preserving by definition) on a Heyting lattice are an exponential ideal
    (a → b closed whenever b is closed), then the operation preserves meets (is L-T).

    NOTE: The theorem as originally stated without monotonicity is FALSE.
    Counterexample: 4-element Boolean algebra {0, a, ¬a, 1}; j(0)=a, j(a)=a,
    j(¬a)=¬a, j(1)=1. This is inflationary, idempotent, hIdeal holds (fixed points
    {a,¬a,1} closed under →), but j(a∧¬a)=j(0)=a ≠ 0=a∧¬a=j(a)∧j(¬a).
    The book's §1.815 "closure operation" requires monotonicity (order-preserving),
    which is now part of `ProtoClosure` (extending `ClosureOpPoset`). -/
theorem exponential_ideal_implies_lt_closure
    (L : HeytingLattice)
    (j : ProtoClosure L.toMeetLattice)
    (hIdeal : ∀ (a b : L.carrier), j.isClosed b → j.isClosed (L.imp a b)) :
    ∀ x y, j.op (L.meet x y) = L.meet (j.op x) (j.op y) := by
  intro x y
  apply L.le_antisymm
  · -- ≤ direction: j(x∧y) ≤ j(x)∧j(y), from order_preserving.
    apply L.le_meet
    · exact j.isClosureOp.monotone (L.meet_le_left x y)
    · exact j.isClosureOp.monotone (L.meet_le_right x y)
  · -- ≥ direction: j(x)∧j(y) ≤ j(x∧y).
    -- KEY LEMMA: z ≤ c (c closed) → j(z) ≤ c  (via order_preserving: j(z) ≤ j(c) = c).
    have key : ∀ z c, j.isClosed c → L.le z c → L.le (j.op z) c := fun z c hc hzc =>
      hc ▸ j.isClosureOp.monotone hzc
    -- j(x∧y) is closed (idempotent).
    have hxy_cl : j.isClosed (j.op (L.meet x y)) := j.idem_eq (L.meet x y)
    -- imp x (j(x∧y)) is closed.
    have hc1 : j.isClosed (L.imp x (j.op (L.meet x y))) := hIdeal x _ hxy_cl
    -- y ≤ imp x j(x∧y): imp_adj.mp with x∧y ≤ j(x∧y) (inflationary).
    have hy_le : L.le y (L.imp x (j.op (L.meet x y))) :=
      L.imp_adj.mp (j.isClosureOp.inflationary (L.meet x y))
    -- j(y) ≤ imp x j(x∧y) by KEY LEMMA (y ≤ it, it closed).
    have hjy_le : L.le (j.op y) (L.imp x (j.op (L.meet x y))) := key y _ hc1 hy_le
    -- x∧j(y) ≤ j(x∧y): imp_adj.mpr with j(y) ≤ imp x j(x∧y).
    have step4 : L.le (L.meet x (j.op y)) (j.op (L.meet x y)) :=
      L.imp_adj.mpr hjy_le
    -- imp j(y) j(x∧y) is closed.
    have hc2 : j.isClosed (L.imp (j.op y) (j.op (L.meet x y))) := hIdeal _ _ hxy_cl
    -- x ≤ imp j(y) j(x∧y): imp_adj.mp with meet j(y) x ≤ j(x∧y).
    have hx_le : L.le x (L.imp (j.op y) (j.op (L.meet x y))) :=
      L.imp_adj.mp (L.le_trans
        (L.le_meet (L.meet_le_right (j.op y) x) (L.meet_le_left (j.op y) x))
        step4)
    -- j(x) ≤ imp j(y) j(x∧y) by KEY LEMMA.
    have hjx_le : L.le (j.op x) (L.imp (j.op y) (j.op (L.meet x y))) := key x _ hc2 hx_le
    -- j(x)∧j(y) ≤ j(x∧y): imp_adj.mpr gives meet (j.op y) (j.op x) ≤ j(x∧y).
    have hmet : L.le (L.meet (j.op y) (j.op x)) (j.op (L.meet x y)) :=
      L.imp_adj.mpr hjx_le
    exact L.le_trans
      (L.le_meet (L.meet_le_right (j.op x) (j.op y)) (L.meet_le_left (j.op x) (j.op y)))
      hmet

end ClosureOnLattice

/-! ## §1.859  Baseable objects

  Given a category 𝒜 with binary products, an object B is BASEABLE if
  B^A = (A × -, B) is representable for all A.  The full subcategory
  𝔹 of baseable objects is itself exponential, and the inclusion 𝔹 → 𝒜
  preserves equalizers. -/

section Baseable

variable {𝒜 : Type u} [Cat.{v} 𝒜] [HasBinaryProducts 𝒜]

/-- B ∈ |𝒜| is BASEABLE if for every A ∈ |𝒜|, the functor (A × -, B)
    is representable (i.e. B^A exists) (§1.859). -/
def Baseable (B : 𝒜) : Prop :=
  ∀ (A : 𝒜), ∃ (E : 𝒜) (ev : prod A E ⟶ B),
    ∀ (X : 𝒜) (f : prod A X ⟶ B),
      ∃ (g : X ⟶ E), prodMap A X E g ≫ ev = f ∧
        ∀ (g' : X ⟶ E), prodMap A X E g' ≫ ev = f → g' = g

/-- The full subcategory of BASEABLE objects of 𝒜 (§1.859). -/
def BaseableSubcat (𝒜 : Type u) [Cat.{v} 𝒜] [HasBinaryProducts 𝒜] : Type u := { B : 𝒜 // Baseable B }

instance : Cat.{v} (BaseableSubcat 𝒜) where
  Hom B₁ B₂ := B₁.1 ⟶ B₂.1
  id B := Cat.id B.1
  comp f g := f ≫ g
  id_comp f := Cat.id_comp f
  comp_id f := Cat.comp_id f
  assoc f g h := Cat.assoc f g h

/-- The inclusion functor 𝔹 → 𝒜. -/
def baseableIncl : BaseableSubcat 𝒜 → 𝒜 := Subtype.val

def baseableInclFunctor : Functor (BaseableSubcat 𝒜) 𝒜 where
  obj := baseableIncl (𝒜 := 𝒜)
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- §1.859: The full subcategory of BASEABLE objects is closed under equalizers — the
    equalizer (taken in 𝒜) of two maps `f, g : B₂ ⇉ B₃` between baseable objects is again
    baseable.  Equivalently, the inclusion `𝔹 → 𝒜` preserves equalizers (the 𝔹-equalizer
    of `f, g` IS their 𝒜-equalizer `eqObj f g`, which therefore lies in 𝔹).

    Freyd's construction (§1.859): for each `A`, `E := eqObj f g` is the equalizer of the
    exponential transposes `f^A, g^A : B₂^A ⇉ B₃^A`, exhibiting `E^A` and hence `E` as
    baseable.  CLOSED (axiom-free): the per-`A` representability is built via the power-object
    classify bijection; `baseable_equalizer_is_baseable` is sorry-free.

    NOTE: this replaces an earlier vacuous version that assumed `[HasEqualizers 𝒜]`, ignored
    its cone/lift hypotheses, and merely returned the ambient equalizer (asserting nothing
    about baseability). The substantive content is exactly this baseable-CLOSURE statement,
    which is what §1.92 `topos_has_exponentials` requires. -/
theorem baseable_equalizer_is_baseable [HasEqualizers 𝒜]
    {B₂ B₃ : 𝒜} (hB₂ : Baseable B₂) (hB₃ : Baseable B₃) (f g : B₂ ⟶ B₃) :
    Baseable (eqObj f g) := by
  -- E := eqObj f g, with q₀ := eqMap f g : E → B₂ monic, q₀≫f = q₀≫g.
  have hq₀mono : Monic (eqMap f g) := eqMap_monic f g
  intro A
  -- Representing data for B₂ and B₃ at stage A.
  obtain ⟨E₂, ev₂, hu₂⟩ := hB₂ A
  obtain ⟨E₃, ev₃, hu₃⟩ := hB₃ A
  -- Exponential transposes fA, gA : E₂ → E₃ of post-composition with f, g.
  obtain ⟨fA, hfA, hfA_uniq⟩ := hu₃ E₂ (ev₂ ≫ f)
  obtain ⟨gA, hgA, _⟩ := hu₃ E₂ (ev₂ ≫ g)
  -- E_A := equalizer of fA, gA, with q := eqMap fA gA : E_A → E₂, q≫fA = q≫gA.
  refine ⟨eqObj fA gA, ?_, ?_⟩
  · -- ev : prod A E_A → E = eqObj f g.
    -- prodMap A E_A E₂ q ≫ ev₂ equalizes f, g, so factors through E.
    refine eqLift f g (prodMap A (eqObj fA gA) E₂ (eqMap fA gA) ≫ ev₂) ?_
    -- (prodMap q ≫ ev₂)≫f = prodMap A E_A E₃ (q≫fA) ≫ ev₃ ; symmetric for g; q≫fA=q≫gA.
    rw [Cat.assoc, Cat.assoc, ← hfA, ← hgA, ← Cat.assoc, ← Cat.assoc,
        ← prodMap_comp, ← prodMap_comp, eqMap_eq]
  · -- Universal property of (E_A, ev).
    intro X φ
    -- φ ≫ q₀ : prod A X → B₂; transpose via B₂-representability to ψ : X → E₂.
    obtain ⟨ψ, hψ, hψ_uniq⟩ := hu₂ X (φ ≫ eqMap f g)
    -- ψ equalizes fA, gA, so lifts to h : X → E_A.
    have hψ_eq : ψ ≫ fA = ψ ≫ gA := by
      -- Both transpose to the same prod A X → B₃ map; cancel by hu₃-injectivity at X.
      obtain ⟨_, _, hinj⟩ := hu₃ X (prodMap A X E₃ (ψ ≫ fA) ≫ ev₃)
      rw [hinj (ψ ≫ fA) rfl, hinj (ψ ≫ gA) ?_]
      -- prodMap A X E₃ (ψ≫gA) ≫ ev₃ = prodMap A X E₃ (ψ≫fA) ≫ ev₃
      rw [prodMap_comp, prodMap_comp, Cat.assoc, Cat.assoc, hfA, hgA,
          ← Cat.assoc, ← Cat.assoc, hψ, Cat.assoc, Cat.assoc, eqMap_eq]
    -- h : X → E_A with h ≫ q = ψ.
    refine ⟨eqLift fA gA ψ hψ_eq, ?_, ?_⟩
    · -- prodMap A X E_A h ≫ ev = φ.  Cancel the monic q₀ = eqMap f g.
      apply hq₀mono
      -- ev ≫ q₀ = prodMap A E_A E₂ q ≫ ev₂  (eqLift_fac); prodMap_comp; eqLift_fac for h; hψ.
      rw [Cat.assoc, eqLift_fac, ← Cat.assoc, ← prodMap_comp, eqLift_fac, hψ]
    · -- Uniqueness of h.
      intro h' hh'
      -- Composing hh' with q₀ and ev₂ pins down h' ≫ q via hu₂; then q monic ⟹ h'.
      have hq'mono : Monic (eqMap fA gA) := eqMap_monic fA gA
      apply hq'mono
      rw [eqLift_fac]
      -- h' ≫ q = ψ via hu₂ uniqueness: prodMap A X E₂ (h'≫q) ≫ ev₂ = φ ≫ q₀.
      rw [hψ_uniq (h' ≫ eqMap fA gA) (by
        -- LHS = prodMap h' ≫ (prodMap q ≫ ev₂) = prodMap h' ≫ (ev ≫ q₀) = φ ≫ q₀.
        rw [prodMap_comp, Cat.assoc,
            ← eqLift_fac f g (prodMap A (eqObj fA gA) E₂ (eqMap fA gA) ≫ ev₂)
              (by rw [Cat.assoc, Cat.assoc, ← hfA, ← hgA, ← Cat.assoc, ← Cat.assoc,
                      ← prodMap_comp, ← prodMap_comp, eqMap_eq]),
            ← Cat.assoc, hh'])]

/-- The evaluation transpose of `c : Y ⟶ E^^A`. -/
def transp {A E Y : 𝒞} (c : Y ⟶ E ^^ A) : prod A Y ⟶ E :=
  prodMap A Y (E ^^ A) c ≫ eval_exp A E

/-- `transp` turns precomposition with `u : Y' ⟶ Y` into precomposition with `(A × u)`. -/
theorem transp_precomp {A E Y Y' : 𝒞} (u : Y' ⟶ Y) (c : Y ⟶ E ^^ A) :
    transp (u ≫ c) = prodMap A Y' Y u ≫ transp c := by
  dsimp [transp]; rw [prodMap_comp, Cat.assoc]

end Baseable

end Freyd
