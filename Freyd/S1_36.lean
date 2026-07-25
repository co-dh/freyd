/-
  Freyd & Scedrov, *Categories and Allegories* §1.36–§1.367
  Inflation, strong equivalence, equivalent categories, equivalence kernel, factorization.
-/


import Freyd.S1_1
import Freyd.S1_18
import Freyd.S1_31
import Freyd.S1_41


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-! ## §1.36 Inflation

  An INFLATION of B is a category [T] with objects 𝛂, an onto function
  T: 𝛂 → |B|, and morphisms A → B defined as the most inclusive
  (when TA = □x and TB = x□).  The forgetful functor [T] → B is
  a full embedding and onto, hence an equivalence functor. -/

/-- An inflation: artificially replicate objects of B.  Given T : 𝛂 → |B| onto,
    the category [T] has objects 𝛂, hom 𝛂(A,B) = B(TA,TB). -/
structure Inflation (B : 𝒞) where
  objSet  : Type u
  T       : objSet → 𝒞
  isOnto  : ∀ b : 𝒞, ∃ a : objSet, T a = b  -- T is surjective (onto)

/-- The inflated category [T] with objects objSet and hom via T. -/
instance (B : 𝒞) (I : Inflation B) : Cat.{v} I.objSet where
  Hom A B := I.T A ⟶ I.T B
  id A := Cat.id (I.T A)
  comp f g := f ≫ g
  id_comp _ := Cat.id_comp _
  comp_id _ := Cat.comp_id _
  assoc _ _ _ := Cat.assoc _ _ _

/-- The inflation forgetful functor F : [T] → B, which is a full embedding. -/
def Inflation.forgetFunctor (B : 𝒞) (I : Inflation B) : Functor I.objSet 𝒞 where
  obj := I.T
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- An inflation cross-section: S : |B| → 𝛂 with T∘S = id. -/
structure InflationCrossSection (B : 𝒞) (I : Inflation B) where
  S : 𝒞 → I.objSet
  sec : ∀ b : 𝒞, I.T (S b) = b

/-! ## §1.362 Strong equivalence from inflation

  The axiom of choice implies every inflation is strongly equivalent to B.
  (We state the condition without assuming AC.) -/

/-- Transport of an identity morphism along an object equality `e : X = Y`.
    This is the canonical iso `X ⟶ Y` witnessing `X = Y` in any category. -/
def eqToHom {X Y : 𝒞} (e : X = Y) : X ⟶ Y := e ▸ Cat.id X

@[simp] theorem eqToHom_refl (X : 𝒞) : eqToHom (rfl : X = X) = Cat.id X := rfl

theorem eqToHom_trans {X Y Z : 𝒞} (e : X = Y) (e' : Y = Z) :
    eqToHom e ≫ eqToHom e' = eqToHom (e.trans e') := by
  cases e; cases e'; exact Cat.id_comp _

theorem eqToHom_comp_eqToHom_symm {X Y : 𝒞} (e : X = Y) :
    eqToHom e ≫ eqToHom e.symm = Cat.id X := by cases e; exact Cat.id_comp _

theorem eqToHom_symm_comp_eqToHom {X Y : 𝒞} (e : X = Y) :
    eqToHom e.symm ≫ eqToHom e = Cat.id Y := by cases e; exact Cat.id_comp _

/-- The cross-section functor `𝒞 → [T]`, sending `b ↦ S b`.  On a map `h : X ⟶ Y`
    it returns `h` transported along `S.sec : I.T (S X) = X` at each endpoint, since
    `Hom` in `[T]` between `S X` and `S Y` is `I.T (S X) ⟶ I.T (S Y)`. -/
def csFunctor (B : 𝒞) (I : Inflation B) (S : InflationCrossSection B I) :
    Functor 𝒞 I.objSet where
  obj b := S.S b
  map {X Y} h := (eqToHom (S.sec X) ≫ h ≫ eqToHom (S.sec Y).symm :
    I.T (S.S X) ⟶ I.T (S.S Y))
  map_id X := by
    show eqToHom (S.sec X) ≫ Cat.id X ≫ eqToHom (S.sec X).symm = Cat.id (I.T (S.S X))
    rw [Cat.id_comp, eqToHom_comp_eqToHom_symm]
  map_comp {X Y Z} f g := by
    show eqToHom (S.sec X) ≫ (f ≫ g) ≫ eqToHom (S.sec Z).symm
      = (eqToHom (S.sec X) ≫ f ≫ eqToHom (S.sec Y).symm)
        ≫ (eqToHom (S.sec Y) ≫ g ≫ eqToHom (S.sec Z).symm)
    simp only [Cat.assoc]
    rw [← Cat.assoc (eqToHom (S.sec Y).symm) (eqToHom (S.sec Y)),
        eqToHom_symm_comp_eqToHom, Cat.id_comp]

/-- If T has a left-inverse (a cross-section S), then the forgetful functor `[T] → B`
    and the cross-section functor `b ↦ S b` constitute a strong equivalence (§1.362). -/
theorem inflation_strong_equiv (B : 𝒞) (I : Inflation B) (S : InflationCrossSection B I) :
    StrongEquivalence (I.forgetFunctor B) (csFunctor B I S) where
  -- unit : NatIso ((csFunctor) ∘ forget) id  on  [T].
  -- component at `a : I.objSet` lives in [T], i.e. is a map I.T (S (I.T a)) ⟶ I.T a in 𝒞.
  unit := ⟨{
    nat := {
      app a := (eqToHom (S.sec (I.T a)) : I.T (S.S (I.T a)) ⟶ I.T a)
      naturality {a a'} f := by
        show (eqToHom (S.sec (I.T a)) ≫ f ≫ eqToHom (S.sec (I.T a')).symm)
            ≫ eqToHom (S.sec (I.T a')) = eqToHom (S.sec (I.T a)) ≫ f
        rw [Cat.assoc, Cat.assoc, eqToHom_symm_comp_eqToHom, Cat.comp_id]
    }
    isIso a := ⟨(eqToHom (S.sec (I.T a)).symm : I.T a ⟶ I.T (S.S (I.T a))),
      eqToHom_comp_eqToHom_symm _, eqToHom_symm_comp_eqToHom _⟩
  }⟩
  -- counit : NatIso (forget ∘ csFunctor) id  on  𝒞.
  -- forget (csFunctor b) = I.T (S b); component at `b` is I.T (S b) ⟶ b via S.sec.
  counit := ⟨{
    nat := {
      app b := (eqToHom (S.sec b) : I.T (S.S b) ⟶ b)
      naturality {b b'} f := by
        show (eqToHom (S.sec b) ≫ f ≫ eqToHom (S.sec b').symm)
            ≫ eqToHom (S.sec b') = eqToHom (S.sec b) ≫ f
        rw [Cat.assoc, Cat.assoc, eqToHom_symm_comp_eqToHom, Cat.comp_id]
    }
    isIso b := ⟨eqToHom (S.sec b).symm,
      eqToHom_comp_eqToHom_symm _, eqToHom_symm_comp_eqToHom _⟩
  }⟩

/-! ## §1.366 Equivalence kernel

  The kernel of an equivalence functor T : A → B is the subcategory 𝓚 ⊆ A
  of maps sent by T to identity maps.  𝓚 is:
  1. Contains all identity maps
  2. A groupoid (every map is iso with inverse in 𝓚)
  3. A pre-order (at most one map A → B)
  Any such subcategory is an EQUIVALENCE KERNEL. -/

/-- An equivalence kernel: a set of maps K ⊆ Mor(A) satisfying:
    1. id_X ∈ K for all X
    2. If f ∈ K then f is iso and f⁻¹ ∈ K
    3. There is at most one K-map between any two objects. -/
structure EquivalenceKernel (𝒞 : Type u) [Cat.{v} 𝒞] where
  mem    : {X Y : 𝒞} → (X ⟶ Y) → Prop
  mem_id : ∀ X : 𝒞, mem (Cat.id X)
  isGroupoid : ∀ {X Y : 𝒞} (f : X ⟶ Y), mem f → (∃ g : Y ⟶ X, mem g ∧ f ≫ g = Cat.id X ∧ g ≫ f = Cat.id Y)
  isPreorder : ∀ {X Y : 𝒞} (f g : X ⟶ Y), mem f → mem g → f = g
  -- A kernel is a subcategory, hence closed under composition: `Q(fg)=Q f·Q g=1·1=1`.
  mem_comp : ∀ {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z), mem f → mem g → mem (f ≫ g)

/-- The kernel of an equivalence functor `T`: the maps `T` sends to identities.

    A map sent to an identity necessarily has equal `T`-images of its endpoints,
    so membership bundles that object equality `e : F X = F Y` alongside the
    `HEq` witnessing `T f = 1`.  Proving the kernel is a *groupoid* genuinely
    needs `T` to be a full embedding (the book's equivalence functor): fullness
    lifts the inverse identity to a map `g : Y → X`, and the embedding (faithful)
    transports `T(fg) = 1 = T(1)` back to `fg = 1`. -/
def equivalenceKernel (F : Functor 𝒞 𝒟) (emb : Embedding F) (full : Full F) :
    EquivalenceKernel 𝒞 where
  mem {X Y} f := ∃ _ : F.obj X = F.obj Y, HEq (F.map f) (Cat.id (F.obj X))
  mem_id X := ⟨rfl, heq_of_eq (F.map_id X)⟩
  isGroupoid {X Y} f h := by
    obtain ⟨e, hf⟩ := h
    -- `cases` on an object-equality only fires when one side is a free variable,
    -- so we package the needed transports as little lemmas over a fresh endpoint.
    have key : ∀ {P Q : 𝒟} (mf : P ⟶ Q) (mg : Q ⟶ P), P = Q →
        HEq mf (Cat.id P) → HEq mg (Cat.id P) → mf ≫ mg = Cat.id P := by
      intro P Q mf mg e' hmf hmg; cases e'
      rw [eq_of_heq hmf, eq_of_heq hmg]; exact Cat.id_comp _
    have idHEq : HEq (Cat.id (F.obj X)) (Cat.id (F.obj Y)) := by
      have h' : ∀ {Q : 𝒟}, F.obj X = Q → HEq (Cat.id (F.obj X)) (Cat.id Q) := by
        intro Q e'; cases e'; exact HEq.rfl
      exact h' e
    -- Lift the inverse identity `F Y → F X` to a kernel map `g : Y → X`.
    obtain ⟨g, hg⟩ := full (cast (congrArg (· ⟶ F.obj X) e) (Cat.id (F.obj X)))
    have hgid : HEq (F.map g) (Cat.id (F.obj X)) := by rw [hg]; exact cast_heq _ _
    refine ⟨g, ⟨e.symm, hgid.trans idHEq⟩, ?_, ?_⟩
    · -- f ≫ g = 1_X, via faithfulness from `T(f)T(g) = 1 = T(1_X)`.
      apply emb (f ≫ g) (Cat.id X)
      rw [F.map_comp, F.map_id]
      exact key (F.map f) (F.map g) e hf hgid
    · -- g ≫ f = 1_Y, symmetrically at the endpoint `F Y`.
      apply emb (g ≫ f) (Cat.id Y)
      rw [F.map_comp, F.map_id]
      exact key (F.map g) (F.map f) e.symm (hgid.trans idHEq) (hf.trans idHEq)
  isPreorder {X Y} f g hf hg := by
    obtain ⟨_, hf'⟩ := hf
    obtain ⟨_, hg'⟩ := hg
    exact emb f g (eq_of_heq (hf'.trans hg'.symm))
  mem_comp {X Y Z} f g hf hg := by
    obtain ⟨e, hf'⟩ := hf
    obtain ⟨e', hg'⟩ := hg
    refine ⟨e.trans e', ?_⟩
    -- `T(fg) = T f · T g`; both factors heq `1`, and `1·1 = 1` at the glued endpoint.
    rw [F.map_comp]
    -- Reduce to a statement over a fresh endpoint so `cases` on object equalities fires.
    have key : ∀ {P Q S : 𝒟} (mf : P ⟶ Q) (mg : Q ⟶ S), P = Q → Q = S →
        HEq mf (Cat.id P) → HEq mg (Cat.id Q) → HEq (mf ≫ mg) (Cat.id P) := by
      intro P Q S mf mg e₁ e₂ hmf hmg; cases e₁; cases e₂
      rw [eq_of_heq hmf, eq_of_heq hmg, Cat.id_comp]
    exact key (F.map f) (F.map g) e e' hf' hg'

/-! ## §1.363 Equivalent categories

  Two categories are EQUIVALENT iff they have isomorphic inflations.  An
  isomorphism of categories is a functor that is a full embedding (faithful +
  full) and a bijection on objects.  Equivalently (the book's Prop.), `𝒞` and
  `𝒟` are equivalent iff there is an equivalence functor between them. -/

/-- A functor is an ISOMORPHISM of categories if it is a full embedding and a
    bijection on objects (§1.363). -/
def IsCatIso (F : Functor 𝒞 𝒟) : Prop :=
  Embedding F ∧ Full F ∧ Function.Injective F.obj ∧ Function.Surjective F.obj

/-- Two categories are EQUIVALENT (§1.363) if they have isomorphic inflations:
    there are inflations `I₁` of `𝒞` and `I₂` of `𝒟` whose inflated categories
    `[T₁]` and `[T₂]` are isomorphic via some functor `Φ`. -/
def AreEquivalent (𝒞 : Type u) [Cat.{v} 𝒞] (𝒟 : Type u) [Cat.{v} 𝒟] : Prop :=
  ∃ (B₁ : 𝒞) (I₁ : Inflation B₁) (B₂ : 𝒟) (I₂ : Inflation B₂)
    (Φ : Functor I₁.objSet I₂.objSet), IsCatIso Φ

/-! ## §1.364 Skeletal category and skeleton

  `IsSkeletal` and `Skeleton` / `CoSkeleton` are defined in `S1_39.lean`
  (they depend on `EquivalentCategories` which in turn uses §1.36 machinery).
  See §1.364 note in S1_36.md. -/

/-! ## §1.361 Factorization of equivalence functors

  Every equivalence functor factors as a cross-section of an inflation, followed
  by an isomorphism of categories, followed by an inflation forgetful functor.

  Following the book: given `F : 𝒞 → 𝒟`, form the category `[T']` whose objects are
  triples `(A, θ, B)` with `θ : FA ≅ B`, and let `T' : [T'] → 𝒟` send `(A,θ,B) ↦ B`.
  `T'` is onto since `F` has a representative image, so `[T']` is an inflation of `𝒟`.
  The functor `Φ : 𝒞 → [T']`, `X ↦ (X, 1, FX)` — the book's cross-section `S` followed
  by the iso `[T] ≅ [T']` — is a **full embedding** with `T' (Φ X) = F X`.

  (Note: `Φ` is a *full embedding*, not a bijection on objects.  A full cat-iso would
  force `F` onto on objects, which an equivalence functor need not be; the book's
  `[T] ≅ [T']` is an iso, but the cross-section `S : 𝒞 → [T]` is not.  The composite
  recorded here is the cross-section-then-iso, i.e. a full embedding.) -/

/-- An object of the inflation `[T']` of `𝒟` built from `F`: a source object `A`,
    a target object `B`, together with the *fact* that some iso `θ : FA ≅ B` exists.

    The book's `G` carries the iso `θ` as data; but the inflated category `[T']` has
    `Hom (A,θ,B) (A',θ',B') = B ⟶ B'`, depending only on the targets, and `θ` is needed
    solely to make `T'` onto.  Recording its *existence* (`Nonempty`) therefore keeps
    `[T']`'s object type in `Type u` while staying faithful — `T'` is still onto exactly
    where `F` has a representative image.  `src` is likewise inessential and dropped. -/
def FactObj (F : Functor 𝒞 𝒟) : Type u :=
  { B : 𝒟 // ∃ (A : 𝒞) (θ : F.obj A ⟶ B), IsIso θ }

/-- The inflation `[T']` of `𝒟` induced by an equivalence functor `F` (its `T'` is
    `Subtype.val`).  `T'` is onto exactly because `F` has a representative image. -/
def factInflation (F : Functor 𝒞 𝒟) (repF : HasRepresentativeImage F) (B : 𝒟) :
    Inflation B where
  objSet := FactObj F
  T := Subtype.val
  isOnto b := by obtain ⟨A, h, hiso⟩ := repF b; exact ⟨⟨b, ⟨A, h, hiso⟩⟩, rfl⟩

/-- The factorizing functor `Φ : 𝒞 → [T']`, `X ↦ (F X, ⟨X, 1, iso⟩)`.  Its action on a
    map is `F`'s, since `Hom (Φ X) (Φ Y) = F X ⟶ F Y` in `[T']`. -/
def factPhi (F : Functor 𝒞 𝒟) (repF : HasRepresentativeImage F) (B : 𝒟) :
    𝒞 → (factInflation F repF B).objSet :=
  fun X => ⟨F.obj X, ⟨X, Cat.id (F.obj X), ⟨Cat.id (F.obj X), Cat.id_comp _, Cat.id_comp _⟩⟩⟩

def factPhiFunctor (F : Functor 𝒞 𝒟) (repF : HasRepresentativeImage F)
    (B : 𝒟) : Functor 𝒞 (factInflation F repF B).objSet where
  obj := factPhi F repF B
  map g := F.map g
  map_id X := F.map_id X
  map_comp f g := F.map_comp f g

/-- §1.361: any equivalence functor `F : 𝒞 → 𝒟` factors through an inflation of `𝒟`.
    There is an inflation `I` of `𝒟` with forgetful `T' : [T'] → 𝒟`, and a *full
    embedding* `Φ : 𝒞 → [T']` (the book's cross-section followed by the iso `[T] ≅ [T']`),
    such that `T' (Φ X) = F X` — i.e. `F = Φ ; T'`. -/
theorem equivalenceFunctor_factorization
    (F : Functor 𝒞 𝒟) (hEq : EquivalenceFunctor F) (B : 𝒟) :
    ∃ (I : Inflation B) (Φ : Functor 𝒞 I.objSet),
      Embedding Φ ∧ Full Φ ∧ ∀ X : 𝒞, I.T (Φ.obj X) = F.obj X := by
  obtain ⟨embF, fullF, repF⟩ := hEq
  refine ⟨factInflation F repF B, factPhiFunctor F repF B, ?_, ?_, ?_⟩
  · -- Embedding: `Φ g = Φ g'` is `F.map g = F.map g'`, so `g = g'` by `F` embedding.
    intro X Y g g' h; exact embF g g' h
  · -- Full: any `h : F X ⟶ F Y` lifts through `F` (full), and `Φ` of the lift is `h`.
    intro X Y h; obtain ⟨g, hg⟩ := fullF h; exact ⟨g, hg⟩
  · -- `T' (Φ X) = F X` by construction (`Subtype.val` of `(F X, …)` is `F X`).
    intro X; rfl

/-! ## §1.366 Quotient by an equivalence kernel

  For any equivalence kernel `K ⊆ A`, there is an onto equivalence functor
  `A → A/K` whose kernel is exactly `K`.  `A/K` glues the `K`-connected objects
  of `A`.  We realise `A/K` as a *skeleton built by representatives*: objects are
  the `K`-classes, and a hom between two classes is just a hom of `𝒞` between the
  chosen representatives.  This makes `Q` full and faithful on the nose and onto
  by construction; the unique `K`-isos to representatives play the role the book's
  double cosets `KxK` play, and Classical choice supplies the representatives. -/

namespace QuotientByKernel

variable (K : EquivalenceKernel 𝒞)

/-- `X` and `Y` are glued iff there is a `K`-map between them.  This is an
    equivalence relation: reflexive by `mem_id`, symmetric by `isGroupoid`,
    transitive by `mem_comp`. -/
def Rel (X Y : 𝒞) : Prop := ∃ f : X ⟶ Y, K.mem f

theorem rel_symm {X Y : 𝒞} : Rel K X Y → Rel K Y X := by
  rintro ⟨f, hf⟩; obtain ⟨g, hg, _, _⟩ := K.isGroupoid f hf; exact ⟨g, hg⟩

theorem rel_trans {X Y Z : 𝒞} : Rel K X Y → Rel K Y Z → Rel K X Z := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩; exact ⟨f ≫ g, K.mem_comp f g hf hg⟩

/-- The setoid gluing `K`-connected objects. -/
def setoid : Setoid 𝒞 := ⟨Rel K, ⟨fun X => ⟨Cat.id X, K.mem_id X⟩, rel_symm K, rel_trans K⟩⟩

/-- Objects of the quotient `𝒞/K`: the `K`-classes. -/
def Obj : Type u := Quotient (setoid K)

/-- The chosen representative object of a class (Classical choice). -/
noncomputable def rep (d : Obj K) : 𝒞 := Classical.choose (Quotient.exists_rep d)

theorem rep_spec (d : Obj K) : Quotient.mk (setoid K) (rep K d) = d :=
  Classical.choose_spec (Quotient.exists_rep d)

/-- Every object is `K`-related to its class representative. -/
theorem rel_rep (X : 𝒞) : Rel K X (rep K (Quotient.mk (setoid K) X)) := by
  have : Quotient.mk (setoid K) X = Quotient.mk (setoid K) (rep K (Quotient.mk (setoid K) X)) :=
    (rep_spec K _).symm
  exact Quotient.exact this

/-- A chosen `K`-iso `κ X : X ⟶ rep ⟦X⟧` (Classical choice of the `K`-map). -/
noncomputable def kappa (X : 𝒞) : X ⟶ rep K (Quotient.mk (setoid K) X) :=
  Classical.choose (rel_rep K X)

/-- The inverse of `κ X`, itself a `K`-map (groupoid), with both round-trips identity. -/
noncomputable def kappaInv (X : 𝒞) : rep K (Quotient.mk (setoid K) X) ⟶ X :=
  Classical.choose (K.isGroupoid _ (Classical.choose_spec (rel_rep K X)))

/-- The quotient category `𝒞/K`: a hom between two classes is a `𝒞`-hom between
    their representatives.  Identity, composition, and the axioms are inherited
    from `𝒞` verbatim. -/
noncomputable instance catObj : Cat.{v} (Obj K) where
  Hom d e := rep K d ⟶ rep K e
  id d := Cat.id (rep K d)
  comp f g := f ≫ g
  id_comp f := Cat.id_comp f
  comp_id f := Cat.comp_id f
  assoc f g h := Cat.assoc f g h

/-- The quotient functor `Q : 𝒞 → 𝒞/K`, identity on objects-up-to-class.  On a
    map `f : X ⟶ Y` it conjugates by the representative isos:
    `Q f = (κ X)⁻¹ ≫ f ≫ κ Y : rep⟦X⟧ ⟶ rep⟦Y⟧`. -/
abbrev Q : 𝒞 → Obj K := fun X => Quotient.mk (setoid K) X

/-- `Q`'s action on maps, conjugating by representative `K`-isos.  Lives in `𝒞` as
    a map `rep⟦X⟧ ⟶ rep⟦Y⟧`, which is exactly `Q K X ⟶ Q K Y` in `catObj`. -/
noncomputable def Qmap {X Y : 𝒞} (f : X ⟶ Y) :
    rep K (Quotient.mk (setoid K) X) ⟶ rep K (Quotient.mk (setoid K) Y) :=
  kappaInv K X ≫ f ≫ kappa K Y

theorem Qmap_id (X : 𝒞) : Qmap K (Cat.id X) = Cat.id (Q K X) := by
  -- both sides live in 𝒞 as maps `rep⟦X⟧ ⟶ rep⟦X⟧`; `Cat.id (Q K X) = Cat.id (rep⟦X⟧)`.
  show kappaInv K X ≫ Cat.id X ≫ kappa K X = Cat.id (rep K (Quotient.mk (setoid K) X))
  rw [Cat.id_comp, show kappaInv K X ≫ kappa K X = Cat.id (rep K (Quotient.mk (setoid K) X))
    from (Classical.choose_spec (K.isGroupoid _ (Classical.choose_spec (rel_rep K X)))).2.2]

theorem Qmap_comp {X Y Z : 𝒞} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Qmap K (f ≫ g) = Qmap K f ≫ Qmap K g := by
  -- `catObj`'s composition is `𝒞`'s, so this is a `𝒞`-identity after cancelling `κY⁻¹κY`.
  show kappaInv K X ≫ (f ≫ g) ≫ kappa K Z
    = (kappaInv K X ≫ f ≫ kappa K Y) ≫ (kappaInv K Y ≫ g ≫ kappa K Z)
  simp only [Cat.assoc]
  rw [← Cat.assoc (kappa K Y) (kappaInv K Y),
    show kappa K Y ≫ kappaInv K Y = Cat.id Y
      from (Classical.choose_spec (K.isGroupoid _ (Classical.choose_spec (rel_rep K Y)))).2.1, Cat.id_comp]

noncomputable def functorQ : Functor 𝒞 (Obj K) where
  obj := Q K
  map := Qmap K
  map_id := Qmap_id K
  map_comp := Qmap_comp K

theorem Q_surjective : Function.Surjective (Q K) := by
  intro d; exact ⟨rep K d, rep_spec K d⟩

/-- `Q` is faithful: `Qmap f = Qmap g` forces `f = g`, because conjugation by
    the iso `κ` is injective. -/
theorem Q_embedding : Embedding (functorQ K) := by
  intro X Y f g h
  -- h : Qmap f = Qmap g, i.e. (κX)⁻¹ ≫ f ≫ κY = (κX)⁻¹ ≫ g ≫ κY.
  have h' : kappaInv K X ≫ f ≫ kappa K Y = kappaInv K X ≫ g ≫ kappa K Y := h
  -- precompose by κX, cancel; postcompose by (κY)⁻¹, cancel.
  have e1 : kappa K X ≫ (kappaInv K X ≫ f ≫ kappa K Y) ≫ kappaInv K Y
          = kappa K X ≫ (kappaInv K X ≫ g ≫ kappa K Y) ≫ kappaInv K Y := by rw [h']
  -- LHS simplifies to f, RHS to g.
  have simp1 : ∀ h : X ⟶ Y,
      kappa K X ≫ (kappaInv K X ≫ h ≫ kappa K Y) ≫ kappaInv K Y = h := by
    intro h
    simp only [Cat.assoc]
    rw [← Cat.assoc (kappa K X) (kappaInv K X),
      show kappa K X ≫ kappaInv K X = Cat.id X
        from (Classical.choose_spec (K.isGroupoid _ (Classical.choose_spec (rel_rep K X)))).2.1, Cat.id_comp,
      show kappa K Y ≫ kappaInv K Y = Cat.id Y
        from (Classical.choose_spec (K.isGroupoid _ (Classical.choose_spec (rel_rep K Y)))).2.1, Cat.comp_id]
  rw [simp1 f, simp1 g] at e1; exact e1

/-- `Q` is full: every hom `rep⟦X⟧ ⟶ rep⟦Y⟧` is `Qmap` of some `f : X ⟶ Y`. -/
theorem Q_full : Full (functorQ K) := by
  intro X Y (h : rep K (Quotient.mk (setoid K) X) ⟶ rep K (Quotient.mk (setoid K) Y))
  -- take f := κX ≫ h ≫ (κY)⁻¹; then Qmap f = (κX)⁻¹ ≫ (κX ≫ h ≫ (κY)⁻¹) ≫ κY = h.
  refine ⟨kappa K X ≫ h ≫ kappaInv K Y, ?_⟩
  show kappaInv K X ≫ (kappa K X ≫ h ≫ kappaInv K Y) ≫ kappa K Y = h
  simp only [Cat.assoc]
  rw [← Cat.assoc (kappaInv K X) (kappa K X),
    show kappaInv K X ≫ kappa K X = Cat.id (rep K (Quotient.mk (setoid K) X))
      from (Classical.choose_spec (K.isGroupoid _ (Classical.choose_spec (rel_rep K X)))).2.2, Cat.id_comp,
    show kappaInv K Y ≫ kappa K Y = Cat.id (rep K (Quotient.mk (setoid K) Y))
      from (Classical.choose_spec (K.isGroupoid _ (Classical.choose_spec (rel_rep K Y)))).2.2, Cat.comp_id]

theorem Q_repImage : HasRepresentativeImage (functorQ K) := by
  intro d
  -- d = ⟦rep d⟧ = Q (rep d); the identity is an iso witness.
  refine ⟨rep K d, ?_⟩
  -- Q (rep d) = ⟦rep d⟧ = d, so we need an iso Q(rep d) ⟶ d. Use eqToHom over that equality.
  have e : Q K (rep K d) = d := rep_spec K d
  exact ⟨eqToHom e, eqToHom e.symm, eqToHom_comp_eqToHom_symm e, eqToHom_symm_comp_eqToHom e⟩

/-- `Q f` is a `K`-map whenever `f` is: it is `(κX)⁻¹ ≫ f ≫ κY`, a composite of `K`-maps. -/
theorem Qmap_mem_of_mem {X Y : 𝒞} (f : X ⟶ Y) (hf : K.mem f) : K.mem (Qmap K f) :=
  K.mem_comp _ _ (Classical.choose_spec (K.isGroupoid _ (Classical.choose_spec (rel_rep K X)))).1
    (K.mem_comp _ _ hf (Classical.choose_spec (rel_rep K Y)))

/-- Conversely, `f = κX ≫ (Q f) ≫ (κY)⁻¹`, so `f` is a `K`-map whenever `Q f` is. -/
theorem mem_of_Qmap_mem {X Y : 𝒞} (f : X ⟶ Y) (hQf : K.mem (Qmap K f)) : K.mem f := by
  have hfac : kappa K X ≫ Qmap K f ≫ kappaInv K Y = f := by
    show kappa K X ≫ (kappaInv K X ≫ f ≫ kappa K Y) ≫ kappaInv K Y = f
    simp only [Cat.assoc]
    rw [← Cat.assoc (kappa K X) (kappaInv K X),
      show kappa K X ≫ kappaInv K X = Cat.id X
        from (Classical.choose_spec (K.isGroupoid _ (Classical.choose_spec (rel_rep K X)))).2.1, Cat.id_comp,
      show kappa K Y ≫ kappaInv K Y = Cat.id Y
        from (Classical.choose_spec (K.isGroupoid _ (Classical.choose_spec (rel_rep K Y)))).2.1, Cat.comp_id]
  rw [← hfac]
  exact K.mem_comp _ _ (Classical.choose_spec (rel_rep K X))
    (K.mem_comp _ _ hQf (Classical.choose_spec (K.isGroupoid _ (Classical.choose_spec (rel_rep K Y)))).1)

/-- If two objects are glued (`Q X = Q Y`) their representatives are equal. -/
theorem rep_eq_of_Q_eq {X Y : 𝒞} (h : Q K X = Q K Y) :
    rep K (Q K X) = rep K (Q K Y) := congrArg (rep K) h

end QuotientByKernel

/-- §1.366: every equivalence kernel `K` of `𝒞` arises as the kernel of an onto
    equivalence functor `Q : 𝒞 → 𝒟`.  "Kernel = K" means a map `f` lies in `K`
    iff `Q` collapses it to an identity (equal endpoints, `Q f` heq `1`). -/
theorem quotientByKernel_exists (K : EquivalenceKernel 𝒞) :
    ∃ (𝒟 : Type u) (_ : Cat.{v} 𝒟) (Q : Functor 𝒞 𝒟),
      EquivalenceFunctor Q ∧ Function.Surjective Q.obj ∧
      (∀ {X Y : 𝒞} (f : X ⟶ Y),
        K.mem f ↔ ∃ _ : Q.obj X = Q.obj Y, HEq (Q.map f) (Cat.id (Q.obj X))) := by
  refine ⟨QuotientByKernel.Obj K, QuotientByKernel.catObj K,
    QuotientByKernel.functorQ K,
    ⟨QuotientByKernel.Q_embedding K, QuotientByKernel.Q_full K, QuotientByKernel.Q_repImage K⟩,
    QuotientByKernel.Q_surjective K, ?_⟩
  intro X Y f
  constructor
  · -- f ∈ K  ⟹  Q X = Q Y  and  Q f heq 1.
    intro hf
    have hXY : QuotientByKernel.Q K X = QuotientByKernel.Q K Y := Quotient.sound ⟨f, hf⟩
    refine ⟨hXY, ?_⟩
    -- `Q f = (κX)⁻¹ ≫ f ≫ κY` is a `K`-map; over the equal endpoints `rep⟦X⟧ = rep⟦Y⟧`
    -- the preorder forces it equal to the identity (also a `K`-map there).
    have hQf : K.mem (QuotientByKernel.Qmap K f) := QuotientByKernel.Qmap_mem_of_mem K f hf
    -- Generalise over the endpoint equality so `cases` can fire.
    have e : QuotientByKernel.rep K (QuotientByKernel.Q K X)
           = QuotientByKernel.rep K (QuotientByKernel.Q K Y) :=
      QuotientByKernel.rep_eq_of_Q_eq K hXY
    -- `hQf.map f` lives in `rep⟦X⟧ ⟶ rep⟦Y⟧`; transport to `rep⟦X⟧ ⟶ rep⟦X⟧` and use preorder.
    -- `Cat.id (Q X)` in `catObj` is `Cat.id (rep⟦X⟧)` in `𝒞`.
    show HEq (QuotientByKernel.Qmap K f)
      (Cat.id (QuotientByKernel.rep K (QuotientByKernel.Q K X)))
    revert hQf
    generalize QuotientByKernel.Qmap K f = m
    -- Now `m : rep⟦X⟧ ⟶ rep⟦Y⟧`.  With `e : rep⟦X⟧ = rep⟦Y⟧`, cases on `e`.
    revert m
    rw [← e]
    intro m hm
    -- `m, Cat.id` are both `K`-maps `rep⟦X⟧ ⟶ rep⟦X⟧`; the preorder identifies them.
    exact heq_of_eq (K.isPreorder m (Cat.id _) hm (K.mem_id _))
  · -- Q X = Q Y  and  Q f heq 1  ⟹  f ∈ K.
    rintro ⟨hXY, hf⟩
    -- `Q f` heq the identity, hence (over the equal endpoints) is a `K`-map; then `f` is too.
    apply QuotientByKernel.mem_of_Qmap_mem K f
    have e : QuotientByKernel.rep K (QuotientByKernel.Q K X)
           = QuotientByKernel.rep K (QuotientByKernel.Q K Y) :=
      QuotientByKernel.rep_eq_of_Q_eq K hXY
    -- `hf : HEq (Q f) (Cat.id rep⟦X⟧)`.  Transport `Q f` to `rep⟦X⟧ ⟶ rep⟦X⟧` and read off `= id`.
    have hf' : HEq (QuotientByKernel.Qmap K f)
        (Cat.id (QuotientByKernel.rep K (QuotientByKernel.Q K X))) := hf
    revert hf'
    generalize QuotientByKernel.Qmap K f = m
    revert m
    rw [← e]
    intro m hm
    rw [eq_of_heq hm]; exact K.mem_id _

/-! ## §1.366 Universal property of the quotient by an equivalence kernel

  Book §1.366 second emph: if F : A → B is any functor such that F sends every
  K-map to an identity map, then there exists a unique functor A/K → B making
  F = A → A/K → B.  This is the universal property of the kernel quotient. -/

/-- §1.366 (universal property): if `F : 𝒞 → 𝒟` collapses all `K`-maps to identities,
    it factors uniquely through the quotient `Q : 𝒞 → 𝒞/K`.
    The induced functor sends a class `d = ⟦X⟧` to `F (rep K d)` (the F-image of the
    chosen representative), and its uniqueness follows from Q being a full embedding. -/
theorem quotient_universal_property (K : EquivalenceKernel 𝒞)
    {𝒟 : Type u} [Cat.{v} 𝒟]
    (F : Functor 𝒞 𝒟)
    (hFK : ∀ {X Y : 𝒞} (f : X ⟶ Y), K.mem f →
        ∃ _ : F.obj X = F.obj Y, HEq (F.map f) (Cat.id (F.obj X))) :
    ∃ (G : Functor (QuotientByKernel.Obj K) 𝒟),
      (∀ X : 𝒞, G.obj (QuotientByKernel.Q K X) = F.obj X) ∧
      (∀ G' : Functor (QuotientByKernel.Obj K) 𝒟,
        (∀ X : 𝒞, G'.obj (QuotientByKernel.Q K X) = F.obj X) → G'.obj = G.obj) := by
  -- The induced functor sends each class d to F of its chosen representative.
  -- G.map (h : rep d ⟶ rep e) := F.map h; axioms inherited from F.
  refine ⟨⟨fun d => F.obj (QuotientByKernel.rep K d), fun h => F.map h,
    fun d => F.map_id _, fun f g => F.map_comp f g⟩, ?_, ?_⟩
  · -- Existence: G ∘ Q = F on objects.
    -- G (Q K X) = F (rep K (Q K X)); need F (rep K (Q K X)) = F X.
    -- hFK on the K-iso κ X : X ⟶ rep K (Q K X) gives F X = F (rep K (Q K X)).
    intro X
    obtain ⟨e, _⟩ := hFK (QuotientByKernel.kappa K X)
      (Classical.choose_spec (QuotientByKernel.rel_rep K X))
    exact e.symm
  · -- Uniqueness (of the object map): any G' with G'.obj (Q K X) = F.obj X agrees with G on objects.
    intro G' hG'
    funext d
    -- d = Q K (rep K d) by rep_spec, so G'.obj d = G'.obj (Q K (rep K d)) = F.obj (rep K d) = G.obj d.
    have hd : QuotientByKernel.Q K (QuotientByKernel.rep K d) = d :=
      QuotientByKernel.rep_spec K d
    calc G'.obj d
        = G'.obj (QuotientByKernel.Q K (QuotientByKernel.rep K d)) := by rw [hd]
      _ = F.obj (QuotientByKernel.rep K d) := hG' _

/-! ## §1.367 Factorization of equivalence functors via equivalence kernel

  Book §1.367: combining §1.361 and §1.366, any equivalence functor
  `F : A → B` is the composition of an inflation cross-section, followed
  by a canonical functor of the form `A → A/K`, followed by an isomorphism.

  That is: there is an equivalence kernel `K ⊆ [T]` (the book's mapping-cylinder
  kernel) such that the induced quotient functor `[T] → [T]/K` is an isomorphism
  of categories, and the inflation forgetful map is the identity on the target side.
  The cleanest statement is that `F` is conjugate to a composition of an inflation
  cross-section with an onto equivalence functor whose kernel is exactly the book's K. -/

/-- §1.367: Any equivalence functor `F : 𝒞 → 𝒟` factors as
    the canonical quotient `Q : 𝒞 → 𝒞/K` (onto equivalence functor whose kernel is K)
    followed by an equivalence functor `G : 𝒞/K → 𝒟` that is also a full embedding,
    where `K = equivalenceKernel F`.

    Combining §1.361 and §1.366: `K` is the equivalence kernel of `F` (maps sent to identities);
    the quotient `Q` by `K` has kernel exactly `K`; the universal property of `Q` produces a
    unique `G` with `G ∘ Q = F`; and `G` is an isomorphism in the sense of `EquivalenceFunctor`
    (embedding + full + representative image), because `F` is an equivalence functor.

    Note: `IsCatIso` requires strict surjectivity on objects, which equivalence functors
    need not satisfy (they are only surjective up to isomorphism).  The correct conclusion
    is `EquivalenceFunctor G`, matching the book. -/
theorem equivalenceFunctor_factors_via_kernel
    (F : Functor 𝒞 𝒟) (hEq : EquivalenceFunctor F) :
    let K := equivalenceKernel F hEq.1 hEq.2.1
    let Q := @QuotientByKernel.Q 𝒞 _ K
    ∃ (G : Functor (QuotientByKernel.Obj K) 𝒟),
      (∀ X : 𝒞, G.obj (Q X) = F.obj X) ∧ EquivalenceFunctor G := by
  obtain ⟨embF, fullF, repF⟩ := hEq
  let K := equivalenceKernel F embF fullF
  -- Build G explicitly: G d = F (rep K d), G.map h = F.map h.
  -- This is the unique functor given by the universal property (§1.366), constructed directly.
  let G : Functor (QuotientByKernel.Obj K) 𝒟 :=
    ⟨fun d => F.obj (QuotientByKernel.rep K d), fun h => F.map h,
      fun d => F.map_id _, fun f g => F.map_comp f g⟩
  -- Commutativity: G (Q K X) = F X, via F (rep K (Q K X)) = F X.
  -- equivalenceKernel maps X to rep(⟦X⟧) which is κ-related to X; F sends κ X to id,
  -- so F (rep K (Q K X)) = F X by injectivity + the K-iso witnessing their equality.
  have hGQ : ∀ X : 𝒞, G.obj (QuotientByKernel.Q K X) = F.obj X := by
    intro X
    -- G (Q K X) = F (rep K (Q K X)).  The κ-iso κ X : X ⟶ rep(⟦X⟧) is a K-map.
    -- K.mem (kappa K X) means ∃ e : F X = F (rep K (Q K X)), HEq (F.map (kappa K X)) (Cat.id (F X)).
    obtain ⟨e, _⟩ := Classical.choose_spec (QuotientByKernel.rel_rep K X)
    exact e.symm
  refine ⟨G, hGQ, ?_, ?_, ?_⟩
  -- Step 3: G is an embedding.
  -- G.map is definitionally F.map, so embF applies directly.
  · intro D E h h' hGhh'
    exact embF h h' hGhh'
  -- Step 4: G is full: any k : F(rep D) ⟶ F(rep E) lifts via fullF.
  -- f : rep D ⟶ rep E is DEFINITIONALLY a hom D ⟶ E in catObj (Hom D E = rep D ⟶ rep E).
  · intro D E k
    obtain ⟨f, hf⟩ := fullF k
    exact ⟨f, hf⟩
  -- Step 5: G has representative image.
  -- For b : 𝒟, repF gives A : 𝒞 with h : F A ⟶ b iso.
  -- G (Q K A) = F A by hGQ, so eqToHom (hGQ A) ≫ h : G (Q K A) ⟶ b is an iso.
  · intro b
    obtain ⟨A, h, hiso⟩ := repF b
    refine ⟨QuotientByKernel.Q K A, eqToHom (hGQ A) ≫ h, ?_⟩
    exact isIso_comp ⟨eqToHom (hGQ A).symm, eqToHom_comp_eqToHom_symm _, eqToHom_symm_comp_eqToHom _⟩ hiso

/-! ## §1.367 Equivalence kernels classify equivalence functors

  Combining §1.366 and `equivalenceKernel`: the equivalence kernels of `𝒞` are
  exactly the kernels of onto equivalence functors out of `𝒞`. -/

/-- §1.367: a subset of maps `K` is an equivalence kernel of `𝒞` iff it is the
    kernel of some onto equivalence functor out of `𝒞`. -/
theorem equivalenceKernel_iff_kernel_of_functor
    (mem : {X Y : 𝒞} → (X ⟶ Y) → Prop) :
    (∃ K : EquivalenceKernel 𝒞, ∀ {X Y : 𝒞} (f : X ⟶ Y), K.mem f ↔ mem f) ↔
    (∃ (𝒟 : Type u) (_ : Cat.{v} 𝒟) (Q : Functor 𝒞 𝒟),
      EquivalenceFunctor Q ∧ Function.Surjective Q.obj ∧
      ∀ {X Y : 𝒞} (f : X ⟶ Y),
        mem f ↔ ∃ _ : Q.obj X = Q.obj Y, HEq (Q.map f) (Cat.id (Q.obj X))) := by
  constructor
  · -- forward: every equivalence kernel is the kernel of its quotient functor (§1.366).
    rintro ⟨K, hK⟩
    obtain ⟨𝒟, instD, Q, heq, honto, hker⟩ := quotientByKernel_exists K
    refine ⟨𝒟, instD, Q, heq, honto, ?_⟩
    intro X Y f
    exact (hK f).symm.trans (hker f)
  · -- backward: the kernel of an onto equivalence functor is an equivalence kernel
    --   (its members are exactly the maps `Q` collapses), via `equivalenceKernel`.
    rintro ⟨𝒟, instD, Q, ⟨emb, full, _⟩, _honto, hker⟩
    refine ⟨equivalenceKernel Q emb full, ?_⟩
    intro X Y f
    -- `equivalenceKernel`'s membership IS the `Q`-collapse condition, definitionally.
    exact (Iff.rfl).trans (hker f).symm

end Freyd
