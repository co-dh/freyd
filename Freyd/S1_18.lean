/-
  Freyd & Scedrov, *Categories and Allegories* §1.18  Functors, §1.181.

  §1.18  A functor F : A → B preserves source, target, and composition.
         In object-centric form: object map + morphism map preserving id/comp.
  §1.181 Any functor preserves left- and right-invertibility.
         Moreover, the image of an inverse is an inverse of the image.

  ---
  ## Lean tactics used in this file (for readers unfamiliar with Lean)

  `rw [h]`      — **rewrite**.  Replace the goal (or a hypothesis) using the
                  equality `h`.  `rw` searches for the left side of `h` in the
                  goal and replaces it with the right side.  `← h` rewrites
                  the other direction (right side → left side).

  `refine ⟨x, h₁, h₂⟩` — provide the components of an `∃` or `∧` goal one
                  by one.  `⟨a, b⟩` is syntax for a tuple; `?` marks a subgoal
                  to be proved in a later bullet `·`.

  `obtain ⟨g, hfg, hgf⟩ := hf` — **case split**.  If `hf : IsIso f` (i.e.
                  `∃ g, f ≫ g = id ∧ g ≫ f = id`), this names the witness
                  `g` and the two proofs `hfg`, `hgf`.

  `constructor` — split an `∧` goal into two separate subgoals.

  `dsimp`       — **definitional simplify**.  Unfolds definitions.

  `·`           — **bullet**.  Starts the proof of the next subgoal.

  `rfl`         — **reflexivity**.  Proves `x = x`.

  `by`          — enters **tactic mode** for a proof block.
-/

module

public import Freyd.S1_10
public import Freyd.S1_17
public import Freyd.S1_41


open Freyd

universe v v₁ v₂ u u₁ u₂ u₃

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-- §1.18  A functor from `𝒞` to `𝒟`, bundled as one structure:
    - `obj`   : the map on objects.
    - `map`   : for each `f : X ⟶ Y`, a morphism `map f : obj X ⟶ obj Y`.
    - `map_id` / `map_comp` : preservation laws.

    In the book's single-sorted language, a functor is a function `F`
    on morphisms such that `□(Fx) = F(□x)`, `(Fx)□ = F(x□)`, and
    `F(xy) = (Fx)(Fy)`.  Our object-centric definition is equivalent.
    (Bundled rather than a class over the object map: distinct functors
    routinely share an object map — e.g. functors between one-object
    categories are monoid homomorphisms — so the morphism action cannot
    be recovered by instance search.) -/
public structure Functor (C : Type u₁) (D : Type u₂) [Cat.{v₁} C] [Cat.{v₂} D] where
  obj  : C → D
  map  : {X Y : C} → (X ⟶ Y) → (obj X ⟶ obj Y)
  map_id : ∀ (X : C), map (Cat.id X) = Cat.id (obj X)
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g

/-- The identity functor `1_𝒞` : every object and morphism maps to itself.
    Reducible so that `idFunctor.obj X`/`idFunctor.map f` compute to `X`/`f` at reducible
    transparency — the bundled replacement for the old raw `λ X => X` object map, which
    β-reduced on its own in identity/naturality laws. -/
@[reducible, expose] public def idFunctor : Functor 𝒞 𝒞 where
  obj X := X
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Composition of two functors, in diagram order: first `F`, then `G`.
    Fully universe-polymorphic (source, middle, target may live in different object
    universes) so it also serves the cross-universe compositions §1.1(10) needs. -/
@[expose] public def compFunctor {C : Type u₁} [Cat.{v} C] {D : Type u₂} [Cat.{v} D] {E : Type u₃} [Cat.{v} E]
    (F : Functor C D) (G : Functor D E) : Functor C E where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)
  map_id X := by
    rw [F.map_id, G.map_id]
  map_comp f g := by
    rw [F.map_comp, G.map_comp]

/-! Definitional computation lemmas for `idFunctor`/`compFunctor` (all `rfl`), marked
    `@[simp]` so `simp` normalizes the object/morphism action of composites and the
    identity — the standard idiom, needed because a bundled functor's `.obj`/`.map`
    projection does not β-reduce on its own (unlike the old raw `λ X => X`). -/

@[simp] theorem idFunctor_obj (X : 𝒞) : (idFunctor : Functor 𝒞 𝒞).obj X = X := rfl

@[simp] theorem idFunctor_map {X Y : 𝒞} (f : X ⟶ Y) : (idFunctor : Functor 𝒞 𝒞).map f = f := rfl

@[simp] public theorem compFunctor_obj {C : Type u₁} [Cat.{v} C] {D : Type u₂} [Cat.{v} D]
    {E : Type u₃} [Cat.{v} E] (F : Functor C D) (G : Functor D E)
    (X : C) : (compFunctor F G).obj X = G.obj (F.obj X) := rfl

@[simp] theorem compFunctor_map {C : Type u₁} [Cat.{v} C] {D : Type u₂} [Cat.{v} D]
    {E : Type u₃} [Cat.{v} E] (F : Functor C D) (G : Functor D E)
    {X Y : C} (f : X ⟶ Y) : (compFunctor F G).map f = G.map (F.map f) := rfl

/-! ## §1.181 as a general concept: preservation / reflection of a morphism-property -/

/-- A property of morphisms, uniform across all categories (e.g. `@Monic`, `@IsIso`, `@Cover`). -/
abbrev MorphProp := ∀ {𝒜 : Type u} [Cat.{v} 𝒜] {X Y : 𝒜}, (X ⟶ Y) → Prop

/-- `F` PRESERVES `P` if it carries `P`-arrows to `P`-arrows. -/
def Preserves {ℰ ℱ : Type u} [Cat.{v} ℰ] [Cat.{v} ℱ] (F : Functor ℰ ℱ) (P : MorphProp.{v,u}) : Prop :=
  ∀ {X Y : ℰ} {f : X ⟶ Y}, P f → P (F.map f)

/-- `F` REFLECTS `P` if a `P`-image forces a `P`-arrow (the shape of the §1.531 Slice Lemma). -/
def Reflects {ℰ ℱ : Type u} [Cat.{v} ℰ] [Cat.{v} ℱ] (F : Functor ℰ ℱ) (P : MorphProp.{v,u}) : Prop :=
  ∀ {X Y : ℰ} {f : X ⟶ Y}, P (F.map f) → P f

/-! ### Cross-universe preservation/reflection of `Monic`

  The generic `Preserves`/`Reflects` above take the property as a `MorphProp`
  *parameter*, which fixes one object universe — so they only apply to functors
  whose source and target live in the same universe (e.g. endofunctors).  The
  slice forgetful functor `Σ : A/B → A` is genuinely cross-universe
  (`Over B : Type (max u v)` vs `A : Type u`), so we give `Monic`-specific
  versions: because `Monic` is applied *directly* (not through a parameter) and is
  itself universe-polymorphic, these work for `Functor`s between categories in
  different universes. -/

/-- `F` PRESERVES monos: it carries monos to monos. -/
@[expose] public def PreservesMono {C : Type u₁} [Cat.{v} C] {D : Type u₂} [Cat.{v} D]
    (F : Functor C D) : Prop :=
  ∀ {X Y : C} {f : X ⟶ Y}, Monic f → Monic (F.map f)

/-- `F` REFLECTS monos: a mono image forces a mono. -/
@[expose] public def ReflectsMono {C : Type u₁} [Cat.{v} C] {D : Type u₂} [Cat.{v} D]
    (F : Functor C D) : Prop :=
  ∀ {X Y : C} {f : X ⟶ Y}, Monic (F.map f) → Monic f

/-- **§1.181**: a functor preserves isomorphisms.  If `f : X → Y` has a two-sided inverse in `𝒞`,
    then `F.map f` has a two-sided inverse in `𝒟`.

    Stated across two object universes, unlike `preserves_iso` below, which cannot be: `Preserves`
    quantifies over a single `MorphProp.{v,u}` and so forces `𝒞` and `𝒟` into one universe.  The
    cross-universe form is what the §2.218 stalk composite `Map 𝒜 → Set^I` needs. -/
public theorem functor_preserves_iso {𝒞 : Type u₁} {𝒟 : Type u₂} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    {F : Functor 𝒞 𝒟} {X Y : 𝒞} (f : X ⟶ Y) (hf : IsIso f) : IsIso (F.map f) := by
  obtain ⟨g, hfg, hgf⟩ := hf
  exact ⟨F.map g,
    by rw [← F.map_comp, hfg, F.map_id],
    by rw [← F.map_comp, hgf, F.map_id]⟩

/-- **§1.181 restated**: every functor preserves isomorphisms.  This is the one
    morphism-property preserved by *all* functors; preservation of `@Monic`, `@Cover`, … are
    separate statements that need hypotheses on `F`. -/
theorem preserves_iso (F : Functor 𝒞 𝒟) : Preserves F @IsIso :=
  fun hf => functor_preserves_iso _ hf

/-- **§1.181**: every functor preserves right-invertibility. -/
theorem preserves_has_right_inv (F : Functor 𝒞 𝒟) : Preserves F RightInvertible := by
  intro X Y f ⟨g, hfg⟩
  exact ⟨F.map g, by rw [← F.map_comp, hfg, F.map_id]⟩

/-- **§1.181**: every functor preserves left-invertibility. -/
theorem preserves_has_left_inv (F : Functor 𝒞 𝒟) : Preserves F LeftInvertible := by
  intro X Y f ⟨g, hgf⟩
  exact ⟨F.map g, by rw [← F.map_comp, hgf, F.map_id]⟩

section FunctorProperties
variable {F : Functor 𝒞 𝒟}

/-- **§1.181**: the image of the inverse is an inverse of the image.

    If `g` is a specific two-sided inverse of `f` (so `f ≫ g = id_X`
    and `g ≫ f = id_Y`), then `F.map g` is a two-sided inverse of
    `F.map f`.  Returns both equations as a pair (`∧`). -/
theorem functor_map_inv {X Y : 𝒞} (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : f ≫ g = Cat.id X) (hgf : g ≫ f = Cat.id Y) :
    F.map f ≫ F.map g = Cat.id (F.obj X) ∧
    F.map g ≫ F.map f = Cat.id (F.obj Y) := by
  constructor
  · rw [← F.map_comp, hfg, F.map_id]
  · rw [← F.map_comp, hgf, F.map_id]

end FunctorProperties

/-! ## §1.182  Opposite category and contravariant functors

  The book defines `Aᵒᵖ` by keeping the same elements but swapping source/target
  and reversing composition: `x ∘ y` in `Aᵒᵖ` is `y ∘ x` in `A`.
  The identity function `A → Aᵒᵖ` is a contravariant isomorphism.

  `ContraFunctor` (§1.182 proper) is defined in S1_81.lean; it imports S1_18.
  We define `OppCat` here since it is a §1.182 concept. -/

/-- **§1.182**: The OPPOSITE CATEGORY `OppCat 𝒞` has the same objects as `𝒞`
    but reversed morphisms: `X ⟶ Y` in `OppCat 𝒞` means `Y ⟶ X` in `𝒞`,
    and composition is reversed (`x ∘ y` becomes `y ∘ x`). -/
@[expose] public def OppCat (C : Type u) := C

@[expose] public instance oppCatInst (C : Type u) [cat : Cat.{v} C] : Cat.{v} (OppCat C) where
  Hom X Y := cat.Hom Y X
  id X    := cat.id X
  comp f g := cat.comp g f
  id_comp f := cat.comp_id f
  comp_id f := cat.id_comp f
  assoc f g h := (cat.assoc h g f).symm

/-- The canonical coercion: every object of `C` is trivially an object of `OppCat C`. -/
abbrev toOpp {C : Type u} (X : C) : OppCat C := X

/-- The canonical coercion back: every object of `OppCat C` is an object of `C`. -/
abbrev fromOpp {C : Type u} (X : OppCat C) : C := X

/-- **§1.182**: The identity function `OppCat (OppCat C) = C` — taking the opposite twice
    recovers the original category (`Aᵒᵒ = A`). -/
theorem oppOpp_eq (C : Type u) [Cat.{v} C] : OppCat (OppCat C) = C := rfl

/-! ## §1.19  Identity morphisms and the induced map

  `|A|` in the book denotes the set of identity morphisms of `A`.
  We represent this as the subtype `IdMorphs 𝒞 := { p : Σ X : 𝒞, X ⟶ X // p.2 = Cat.id p.1 }`,
  or more directly as just `𝒞` itself (each object has a unique identity morphism).
  The cleanest encoding: `IdMorphs 𝒞` is the type of pairs `(X, id_X)`. -/

/-- **§1.19**: The SET OF IDENTITY MORPHISMS of `𝒞`, written `|𝒞|` in the book.
    Each element is a pair of an object `X` and its identity morphism `id_X`. -/
def IdMorphs (C : Type u) [Cat.{v} C] := C

/-- **§1.19**: A functor `F : 𝒞 → 𝒟` induces a function `|𝒞| → |𝒟|`
    by sending each identity `id_X` to the identity `id_{FX}`. -/
def functor_on_idMorphs {C : Type u₁} [Cat.{v} C] {D : Type u₂} [Cat.{v} D]
    (F : Functor C D) : IdMorphs C → IdMorphs D := F.obj
