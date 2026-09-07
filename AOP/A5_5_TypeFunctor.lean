/-
  Bird & de Moor, *Algebra of Programming* §2.7 Type functors (pp. 49-52) and
  §5.5 Relational catamorphisms, "Type relators" (p. 122).

  §2.7: a BIFUNCTOR `F` with initial algebras `α_A : TA ← F(A,TA)` for every `A` makes the
  construction `T` a functor via `T(f) = ⦇F(f,𝟙)α⦈` (2.13, mirrored to diagram order); the book
  proves `T(𝟙)=𝟙`, `T(f)T(g)=T(fg)`, type functor fusion `T(f)⦇h⦈=⦇F(f,𝟙)h⦈` (2.14), and that
  `α` is natural from `G(f)=F(f,T(f))` to `T`.  "We will say that `(α,T)` is the initial type
  defined by the bifunctor `F`."

  §5.5 p. 122: "Let `F` be a binary relator with initial type `(α,T)`, so `T` is a type
  functor. To show that `T` is a relator, it is sufficient to prove that it preserves
  converse: `T(R)° = T(R°)`."  All five laws are proved here for RELATIONS `R`, over an
  arbitrary unguarded power allegory, from the Eilenberg-Wright UP `relCata_UP` (5.12).

  Hypothesis split (each law at its weakest setting):
  - defining equation, functor laws, fusion, naturality of `α`: `UnguardedPowerAllegory`.
  - `T(R)°=T(R°)`: + `F` preserves converse (`BiRelator.PreservesRecip`; automatic over a
    tabular source, as in the unary Theorem 5.1(a)).
  - the bundled `typeRelator`: `UnguardedPowerLCDA`.  This repo's `Relator` is a MONOTONE
    functor, so the bundle's extra obligation is monotonicity, not converse: the book's
    "sufficient to preserve converse" is Theorem 5.1(b), dropped in `A5_1` (see the blocker
    there), and monotonicity comes instead from the least-fixed-point reading of `⦇·⦈`
    (`relCata_mono`, ch. 6) — hence this A5 file imports `AOP.A6_2` (Lambek + `relCata_mono`).
-/
module

public import AOP.A6_2
-- §5.7's `StrictNatural` and `Relator.pair`: `α`'s square is a NATURALITY statement, and saying so
-- needs the 2-cell vocabulary.  The file already reaches forward to ch. 6 for `relCata_mono`.
public import AOP.A5_7

universe v u

namespace Freyd.Alg

/-! ## Binary relators

  B&dM §2.7 p. 50: "we think of `F` as a bifunctor.  We will always arrange the arguments of
  a bifunctor so that the functor obtained by fixing the first argument (and varying the
  second) is the one that describes the initial algebra."  A binary RELATOR is the §5.1
  notion in two arguments: functorial and monotonic in the pair — equivalently a relator out
  of the product allegory `𝒜 × 𝒜`, stated componentwise.  The pair-form `map_id`/`map_comp`
  give both partial functoriality and the interchange `F(R,𝟙)F(𝟙,S) = F(R,S) = F(𝟙,S)F(R,𝟙)`,
  the side condition of type functor fusion. -/

/-- A BINARY RELATOR: a monotonic bifunctor on an allegory (B&dM §5.1 in two arguments). -/
public structure BiRelator (𝒜 : Type u) [Allegory.{v} 𝒜] where
  obj : 𝒜 → 𝒜 → 𝒜
  map : {a₁ a₂ b₁ b₂ : 𝒜} → (a₁ ⟶ a₂) → (b₁ ⟶ b₂) → (obj a₁ b₁ ⟶ obj a₂ b₂)
  map_id : ∀ (A B : 𝒜), map (𝟙 A) (𝟙 B) = 𝟙 (obj A B)
  map_comp : ∀ {a₁ a₂ a₃ b₁ b₂ b₃ : 𝒜} (R : a₁ ⟶ a₂) (R' : a₂ ⟶ a₃) (S : b₁ ⟶ b₂)
    (S' : b₂ ⟶ b₃), map (R ≫ R') (S ≫ S') = map R S ≫ map R' S'
  map_mono : ∀ {a₁ a₂ b₁ b₂ : 𝒜} {R R' : a₁ ⟶ a₂} {S S' : b₁ ⟶ b₂},
    R ⊑ R' → S ⊑ S' → map R S ⊑ map R' S'

namespace BiRelator

variable {𝒜 : Type u} [Allegory.{v} 𝒜] (F : BiRelator 𝒜)

/-- INTERCHANGE, `F(R,𝟙)F(𝟙,S) = F(R,S)`: both are `F` of the pair `(R,S)`, split into the
    two partial actions.  "The side condition holds because `F` is a bifunctor." -/
public theorem interchange {a₁ a₂ b₁ b₂ : 𝒜} (R : a₁ ⟶ a₂) (S : b₁ ⟶ b₂) :
    F.map R (𝟙 b₁) ≫ F.map (𝟙 a₂) S = F.map R S := by
  rw [← F.map_comp, Cat.comp_id, Cat.id_comp]

/-- INTERCHANGE, the other split: `F(𝟙,S)F(R,𝟙) = F(R,S)`. -/
public theorem interchange' {a₁ a₂ b₁ b₂ : 𝒜} (R : a₁ ⟶ a₂) (S : b₁ ⟶ b₂) :
    F.map (𝟙 a₁) S ≫ F.map R (𝟙 b₂) = F.map R S := by
  rw [← F.map_comp, Cat.comp_id, Cat.id_comp]

/-- The partial application `F(a,−)`, a unary relator — "the functor obtained by fixing the
    first argument ... is the one that describes the initial algebra" (§2.7 p. 50); the note
    abbreviates its action as `F(X) ≜ F(𝟙,X)`.  Reducible so that `rw` against the unary
    `relCata` lemmas (stated at `F.appl a`) matches goals spelled with `F.obj`/`F.map`. -/
@[expose, reducible] public def appl (A : 𝒜) : Relator 𝒜 𝒜 where
  obj B := F.obj A B
  map S := F.map (𝟙 A) S
  map_id B := F.map_id A B
  map_comp S S' := by rw [← F.map_comp, Cat.id_comp]
  map_mono h := F.map_mono (le_refl _) h

/-- The other partial application `F(−,b)`, fixing the recursive position. -/
@[expose, reducible] public def appr (B : 𝒜) : Relator 𝒜 𝒜 where
  obj A := F.obj A B
  map R := F.map R (𝟙 B)
  map_id A := F.map_id A B
  map_comp R R' := by rw [← F.map_comp, Cat.id_comp]
  map_mono h := F.map_mono h (le_refl _)

/-- `F(R°,S°) = F(R,S)°`, the binary form of `Relator.PreservesRecip`.  Carried as a
    hypothesis on the one law that needs it (`typeMap_recip`); automatic over a tabular
    source (below). -/
@[expose] public def PreservesRecip : Prop :=
  ∀ {a₁ a₂ b₁ b₂ : 𝒜} (R : a₁ ⟶ a₂) (S : b₁ ⟶ b₂), F.map R° S° = (F.map R S)°

/-- **Theorem 5.1(a), binary form** (B&dM p. 112): over a tabular source every binary
    relator preserves converse — the unary theorem applied to each partial application,
    glued by interchange. -/
public theorem preservesRecip_of_tabular {𝒜 : Type u} [TabularAllegory 𝒜]
    (F : BiRelator 𝒜) : F.PreservesRecip := by
  intro a₁ a₂ b₁ b₂ R S
  have h1 : F.map R° (𝟙 b₂) = (F.map R (𝟙 b₂))° :=
    Relator.preservesRecip_of_tabular (F.appr b₂) R
  have h2 : F.map (𝟙 a₁) S° = (F.map (𝟙 a₁) S)° :=
    Relator.preservesRecip_of_tabular (F.appl a₁) S
  rw [← F.interchange R° S°, h1, h2, ← Allegory.recip_comp, F.interchange']

/-- `F` AS A UNARY RELATOR out of the PRODUCT allegory: `(a,b) ↦ F.obj a b`, `(R,S) ↦ F.map R S`.
    B&dM's bifunctor "arranged so that fixing the first argument describes the initial algebra" is
    a relator `𝒜×𝒜 ⟶ 𝒜` once its two arguments are packed, and that is the only form in which it
    is a single functor of one variable — which is what an argument that itself varies with the
    parameter (`F(R,T(R))`) needs before it can be read as one thing applied to one arrow. -/
@[expose] public def toRelator : Relator (𝒜 × 𝒜) 𝒜 where
  obj p := F.obj p.1 p.2
  map R := F.map R.1 R.2
  map_id p := F.map_id p.1 p.2
  map_comp R S := F.map_comp R.1 S.1 R.2 S.2
  map_mono h := F.map_mono (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- The two spellings of one arrow: `F(R,S)` is the unary relator at the pair `(R,S)`.  Packing the
    arguments is a change of notation and nothing else — both sides are `F.map R S`. -/
public theorem map_eq_toRelator {a₁ a₂ b₁ b₂ : 𝒜} (R : a₁ ⟶ a₂) (S : b₁ ⟶ b₂) :
    F.map R S = F.toRelator.map ((R, S) : ((a₁, b₁) : 𝒜 × 𝒜) ⟶ (a₂, b₂)) := rfl

end BiRelator

/-! ## The type functor `T` of an initial type `(α,T)`

  `F` is a binary relator whose partial applications `F(A,−)` all have initial algebras
  `α_A : F(A,TA) ⟶ TA` in the maps — B&dM's "initial type `(α,T)` defined by the bifunctor
  `F`" (§2.7 p. 51), carried as the family `I : ∀ a, InitialAlgebra (F.appl a)` with
  `TA = (I A).t`, `α_A = (I A).α`.  Every law below is one application of the
  Eilenberg-Wright UP `relCata_UP` (5.12) or of the equality fusion (2.12). -/

variable {𝒜 : Type u} [UnguardedPowerAllegory 𝒜] {F : BiRelator 𝒜}
  (I : ∀ A : 𝒜, InitialAlgebra (F.appl A))

/-- **(2.13) / B&dM p. 122**: `T` acts on an arrow `R : A ⟶ B` by `T(R) = ⦇F(R,𝟙)α⦈ : TA ⟶ TB`
    — rebuild the structure with `α`, applying `R` to the parameter on the way. -/
@[expose] public def typeMap {A B : 𝒜} (R : A ⟶ B) : (I A).t ⟶ (I B).t :=
  relCata (I := I A) (F.map R (𝟙 (I B).t) ≫ (I B).α)

/-- The defining equation (2.13), unfolded — `T(R) = ⦇F(R,𝟙)α⦈` as a citable statement. -/
public theorem typeMap_defn {A B : 𝒜} (R : A ⟶ B) :
    typeMap I R = relCata (I := I A) (F.map R (𝟙 (I B).t) ≫ (I B).α) := rfl

/-- **§2.7**: `T(𝟙) = 𝟙` — "bifunctors preserve identities; reflection law". -/
public theorem typeMap_id (A : 𝒜) : typeMap I (𝟙 A) = 𝟙 (I A).t := by
  rw [typeMap_defn I (𝟙 A)]
  refine ((relCata_UP (I A) _ _).mp ?_).symm
  dsimp only [BiRelator.appl]
  rw [Cat.comp_id, F.map_id, Cat.id_comp, Cat.id_comp]

/-- **Type functor fusion (2.14)**: `T(R)⦇Q⦈ = ⦇F(R,𝟙)Q⦈` — "a catamorphism composed with
    its type functor can always be expressed as a single catamorphism."  The side condition
    of (2.12)-fusion is discharged by interchange, `F` being a bifunctor. -/
public theorem typeMap_fusion {A B C : 𝒜} (f : A ⟶ B) (h : F.obj B C ⟶ C) :
    typeMap I f ≫ relCata (I := I B) h = relCata (I := I A) (F.map f (𝟙 C) ≫ h) := by
  rw [typeMap_defn I f]
  refine relCata_fusion (I A) ?_
  rw [Cat.assoc, relCata_cancel (I B) h]
  dsimp only [BiRelator.appl]
  rw [← Cat.assoc, F.interchange, ← F.interchange' f (relCata (I := I B) h), Cat.assoc]

/-- **§2.7**: `T(R)T(S) = T(RS)` — type functor fusion at `Q := F(S,𝟙)α`, then `F` bifunctor. -/
public theorem typeMap_comp {A B C : 𝒜} (R : A ⟶ B) (S : B ⟶ C) :
    typeMap I R ≫ typeMap I S = typeMap I (R ≫ S) := by
  rw [typeMap_defn I S, typeMap_fusion I R, typeMap_defn I (R ≫ S), ← Cat.assoc,
    ← F.map_comp, Cat.comp_id]

/-- **§2.7 p. 51**: the initial algebras as one FAMILY in the parameter — `αᴀ : F(A,TA) ⟶ TA`,
    the note's `α : F(⟨𝟙,T⟩(A))⟶T(A)`, whose square in `A` is `alpha_natural` below.  Not the
    single arrow `α : F(T)⟶T` of one initial algebra (@cata-defn): the same letter, indexed. -/
@[expose] public def alphaT (A : 𝒜) : F.obj A (I A).t ⟶ (I A).t := (I A).α

/-- **§2.7 p. 51**: `αT(R) = F(R,T(R))α` — "`α` is a natural transformation from
    `G(R) = F(R,T(R))` to `T`": building and then mapping is mapping the parts and then
    building.  The cancellation `α⦇·⦈ = F(⦇·⦈)·` (5.12) plus interchange. -/
public theorem alpha_natural {A B : 𝒜} (R : A ⟶ B) :
    alphaT I A ≫ typeMap I R = F.map R (typeMap I R) ≫ alphaT I B := by
  show (I A).α ≫ typeMap I R = F.map R (typeMap I R) ≫ (I B).α
  rw [typeMap_defn I R, relCata_cancel (I A)]
  dsimp only [BiRelator.appl]
  rw [← Cat.assoc, F.interchange']

/-- **B&dM p. 122 (type relators)**: `T(R)° = T(R°)` — a datatype acts on relations, and the
    map of the converse is the converse of the map.  Needs `F` converse-preserving; the
    book's chain (converse the naturality square, cancel the invertible `α` on both sides)
    with Lambek's `α°≫α = 𝟙`, `α≫α° = 𝟙` from `AOP.A6_2`. -/
public theorem typeMap_recip (hF : F.PreservesRecip) {A B : 𝒜} (R : A ⟶ B) :
    (typeMap I R)° = typeMap I R° := by
  have hrec : (typeMap I R)° ≫ (I A).α° = (I B).α° ≫ (F.map R (typeMap I R))° := by
    rw [← Allegory.recip_comp, ← Allegory.recip_comp,
      show (I A).α ≫ typeMap I R = F.map R (typeMap I R) ≫ (I B).α from alpha_natural I R]
  rw [typeMap_defn I R°]
  refine (relCata_UP (I B) _ _).mp ?_
  dsimp only [BiRelator.appl]
  calc (I B).α ≫ (typeMap I R)°
      = (I B).α ≫ ((typeMap I R)° ≫ (I A).α°) ≫ (I A).α := by
        rw [Cat.assoc, (I A).recip_alpha_alpha, Cat.comp_id]
    _ = ((I B).α ≫ (I B).α°) ≫ (F.map R (typeMap I R))° ≫ (I A).α := by
        rw [hrec, Cat.assoc, Cat.assoc]
    _ = F.map R° (typeMap I R)° ≫ (I A).α := by
        rw [(I B).alpha_alpha_recip, Cat.id_comp, ← hF R (typeMap I R)]
    _ = F.map (𝟙 B) (typeMap I R)° ≫ F.map R° (𝟙 (I A).t) ≫ (I A).α := by
        rw [← Cat.assoc, F.interchange']

/-! ## The type relator, bundled

  Monotonicity of `T` cannot follow from the equational UP alone: the book gets it from
  "sufficient to preserve converse", i.e. Theorem 5.1(b) over a tabular source, dropped in
  `A5_1`.  Here it comes from the least-fixed-point reading of `⦇·⦈` (`relCata_mono`), so
  the bundle lives in the locally complete setting `UnguardedPowerLCDA`. -/

section TypeRelator

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : BiRelator 𝒜}
  (I : ∀ A : 𝒜, InitialAlgebra (F.appl A))

/-- `T` is MONOTONIC: `⦇·⦈` is monotonic in the algebra (Ex 6.7) and `F` in its arguments. -/
public theorem typeMap_mono {A B : 𝒜} {R S : A ⟶ B} (h : R ⊑ S) :
    typeMap I R ⊑ typeMap I S := by
  rw [typeMap_defn I R, typeMap_defn I S]
  exact relCata_mono (I A) (comp_mono_right (F.map_mono h (le_refl _)) (I B).α)

/-- **B&dM §5.5 p. 122**: the TYPE RELATOR — the type functor `T` of the initial type
    `(α,T)` of a binary relator `F`, bundled as a relator: `A ↦ TA`, `R ↦ ⦇F(R,𝟙)α⦈`. -/
@[expose] public def typeRelator : Relator 𝒜 𝒜 where
  obj A := (I A).t
  map := typeMap I
  map_id := typeMap_id I
  map_comp R S := (typeMap_comp I R S).symm
  map_mono := typeMap_mono I

/-- **§2.7 p. 51 as a 2-CELL**: `α` is STRICTLY NATURAL from `F∘⟨𝟙,T⟩` to `T`.  Same square as
    `alpha_natural`, with both sides spelled as relators of `𝒜`: `F(R,T(R))` is `F` applied to the
    pairing `⟨𝟙,T⟩` at the one arrow `R`, so the source is a relator and not a family of objects,
    which is what makes the square a naturality statement rather than an equation per `A`. -/
public theorem alphaT_strictNatural :
    StrictNatural (typeRelator I)
      (Relator.comp (Relator.pair (Relator.idRelator 𝒜) (typeRelator I)) F.toRelator)
      (alphaT I) :=
  fun R => (alpha_natural I R).symm

end TypeRelator

-- printing-only unexpanders: the note's spelling.  `α` bare and `T` applied to the arrow it maps:
-- §2.7's own `α : F(⟨𝟙,T⟩)⟶T` and `T(R)`.  The family argument `I` is not part of either name — it
-- is which initial algebras, not which component — and neither is the OBJECT `α` is taken at: on a
-- string diagram that object is the wire the bead sits over, and writing it in the label as well
-- spells it twice.
open Lean PrettyPrinter in
@[app_unexpander alphaT] public meta def unexpandAlphaT : Unexpander
  | `($_ $_ $_) => `($(mkIdent `α))
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander typeMap] public meta def unexpandTypeMap : Unexpander
  | `($_ $_ $R) => `($(mkIdent `T) $R)
  | _ => throw ()

-- A bifunctor prints on its second argument only, as the endofunctor `F(A,−)` it is at a fixed
-- parameter: juxtaposing both, `F R (T R)`, reads as a composite under the book's convention.
open Lean PrettyPrinter in
@[app_unexpander BiRelator.obj] public meta def unexpandBiRelatorObj : Unexpander
  | `($_ $F $_ $b) => `($F $b)
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander BiRelator.map] public meta def unexpandBiRelatorMap : Unexpander
  | `($_ $F $_ $S) => `($F $S)
  | _ => throw ()

/-! ## §3.2  Ruby triangles and Horner's rule

  B&dM §3.2 pp. 58-59, mirrored to diagram order.  For `f : A ⟶ A` the RUBY TRIANGLE
  `tri(f) : TA ⟶ TA` applies `f` one more time at each level of the structure — on cons-lists
  `tri(f)[a₀,a₁,…,aᵢ,…,aₙ] = [a₀,f(a₁),…,fⁱ(aᵢ),…,fⁿ(aₙ)]`, the book's four stages ending at
  `tri(f) = ⦇F(𝟙,T(f))α⦈` for an arbitrary initial type `(α,T)`.  Horner's rule fuses the
  triangle into the fold that follows it, and its whole side condition is the one distribution
  law `gf = F(f,f)g`. -/

/-- **B&dM §3.2 p. 59**: the RUBY TRIANGLE `tri(f) = ⦇F(𝟙,T(f))α⦈ : TA ⟶ TA` — rebuild the
    structure with `α`, mapping `f` over the substructure already built, so what sits `i` levels
    down comes out under `fⁱ`. -/
@[expose] public def tri {A : 𝒜} (f : A ⟶ A) : (I A).t ⟶ (I A).t :=
  relCata (I := I A) (F.map (𝟙 A) (typeMap I f) ≫ alphaT I A)

/-- The defining equation, unfolded — `tri(f) = ⦇F(𝟙,T(f))α⦈` as a citable statement. -/
public theorem tri_defn {A : 𝒜} (f : A ⟶ A) :
    tri I f = relCata (I := I A) (F.map (𝟙 A) (typeMap I f) ≫ alphaT I A) := rfl

/-- Under `gf = F(f,f)g` the two ways of pushing `f` through a fold agree: `T(f)⦇g⦈ = ⦇g⦈f` —
    mapping `f` over the structure and then folding is folding and then applying `f` once.  Type
    functor fusion turns the left side into `⦇F(f,𝟙)g⦈`, and (2.12)-fusion turns the right side
    into the same fold, its side condition being exactly the hypothesis after interchange. -/
public theorem typeMap_comp_relCata {A : 𝒜} {f : A ⟶ A} {g : F.obj A A ⟶ A}
    (h : g ≫ f = F.map f f ≫ g) :
    typeMap I f ≫ relCata (I := I A) g = relCata (I := I A) g ≫ f := by
  rw [typeMap_fusion I f g]
  refine (relCata_fusion (I A) ?_).symm
  show g ≫ f = F.map (𝟙 A) f ≫ (F.map f (𝟙 A) ≫ g)
  rw [← Cat.assoc, F.interchange' f f]
  exact h

/-- **HORNER'S RULE (B&dM §3.2, pp. 58-59)**: `tri(f)⦇g⦈ = ⦇F(𝟙,f)g⦈ ⟸ gf = F(f,f)g` — a
    triangle followed by a fold is a single fold, whose algebra applies `f` to the parameter
    before `g`.  For cons-lists and `g = plus`, `f = (×x)` this is the schoolbook way of
    evaluating a polynomial, which is why the book calls it Horner's rule.  One (2.12)-fusion,
    whose side condition reduces by `α⦇g⦈ = F(𝟙,⦇g⦈)g` and `typeMap_comp_relCata` to the
    hypothesis. -/
public theorem tri_cata_fusion {A : 𝒜} {f : A ⟶ A} {g : F.obj A A ⟶ A}
    (h : g ≫ f = F.map f f ≫ g) :
    tri I f ≫ relCata (I := I A) g = relCata (I := I A) (F.map (𝟙 A) f ≫ g) := by
  rw [tri_defn I f]
  refine relCata_fusion (I A) ?_
  show (F.map (𝟙 A) (typeMap I f) ≫ (I A).α) ≫ relCata (I := I A) g
      = F.map (𝟙 A) (relCata (I := I A) g) ≫ (F.map (𝟙 A) f ≫ g)
  calc (F.map (𝟙 A) (typeMap I f) ≫ (I A).α) ≫ relCata (I := I A) g
      = F.map (𝟙 A) (typeMap I f) ≫ ((I A).α ≫ relCata (I := I A) g) := Cat.assoc _ _ _
    _ = F.map (𝟙 A) (typeMap I f) ≫ (F.map (𝟙 A) (relCata (I := I A) g) ≫ g) := by
          rw [relCata_cancel (I A) g]
    _ = (F.map (𝟙 A) (typeMap I f) ≫ F.map (𝟙 A) (relCata (I := I A) g)) ≫ g :=
          (Cat.assoc _ _ _).symm
    _ = F.map (𝟙 A) (typeMap I f ≫ relCata (I := I A) g) ≫ g := by
          rw [← F.map_comp, Cat.id_comp]
    _ = F.map (𝟙 A) (relCata (I := I A) g ≫ f) ≫ g := by rw [typeMap_comp_relCata I h]
    _ = (F.map (𝟙 A) (relCata (I := I A) g) ≫ F.map (𝟙 A) f) ≫ g := by
          rw [← F.map_comp, Cat.id_comp]
    _ = F.map (𝟙 A) (relCata (I := I A) g) ≫ (F.map (𝟙 A) f ≫ g) := Cat.assoc _ _ _

end Freyd.Alg
