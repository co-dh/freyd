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
  map_id : ∀ (a b : 𝒜), map (𝟙 a) (𝟙 b) = 𝟙 (obj a b)
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
@[expose, reducible] public def appl (a : 𝒜) : Relator 𝒜 𝒜 where
  obj b := F.obj a b
  map S := F.map (𝟙 a) S
  map_id b := F.map_id a b
  map_comp S S' := by rw [← F.map_comp, Cat.id_comp]
  map_mono h := F.map_mono (le_refl _) h

/-- The other partial application `F(−,b)`, fixing the recursive position. -/
@[expose, reducible] public def appr (b : 𝒜) : Relator 𝒜 𝒜 where
  obj a := F.obj a b
  map R := F.map R (𝟙 b)
  map_id a := F.map_id a b
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

end BiRelator

/-! ## The type functor `T` of an initial type `(α,T)`

  `F` is a binary relator whose partial applications `F(A,−)` all have initial algebras
  `α_A : F(A,TA) ⟶ TA` in the maps — B&dM's "initial type `(α,T)` defined by the bifunctor
  `F`" (§2.7 p. 51), carried as the family `I : ∀ a, InitialAlgebra (F.appl a)` with
  `TA = (I A).t`, `α_A = (I A).α`.  Every law below is one application of the
  Eilenberg-Wright UP `relCata_UP` (5.12) or of the equality fusion (2.12). -/

variable {𝒜 : Type u} [UnguardedPowerAllegory 𝒜] {F : BiRelator 𝒜}
  (I : ∀ a : 𝒜, InitialAlgebra (F.appl a))

/-- **(2.13) / B&dM p. 122**: `T` acts on an arrow `R : A ⟶ B` by `T(R) = ⦇F(R,𝟙)α⦈ : TA ⟶ TB`
    — rebuild the structure with `α`, applying `R` to the parameter on the way. -/
@[expose] public def typeMap {a b : 𝒜} (R : a ⟶ b) : (I a).t ⟶ (I b).t :=
  relCata (I := I a) (F.map R (𝟙 (I b).t) ≫ (I b).α)

/-- The defining equation (2.13), unfolded — `T(R) = ⦇F(R,𝟙)α⦈` as a citable statement. -/
public theorem typeMap_defn {a b : 𝒜} (R : a ⟶ b) :
    typeMap I R = relCata (I := I a) (F.map R (𝟙 (I b).t) ≫ (I b).α) := rfl

/-- **§2.7**: `T(𝟙) = 𝟙` — "bifunctors preserve identities; reflection law". -/
public theorem typeMap_id (a : 𝒜) : typeMap I (𝟙 a) = 𝟙 (I a).t := by
  rw [typeMap_defn I (𝟙 a)]
  refine ((relCata_UP (I a) _ _).mp ?_).symm
  dsimp only [BiRelator.appl]
  rw [Cat.comp_id, F.map_id, Cat.id_comp, Cat.id_comp]

/-- **Type functor fusion (2.14)**: `T(R)⦇Q⦈ = ⦇F(R,𝟙)Q⦈` — "a catamorphism composed with
    its type functor can always be expressed as a single catamorphism."  The side condition
    of (2.12)-fusion is discharged by interchange, `F` being a bifunctor. -/
public theorem typeMap_fusion {a b c : 𝒜} (R : a ⟶ b) (Q : F.obj b c ⟶ c) :
    typeMap I R ≫ relCata (I := I b) Q = relCata (I := I a) (F.map R (𝟙 c) ≫ Q) := by
  rw [typeMap_defn I R]
  refine relCata_fusion (I a) ?_
  rw [Cat.assoc, relCata_cancel (I b) Q]
  dsimp only [BiRelator.appl]
  rw [← Cat.assoc, F.interchange, ← F.interchange' R (relCata (I := I b) Q), Cat.assoc]

/-- **§2.7**: `T(R)T(S) = T(RS)` — type functor fusion at `Q := F(S,𝟙)α`, then `F` bifunctor. -/
public theorem typeMap_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    typeMap I R ≫ typeMap I S = typeMap I (R ≫ S) := by
  rw [typeMap_defn I S, typeMap_fusion I R, typeMap_defn I (R ≫ S), ← Cat.assoc,
    ← F.map_comp, Cat.comp_id]

/-- **§2.7 p. 51**: `αT(R) = F(R,T(R))α` — "`α` is a natural transformation from
    `G(R) = F(R,T(R))` to `T`": building and then mapping is mapping the parts and then
    building.  The cancellation `α⦇·⦈ = F(⦇·⦈)·` (5.12) plus interchange. -/
public theorem alpha_natural {a b : 𝒜} (R : a ⟶ b) :
    (I a).α ≫ typeMap I R = F.map R (typeMap I R) ≫ (I b).α := by
  rw [typeMap_defn I R, relCata_cancel (I a)]
  dsimp only [BiRelator.appl]
  rw [← Cat.assoc, F.interchange']

/-- **B&dM p. 122 (type relators)**: `T(R)° = T(R°)` — a datatype acts on relations, and the
    map of the converse is the converse of the map.  Needs `F` converse-preserving; the
    book's chain (converse the naturality square, cancel the invertible `α` on both sides)
    with Lambek's `α°≫α = 𝟙`, `α≫α° = 𝟙` from `AOP.A6_2`. -/
public theorem typeMap_recip (hF : F.PreservesRecip) {a b : 𝒜} (R : a ⟶ b) :
    (typeMap I R)° = typeMap I R° := by
  have hrec : (typeMap I R)° ≫ (I a).α° = (I b).α° ≫ (F.map R (typeMap I R))° := by
    rw [← Allegory.recip_comp, ← Allegory.recip_comp, alpha_natural I R]
  rw [typeMap_defn I R°]
  refine (relCata_UP (I b) _ _).mp ?_
  dsimp only [BiRelator.appl]
  calc (I b).α ≫ (typeMap I R)°
      = (I b).α ≫ ((typeMap I R)° ≫ (I a).α°) ≫ (I a).α := by
        rw [Cat.assoc, (I a).recip_alpha_alpha, Cat.comp_id]
    _ = ((I b).α ≫ (I b).α°) ≫ (F.map R (typeMap I R))° ≫ (I a).α := by
        rw [hrec, Cat.assoc, Cat.assoc]
    _ = F.map R° (typeMap I R)° ≫ (I a).α := by
        rw [(I b).alpha_alpha_recip, Cat.id_comp, ← hF R (typeMap I R)]
    _ = F.map (𝟙 b) (typeMap I R)° ≫ F.map R° (𝟙 (I a).t) ≫ (I a).α := by
        rw [← Cat.assoc, F.interchange']

/-! ## The type relator, bundled

  Monotonicity of `T` cannot follow from the equational UP alone: the book gets it from
  "sufficient to preserve converse", i.e. Theorem 5.1(b) over a tabular source, dropped in
  `A5_1`.  Here it comes from the least-fixed-point reading of `⦇·⦈` (`relCata_mono`), so
  the bundle lives in the locally complete setting `UnguardedPowerLCDA`. -/

section TypeRelator

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : BiRelator 𝒜}
  (I : ∀ a : 𝒜, InitialAlgebra (F.appl a))

/-- `T` is MONOTONIC: `⦇·⦈` is monotonic in the algebra (Ex 6.7) and `F` in its arguments. -/
public theorem typeMap_mono {a b : 𝒜} {R S : a ⟶ b} (h : R ⊑ S) :
    typeMap I R ⊑ typeMap I S := by
  rw [typeMap_defn I R, typeMap_defn I S]
  exact relCata_mono (I a) (comp_mono_right (F.map_mono h (le_refl _)) (I b).α)

/-- **B&dM §5.5 p. 122**: the TYPE RELATOR — the type functor `T` of the initial type
    `(α,T)` of a binary relator `F`, bundled as a relator: `A ↦ TA`, `R ↦ ⦇F(R,𝟙)α⦈`. -/
@[expose] public def typeRelator : Relator 𝒜 𝒜 where
  obj a := (I a).t
  map := typeMap I
  map_id := typeMap_id I
  map_comp R S := (typeMap_comp I R S).symm
  map_mono := typeMap_mono I

end TypeRelator

end Freyd.Alg
