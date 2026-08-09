/-
  Freyd & Scedrov, *Categories and Allegories* — §2.16(14): the effective reflection
  of `Rel(A)` for the category **A** of assemblies.

  Book text: "Let A be the category of assemblies [2.153].  The effective reflection E
  of Rel(A) may be described as follows.  The objects are pairs ⟨A, I⟩ (we will write
  A/I to suggest the formal quotient), where A is an assembly and I : A → A in Rel(A)
  is an equivalence relation.  A relation R : A → B in Rel(A) is considered a morphism
  from A/I to B/J in E iff IR = R = RJ in Rel(A).  Every assembly A may be considered
  as an object A/1_A in E."

  Formalized as the INSTANTIATION `E = Spl(Eq (Rel(Assembly K)))` of the generic
  reflexive splitting completion `SplEqObj` (§2.433, S2_433_SplEqInstance2):

  •  `splHom_fixed_iff_book` / `splEq_hom_iff` — the repo's sandwich hom-condition
     `eRf = R` (§2.164) is EXACTLY the book's two-sided `IR = R = RJ`.
  •  `AsmRel K` / `AsmEffReflection K` — `Rel(A)` and its effective reflection `E`.
  •  `asmQuot` — the book's object `⟨A, I⟩ = A/I` from an equivalence relation `I`
     (reflexive, symmetric, transitive), and `asmEffReflection_obj_form` — every
     object of `E` is such a pair.
  •  `asmRel_hom_iff` — the book's morphism description of `E`.
  •  `asmEmbed`/`asmEmbedHom` (full `asmEmbed_full`, faithful `asmEmbed_faithful`,
     `asmEmbedHom_map_iff`) — "every assembly A may be considered as an object
     A/1_A in E", at the relation level (re-exports of the §2.433 `embEq` embedding).
  •  `asmEmbedMap` — an assembly MORPHISM `f : A → B`, via its graph, is a MAP
     `A/1_A → B/1_B` of `E`, functorially (`asmEmbedMap_id`/`asmEmbedMap_comp`) and
     faithfully (`asmEmbedMap_faithful`).
  •  `asmEffReflection_eqSplits` — `E` is EFFECTIVE: every equivalence relation of
     `E` splits with a map leg (§2.433 `splEq_hsplit`, instantiated).

  NOT formalized (out of scope): the universal property making `E` the reflection of
  `Rel(A)` into effective allegories (needs allegory-functor factorization machinery),
  and the book's closing remark that `E` is also the splitting of all symmetric
  idempotents of the full subcategory of set-like assemblies (all caucuses equal), of
  which `Rel(A)` itself is the coreflexive splitting.

  Conventions: diagram-order composition `R ≫ S`, reciprocation `R°`, intersection
  `R ∩ S`, order `R ⊑ S`.  Mathlib-free.
-/
module

public import Freyd.S2_16c
public import Freyd.S2_153_Assemblies
public import Freyd.S2_111_RelCat

universe v u

namespace Freyd.Alg

open Cat

/-! ## The book's hom description `IR = R = RJ` (§2.16(14))

  The repo's splitting completion (§2.164, `SplHom`) types a hom `(a,e) ⟶ (b,f)` by
  the sandwich condition `e ≫ R ≫ f = R`; the book's §2.16(14) description uses the
  two one-sided equations `IR = R = RJ`.  They are equivalent for ANY symmetric
  idempotents (`fixed_left`/`fixed_right` one way; `e(Rf) = eR = R` the other). -/

section BookHom
variable {𝒜 : Type u} [Allegory 𝒜]

/-- The §2.164 sandwich condition `e ≫ R ≫ f = R` is equivalent to the book's
    §2.16(14) two-sided condition `e ≫ R = R ∧ R ≫ f = R` (`IR = R = RJ`). -/
theorem splHom_fixed_iff_book {E F : SplObj 𝒜} (R : E.carrier ⟶ F.carrier) :
    E.idem.e ≫ R ≫ F.idem.e = R ↔ (E.idem.e ≫ R = R ∧ R ≫ F.idem.e = R) := by
  constructor
  · intro h
    exact ⟨(SplHom.mk R h).fixed_left, (SplHom.mk R h).fixed_right⟩
  · rintro ⟨h₁, h₂⟩
    rw [h₂, h₁]

/-- **§2.16(14) hom description, generic form**: a morphism `R : a ⟶ b` of `𝒜`
    underlies a hom `(a,e) ⟶ (b,f)` of `Spl(Eq 𝒜)` iff `e ≫ R = R = R ≫ f` — the
    book's "`R` is considered a morphism from `A/I` to `B/J` in `E` iff `IR = R = RJ`". -/
theorem splEq_hom_iff {E F : SplEqObj 𝒜} (R : E.1.carrier ⟶ F.1.carrier) :
    (∃ Φ : E ⟶ F, Φ.R = R) ↔ (E.1.idem.e ≫ R = R ∧ R ≫ F.1.idem.e = R) := by
  constructor
  · rintro ⟨Φ, rfl⟩
    exact ⟨Φ.fixed_left, Φ.fixed_right⟩
  · intro h
    exact ⟨⟨R, (splHom_fixed_iff_book R).mpr h⟩, rfl⟩

end BookHom

/-! ## §2.16(14)  The effective reflection of `Rel(Assembly K)`

  Instantiate the generic theory at `𝒜 = Rel(A)`, `A` = the category of assemblies
  over a modulus system `K` (§2.153).  `Rel(A)` is an allegory because `A` is regular
  (`asmRegular`, §2.153; `relAllegory`, §2.111). -/

section Assemblies
-- `relGraph`/`relGraph_comp` (§2.217 graph embedding) live in `Freyd.DisjointGluing`.
open DisjointGluing
variable (K : ModulusSystem)

/-- **§2.16(14)**: `Rel(A)` — the allegory of relations of the category of
    assemblies over `K` (regular by §2.153, so §2.111 applies). -/
@[expose] public abbrev AsmRel : Type (u + 1) := RelObj (Assembly.{u} K)

/-- **§2.16(14)**: the effective reflection `E` of `Rel(A)`: the reflexive splitting
    completion `Spl(Eq (Rel A))` (§2.433).  Objects are pairs `⟨A, I⟩` — written `A/I`
    to suggest the formal quotient — of an assembly `A` and an equivalence relation
    `I : A → A` in `Rel(A)`. -/
@[expose] public abbrev AsmEffReflection : Type (u + 1) := SplEqObj (AsmRel K)

/-- **§2.16(14)**: the object `⟨A, I⟩ = A/I` of `E`, from an assembly `A` and an
    equivalence relation `I` on it in `Rel(A)` (reflexive, symmetric, transitive —
    packaged into the reflexive symmetric idempotent that `Spl(Eq)` splits). -/
@[expose] public def asmQuot (A : Assembly.{u} K) (I : (⟨A⟩ : AsmRel K) ⟶ ⟨A⟩)
    (hrefl : Reflexive I) (hsym : Symmetric I) (htrans : Transitive I) :
    AsmEffReflection K :=
  eqRelObj I hrefl (symmetric_eq hsym) (reflexive_transitive_idempotent hrefl htrans)

/-- The objects of `E` are EXACTLY the book's pairs `⟨A, I⟩`: every object of the
    reflection is `asmQuot` of an assembly and an equivalence relation on it. -/
public theorem asmEffReflection_obj_form (E : AsmEffReflection K) :
    ∃ (A : Assembly.{u} K) (I : (⟨A⟩ : AsmRel K) ⟶ ⟨A⟩) (hrefl : Reflexive I)
      (hsym : Symmetric I) (htrans : Transitive I),
      E = asmQuot K A I hrefl hsym htrans := by
  obtain ⟨⟨⟨A⟩, ⟨I, hsym, hidem⟩⟩, hrefl⟩ := E
  exact ⟨A, I, hrefl, (symmetric_iff I).mpr hsym,
    by show I ≫ I ⊑ I; rw [hidem]; exact le_refl I, rfl⟩

/-- **§2.16(14) morphism description**: "a relation `R : A → B` in `Rel(A)` is
    considered a morphism from `A/I` to `B/J` in `E` iff `IR = R = RJ` in `Rel(A)`". -/
theorem asmRel_hom_iff {E F : AsmEffReflection K} (R : E.1.carrier ⟶ F.1.carrier) :
    (∃ Φ : E ⟶ F, Φ.R = R) ↔ (E.1.idem.e ≫ R = R ∧ R ≫ F.1.idem.e = R) :=
  splEq_hom_iff R

/-! ### "Every assembly A may be considered as an object A/1_A in E"

  The §2.433 embedding `embEq : 𝒜 ↪ Spl(Eq 𝒜)`, instantiated: on objects `A ↦ A/1_A`;
  on relations it is the identity (`embEqHom`), full and faithful, preserving and
  reflecting `≫`/`°`/`∩`/`⊑`/`Map` (re-exported from S2_16c where useful by name;
  the generic `embEq_*` lemmas apply verbatim). -/

/-- **§2.16(14)**: the embedding on objects — the assembly `A` considered as the
    object `A/1_A` of `E`. -/
def asmEmbed (A : Assembly.{u} K) : AsmEffReflection K := embEq ⟨A⟩

@[simp] theorem asmEmbed_carrier (A : Assembly.{u} K) :
    (asmEmbed K A).1.carrier = ⟨A⟩ := rfl

@[simp] theorem asmEmbed_idem (A : Assembly.{u} K) :
    (asmEmbed K A).1.idem.e = Cat.id (⟨A⟩ : AsmRel K) := rfl

/-- The embedding on relations: `R : A → B` of `Rel(A)` viewed as `A/1_A ⟶ B/1_B`
    (it is literally `R`, since `1R1 = R`). -/
def asmEmbedHom {A B : Assembly.{u} K} (R : (⟨A⟩ : AsmRel K) ⟶ ⟨B⟩) :
    asmEmbed K A ⟶ asmEmbed K B :=
  embEqHom R

@[simp] theorem asmEmbedHom_R {A B : Assembly.{u} K} (R : (⟨A⟩ : AsmRel K) ⟶ ⟨B⟩) :
    (asmEmbedHom K R).R = R := rfl

/-- The embedding `Rel(A) ↪ E` is FAITHFUL. -/
theorem asmEmbed_faithful {A B : Assembly.{u} K} {R S : (⟨A⟩ : AsmRel K) ⟶ ⟨B⟩}
    (h : asmEmbedHom K R = asmEmbedHom K S) : R = S :=
  embHom_injective h

/-- The embedding preserves and reflects MAPS (so the maps `A/1_A → B/1_B` of `E` are
    exactly the maps of `Rel(A)`, i.e. — §2.217 — the assembly morphisms). -/
theorem asmEmbedHom_map_iff {A B : Assembly.{u} K} (R : (⟨A⟩ : AsmRel K) ⟶ ⟨B⟩) :
    Map (asmEmbedHom K R) ↔ Map R :=
  embEq_map_iff R

/-! ### Assembly morphisms become maps of the reflection

  Composing the graph embedding `A → Rel(A)` (§2.217, `relGraph`) with `asmEmbedHom`
  realizes the category **A** of assemblies inside (the maps of) `E`. -/

/-- An assembly MORPHISM `f : A → B`, via its graph `[graph f]`, considered as a
    morphism `A/1_A ⟶ B/1_B` of `E`. -/
def asmEmbedMap {A B : Assembly.{u} K} (f : A ⟶ B) :
    asmEmbed K A ⟶ asmEmbed K B :=
  embEqHom (𝒜 := AsmRel K) (a := ⟨A⟩) (b := ⟨B⟩) (relGraph f)

/-- `asmEmbedMap f` is a MAP of `E` (graphs are maps, §2.217 `relClass_graph_map`;
    the embedding reflects maps). -/
theorem asmEmbedMap_map {A B : Assembly.{u} K} (f : A ⟶ B) :
    Map (asmEmbedMap K f) :=
  (embEq_map_iff _).mpr (relClass_graph_map f)

/-- `asmEmbedMap` preserves identities. -/
theorem asmEmbedMap_id (A : Assembly.{u} K) :
    asmEmbedMap K (Cat.id A) = Cat.id (asmEmbed K A) :=
  embEq_id (⟨A⟩ : AsmRel K)

/-- `asmEmbedMap` preserves composition (graphs compose, §2.217 `relGraph_comp`). -/
theorem asmEmbedMap_comp {A B C : Assembly.{u} K} (f : A ⟶ B) (g : B ⟶ C) :
    asmEmbedMap K (f ≫ g) = asmEmbedMap K f ≫ asmEmbedMap K g := by
  show embEqHom (𝒜 := AsmRel K) (a := ⟨A⟩) (b := ⟨C⟩) (relGraph (f ≫ g)) = _
  rw [relGraph_comp]
  exact embEq_comp (𝒜 := AsmRel K) (a := ⟨A⟩) (b := ⟨B⟩) (c := ⟨C⟩)
    (relGraph f) (relGraph g)

/-- `asmEmbedMap` is FAITHFUL: the category of assemblies sits inside `E`
    (graph injectivity `relClass_graph_inj` + faithfulness of the embedding). -/
theorem asmEmbedMap_faithful {A B : Assembly.{u} K} {f g : A ⟶ B}
    (h : asmEmbedMap K f = asmEmbedMap K g) : f = g :=
  relClass_graph_inj (embHom_injective h)

/-! ### Effectiveness -/

/-- **§2.16(14) headline (effectiveness)**: the reflection `E` of `Rel(A)` is
    EFFECTIVE — every equivalence relation of `E` splits with a map leg.  This is the
    §2.433 splitting fact `splEq_hsplit`, instantiated at `𝒜 = Rel(Assembly K)`. -/
theorem asmEffReflection_eqSplits : EqSplits (AsmEffReflection K) :=
  splEq_hsplit

end Assemblies

end Freyd.Alg
