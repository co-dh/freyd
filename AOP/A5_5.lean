/-
  Bird & de Moor, *Algebra of Programming* §5.5  Relational catamorphisms
  (the Eilenberg–Wright lemma, book pp. 121–122).

  For a relator `F` on `𝒜` with an initial algebra `α : F t ⟶ t` in the subcategory of
  MAPS of `𝒜`, every algebra `R : F A ⟶ A` (a relation, not necessarily a map) has a
  UNIQUE relational catamorphism `(|R|) : t ⟶ A` characterised by
  `α · X = FX · R ⟺ X = (|R|)`  (5.12, mirrored to diagram order: `α ≫ X = F.map X ≫ R`).

  B&dM's construction: `(|R|) = ∈ · (|Λ(R·F∈)|)`, i.e. transpose the relational algebra
  `R : F A ⟶ A` through the power object of `A` to the MAP algebra
  `Λ(R·F∈) : F [A] ⟶ [A]` (Freyd: `Λ (F.map (∋ A) ≫ R) : F.obj (powerObj A) ⟶ powerObj A`),
  take the ordinary (map) catamorphism of that, and compose with `∈` to come back down
  to `A`.  All composition is diagram order (Freyd `≫`), mirroring B&dM's `·`.

  Needs Lemma 5.1 ("relators preserve maps": `Map f → Map (F f) ∧ F(f°) = (F f)°`) — its
  canonical home is `A5_1.lean` (added by a parallel wave); a private copy is proved here
  from `recip_of_comp_id` (A4_2) so this file does not block on that landing.
-/
module

public import Freyd.S2_40
public import AOP.A4_6
public import AOP.A4_2
public import AOP.A5_1

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerAllegory 𝒜] (F : Relator 𝒜 𝒜)

-- (Lemma 5.1 "relators preserve maps" now comes from A5_1: `Relator.map_is_map`.)

/-- **B&dM p.121**: `F` has an initial algebra `α : F t ⟶ t` IN THE SUBCATEGORY OF MAPS —
    `α` is a map, and for every MAP algebra `f : F A ⟶ A` there is a unique map
    `cata f hf : t ⟶ A` with `α ≫ cata f hf = F.map (cata f hf) ≫ f`
    (B&dM `cata f hf · α = f · F(cata f hf)`, mirrored). -/
public class InitialAlgebra (F : Relator 𝒜 𝒜) where
  t : 𝒜
  α : F.obj t ⟶ t
  α_map : Map α
  cata : ∀ {A : 𝒜} (f : F.obj A ⟶ A), Map f → (t ⟶ A)
  cata_map : ∀ {A : 𝒜} (f : F.obj A ⟶ A) (hf : Map f), Map (cata f hf)
  cata_comm : ∀ {A : 𝒜} (f : F.obj A ⟶ A) (hf : Map f), α ≫ cata f hf = F.map (cata f hf) ≫ f
  cata_unique : ∀ {A : 𝒜} (f : F.obj A ⟶ A) (hf : Map f) (h : t ⟶ A), Map h →
    α ≫ h = F.map h ≫ f → h = cata f hf

variable {F}

/-- **B&dM p.121**: the RELATIONAL catamorphism `(|R|) = ∈·(|Λ(R·F∈)|)` (mirrored):
    transpose the algebra `R : F A ⟶ A` to the map algebra `Λ(R·F∈) : F[A] ⟶ [A]`, take
    its (map) catamorphism, and compose back down with `∈`. -/
@[expose] public def relCata [I : InitialAlgebra F] {A : 𝒜} (R : F.obj A ⟶ A) : I.t ⟶ A :=
  I.cata (Λ (F.map (∋ A) ≫ R)) (Λ_is_map' _) ≫ ∋ A

/-- The book's banana brackets `(|R|)`.  The ONE global binding: the structural folds `cataR`
    equal `relCata` only propositionally (`cataR_eq_relCata`), so they are spelled by name. -/
notation:max "⦇" R "⦈" => relCata R

open Lean PrettyPrinter in
/-- The MAP fold wears the same banana as the relational one: the note's `<initial-defn>` square
    writes `⦇f⦈` for the arrow `cata_comm` characterises.  `hf : Map f` is a proof, and a proof is
    not part of what the note calls the arrow. -/
@[app_unexpander InitialAlgebra.cata] public meta def unexpandCata : Unexpander
  | `($_ $f $_hf) => `(⦇$f⦈)
  | _ => throw ()

public theorem relCata_unfold (I : InitialAlgebra F) {A : 𝒜} (R : F.obj A ⟶ A) :
    relCata R = I.cata (Λ (F.map (∋ A) ≫ R)) (Λ_is_map' _) ≫ ∋ A := rfl

/-- **Eilenberg–Wright lemma (5.12)**: `α · X = FX · R ⟺ X = (|R|)`, mirrored to
    `α ≫ X = F.map X ≫ R ⟺ X = relCata I R`.  This is the defining universal property
    of the relational catamorphism, characterising `(|R|)` among ALL relations `X : t ⟶ A`
    (not just maps). -/
public theorem relCata_UP (I : InitialAlgebra F) {A : 𝒜} (f : F.obj A ⟶ A) (X : I.t ⟶ A) :
    (I.α ≫ X = F.map X ≫ f) ↔ X = relCata f := by
  constructor
  · intro h
    -- `Λ X` is a map, so `X = Λ X ≫ ∋ A`; rewrite both sides of `h` through this map
    -- and transport the equation to `Λ (F.map (∋ A) ≫ R)` via `Λ_fusion`.
    have hX_eps : Λ X ≫ ∋ A = X := Λ_eps_eq' X
    have hFX : F.map X = F.map (Λ X) ≫ F.map (∋ A) := by
      -- rewrite the LARGER pattern `Λ X ≫ ∋ A` (not bare `X`) so the `Λ X` inside it
      -- does not spuriously get rewritten too.
      have hcomp : F.map (Λ X ≫ ∋ A) = F.map (Λ X) ≫ F.map (∋ A) := F.map_comp _ _
      rwa [hX_eps] at hcomp
    have hRHS : Λ (F.map X ≫ f) = F.map (Λ X) ≫ Λ (F.map (∋ A) ≫ f) := by
      rw [hFX, Cat.assoc, Λ_fusion (F.map_is_map (Λ_is_map' X))]
    have hLHS : Λ (I.α ≫ X) = I.α ≫ Λ X := Λ_fusion I.α_map X
    have heq : I.α ≫ Λ X = F.map (Λ X) ≫ Λ (F.map (∋ A) ≫ f) := by
      rw [← hLHS, h, hRHS]
    have hAX_eq_u : Λ X = I.cata (Λ (F.map (∋ A) ≫ f)) (Λ_is_map' _) :=
      I.cata_unique _ (Λ_is_map' _) (Λ X) (Λ_is_map' X) heq
    rw [relCata_unfold, ← hAX_eq_u, hX_eps]
  · intro h
    rw [h, relCata_unfold]
    generalize hu_def : I.cata (Λ (F.map (∋ A) ≫ f)) (Λ_is_map' _) = u
    have hu_comm : I.α ≫ u = F.map u ≫ Λ (F.map (∋ A) ≫ f) := by
      rw [← hu_def]; exact I.cata_comm _ _
    calc I.α ≫ (u ≫ ∋ A)
        = (I.α ≫ u) ≫ ∋ A := by rw [Cat.assoc]
      _ = (F.map u ≫ Λ (F.map (∋ A) ≫ f)) ≫ ∋ A := by rw [hu_comm]
      _ = F.map u ≫ (Λ (F.map (∋ A) ≫ f) ≫ ∋ A) := by rw [Cat.assoc]
      _ = F.map u ≫ (F.map (∋ A) ≫ f) := by rw [Λ_eps_eq']
      _ = (F.map u ≫ F.map (∋ A)) ≫ f := by rw [Cat.assoc]
      _ = F.map (u ≫ ∋ A) ≫ f := by rw [F.map_comp]

/-- (5.12), read backwards at `X := (|R|)`: `(|R|)` satisfies its own defining equation. -/
public theorem relCata_cancel (I : InitialAlgebra F) {A : 𝒜} (R : F.obj A ⟶ A) :
    I.α ≫ relCata R = F.map (relCata R) ≫ R :=
  (relCata_UP I R (relCata R)).mpr rfl

/-- The relational catamorphism over a MAP algebra is the ordinary (map) catamorphism:
    `(|f|) = cata f hf` when `f` is a map. -/
theorem relCata_map (I : InitialAlgebra F) {A : 𝒜} (f : F.obj A ⟶ A) (hf : Map f) :
    relCata f = I.cata f hf :=
  ((relCata_UP I f (I.cata f hf)).mp (I.cata_comm f hf)).symm

/-- `Λ(|R|) = (|Λ(R·F∈)|)` (B&dM p.121): the power-transpose of the relational catamorphism
    is exactly the map catamorphism of the transposed algebra it was built from. -/
public theorem Λ_relCata (I : InitialAlgebra F) {A : 𝒜} (R : F.obj A ⟶ A) :
    Λ (relCata R) = I.cata (Λ (F.map (∋ A) ≫ R)) (Λ_is_map' _) := by
  rw [relCata_unfold]
  generalize hu_def : I.cata (Λ (F.map (∋ A) ≫ R)) (Λ_is_map' _) = u
  have hu_map : Map u := hu_def ▸ I.cata_map _ _
  exact ((Λ_UP (u ≫ ∋ A) hu_map).mpr rfl).symm

/-- **B&dM p.121, the map algebra's square**: the fold's defining equation at the MAP algebra
    `Λ(F(∋)R)`, together with the triangle saying what that algebra is — `Λ(F(∋)R)∋ = F(∋)R`.
    Two faces of one picture: the second says the algebra the first folds is the transpose of
    `F(∋)R`, and they share that algebra.  The algebra is NAMED `f` and pinned by `hf`, which is
    how the picture writes a name on that arrow with its value beneath. -/
public theorem relCata_mapAlg_cancel (I : InitialAlgebra F) {A : 𝒜} (R : F.obj A ⟶ A)
    {f} (hf : f = Λ (F.map (∋ A) ≫ R)) (hm : Map f) :
    I.α ≫ I.cata f hm = F.map (I.cata f hm) ≫ f
      ∧ f ≫ ∋ A = F.map (∋ A) ≫ R := by
  subst hf; exact ⟨I.cata_comm _ _, Λ_comp_eps _⟩

/-! ## §2.6  Fusion (2.12) and Ex 2.35 (book pp. 46, 49)

  These belong here, not in `AOP.A6_2`: the INCLUSION fusion laws (6.4)/(6.5) there need
  `UnguardedPowerLCDA` because they argue through a least fixed point, whereas the EQUALITY
  fusion below follows from the universal property `relCata_UP` alone and so lives in the
  weaker `UnguardedPowerAllegory` setting of this file. -/

/-- **B&dM (2.12), p.46 — fusion**: `h·(|f|) = (|g|) ⟸ h·f = g·F h`, mirrored to diagram
    order (`h·f ↦ f h`) as `(|R|) S = (|Q|) ⟸ R S = (F S) Q`.

    Unlike the inclusion laws (6.4)/(6.5) of `AOP.A6_2` this needs NO local completeness —
    no `Sup`/`Inf`, no fixed point — only `relCata_UP` and `relCata_cancel`: the composite
    `(|R|) S` is shown to satisfy `Q`'s defining equation, and uniqueness does the rest. -/
public theorem relCata_fusion (I : InitialAlgebra F) {B C : 𝒜} {R : F.obj B ⟶ B}
    {Q : F.obj C ⟶ C} {S : B ⟶ C} (h : R ≫ S = F.map S ≫ Q) :
    relCata R ≫ S = relCata Q := by
  apply (relCata_UP I Q (relCata R ≫ S)).mp
  calc I.α ≫ relCata R ≫ S
      = (I.α ≫ relCata R) ≫ S := by rw [Cat.assoc]
    _ = (F.map (relCata R) ≫ R) ≫ S := by rw [relCata_cancel]
    _ = F.map (relCata R) ≫ R ≫ S := by rw [Cat.assoc]
    _ = F.map (relCata R) ≫ F.map S ≫ Q := by rw [h]
    _ = (F.map (relCata R) ≫ F.map S) ≫ Q := by rw [Cat.assoc]
    _ = F.map (relCata R ≫ S) ≫ Q := by rw [F.map_comp]

/-- **B&dM Ex 2.35, p.49**, verbatim: "Show that `(|f · g|) = f · (|g · F f|)`", with the
    types the book leaves implicit — `f : A ← X` and `g : X ← F A`, so `f·g : A ← F A` is an
    F-algebra on `A` and `g·F f : X ← F X` one on `X`.  Mirrored to diagram order with
    `f : x ⟶ a` and `g : F.obj a ⟶ x` it reads `(|(F f) g|) f = (|g f|)`.

    This is `relCata_fusion` at `R := (F f) g`, `S := f`, `Q := g f`, whose side condition
    `R S = (F S) Q` is nothing but associativity: both sides are the same three-arrow word
    `(F f) g f`, bracketed `((F f) g) f` on the left and `(F f) (g f)` on the right.

    A one-term theorem, kept despite the repo's no-wrapper rule under its stated exception
    for a statement that is itself a required deliverable — this is a book-numbered exercise. -/
public theorem relCata_of_comp (I : InitialAlgebra F) {A x : 𝒜} (f : x ⟶ A) (g : F.obj A ⟶ x) :
    relCata (F.map f ≫ g) ≫ f = relCata (g ≫ f) :=
  relCata_fusion I (Cat.assoc (F.map f) g f)

/-! ## The category of `F`-algebras, and `⦇·⦈` as a family natural in the ALGEBRA

  `relCata_fusion` above is stated arrow by arrow.  Read instead as a statement about the
  CATEGORY whose objects are the algebras `R : F A ⟶ A` and whose arrows are the
  homomorphisms, it says that the fold is a natural transformation

      `⦇·⦈ : Δᴛ ⟹ U`,   `Δᴛ` constant at the initial carrier `t`, `U` the forgetful functor,

  which is what lets a picture draw it as a BEAD where the algebra region closes, rather than
  as an opaque label (IntroString p. 147, (5.8), middle: `UΣ∘ϵ : UΣ FreeΣ ⟹ UΣ`, read here at
  initiality instead of at a free algebra — `Δᴛ` factors through the terminal category, so its
  leg enters from the region's boundary where (5.8)'s `FreeΣ` wire passes through from the top).

  WHICH CONDITION ON THE ARROWS.  Both candidates compose and both carry the identity:
  `R S = F(S) Q` (strict) and `R S ⊑ F(S) Q` (lax) are each preserved by `≫`, the lax one
  because `≫` is monotone in both arguments.  They differ in what the fold then satisfies:

  - STRICT arrows: `relCata_fusion` gives `⦇R⦈S = ⦇Q⦈` — an EQUALITY, so the family is
    STRICTLY natural, and it holds in this file's `UnguardedPowerAllegory`, from the universal
    property `relCata_UP` alone.  That is the form stated below.
  - LAX arrows: the best available is `comp_le_relCata` (`AOP.A6_2`), `⦇R⦈S ⊑ ⦇Q⦈`.  Note the
    DIRECTION: with `φ A ≜ ⦇A.alg⦈ : t ⟶ A` the square runs `φ A ≫ U(S) ⊑ Δᴛ(S) ≫ φ B`, the
    reverse of `LaxNatural`'s `G(R) ≫ φ B ⊑ φ A ≫ F(R)` — so over the lax category the fold is
    OPLAX, not lax.  It also costs local completeness (`UnguardedPowerLCDA`), because it is
    proved from the least-fixed-point reading of `⦇·⦈` and not from `relCata_UP`.

  So the strict category is what the proof gives, and it is the cheaper one; the lax category's
  statement is `comp_le_relCata` and is not restated here. -/

/-- An `F`-ALGEBRA (B&dM p. 121): a carrier with an algebra — a RELATION, not necessarily a
    map — on it.  The objects of the category the fold is natural over. -/
public structure Algebra {𝒜 : Type u} [UnguardedPowerAllegory 𝒜] (F : Relator 𝒜 𝒜) where
  carrier : 𝒜
  alg : F.obj carrier ⟶ carrier

/-- A HOMOMORPHISM of `F`-algebras: `R S = F(S) Q`, the arrows of the STRICT algebra category
    (see the section note for why the lax condition is not the one taken). -/
public structure AlgHom {𝒜 : Type u} [UnguardedPowerAllegory 𝒜] {F : Relator 𝒜 𝒜}
    (A B : Algebra F) where
  hom : A.carrier ⟶ B.carrier
  comm : A.alg ≫ hom = F.map hom ≫ B.alg

/-- Two homomorphisms with the same underlying arrow are equal: `comm` is a proof. -/
public theorem AlgHom.ext {A B : Algebra F} : ∀ {S T : AlgHom A B}, S.hom = T.hom → S = T
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- Homomorphisms COMPOSE: the two squares glue, `F` turning the two arrows into one. -/
public theorem AlgHom.comm_comp {A B C : Algebra F} (S : AlgHom A B) (T : AlgHom B C) :
    A.alg ≫ (S.hom ≫ T.hom) = F.map (S.hom ≫ T.hom) ≫ C.alg := by
  rw [← Cat.assoc, S.comm, Cat.assoc, T.comm, ← Cat.assoc, ← F.map_comp]

/-- The CATEGORY of `F`-algebras.  NOT an allegory: the homomorphism condition is closed under
    neither `°` (converse turns `R S = F(S) Q` into `S° R° = Q° F(S)°`, which is not a
    homomorphism condition) nor `∩` (it would need `F(S)Q ∩ F(S')Q ⊑ F(S∩S')Q`, and a relator
    preserves `∩` only on coreflexives, Ex 5.2) — so `U` and `Δᴛ` below are `Freyd.Functor`s
    and not `Relator`s, and the fold's naturality is `=`, not `⊑`. -/
@[expose] public instance instCatAlgebra {𝒜 : Type u} [UnguardedPowerAllegory 𝒜]
    (F : Relator 𝒜 𝒜) : Cat (Algebra F) where
  Hom A B := AlgHom A B
  id A := ⟨𝟙 A.carrier, by rw [Cat.comp_id, F.map_id, Cat.id_comp]⟩
  comp S T := ⟨S.hom ≫ T.hom, S.comm_comp T⟩
  id_comp S := AlgHom.ext (Cat.id_comp S.hom)
  comp_id S := AlgHom.ext (Cat.comp_id S.hom)
  assoc S T U := AlgHom.ext (Cat.assoc S.hom T.hom U.hom)

/-- `U`, the FORGETFUL functor: an algebra to its carrier, a homomorphism to its arrow. -/
@[expose] public def algU {𝒜 : Type u} [UnguardedPowerAllegory 𝒜] (F : Relator 𝒜 𝒜) :
    Freyd.Functor (Algebra F) 𝒜 where
  obj A := A.carrier
  map S := S.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `Δᴛ`, the CONSTANT functor at the initial algebra's carrier `t`.  It factors through the
    terminal category, which is why the fold's source leg enters a panel from the region's
    boundary instead of passing through it from the top. -/
@[expose] public def algDelta [I : InitialAlgebra F] : Freyd.Functor (Algebra F) 𝒜 where
  obj _ := I.t
  map _ := 𝟙 I.t
  map_id _ := rfl
  map_comp _ _ := (Cat.id_comp (𝟙 I.t)).symm

/-- **THE FOLD AS A FAMILY** over the algebras: `⦇·⦈ A = ⦇A.alg⦈ : t ⟶ A`, a component of
    `Δᴛ ⟹ U` at each algebra.

    THE TARGET IS THE CARRIER AND THE SOURCE IS `Δᴛ` APPLIED, which is IntroString (5.8)'s middle
    diagram: its `ϵ` has the composite `Free(A)` above it and the bare algebra `(A,a)` below, so the
    region between the functor wire and the object wire CLOSES at the bead.  Here the wire that dies
    is `Δᴛ` and the object wire passes from the algebra category into `𝒜` — spelling the target
    `U(A)` instead puts a second lane under the bead and the two wires run past each other rather
    than meeting.  `U(A)` and `A.carrier` are the same object, so `fold_natural` reads either way. -/
@[expose] public def fold [I : InitialAlgebra F] (A : Algebra F) :
    (algDelta (F := F)).obj A ⟶ A.carrier := relCata A.alg

/-- The note's name for the constant functor at the initial carrier. -/
notation:max "Δᴛ" => algDelta

open Lean PrettyPrinter in
/-- THE LANE IS THE FUNCTOR, NOT ITS PARAMETER: `F` is which algebra category the panel is in —
    the region — so the wire's name is the letter `U` alone. -/
@[app_unexpander algU] public meta def unexpandAlgU : Unexpander
  -- `mkIdent`, not a quoted `U`: a quotation's identifier carries macro scopes and the lane's
  -- label comes out `U✝`.
  | `($_ $_F) => `($(mkIdent `U))
  | _ => throw ()

/-- THE BARE FOLD IS A BARE BANANA: `⦇·⦈`, the rule beside the constant that lets a picture drop
    the index, since the object wire under the bead already says which algebra it is taken at. -/
notation:max "⦇·⦈" => fold

open Lean PrettyPrinter in
/-- THE FOLD WEARS THE BOOK'S BANANA, with the ALGEBRA inside it: `⦇A⦈`, where `A` is the object
    of the algebra category and `⦇R⦈` the same arrow written at that algebra's own structure.  This
    is the spelling a FORMULA takes, which has no wire to read the index off; a picture strips it
    down to the `⦇·⦈` above. -/
@[app_unexpander fold] public meta def unexpandFold : Unexpander
  | `($_ $A) => `(⦇$A⦈)
  | _ => throw ()

open Lean PrettyPrinter in
/-- A HOMOMORPHISM AND ITS UNDERLYING ARROW WEAR ONE NAME, the book's own practice: `U(S)` is the
    forgetful functor applied, and a functor applied to an arrow is drawn by the arrow's own bead
    with the functor wire running past, so a second name at the bead would spell `U` twice. -/
@[app_unexpander AlgHom.hom] public meta def unexpandAlgHom : Unexpander
  | `($_ $S) => `($S)
  | _ => throw ()

/-- **THE FOLD IS STRICTLY NATURAL IN ITS ALGEBRA**: `Δᴛ(S) ⦇B⦈ = ⦇A⦈ S` for every homomorphism
    `S : A ⟶ B`, `S` below the fold being `U(S)`, the underlying arrow.  `Δᴛ(S)` is the identity,
    so this is `relCata_fusion` read as one square of a natural transformation — an EQUALITY, in
    `UnguardedPowerAllegory`. -/
public theorem fold_natural [I : InitialAlgebra F] {A B : Algebra F} (S : A ⟶ B) :
    (algDelta (F := F)).map S ≫ fold B = fold A ≫ S.hom := by
  show 𝟙 I.t ≫ relCata B.alg = relCata A.alg ≫ S.hom
  rw [Cat.id_comp, relCata_fusion I S.comm]

/-!
  ## Ex 5.19 — dropped

  B&dM's exercise asks to show `Entire R → Entire (|R|)`, hinting "use reflection to show
  `dom (|R|) = id`".  Genuine attempts (3):

  1. `dom (relCata I R) = dom (u ≫ ∋ A) = dom (u ≫ dom (∋ A))` via `dom_comp_dom` (A4_2),
     with `u` the map catamorphism above.  This reduces the goal to `u ≫ dom (∋ A) `
     having full domain, i.e. that `u` (hence, by the same shape of argument, `(|R|)`
     itself) always lands in the coreflexive "nonempty-set" part of `[A]` cut out by
     `dom (∋ A)`.  Proving THAT needs an inductive/fusion argument on `u` as the initial
     map-catamorphism — exactly as hard as the original goal, not a reduction.
  2. Apply `dom`/`congrArg` to `relCata_cancel`'s equation `α ≫ (|R|) = F(|R|) ≫ R` and push
     `dom` through both sides via `dom_comp_dom` + `Entire R` (`dom R = id`, so
     `dom (F(|R|) ≫ R) = dom (F(|R|))`).  This yields `dom (α ≫ dom(|R|)) = dom (F (|R|))`,
     relating `dom(|R|)` to `dom (F.map (relCata I R))` — but nothing here lets us peel
     `dom` through `F.map`, since a bare `Relator` need NOT preserve converse (`°`)
     without the extra `PreservesRecip` hypothesis (Theorem 5.1, tabular-only), so
     `dom (F.map X)` cannot be related to `F.map (dom X)` in general.
  3. Tried to phrase "R entire" as a subalgebra/mono condition on `t` and use
     `cata_unique` as an induction principle (the standard "no-junk" argument for initial
     algebras).  `InitialAlgebra` as specified only bundles the universal property for
     MAPS `t ⟶ A` against a FIXED target `A` (uniqueness of the homomorphism solving
     `α ≫ h = F.map h ≫ f`); it does not give an induction/extremal principle over
     mono-subobjects of `t` needed to transport a pointwise property ("is `R`-entire")
     through `α`.  That principle is extra initial-algebra infrastructure this file's
     `InitialAlgebra` does not carry.

  Conclusion: `Entire R → Entire (relCata I R)` is a genuine wall — it needs either (a) a
  `PreservesRecip`/tabular hypothesis on `F` making route 2 close, or (b) strengthening
  `InitialAlgebra` with an induction/no-junk principle for route 3. Left open here; not
  attempted further per the task's explicit license to drop this item.
-/

-- printing-only unexpanders: the note's spelling.  A picture drawn by `diag-export --commutative`
-- takes every label from `Meta.ppExpr`, so what the note calls a thing has to be what Lean PRINTS
-- it as; these change no statement and no `stmt_key`.
-- The carrier and the algebra of an initial algebra are `T` and `α` — the letters `<initial-defn>`
-- and B&dM §2.6 draw them with — and the relator argument is not part of either name.  When that
-- relator is itself a PARTIAL APPLICATION (`F.appl a`, `CL.F Unit A`, …) the initial algebra is one
-- member of a family and its last argument is the index, so it is written back on: `T A`, `α A`.
-- The index is the LAST argument of whichever operand is itself an application: the family `I`
-- taken at `a` (`(I a).t`, how field notation prints it) and the partial relator `F.appl a` are the
-- same indexing, so both spellings answer `a`.  An operand that is not an application is one
-- initial algebra, not a family, and carries no index.
-- Which member of the family, read off whichever operand is an application: `F.appl a`, `(I a)` and
-- `CL.F Unit a` all answer `a`, whether the printer put the relator or the algebra in front.  An
-- operand that is a plain name is one initial algebra, not a family, and has no index.
open Lean in
public meta def lastArg : Term → Option Term
  | `($_ $_ $a) => some a
  | `($_ $a) => some a
  | _ => none

-- A quotation pattern's own brackets are a `paren` node, which a delaborated argument does not
-- carry, so the operand is bound and taken apart on its own rather than matched in place.
open Lean in
public meta def familyIndex : Term → Option Term
  | `($_ $x) => lastArg x
  | _ => none

open Lean PrettyPrinter in
@[app_unexpander InitialAlgebra.t] public meta def unexpandInitialAlgebraT : Unexpander := fun stx =>
  match familyIndex ⟨stx⟩ with
  | some a => `($(mkIdent `T) $a)
  | none => `($(mkIdent `T))

open Lean PrettyPrinter in
@[app_unexpander InitialAlgebra.α] public meta def unexpandInitialAlgebraAlpha : Unexpander :=
  fun stx => match familyIndex ⟨stx⟩ with
  | some a => `($(mkIdent `α) $a)
  | none => `($(mkIdent `α))

/-! ## Mutual recursion (B&dM Ex 3.8, p. 58) -/

/-- **An algebra on a PRODUCT carrier is folded by a fork.**  `⟨f,g⟩` meets the two defining
    equations of `h` and `k` — one per component, each seeing BOTH components through `F(⟨f,g⟩)` —
    exactly when it is `⦇⟨h,k⟩⦈`.  Strictly more general than banana split, where `h` and `k`
    factor as `F(π₁)h` and `F(π₂)k` and so each sees only its own component. -/
public theorem pair_eq_relCata_pair_iff [HasBinaryProducts 𝒜] (I : InitialAlgebra F)
    {A B : 𝒜} (f : I.t ⟶ A) (g : I.t ⟶ B)
    (h : F.obj (prod A B) ⟶ A) (k : F.obj (prod A B) ⟶ B) :
    (I.α ≫ f = F.map (pair f g) ≫ h ∧ I.α ≫ g = F.map (pair f g) ≫ k)
      ↔ pair f g = ⦇pair h k⦈ := by
  -- The fold's universal property at `X := ⟨f,g⟩`, `R := ⟨h,k⟩`, with both sides of its equation
  -- pushed through the fork (`pair_precomp`); `⟨-,-⟩` is then injective by its own two β-laws.
  rw [← relCata_UP I (pair h k) (pair f g), pair_precomp, pair_precomp]
  constructor
  · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
  · intro hEq
    exact ⟨by rw [← fst_pair (I.α ≫ f) (I.α ≫ g), hEq, fst_pair],
           by rw [← snd_pair (I.α ≫ f) (I.α ≫ g), hEq, snd_pair]⟩

end Freyd.Alg

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerAllegory 𝒜] {F : Relator 𝒜 𝒜}

/-- **BANANA SPLIT (B&dM figure 7b)**: the product's universal property read AT THE TWO FOLDS.
    `⟨⦇h⦈,⦇k⦈⟩` is the one arrow `T⟶A×B` with components `⦇h⦈` and `⦇k⦈`, and these are the two
    triangles the note draws round it — which is why the statement is the pair of β-laws at
    `⦇h⦈`, `⦇k⦈` rather than the β-laws at two arbitrary arrows. -/
public theorem relCata_pair_beta [HasBinaryProducts 𝒜] (I : InitialAlgebra F) {A B : 𝒜}
    (h : F.obj A ⟶ A) (k : F.obj B ⟶ B) :
    pair ⦇h⦈ ⦇k⦈ ≫ fst = ⦇h⦈ ∧ pair ⦇h⦈ ⦇k⦈ ≫ snd = ⦇k⦈ :=
  ⟨fst_pair _ _, snd_pair _ _⟩

/-- **BANANA SPLIT (B&dM Ex 3.6, p. 57)**: `⟨(|h|),(|k|)⟩ = (|⟨F(π₁)·h, F(π₂)·k⟩|)` — a fork of
    two folds is ONE fold, hence one traversal.  It is the special case of the mutual-recursion
    law (`pair_eq_relCata_pair_iff`) where the two algebras factor through the projections, so
    each sees only its own component; the two defining equations then reduce to
    `F(⟨(|h|),(|k|)⟩)·F(π₁) = F((|h|))` and its mirror. -/
public theorem pair_relCata_eq_relCata_pair [HasBinaryProducts 𝒜] (I : InitialAlgebra F)
    {A B : 𝒜} (h : F.obj A ⟶ A) (k : F.obj B ⟶ B) :
    pair ⦇h⦈ ⦇k⦈ = ⦇pair (F.map fst ≫ h) (F.map snd ≫ k)⦈ :=
  (pair_eq_relCata_pair_iff I ⦇h⦈ ⦇k⦈ (F.map fst ≫ h) (F.map snd ≫ k)).mp
    ⟨by rw [relCata_cancel I h, ← Cat.assoc, ← F.map_comp, fst_pair],
     by rw [relCata_cancel I k, ← Cat.assoc, ← F.map_comp, snd_pair]⟩

end Freyd.Alg
