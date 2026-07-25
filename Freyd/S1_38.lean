/-
  Freyd & Scedrov, *Categories and Allegories* §1.38–§1.399
  Duality, Stone duality, Finite presentation, Q-sequences.

  §1.38 DUALITY: a contravariant strong equivalence between categories.
  §1.389 STONE DUALITY: Boolean algebras ↔ Stone spaces.
  §1.392 FINITE PRESENTATION via Q-SEQUENCE: a category presented
         by a finite graph with composition/identity equations,
         plus the op-dual presentation and functor preserve/reflect.

  NOTE: the genuine §1.395 (quantified Q-sequence + satisfaction relation
  with ∀/∃ steps and complement = transpose-quantifiers) lives in S1_38b.lean.
  The "complementaryQSequence" / preserve-reflect lemmas below are the §1.392
  finite-presentation duality (reverse arrows, functor-image), NOT the §1.395
  quantifier transpose.
-/


import Freyd.S1_01
import Freyd.S1_18
import Freyd.S1_31
import Freyd.S1_41
import Freyd.S1_81


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞] {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-! ## §1.38 Duality

  A DUALITY between 𝒞 and 𝒟 is a contravariant strong equivalence.
  Concretely: a pair of contravariant functors F : 𝒞 → 𝒟 and G : 𝒟 → 𝒞
  such that G∘F ≅ Id_𝒞 (covariant natural iso) and F∘G ≅ Id_𝒟.

  Since contra∘contra = covariant, G∘F and F∘G carry covariant Functor
  instances (via `compContraFunctor` below), and `NatIso` from §1.31 applies. -/

/-- Composing two contravariant functors gives a covariant functor. -/
def compContraFunctor {ℰ : Type u} [Cat.{v} ℰ] (F : 𝒞 → 𝒟) (G : 𝒟 → ℰ)
    [hF : ContraFunctor F] [hG : ContraFunctor G] : Functor 𝒞 ℰ where
  obj X        := G (F X)
  map f        := hG.map (hF.map f)
  map_id X     := by rw [hF.map_id, hG.map_id]
  map_comp f g := by rw [hF.map_comp, hG.map_comp]

/-- A DUALITY between 𝒞 and 𝒟 (§1.38): a contravariant strong equivalence.
    F : 𝒞 → 𝒟 and G : 𝒟 → 𝒞 are both contravariant, with G∘F ≅ Id_𝒞 and
    F∘G ≅ Id_𝒟 as covariant natural isomorphisms. -/
structure Duality (F : 𝒞 → 𝒟) (G : 𝒟 → 𝒞)
    [ContraFunctor F] [ContraFunctor G] where
  unit   : Nonempty (NatIso (compContraFunctor F G) idFunctor)
  counit : Nonempty (NatIso (compContraFunctor G F) idFunctor)

/-! ## §1.389 Stone duality

  STONE DUALITY: the category of Boolean algebras is dual to the
  category of Stone spaces (compact Hausdorff totally disconnected).
  A STONE SPACE is a compact totally disconnected Hausdorff space. -/

/-- STONE SPACE (§1.389): compact, Hausdorff, totally disconnected.
    (Set-theoretic definition; we give a placeholder type.) -/
opaque StoneSpace : Type u

/- STONE DUALITY (§1.389): BoolAlg° ≅ Stone.  Placeholder — the `def` is
   omitted until `Cat StoneSpace` and the equivalence are formalized. -/

/-! ## §1.392 Finite presentation via Q-sequence

  A Q-SEQUENCE presents a category by generators (graph) and
  relations (equations on paths).  SATISFIES means the equations hold.

  FINITE PRESENTATION: a category given by a finite graph and
  finitely many equations. -/

/-- A Q-SEQUENCE (§1.392): a directed graph with equations. -/
structure QSequence where
  objects   : Type
  arrows    : Type
  src       : arrows → objects
  tgt       : arrows → objects
  equations : Type
  eq_lhs    : equations → List arrows
  eq_rhs    : equations → List arrows

/-! ### Path composition for Q-sequences

  A *path* in a Q-sequence is a list of arrows where each consecutive pair
  is composable: `Q.tgt aᵢ = Q.src aᵢ₊₁`.  Given an interpretation
  `interp : Q.objects → 𝒜` and `arrowMap a : interp (Q.src a) ⟶ interp (Q.tgt a)`,
  we lift a composable path to a single hom in `𝒜`.

  We carry the composability witness in the type, using a `Fin`-indexed
  family of composability proofs. -/

/-- A composable path in `Q`: a list of arrows together with the proof that
    consecutive endpoints match. -/
def ComposablePath (Q : QSequence) : List Q.arrows → Prop
  | []           => True
  | [_]          => True
  | a :: b :: rest => Q.tgt a = Q.src b ∧ ComposablePath Q (b :: rest)

/-- Lift a non-empty composable path to a morphism in `𝒜`. -/
def composeComposablePath {Q : QSequence} {𝒜 : Type u} [Cat.{v} 𝒜]
    (interp   : Q.objects → 𝒜)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a))
    : (path : List Q.arrows) → (h : path ≠ []) → ComposablePath Q path
    → interp (Q.src (path.head h)) ⟶ interp (Q.tgt (path.getLast h))
  | [a],            _,  _        => arrowMap a
  | a :: b :: rest, _, ⟨hab, hc⟩ =>
      arrowMap a ≫ (hab ▸ composeComposablePath interp arrowMap (b :: rest)
        (List.cons_ne_nil b rest) hc)

/-- SATISFIES a Q-sequence (§1.392): for every equation, both sides are composable
    paths with matching source and target in `Q`, and their compositions in `𝒜`
    agree (after transporting to the same type via the endpoint-matching proofs). -/
def SatisfiesQSequence (Q : QSequence) (𝒜 : Type u) [Cat.{v} 𝒜]
    (interp   : Q.objects → 𝒜)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a)) : Prop :=
  ∀ (e : Q.equations)
    (hlL : Q.eq_lhs e ≠ []) (hlR : Q.eq_rhs e ≠ [])
    (hcL : ComposablePath Q (Q.eq_lhs e)) (hcR : ComposablePath Q (Q.eq_rhs e))
    (hSrc : Q.src ((Q.eq_lhs e).head hlL) = Q.src ((Q.eq_rhs e).head hlR))
    (hTgt : Q.tgt ((Q.eq_lhs e).getLast hlL) = Q.tgt ((Q.eq_rhs e).getLast hlR)),
    -- Transport lhs to the type of rhs and compare
    hSrc ▸ hTgt ▸
      composeComposablePath interp arrowMap (Q.eq_lhs e) hlL hcL =
    composeComposablePath interp arrowMap (Q.eq_rhs e) hlR hcR

/-- OP-DUAL PRESENTATION (§1.392): dual by reversing arrows.
    NOTE: this is the presentation-level op-dual (reverse lhs↔rhs paths and
    src↔tgt), NOT the §1.395 complementary Q-sequence, which transposes the ∀/∃
    quantifiers (see `QSeq.complement` in S1_38b.lean). -/
def complementaryQSequence (Q : QSequence) : QSequence where
  objects   := Q.objects
  arrows    := Q.arrows
  src       := Q.tgt
  tgt       := Q.src
  equations := Q.equations
  eq_lhs  e := (Q.eq_rhs e).reverse
  eq_rhs  e := (Q.eq_lhs e).reverse

/-! ### §1.392 Functors preserve and reflect satisfaction (finite presentation)

  For a finitely-presented Q-sequence (§1.392), a functor preserves satisfaction,
  and an embedding reflects it.  In our object-centric formalization,
  the analogous statement is that a functor `F : 𝒜 → ℬ` that reflects equality
  (i.e., is an embedding) reflects satisfaction of Q-sequences under post-composition.

  The key technical ingredient is that functors distribute over `composeComposablePath`. -/

/-- A functor distributes over `composeComposablePath`: the composition of
    `F`-images equals the `F`-image of the composition. -/
private theorem functor_composeComposablePath
    {Q : QSequence} {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (F : Functor 𝒜 ℬ)
    (interp   : Q.objects → 𝒜)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a))
    : ∀ (path : List Q.arrows) (h : path ≠ []) (hc : ComposablePath Q path),
      F.map (composeComposablePath interp arrowMap path h hc) =
        composeComposablePath (F.obj ∘ interp) (fun a => F.map (arrowMap a)) path h hc
  | [_], _, _ => rfl
  | a :: b :: rest, _, hc => by
      obtain ⟨hab, hc'⟩ := hc
      simp only [composeComposablePath]
      rw [F.map_comp]
      congr 1
      -- Use the inductive hypothesis and then commute F.map with the ▸ transport
      have key := functor_composeComposablePath F interp arrowMap (b :: rest)
                    (List.cons_ne_nil _ _) hc'
      show F.map (hab ▸ composeComposablePath interp arrowMap (b :: rest)
                     (List.cons_ne_nil b rest) hc') =
           hab ▸ composeComposablePath (F.obj ∘ interp) (fun x => F.map (arrowMap x))
                   (b :: rest) (List.cons_ne_nil b rest) hc'
      rw [← key]
      exact hab.symm.rec rfl

/-- A functor commutes with double transport along object equalities: transporting the
    `F`-image equals the `F`-image of the transport.  Proved by `subst`-ing both equalities. -/
private theorem functor_dbl_transport
    {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (F : Functor 𝒜 ℬ)
    {P : Type} (interp : P → 𝒜)
    {x x' y y' : P} (hx : x = x') (hy : y = y')
    (f : interp x ⟶ interp y) :
    hx ▸ hy ▸ F.map f = F.map (hx ▸ hy ▸ f) := by
  subst hx; subst hy; rfl

/-- Embedding functors reflect satisfaction of a finitely-presented Q-sequence
    (§1.392).  We state this as: if `F : 𝒜 → ℬ` is an embedding,
    then satisfaction of a Q-sequence via `(F ∘ interp, F ∘ arrowMap)` implies (and
    is implied by) satisfaction via `(interp, arrowMap)`.

    The reflect direction (given here) uses `Embedding F` (injectivity on homs).
    The preserve direction is `iso_preserves_sat` below (functoriality alone suffices). -/
theorem iso_reflects_sat (Q : QSequence) {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (F : Functor 𝒜 ℬ)
    (hEmb : Embedding F)
    (interp   : Q.objects → 𝒜)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a))
    (sat : SatisfiesQSequence Q ℬ (F.obj ∘ interp) (fun a => F.map (arrowMap a))) :
    SatisfiesQSequence Q 𝒜 interp arrowMap := by
  intro e hlL hlR hcL hcR hSrc hTgt
  have heq := sat e hlL hlR hcL hcR hSrc hTgt
  simp only [← functor_composeComposablePath F interp arrowMap] at heq
  -- heq : hSrc ▸ hTgt ▸ F.map (compose interp lhs) = F.map (compose interp rhs)
  -- Goal : hSrc ▸ hTgt ▸ compose interp lhs = compose interp rhs
  -- Apply F-injectivity, then commute F.map with the double transport.
  apply hEmb
  rw [← functor_dbl_transport F interp hSrc hTgt]
  exact heq

/-- Any functor preserves satisfaction of a finitely-presented Q-sequence (§1.392): if `interp, arrowMap`
    satisfies the Q-sequence in `𝒜`, then `F ∘ interp, F ∘ arrowMap` satisfies it in `ℬ`.
    This is immediate from functoriality (F distributes over path composition). -/
theorem iso_preserves_sat (Q : QSequence) {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (F : Functor 𝒜 ℬ)
    (interp   : Q.objects → 𝒜)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a))
    (sat : SatisfiesQSequence Q 𝒜 interp arrowMap) :
    SatisfiesQSequence Q ℬ (F.obj ∘ interp) (fun a => F.map (arrowMap a)) := by
  intro e hlL hlR hcL hcR hSrc hTgt
  have heq := sat e hlL hlR hcL hcR hSrc hTgt
  simp only [← functor_composeComposablePath F interp arrowMap]
  -- Goal: hSrc ▸ hTgt ▸ F.map (compose interp lhs) = F.map (compose interp rhs)
  -- Commute F.map with the double transport, then apply `congrArg F.map heq`.
  rw [functor_dbl_transport F interp hSrc hTgt]
  exact congrArg F.map heq

/-! ## §1.396 Inflation-class morphisms preserve/reflect Q-sequences

  The book considers two classes of morphisms: `𝔹` (functors that separate objects)
  and `𝒜` (inflations).  The key condition is an orthogonal lift: for every commutative
  square with top in `𝔹` and right in `𝒜` there is a diagonal filler.  Under this
  condition, `𝒜`-morphisms preserve and reflect satisfaction of Q-sequences in `𝔹`
  (proof by induction on the Q-sequence length). -/

/-- A SEPARATES-OBJECTS functor: injective on objects (§1.396 context).
    A functor `T : 𝒞 → 𝒟` separates objects if `T A = T B → A = B`. -/
def SeparatesObjects (T : 𝒞 → 𝒟) : Prop :=
  Function.Injective T

/-- The DIAGONAL FILL condition between classes `𝔹` and `𝒜` (§1.396):
    for every commutative square with top `b : A₀ → A₁` in `𝔹` and right `a : B → B'`
    in `𝒜`, there exists a diagonal `A₁ → B`. -/
def DiagonalFillable
    (𝔹 : ∀ {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ] (_F : Functor 𝒜 ℬ), Prop)
    (𝒜cls : ∀ {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ] (_F : Functor 𝒜 ℬ), Prop) : Prop :=
  ∀ {𝒜₀ 𝒜₁ ℬ ℬ' : Type u} [Cat.{v} 𝒜₀] [Cat.{v} 𝒜₁] [Cat.{v} ℬ] [Cat.{v} ℬ']
    (b : Functor 𝒜₀ 𝒜₁) (a : Functor ℬ ℬ'),
    𝔹 b → 𝒜cls a → True  -- placeholder: existence of diagonal in the functor-category sense

/-- §1.396: Morphisms in `𝒜` preserve satisfaction of a Q-sequence in `𝔹` (forward direction).
    The full proof goes by induction on the Q-sequence length. -/
theorem inflation_class_preserves_sat
    (Q : QSequence) {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (T : Functor 𝒜 ℬ)
    (_hSep : SeparatesObjects T.obj)
    (interp   : Q.objects → 𝒜)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a))
    (sat : SatisfiesQSequence Q 𝒜 interp arrowMap) :
    SatisfiesQSequence Q ℬ (T.obj ∘ interp) (fun a => T.map (arrowMap a)) :=
  iso_preserves_sat Q T interp arrowMap sat

/-- §1.396: Morphisms in `𝒜` reflect satisfaction of a Q-sequence in `𝔹` (backward direction).
    The book reduces reflection to preservation of the complementary Q-sequence.
    Here we require `Embedding T` (the faithful case). -/
theorem inflation_class_reflects_sat
    (Q : QSequence) {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (T : Functor 𝒜 ℬ)
    (_hSep : SeparatesObjects T.obj)
    (hEmb : Embedding T)
    (interp   : Q.objects → 𝒜)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a))
    (sat : SatisfiesQSequence Q ℬ (T.obj ∘ interp) (fun a => T.map (arrowMap a))) :
    SatisfiesQSequence Q 𝒜 interp arrowMap :=
  iso_reflects_sat Q T hEmb interp arrowMap sat

/-! ## §1.397 Equivalence functors preserve/reflect Q-sequences

  An INFLATION CROSS-SECTION (§1.362) has `B₁ → B₂ ∈ 𝒜` and
  `B₁ → B₂ ↩ B₃ ∈ 𝒜`.  These preserve and reflect Q-sequences.
  Any equivalence functor (embedding + full + representative image)
  therefore preserves and reflects Q-sequences whose functors separate objects.

  (The book's proof in §1.397: cross-sections preserve/reflect by §1.396;
  compositions of such morphisms do too; by §1.361 every equivalence functor
  factors through inflations, so it preserves and reflects.) -/

/-- §1.397: An EQUIVALENCE FUNCTOR preserves satisfaction of a Q-sequence. -/
theorem equiv_preserves_sat (Q : QSequence) {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (T : Functor 𝒜 ℬ)
    (_hEquiv : EquivalenceFunctor T)
    (interp   : Q.objects → 𝒜)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a))
    (sat : SatisfiesQSequence Q 𝒜 interp arrowMap) :
    SatisfiesQSequence Q ℬ (T.obj ∘ interp) (fun a => T.map (arrowMap a)) :=
  iso_preserves_sat Q T interp arrowMap sat

/-- §1.397: An EQUIVALENCE FUNCTOR reflects satisfaction of a Q-sequence.
    (Uses only the `Embedding` component of `EquivalenceFunctor`.) -/
theorem equiv_reflects_sat (Q : QSequence) {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ]
    (T : Functor 𝒜 ℬ)
    (hEquiv : EquivalenceFunctor T)
    (interp   : Q.objects → 𝒜)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a))
    (sat : SatisfiesQSequence Q ℬ (T.obj ∘ interp) (fun a => T.map (arrowMap a))) :
    SatisfiesQSequence Q 𝒜 interp arrowMap :=
  iso_reflects_sat Q T hEquiv.1 interp arrowMap sat

/-! ## §1.398 Q-sequence classes closed under Cartesian products

  A Q-sequence of categories (beginning with the empty category) defines
  a *class of categories* — those `A` for which `∅ → A` satisfies the Q-sequence.
  This class is CLOSED UNDER CARTESIAN PRODUCTS: if both `A` and `B` satisfy
  then so does `A × B` (the product category).

  We first give the product category structure, then prove closure. -/

/-- The PRODUCT CATEGORY `𝒞 × 𝒟`: objects are pairs, morphisms are pairs of morphisms. -/
instance prodCat (𝒞 𝒟 : Type u) [Cat.{v} 𝒞] [Cat.{v} 𝒟] : Cat.{v} (𝒞 × 𝒟) where
  Hom p q        := (p.1 ⟶ q.1) × (p.2 ⟶ q.2)
  id p           := (Cat.id p.1, Cat.id p.2)
  comp f g       := (f.1 ≫ g.1, f.2 ≫ g.2)
  id_comp _      := Prod.ext (Cat.id_comp _) (Cat.id_comp _)
  comp_id _      := Prod.ext (Cat.comp_id _) (Cat.comp_id _)
  assoc _ _ _    := Prod.ext (Cat.assoc _ _ _) (Cat.assoc _ _ _)

/-- The first-projection functor `π₁ : 𝒞 × 𝒟 → 𝒞`. -/
def fstFunctor (𝒞 𝒟 : Type u) [Cat.{v} 𝒞] [Cat.{v} 𝒟] : Functor (𝒞 × 𝒟) 𝒞 where
  obj        := Prod.fst
  map f      := f.1
  map_id _   := rfl
  map_comp _ _ := rfl

/-- The second-projection functor `π₂ : 𝒞 × 𝒟 → 𝒟`. -/
def sndFunctor (𝒞 𝒟 : Type u) [Cat.{v} 𝒞] [Cat.{v} 𝒟] : Functor (𝒞 × 𝒟) 𝒟 where
  obj        := Prod.snd
  map f      := f.2
  map_id _   := rfl
  map_comp _ _ := rfl

/-- A Q-sequence-definable class of categories: `A` belongs iff the unique functor
    `∅ → A` satisfies the Q-sequence.  We represent this by a predicate. -/
def QDefinedClass (Q : QSequence) (𝒜 : Type u) [Cat.{v} 𝒜]
    (interp   : Q.objects → 𝒜)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a)) : Prop :=
  SatisfiesQSequence Q 𝒜 interp arrowMap

/-- `composeComposablePath` for the product interpretation decomposes as a pair (Prod.ext form).
    The fst component equals the C-path and snd equals the D-path, via the projection functors. -/
private theorem composeComposablePath_prod
    {Q : QSequence} {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    (interpC : Q.objects → 𝒞)
    (arrowMapC : (a : Q.arrows) → interpC (Q.src a) ⟶ interpC (Q.tgt a))
    (interpD : Q.objects → 𝒟)
    (arrowMapD : (a : Q.arrows) → interpD (Q.src a) ⟶ interpD (Q.tgt a))
    (path : List Q.arrows) (hn : path ≠ []) (hc : ComposablePath Q path) :
    composeComposablePath (fun o => (interpC o, interpD o))
      (fun a => (arrowMapC a, arrowMapD a)) path hn hc =
    (composeComposablePath interpC arrowMapC path hn hc,
     composeComposablePath interpD arrowMapD path hn hc) := by
  apply Prod.ext
  · -- fst: use the existing functor_composeComposablePath for fstFunctor
    have := functor_composeComposablePath (fstFunctor 𝒞 𝒟)
               (fun o => (interpC o, interpD o))
               (fun a => (arrowMapC a, arrowMapD a)) path hn hc
    -- this : fstFunctor.map (compose prod path) = compose (fstFunctor ∘ pair) (map ∘ pair) path
    -- fstFunctor.map f = f.1, so LHS = (compose prod path).1
    -- RHS: fstFunctor ∘ pair = interpC, map ∘ pair = arrowMapC
    exact this
  · -- snd: use sndFunctor
    have := functor_composeComposablePath (sndFunctor 𝒞 𝒟)
               (fun o => (interpC o, interpD o))
               (fun a => (arrowMapC a, arrowMapD a)) path hn hc
    exact this

/-- §1.398: If both `𝒞` and `𝒟` satisfy a Q-sequence (via interpretations),
    then the product category `𝒞 × 𝒟` satisfies it too.
    The interpretation maps to pairs component-wise. -/
theorem qseq_closed_under_product
    (Q : QSequence) {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    (interpC   : Q.objects → 𝒞)
    (arrowMapC : (a : Q.arrows) → interpC (Q.src a) ⟶ interpC (Q.tgt a))
    (interpD   : Q.objects → 𝒟)
    (arrowMapD : (a : Q.arrows) → interpD (Q.src a) ⟶ interpD (Q.tgt a))
    (satC : SatisfiesQSequence Q 𝒞 interpC arrowMapC)
    (satD : SatisfiesQSequence Q 𝒟 interpD arrowMapD) :
    SatisfiesQSequence Q (𝒞 × 𝒟)
      (fun o => (interpC o, interpD o))
      (fun a => (arrowMapC a, arrowMapD a)) := by
  intro e hlL hlR hcL hcR hSrc hTgt
  have hC := satC e hlL hlR hcL hcR hSrc hTgt
  have hD := satD e hlL hlR hcL hcR hSrc hTgt
  -- Use composeComposablePath_prod to rewrite both lhs and rhs paths.
  rw [composeComposablePath_prod interpC arrowMapC interpD arrowMapD _ hlL hcL,
      composeComposablePath_prod interpC arrowMapC interpD arrowMapD _ hlR hcR]
  -- Now goal: hSrc ▸ hTgt ▸ (pC, pD) = (qC, qD) in 𝒞 × 𝒟.
  -- Apply Prod.ext and use functor_dbl_transport to commute ▸ with .fst/.snd.
  apply Prod.ext
  · -- fst goal: (hSrc ▸ hTgt ▸ (pC, pD)).fst = (qC, qD).fst
    -- Use functor_dbl_transport for fstFunctor to relate (▸ (pC,pD)).fst and ▸ pC.
    have keyL := functor_dbl_transport (fstFunctor 𝒞 𝒟)
                   (fun o => (interpC o, interpD o)) hSrc hTgt
                   (composeComposablePath interpC arrowMapC (Q.eq_lhs e) hlL hcL,
                    composeComposablePath interpD arrowMapD (Q.eq_lhs e) hlL hcL)
    simp only [fstFunctor] at keyL
    -- keyL : hSrc ▸ hTgt ▸ pC = (hSrc ▸ hTgt ▸ (pC,pD)).fst
    exact keyL.symm.trans hC
  · have keyL := functor_dbl_transport (sndFunctor 𝒞 𝒟)
                   (fun o => (interpC o, interpD o)) hSrc hTgt
                   (composeComposablePath interpC arrowMapC (Q.eq_lhs e) hlL hcL,
                    composeComposablePath interpD arrowMapD (Q.eq_lhs e) hlL hcL)
    simp only [sndFunctor] at keyL
    exact keyL.symm.trans hD

/-! ## §1.399 Conjugate functors satisfy the same Q-sequences

  Two functors `F₁, F₂ : 𝒞 → 𝒟` are CONJUGATE if there is a natural isomorphism
  `α : NatIso F₁ F₂`.  §1.399 states: if `F₁` satisfies a property on diagrams
  preserved and reflected by equivalence functors, then so does `F₂`.

  In terms of Q-sequences: `A₀ → ℬ` satisfies iff `A₀ → ℬ' → ℬ` does (§1.396),
  and the conjugation construction in the book builds a mapping cylinder `ℬ'` so
  that `F₂ = F₁' ≫ inc` where `F₁' : 𝒞 → ℬ'` separates objects.
  The Lean statement says directly that if `F₁` satisfies a Q-sequence (via interp
  and arrowMap) and `α : NatIso F₁ F₂`, then `F₂` satisfies the same Q-sequence. -/

/-- A chosen inverse of the `X`-component of a natural isomorphism `α : NatIso F₁ F₂`.
    `α.nat.app X : F₁ X ⟶ F₂ X` is an iso (`α.isIso X`); `natIsoInv` is its inverse,
    going `F₂ X ⟶ F₁ X`.  (The inverse is only known to *exist*, so extracting it is
    the one unavoidable use of choice in §1.399.) -/
private noncomputable def natIsoInv {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    {F₁ F₂ : Functor 𝒞 𝒟} (α : NatIso F₁ F₂) (X : 𝒞) :
    F₂.obj X ⟶ F₁.obj X := (α.isIso X).choose

private theorem natIsoInv_left {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    {F₁ F₂ : Functor 𝒞 𝒟} (α : NatIso F₁ F₂) (X : 𝒞) :
    α.nat.app X ≫ natIsoInv α X = Cat.id (F₁.obj X) := (α.isIso X).choose_spec.1

private theorem natIsoInv_right {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    {F₁ F₂ : Functor 𝒞 𝒟} (α : NatIso F₁ F₂) (X : 𝒞) :
    natIsoInv α X ≫ α.nat.app X = Cat.id (F₂.obj X) := (α.isIso X).choose_spec.2

/-- Transport along an object equality `h : x = y` distributes over the conjugation pattern
    `αinv(interp y) ≫ M`: moving the source object `y` to `x` simply re-indexes the leading
    `αinv` and applies the same transport to the trailing morphism `M`.  Proved by `subst h`. -/
private theorem transp_natIsoInv_comp
    {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    {F₁ F₂ : Functor 𝒞 𝒟} (α : NatIso F₁ F₂)
    {P : Type} (interp : P → 𝒞) {x y : P} (h : x = y) {Z : 𝒟}
    (M : F₁.obj (interp y) ⟶ Z) :
    (h ▸ (natIsoInv α (interp y) ≫ M) : F₂.obj (interp x) ⟶ Z) =
      natIsoInv α (interp x) ≫ (h ▸ M : F₁.obj (interp x) ⟶ Z) := by
  subst h; rfl

/-- Transport along an object equality `h : x = y` (acting on the *source* of a morphism)
    passes through a right composition with a fixed `k` whose endpoints don't move. -/
private theorem transp_comp_right
    {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    {F₁ : Functor 𝒞 𝒟}
    {P : Type} (interp : P → 𝒞) {x y : P} (h : x = y) {W Z : 𝒟}
    (T : F₁.obj (interp y) ⟶ W) (k : W ⟶ Z) :
    (h ▸ (T ≫ k) : F₁.obj (interp x) ⟶ Z) = (h ▸ T : F₁.obj (interp x) ⟶ W) ≫ k := by
  subst h; rfl

/-- Naturality for the inverse of a natural isomorphism: `F₂(f) ≫ αinv = αinv ≫ F₁(f)`.
    Derived from naturality of `α` itself by cancelling the iso components. -/
private theorem natIsoInv_naturality
    {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    {F₁ F₂ : Functor 𝒞 𝒟} (α : NatIso F₁ F₂)
    {X Y : 𝒞} (f : X ⟶ Y) :
    F₂.map f ≫ natIsoInv α Y = natIsoInv α X ≫ F₁.map f := by
  have nat := α.nat.naturality f  -- F₁(f) ≫ α Y = α X ≫ F₂(f)
  calc F₂.map f ≫ natIsoInv α Y
        = (Cat.id (F₂.obj X) ≫ F₂.map f) ≫ natIsoInv α Y := by rw [Cat.id_comp]
      _ = ((natIsoInv α X ≫ α.nat.app X) ≫ F₂.map f) ≫ natIsoInv α Y := by
            rw [natIsoInv_right]
      _ = natIsoInv α X ≫ (α.nat.app X ≫ F₂.map f) ≫ natIsoInv α Y := by
            simp only [Cat.assoc]
      _ = natIsoInv α X ≫ (F₁.map f ≫ α.nat.app Y) ≫ natIsoInv α Y := by rw [nat]
      _ = natIsoInv α X ≫ F₁.map f ≫ (α.nat.app Y ≫ natIsoInv α Y) := by
            rw [Cat.assoc]
      _ = natIsoInv α X ≫ F₁.map f := by rw [natIsoInv_left, Cat.comp_id]

/-- Telescoping conjugation: the `F₂`-image of a composable path equals the `F₁`-image,
    pre/post-composed with the boundary components of `α` (its inverse at the source, and
    `α` itself at the target).  Proved by induction using naturality of `α`. -/
private theorem composeComposablePath_natIso
    {Q : QSequence} {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    {F₁ F₂ : Functor 𝒞 𝒟} (α : NatIso F₁ F₂)
    (interp   : Q.objects → 𝒞)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a))
    : ∀ (path : List Q.arrows) (h : path ≠ []) (hc : ComposablePath Q path),
      composeComposablePath (F₂.obj ∘ interp) (fun a => F₂.map (arrowMap a)) path h hc =
        natIsoInv α (interp (Q.src (path.head h)))
          ≫ composeComposablePath (F₁.obj ∘ interp) (fun a => F₁.map (arrowMap a)) path h hc
          ≫ α.nat.app (interp (Q.tgt (path.getLast h)))
  | [a], _, _ => by
      -- F₂(arrowMap a) = αinv ≫ F₁(arrowMap a) ≫ α  by naturality.
      show F₂.map (arrowMap a) =
        natIsoInv α (interp (Q.src a)) ≫ F₁.map (arrowMap a)
          ≫ α.nat.app (interp (Q.tgt a))
      have nat := α.nat.naturality (arrowMap a)
      -- nat : hF₁.map (arrowMap a) ≫ α.app (interp (tgt a)) = α.app (interp (src a)) ≫ hF₂.map (arrowMap a)
      rw [nat, ← Cat.assoc, natIsoInv_right, Cat.id_comp]
  | a :: b :: rest, _, ⟨hab, hc⟩ => by
      simp only [composeComposablePath]
      have ih := composeComposablePath_natIso α interp arrowMap (b :: rest)
                   (List.cons_ne_nil b rest) hc
      rw [ih]
      -- Reduce `(b::rest).head`/`(a::b::rest).head` to `b`/`a` so the boundary objects
      -- appear literally.
      simp only [List.head_cons]
      -- Push the composability transport `hab : Q.tgt a = Q.src b` through the conjugation
      -- pattern: `αinv` re-indexes to `interp (Q.tgt a)` and the tail transports.
      rw [transp_natIsoInv_comp α interp hab, transp_comp_right interp hab]
      -- Goal: F₂(a) ≫ (αinv(tgt a) ≫ (hab ▸ T₁) ≫ α) = αinv(src a) ≫ (F₁(a) ≫ (hab ▸ T₁)) ≫ α.
      -- Reassociate so the common `(hab ▸ T₁) ≫ α` suffix lines up, then use inverse-naturality.
      -- The `getLast` of `a::b::rest` and `b::rest` are definitionally equal, so `rfl` finishes.
      rw [← Cat.assoc, ← Cat.assoc, ← Cat.assoc, natIsoInv_naturality α (arrowMap a)]
      simp only [Cat.assoc]
      rfl

/-- Double transport commutes with the conjugation pattern `αinv(interp s) ≫ P ≫ α(interp t)`:
    transporting both boundary objects simply re-indexes the boundary isos and applies the
    same double transport to the middle morphism.  Proved by `subst`-ing both equalities. -/
private theorem conj_dbl_transport
    {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    {F₁ F₂ : Functor 𝒞 𝒟} (α : NatIso F₁ F₂)
    {P : Type} (interp : P → 𝒞) {s s' t t' : P} (hS : s = s') (hT : t = t')
    (M : F₁.obj (interp s) ⟶ F₁.obj (interp t)) :
    (hS ▸ hT ▸ (natIsoInv α (interp s) ≫ M ≫ α.nat.app (interp t)) :
        F₂.obj (interp s') ⟶ F₂.obj (interp t')) =
      natIsoInv α (interp s') ≫ (hS ▸ hT ▸ M : F₁.obj (interp s') ⟶ F₁.obj (interp t'))
        ≫ α.nat.app (interp t') := by
  subst hS; subst hT; rfl

/-- §1.399: Conjugate functors (connected by a natural isomorphism `α : NatIso F₁ F₂`) satisfy
    the same Q-sequences.  Forward direction: `F₁` satisfies → `F₂` satisfies.  The book builds
    a mapping cylinder; here we route through the telescoping conjugation `composeComposablePath_natIso`
    applied componentwise: each `F₂`-path equals the `F₁`-path conjugated by `α`'s boundary
    components, and the shared endpoints make the two sides of every equation conjugate by the
    *same* isos, so `sat₁` transfers. -/
theorem conjugate_satisfies_sat (Q : QSequence) {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    (F₁ F₂ : Functor 𝒞 𝒟)
    (α : NatIso F₁ F₂)
    (interp   : Q.objects → 𝒞)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a))
    (sat₁ : SatisfiesQSequence Q 𝒟 (F₁.obj ∘ interp) (fun a => F₁.map (arrowMap a))) :
    SatisfiesQSequence Q 𝒟 (F₂.obj ∘ interp) (fun a => F₂.map (arrowMap a)) := by
  intro e hlL hlR hcL hcR hSrc hTgt
  have h₁ := sat₁ e hlL hlR hcL hcR hSrc hTgt
  -- Express both F₂-paths as F₁-paths conjugated by α's boundary components.
  rw [composeComposablePath_natIso α interp arrowMap (Q.eq_lhs e) hlL hcL,
      composeComposablePath_natIso α interp arrowMap (Q.eq_rhs e) hlR hcR]
  -- Move the double transport across the lhs conjugation so the boundary isos match the rhs.
  rw [conj_dbl_transport α interp hSrc hTgt]
  -- Now both sides are `αinv(src_r) ≫ _ ≫ α(tgt_r)`; the middles are `h₁`-equal.
  rw [h₁]

/-- The inverse natural isomorphism `α⁻¹ : NatIso F₂ F₁` of `α : NatIso F₁ F₂`: components are
    the chosen inverses `natIsoInv α`, natural by `natIsoInv_naturality`, each an iso (inverse
    `α.nat.app`). -/
private noncomputable def natIsoSymm {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    {F₁ F₂ : Functor 𝒞 𝒟} (α : NatIso F₁ F₂) : NatIso F₂ F₁ where
  nat := { app := fun X => natIsoInv α X
           naturality := fun f => natIsoInv_naturality α f }
  isIso := fun X => ⟨α.nat.app X, natIsoInv_right α X, natIsoInv_left α X⟩

/-- §1.399 (converse): if `F₂` satisfies then `F₁` satisfies.  By symmetry of conjugation —
    apply the forward direction to the inverse natural isomorphism `natIsoSymm α : NatIso F₂ F₁`. -/
theorem conjugate_satisfies_sat_symm (Q : QSequence) {𝒞 𝒟 : Type u} [Cat.{v} 𝒞] [Cat.{v} 𝒟]
    (F₁ F₂ : Functor 𝒞 𝒟)
    (α : NatIso F₁ F₂)
    (interp   : Q.objects → 𝒞)
    (arrowMap : (a : Q.arrows) → interp (Q.src a) ⟶ interp (Q.tgt a))
    (sat₂ : SatisfiesQSequence Q 𝒟 (F₂.obj ∘ interp) (fun a => F₂.map (arrowMap a))) :
    SatisfiesQSequence Q 𝒟 (F₁.obj ∘ interp) (fun a => F₁.map (arrowMap a)) :=
  conjugate_satisfies_sat Q F₂ F₁ (natIsoSymm α) interp arrowMap sat₂

/-! ## §1.39 Linear order / finite presentation

  A LINEARLY ORDERED CATEGORY has objects totally ordered. -/

/-- A LINEARLY ORDERED CATEGORY (§1.39): objects form a totally ordered set. -/
class LinearlyOrdered (𝒞 : Type u) [Cat.{v} 𝒞] where
  order : 𝒞 → 𝒞 → Prop
  total : ∀ a b : 𝒞, order a b ∨ order b a

end Freyd
