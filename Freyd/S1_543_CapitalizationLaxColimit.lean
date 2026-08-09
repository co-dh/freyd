/-
  §1.543 — the FILTERED, PSEUDO-functorial colimit of categories (lax interface).

  ════════════════════════════════════════════════════════════════════════════════════════════
  WHY THIS FILE EXISTS — the precise diagnosis of the §1.543 capitalization wall, AND the route
  that resolves it.  §1.543 is now PROVEN Sorry-free (`Freyd.capitalization_lemma`): the lax
  interface built here is exactly what sidesteps the strict base-change obstruction below.
  ════════════════════════════════════════════════════════════════════════════════════════════

  The §1.547 relative capitalization needs `PreRegular A*`, where `A*` is the colimit of the
  finite-product slices `A/(∏U) = Over (listProd U)` over the FILTERED index `listDirected`
  (finite lists `U` of ws objects, ordered by `listSubset`; any two have an upper bound = append).
  Each fibre `Over (listProd U)` is PRE-REGULAR (`overPreRegular`, `SliceRegular.lean`).  The
  transitions are BASE-CHANGE `A/(∏V) → A/(∏U)` for `V ⊆ U` (`baseChangeFunctor` along a product
  projection `∏U ⟶ ∏V`).

  The repo's strict colimit machinery `Colim.CatSystem` / `colimitCat` / `colimitPreRegular`
  (`CatColimit.lean`, `CatColimitRegular.lean`) consumes ON-THE-NOSE transition laws:

      CatSystem.F_refl  : F (D.refl i) x = x                       -- strict identity
      CatSystem.F_trans : F (D.trans hij hjk) x = F hjk (F hij x)  -- strict composition

  **Base-change satisfies NEITHER.**  `baseChangeObj (Cat.id) X = X ×_D D` is canonically ISO to
  `X` but not equal; `baseChangeObj (g ≫ g')` re-associates an iterated pullback, equal only up to
  canonical iso.  This is residual (B-strict) of `RelativeCapitalization.lean`'s `innerCatSystem`,
  and it is documented there as the open obstruction (`StrictBaseChange` is a *false* statement for
  raw base-change, taken as a hypothesis the project could never discharge).

  The parked Σ-carrier attempt `CapitalizationGroth.lean` removes the OBJECT-CARRIER quotient
  dependency (objects become the bare `Σ i, A i` instead of the strict colimit's quotient), but it
  is still built on a `Colim.CatSystem` and a `Colim.CatSystem.Coherent` — so it STILL presupposes
  the strict `F_refl`/`F_trans`.  It does not escape residual (B-strict); it only escapes the
  carrier-quotient.

  ════════════════════════════════════════════════════════════════════════════════════════════
  THE WAY OUT — replace strict transition EQUALITIES with coherence ISOS (`NatIso`).
  ════════════════════════════════════════════════════════════════════════════════════════════

  A `LaxCatSystem` (this file) is a directed system of categories whose transitions are FUNCTORS
  with coherence supplied as natural ISOMORPHISMS

      F_refl_iso  : NatIso (F (D.refl i))            (id)
      F_trans_iso : NatIso (F (D.trans hij hjk))     (F hjk ∘ F hij)

  rather than strict equalities.  This is EXACTLY the data base-change supplies (it is a
  pseudofunctor `(listDirected)ᵒᵖ → Cat`), so the residual (B-strict) wall evaporates: there is no
  false equation to discharge, only canonical pullback isos to build.

  This file delivers, SORRY-FREE:
    * `LaxCatSystem` — the pseudo-functorial directed-system interface (the missing abstraction).
    * its underlying object Σ-carrier and directed colimit of object-types (reusing
      `DirectedColimit.lean`, which needs NO transition laws on objects — `incl` is the bare
      Σ-injection up to germ equivalence, and germ equivalence only ever uses transition *maps*,
      never their strict laws).
    * `ofStrict` — every strict `Colim.CatSystem` is a `LaxCatSystem` (the lax interface
      generalises the strict one; coherence isos are the identity NatIso), so nothing is lost.

  AND the PSEUDO hom-colimit + the `Cat` instance `laxColimCat : Cat (Obj L)` (relative to the
  pseudofunctor coherence `Coherent L`): a morphism `⟨i,x⟩ → ⟨j,y⟩` is a germ of
  `Hom_{A k}(F_{ik} x, F_{jk} y)` over upper bounds `k`, with germ equivalence transported along the
  COHERENCE ISOS (`pushHom`, the iso-conjugation analogue of the strict `castHom`).  The remaining
  work (documented `next blocker` at the end) is to discharge `Coherent` for base-change (the
  pullback unit/pentagon coherence) — stated precisely below.

  Mathlib-free; built on the repo's own `Cat`, `Functor`, `NaturalTransformation`, `NatIso`,
  `IsIso`, and `Freyd.Colim` (`DirectedColimit.lean`).
-/
module

public import Freyd.S1_31
public import Freyd.S1_36
public import Freyd.S1_41
public import Freyd.S1_543_DirectedColimit
public import Freyd.S1_543_CatColimit
public import Freyd.S1_53_SliceRegular

open Freyd
open Freyd.Colim

namespace Freyd.LaxColim

universe u w

variable {ι : Type u} {D : Directed ι}

/-! ## The pseudo-functorial (lax) directed system of categories

  Identical OBJECT/`Cat`/FUNCTOR data to `Colim.CatSystem`, but the two coherence fields are
  natural ISOMORPHISMS instead of strict equalities.  `functF hij : Functor (F hij)` makes each
  transition a genuine functor; `F_refl_iso`/`F_trans_iso` are the pseudofunctor coherences. -/
/-- The object/`Cat`/transition-functor data of a lax directed system (no coherences yet):
    the object map `F` and morphism map `Fmap` of each transition, with the two functor laws.
    Split out from `LaxCatSystem` so the bundled transition functor `functF` can be defined
    before the pseudofunctor coherence isos that mention it. -/
public structure LaxCatSystemData (ι : Type u) (D : Directed ι) where
  /-- the stage categories' carriers -/
  A : ι → Type w
  /-- each stage is a category -/
  catA : ∀ i, Cat.{w} (A i)
  /-- the object map of each transition -/
  F : ∀ {i j}, D.le i j → A i → A j
  /-- the morphism map of each transition -/
  Fmap : ∀ {i j} (hij : D.le i j) {x y : A i},
    @Cat.Hom (A i) (catA i) x y → @Cat.Hom (A j) (catA j) (F hij x) (F hij y)
  Fmap_id : ∀ {i j} (hij : D.le i j) (x : A i),
    Fmap hij (@Cat.id (A i) (catA i) x) = @Cat.id (A j) (catA j) (F hij x)
  Fmap_comp : ∀ {i j} (hij : D.le i j) {x y z : A i}
    (f : @Cat.Hom (A i) (catA i) x y) (g : @Cat.Hom (A i) (catA i) y z),
    Fmap hij (@Cat.comp (A i) (catA i) x y z f g)
      = @Cat.comp (A j) (catA j) (F hij x) (F hij y) (F hij z) (Fmap hij f) (Fmap hij g)

attribute [instance] LaxCatSystemData.catA

/-- The transition functor `A i → A j` as a bundled `Functor` (object action `F`, morphism
    action `Fmap`); the pseudofunctor coherence isos below are stated over it. -/
@[expose] public def LaxCatSystemData.functF (S : LaxCatSystemData ι D) {i j} (hij : D.le i j) :
    Functor (S.A i) (S.A j) where
  obj := S.F hij
  map := S.Fmap hij
  map_id := S.Fmap_id hij
  map_comp := S.Fmap_comp hij

/-- A directed system of categories with pseudofunctor (lax) coherences: the same object/functor
    data as `Colim.CatSystem`, but the two coherence fields are natural ISOMORPHISMS instead of
    strict equalities.  `functF hij` makes each transition a genuine functor; `F_refl_iso`/
    `F_trans_iso` are the pseudofunctor coherences. -/
public structure LaxCatSystem (ι : Type u) (D : Directed ι) extends LaxCatSystemData ι D where
  /-- pseudo-identity: the reflexive transition is naturally isomorphic to the identity functor -/
  F_refl_iso : ∀ {i}, NatIso (toLaxCatSystemData.functF (D.refl i)) (@idFunctor (A i) (catA i))
  /-- pseudo-composition: a composite transition is naturally isomorphic to the composite of the
      two transition functors -/
  F_trans_iso : ∀ {i j k} (hij : D.le i j) (hjk : D.le j k),
    NatIso (toLaxCatSystemData.functF (D.trans hij hjk))
      (compFunctor (toLaxCatSystemData.functF hij) (toLaxCatSystemData.functF hjk))

/-! ## The object carrier of the pseudo-colimit: the bare Σ-type

  For a FILTERED colimit of categories the objects are the bare `Σ i, A i` — NO quotient.  (Two
  representatives that become isomorphic at a common bound are *isomorphic in the colimit category*,
  but they are kept as distinct objects; the colimit category is not skeletal.)  This is the same
  carrier as `CapitalizationGroth.lean`'s `SigmaObj`, but here it costs nothing: it needs no
  transition laws at all, so it is well-defined for a LAX system where the object-level `F_refl`/
  `F_trans` are only isos.  Contrast the STRICT `Colim.CatSystem.Obj`, a quotient of `Σ i, A i` by
  germ equivalence, whose well-definedness uses the strict `F_refl`/`F_trans` (`DirectedColimit`'s
  `System.tr_refl`/`tr_trans`) — exactly the laws base-change lacks. -/
@[expose] public abbrev Obj (S : LaxCatSystem.{u, w} ι D) : Type _ := Σ i, S.A i

/-- The cocone inclusion `A i → Σ i, A i` is the bare injection. -/
@[expose] public def objIncl (S : LaxCatSystem ι D) (i : ι) (x : S.A i) : Obj S := ⟨i, x⟩

/-! ## A natural iso from a pointwise object-equality of two functors

  Given functors `F G : 𝒜 → ℬ` whose object maps agree pointwise (`∀ x, F x = G x`) AND whose
  morphism maps match under the induced `eqToHom` conjugation, the family of `eqToHom` arrows is a
  natural isomorphism `F ≅ G`.  This is the bridge that turns the STRICT `CatSystem.F_refl`/
  `F_trans` *equalities* into the LAX `F_refl_iso`/`F_trans_iso` *isos*, proving the lax interface
  genuinely generalises the strict one (`ofStrict`).  Built on the repo's `eqToHom` (§1.36). -/
section PointwiseNatIso

variable {𝒜 ℬ : Type w} [Cat.{w} 𝒜] [Cat.{w} ℬ]

/-- **Pointwise object-equality ⟹ natural iso.**  If two functors agree on objects pointwise and
    their morphism maps satisfy the `eqToHom` conjugation `G.map f = eqToHom (hpt X).symm ≫ F.map f
    ≫ eqToHom (hpt Y)`, the `eqToHom` family is a `NatIso F G`. -/
def natIsoOfPointwise {F G : Functor 𝒜 ℬ}
    (hpt : ∀ x, F.obj x = G.obj x)
    (hmap : ∀ {X Y : 𝒜} (f : X ⟶ Y),
      G.map f = eqToHom (hpt X).symm ≫ F.map f ≫ eqToHom (hpt Y)) :
    NatIso F G where
  nat :=
    { app X := eqToHom (hpt X)
      naturality {X Y} f := by
        -- goal: `F.map f ≫ eqToHom (hpt Y) = eqToHom (hpt X) ≫ G.map f`.  Expand `G.map f` by
        -- `hmap`, then collapse `eqToHom (hpt X) ≫ eqToHom (hpt X).symm = id` on the RHS.
        rw [hmap f, ← Cat.assoc (eqToHom (hpt X)), eqToHom_comp_eqToHom_symm, Cat.id_comp] }
  isIso X := ⟨eqToHom (hpt X).symm, eqToHom_comp_eqToHom_symm _, eqToHom_symm_comp_eqToHom _⟩

/-- A `HEq` between two morphisms over equal endpoints is the `eqToHom` conjugation.  This converts
    the STRICT system's morphism-coherence (`CatSystem.Coherent.refl_map`/`trans_map`, stated with
    `HEq`) into the `hmap` hypothesis `natIsoOfPointwise` needs. -/
theorem heq_eqToHom_conj {A B A' B' : ℬ} (hA : A = A') (hB : B = B')
    {m : A ⟶ B} {m' : A' ⟶ B'} (h : HEq m m') :
    m' = eqToHom hA.symm ≫ m ≫ eqToHom hB := by
  cases hA; cases hB
  simp only [eqToHom_refl, Cat.id_comp, Cat.comp_id]
  exact (eq_of_heq h).symm

end PointwiseNatIso

/-! ## Every strict `Colim.CatSystem` is a `LaxCatSystem`

  The lax interface generalises the strict one: the object data, `Cat`, and transition functors are
  carried over verbatim, and the strict `F_refl`/`F_trans` *equalities* yield the coherence *isos*
  via `natIsoOfPointwise` (the morphism-level `hmap` comes from `Coherent.refl_map`/`trans_map`
  through `heq_eqToHom_conj`).  So nothing is lost in moving to the lax setting — and base-change,
  which is NOT a strict `CatSystem`, will still be a `LaxCatSystem`. -/
noncomputable def ofStrict (C : Colim.CatSystem.{u, w} ι D) (hC : C.Coherent) :
    LaxCatSystem.{u, w} ι D where
  A := C.A
  catA := C.catA
  F := @C.F
  Fmap := @C.Fmap
  Fmap_id := @C.Fmap_id
  Fmap_comp := @C.Fmap_comp
  F_refl_iso {i} := natIsoOfPointwise (F := C.functF (D.refl i)) (G := @idFunctor (C.A i) (C.catA i))
    (fun x => C.F_refl x)
    (fun {X Y} f =>
      -- `idFunctor.map f = f`; `Coherent.refl_map f : HEq ((functF refl).map f) f` conjugates.
      heq_eqToHom_conj (C.F_refl X) (C.F_refl Y) (hC.refl_map f))
  F_trans_iso {_i _j _k} hij hjk := natIsoOfPointwise
    (F := C.functF (D.trans hij hjk))
    (G := compFunctor (C.functF hij) (C.functF hjk))
    (fun x => C.F_trans hij hjk x)
    (fun {X Y} f =>
      heq_eqToHom_conj (C.F_trans hij hjk X) (C.F_trans hij hjk Y) (hC.trans_map hij hjk f))

/-! ## The §1.547 base-change slice system as a `LaxCatSystem`

  Here is the payoff for §1.547.  The inner directed system of finite-product slices `A/(∏U)` over
  the filtered index `listDirected`, with BASE-CHANGE transitions (`RelativeCapitalization.lean`'s
  `innerObj`/`innerF`/`innerFunctF`), CANNOT be a strict `Colim.CatSystem` — its
  `StrictBaseChange` hypothesis is a *false* statement for raw base-change (`baseChangeObj (id) X =
  X ×_D D ≠ X` on the nose).  But it IS a `LaxCatSystem`: the coherence isos are the canonical
  pullback isomorphisms, which DO exist.

  We phrase this abstractly over any directed product-projection system so it is reusable and
  imports only the light `SliceRegular` (not the heavy `Capitalization` chain): a `ProjSystem` is a
  `Directed ι` together with stage products `pr i` and a strictly-coherent projection family
  `proj`.  Its base-change object/functor data is Sorry-free; the two pseudo-coherence isos are the
  genuine remaining content, isolated as honest TRUE obligations in `PseudoBaseChange` (no false
  equation — unlike `StrictBaseChange`, these isos really hold). -/
section BaseChangeLax

variable {𝒞 : Type w} [Cat.{w} 𝒞] [HasPullbacks 𝒞]

/-- A directed system of "products with projections": stage objects `pr i`, and for every
    `i ≤ j` a projection `pr j ⟶ pr i` (the bigger product onto the smaller), strictly coherent
    (`Cat.id` on `refl`, composite on `trans`).  This abstracts §1.547's `ListProjFamily` over
    `listDirected`; the projections ARE constructible (the only obstruction to a concrete instance
    is `DecidableEq 𝒞` for positional matching, orthogonal to the colimit construction here). -/
public structure ProjSystem (ι : Type u) (D : Directed ι) (𝒞 : Type w) [Cat.{w} 𝒞] where
  /-- the stage product object `∏(stage i)` -/
  pr : ι → 𝒞
  /-- the projection `∏j ⟶ ∏i` for `i ≤ j` -/
  proj : ∀ {i j}, D.le i j → (pr j ⟶ pr i)
  /-- strict unit: the reflexive projection is the identity -/
  proj_refl : ∀ i, proj (D.refl i) = Cat.id (pr i)
  /-- strict composition (note the contravariance: `i ≤ j ≤ k` gives `∏k ⟶ ∏i` two ways) -/
  proj_trans : ∀ {i j k} (hij : D.le i j) (hjk : D.le j k),
    proj (D.trans hij hjk) = proj hjk ≫ proj hij

variable {ι : Type u} {D : Directed ι}

/-- Stage `i` of the base-change system: the slice `A/(pr i) = Over (pr i)`. -/
@[expose] public abbrev pcObj (P : ProjSystem ι D 𝒞) (i : ι) : Type w := Over (P.pr i)

/-- The base-change transition object map `A/(pr i) → A/(pr j)` along the projection `proj : pr j
    ⟶ pr i` (for `i ≤ j`): `X ↦ X ×_{pr i} pr j`.  Sorry-free (`baseChangeObj`). -/
@[expose] public def pcF (P : ProjSystem ι D 𝒞) {i j} (h : D.le i j) : pcObj P i → pcObj P j :=
  baseChangeObj (P.proj h)

/-- The base-change transition is a functor (Sorry-free, `baseChangeFunctor`). -/
@[expose] public def pcFunctF (P : ProjSystem ι D 𝒞) {i j} (h : D.le i j) :
    @Functor (pcObj P i) (pcObj P j) (overCat (P.pr i)) (overCat (P.pr j)) :=
  baseChangeFunctor (P.proj h)

/-! ### The reflexive coherence iso is REAL — `baseChangeObj (id) ≅ id`

  Demonstration that `PseudoBaseChange.refl_iso` is genuinely inhabitable (not a renamed wall): the
  pullback of any `X.hom` along the identity is canonically `X`.  The per-object iso `X ≅
  baseChangeObj (Cat.id C) X` is built from the pullback universal property; the inverse pair is
  `lift`/`π₁`, and `π₁ ≫ lift = id` follows from `lift_uniq`.  This is the harder of the two
  obligations' EASY half; the composite (`trans_iso`, pullback pasting) remains the next blocker. -/
section BaseChangeIdIso

variable {C : 𝒞}

@[expose] public def _idPB (X : Over C) : HasPullback X.hom (Cat.id C) := HasPullbacks.has X.hom (Cat.id C)

/-- The cone `⟨X.dom, id, X.hom⟩` over the cospan `(X.hom, id_C)`. -/
private def _idCone (X : Over C) : Cone X.hom (Cat.id C) :=
  ⟨X.dom, Cat.id X.dom, X.hom, by rw [Cat.id_comp, Cat.comp_id]⟩

/-- The forward arrow `X ⟶ baseChangeObj (id) X`: the lift of `_idCone` into the pullback.  Its
    over-`C` triangle is `lift ≫ π₂ = X.hom` (`lift_snd`). -/
private def _idFwd (X : Over C) : OverHom X (baseChangeObj (Cat.id C) X) :=
  ⟨(_idPB X).lift (_idCone X), (_idPB X).lift_snd (_idCone X)⟩

/-- The backward arrow `baseChangeObj (id) X ⟶ X`: the first projection `π₁`.  Its over-`C` triangle
    is `π₁ ≫ X.hom = π₂` from the pullback square `w` (since the other leg is `id_C`). -/
@[expose] public def _idBwd (X : Over C) : OverHom (baseChangeObj (Cat.id C) X) X :=
  ⟨(_idPB X).cone.π₁, by
    show (_idPB X).cone.π₁ ≫ X.hom = (_idPB X).cone.π₂
    have := (_idPB X).cone.w; rw [Cat.comp_id] at this; exact this⟩

/-- `_idBwd` is an iso, with inverse `_idFwd`: back-then-forward is `id` by `lift_fst`; forward-
    then-back is `id` by pullback uniqueness (`lift_uniq`, the identity cone's lift is `id`). -/
public theorem _idBwd_isIso (X : Over C) : @IsIso (Over C) _ _ _ (_idBwd X) := by
  refine ⟨_idFwd X, ?_, ?_⟩
  · -- `_idBwd ⊚ _idFwd = id_{baseChangeObj}` ⟺ `π₁ ≫ lift = id_pt`, by `lift_uniq`.
    apply OverHom.ext
    show (_idPB X).cone.π₁ ≫ (_idPB X).lift (_idCone X) = Cat.id _
    -- both `π₁ ≫ lift` and `id_pt` lift the self-cone `⟨pt, π₁, π₂⟩`, so they are equal.
    let selfCone : Cone X.hom (Cat.id C) :=
      ⟨(_idPB X).cone.pt, (_idPB X).cone.π₁, (_idPB X).cone.π₂, (_idPB X).cone.w⟩
    have h1 : (_idPB X).cone.π₁ ≫ (_idPB X).lift (_idCone X) = (_idPB X).lift selfCone := by
      refine (_idPB X).lift_uniq selfCone _ ?_ ?_
      · rw [Cat.assoc, (_idPB X).lift_fst (_idCone X)]; show (_idPB X).cone.π₁ ≫ Cat.id _ = _
        rw [Cat.comp_id]
      · rw [Cat.assoc, (_idPB X).lift_snd (_idCone X)]
        show (_idPB X).cone.π₁ ≫ X.hom = (_idPB X).cone.π₂
        have := (_idPB X).cone.w; rw [Cat.comp_id] at this; exact this
    have h2 : Cat.id (_idPB X).cone.pt = (_idPB X).lift selfCone :=
      (_idPB X).lift_uniq selfCone (Cat.id _) (by rw [Cat.id_comp]) (by rw [Cat.id_comp])
    rw [h1, ← h2]
  · -- `_idFwd ⊚ _idBwd = id_X` ⟺ `lift ≫ π₁ = id_{X.dom}` (`lift_fst` of `_idCone`).
    apply OverHom.ext
    show (_idPB X).lift (_idCone X) ≫ (_idPB X).cone.π₁ = Cat.id X.dom
    exact (_idPB X).lift_fst (_idCone X)

/-- **`baseChangeObj (Cat.id C) ≅ id` as a `NatIso`.**  Components are `_idBwd` (= `π₁`, iso by
    `_idBwd_isIso`); naturality is the pullback square `w` (`π₁` commutes with the base-change map's
    `π₁`-leg, which is `lift_fst`).  This proves `PseudoBaseChange.refl_iso` is genuinely
    inhabitable — the reflexive coherence iso is NOT a hidden wall. -/
@[expose] public def baseChangeIdNatIso : NatIso (baseChangeFunctor (Cat.id C)) (@idFunctor (Over C) _) where
  nat :=
    { app := _idBwd
      naturality {X Y} m := by
        -- `baseChangeMap (id) m ⊚ _idBwd Y = _idBwd X ⊚ m`, i.e. on arrows
        -- `(lift (baseChangeCone m)) ≫ π₁ʸ = π₁ˣ ≫ m.f`, which is exactly `lift_fst`.
        apply OverHom.ext
        show ((_idPB Y).lift (baseChangeCone (Cat.id C) m)) ≫ (_idPB Y).cone.π₁
          = (_idPB X).cone.π₁ ≫ m.f
        rw [(_idPB Y).lift_fst (baseChangeCone (Cat.id C) m)]; rfl }
  isIso := _idBwd_isIso

end BaseChangeIdIso

/-! ### The composite coherence iso is REAL — pullback pasting `baseChangeObj (g' ≫ g) ≅ baseChangeObj g' ∘ baseChangeObj g`

  The pullback-pasting lemma plus `isIso_of_two_pullbacks` (§1.43) gives the iterated-pullback
  natural iso.  With base maps `g : C ⟶ D`, `g' : E ⟶ C` (diagram-order, so `g' ≫ g : E ⟶ D`):
  pulling `X.hom` back along `g' ≫ g` is canonically iso to pulling back along `g` then `g'`.  This
  discharges `PseudoBaseChange.trans_iso`; needs only `HasPullbacks 𝒞`, NO choice. -/
section BaseChangeTransIso

variable {D C E : 𝒞} (g : C ⟶ D) (g' : E ⟶ C)

/-- **Pullback pasting.**  If the inner square (cone `c1` over `(h, g)`) is a pullback and the outer
    square (cone `c2` over `(c1.π₂, g')`) is a pullback, then the composite cone
    `⟨c2.pt, c2.π₁ ≫ c1.π₁, c2.π₂⟩` over `(h, g' ≫ g)` is a pullback.  The classic two-pullback
    pasting lemma (left + right square pullbacks ⇒ outer rectangle pullback). -/
public theorem pasteCone_isPullback {X : 𝒞} {h : X ⟶ D}
    {c1 : Cone h g} (hc1 : c1.IsPullback)
    {c2 : Cone c1.π₂ g'} (hc2 : c2.IsPullback) :
    (Cone.mk (f := h) (g := g' ≫ g) c2.pt (c2.π₁ ≫ c1.π₁) c2.π₂
      (by rw [Cat.assoc, c1.w, ← Cat.assoc, c2.w, Cat.assoc])).IsPullback := by
  intro d
  -- d : cone over (h, g' ≫ g): d.π₁ ≫ h = d.π₂ ≫ (g' ≫ g).
  -- Step 1: (d.π₁, d.π₂ ≫ g') is a cone over (h, g), lift into c1 ⇒ e : d.pt ⟶ c1.pt.
  have hw1 : d.π₁ ≫ h = (d.π₂ ≫ g') ≫ g := by rw [d.w, Cat.assoc]
  obtain ⟨e, ⟨he₁, he₂⟩, huniq1⟩ := hc1 (Cone.mk d.pt d.π₁ (d.π₂ ≫ g') hw1)
  -- Step 2: (e, d.π₂) is a cone over (c1.π₂, g') (he₂ : e ≫ c1.π₂ = d.π₂ ≫ g'), lift into c2.
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hc2 (Cone.mk d.pt e d.π₂ he₂)
  refine ⟨u, ⟨?_, hu₂⟩, ?_⟩
  · -- u ≫ (c2.π₁ ≫ c1.π₁) = d.π₁
    rw [← Cat.assoc, hu₁, he₁]
  · -- uniqueness: any v with v ≫ (c2.π₁ ≫ c1.π₁) = d.π₁ and v ≫ c2.π₂ = d.π₂ equals u.
    intro v hv₁ hv₂
    -- v ≫ c2.π₁ lifts the c1-cone (d.π₁, d.π₂ ≫ g'), hence equals e by uniqueness in c1.
    have hve : v ≫ c2.π₁ = e :=
      huniq1 (v ≫ c2.π₁) (by rw [Cat.assoc]; exact hv₁)
        (by show (v ≫ c2.π₁) ≫ c1.π₂ = d.π₂ ≫ g'
            calc (v ≫ c2.π₁) ≫ c1.π₂ = v ≫ (c2.π₁ ≫ c1.π₂) := Cat.assoc _ _ _
              _ = v ≫ (c2.π₂ ≫ g') := congrArg (v ≫ ·) c2.w
              _ = (v ≫ c2.π₂) ≫ g' := (Cat.assoc _ _ _).symm
              _ = d.π₂ ≫ g' := congrArg (· ≫ g') hv₂)
    -- then v lifts the c2-cone (e, d.π₂), hence equals u.
    exact huniq v hve hv₂

/-! ### From pasting to the `trans` natural iso

  `baseChangeObj g X` is, definitionally, the chosen pullback of `X.hom` along `g`.  We abbreviate
  that chosen pullback as `_pb`.  The LHS `baseChangeObj (g' ≫ g) X` and the pasted RHS
  `baseChangeObj g' (baseChangeObj g X)` are two pullbacks of the SAME cospan `(X.hom, g' ≫ g)`
  (by `pasteCone_isPullback`), so they are canonically iso (`isIso_of_two_pullbacks`). -/

/-- The chosen pullback of `X.hom` along a base map, matching `baseChangeObj`'s internal choice. -/
@[expose] public def _pb (g : C ⟶ D) (X : Over D) : HasPullback X.hom g := HasPullbacks.has X.hom g

/-- The pasted RHS cone `baseChangeObj g' (baseChangeObj g X)`, viewed as a cone over the composite
    cospan `(X.hom, g' ≫ g)`, is a pullback. -/
private theorem _rhsPasted (X : Over D) :
    (Cone.mk (f := X.hom) (g := g' ≫ g)
      (_pb g' (baseChangeObj g X)).cone.pt
      ((_pb g' (baseChangeObj g X)).cone.π₁ ≫ (_pb g X).cone.π₁)
      (_pb g' (baseChangeObj g X)).cone.π₂
      (by
        have hc1 := (_pb g X).cone.w
        have hc2 := (_pb g' (baseChangeObj g X)).cone.w
        calc ((_pb g' (baseChangeObj g X)).cone.π₁ ≫ (_pb g X).cone.π₁) ≫ X.hom
            = (_pb g' (baseChangeObj g X)).cone.π₁ ≫ ((_pb g X).cone.π₁ ≫ X.hom) := Cat.assoc _ _ _
          _ = (_pb g' (baseChangeObj g X)).cone.π₁ ≫ ((_pb g X).cone.π₂ ≫ g) :=
                congrArg ((_pb g' (baseChangeObj g X)).cone.π₁ ≫ ·) hc1
          _ = ((_pb g' (baseChangeObj g X)).cone.π₁ ≫ (_pb g X).cone.π₂) ≫ g := (Cat.assoc _ _ _).symm
          _ = ((_pb g' (baseChangeObj g X)).cone.π₂ ≫ g') ≫ g := congrArg (· ≫ g) hc2
          _ = (_pb g' (baseChangeObj g X)).cone.π₂ ≫ (g' ≫ g) := Cat.assoc _ _ _)).IsPullback :=
  pasteCone_isPullback g g'
    (h := X.hom) ((_pb g X).cone_isPullback) ((_pb g' (baseChangeObj g X)).cone_isPullback)

/-! The forward comparison map is built CONSTRUCTIVELY from the chosen pullbacks' `lift` (no
    `Classical.choice` on the `IsPullback` existential): first lift the LHS cone into the inner
    pullback `(_pb g X)` to get `_qInner : (LHS X).dom ⟶ (bc g X).dom`, then lift `(_qInner,
    (LHS X).π₂)` into the outer pullback `(_pb g' (bc g X))`. -/

/-- The inner factorization `(LHS X).dom ⟶ (bc g X).dom`: the lift of `((LHS X).π₁, (LHS X).π₂ ≫ g')`
    through the inner pullback `(_pb g X)` (cone over `(X.hom, g)`). -/
private def _qInner (X : Over D) : (baseChangeObj (g' ≫ g) X).dom ⟶ (baseChangeObj g X).dom :=
  (_pb g X).lift (Cone.mk (f := X.hom) (g := g) (baseChangeObj (g' ≫ g) X).dom
    ((_pb (g' ≫ g) X).cone.π₁) ((_pb (g' ≫ g) X).cone.π₂ ≫ g')
    (by rw [(_pb (g' ≫ g) X).cone.w, Cat.assoc]))

private theorem _qInner_fst (X : Over D) :
    _qInner g g' X ≫ (_pb g X).cone.π₁ = (_pb (g' ≫ g) X).cone.π₁ :=
  (_pb g X).lift_fst _

private theorem _qInner_snd (X : Over D) :
    _qInner g g' X ≫ (_pb g X).cone.π₂ = (_pb (g' ≫ g) X).cone.π₂ ≫ g' :=
  (_pb g X).lift_snd _

/-- The forward comparison map `(baseChangeObj (g' ≫ g) X).dom ⟶ (baseChangeObj g' (baseChangeObj g
    X)).dom`: the lift of `(_qInner, (LHS X).π₂)` through the outer pullback `(_pb g' (bc g X))`. -/
private def _transFwdf (X : Over D) :
    (baseChangeObj (g' ≫ g) X).dom ⟶ (baseChangeObj g' (baseChangeObj g X)).dom :=
  (_pb g' (baseChangeObj g X)).lift
    (Cone.mk (f := (baseChangeObj g X).hom) (g := g') (baseChangeObj (g' ≫ g) X).dom
      (_qInner g g' X) ((_pb (g' ≫ g) X).cone.π₂)
      (by show _qInner g g' X ≫ (_pb g X).cone.π₂ = (_pb (g' ≫ g) X).cone.π₂ ≫ g'
          exact _qInner_snd g g' X))

private theorem _transFwd_π₂ (X : Over D) :
    _transFwdf g g' X ≫ (_pb g' (baseChangeObj g X)).cone.π₂ = (_pb (g' ≫ g) X).cone.π₂ :=
  (_pb g' (baseChangeObj g X)).lift_snd _

private theorem _transFwd_outer_fst (X : Over D) :
    _transFwdf g g' X ≫ (_pb g' (baseChangeObj g X)).cone.π₁ = _qInner g g' X :=
  (_pb g' (baseChangeObj g X)).lift_fst _

private theorem _transFwd_π₁ (X : Over D) :
    _transFwdf g g' X ≫ ((_pb g' (baseChangeObj g X)).cone.π₁ ≫ (_pb g X).cone.π₁)
      = (_pb (g' ≫ g) X).cone.π₁ := by
  -- `_transFwdf ≫ (_pb g' ..).π₁ = _qInner` (lift_fst); then `_qInner ≫ (_pb g X).π₁ = (LHS).π₁`.
  rw [← Cat.assoc, _transFwd_outer_fst g g' X]
  exact _qInner_fst g g' X

/-- The forward comparison as a slice arrow `baseChangeObj (g' ≫ g) X ⟶ baseChangeObj g'
    (baseChangeObj g X)`.  Its `π₂`-leg is the over-`pr k` triangle, which is `_transFwd_π₂`
    (recall the structure map of both slice objects is `π₂`). -/
private def _transFwd (X : Over D) :
    OverHom (baseChangeObj (g' ≫ g) X) (baseChangeObj g' (baseChangeObj g X)) :=
  ⟨_transFwdf g g' X, _transFwd_π₂ g g' X⟩

/-- The forward comparison is iso: it is the comparison of two pullbacks of `(X.hom, g' ≫ g)` —
    the LHS chosen pullback and the pasted RHS pullback — so `isIso_of_two_pullbacks` applies. -/
private theorem _transFwd_isIso (X : Over D) : OverIso (_transFwd g g' X) :=
  overIso_of_underlying _
    (isIso_of_two_pullbacks ((_pb (g' ≫ g) X).cone_isPullback) (_rhsPasted g g' X)
      (_transFwdf g g' X) (_transFwd_π₁ g g' X) (_transFwd_π₂ g g' X))

/-- Naturality of the forward comparison, at the level of underlying arrows: for `m : OverHom X Y`,
    `(baseChangeMap (g' ≫ g) m).f ≫ _transFwdf Y = _transFwdf X ≫ (baseChangeMap g' (baseChangeMap g
    m)).f`.  Both sides factor the same cone through the RHS pasted pullback of `Y`, so they agree by
    `lift_uniq`.  The shared cone has legs `((_pb (g'≫g) X).π₁ ≫ m.f, (_pb (g'≫g) X).π₂)` over the
    pasted projections `((_pb g' (bc g Y)).π₁ ≫ (_pb g Y).π₁, (_pb g' (bc g Y)).π₂)`. -/
private theorem _transFwd_natf {X Y : Over D} (m : OverHom X Y) :
    (baseChangeMap (g' ≫ g) m).f ≫ _transFwdf g g' Y
      = _transFwdf g g' X ≫ (baseChangeMap g' (baseChangeMap g m)).f := by
  -- It suffices that both sides agree after post-composing with the two pasted projections of `Y`,
  -- since the pasted cone of `Y` is a pullback (`_rhsPasted ... Y`).  Apply that uniqueness to the
  -- shared cone `d` with legs `((_pb (g'≫g) X).π₁ ≫ m.f, (_pb (g'≫g) X).π₂)` over `(Y.hom, g'≫g)`.
  have hdw : ((_pb (g' ≫ g) X).cone.π₁ ≫ m.f) ≫ Y.hom
      = (_pb (g' ≫ g) X).cone.π₂ ≫ (g' ≫ g) := by
    calc ((_pb (g' ≫ g) X).cone.π₁ ≫ m.f) ≫ Y.hom
        = (_pb (g' ≫ g) X).cone.π₁ ≫ (m.f ≫ Y.hom) := Cat.assoc _ _ _
      _ = (_pb (g' ≫ g) X).cone.π₁ ≫ X.hom := congrArg ((_pb (g' ≫ g) X).cone.π₁ ≫ ·) m.w
      _ = (_pb (g' ≫ g) X).cone.π₂ ≫ (g' ≫ g) := (_pb (g' ≫ g) X).cone.w
  obtain ⟨_, _, huniq⟩ := (_rhsPasted g g' Y)
    (Cone.mk (f := Y.hom) (g := g' ≫ g) (baseChangeObj (g' ≫ g) X).dom
      ((_pb (g' ≫ g) X).cone.π₁ ≫ m.f) ((_pb (g' ≫ g) X).cone.π₂) hdw)
  -- `baseChangeMap`'s `.f` projected against the relevant pullback legs (term-typed so they `rw`).
  have hg_fst : (baseChangeMap g m).f ≫ (_pb g Y).cone.π₁ = (_pb g X).cone.π₁ ≫ m.f :=
    (_pb g Y).lift_fst (baseChangeCone g m)
  have hg'_fst : (baseChangeMap g' (baseChangeMap g m)).f ≫ (_pb g' (baseChangeObj g Y)).cone.π₁
      = (_pb g' (baseChangeObj g X)).cone.π₁ ≫ (baseChangeMap g m).f :=
    (_pb g' (baseChangeObj g Y)).lift_fst (baseChangeCone g' (baseChangeMap g m))
  have hg'_snd : (baseChangeMap g' (baseChangeMap g m)).f ≫ (_pb g' (baseChangeObj g Y)).cone.π₂
      = (_pb g' (baseChangeObj g X)).cone.π₂ :=
    (_pb g' (baseChangeObj g Y)).lift_snd (baseChangeCone g' (baseChangeMap g m))
  refine (huniq ((baseChangeMap (g' ≫ g) m).f ≫ _transFwdf g g' Y) ?rl1 ?rl2).trans
    (huniq (_transFwdf g g' X ≫ (baseChangeMap g' (baseChangeMap g m)).f) ?ll1 ?ll2).symm
  case ll1 =>
    -- π₁ leg: (_transFwdf X ≫ (bc g' (bc g m)).f) ≫ (p₁ʸ) = (_pb (g'≫g) X).π₁ ≫ m.f
    calc (_transFwdf g g' X ≫ (baseChangeMap g' (baseChangeMap g m)).f)
            ≫ ((_pb g' (baseChangeObj g Y)).cone.π₁ ≫ (_pb g Y).cone.π₁)
        = _transFwdf g g' X ≫ (((baseChangeMap g' (baseChangeMap g m)).f
            ≫ (_pb g' (baseChangeObj g Y)).cone.π₁) ≫ (_pb g Y).cone.π₁) := by
          simp only [Cat.assoc]
      _ = _transFwdf g g' X ≫ (((_pb g' (baseChangeObj g X)).cone.π₁ ≫ (baseChangeMap g m).f)
            ≫ (_pb g Y).cone.π₁) := by rw [hg'_fst]
      _ = _transFwdf g g' X ≫ ((_pb g' (baseChangeObj g X)).cone.π₁
            ≫ ((baseChangeMap g m).f ≫ (_pb g Y).cone.π₁)) := by rw [Cat.assoc]
      _ = _transFwdf g g' X ≫ ((_pb g' (baseChangeObj g X)).cone.π₁
            ≫ ((_pb g X).cone.π₁ ≫ m.f)) := by rw [hg_fst]
      _ = (_transFwdf g g' X ≫ ((_pb g' (baseChangeObj g X)).cone.π₁ ≫ (_pb g X).cone.π₁)) ≫ m.f := by
          simp only [Cat.assoc]
      _ = (_pb (g' ≫ g) X).cone.π₁ ≫ m.f := by rw [_transFwd_π₁ g g' X]
  case ll2 =>
    calc (_transFwdf g g' X ≫ (baseChangeMap g' (baseChangeMap g m)).f)
            ≫ (_pb g' (baseChangeObj g Y)).cone.π₂
        = _transFwdf g g' X
            ≫ ((baseChangeMap g' (baseChangeMap g m)).f ≫ (_pb g' (baseChangeObj g Y)).cone.π₂) :=
          Cat.assoc _ _ _
      _ = _transFwdf g g' X ≫ (_pb g' (baseChangeObj g X)).cone.π₂ := by rw [hg'_snd]
      _ = (_pb (g' ≫ g) X).cone.π₂ := _transFwd_π₂ g g' X
  case rl1 =>
    calc ((baseChangeMap (g' ≫ g) m).f ≫ _transFwdf g g' Y)
            ≫ ((_pb g' (baseChangeObj g Y)).cone.π₁ ≫ (_pb g Y).cone.π₁)
        = (baseChangeMap (g' ≫ g) m).f ≫ (_transFwdf g g' Y
            ≫ ((_pb g' (baseChangeObj g Y)).cone.π₁ ≫ (_pb g Y).cone.π₁)) := Cat.assoc _ _ _
      _ = (baseChangeMap (g' ≫ g) m).f ≫ (_pb (g' ≫ g) Y).cone.π₁ := by
          rw [_transFwd_π₁ g g' Y]
      _ = (_pb (g' ≫ g) X).cone.π₁ ≫ m.f :=
          (_pb (g' ≫ g) Y).lift_fst (baseChangeCone (g' ≫ g) m)
  case rl2 =>
    calc ((baseChangeMap (g' ≫ g) m).f ≫ _transFwdf g g' Y)
            ≫ (_pb g' (baseChangeObj g Y)).cone.π₂
        = (baseChangeMap (g' ≫ g) m).f ≫ (_transFwdf g g' Y
            ≫ (_pb g' (baseChangeObj g Y)).cone.π₂) := Cat.assoc _ _ _
      _ = (baseChangeMap (g' ≫ g) m).f ≫ (_pb (g' ≫ g) Y).cone.π₂ := by
          rw [_transFwd_π₂ g g' Y]
      _ = (_pb (g' ≫ g) X).cone.π₂ := (_pb (g' ≫ g) Y).lift_snd (baseChangeCone (g' ≫ g) m)

/-- **The composite coherence iso of base-change, over arbitrary composable base maps.**
    `baseChangeObj (g' ≫ g) ≅ baseChangeObj g' ∘ baseChangeObj g` as a `NatIso` (natural in `X`):
    the iterated-pullback / pullback-pasting isomorphism.  Components are `_transFwd` (iso by
    `_transFwd_isIso`); naturality is `_transFwd_natf` (pullback-lift uniqueness). -/
public def baseChangeTransNatIso :
    NatIso (baseChangeFunctor (g' ≫ g))
      (compFunctor (baseChangeFunctor g) (baseChangeFunctor g')) where
  nat :=
    { app := _transFwd g g'
      naturality {_ _} m := OverHom.ext (_transFwd_natf g g' m) }
  isIso := _transFwd_isIso g g'

-- Public `.f`-leg characterisation of the composite coherence iso.
-- `baseChangeTransNatIso g g' X` has underlying comparison arrow `_transFwdf g g' X`
-- (the iterated-/pasted-pullback comparison).  The lemmas below expose how it interacts with the
-- chosen pullback projections, stated entirely in PUBLIC terms (`HasPullbacks.has _ _` — exactly what
-- the private `_pb` abbreviates — and `baseChangeObj`).  Downstream §1.546 descent code consumes them.

/-- The underlying comparison arrow of `baseChangeTransNatIso g g' X` is `_transFwdf g g' X`. -/
theorem baseChangeTransNatIso_app_f (X : Over D) :
    ((baseChangeTransNatIso g g').nat.app X).f = _transFwdf g g' X := rfl

/-- **`π₂`-leg of the composite coherence comparison.**  The comparison sends the outer (structure)
    projection of the pasted RHS pullback to the LHS structure projection. -/
theorem baseChangeTransNatIso_app_f_π₂ (X : Over D) :
    ((baseChangeTransNatIso g g').nat.app X).f
        ≫ (HasPullbacks.has (baseChangeObj g X).hom g').cone.π₂
      = (HasPullbacks.has X.hom (g' ≫ g)).cone.π₂ :=
  _transFwd_π₂ g g' X

/-- **`π₁ ≫ π₁`-leg of the composite coherence comparison.**  The comparison sends the deep
    (content) projection of the pasted RHS pullback — outer `π₁` then inner `π₁` — to the LHS
    content projection. -/
public theorem baseChangeTransNatIso_app_f_π₁ (X : Over D) :
    ((baseChangeTransNatIso g g').nat.app X).f
        ≫ ((HasPullbacks.has (baseChangeObj g X).hom g').cone.π₁
            ≫ (HasPullbacks.has X.hom g).cone.π₁)
      = (HasPullbacks.has X.hom (g' ≫ g)).cone.π₁ :=
  _transFwd_π₁ g g' X

/-- **mixed `π₁ ≫ π₂`-leg of the composite coherence comparison.**  Outer `π₁` then inner `π₂` of the
    pasted RHS pullback equals the LHS structure projection post-composed with `g'`. -/
theorem baseChangeTransNatIso_app_f_π₁π₂ (X : Over D) :
    ((baseChangeTransNatIso g g').nat.app X).f
        ≫ ((HasPullbacks.has (baseChangeObj g X).hom g').cone.π₁
            ≫ (HasPullbacks.has X.hom g).cone.π₂)
      = (HasPullbacks.has X.hom (g' ≫ g)).cone.π₂ ≫ g' := by
  show _transFwdf g g' X ≫ _ = _
  rw [← Cat.assoc, _transFwd_outer_fst g g' X]; exact _qInner_snd g g' X

end BaseChangeTransIso

/-- **The composite coherence iso of base-change.**  Unlike `StrictBaseChange` (a FALSE equation
    taken as a hypothesis), this is the canonical iterated-pullback isomorphism, which genuinely
    exists:

      `trans_iso` : `baseChangeObj (g' ≫ g) ≅ baseChangeObj g' ∘ baseChangeObj g`
                    — pullback pasting / iterated-pullback iso.

    BOTH coherence isos are now DISCHARGED, Sorry-free and axiom-free: `projReflIso` (reflexive,
    transport of `baseChangeIdNatIso`) and `projTransIso` (composite, transport of
    `baseChangeTransNatIso`, the pullback-pasting iso `pasteCone_isPullback` + `isIso_of_two_pullbacks`).
    So `PseudoBaseChange` is inhabited UNCONDITIONALLY (`pseudoBaseChange`), and `laxOfProjSystem'`
    builds the §1.543 inner base-change `LaxCatSystem` outright (no hypothesis to discharge). -/
public structure PseudoBaseChange (P : ProjSystem ι D 𝒞) where
  trans_iso : ∀ {i j k : ι} (hij : D.le i j) (hjk : D.le j k),
    NatIso (pcFunctF P (D.trans hij hjk))
      (compFunctor (pcFunctF P hij) (pcFunctF P hjk))

/-- **The reflexive coherence iso of ANY base-change projection system is real.**  Transporting
    `baseChangeIdNatIso` along `P.proj_refl i : P.proj (D.refl i) = Cat.id (pr i)` discharges the
    `refl_iso` field for every `ProjSystem` — Sorry-free.  So `PseudoBaseChange` reduces to its
    `trans_iso` field alone: the reflexive half is NOT a blocker. -/
@[expose] public def projReflIso (P : ProjSystem ι D 𝒞) (i : ι) :
    NatIso (pcFunctF P (D.refl i)) (@idFunctor (pcObj P i) (overCat (P.pr i))) := by
  -- `pcF P (D.refl i) = baseChangeObj (P.proj (D.refl i))`; rewrite the projection to `id`.
  show NatIso (baseChangeFunctor (P.proj (D.refl i))) (@idFunctor (Over (P.pr i)) _)
  rw [P.proj_refl i]
  exact baseChangeIdNatIso

/-- **The composite coherence iso of ANY base-change projection system is real.**  Transporting
    `baseChangeTransNatIso` along `P.proj_trans hij hjk : P.proj (D.trans hij hjk) = P.proj hjk ≫
    P.proj hij` discharges the `trans_iso` field for every `ProjSystem` — Sorry-free.  This is the
    pullback-pasting natural iso, instantiated at the projection composite.  So `PseudoBaseChange` is
    inhabited UNCONDITIONALLY (`pseudoBaseChange`): neither coherence half is a blocker. -/
@[expose] public def projTransIso (P : ProjSystem ι D 𝒞) {i j k : ι} (hij : D.le i j) (hjk : D.le j k) :
    NatIso (pcFunctF P (D.trans hij hjk))
      (compFunctor (pcFunctF P hij) (pcFunctF P hjk)) := by
  -- `pcF P (D.trans hij hjk) = baseChangeObj (P.proj (D.trans hij hjk))`; rewrite the projection to
  -- the composite `P.proj hjk ≫ P.proj hij` and apply `baseChangeTransNatIso`.
  show NatIso (baseChangeFunctor (P.proj (D.trans hij hjk)))
    (compFunctor (baseChangeFunctor (P.proj hij)) (baseChangeFunctor (P.proj hjk)))
  rw [P.proj_trans hij hjk]
  exact baseChangeTransNatIso (P.proj hij) (P.proj hjk)

/-- **`PseudoBaseChange` is inhabited for every projection system**, Sorry-free: both coherence
    isos (`projReflIso`, `projTransIso`) are the canonical pullback isos, which genuinely exist.
    This turns `laxOfProjSystem` into an UNCONDITIONAL construction — the §1.543 inner base-change
    slice system is a `LaxCatSystem` with no hypothesis to discharge. -/
@[expose] public def pseudoBaseChange (P : ProjSystem ι D 𝒞) : PseudoBaseChange P where
  trans_iso := fun hij hjk => projTransIso P hij hjk

/-- **The §1.547 base-change slice system as a `LaxCatSystem`.**  Given the directed projection
    system `P` and its (TRUE) pseudo-coherence isos `H`, the finite-product slices `A/(pr i)` with
    base-change transitions form a `LaxCatSystem` — Sorry-free.  This is the lax analogue of
    `Freyd.innerCatSystem`, but WITHOUT the false `StrictBaseChange` input: the coherence is carried
    by genuine isos.  THIS is the construction the strict `Colim.CatSystem` could not host. -/
@[expose] public def laxOfProjSystem (P : ProjSystem ι D 𝒞) (H : PseudoBaseChange P) : LaxCatSystem.{u, w} ι D where
  A := pcObj P
  catA := fun i => overCat (P.pr i)
  F := fun h => pcF P h
  Fmap := fun h => (pcFunctF P h).map
  Fmap_id := fun h => (pcFunctF P h).map_id
  Fmap_comp := fun h => (pcFunctF P h).map_comp
  F_refl_iso := fun {i} => projReflIso P i
  F_trans_iso := fun hij hjk => H.trans_iso hij hjk

/-- **The §1.547 base-change slice system as a `LaxCatSystem`, UNCONDITIONALLY.**  Since
    `pseudoBaseChange P` supplies the coherence isos for free (both `projReflIso` and `projTransIso`
    are real pullback isos), no `PseudoBaseChange` hypothesis is needed: every `ProjSystem` yields a
    `LaxCatSystem` outright.  This closes the §1.543 wall for the base-change inner system — the
    documented blocker (`PseudoBaseChange.trans_iso`, the pullback-pasting iso) is discharged. -/
@[expose] public def laxOfProjSystem' (P : ProjSystem ι D 𝒞) : LaxCatSystem.{u, w} ι D :=
  laxOfProjSystem P (pseudoBaseChange P)

end BaseChangeLax

/-! ## The PSEUDO hom-colimit — morphisms of `LaxColim L`

  A morphism `⟨i,x⟩ → ⟨j,y⟩` is a germ of `Hom_{L.A k}(L.F (i≤k) x, L.F (j≤k) y)` over the upper
  bounds `k ≥ i,j`, quotiented by agreement at a common higher bound.  The strict construction
  (`CatColimit.lean`'s `HomColim`) re-types the pushed morphism along the STRICT object equalities
  `F_refl`/`F_trans` using `castHom`.  Here the objects only agree UP TO the coherence isos
  `F_refl_iso`/`F_trans_iso`, so `castHom` (transport along an *equality*) is replaced by
  CONJUGATION by the coherence-iso components — the lax `pushHom`.

  This section isolates, Sorry-free, the lax hom-transition `pushHom` and the EXACT coherence
  obligations its functoriality (`pushHom_refl`/`pushHom_trans`) demands — which are precisely the
  pseudofunctor UNIT and ASSOCIATIVITY coherences the bare `LaxCatSystem` does not yet carry. -/
section LaxHom

variable (L : LaxCatSystem.{u, w} ι D)

/-- The chosen inverse of an iso (the `NatIso`/`IsIso` field is a `Prop`-existential, so extracting
    the inverse arrow as data is necessarily noncomputable — this is an interface limitation of the
    `IsIso := ∃ g, …` encoding, not a use of choice on mathematical content). -/
@[expose] public noncomputable def isoInv {𝒜 : Type w} [Cat.{w} 𝒜] {X Y : 𝒜} {f : X ⟶ Y} (h : IsIso f) : Y ⟶ X :=
  Classical.choose h

public theorem isoInv_comp {𝒜 : Type w} [Cat.{w} 𝒜] {X Y : 𝒜} {f : X ⟶ Y} (h : IsIso f) :
    f ≫ isoInv h = Cat.id X := (Classical.choose_spec h).1

public theorem inv_isoInv_comp {𝒜 : Type w} [Cat.{w} 𝒜] {X Y : 𝒜} {f : X ⟶ Y} (h : IsIso f) :
    isoInv h ≫ f = Cat.id Y := (Classical.choose_spec h).2

/-- The forward component of the `trans` coherence iso at an object, `F (trans hik hkm) x ⟶
    F hkm (F hik x)`: the "source coercion" that the pushed morphism's domain needs. -/
@[expose] public def transApp {i k m : ι} (hik : D.le i k) (hkm : D.le k m) (x : L.A i) :
    L.F (D.trans hik hkm) x ⟶ L.F hkm (L.F hik x) :=
  (L.F_trans_iso hik hkm).nat.app x

public theorem transApp_isIso {i k m : ι} (hik : D.le i k) (hkm : D.le k m) (x : L.A i) :
    IsIso (transApp L hik hkm x) :=
  (L.F_trans_iso hik hkm).isIso x

/-- **Naturality of the `trans` coherence component.**  `transApp L hkm hmn (·)` is the component
    of the natural iso `F_trans_iso hkm hmn`, so for any `f : X ⟶ Y` in `L.A k` it intertwines the
    composite transition `F (trans hkm hmn)` with the iterated `F hmn ∘ F hkm`.  (Stated in the
    abstract section so all `Functor`/`compFunctor` instances are supplied explicitly — avoids the
    `compFunctor` instance-head synthesis trap inside the base-change namespace.) -/
public theorem transApp_natural {k m n : ι} (hkm : D.le k m) (hmn : D.le m n)
    {X Y : L.A k} (f : X ⟶ Y) :
    (L.functF (D.trans hkm hmn)).map f ≫ transApp L hkm hmn Y
    = transApp L hkm hmn X
      ≫ (compFunctor (L.functF hkm) (L.functF hmn)).map f :=
  (L.F_trans_iso hkm hmn).nat.naturality f

/-- The lax hom-transition (the pseudo analogue of `castHom`-based `homTr`).  Given a stage-`k`
    morphism `g : F hik x ⟶ F hjk y` and `hkm : k ≤ m`, push it to a morphism
    `F (trans hik hkm) x ⟶ F (trans hjk hkm) y` at level `m`, by mapping along `F hkm` and
    CONJUGATING by the two `trans` coherence isos (forward on the source, inverse on the target). -/
@[expose] public noncomputable def pushHom {i j : ι} (x : L.A i) (y : L.A j) {k m : ι}
    (hik : D.le i k) (hjk : D.le j k) (hkm : D.le k m)
    (g : L.F hik x ⟶ L.F hjk y) :
    L.F (D.trans hik hkm) x ⟶ L.F (D.trans hjk hkm) y :=
  transApp L hik hkm x
    ≫ (L.functF hkm).map g
    ≫ isoInv (transApp_isIso L hjk hkm y)

/-- `pushHom` distributes over composition — the iso-conjugation analogue of `homTr_comp`.  The
    middle coherence iso `inv (transApp y) ≫ transApp y = id` cancels, and `map (f ≫ g) = map f ≫
    map g`.  PROVEN from the bare structure — needs NO pseudofunctor coherence. -/
public theorem pushHom_comp {i j l : ι} (x : L.A i) (y : L.A j) (z : L.A l) {k m : ι}
    (hik : D.le i k) (hjk : D.le j k) (hlk : D.le l k) (hkm : D.le k m)
    (f : L.F hik x ⟶ L.F hjk y) (g : L.F hjk y ⟶ L.F hlk z) :
    pushHom L x z hik hlk hkm (f ≫ g)
      = pushHom L x y hik hjk hkm f ≫ pushHom L y z hjk hlk hkm g := by
  unfold pushHom
  rw [(L.functF hkm).map_comp f g]
  -- collapse `inv (transApp y) ≫ transApp y = id` in the middle.
  simp only [Cat.assoc]
  rw [← Cat.assoc (isoInv (transApp_isIso L hjk hkm y)), inv_isoInv_comp, Cat.id_comp]

/-- **The source-naturality characterisation of `pushHom`** (the decisive Phase-1 primitive).  By
    construction `pushHom g = transApp x ≫ map g ≫ inv (transApp y)`, so post-composing with the
    target collapse iso `transApp y` cancels its inverse, leaving `transApp x ≫ map g`.  This is the
    clean equation that lets one COMPUTE `(pushHom g)` (and hence its `.f` underlying arrow) WITHOUT
    unfolding `isoInv`: the two collapse isos `transApp x`, `transApp y` are the concrete pullback
    comparison isos, whose `.f` legs are characterised by the `transApp_f_*` lemmas. -/
public theorem pushHom_transApp {i j : ι} (x : L.A i) (y : L.A j) {k m : ι}
    (hik : D.le i k) (hjk : D.le j k) (hkm : D.le k m)
    (g : L.F hik x ⟶ L.F hjk y) :
    pushHom L x y hik hjk hkm g ≫ transApp L hjk hkm y
      = transApp L hik hkm x
        ≫ (L.functF hkm).map g := by
  unfold pushHom
  rw [Cat.assoc, Cat.assoc, inv_isoInv_comp, Cat.comp_id]

/-- `pushHom` preserves identities — the analogue of `homTr_id`.  `map id = id`, then `transApp x ≫
    inv (transApp x) = id`.  PROVEN from the bare structure — needs NO pseudofunctor coherence. -/
public theorem pushHom_id {i : ι} (x : L.A i) {k m : ι} (hik : D.le i k) (hkm : D.le k m) :
    pushHom L x x hik hik hkm (Cat.id (L.F hik x)) = Cat.id (L.F (D.trans hik hkm) x) := by
  unfold pushHom
  rw [(L.functF hkm).map_id]
  rw [show (Cat.id ((L.functF hkm).obj (L.F hik x)) : L.F hkm (L.F hik x) ⟶ _)
        ≫ isoInv (transApp_isIso L hik hkm x) = isoInv (transApp_isIso L hik hkm x)
      from Cat.id_comp _]
  exact isoInv_comp _

/-! ### Pseudofunctor coherence of the lax hom-transition

  The bare `LaxCatSystem` carries the coherence isos `F_refl_iso`/`F_trans_iso` but NO laws relating
  them (no pseudofunctor unit/associativity / triangle / pentagon).  The hom-colimit needs exactly
  the two laws that make `pushHom` behave like the strict `homTr`: pushing along `refl` is the
  identity, and pushing along a composite bound is pushing twice.  These are the pseudofunctor UNIT
  and ASSOCIATIVITY coherences expressed directly on hom-sets.

  Unlike the STRICT `CatSystem.Coherent` (a `HEq` statement that is *false* for raw base-change),
  these are TRUE for base-change — they are the standard pullback-pasting coherences.  We isolate
  them here as a hypothesis (`Coherent`); the whole hom-colimit `Cat` is built relative to it.
  `Coherent` for `laxOfProjSystem'` (base-change) — the pullback pentagon — is now DISCHARGED
  Sorry-free as `coherentProj` (below), so §1.543 is proven and nothing here is deferred. -/
public structure Coherent (L : LaxCatSystem.{u, w} ι D) : Prop where
  /-- UNIT: pushing a stage-`k` morphism along the reflexive bound `k ≤ k` is the identity.
      (Type-correct because `D.trans hik (D.refl k) = hik` by proof irrelevance of `D.le`.) -/
  push_refl : ∀ {i j : ι} (x : L.A i) (y : L.A j) {k : ι}
    (hik : D.le i k) (hjk : D.le j k) (g : L.F hik x ⟶ L.F hjk y),
    pushHom L x y hik hjk (D.refl k) g = g
  /-- ASSOCIATIVITY: pushing along a composite bound `k ≤ m ≤ n` equals pushing to `m` then to `n`.
      (Type-correct because `D.trans hik (D.trans hkm hmn) = D.trans (D.trans hik hkm) hmn`.) -/
  push_trans : ∀ {i j : ι} (x : L.A i) (y : L.A j) {k m n : ι}
    (hik : D.le i k) (hjk : D.le j k) (hkm : D.le k m) (hmn : D.le m n)
    (g : L.F hik x ⟶ L.F hjk y),
    pushHom L x y hik hjk (D.trans hkm hmn) g
      = pushHom L x y (D.trans hik hkm) (D.trans hjk hkm) hmn (pushHom L x y hik hjk hkm g)

/-! ### Object-level nested-`F` collapse isos (Phase 1 (i))

  `transApp L hik hkm x : F (trans hik hkm) x ⟶ F hkm (F hik x)` is the BINARY object collapse iso.
  For a three-step bound `i ≤ b ≤ c ≤ d` we want the analogous iso
  `F (trans (trans hib hbc) hcd) x ⟶ F hcd (F hbc (F hib x))`, obtained by collapsing the outer
  `trans` first (`transApp … x : F (trans (…) hcd) x ⟶ F hcd (F (trans hib hbc) x)`) and then mapping
  the inner collapse `transApp hib hbc x` along `F hcd`.  This is exactly the object-level analogue of
  the hom-level `pushHom`-composition used by `homCompRawL_eq_stage`. -/

/-- The three-fold object collapse iso `F (trans (trans hib hbc) hcd) x ⟶ F hcd (F hbc (F hib x))`,
    built by collapsing the outer `trans` (`transApp`) then mapping the inner collapse along `F hcd`. -/
@[expose] public noncomputable def nestApp3 {i b c d : ι}
    (hib : D.le i b) (hbc : D.le b c) (hcd : D.le c d) (x : L.A i) :
    L.F (D.trans (D.trans hib hbc) hcd) x ⟶ L.F hcd (L.F hbc (L.F hib x)) :=
  transApp L (D.trans hib hbc) hcd x
    ≫ (L.functF hcd).map (transApp L hib hbc x)

public theorem nestApp3_isIso {i b c d : ι}
    (hib : D.le i b) (hbc : D.le b c) (hcd : D.le c d) (x : L.A i) :
    IsIso (nestApp3 L hib hbc hcd x) :=
  isIso_comp (transApp_isIso L (D.trans hib hbc) hcd x)
    (functor_preserves_iso (F := L.functF hcd) (transApp L hib hbc x) (transApp_isIso L hib hbc x))

end LaxHom

/-! ## The germ hom-colimit and the `Cat` instance on `LaxColim L`

  With `Coherent L` in hand, the lax hom-transition `pushHom` is a genuine `Colim.System` over the
  directed set of upper bounds (`pushHom_refl`/`pushHom_trans` ARE the `System` laws `tr_refl`/
  `tr_trans`).  So the entire strict `CatColimit.lean` germ machinery (`Colimit`, `incl`,
  `incl_compat`, the universal property) applies VERBATIM — only the transition map changed from
  `castHom`-based `homTr` to iso-conjugation `pushHom`.  Objects are the bare `Σ i, A i` (`Obj`), so
  unlike the strict colimit we need NO `Quotient.out`/choice on objects: the hom-type of `⟨i,x⟩ →
  ⟨j,y⟩` is directly the germ colimit. -/
section HomColim

variable (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L)

/-- The hom-colimit `Colim.System` for fixed representatives `x : A i`, `y : A j`: at each upper
    bound `k` the hom-set `Hom_{A k}(F x, F y)`, with transition the lax `pushHom`.  Its `tr_refl`/
    `tr_trans` are exactly `Coherent.push_refl`/`push_trans`. -/
@[expose] public noncomputable def homSystemL {i j : ι} (x : L.A i) (y : L.A j) :
    System (UpperBound D i j) (upperDirected D i j) where
  X a := L.F a.2.1 x ⟶ L.F a.2.2 y
  tr {a _} hab g := pushHom L x y a.2.1 a.2.2 hab g
  tr_refl {a} g := hL.push_refl x y a.2.1 a.2.2 g
  tr_trans {a _ _} hab hbc g := hL.push_trans x y a.2.1 a.2.2 hab hbc g

/-- Morphisms `⟨i,x⟩ → ⟨j,y⟩` in `LaxColim L`: the directed colimit of `Hom_{A k}(F x, F y)` over
    the common upper bounds `k` (germs of stage morphisms under the lax transition). -/
@[expose] public noncomputable def HomColimL {i j : ι} (x : L.A i) (y : L.A j) : Type _ :=
  Colimit (homSystemL L hL x y)

/-- Include a stage-`a` morphism into the lax hom-colimit. -/
@[expose] public noncomputable def homInclL {i j : ι} (x : L.A i) (y : L.A j)
    (a : UpperBound D i j) (g : L.F a.2.1 x ⟶ L.F a.2.2 y) : HomColimL L hL x y :=
  incl (homSystemL L hL x y) a g

/-- Pushing a germ to a higher bound and including equals including at the lower bound (the colimit
    absorbs the transition — `incl_compat` for `homSystemL`). -/
public theorem homInclL_compat {i j : ι} (x : L.A i) (y : L.A j)
    {a b : UpperBound D i j} (hab : (upperDirected D i j).le a b)
    (g : L.F a.2.1 x ⟶ L.F a.2.2 y) :
    homInclL L hL x y b (pushHom L x y a.2.1 a.2.2 hab g) = homInclL L hL x y a g :=
  incl_compat (homSystemL L hL x y) hab g

/-- The identity germ at `⟨i,x⟩`: the germ of `𝟙 (F (refl i) x)` at the trivial upper bound
    `⟨i, refl i, refl i⟩`. -/
@[expose] public noncomputable def homIdL {i : ι} (x : L.A i) : HomColimL L hL x x :=
  homInclL L hL x x ⟨i, D.refl i, D.refl i⟩ (Cat.id (L.F (D.refl i) x))

/-! ### Composition at an explicit common bound, and bound-independence -/

/-- Compose germs `f` (level `a`) and `g` (level `b`) at an explicit common bound `e`: push both to
    `e` (`pushHom`) and compose in `A e`.  The middle objects `F(trans a.2.2 hae) xq` and
    `F(trans b.2.1 hbe) xq` are defeq (proof irrelevance of `D.le iq e`), so the composite
    typechecks without re-typing. -/
@[expose] public noncomputable def compAtL {ip iq ir : ι} (xp : L.A ip) (xq : L.A iq) (xr : L.A ir)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : L.F b.2.1 xq ⟶ L.F b.2.2 xr)
    (e : ι) (hae : D.le a.1 e) (hbe : D.le b.1 e) : HomColimL L hL xp xr :=
  homInclL L hL xp xr ⟨e, D.trans a.2.1 hae, D.trans b.2.2 hbe⟩
    (pushHom L xp xq a.2.1 a.2.2 hae f ≫ pushHom L xq xr b.2.1 b.2.2 hbe g)

/-- Composing at level `e` equals composing at any higher level `d` (`e ≤ d`): push each pushed
    piece further by `push_trans`, merge by `pushHom_comp`, absorb by `homInclL_compat`. -/
public theorem compAtL_mono {ip iq ir : ι} (xp : L.A ip) (xq : L.A iq) (xr : L.A ir)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : L.F b.2.1 xq ⟶ L.F b.2.2 xr)
    {e d : ι} (hae : D.le a.1 e) (hbe : D.le b.1 e) (hed : D.le e d) :
    compAtL L hL xp xq xr a f b g e hae hbe
      = compAtL L hL xp xq xr a f b g d (D.trans hae hed) (D.trans hbe hed) := by
  symm
  unfold compAtL
  -- push each piece from `e` to `d` via the associativity coherence `push_trans`.
  rw [hL.push_trans xp xq a.2.1 a.2.2 hae hed f, hL.push_trans xq xr b.2.1 b.2.2 hbe hed g]
  -- merge the two `pushHom …hed` into one composite via `pushHom_comp`.
  rw [← pushHom_comp L xp xq xr (D.trans a.2.1 hae) (D.trans a.2.2 hae) (D.trans b.2.2 hbe) hed
        (pushHom L xp xq a.2.1 a.2.2 hae f) (pushHom L xq xr b.2.1 b.2.2 hbe g)]
  -- absorb the level `e → d` transition by `homInclL_compat`.
  exact homInclL_compat L hL xp xr
    (a := ⟨e, D.trans a.2.1 hae, D.trans b.2.2 hbe⟩)
    (b := ⟨d, D.trans (D.trans a.2.1 hae) hed, D.trans (D.trans b.2.2 hbe) hed⟩) hed _

/-- Composition is independent of the chosen common bound: route any two bounds through a higher
    one (`D.bound`) and apply `compAtL_mono`. -/
public theorem compAtL_indep {ip iq ir : ι} (xp : L.A ip) (xq : L.A iq) (xr : L.A ir)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : L.F b.2.1 xq ⟶ L.F b.2.2 xr)
    {e₁ e₂ : ι} (hae₁ : D.le a.1 e₁) (hbe₁ : D.le b.1 e₁)
    (hae₂ : D.le a.1 e₂) (hbe₂ : D.le b.1 e₂) :
    compAtL L hL xp xq xr a f b g e₁ hae₁ hbe₁ = compAtL L hL xp xq xr a f b g e₂ hae₂ hbe₂ := by
  obtain ⟨d, h1d, h2d⟩ := D.bound e₁ e₂
  rw [compAtL_mono L hL xp xq xr a f b g hae₁ hbe₁ h1d,
      compAtL_mono L hL xp xq xr a f b g hae₂ hbe₂ h2d]

/-! ### Raw composition of germ representatives, and its well-definedness -/

/-- Raw composition of germ representatives: compose at the CHOSEN common bound `D.bound a.1 b.1`. -/
@[expose] public noncomputable def homCompRawL {ip iq ir : ι} (xp : L.A ip) (xq : L.A iq) (xr : L.A ir)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : L.F b.2.1 xq ⟶ L.F b.2.2 xr) : HomColimL L hL xp xr :=
  compAtL L hL xp xq xr a f b g (Classical.choose (D.bound a.1 b.1))
    (Classical.choose_spec (D.bound a.1 b.1)).1 (Classical.choose_spec (D.bound a.1 b.1)).2

/-- `homCompRawL` equals `compAtL` at ANY common bound (all bounds agree, `compAtL_indep`). -/
public theorem homCompRawL_eq_compAtL {ip iq ir : ι} (xp : L.A ip) (xq : L.A iq) (xr : L.A ir)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : L.F b.2.1 xq ⟶ L.F b.2.2 xr)
    (e : ι) (hae : D.le a.1 e) (hbe : D.le b.1 e) :
    homCompRawL L hL xp xq xr a f b g = compAtL L hL xp xq xr a f b g e hae hbe :=
  compAtL_indep L hL xp xq xr a f b g _ _ hae hbe

/-- Pushing the LEFT germ's representative up to a higher bound doesn't change the composite. -/
public theorem homCompRawL_push_left {ip iq ir : ι} (xp : L.A ip) (xq : L.A iq) (xr : L.A ir)
    (a a₂ : UpperBound D ip iq) (h : D.le a.1 a₂.1) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : L.F b.2.1 xq ⟶ L.F b.2.2 xr) :
    homCompRawL L hL xp xq xr a₂ (pushHom L xp xq a.2.1 a.2.2 h f) b g
      = homCompRawL L hL xp xq xr a f b g := by
  obtain ⟨M, ha₂M, hbM⟩ := D.bound a₂.1 b.1
  rw [homCompRawL_eq_compAtL L hL xp xq xr a₂ (pushHom L xp xq a.2.1 a.2.2 h f) b g M ha₂M hbM,
      homCompRawL_eq_compAtL L hL xp xq xr a f b g M (D.trans h ha₂M) hbM]
  unfold compAtL
  rw [hL.push_trans xp xq a.2.1 a.2.2 h ha₂M f]

/-- Pushing the RIGHT germ's representative up to a higher bound doesn't change the composite. -/
public theorem homCompRawL_push_right {ip iq ir : ι} (xp : L.A ip) (xq : L.A iq) (xr : L.A ir)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq)
    (b b₂ : UpperBound D iq ir) (h : D.le b.1 b₂.1) (g : L.F b.2.1 xq ⟶ L.F b.2.2 xr) :
    homCompRawL L hL xp xq xr a f b₂ (pushHom L xq xr b.2.1 b.2.2 h g)
      = homCompRawL L hL xp xq xr a f b g := by
  obtain ⟨M, haM, hb₂M⟩ := D.bound a.1 b₂.1
  rw [homCompRawL_eq_compAtL L hL xp xq xr a f b₂ (pushHom L xq xr b.2.1 b.2.2 h g) M haM hb₂M,
      homCompRawL_eq_compAtL L hL xp xq xr a f b g M haM (D.trans h hb₂M)]
  unfold compAtL
  rw [hL.push_trans xq xr b.2.1 b.2.2 h hb₂M g]

/-- Raw composition respects germ equivalence on BOTH arguments (well-definedness): push each
    representative up to its germ-witness level (`push_left`/`push_right`), where they agree. -/
public theorem homCompRawL_wd {ip iq ir : ι} (xp : L.A ip) (xq : L.A iq) (xr : L.A ir)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq)
    (a' : UpperBound D ip iq) (f' : L.F a'.2.1 xp ⟶ L.F a'.2.2 xq)
    (hP : Rel (homSystemL L hL xp xq) ⟨a, f⟩ ⟨a', f'⟩)
    (b : UpperBound D iq ir) (g : L.F b.2.1 xq ⟶ L.F b.2.2 xr)
    (b' : UpperBound D iq ir) (g' : L.F b'.2.1 xq ⟶ L.F b'.2.2 xr)
    (hQ : Rel (homSystemL L hL xq xr) ⟨b, g⟩ ⟨b', g'⟩) :
    homCompRawL L hL xp xq xr a f b g = homCompRawL L hL xp xq xr a' f' b' g' := by
  obtain ⟨k, hak, ha'k, hf⟩ := hP
  obtain ⟨l, hbl, hb'l, hg⟩ := hQ
  have hf' : pushHom L xp xq a.2.1 a.2.2 hak f = pushHom L xp xq a'.2.1 a'.2.2 ha'k f' := hf
  have hg' : pushHom L xq xr b.2.1 b.2.2 hbl g = pushHom L xq xr b'.2.1 b'.2.2 hb'l g' := hg
  rw [← homCompRawL_push_left L hL xp xq xr a k hak f b g, hf',
      homCompRawL_push_left L hL xp xq xr a' k ha'k f' b g,
      ← homCompRawL_push_right L hL xp xq xr a' f' b l hbl g, hg',
      homCompRawL_push_right L hL xp xq xr a' f' b' l hb'l g']

/-! ### The hom-type, identity, and composition on the bare Σ-object carrier `Obj L`

  Objects of `LaxColim L` are the bare `Σ i, A i` (`Obj`), so a morphism `⟨i,x⟩ → ⟨j,y⟩` is directly
  the germ colimit `HomColimL x y` — NO `Quotient.out`/choice on objects (the strict `colimitCat`
  needed `colimOut`).  Composition lifts `homCompRawL` over the two germ quotients
  (`homCompRawL_wd`). -/

/-- The hom-type `⟨i,x⟩ ⟶ ⟨j,y⟩` of `LaxColim L`: the germ colimit of the fibre representatives. -/
@[expose] public noncomputable def homL (p q : Obj L) : Type _ := HomColimL L hL p.2 q.2

/-- Identity of `⟨i,x⟩`: the identity germ `homIdL`. -/
@[expose] public noncomputable def idL (p : Obj L) : homL L hL p p := homIdL L hL p.2

/-- Composition of germs, lifted from `homCompRawL` over the two quotients (well-defined by
    `homCompRawL_wd`). -/
@[expose] public noncomputable def compL {p q r : Obj L} (m : homL L hL p q) (n : homL L hL q r) : homL L hL p r :=
  Quotient.lift₂
    (fun rm rn => homCompRawL L hL p.2 q.2 r.2 rm.1 rm.2 rn.1 rn.2)
    (fun _ _ _ _ hP hQ => homCompRawL_wd L hL p.2 q.2 r.2 _ _ _ _ hP _ _ _ _ hQ)
    m n

/-! ### Category axioms (identity laws and associativity) -/

/-- Left identity at the raw level: `id ∘ f = f` (composing the identity germ with `f`). -/
public theorem homCompRawL_id_left {ip iq : ι} (xp : L.A ip) (xq : L.A iq)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq) :
    homCompRawL L hL xp xp xq ⟨ip, D.refl ip, D.refl ip⟩ (Cat.id (L.F (D.refl ip) xp)) a f
      = homInclL L hL xp xq a f := by
  rw [homCompRawL_eq_compAtL L hL xp xp xq ⟨ip, D.refl ip, D.refl ip⟩
        (Cat.id (L.F (D.refl ip) xp)) a f a.1 a.2.1 (D.refl a.1)]
  unfold compAtL
  -- left push: `pushHom id = id` (`pushHom_id`); right push at `refl`: `pushHom f = f` (`push_refl`).
  rw [pushHom_id L xp (D.refl ip) a.2.1, hL.push_refl xp xq a.2.1 a.2.2 f, Cat.id_comp]
  -- the remaining bound differs from `a` only in `D.le` proofs (irrelevant): defeq.
  rfl

/-- Right identity at the raw level: `f ∘ id = f`. -/
public theorem homCompRawL_id_right {ip iq : ι} (xp : L.A ip) (xq : L.A iq)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq) :
    homCompRawL L hL xp xq xq a f ⟨iq, D.refl iq, D.refl iq⟩ (Cat.id (L.F (D.refl iq) xq))
      = homInclL L hL xp xq a f := by
  rw [homCompRawL_eq_compAtL L hL xp xq xq a f ⟨iq, D.refl iq, D.refl iq⟩
        (Cat.id (L.F (D.refl iq) xq)) a.1 (D.refl a.1) a.2.2]
  unfold compAtL
  rw [pushHom_id L xq (D.refl iq) a.2.2, hL.push_refl xp xq a.2.1 a.2.2 f, Cat.comp_id]
  rfl

/-- Left identity in `LaxColim L`: `idL ∘ m = m`. -/
public theorem compL_id_left {p q : Obj L} (m : homL L hL p q) : compL L hL (idL L hL p) m = m := by
  induction m using Quotient.ind with
  | _ rm => obtain ⟨a, f⟩ := rm; exact homCompRawL_id_left L hL p.2 q.2 a f

/-- Right identity in `LaxColim L`: `m ∘ idL = m`. -/
public theorem compL_id_right {p q : Obj L} (m : homL L hL p q) : compL L hL m (idL L hL q) = m := by
  induction m using Quotient.ind with
  | _ rm => obtain ⟨a, f⟩ := rm; exact homCompRawL_id_right L hL p.2 q.2 a f

/-- Associativity in `LaxColim L`.  Mirrors the strict `colimComp_assoc`: push all three germ
    representatives to a single common bound `M`, where both bracketings reduce to one stage
    composite `(F_M ≫ G_M) ≫ H_M` resp. `F_M ≫ (G_M ≫ H_M)`, equal by `Cat.assoc`.  The strict
    `homTr_refl`/`homTr_comp` become `push_refl`/`pushHom_comp`. -/
public theorem compL_assoc {p q r s : Obj L}
    (m : homL L hL p q) (n : homL L hL q r) (k : homL L hL r s) :
    compL L hL (compL L hL m n) k = compL L hL m (compL L hL n k) := by
  refine Quotient.inductionOn m (fun rm => ?_)
  refine Quotient.inductionOn n (fun rn => ?_)
  refine Quotient.inductionOn k (fun rk => ?_)
  obtain ⟨a, f⟩ := rm; obtain ⟨b, g⟩ := rn; obtain ⟨c, h⟩ := rk
  let xp := p.2
  let xq := q.2
  let xr := r.2
  let xs := s.2
  -- common bound `M` of `a.1, b.1, c.1`.
  obtain ⟨e₁, hae₁, hbe₁⟩ := D.bound a.1 b.1
  obtain ⟨M, he₁M, hcM⟩ := D.bound e₁ c.1
  have haM : D.le a.1 M := D.trans hae₁ he₁M
  have hbM : D.le b.1 M := D.trans hbe₁ he₁M
  -- bounds at `M`.
  let aM : UpperBound D p.1 q.1 := ⟨M, D.trans a.2.1 haM, D.trans a.2.2 haM⟩
  let bM : UpperBound D q.1 r.1 := ⟨M, D.trans b.2.1 hbM, D.trans b.2.2 hbM⟩
  let cM : UpperBound D r.1 s.1 := ⟨M, D.trans c.2.1 hcM, D.trans c.2.2 hcM⟩
  let F_M : L.F aM.2.1 xp ⟶ L.F aM.2.2 xq := pushHom L xp xq a.2.1 a.2.2 haM f
  let G_M : L.F bM.2.1 xq ⟶ L.F bM.2.2 xr := pushHom L xq xr b.2.1 b.2.2 hbM g
  let H_M : L.F cM.2.1 xr ⟶ L.F cM.2.2 xs := pushHom L xr xs c.2.1 c.2.2 hcM h
  let ub_pr : UpperBound D p.1 r.1 := ⟨M, D.trans a.2.1 haM, D.trans b.2.2 hbM⟩
  let ub_qs : UpperBound D q.1 s.1 := ⟨M, D.trans b.2.1 hbM, D.trans c.2.2 hcM⟩
  let ub_ps : UpperBound D p.1 s.1 := ⟨M, D.trans a.2.1 haM, D.trans c.2.2 hcM⟩
  -- inner composites reduce to `compAtL` at `M`.
  have h_innerL : compL L hL (Quotient.mk _ ⟨a, f⟩) (Quotient.mk _ ⟨b, g⟩)
      = compAtL L hL xp xq xr a f b g M haM hbM :=
    homCompRawL_eq_compAtL L hL xp xq xr a f b g M haM hbM
  have h_innerR : compL L hL (Quotient.mk _ ⟨b, g⟩) (Quotient.mk _ ⟨c, h⟩)
      = compAtL L hL xq xr xs b g c h M hbM hcM :=
    homCompRawL_eq_compAtL L hL xq xr xs b g c h M hbM hcM
  -- outer composites (`compAtL` returns a `homInclL = mk`, so the next `compL` is `homCompRawL`).
  have h_outerL : compL L hL (compAtL L hL xp xq xr a f b g M haM hbM) (Quotient.mk _ ⟨c, h⟩)
      = homCompRawL L hL xp xr xs ub_pr (F_M ≫ G_M) c h := rfl
  have h_outerR : compL L hL (Quotient.mk _ ⟨a, f⟩) (compAtL L hL xq xr xs b g c h M hbM hcM)
      = homCompRawL L hL xp xq xs a f ub_qs (G_M ≫ H_M) := rfl
  -- push outer `homCompRawL` to `compAtL` at `M`, then simplify the `D.refl M` push by `push_refl`.
  have h_simpL : homCompRawL L hL xp xr xs ub_pr (F_M ≫ G_M) c h
      = homInclL L hL xp xs ub_ps ((F_M ≫ G_M) ≫ H_M) := by
    rw [homCompRawL_eq_compAtL L hL xp xr xs ub_pr (F_M ≫ G_M) c h M (D.refl M) hcM]
    unfold compAtL
    rw [hL.push_refl xp xr ub_pr.2.1 ub_pr.2.2 (F_M ≫ G_M)]
  have h_simpR : homCompRawL L hL xp xq xs a f ub_qs (G_M ≫ H_M)
      = homInclL L hL xp xs ub_ps (F_M ≫ (G_M ≫ H_M)) := by
    rw [homCompRawL_eq_compAtL L hL xp xq xs a f ub_qs (G_M ≫ H_M) M haM (D.refl M)]
    unfold compAtL
    rw [hL.push_refl xq xs ub_qs.2.1 ub_qs.2.2 (G_M ≫ H_M)]
  calc
    compL L hL (compL L hL (Quotient.mk _ ⟨a, f⟩) (Quotient.mk _ ⟨b, g⟩)) (Quotient.mk _ ⟨c, h⟩)
        = compL L hL (compAtL L hL xp xq xr a f b g M haM hbM) (Quotient.mk _ ⟨c, h⟩) := by
          rw [h_innerL]
    _ = homCompRawL L hL xp xr xs ub_pr (F_M ≫ G_M) c h := h_outerL
    _ = homInclL L hL xp xs ub_ps ((F_M ≫ G_M) ≫ H_M) := h_simpL
    _ = homInclL L hL xp xs ub_ps (F_M ≫ (G_M ≫ H_M)) := by rw [Cat.assoc F_M G_M H_M]
    _ = homCompRawL L hL xp xq xs a f ub_qs (G_M ≫ H_M) := h_simpR.symm
    _ = compL L hL (Quotient.mk _ ⟨a, f⟩) (compAtL L hL xq xr xs b g c h M hbM hcM) := h_outerR.symm
    _ = compL L hL (Quotient.mk _ ⟨a, f⟩) (compL L hL (Quotient.mk _ ⟨b, g⟩) (Quotient.mk _ ⟨c, h⟩)) := by
          rw [h_innerR]

/-! ### The `Cat` instance on the lax colimit -/

/-- **The lax colimit category `LaxColim L`.**  Objects are the bare `Σ i, A i` (`Obj L`); morphisms
    `⟨i,x⟩ → ⟨j,y⟩` are germs of `Hom_{A k}(F x, F y)` over upper bounds `k` (`homL`); identity is the
    germ of `𝟙` (`idL`); composition is the bound-coherent germ composition (`compL`).  The three
    category axioms are `compL_id_left`/`compL_id_right`/`compL_assoc`.  Built relative to the
    pseudofunctor coherence `Coherent L` (the lax analogue of `CatSystem.Coherent` — TRUE for
    base-change, unlike the strict `StrictBaseChange`). -/
@[expose] public noncomputable def laxColimCat : Cat (Obj L) where
  Hom p q := homL L hL p q
  id p := idL L hL p
  comp m n := compL L hL m n
  id_comp m := compL_id_left L hL m
  comp_id m := compL_id_right L hL m
  assoc m n k := compL_assoc L hL m n k

end HomColim

/-! ## Coherence of the base-change `LaxCatSystem` (`laxOfProjSystem' P`)

  The last §1.543 obligation, now DISCHARGED here (`coherentProj`): `LaxCatSystem.Coherent
  (laxOfProjSystem' P)`, i.e. the pseudofunctor UNIT (`push_refl`) and ASSOCIATIVITY (`push_trans`)
  of the lax hom-transition `pushHom` built from the pullback coherence isos
  `projReflIso`/`projTransIso`.  Both reduce to arrow-equalities between fixed pullback apices,
  proved by pullback-`lift` uniqueness.  With this, §1.543 is proven Sorry-free. -/
section BaseChangeCoherent

variable {𝒞 : Type w} [Cat.{w} 𝒞] [HasPullbacks 𝒞]
variable {ι : Type u} {D : Directed ι}

/-- The `.nat.app` underlying arrow of a base-map-transport of a `NatIso` of base-change functors:
    transporting `baseChangeObj b ≅ G` along `e : a = b` conjugates the component by the `eqToHom`
    of the pullback objects.  (The pullbacks coincide after `subst e`, so it is the identity.) -/
public theorem mpr_natiso_app {C E : 𝒞} {a b : E ⟶ C} (e : a = b)
    {G : Functor (Over C) (Over E)}
    (N : NatIso (baseChangeFunctor b) G) (X : Over C) :
    ((Eq.mpr (congrArg (fun z => NatIso (baseChangeFunctor z) G) e) N).nat.app
        X).f
      = (eqToHom (congrArg (fun z => baseChangeObj z X) e)).f ≫ (N.nat.app X).f := by
  subst e
  show (N.nat.app X).f = (eqToHom (rfl : baseChangeObj a X = _)).f ≫ (N.nat.app X).f
  rw [show ((eqToHom (rfl : baseChangeObj a X = baseChangeObj a X)) : baseChangeObj a X ⟶ _)
        = Cat.id _ from rfl]
  exact (Cat.id_comp _).symm

/-- The `.nat.app` of the transported composite coherence iso `projTransIso`, computed via
    `eqToHom`-conjugation of the underlying `baseChangeTransNatIso`.  Generalises the internal
    `rw [P.proj_trans …]` transport so that the pushed-morphism arrows become explicit. -/
private theorem projTransIso_app (P : ProjSystem ι D 𝒞) {i j k : ι}
    (hij : D.le i j) (hjk : D.le j k) (X : pcObj P i) :
    (transApp (laxOfProjSystem' P) hij hjk X).f
      = (eqToHom (congrArg (fun z => baseChangeObj z X) (P.proj_trans hij hjk))).f
          ≫ _transFwdf (P.proj hij) (P.proj hjk) X := by
  unfold transApp
  simp only [laxOfProjSystem', laxOfProjSystem, pseudoBaseChange, projTransIso, id_eq]
  rw [mpr_natiso_app (P.proj_trans hij hjk) (baseChangeTransNatIso (P.proj hij) (P.proj hjk)) X]
  rfl

/-- `eqToHom` between two base-change objects over equal base maps, post-composed with the chosen
    pullback's `π₂`, is the source `π₂` (the transport is the identity on pullbacks). -/
public theorem eqToHom_bc_π₂ {C E : 𝒞} {a b : E ⟶ C} (e : a = b) (X : Over C) :
    (eqToHom (congrArg (fun z => baseChangeObj z X) e)).f ≫ (_pb b X).cone.π₂
      = (_pb a X).cone.π₂ := by
  subst e
  rw [show (eqToHom (congrArg (fun z => baseChangeObj z X) (rfl : a = a))
        : baseChangeObj a X ⟶ baseChangeObj a X) = Cat.id _ from rfl]
  exact Cat.id_comp _

/-- Same, post-composed with the chosen pullback's `π₁`. -/
public theorem eqToHom_bc_π₁ {C E : 𝒞} {a b : E ⟶ C} (e : a = b) (X : Over C) :
    (eqToHom (congrArg (fun z => baseChangeObj z X) e)).f ≫ (_pb b X).cone.π₁
      = (_pb a X).cone.π₁ := by
  subst e
  rw [show (eqToHom (congrArg (fun z => baseChangeObj z X) (rfl : a = a))
        : baseChangeObj a X ⟶ baseChangeObj a X) = Cat.id _ from rfl]
  exact Cat.id_comp _

/-- `baseChangeMap`'s underlying arrow against the codomain pullback's `π₂` is the source `π₂`. -/
private theorem baseChangeMap_f_π₂ {C E : 𝒞} (g : E ⟶ C) {X Y : Over C} (m : OverHom X Y) :
    (baseChangeMap g m).f ≫ (_pb g Y).cone.π₂ = (_pb g X).cone.π₂ :=
  (_pb g Y).lift_snd (baseChangeCone g m)

/-- `baseChangeMap`'s underlying arrow against the codomain pullback's `π₁` is `π₁ ≫ m.f`. -/
public theorem baseChangeMap_f_π₁ {C E : 𝒞} (g : E ⟶ C) {X Y : Over C} (m : OverHom X Y) :
    (baseChangeMap g m).f ≫ (_pb g Y).cone.π₁ = (_pb g X).cone.π₁ ≫ m.f :=
  (_pb g Y).lift_fst (baseChangeCone g m)

/-- Two arrows into a chosen pullback agreeing on both projections are equal. -/
private theorem pb_hom_ext {A B C : 𝒞} {f : A ⟶ C} {g : B ⟶ C} (p : HasPullback f g)
    {Z : 𝒞} {u v : Z ⟶ p.cone.pt}
    (h₁ : u ≫ p.cone.π₁ = v ≫ p.cone.π₁) (h₂ : u ≫ p.cone.π₂ = v ≫ p.cone.π₂) : u = v := by
  rw [p.lift_uniq ⟨Z, u ≫ p.cone.π₁, u ≫ p.cone.π₂,
        by rw [Cat.assoc, p.cone.w, Cat.assoc]⟩ u rfl rfl,
      p.lift_uniq ⟨Z, u ≫ p.cone.π₁, u ≫ p.cone.π₂,
        by rw [Cat.assoc, p.cone.w, Cat.assoc]⟩ v h₁.symm h₂.symm]

/-- The composite `eqToHom (proj_trans) ≫ _qInner (proj hik) (proj (refl)) x` is the identity on the
    pullback `baseChangeObj (P.proj hik) x` (the `trans`-iso's inner factorisation, at a reflexive
    second leg `P.proj (D.refl k) = id`, collapses to the identity).  This is the local heart of the
    reflexive coherence. -/
private theorem qInner_refl_id (P : ProjSystem ι D 𝒞) {i : ι} {k : ι}
    (hik : D.le i k) (x : pcObj P i) :
    (eqToHom (congrArg (fun z => baseChangeObj z x) (P.proj_trans hik (D.refl k)))).f
        ≫ _qInner (P.proj hik) (P.proj (D.refl k)) x
      = Cat.id (baseChangeObj (P.proj hik) x).dom := by
  apply pb_hom_ext (_pb (P.proj hik) x)
  · rw [Cat.assoc, _qInner_fst (P.proj hik) (P.proj (D.refl k)) x,
        eqToHom_bc_π₁ (P.proj_trans hik (D.refl k)) x, Cat.id_comp]
  · have hr : (_pb (P.proj (D.refl k) ≫ P.proj hik) x).cone.π₂ ≫ P.proj (D.refl k)
        = (_pb (P.proj (D.refl k) ≫ P.proj hik) x).cone.π₂ := by
      rw [P.proj_refl k, Cat.comp_id]
    rw [Cat.assoc, _qInner_snd (P.proj hik) (P.proj (D.refl k)) x, hr,
        eqToHom_bc_π₂ (P.proj_trans hik (D.refl k)) x, Cat.id_comp]

/-- The naturality-square reduction of `proj_push_refl`: pushing `g` along the reflexive bound
    intertwines the two `trans`-coherence forward maps. -/
private theorem proj_push_refl_key (P : ProjSystem ι D 𝒞)
    {i j : ι} (x : (laxOfProjSystem' P).A i) (y : (laxOfProjSystem' P).A j) {k : ι}
    (hik : D.le i k) (hjk : D.le j k)
    (g : (laxOfProjSystem' P).F hik x ⟶ (laxOfProjSystem' P).F hjk y) :
    transApp (laxOfProjSystem' P) hik (D.refl k) x
      ≫ Functor.map (self := (laxOfProjSystem' P).functF (D.refl k)) g
      = g ≫ transApp (laxOfProjSystem' P) hjk (D.refl k) y := by
  apply OverHom.ext
  show (transApp (laxOfProjSystem' P) hik (D.refl k) x).f ≫ (baseChangeMap (P.proj (D.refl k)) g).f
      = g.f ≫ (transApp (laxOfProjSystem' P) hjk (D.refl k) y).f
  rw [projTransIso_app, projTransIso_app]
  apply pb_hom_ext (_pb (P.proj (D.refl k)) (baseChangeObj (P.proj hjk) y))
  · -- π₁ leg: reduces (via `_qInner`) to an equality of arrows into the pullback `bc (P.proj hjk) y`.
    simp only [Cat.assoc]
    rw [baseChangeMap_f_π₁ (P.proj (D.refl k)) g]
    rw [← Cat.assoc (_transFwdf (P.proj hik) (P.proj (D.refl k)) x),
        _transFwd_outer_fst (P.proj hik) (P.proj (D.refl k)) x,
        _transFwd_outer_fst (P.proj hjk) (P.proj (D.refl k)) y]
    -- goal: eqToHom.f ≫ _qInner gik r x ≫ g.f = g.f ≫ eqToHom.f ≫ _qInner gjk r y
    -- both inner factorisations collapse to the identity (`qInner_refl_id`).
    rw [← Cat.assoc, qInner_refl_id P hik x, qInner_refl_id P hjk y]
    exact (Cat.id_comp _).trans (Cat.comp_id _).symm
  · -- π₂ leg: both sides reduce to `(baseChangeObj (P.proj hik) x).hom`.
    simp only [Cat.assoc]
    rw [baseChangeMap_f_π₂ (P.proj (D.refl k)) g,
        _transFwd_π₂ (P.proj hik) (P.proj (D.refl k)) x,
        eqToHom_bc_π₂ (P.proj_trans hik (D.refl k)) x,
        _transFwd_π₂ (P.proj hjk) (P.proj (D.refl k)) y,
        eqToHom_bc_π₂ (P.proj_trans hjk (D.refl k)) y]
    exact (g.w).symm

/-- `push_refl` for the base-change system. -/
public theorem proj_push_refl (P : ProjSystem ι D 𝒞)
    {i j : ι} (x : (laxOfProjSystem' P).A i) (y : (laxOfProjSystem' P).A j) {k : ι}
    (hik : D.le i k) (hjk : D.le j k)
    (g : (laxOfProjSystem' P).F hik x ⟶ (laxOfProjSystem' P).F hjk y) :
    pushHom (laxOfProjSystem' P) x y hik hjk (D.refl k) g = g := by
  unfold pushHom
  rw [← Cat.assoc, proj_push_refl_key P x y hik hjk g, Cat.assoc, isoInv_comp, Cat.comp_id]

/-- Right-cancellation of an isomorphism: if `a ≫ h = b ≫ h` and `h` is iso, then `a = b`.  Stated
    over an arbitrary category `𝒜` (the cancellation happens in a slice `L.A n`, not the base `𝒞`). -/
private theorem iso_cancel_right {𝒜 : Type w} [Cat.{w} 𝒜] {X Y Y' : 𝒜} {a b : X ⟶ Y}
    (h : Y ⟶ Y') (hh : IsIso h) (e : a ≫ h = b ≫ h) : a = b := by
  obtain ⟨h', hh1, _⟩ := hh
  calc a = a ≫ (h ≫ h') := by rw [hh1, Cat.comp_id]
    _ = (a ≫ h) ≫ h' := (Cat.assoc _ _ _).symm
    _ = (b ≫ h) ≫ h' := by rw [e]
    _ = b ≫ (h ≫ h') := Cat.assoc _ _ _
    _ = b := by rw [hh1, Cat.comp_id]

/-- `reassoc` form of `baseChangeMap_f_π₁`. -/
private theorem baseChangeMap_f_π₁' {C E : 𝒞} (g : E ⟶ C) {X Y : Over C} (m : OverHom X Y)
    {W : 𝒞} (z : Y.dom ⟶ W) :
    (baseChangeMap g m).f ≫ (_pb g Y).cone.π₁ ≫ z = (_pb g X).cone.π₁ ≫ m.f ≫ z := by
  rw [← Cat.assoc, baseChangeMap_f_π₁ g m, Cat.assoc]

/-- `reassoc` form of `baseChangeMap_f_π₂`. -/
private theorem baseChangeMap_f_π₂' {C E : 𝒞} (g : E ⟶ C) {X Y : Over C} (m : OverHom X Y)
    {W : 𝒞} (z : E ⟶ W) :
    (baseChangeMap g m).f ≫ (_pb g Y).cone.π₂ ≫ z = (_pb g X).cone.π₂ ≫ z := by
  rw [← Cat.assoc, baseChangeMap_f_π₂ g m]

/-- The outer `π₂`-leg of `transApp`'s underlying arrow: it is the composite pullback's `π₂` (the
    structure map to `pr m`).  Stated in `reassoc` form (trailing `≫ z`) so it applies as a `simp`
    lemma regardless of how the surrounding composite is associated. -/
private theorem transApp_f_π₂ (P : ProjSystem ι D 𝒞) {i k m : ι} (hik : D.le i k) (hkm : D.le k m)
    (x : pcObj P i) {W : 𝒞} (z : P.pr m ⟶ W) :
    (transApp (laxOfProjSystem' P) hik hkm x).f
        ≫ (_pb (P.proj hkm) (baseChangeObj (P.proj hik) x)).cone.π₂ ≫ z
      = (_pb (P.proj (D.trans hik hkm)) x).cone.π₂ ≫ z := by
  rw [← Cat.assoc, projTransIso_app, Cat.assoc, Cat.assoc,
      ← Cat.assoc (_transFwdf (P.proj hik) (P.proj hkm) x),
      _transFwd_π₂ (P.proj hik) (P.proj hkm) x, ← Cat.assoc,
      eqToHom_bc_π₂ (P.proj_trans hik hkm) x]

/-- The deep `π₁ ≫ π₁`-leg of `transApp`'s underlying arrow projects to the composite pullback's
    `π₁` (down to `x.dom`).  `reassoc` form. -/
public theorem transApp_f_π₁π₁ (P : ProjSystem ι D 𝒞) {i k m : ι}
    (hik : D.le i k) (hkm : D.le k m) (x : pcObj P i) {W : 𝒞} (z : x.dom ⟶ W) :
    (transApp (laxOfProjSystem' P) hik hkm x).f
        ≫ (_pb (P.proj hkm) (baseChangeObj (P.proj hik) x)).cone.π₁
            ≫ (_pb (P.proj hik) x).cone.π₁ ≫ z
      = (_pb (P.proj (D.trans hik hkm)) x).cone.π₁ ≫ z := by
  rw [projTransIso_app, Cat.assoc,
      ← Cat.assoc ((_pb (P.proj hkm) (baseChangeObj (P.proj hik) x)).cone.π₁)
        ((_pb (P.proj hik) x).cone.π₁) z,
      ← Cat.assoc (_transFwdf (P.proj hik) (P.proj hkm) x),
      _transFwd_π₁ (P.proj hik) (P.proj hkm) x, ← Cat.assoc,
      eqToHom_bc_π₁ (P.proj_trans hik hkm) x]

/-- The mixed `π₁ ≫ π₂`-leg of `transApp`'s underlying arrow: it is the composite pullback's `π₂`
    post-composed with the second projection `proj hkm` (the inner pasting square).  `reassoc` form. -/
private theorem transApp_f_π₁π₂ (P : ProjSystem ι D 𝒞) {i k m : ι}
    (hik : D.le i k) (hkm : D.le k m) (x : pcObj P i) {W : 𝒞} (z : P.pr k ⟶ W) :
    (transApp (laxOfProjSystem' P) hik hkm x).f
        ≫ (_pb (P.proj hkm) (baseChangeObj (P.proj hik) x)).cone.π₁
            ≫ (_pb (P.proj hik) x).cone.π₂ ≫ z
      = (_pb (P.proj (D.trans hik hkm)) x).cone.π₂ ≫ P.proj hkm ≫ z := by
  rw [projTransIso_app, Cat.assoc,
      ← Cat.assoc (_transFwdf (P.proj hik) (P.proj hkm) x)
        ((_pb (P.proj hkm) (baseChangeObj (P.proj hik) x)).cone.π₁),
      _transFwd_outer_fst (P.proj hik) (P.proj hkm) x,
      ← Cat.assoc (_qInner (P.proj hik) (P.proj hkm) x),
      _qInner_snd (P.proj hik) (P.proj hkm) x, Cat.assoc,
      ← Cat.assoc (eqToHom (congrArg (fun z => baseChangeObj z x) (P.proj_trans hik hkm))).f,
      eqToHom_bc_π₂ (P.proj_trans hik hkm) x]

/-- Terminal (`z = id`) form of `transApp_f_π₂`. -/
private theorem transApp_f_π₂₀ (P : ProjSystem ι D 𝒞) {i k m : ι} (hik : D.le i k) (hkm : D.le k m)
    (x : pcObj P i) :
    (transApp (laxOfProjSystem' P) hik hkm x).f
        ≫ (_pb (P.proj hkm) (baseChangeObj (P.proj hik) x)).cone.π₂
      = (_pb (P.proj (D.trans hik hkm)) x).cone.π₂ := by
  have h := transApp_f_π₂ P hik hkm x (Cat.id _); rwa [Cat.comp_id, Cat.comp_id] at h

/-- Terminal form of `transApp_f_π₁π₁`. -/
private theorem transApp_f_π₁π₁₀ (P : ProjSystem ι D 𝒞) {i k m : ι}
    (hik : D.le i k) (hkm : D.le k m) (x : pcObj P i) :
    (transApp (laxOfProjSystem' P) hik hkm x).f
        ≫ (_pb (P.proj hkm) (baseChangeObj (P.proj hik) x)).cone.π₁
            ≫ (_pb (P.proj hik) x).cone.π₁
      = (_pb (P.proj (D.trans hik hkm)) x).cone.π₁ := by
  have h := transApp_f_π₁π₁ P hik hkm x (Cat.id _); rwa [Cat.comp_id, Cat.comp_id] at h

/-- Terminal form of `transApp_f_π₁π₂`. -/
private theorem transApp_f_π₁π₂₀ (P : ProjSystem ι D 𝒞) {i k m : ι}
    (hik : D.le i k) (hkm : D.le k m) (x : pcObj P i) :
    (transApp (laxOfProjSystem' P) hik hkm x).f
        ≫ (_pb (P.proj hkm) (baseChangeObj (P.proj hik) x)).cone.π₁
            ≫ (_pb (P.proj hik) x).cone.π₂
      = (_pb (P.proj (D.trans hik hkm)) x).cone.π₂ ≫ P.proj hkm := by
  have h := transApp_f_π₁π₂ P hik hkm x (Cat.id _); rwa [Cat.comp_id, Cat.comp_id] at h

/-- Terminal form of `baseChangeMap_f_π₁'` (= `baseChangeMap_f_π₁`). -/
private theorem baseChangeMap_f_π₂₀ {C E : 𝒞} (g : E ⟶ C) {X Y : Over C} (m : OverHom X Y) :
    (baseChangeMap g m).f ≫ (_pb g Y).cone.π₂ = (_pb g X).cone.π₂ := baseChangeMap_f_π₂ g m

/-- **The `transApp` pentagon / 2-cocycle.**  Pushing the source along the composite `k ≤ m ≤ n`
    factors as the iterated push: `transApp (k≤m·n) ≫ transApp (m≤n)` equals
    `transApp (i·k≤n) ≫ F(m≤n)(transApp (i≤k…))`.  Both are arrows
    `F(trans hik (trans hkm hmn)) x ⟶ F hmn (F hkm (F hik x))`; geometrically the two ways to
    re-associate the iterated pullback of `x.hom` along `proj hik`, `proj hkm`, `proj hmn`.  Proved
    by pullback-`lift` uniqueness into the deepest pullback apex. -/
private theorem transApp_cocycle (P : ProjSystem ι D 𝒞) {i : ι} {k m n : ι}
    (hik : D.le i k) (hkm : D.le k m) (hmn : D.le m n) (x : pcObj P i) :
    transApp (laxOfProjSystem' P) hik (D.trans hkm hmn) x
        ≫ transApp (laxOfProjSystem' P) hkm hmn ((laxOfProjSystem' P).F hik x)
      = transApp (laxOfProjSystem' P) (D.trans hik hkm) hmn x
          ≫ Functor.map (self := (laxOfProjSystem' P).functF hmn)
              (transApp (laxOfProjSystem' P) hik hkm x) := by
  apply OverHom.ext
  show (transApp (laxOfProjSystem' P) hik (D.trans hkm hmn) x).f
        ≫ (transApp (laxOfProjSystem' P) hkm hmn (baseChangeObj (P.proj hik) x)).f
      = (transApp (laxOfProjSystem' P) (D.trans hik hkm) hmn x).f
        ≫ (baseChangeMap (P.proj hmn) (transApp (laxOfProjSystem' P) hik hkm x)).f
  -- Abbreviation for the two stacked inner `transApp`s, projected leg-by-leg via the clean
  -- `transApp_f_*` lemmas.  The codomain is the triple pullback `bc hmn (bc hkm (bc hik x))`.
  -- Every leaf reduces both sides to the SAME composite-pullback projection (equal up to
  -- `proj_trans` proof irrelevance on the `D.le i n` index), via the `transApp_f_*` leg lemmas.
  apply pb_hom_ext (_pb (P.proj hmn) (baseChangeObj (P.proj hkm) (baseChangeObj (P.proj hik) x)))
  · -- π₁ leg: lands in the inner double pullback `bc hkm (bc hik x)`; nest twice more.
    apply pb_hom_ext (_pb (P.proj hkm) (baseChangeObj (P.proj hik) x))
    · apply pb_hom_ext (_pb (P.proj hik) x)
      · -- innermost π₁ → `x.dom`
        simp only [Cat.assoc]
        rw [transApp_f_π₁π₁ P hkm hmn (baseChangeObj (P.proj hik) x),
            transApp_f_π₁π₁₀ P hik (D.trans hkm hmn) x,
            baseChangeMap_f_π₁' (P.proj hmn) (transApp (laxOfProjSystem' P) hik hkm x),
            transApp_f_π₁π₁₀ P hik hkm x, transApp_f_π₁π₁₀ P (D.trans hik hkm) hmn x]
      · -- innermost π₂ → `pr k`
        simp only [Cat.assoc]
        rw [transApp_f_π₁π₁ P hkm hmn (baseChangeObj (P.proj hik) x),
            transApp_f_π₁π₂₀ P hik (D.trans hkm hmn) x,
            baseChangeMap_f_π₁' (P.proj hmn) (transApp (laxOfProjSystem' P) hik hkm x),
            transApp_f_π₁π₂₀ P hik hkm x, transApp_f_π₁π₂ P (D.trans hik hkm) hmn x,
            P.proj_trans hkm hmn]
    · -- middle π₂ → `pr m`
      simp only [Cat.assoc]
      rw [transApp_f_π₁π₂₀ P hkm hmn (baseChangeObj (P.proj hik) x),
          transApp_f_π₂ P hik (D.trans hkm hmn) x,
          baseChangeMap_f_π₁' (P.proj hmn) (transApp (laxOfProjSystem' P) hik hkm x),
          transApp_f_π₂₀ P hik hkm x, transApp_f_π₁π₂₀ P (D.trans hik hkm) hmn x]
  · -- outer π₂ → `pr n`
    simp only [Cat.assoc]
    rw [transApp_f_π₂₀ P hkm hmn (baseChangeObj (P.proj hik) x),
        transApp_f_π₂₀ P hik (D.trans hkm hmn) x,
        baseChangeMap_f_π₂₀ (P.proj hmn) (transApp (laxOfProjSystem' P) hik hkm x),
        transApp_f_π₂₀ P (D.trans hik hkm) hmn x]

/-- `push_trans` for the base-change system. -/
public theorem proj_push_trans (P : ProjSystem ι D 𝒞)
    {i j : ι} (x : (laxOfProjSystem' P).A i) (y : (laxOfProjSystem' P).A j) {k m n : ι}
    (hik : D.le i k) (hjk : D.le j k) (hkm : D.le k m) (hmn : D.le m n)
    (g : (laxOfProjSystem' P).F hik x ⟶ (laxOfProjSystem' P).F hjk y) :
    pushHom (laxOfProjSystem' P) x y hik hjk (D.trans hkm hmn) g
      = pushHom (laxOfProjSystem' P) x y (D.trans hik hkm) (D.trans hjk hkm) hmn
          (pushHom (laxOfProjSystem' P) x y hik hjk hkm g) := by
  -- `key`: the source-naturality characterisation of `pushHom` (the `isoInv` cancels on the right).
  have key : ∀ {i' j' : ι} (x' : (laxOfProjSystem' P).A i') (y' : (laxOfProjSystem' P).A j')
      {k' m' : ι} (hik' : D.le i' k') (hjk' : D.le j' k') (hkm' : D.le k' m')
      (g' : (laxOfProjSystem' P).F hik' x' ⟶ (laxOfProjSystem' P).F hjk' y'),
      pushHom (laxOfProjSystem' P) x' y' hik' hjk' hkm' g'
          ≫ transApp (laxOfProjSystem' P) hjk' hkm' y'
        = transApp (laxOfProjSystem' P) hik' hkm' x'
          ≫ Functor.map (self := (laxOfProjSystem' P).functF hkm') g' := by
    intro i' j' x' y' k' m' hik' hjk' hkm' g'
    exact pushHom_transApp (laxOfProjSystem' P) x' y' hik' hjk' hkm' g'
  -- Naturality of `transApp hkm hmn (·)` at `g` (it is the component of `F_trans_iso hkm hmn`).
  have tnat := transApp_natural (laxOfProjSystem' P) hkm hmn g
  -- Cancel the iso `Φ_y := transApp(hjk, trans hkm hmn, y) ≫ transApp(hkm, hmn, F hjk y)`; both LHS
  -- and RHS post-composed with it equal a common arrow into `F hmn (F hkm (F hjk y))`.
  refine iso_cancel_right (Y' := (laxOfProjSystem' P).F hmn
      ((laxOfProjSystem' P).F hkm ((laxOfProjSystem' P).F hjk y)))
    (transApp (laxOfProjSystem' P) hjk (D.trans hkm hmn) y
        ≫ transApp (laxOfProjSystem' P) hkm hmn ((laxOfProjSystem' P).F hjk y))
    (isIso_comp (transApp_isIso (laxOfProjSystem' P) hjk (D.trans hkm hmn) y)
      (transApp_isIso (laxOfProjSystem' P) hkm hmn ((laxOfProjSystem' P).F hjk y))) ?_
  calc pushHom (laxOfProjSystem' P) x y hik hjk (D.trans hkm hmn) g
          ≫ (transApp (laxOfProjSystem' P) hjk (D.trans hkm hmn) y
              ≫ transApp (laxOfProjSystem' P) hkm hmn ((laxOfProjSystem' P).F hjk y))
      = (pushHom (laxOfProjSystem' P) x y hik hjk (D.trans hkm hmn) g
            ≫ transApp (laxOfProjSystem' P) hjk (D.trans hkm hmn) y)
          ≫ transApp (laxOfProjSystem' P) hkm hmn ((laxOfProjSystem' P).F hjk y) :=
        (Cat.assoc _ _ _).symm
    _ = (transApp (laxOfProjSystem' P) hik (D.trans hkm hmn) x
          ≫ Functor.map (self := (laxOfProjSystem' P).functF (D.trans hkm hmn)) g)
          ≫ transApp (laxOfProjSystem' P) hkm hmn ((laxOfProjSystem' P).F hjk y) := by rw [key]
    _ = transApp (laxOfProjSystem' P) hik (D.trans hkm hmn) x
          ≫ (Functor.map (self := (laxOfProjSystem' P).functF (D.trans hkm hmn)) g
              ≫ transApp (laxOfProjSystem' P) hkm hmn ((laxOfProjSystem' P).F hjk y)) :=
        Cat.assoc _ _ _
    _ = transApp (laxOfProjSystem' P) hik (D.trans hkm hmn) x
          ≫ (transApp (laxOfProjSystem' P) hkm hmn ((laxOfProjSystem' P).F hik x)
              ≫ Functor.map (self := (laxOfProjSystem' P).functF hmn)
                  (Functor.map (self := (laxOfProjSystem' P).functF hkm) g)) := by rw [tnat]; rfl
    _ = (transApp (laxOfProjSystem' P) hik (D.trans hkm hmn) x
          ≫ transApp (laxOfProjSystem' P) hkm hmn ((laxOfProjSystem' P).F hik x))
          ≫ Functor.map (self := (laxOfProjSystem' P).functF hmn)
              (Functor.map (self := (laxOfProjSystem' P).functF hkm) g) := (Cat.assoc _ _ _).symm
    _ = (transApp (laxOfProjSystem' P) (D.trans hik hkm) hmn x
          ≫ Functor.map (self := (laxOfProjSystem' P).functF hmn)
              (transApp (laxOfProjSystem' P) hik hkm x))
          ≫ Functor.map (self := (laxOfProjSystem' P).functF hmn)
              (Functor.map (self := (laxOfProjSystem' P).functF hkm) g) := by
        rw [transApp_cocycle P hik hkm hmn x]
    _ = transApp (laxOfProjSystem' P) (D.trans hik hkm) hmn x
          ≫ (Functor.map (self := (laxOfProjSystem' P).functF hmn)
                (transApp (laxOfProjSystem' P) hik hkm x)
              ≫ Functor.map (self := (laxOfProjSystem' P).functF hmn)
                  (Functor.map (self := (laxOfProjSystem' P).functF hkm) g)) := Cat.assoc _ _ _
    _ = transApp (laxOfProjSystem' P) (D.trans hik hkm) hmn x
          ≫ Functor.map (self := (laxOfProjSystem' P).functF hmn)
              (transApp (laxOfProjSystem' P) hik hkm x
                ≫ Functor.map (self := (laxOfProjSystem' P).functF hkm) g) := by
        rw [Functor.map_comp (self := (laxOfProjSystem' P).functF hmn)]
    _ = transApp (laxOfProjSystem' P) (D.trans hik hkm) hmn x
          ≫ Functor.map (self := (laxOfProjSystem' P).functF hmn)
              (pushHom (laxOfProjSystem' P) x y hik hjk hkm g
                ≫ transApp (laxOfProjSystem' P) hjk hkm y) := by rw [key]
    _ = transApp (laxOfProjSystem' P) (D.trans hik hkm) hmn x
          ≫ (Functor.map (self := (laxOfProjSystem' P).functF hmn)
                (pushHom (laxOfProjSystem' P) x y hik hjk hkm g)
              ≫ Functor.map (self := (laxOfProjSystem' P).functF hmn)
                  (transApp (laxOfProjSystem' P) hjk hkm y)) := by
        rw [Functor.map_comp (self := (laxOfProjSystem' P).functF hmn)]
    _ = (transApp (laxOfProjSystem' P) (D.trans hik hkm) hmn x
          ≫ Functor.map (self := (laxOfProjSystem' P).functF hmn)
              (pushHom (laxOfProjSystem' P) x y hik hjk hkm g))
          ≫ Functor.map (self := (laxOfProjSystem' P).functF hmn)
              (transApp (laxOfProjSystem' P) hjk hkm y) := (Cat.assoc _ _ _).symm
    _ = (pushHom (laxOfProjSystem' P) x y (D.trans hik hkm) (D.trans hjk hkm) hmn
            (pushHom (laxOfProjSystem' P) x y hik hjk hkm g)
          ≫ transApp (laxOfProjSystem' P) (D.trans hjk hkm) hmn y)
          ≫ Functor.map (self := (laxOfProjSystem' P).functF hmn)
              (transApp (laxOfProjSystem' P) hjk hkm y) := by rw [key]
    _ = pushHom (laxOfProjSystem' P) x y (D.trans hik hkm) (D.trans hjk hkm) hmn
            (pushHom (laxOfProjSystem' P) x y hik hjk hkm g)
          ≫ (transApp (laxOfProjSystem' P) (D.trans hjk hkm) hmn y
              ≫ Functor.map (self := (laxOfProjSystem' P).functF hmn)
                  (transApp (laxOfProjSystem' P) hjk hkm y)) := Cat.assoc _ _ _
    _ = pushHom (laxOfProjSystem' P) x y (D.trans hik hkm) (D.trans hjk hkm) hmn
            (pushHom (laxOfProjSystem' P) x y hik hjk hkm g)
          ≫ (transApp (laxOfProjSystem' P) hjk (D.trans hkm hmn) y
              ≫ transApp (laxOfProjSystem' P) hkm hmn ((laxOfProjSystem' P).F hjk y)) := by
        rw [transApp_cocycle P hjk hkm hmn y]

/-- **`.f`-projection characterisation of `pushHom` for the base-change system — the `π₂` (structure
    map) leg.**  The codomain `F (trans hjk hkm) y = baseChangeObj (proj (trans hjk hkm)) y` carries a
    pullback whose `π₂` is its over-`(pr m)` structure map.  Post-composing `(pushHom g).f` with the
    target collapse iso `(transApp hjk hkm y).f` lands in the nested pullback `bc hkm (bc hjk y)`,
    whose outer `π₂` is `proj`-pullback projection; `pushHom_transApp` then collapses the whole thing
    to the source side `(transApp hik hkm x).f ≫ (map g).f`.  Concretely this says `pushHom` preserves
    the deepest `(pr m)`-projection, i.e. it is an over-`(pr m)` arrow on the nose. -/
theorem proj_pushHom_f_π₂ (P : ProjSystem ι D 𝒞)
    {i j : ι} (x : (laxOfProjSystem' P).A i) (y : (laxOfProjSystem' P).A j) {k m : ι}
    (hik : D.le i k) (hjk : D.le j k) (hkm : D.le k m)
    (g : (laxOfProjSystem' P).F hik x ⟶ (laxOfProjSystem' P).F hjk y) :
    (pushHom (laxOfProjSystem' P) x y hik hjk hkm g).f
        ≫ (_pb (P.proj (D.trans hjk hkm)) y).cone.π₂
      = (_pb (P.proj (D.trans hik hkm)) x).cone.π₂ := by
  -- post-compose `pushHom_transApp` with the `π₂`-leg of the target collapse iso; both reduce to the
  -- deepest projection via `transApp_f_π₂₀` and `baseChangeMap_f_π₂₀`.
  have h : (pushHom (laxOfProjSystem' P) x y hik hjk hkm g).f
        ≫ (transApp (laxOfProjSystem' P) hjk hkm y).f
      = (transApp (laxOfProjSystem' P) hik hkm x).f
        ≫ (((laxOfProjSystem' P).functF hkm).map g).f :=
    congrArg OverHom.f (pushHom_transApp (laxOfProjSystem' P) x y hik hjk hkm g)
  have h₂ := congrArg (· ≫ (_pb (P.proj hkm) (baseChangeObj (P.proj hjk) y)).cone.π₂) h
  simp only at h₂
  rw [Cat.assoc, Cat.assoc, transApp_f_π₂₀ P hjk hkm y,
      show (((laxOfProjSystem' P).functF hkm).map g)
        = baseChangeMap (P.proj hkm) g from rfl,
      baseChangeMap_f_π₂₀ (P.proj hkm) g, transApp_f_π₂₀ P hik hkm x] at h₂
  exact h₂

/-- **`.f`-projection characterisation of `pushHom` for the base-change system — the `π₁` (content)
    leg.**  The codomain pullback `(_pb (proj (trans hjk hkm)) y)`'s `π₁` reaches `y.dom`; `pushHom g`
    intertwines it with the source pullback's `π₁` post-composed by the underlying `g.f`.  This is the
    on-the-nose statement that base-change `pushHom` is "`g.f` on the fibre over the `y.dom` factor",
    the content the §1.546 escape extracts.  Proven by post-composing `pushHom_transApp` (`.f`) with
    the `π₁∘π₁`-path of the target collapse iso (`transApp_f_π₁π₁`) and `baseChangeMap_f_π₁`. -/
public theorem proj_pushHom_f_π₁ (P : ProjSystem ι D 𝒞)
    {i j : ι} (x : (laxOfProjSystem' P).A i) (y : (laxOfProjSystem' P).A j) {k m : ι}
    (hik : D.le i k) (hjk : D.le j k) (hkm : D.le k m)
    (g : (laxOfProjSystem' P).F hik x ⟶ (laxOfProjSystem' P).F hjk y) :
    (pushHom (laxOfProjSystem' P) x y hik hjk hkm g).f
        ≫ (transApp (laxOfProjSystem' P) hjk hkm y).f
          ≫ (_pb (P.proj hkm) (baseChangeObj (P.proj hjk) y)).cone.π₁
      = (transApp (laxOfProjSystem' P) hik hkm x).f
          ≫ (_pb (P.proj hkm) (baseChangeObj (P.proj hik) x)).cone.π₁ ≫ g.f := by
  have h : (pushHom (laxOfProjSystem' P) x y hik hjk hkm g).f
        ≫ (transApp (laxOfProjSystem' P) hjk hkm y).f
      = (transApp (laxOfProjSystem' P) hik hkm x).f
        ≫ (((laxOfProjSystem' P).functF hkm).map g).f :=
    congrArg OverHom.f (pushHom_transApp (laxOfProjSystem' P) x y hik hjk hkm g)
  -- post-compose with the OUTER `π₁` (reaching `(F hjk y).dom = (bc (proj hjk) y).dom`).
  have h₂ := congrArg (· ≫ (_pb (P.proj hkm) (baseChangeObj (P.proj hjk) y)).cone.π₁) h
  simp only [Cat.assoc] at h₂
  rw [show (((laxOfProjSystem' P).functF hkm).map g)
        = baseChangeMap (P.proj hkm) g from rfl,
      baseChangeMap_f_π₁ (P.proj hkm) g] at h₂
  exact h₂

/-- **`Coherent (laxOfProjSystem' P)`** — the §1.547 base-change system is pseudofunctor-coherent. -/
@[expose] public def coherentProj (P : ProjSystem ι D 𝒞) : Coherent (laxOfProjSystem' P) where
  push_refl := proj_push_refl P
  push_trans := proj_push_trans P

/-- **The §1.547 relative-capitalization category `A*`** — the lax hom-colimit of the base-change
    slice system, as a concrete `Cat` instance (no `Coherent` hypothesis to supply). -/
@[expose] public noncomputable def ratCapCat (P : ProjSystem ι D 𝒞) : Cat (Obj (laxOfProjSystem' P)) :=
  laxColimCat (laxOfProjSystem' P) (coherentProj P)

end BaseChangeCoherent

end Freyd.LaxColim

/-!
════════════════════════════════════════════════════════════════════════════════════════════════
  DESIGN ASSESSMENT (§1.543 capitalization, filtered pseudo-colimit route) — NOW COMPLETE.
  §1.543 is PROVEN Sorry-free (`Freyd.capitalization_lemma`); the former "NEXT BLOCKER" below
  (`Coherent (laxOfProjSystem' P)`) is discharged by `coherentProj`.
════════════════════════════════════════════════════════════════════════════════════════════════

WHAT THIS FILE ESTABLISHES (all Sorry-free, axiom-free):

  * `LaxCatSystem` — the missing abstraction: a directed system of categories whose transitions are
    FUNCTORS with coherence given as natural ISOS (`F_refl_iso`/`F_trans_iso`), not strict
    equalities.  This is the exact interface base-change can inhabit; the strict `Colim.CatSystem`
    (`F_refl`/`F_trans` on-the-nose equalities) cannot, which is the documented §1.543 wall
    (`StrictBaseChange` is FALSE for raw base-change).
  * `ofStrict` — every strict `Colim.CatSystem` is a `LaxCatSystem`; the lax interface strictly
    generalises the strict one (via `natIsoOfPointwise` + `heq_eqToHom_conj`).  Nothing is lost.
  * `Obj`/`objIncl` — the colimit's OBJECT carrier is the bare `Σ i, A i` (no quotient): for a
    FILTERED colimit of categories the objects are kept distinct (the colimit is non-skeletal), so
    no transition law on objects is needed.  Same carrier `CapitalizationGroth.lean` uses, but here
    it costs nothing and is correct for the lax setting.
  * `ProjSystem`/`pcF`/`pcFunctF`/`laxOfProjSystem`/`laxOfProjSystem'` — the §1.547 inner base-change
    slice system (`A/(∏U)`, base-change transitions over the filtered `listDirected`) as a
    `LaxCatSystem`, the lax analogue of `Freyd.innerCatSystem` but WITHOUT the false
    `StrictBaseChange`.  `laxOfProjSystem'` is UNCONDITIONAL (no hypothesis).
  * `baseChangeIdNatIso` + `projReflIso` — the REFLEXIVE coherence iso `baseChangeObj (id) ≅ id`,
    PROVEN (pullback along an identity is iso).
  * `pasteCone_isPullback` + `baseChangeTransNatIso` + `projTransIso` + `pseudoBaseChange` — the
    COMPOSITE coherence iso `baseChangeObj (g' ≫ g) ≅ baseChangeObj g' ∘ baseChangeObj g`, PROVEN:
    the two-pullback pasting lemma gives a second pullback of the same cospan, `isIso_of_two_pullbacks`
    makes the comparison `lift` an iso, naturality is `lift`-uniqueness.  Built constructively from
    the chosen pullbacks' `lift` (NO `Classical.choice`; `#print axioms` = `propext` only).  So
    `PseudoBaseChange` is now FULLY discharged — both coherence fields are real.

WHY THE FILTERED ROUTE (this file) BEATS THE TRANSFINITE TOWER (`CapitalizationGroth.lean`):

  * The tower indexes by a well-order with LIMIT ordinals and needs cross-stage `belowObjAgree`/
    `belowCoherent` (5 `Sorry`s bottoming out in `CapitalizationTower.lean`) plus `gLimTopPre`.
  * Here the index `listDirected` is FILTERED (any two finite lists have an upper bound = append);
    there are NO limit ordinals, NO `below*` agreement, NO transfinite coherence.  The Σ-object
    carrier is unconditional, and the coherence is entirely on hom-sets / per-pair transition isos.

`PseudoBaseChange.trans_iso` — DISCHARGED (was the prior NEXT BLOCKER):

    `baseChangeObj (g' ≫ g) X  ≅  baseChangeObj g' (baseChangeObj g X)`   as a `NatIso`,

  the iterated-pullback (pullback-pasting) natural isomorphism — pulling `X.hom` back along the
  composite `g' ≫ g` equals pulling back along `g` then along `g'`.  Proven by `baseChangeTransNatIso`
  (apices `(X ×_C B) ×_B A ≅ X ×_C A` via `pasteCone_isPullback` + `isIso_of_two_pullbacks`;
  naturality by `lift`-uniqueness), and discharged for every `ProjSystem` by `projTransIso` /
  `pseudoBaseChange`.  Needs only `HasPullbacks 𝒞`; constructive (no choice, no transfinite recursion).

THE PSEUDO HOM-COLIMIT + `Cat` INSTANCE — DONE (was the prior NEXT BLOCKER):

  A morphism `⟨i,x⟩ → ⟨j,y⟩` is a germ of `Hom_{A k}(F_{ik} x, F_{jk} y)` over upper bounds `k`,
  with germ equivalence transported along the COHERENCE ISOS via `pushHom` (iso-conjugation, the
  lax analogue of the strict `castHom`-based `homTr`).  Now built, Sorry-free:

    * `pushHom` / `transApp` / `isoInv` — the lax hom-transition: map along `F hkm`, conjugate by the
      `F_trans_iso` components (forward on source, inverse on target).
    * `pushHom_comp` / `pushHom_id` — `pushHom` is functorial on hom-sets; PROVEN from the bare
      structure (iso cancellation + `map_comp`/`map_id`), NEEDS NO extra coherence.
    * `LaxCatSystem.Coherent` — the two pseudofunctor coherences `pushHom` needs as `System` laws:
      `push_refl` (UNIT: pushing along `refl` = id) and `push_trans` (ASSOCIATIVITY: pushing along a
      composite bound = pushing twice).  TRUE for base-change (the pullback pasting coherences),
      unlike the strict `CatSystem.Coherent` which is FALSE for base-change.
    * `homSystemL` / `HomColimL` / `homInclL` — the germ hom-colimit as a `Colim.System`
      (`tr_refl`/`tr_trans` = `push_refl`/`push_trans`), so the strict `DirectedColimit` germ
      machinery (`Colimit`, `incl`, `incl_compat`, the universal property) applies verbatim.
    * `compAtL` / `compAtL_mono` / `compAtL_indep` / `homCompRawL` / `homCompRawL_wd` — bound-coherent
      germ composition + well-definedness on BOTH germ quotients.
    * `compL` / `idL` / `homL` — composition, identity, hom-type on the bare Σ-carrier `Obj L`
      (NO `Quotient.out`/choice on objects, unlike the strict `colimitCat`).
    * `compL_id_left` / `compL_id_right` / `compL_assoc` — the three `Cat` axioms.
    * `laxColimCat : Cat (Obj L)` — THE CATEGORY.  `#print axioms` = `Classical.choice`, `Quot.sound`,
      `propext` (NO `SorryAx`).  The `Classical.choice` is forced only by the interface
      (`IsIso := ∃ g, …` is a Prop, so the inverse arrow `isoInv` is extracted by choice; and the raw
      composite picks a bound by `D.bound`'s choice) — never by faking mathematical content.

THE FORMER NEXT BLOCKER — DISCHARGED — `Coherent (laxOfProjSystem' P)` for the §1.547 base-change
system: `push_refl`/`push_trans` for `pushHom` built from the pullback coherence isos
`projReflIso`/`projTransIso`.  Unfolding `pushHom`, `push_refl` is the pullback UNIT-coherence
(`baseChangeIdNatIso` interacting with `D.refl`) and `push_trans` is the pullback PENTAGON /
2-cocycle condition relating `baseChangeTransNatIso (proj hkm) (proj hmn)` to the iterated
single-step transports — the standard coherence of the pullback pseudofunctor.
Both are equalities of arrows between fixed pullback apices, proved by pullback-`lift` uniqueness
(every leg matches), as `coherentProj` (`proj_push_refl`/`proj_push_trans`).  With it,
`laxColimCat (laxOfProjSystem' P)` (= `ratCapCat P`) IS the §1.547 relative capitalization `A*` as
an honest category, and `PreRegular (ratCapCat P)` follows (`RatCapPreReg`/`RatCapStagePTC`/
`RatCapHcanon`); §1.543 is proven.
-/

