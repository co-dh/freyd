/-
  §1.543 — PRE-REGULARITY of the FILTERED lax colimit `ratCapCat P` (the §1.547 relative
  capitalization `A*`).

  ════════════════════════════════════════════════════════════════════════════════════════════
  GOAL.  `CapitalizationLaxColimit.lean` builds, Sorry-free, the §1.547 relative capitalization
  `A* = ratCapCat P : Cat (Obj (laxOfProjSystem' P))` — the FILTERED lax colimit of the slices
  `A/(∏U) = Over (listProd U)` over the filtered index of finite ws-lists, with BASE-CHANGE
  transitions (a pseudofunctor, coherence supplied as natural isos `F_refl_iso`/`F_trans_iso`,
  never strict equalities).  Each fibre `Over (listProd U)` is `PreRegularCategory`
  (`overPreRegular`, `SliceRegular.lean`).

  This file transfers PRE-REGULARITY to the colimit:  `PreRegularCategory (ratCapCat P)`.  The
  principle is "FILTERED colimits commute with FINITE limits": a finite diagram in the colimit,
  pushed along transitions to a COMMON upper stage (filtered: any finite index set has a bound),
  lives in a single fibre, where the fibre's finite limit is computed and then included.

  It MIRRORS the STRICT analogue `Colim.colimitPreRegular` (`CatColimitRegular.lean:2450`), which
  proves exactly this for the STRICT colimit, replacing strict `castHom`/object-equalities with the
  lax `pushHom`/coherence-isos.  The crucial SIMPLIFICATION over the strict file: the lax colimit's
  objects are the bare `Σ i, A i` (`Obj L`), so every object is LITERALLY `objIncl i x = ⟨i,x⟩` —
  there is NO `colimOut`/`Quotient.out` representative-section to fight (the strict file's pervasive
  `colimOut`/`colimOut_spec` machinery simply vanishes).

  ADAPTATION PLAN from `colimitPreRegular` (the strict assembly takes per-fibre limit existence
  PLUS the transitions' finite-limit PRESERVATION; the lax version takes the same):

    * `HasTerminal`  — strict `colimitHasTerminal` needs `ht i` + `hpres : F hij one = one`
      (strict).  Lax: the pushed terminal `F hij (ht i).one` is again TERMINAL (true for
      base-change: `g* ⟨pr i, id⟩ ≅ ⟨pr j, id⟩`); state that as the preservation hypothesis and the
      whole proof goes through with `homInclL`/`pushHom` in place of `homIncl`/`castHom`.  DONE here.
    * `HasBinaryProducts`/`HasEqualizers`/`HasPullbacks` — push the two/one objects to a common
      stage, take the fibre limit, include; universal property via the germ colimit + the fibres'
      limit-preservation across transitions.  (Mirrors `colimitHasBinaryProducts`/`…Equalizers`/
      `…Pullbacks`.)  NEXT.
    * `PullbacksTransferCovers` — a colimit cover + pullback align to a common fibre where the
      fibre's PTC applies; transfer back (mirrors `colimitPullbacksTransferCovers`).
    * assemble `PreRegularCategory (ratCapCat P)` (mirrors `colimitPreRegular`).

  Mathlib-free; built on the repo's own `Cat` + `Freyd.LaxColim` (`CapitalizationLaxColimit.lean`).
-/
module

public import Freyd.S1_543_CapitalizationLaxColimit

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

universe u w

variable {ι : Type u} {D : Directed ι}

/-! ## §M3a (lax) — the terminal object of the lax colimit category

  Mirrors `Colim.colimitHasTerminal`.  Pick any stage `i₀` (filtered ⇒ nonempty needed) and let the
  colimit terminal be `objIncl i₀ (ht i₀).one`.  Unlike the strict version there is NO `colimOut`:
  the terminal IS literally `⟨i₀, (ht i₀).one⟩`.

  The preservation hypothesis is the LAX analogue of the strict `hpres : F hij one = one`.  In the
  lax world `F hij (ht i).one` is only ISO to `(ht j).one`, so the strict equation is false; instead
  we ask that the pushed terminal is again a TERMINAL OBJECT (its own `HasTerminal`-witness in
  `L.A j`).  This is exactly what base-change supplies (`g*` of the slice terminal is the slice
  terminal up to iso, and an isomorph of a terminal is terminal), and it is all the proof needs. -/
section LaxTerminal

variable (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L)

/-- LAX terminal-preservation: each fibre has a terminal `ht i`, and the pushed terminal
    `L.F hij (ht i).one` is again terminal in the target fibre `L.A j` (an isomorph of `(ht j).one`).
    For base-change this holds: `g*` carries the slice terminal `⟨pr i, id⟩` to `⟨pr j, id⟩` up to
    iso, and any isomorph of a terminal is terminal. -/
public structure LaxTerminalData where
  /-- each fibre has a terminal -/
  ht : ∀ i, HasTerminal (L.A i)
  /-- the unique map of any object to the pushed terminal -/
  pushTrm : ∀ {i j} (hij : D.le i j) (X : L.A j), X ⟶ L.F hij (ht i).one
  /-- pushed terminal is terminal: maps into it are unique -/
  pushUniq : ∀ {i j} (hij : D.le i j) {X : L.A j}
    (f g : X ⟶ L.F hij (ht i).one), f = g

/-- **§M3a (lax): the lax colimit category has a terminal.**  The terminal is `objIncl i₀ one` for a
    chosen stage `i₀`.  The unique map from `⟨jX, xX⟩` pushes both to a common bound `k`, mapping
    `xX` to the pushed terminal via `pushTrm`; uniqueness is `pushUniq` after pushing two germ
    representatives to a common bound (and absorbing the level shift by `pushHom`/germ equivalence). -/
@[expose] public noncomputable def laxColimHasTerminal [hne : Nonempty ι] (T : LaxTerminalData L) :
    @HasTerminal (Obj L) (laxColimCat L hL) := by
  letI : Cat (Obj L) := laxColimCat L hL
  let i₀ : ι := Classical.choice hne
  let one : Obj L := objIncl L i₀ (T.ht i₀).one
  refine @HasTerminal.mk (Obj L) (laxColimCat L hL) one ?_ ?_
  · -- trm: a morphism `⟨jX, xX⟩ ⟶ one` for every object `X`.
    intro X
    obtain ⟨jX, xX⟩ := X
    -- common bound `k` of `jX` and `i₀` (chosen by `D.bound`; `trm` returns a `Type`, so `choose`).
    let bd := D.bound jX i₀
    let k := Classical.choose bd
    have hk : D.le jX k ∧ D.le i₀ k := Classical.choose_spec bd
    -- the germ of `pushTrm : F (jX≤k) xX ⟶ F (i₀≤k) one` at the upper bound `⟨k, hk.1, hk.2⟩`.
    exact homInclL L hL xX (T.ht i₀).one ⟨k, hk.1, hk.2⟩ (T.pushTrm hk.2 (L.F hk.1 xX))
  · -- uniq: any two germs `⟨jX,xX⟩ ⟶ one` are equal.
    intro X f g
    obtain ⟨jX, xX⟩ := X
    refine Quotient.inductionOn f (fun ⟨a, fa⟩ => ?_)
    refine Quotient.inductionOn g (fun ⟨b, gb⟩ => ?_)
    -- push both representatives to a common bound `k'` of `a.1`, `b.1`; there the targets are the
    -- pushed terminal `F (trans a.2.2 …) one`, so `pushUniq` equates them.
    apply Quotient.sound
    obtain ⟨k', hak', hbk'⟩ := D.bound a.1 b.1
    -- witness the germ relation at the upper bound `⟨k', …⟩` of `⟨jX, xX⟩, ⟨i₀, one⟩`.
    refine ⟨⟨k', D.trans a.2.1 hak', D.trans a.2.2 hak'⟩, hak', hbk', ?_⟩
    -- both `pushHom … fa` and `pushHom … gb` are arrows into the pushed terminal
    -- `F (D.trans a.2.2 hak') one = F (D.trans b.2.2 hbk') one` (proof-irrelevant `D.le i₀ k'`).
    exact T.pushUniq (D.trans a.2.2 hak') _ _

end LaxTerminal

/-! ## The reflexive coherence component `reflApp` (lax analogue of `transApp`)

  `transApp` (in `CapitalizationLaxColimit.lean`) extracts the forward component of `F_trans_iso`.
  Its UNIT counterpart `reflApp` extracts the forward component of `F_refl_iso`: at an object `x` of
  `L.A i` it is the canonical iso `L.F (D.refl i) x ⟶ x` (base-change of the identity onto `x`).
  This is the conjugator that turns a STAGE morphism `f : x ⟶ y` in `L.A i` into a single-stage germ
  representative `reflApp x ≫ f ≫ inv (reflApp y) : L.F (refl i) x ⟶ L.F (refl i) y`, the building
  block of the stage-inclusion functor and of every finite-limit cone in the colimit. -/
section ReflApp

variable (L : LaxCatSystem.{u, w} ι D)

/-- The forward component of the reflexive coherence iso `F_refl_iso` at an object `x : L.A i`:
    the canonical iso `L.F (D.refl i) x ⟶ x`. -/
@[expose] public def reflApp {i : ι} (x : L.A i) : L.F (D.refl i) x ⟶ x :=
  L.F_refl_iso.nat.app x

/-- `reflApp` is an isomorphism (it is a component of the natural iso `F_refl_iso`). -/
public theorem reflApp_isIso {i : ι} (x : L.A i) : IsIso (reflApp L x) :=
  L.F_refl_iso.isIso x

/-- **Naturality of `reflApp`.**  `reflApp` is the component of the natural iso `F_refl_iso`, so for
    any `f : x ⟶ y` in `L.A i` it intertwines the reflexive transition `F (refl i)` with the
    identity functor: `(F (refl i)).map f ≫ reflApp y = reflApp x ≫ f`. -/
theorem reflApp_natural {i : ι} {x y : L.A i} (f : x ⟶ y) :
    (L.functF (D.refl i)).map f
        ≫ reflApp L y
      = reflApp L x ≫ f :=
  L.F_refl_iso.nat.naturality f

/-- **`reflApp` of `laxOfProjSystem'` IS the reflexive base-change pullback `π₁`.**  `reflApp` is the
    `.nat.app` of `projReflIso`, which is `baseChangeIdNatIso` (component `_idBwd = π₁`) transported
    along `P.proj_refl i : P.proj (D.refl i) = Cat.id`; the transport `eqToHom` collapses against the
    chosen pullback's `π₁` by `eqToHom_bc_π₁`, leaving the reflexive pullback's first projection. -/
public theorem reflApp_f_π₁ {𝒞 : Type w} [Cat.{w} 𝒞] [HasPullbacks 𝒞] {ι : Type u} {D : Directed ι}
    (P : ProjSystem ι D 𝒞) {i : ι} (x : pcObj P i) :
    (reflApp (laxOfProjSystem' P) x).f = (_pb (P.proj (D.refl i)) x).cone.π₁ := by
  show ((projReflIso P i).nat.app x).f = _
  unfold projReflIso
  simp only [id_eq]
  rw [mpr_natiso_app (P.proj_refl i) baseChangeIdNatIso x]
  exact eqToHom_bc_π₁ (P.proj_refl i) x

end ReflApp

/-! ## A stage iso includes to a colimit iso (lax `colimHom_isIso_of_rep`)

  If a germ representative `f₀ : L.F a.2.1 x ⟶ L.F a.2.2 y` at a common bound `a` has a two-sided
  stage inverse `g₀`, then its inclusion `homInclL … a f₀` is an ISO in `laxColimCat L hL`.  The
  inverse is the germ of `g₀` at the swapped bound; both round-trips reduce — at the same stage `a.1`
  via `homCompRawL_eq_compAtL` + `push_refl` + `pushHom_id` — to the included stage identity, which
  is the colimit identity by `homInclL_compat`.  Mirrors the strict `colimHom_isIso_of_rep`, but the
  bare-sigma objects remove all `colimOut` transport. -/
public theorem homInclL_isIso_of_rep (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L)
    {i j : ι} (x : L.A i) (y : L.A j) (a : UpperBound D i j)
    (f₀ : L.F a.2.1 x ⟶ L.F a.2.2 y) (g₀ : L.F a.2.2 y ⟶ L.F a.2.1 x)
    (h1 : f₀ ≫ g₀ = Cat.id (L.F a.2.1 x)) (h2 : g₀ ≫ f₀ = Cat.id (L.F a.2.2 y)) :
    @IsIso (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨j, y⟩
      (homInclL L hL x y a f₀) := by
  letI : Cat (Obj L) := laxColimCat L hL
  obtain ⟨av, ah1, ah2⟩ := a
  refine ⟨homInclL L hL y x ⟨av, ah2, ah1⟩ g₀, ?_, ?_⟩
  · -- f₀ ⊚ g₀ = id at level `av`: reduce to the stage composite `f₀ ≫ g₀ = id`, then `homInclL_compat`.
    show homCompRawL L hL x y x ⟨av, ah1, ah2⟩ f₀ ⟨av, ah2, ah1⟩ g₀ = idL L hL ⟨i, x⟩
    rw [homCompRawL_eq_compAtL L hL x y x ⟨av, ah1, ah2⟩ f₀ ⟨av, ah2, ah1⟩ g₀ av (D.refl av) (D.refl av)]
    unfold compAtL
    rw [hL.push_refl x y ah1 ah2 f₀, hL.push_refl y x ah2 ah1 g₀, h1]
    show homInclL L hL x x ⟨av, ah1, ah1⟩ (Cat.id (L.F ah1 x)) = idL L hL ⟨i, x⟩
    rw [show (idL L hL ⟨i, x⟩ : homL L hL ⟨i,x⟩ ⟨i,x⟩) = homIdL L hL x from rfl, homIdL,
        ← pushHom_id L x (D.refl i) ah1]
    exact homInclL_compat L hL x x (a := ⟨i, D.refl i, D.refl i⟩) (b := ⟨av, ah1, ah1⟩) ah1 (Cat.id _)
  · show homCompRawL L hL y x y ⟨av, ah2, ah1⟩ g₀ ⟨av, ah1, ah2⟩ f₀ = idL L hL ⟨j, y⟩
    rw [homCompRawL_eq_compAtL L hL y x y ⟨av, ah2, ah1⟩ g₀ ⟨av, ah1, ah2⟩ f₀ av (D.refl av) (D.refl av)]
    unfold compAtL
    rw [hL.push_refl y x ah2 ah1 g₀, hL.push_refl x y ah1 ah2 f₀, h2]
    show homInclL L hL y y ⟨av, ah2, ah2⟩ (Cat.id (L.F ah2 y)) = idL L hL ⟨j, y⟩
    rw [show (idL L hL ⟨j, y⟩ : homL L hL ⟨j,y⟩ ⟨j,y⟩) = homIdL L hL y from rfl, homIdL,
        ← pushHom_id L y (D.refl j) ah2]
    exact homInclL_compat L hL y y (a := ⟨j, D.refl j, D.refl j⟩) (b := ⟨av, ah2, ah2⟩) ah2 (Cat.id _)

/-! ## Interface bundles for the remaining finite limits (products, equalizers, pullbacks, PTC)

  These mirror the STRICT `colimitPreRegular`'s hypothesis tuples (`CatColimitRegular.lean:2450`):
  per-fibre limit existence PLUS the transitions' finite-limit PRESERVATION, packaged as one
  structure each.  In the STRICT setting preservation is phrased with `C.functF hij`; here the same
  shape applies verbatim with `L.functF hij` (each `L.F hij` is a genuine `Functor`).  For
  base-change these hypotheses are TRUE (the pullback functor `g*` preserves all finite limits —
  it is a right adjoint), so each bundle is inhabitable; discharging them for `laxOfProjSystem' P`
  is downstream work.

  The universal-property assembly (turning a bundle into a `HasBinaryProducts`/… instance on
  `laxColimCat L hL`) is the germ-algebra mirror of `colimitHasBinaryProducts`/`…Equalizers`/
  `…Pullbacks`; it is the precise NEXT BLOCKER (see the end of this file). -/

/-- LAX binary-product preservation bundle (mirrors `colimitHasBinaryProducts`'s `hp`/`hpres`/
    `hpres_pair`).  `hp` gives per-fibre products; `pres` is joint-monic preservation under a
    transition; `presPair` is pairing preservation under a transition. -/
public structure LaxProductData (L : LaxCatSystem.{u, w} ι D) where
  hp : ∀ i, HasBinaryProducts (L.A i)
  pres : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
      (u v : z ⟶ L.F hij ((hp i).prod a b)),
      u ≫ (L.functF hij).map (hp i).fst = v ≫ (L.functF hij).map (hp i).fst →
      u ≫ (L.functF hij).map (hp i).snd = v ≫ (L.functF hij).map (hp i).snd → u = v
  presPair : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
      (p : z ⟶ L.F hij a) (q : z ⟶ L.F hij b),
      ∃ r : z ⟶ L.F hij ((hp i).prod a b),
        r ≫ (L.functF hij).map (hp i).fst = p ∧ r ≫ (L.functF hij).map (hp i).snd = q

/-- LAX equalizer-preservation bundle (mirrors `colimitHasEqualizers`'s `he`/`hepres`/`hepres_lift`). -/
public structure LaxEqualizerData (L : LaxCatSystem.{u, w} ι D) where
  he : ∀ i, HasEqualizers (L.A i)
  pres : ∀ {i j} (hij : D.le i j) {A B : L.A i} (f g : A ⟶ B) (z : L.A j)
      (u v : z ⟶ L.F hij (eqObj f g)),
      u ≫ (L.functF hij).map (eqMap f g) = v ≫ (L.functF hij).map (eqMap f g) → u = v
  presLift : ∀ {i j} (hij : D.le i j) {A B : L.A i} (f g : A ⟶ B) (z : L.A j)
      (k : z ⟶ L.F hij A)
      (_hk : k ≫ (L.functF hij).map f = k ≫ (L.functF hij).map g),
      ∃ r : z ⟶ L.F hij (eqObj f g), r ≫ (L.functF hij).map (eqMap f g) = k

/-! ## §M3b (lax) — binary products of the lax colimit category

  Mirrors `Colim.colimitHasBinaryProducts`.  For `⟨i,x⟩ × ⟨j,y⟩` pick a common bound `k` (filtered);
  the product object is the bare `⟨k, (hp k).prod (F x) (F y)⟩`.  Projections are SINGLE-STAGE germs
  `reflApp ≫ (hp k).fst|snd` at the trivial bound `⟨k, refl k, hik⟩` — no `colimOut`/`kp` transport,
  because the product object lives literally at stage `k`.  `pair` mediates via `presPair` at a common
  competitor stage; the laws push competitors to a common stage and apply `pres`. -/
section LaxProduct

variable (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L) (data : LaxProductData L)

/-- Common product bound of `i,j`. -/
@[expose] public noncomputable def prK (D : Directed ι) (i j : ι) : ι := Classical.choose (D.bound i j)
public theorem prK_le (D : Directed ι) (i j : ι) : D.le i (prK D i j) ∧ D.le j (prK D i j) :=
  Classical.choose_spec (D.bound i j)

/-- The product object `⟨k, (hp k).prod (F x) (F y)⟩` in `Obj L`. -/
@[expose] public noncomputable def prObj {i j : ι} (x : L.A i) (y : L.A j) : Obj L :=
  ⟨prK D i j, (data.hp (prK D i j)).prod (L.F (prK_le D i j).1 x) (L.F (prK_le D i j).2 y)⟩

/-- The `fst` projection germ: `reflApp ≫ (hp k).fst` at bound `⟨k, refl k, hik⟩`. -/
@[expose] public noncomputable def prFst {i j : ι} (x : L.A i) (y : L.A j) :
    homL L hL (prObj L data x y) ⟨i, x⟩ :=
  homInclL L hL ((data.hp (prK D i j)).prod (L.F (prK_le D i j).1 x) (L.F (prK_le D i j).2 y)) x
    ⟨prK D i j, D.refl (prK D i j), (prK_le D i j).1⟩
    (reflApp L _ ≫ (data.hp (prK D i j)).fst)

/-- The `snd` projection germ. -/
@[expose] public noncomputable def prSnd {i j : ι} (x : L.A i) (y : L.A j) :
    homL L hL (prObj L data x y) ⟨j, y⟩ :=
  homInclL L hL ((data.hp (prK D i j)).prod (L.F (prK_le D i j).1 x) (L.F (prK_le D i j).2 y)) y
    ⟨prK D i j, D.refl (prK D i j), (prK_le D i j).2⟩
    (reflApp L _ ≫ (data.hp (prK D i j)).snd)

/-! ### The "unit conjugator" `U`

  Pushing the projection germ `reflApp p ≫ fst` from `k` to `m` produces the prefactor
  `transApp (refl k) hkm p ≫ (functF hkm).map (reflApp p) : F (trans (refl k) hkm) p ⟶ F hkm p`.
  This composite of two coherence isos is itself an iso `U`; it has no closed form (no pseudofunctor
  triangle is assumed in `Coherent`), so we keep it abstract and CANCEL it by building the pair
  germ's representative with `isoInv U` baked in.  Both projections share the same `U` (same
  `reflApp p` source side), so one inverse serves both legs. -/
@[expose] public noncomputable def prUnit {k m : ι} (p : L.A k) (hkm : D.le k m) :
    L.F (D.trans (D.refl k) hkm) p ⟶ L.F hkm p :=
  transApp L (D.refl k) hkm p ≫ (L.functF hkm).map (reflApp L p)

public theorem prUnit_isIso {k m : ι} (p : L.A k) (hkm : D.le k m) :
    IsIso (prUnit L p hkm) :=
  isIso_comp (transApp_isIso L (D.refl k) hkm p)
    (functor_preserves_iso (F := L.functF hkm) (reflApp L p) (reflApp_isIso L p))

/-- Pushing a single-stage projection germ `reflApp p ≫ proj` from `k` to `m` (along `hkm`) equals
    `prUnit ≫ (functF hkm).map proj ≫ isoInv (transApp hik hkm tgt)`.  Unfold `pushHom`, distribute
    `map` over the composite, and fold the `transApp ≫ map reflApp` prefactor into `prUnit`. -/
public theorem pushHom_proj {i k m : ι} (x : L.A i) (p : L.A k)
    (hik : D.le i k) (hkm : D.le k m) (proj : p ⟶ L.F hik x) :
    pushHom L p x (D.refl k) hik hkm (reflApp L p ≫ proj)
      = prUnit L p hkm
        ≫ (L.functF hkm).map proj
        ≫ isoInv (transApp_isIso L hik hkm x) := by
  unfold pushHom prUnit
  rw [(L.functF hkm).map_comp (reflApp L p) proj]
  simp only [Cat.assoc]

/-- **Existence of the pairing mediator.**  For competitor germs `f : ⟨l,z⟩ ⟶ ⟨i,x⟩`,
    `g : ⟨l,z⟩ ⟶ ⟨j,y⟩`, push both to a common stage `m ≥ k`, convert their targets to
    `F hkm (F hik x)`/`F hkm (F hjk y)` by `transApp`, apply `presPair`, and bake `isoInv prUnit`
    into the resulting germ so the projection's `prUnit` prefactor cancels. -/
public theorem prPairExists {i j : ι} (x : L.A i) (y : L.A j) {l : ι} (z : L.A l)
    (f : @Quotient _ (setoid (homSystemL L hL z x))) (g : @Quotient _ (setoid (homSystemL L hL z y))) :
    ∃ h : homL L hL ⟨l, z⟩ (prObj L data x y),
      compL L hL h (prFst L hL data x y) = f ∧ compL L hL h (prSnd L hL data x y) = g := by
  refine Quotient.inductionOn f (fun rf => ?_)
  refine Quotient.inductionOn g (fun rg => ?_)
  obtain ⟨af, fa⟩ := rf
  obtain ⟨ag, ga⟩ := rg
  let k := prK D i j
  have hik : D.le i k := (prK_le D i j).1
  have hjk : D.le j k := (prK_le D i j).2
  let ak := L.F hik x
  let bk := L.F hjk y
  let p := (data.hp k).prod ak bk
  -- common stage `m ≥ af.1, ag.1, k`.
  obtain ⟨e1, he1a, he1b⟩ := D.bound af.1 ag.1
  obtain ⟨m, hme, hmk⟩ := D.bound e1 k
  have hafm : D.le af.1 m := D.trans he1a hme
  have hagm : D.le ag.1 m := D.trans he1b hme
  have hkm : D.le k m := hmk
  have hlm : D.le l m := D.trans af.2.1 hafm
  -- convert pushed competitors' targets to `F hkm ak` / `F hkm bk` via `transApp`.
  let p_comp : L.F hlm z ⟶ L.F hkm ak :=
    pushHom L z x af.2.1 af.2.2 hafm fa ≫ transApp L hik hkm x
  let q_comp : L.F hlm z ⟶ L.F hkm bk :=
    pushHom L z y ag.2.1 ag.2.2 hagm ga ≫ transApp L hjk hkm y
  obtain ⟨r, hr_fst, hr_snd⟩ := data.presPair hkm ak bk (L.F hlm z) p_comp q_comp
  -- both legs share the cancellation `r' ≫ pushHom(reflApp ≫ proj) = (pushed competitor)`, where the
  -- pair germ rep `r' = r ≫ isoInv prUnit` bakes in the inverse unit so `prUnit` cancels.
  have leg : ∀ (i' : ι) (w : L.A i') (hi'k : D.le i' k) (proj : p ⟶ L.F hi'k w)
      (aw : UpperBound D l i') (wa : L.F aw.2.1 z ⟶ L.F aw.2.2 w) (hawm : D.le aw.1 m),
      r ≫ (L.functF hkm).map proj
          = pushHom L z w aw.2.1 aw.2.2 hawm wa ≫ transApp L hi'k hkm w →
      @compL _ _ L hL ⟨l, z⟩ ⟨k, p⟩ ⟨i', w⟩
          (homInclL L hL z p ⟨m, hlm, hkm⟩ (r ≫ isoInv (prUnit_isIso L p hkm)))
          (homInclL L hL p w ⟨k, D.refl k, hi'k⟩ (reflApp L p ≫ proj))
        = Quotient.mk (setoid (homSystemL L hL z w)) ⟨aw, wa⟩ := by
    intro i' w hi'k proj aw wa hawm hcomp
    -- reduce the colimit composite to a stage composite at level `m`.
    show homCompRawL L hL z p w ⟨m, hlm, hkm⟩ (r ≫ isoInv (prUnit_isIso L p hkm))
        ⟨k, D.refl k, hi'k⟩ (reflApp L p ≫ proj)
      = homInclL L hL z w aw wa
    rw [homCompRawL_eq_compAtL L hL z p w ⟨m, hlm, hkm⟩ (r ≫ isoInv (prUnit_isIso L p hkm))
          ⟨k, D.refl k, hi'k⟩ (reflApp L p ≫ proj) m (D.refl m) hkm]
    unfold compAtL
    -- left push along `refl m` is the identity (`push_refl`); right push is `pushHom_proj`.
    rw [hL.push_refl z p hlm hkm (r ≫ isoInv (prUnit_isIso L p hkm)),
        pushHom_proj L w p hi'k hkm proj]
    -- cancel `r' ≫ prUnit = r` (by `inv_isoInv_comp`), then apply `hcomp`.
    rw [Cat.assoc, ← Cat.assoc (isoInv (prUnit_isIso L p hkm)),
        inv_isoInv_comp, Cat.id_comp, ← Cat.assoc, hcomp,
        Cat.assoc, isoInv_comp, Cat.comp_id]
    -- absorb the level `aw.1 → m` transition by `homInclL_compat`.
    exact homInclL_compat L hL z w (a := aw)
      (b := ⟨m, D.trans aw.2.1 hawm, D.trans aw.2.2 hawm⟩) hawm wa
  refine ⟨homInclL L hL z p ⟨m, hlm, hkm⟩ (r ≫ isoInv (prUnit_isIso L p hkm)), ?_, ?_⟩
  · exact leg i x hik (data.hp k).fst af fa hafm hr_fst
  · exact leg j y hjk (data.hp k).snd ag ga hagm hr_snd

/-- The single-germ representative `Ψ` produced by `prCompProj`, as a TWO `pushHom`s (the projection
    germ folded back by `pushHom_proj`): `pushHom m (aw→v) ≫ pushHom (reflApp p ≫ proj) (k→v)`.
    This form makes the level-push coherence `prPsi_push` a pair of `push_trans` applications. -/
@[expose] public noncomputable def prPsi {i' k : ι} {l : ι} (z : L.A l) (p : L.A k) (w : L.A i')
    (hi'k : D.le i' k) (proj : p ⟶ L.F hi'k w)
    (aw : UpperBound D l k) (m : L.F aw.2.1 z ⟶ L.F aw.2.2 p)
    (v : ι) (hawv : D.le aw.1 v) (hkv : D.le k v) :
    L.F (D.trans aw.2.1 hawv) z ⟶ L.F (D.trans hi'k hkv) w :=
  pushHom L z p aw.2.1 aw.2.2 hawv m
    ≫ pushHom L p w (D.refl k) hi'k hkv (reflApp L p ≫ proj)

public theorem prCompProj {i' k : ι} {l : ι} (z : L.A l) (p : L.A k) (w : L.A i')
    (hi'k : D.le i' k) (proj : p ⟶ L.F hi'k w)
    (a₁ : UpperBound D l k) (m₁ : L.F a₁.2.1 z ⟶ L.F a₁.2.2 p)
    (e : ι) (ha₁e : D.le a₁.1 e) (hke : D.le k e) :
    @compL _ _ L hL ⟨l, z⟩ ⟨k, p⟩ ⟨i', w⟩ (Quotient.mk _ ⟨a₁, m₁⟩)
        (homInclL L hL p w ⟨k, D.refl k, hi'k⟩ (reflApp L p ≫ proj))
      = homInclL L hL z w ⟨e, D.trans a₁.2.1 ha₁e, D.trans hi'k hke⟩
          (prPsi L z p w hi'k proj a₁ m₁ e ha₁e hke) := by
  show homCompRawL L hL z p w a₁ m₁ ⟨k, D.refl k, hi'k⟩ (reflApp L p ≫ proj) = _
  rw [homCompRawL_eq_compAtL L hL z p w a₁ m₁ ⟨k, D.refl k, hi'k⟩ (reflApp L p ≫ proj) e ha₁e hke]
  rfl

/-- **Level-push coherence of `prPsi`.**  Pushing the single-germ rep from `v` to `n` (along `hvn`)
    recomputes the rep at `n`: both `pushHom`s merge by `push_trans` (associativity). -/
public theorem prPsi_push (hL : Coherent L) {i' k : ι} {l : ι} (z : L.A l) (p : L.A k) (w : L.A i')
    (hi'k : D.le i' k) (proj : p ⟶ L.F hi'k w)
    (aw : UpperBound D l k) (m : L.F aw.2.1 z ⟶ L.F aw.2.2 p)
    (v n : ι) (hawv : D.le aw.1 v) (hkv : D.le k v) (hvn : D.le v n) :
    pushHom L z w (D.trans aw.2.1 hawv) (D.trans hi'k hkv) hvn
        (prPsi L z p w hi'k proj aw m v hawv hkv)
      = prPsi L z p w hi'k proj aw m n (D.trans hawv hvn) (D.trans hkv hvn) := by
  unfold prPsi
  rw [pushHom_comp L z p w (D.trans aw.2.1 hawv) (D.trans aw.2.2 hawv) (D.trans hi'k hkv) hvn
        (pushHom L z p aw.2.1 aw.2.2 hawv m)
        (pushHom L p w (D.refl k) hi'k hkv (reflApp L p ≫ proj)),
      ← hL.push_trans z p aw.2.1 aw.2.2 hawv hvn m,
      ← hL.push_trans p w (D.refl k) hi'k hkv hvn (reflApp L p ≫ proj)]

/-- **Joint monomorphy of the two projections** (lax mirror of `colimHom_monicPair_of_rep`).  Two
    germs `⟨l,z⟩ ⟶ ⟨k,p⟩` that agree after `prFst` and after `prSnd` are equal.  Reduce both
    projection-composites to single germs (`prCompProj`), extract a common bound from the germ
    equalities, strip the trailing `isoInv (transApp)` isos, and apply `data.pres` (the fibre's
    joint-monic preservation) to the `prUnit`-conjugated representatives. -/
public theorem prJointMono {i j : ι} (x : L.A i) (y : L.A j) {l : ι} (z : L.A l)
    (h₁ h₂ : homL L hL ⟨l, z⟩ (prObj L data x y))
    (hf : compL L hL h₁ (prFst L hL data x y) = compL L hL h₂ (prFst L hL data x y))
    (hs : compL L hL h₁ (prSnd L hL data x y) = compL L hL h₂ (prSnd L hL data x y)) :
    h₁ = h₂ := by
  have hik : D.le i (prK D i j) := (prK_le D i j).1
  have hjk : D.le j (prK D i j) := (prK_le D i j).2
  revert hf hs
  refine Quotient.inductionOn₂ h₁ h₂ (fun rh₁ rh₂ hf hs => ?_)
  obtain ⟨a₁, m₁⟩ := rh₁
  obtain ⟨a₂, m₂⟩ := rh₂
  simp only [prFst, prSnd, prObj] at hf hs ⊢
  -- common bound `e ≥ a₁.1, a₂.1, k`.
  obtain ⟨w0, hw0a, hw0b⟩ := D.bound a₁.1 a₂.1
  obtain ⟨e, hew, hek⟩ := D.bound w0 (prK D i j)
  have ha₁e : D.le a₁.1 e := D.trans hw0a hew
  have ha₂e : D.le a₂.1 e := D.trans hw0b hew
  rw [prCompProj L hL z _ x hik (data.hp (prK D i j)).fst a₁ m₁ e ha₁e hek,
      prCompProj L hL z _ x hik (data.hp (prK D i j)).fst a₂ m₂ e ha₂e hek] at hf
  rw [prCompProj L hL z _ y hjk (data.hp (prK D i j)).snd a₁ m₁ e ha₁e hek,
      prCompProj L hL z _ y hjk (data.hp (prK D i j)).snd a₂ m₂ e ha₂e hek] at hs
  -- extract germ relations from `hf`/`hs`, then a common bound `n`.
  obtain ⟨cf, hcf1, hcf2, eqf⟩ := Quotient.exact hf
  obtain ⟨cs, hcs1, hcs2, eqs⟩ := Quotient.exact hs
  obtain ⟨n, hcfn, hcsn⟩ := D.bound cf.1 cs.1
  -- `eqf`/`eqs` are `pushHom`-of-`prPsi` equalities at `cf.1`/`cs.1`; fold by `prPsi_push` to `prPsi`
  -- at that level, then push on to the common bound `n`.
  simp only [homSystemL] at eqf eqs
  rw [prPsi_push L hL z _ x hik (data.hp (prK D i j)).fst a₁ m₁ e cf.1 ha₁e hek hcf1,
      prPsi_push L hL z _ x hik (data.hp (prK D i j)).fst a₂ m₂ e cf.1 ha₂e hek hcf2] at eqf
  rw [prPsi_push L hL z _ y hjk (data.hp (prK D i j)).snd a₁ m₁ e cs.1 ha₁e hek hcs1,
      prPsi_push L hL z _ y hjk (data.hp (prK D i j)).snd a₂ m₂ e cs.1 ha₂e hek hcs2] at eqs
  have eqf' := congrArg (pushHom L z x (D.trans a₁.2.1 (D.trans ha₁e hcf1))
      (D.trans hik (D.trans hek hcf1)) hcfn) eqf
  have eqs' := congrArg (pushHom L z y (D.trans a₁.2.1 (D.trans ha₁e hcs1))
      (D.trans hjk (D.trans hek hcs1)) hcsn) eqs
  rw [prPsi_push L hL z _ x hik (data.hp (prK D i j)).fst a₁ m₁ cf.1 n _ _ hcfn,
      prPsi_push L hL z _ x hik (data.hp (prK D i j)).fst a₂ m₂ cf.1 n _ _ hcfn] at eqf'
  rw [prPsi_push L hL z _ y hjk (data.hp (prK D i j)).snd a₁ m₁ cs.1 n _ _ hcsn,
      prPsi_push L hL z _ y hjk (data.hp (prK D i j)).snd a₂ m₂ cs.1 n _ _ hcsn] at eqs'
  -- unfold `prPsi` and fold the projection germ to `prUnit ≫ map proj ≫ isoInv (transApp)`.
  unfold prPsi at eqf' eqs'
  rw [pushHom_proj L x _ hik _ (data.hp (prK D i j)).fst] at eqf'
  rw [pushHom_proj L y _ hjk _ (data.hp (prK D i j)).snd] at eqs'
  -- level data at `n`.
  have hkn : D.le (prK D i j) n := D.trans hek (D.trans hcf1 hcfn)
  have ha₁n : D.le a₁.1 n := D.trans ha₁e (D.trans hcf1 hcfn)
  have ha₂n : D.le a₂.1 n := D.trans ha₂e (D.trans hcf1 hcfn)
  -- the `prUnit`-conjugated reps `u₁,u₂ : F(l≤n)z ⟶ F(k≤n)p`.
  let u₁ : L.F (D.trans a₁.2.1 ha₁n) z ⟶ L.F hkn ((data.hp (prK D i j)).prod (L.F hik x) (L.F hjk y)) :=
    pushHom L z _ a₁.2.1 a₁.2.2 ha₁n m₁ ≫ prUnit L _ hkn
  let u₂ : L.F (D.trans a₂.2.1 ha₂n) z ⟶ L.F hkn ((data.hp (prK D i j)).prod (L.F hik x) (L.F hjk y)) :=
    pushHom L z _ a₂.2.1 a₂.2.2 ha₂n m₂ ≫ prUnit L _ hkn
  -- cancel the trailing `isoInv (transApp)` (post-compose with `transApp`).
  have hfst : u₁ ≫ (L.functF hkn).map (data.hp (prK D i j)).fst
      = u₂ ≫ (L.functF hkn).map (data.hp (prK D i j)).fst := by
    have := congrArg (· ≫ transApp L hik hkn x) eqf'
    simp only [Cat.assoc, inv_isoInv_comp, Cat.comp_id] at this
    simpa only [u₁, u₂, Cat.assoc] using this
  have hsnd : u₁ ≫ (L.functF hkn).map (data.hp (prK D i j)).snd
      = u₂ ≫ (L.functF hkn).map (data.hp (prK D i j)).snd := by
    have := congrArg (· ≫ transApp L hjk hkn y) eqs'
    simp only [Cat.assoc, inv_isoInv_comp, Cat.comp_id] at this
    simpa only [u₁, u₂, Cat.assoc] using this
  -- joint-monic preservation gives `u₁ = u₂`; cancel `prUnit` to get the germ witness.
  have huv : u₁ = u₂ :=
    data.pres hkn (L.F hik x) (L.F hjk y) (L.F (D.trans a₁.2.1 ha₁n) z) u₁ u₂ hfst hsnd
  have hmm : pushHom L z _ a₁.2.1 a₁.2.2 ha₁n m₁ = pushHom L z _ a₂.2.1 a₂.2.2 ha₂n m₂ := by
    have h2 := congrArg (· ≫ isoInv (prUnit_isIso L _ hkn)) huv
    simpa only [u₁, u₂, Cat.assoc, isoInv_comp, Cat.comp_id] using h2
  exact Quotient.sound ⟨⟨n, D.trans a₁.2.1 ha₁n, hkn⟩, ha₁n, ha₂n, hmm⟩

/-- **§M3b (lax): the lax colimit category has binary products.**  The product of `⟨i,x⟩`, `⟨j,y⟩` is
    `prObj = ⟨k, (hp k).prod (F x) (F y)⟩` at a common bound `k`; projections are `prFst`/`prSnd`;
    `pair` is the mediator from `prPairExists`; the laws are its spec plus `prJointMono`. -/
@[expose] public noncomputable def laxColimHasBinaryProducts :
    @HasBinaryProducts (Obj L) (laxColimCat L hL) := by
  letI : Cat (Obj L) := laxColimCat L hL
  refine @HasBinaryProducts.mk (Obj L) (laxColimCat L hL)
    (fun X Y => prObj L data X.2 Y.2)
    (fun {X Y} => prFst L hL data X.2 Y.2)
    (fun {X Y} => prSnd L hL data X.2 Y.2)
    (fun {Z X Y} f g => Classical.choose (prPairExists L hL data X.2 Y.2 Z.2 f g))
    (fun {Z X Y} f g => (Classical.choose_spec (prPairExists L hL data X.2 Y.2 Z.2 f g)).1)
    (fun {Z X Y} f g => (Classical.choose_spec (prPairExists L hL data X.2 Y.2 Z.2 f g)).2)
    (fun {Z X Y} f g h hfst hsnd => ?_)
  -- `h` and `pair f g` agree after both projections ⇒ equal by `prJointMono`.
  refine prJointMono L hL data X.2 Y.2 Z.2 h _ ?_ ?_
  · exact hfst.trans (Classical.choose_spec (prPairExists L hL data X.2 Y.2 Z.2 f g)).1.symm
  · exact hsnd.trans (Classical.choose_spec (prPairExists L hL data X.2 Y.2 Z.2 f g)).2.symm

end LaxProduct

/-! ## §M3c (lax) — equalizers of the lax colimit category

  Mirrors `Colim.colimitHasEqualizers`.  For parallel germs `F,G : ⟨i,x⟩ ⟶ ⟨j,y⟩`, push both to a
  common stage `M`, form the fibre equalizer `⟨M, eqObj fM gM⟩`, and include its `eqMap` as a
  single-stage germ `reflApp ≫ eqMap fM gM` (same shape as `prFst`, so the generic `prUnit`/
  `prCompProj`/`prPsi`/`prPsi_push` helpers above apply verbatim).  Monicity uses `eqData.pres`;
  the lift uses `eqData.presLift`.  As with products the bare-σ carrier removes all `colimOut`. -/
section LaxEqualizer

variable (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L) (eqData : LaxEqualizerData L)

/-- **The equalizer germ-map is monic** (single-map mirror of `prJointMono`).  Two germs
    `⟨lW,w⟩ ⟶ ⟨M,Eobj⟩` equal after `m = reflApp ≫ eqMap fM gM` are equal — `prCompProj`/`prPsi_push`
    reduce both to single germs, and `eqData.pres` (the fibre's `eqMap` joint-monic preservation)
    cancels the `prUnit`-conjugated reps. -/
public theorem eqMono (eqData : LaxEqualizerData L) {i j M : ι} (x : L.A i) (y : L.A j)
    {lW : ι} (w : L.A lW) (hiM : D.le i M) (hjM : D.le j M)
    (fM gM : L.F hiM x ⟶ L.F hjM y)
    (h₁ h₂ : homL L hL ⟨lW, w⟩ ⟨M, @eqObj _ _ (eqData.he M) _ _ fM gM⟩)
    (heq : @compL _ _ L hL ⟨lW, w⟩ ⟨M, @eqObj _ _ (eqData.he M) _ _ fM gM⟩ ⟨i, x⟩ h₁
          (homInclL L hL (@eqObj _ _ (eqData.he M) _ _ fM gM) x ⟨M, D.refl M, hiM⟩
            (reflApp L _ ≫ @eqMap _ _ (eqData.he M) _ _ fM gM))
        = @compL _ _ L hL ⟨lW, w⟩ ⟨M, @eqObj _ _ (eqData.he M) _ _ fM gM⟩ ⟨i, x⟩ h₂
          (homInclL L hL (@eqObj _ _ (eqData.he M) _ _ fM gM) x ⟨M, D.refl M, hiM⟩
            (reflApp L _ ≫ @eqMap _ _ (eqData.he M) _ _ fM gM))) :
    h₁ = h₂ := by
  letI : HasEqualizers (L.A M) := eqData.he M
  revert heq
  refine Quotient.inductionOn₂ h₁ h₂ (fun rh₁ rh₂ heq => ?_)
  obtain ⟨a₁, m₁⟩ := rh₁
  obtain ⟨a₂, m₂⟩ := rh₂
  -- common bound `e ≥ a₁.1, a₂.1, M`.
  obtain ⟨w0, hw0a, hw0b⟩ := D.bound a₁.1 a₂.1
  obtain ⟨e, hew, heM⟩ := D.bound w0 M
  have ha₁e : D.le a₁.1 e := D.trans hw0a hew
  have ha₂e : D.le a₂.1 e := D.trans hw0b hew
  rw [prCompProj L hL w (eqObj fM gM) x hiM (eqMap fM gM) a₁ m₁ e ha₁e heM,
      prCompProj L hL w (eqObj fM gM) x hiM (eqMap fM gM) a₂ m₂ e ha₂e heM] at heq
  obtain ⟨c, hc1, hc2, ceq⟩ := Quotient.exact heq
  simp only [homSystemL] at ceq
  rw [prPsi_push L hL w _ x hiM (eqMap fM gM) a₁ m₁ e c.1 ha₁e heM hc1,
      prPsi_push L hL w _ x hiM (eqMap fM gM) a₂ m₂ e c.1 ha₂e heM hc2] at ceq
  -- `ceq : prPsi (eqMap) m₁ c.1 = prPsi (eqMap) m₂ c.1`.
  unfold prPsi at ceq
  rw [pushHom_proj L x _ hiM _ (eqMap fM gM)] at ceq
  -- cancel the trailing `isoInv (transApp)`, then `eqData.pres`, then cancel `prUnit`.
  let N := c.1
  have heN : D.le M N := D.trans heM hc1
  have ha₁N : D.le a₁.1 N := D.trans ha₁e hc1
  have ha₂N : D.le a₂.1 N := D.trans ha₂e hc1
  let u₁ : L.F (D.trans a₁.2.1 ha₁N) w ⟶ L.F heN (eqObj fM gM) :=
    pushHom L w _ a₁.2.1 a₁.2.2 ha₁N m₁ ≫ prUnit L _ heN
  let u₂ : L.F (D.trans a₂.2.1 ha₂N) w ⟶ L.F heN (eqObj fM gM) :=
    pushHom L w _ a₂.2.1 a₂.2.2 ha₂N m₂ ≫ prUnit L _ heN
  have hmap : u₁ ≫ (L.functF heN).map (eqMap fM gM) = u₂ ≫ (L.functF heN).map (eqMap fM gM) := by
    have := congrArg (· ≫ transApp L hiM heN x) ceq
    simp only [Cat.assoc, inv_isoInv_comp, Cat.comp_id] at this
    simpa only [u₁, u₂, Cat.assoc] using this
  have huv : u₁ = u₂ := eqData.pres heN fM gM (L.F (D.trans a₁.2.1 ha₁N) w) u₁ u₂ hmap
  have hmm : pushHom L w _ a₁.2.1 a₁.2.2 ha₁N m₁ = pushHom L w _ a₂.2.1 a₂.2.2 ha₂N m₂ := by
    have h2 := congrArg (· ≫ isoInv (prUnit_isIso L _ heN)) huv
    simpa only [u₁, u₂, Cat.assoc, isoInv_comp, Cat.comp_id] using h2
  exact Quotient.sound ⟨⟨N, D.trans a₁.2.1 ha₁N, heN⟩, ha₁N, ha₂N, hmm⟩

/-- **§M3c (lax): the lax colimit category has equalizers.**  For each parallel pair `F,G` an
    existence `Prop` (`hEdata`) packages the equalizer object/map and its universal property so
    `Quotient.inductionOn` can eliminate `F`, `G`, and cone legs alike; the `HasEqualizer` is then
    extracted by choice.  `eqData.pres` (mono) gives uniqueness, `eqData.presLift` the factorisation. -/
@[expose] public noncomputable def laxColimHasEqualizers :
    @HasEqualizers (Obj L) (laxColimCat L hL) := by
  letI : Cat (Obj L) := laxColimCat L hL
  have hEdata : ∀ (X Y : Obj L) (F G : X ⟶ Y),
      ∃ (E : Obj L) (m : E ⟶ X), m ≫ F = m ≫ G ∧
        ∀ (W : Obj L) (c : W ⟶ X), c ≫ F = c ≫ G →
          ∃ l : W ⟶ E, l ≫ m = c ∧ ∀ l' : W ⟶ E, l' ≫ m = c → l' = l := by
    intro X Y F G
    obtain ⟨i, x⟩ := X
    obtain ⟨j, y⟩ := Y
    refine Quotient.inductionOn F (fun Fr => ?_)
    refine Quotient.inductionOn G (fun Gr => ?_)
    obtain ⟨aF, fF⟩ := Fr
    obtain ⟨aG, gG⟩ := Gr
    -- common stage `M` for the two parallel germs.
    obtain ⟨M, haFM, haGM⟩ := D.bound aF.1 aG.1
    have hiM : D.le i M := D.trans aF.2.1 haFM
    have hjM : D.le j M := D.trans aF.2.2 haFM
    letI : HasEqualizers (L.A M) := eqData.he M
    let fM : L.F hiM x ⟶ L.F hjM y := pushHom L x y aF.2.1 aF.2.2 haFM fF
    let gM : L.F hiM x ⟶ L.F hjM y := pushHom L x y aG.2.1 aG.2.2 haGM gG
    let Eobj : L.A M := eqObj fM gM
    -- the two parallel germs, re-represented at the common stage `M` (`fM`/`gM`).
    have hFM : (Quotient.mk (setoid (homSystemL L hL x y)) ⟨aF, fF⟩
        : @homL _ _ L hL ⟨i, x⟩ ⟨j, y⟩) = homInclL L hL x y ⟨M, hiM, hjM⟩ fM :=
      (homInclL_compat L hL x y (a := aF) (b := ⟨M, hiM, hjM⟩) haFM fF).symm
    have hGM : (Quotient.mk (setoid (homSystemL L hL x y)) ⟨aG, gG⟩
        : @homL _ _ L hL ⟨i, x⟩ ⟨j, y⟩) = homInclL L hL x y ⟨M, hiM, hjM⟩ gM :=
      (homInclL_compat L hL x y (a := aG) (b := ⟨M, hiM, hjM⟩) haGM gG).symm
    -- generic: composing the eqMap germ (at `⟨M,refl M,hiM⟩`) with a stage-`M` right germ `r`
    -- reduces to `reflApp ≫ eqMap fM gM ≫ r` at `⟨M, refl M, hjM⟩` (both pushes are `refl M`).
    have compRight : ∀ (r : L.F hiM x ⟶ L.F hjM y),
        @compL _ _ L hL ⟨M, Eobj⟩ ⟨i, x⟩ ⟨j, y⟩
            (homInclL L hL Eobj x ⟨M, D.refl M, hiM⟩ (reflApp L Eobj ≫ eqMap fM gM))
            (homInclL L hL x y ⟨M, hiM, hjM⟩ r)
          = homInclL L hL Eobj y ⟨M, D.refl M, hjM⟩ (reflApp L Eobj ≫ eqMap fM gM ≫ r) := by
      intro r
      show homCompRawL L hL Eobj x y ⟨M, D.refl M, hiM⟩ (reflApp L Eobj ≫ eqMap fM gM)
          ⟨M, hiM, hjM⟩ r = _
      rw [homCompRawL_eq_compAtL L hL Eobj x y ⟨M, D.refl M, hiM⟩ (reflApp L Eobj ≫ eqMap fM gM)
            ⟨M, hiM, hjM⟩ r M (D.refl M) (D.refl M)]
      unfold compAtL
      rw [hL.push_refl Eobj x (D.refl M) hiM (reflApp L Eobj ≫ eqMap fM gM),
          hL.push_refl x y hiM hjM r, Cat.assoc]
    refine ⟨⟨M, Eobj⟩, homInclL L hL Eobj x ⟨M, D.refl M, hiM⟩ (reflApp L Eobj ≫ eqMap fM gM),
      ?_, ?_⟩
    · -- equalizing: both sides reduce (via `compRight`) to `reflApp ≫ eqMap ≫ fM|gM`, equal by `eqMap_eq`.
      rw [hFM, hGM]
      show @compL _ _ L hL ⟨M, Eobj⟩ ⟨i, x⟩ ⟨j, y⟩ _ (homInclL L hL x y ⟨M, hiM, hjM⟩ fM)
        = @compL _ _ L hL ⟨M, Eobj⟩ ⟨i, x⟩ ⟨j, y⟩ _ (homInclL L hL x y ⟨M, hiM, hjM⟩ gM)
      rw [compRight fM, compRight gM, eqMap_eq fM gM]
    · -- universal property.
      rintro ⟨lW, w⟩ c hcond
      refine Quotient.inductionOn c (fun rc => ?_) hcond
      clear hcond c
      intro hcond
      obtain ⟨ac, cc⟩ := rc
      -- `compStage`: `compL (mk ⟨ac,cc⟩) (homInclL ⟨M,hiM,hjM⟩ r) = homInclL ⟨P⟩ (pushHom cc ≫ pushHom r)`.
      have compStage : ∀ (r : L.F hiM x ⟶ L.F hjM y) (P : ι) (haP : D.le ac.1 P) (hMP : D.le M P),
          @compL _ _ L hL ⟨lW, w⟩ ⟨i, x⟩ ⟨j, y⟩ (Quotient.mk _ ⟨ac, cc⟩)
              (homInclL L hL x y ⟨M, hiM, hjM⟩ r)
            = homInclL L hL w y ⟨P, D.trans ac.2.1 haP, D.trans hjM hMP⟩
                (pushHom L w x ac.2.1 ac.2.2 haP cc ≫ pushHom L x y hiM hjM hMP r) := by
        intro r P haP hMP
        show homCompRawL L hL w x y ac cc ⟨M, hiM, hjM⟩ r = _
        rw [homCompRawL_eq_compAtL L hL w x y ac cc ⟨M, hiM, hjM⟩ r P haP hMP]
        rfl
      -- reduce `hcond` to germ equality at a first common bound `N0`, then extract a working stage
      -- `N` (≥ N0) where the merged reps `pushHom cc ≫ pushHom (f|g)M` agree ON THE NOSE.
      obtain ⟨N0, haN0, hMN0⟩ := D.bound ac.1 M
      rw [hFM, hGM] at hcond
      change @compL _ _ L hL ⟨lW, w⟩ ⟨i, x⟩ ⟨j, y⟩ _ _
        = @compL _ _ L hL ⟨lW, w⟩ ⟨i, x⟩ ⟨j, y⟩ _ _ at hcond
      rw [compStage fM N0 haN0 hMN0, compStage gM N0 haN0 hMN0] at hcond
      obtain ⟨q, hqN, _, qeq⟩ := Quotient.exact hcond
      -- working stage `N := q.1 ≥ N0`; push the merged reps from `N0` to `N` (`pushHom_comp` +
      -- `push_trans` merge), giving the on-the-nose `pushHom cc ≫ pushHom (f|g)M` equality at `N`.
      let N : ι := q.1
      have hN0N : D.le N0 N := hqN
      have hacN : D.le ac.1 N := D.trans haN0 hN0N
      have hMN : D.le M N := D.trans hMN0 hN0N
      have hlWN : D.le lW N := D.trans ac.2.1 hacN
      have hjN : D.le j N := D.trans hjM hMN
      -- `qeq` is `pushHom (pushHom cc ≫ pushHom (f)M) (N0→N) = pushHom (… (g)M) (N0→N)`; split and merge.
      simp only [homSystemL] at qeq
      rw [pushHom_comp L w x y (D.trans ac.2.1 haN0) (D.trans hiM hMN0) (D.trans hjM hMN0) hN0N
            (pushHom L w x ac.2.1 ac.2.2 haN0 cc) (pushHom L x y hiM hjM hMN0 fM),
          pushHom_comp L w x y (D.trans ac.2.1 haN0) (D.trans hiM hMN0) (D.trans hjM hMN0) hN0N
            (pushHom L w x ac.2.1 ac.2.2 haN0 cc) (pushHom L x y hiM hjM hMN0 gM),
          ← hL.push_trans w x ac.2.1 ac.2.2 haN0 hN0N cc,
          ← hL.push_trans x y hiM hjM hMN0 hN0N fM,
          ← hL.push_trans x y hiM hjM hMN0 hN0N gM] at qeq
      -- `qeq : pushHom cc (ac→N) ≫ pushHom fM (M→N) = pushHom cc (ac→N) ≫ pushHom gM (M→N)`.
      -- convert each `pushHom (f|g)M ≫ transApp hjM hMN y = transApp hiM hMN x ≫ map (f|g)M`.
      let cN : L.F hlWN w ⟶ L.F hMN (L.F hiM x) :=
        pushHom L w x ac.2.1 ac.2.2 hacN cc ≫ transApp L hiM hMN x
      have pushHom_transApp : ∀ (r : L.F hiM x ⟶ L.F hjM y),
          pushHom L x y hiM hjM hMN r ≫ transApp L hjM hMN y
            = transApp L hiM hMN x ≫ (L.functF hMN).map r := by
        intro r
        unfold pushHom
        rw [Cat.assoc, Cat.assoc, inv_isoInv_comp, Cat.comp_id]
      have hcN : cN ≫ (L.functF hMN).map fM = cN ≫ (L.functF hMN).map gM := by
        have h := congrArg (· ≫ transApp L hjM hMN y) qeq
        simp only [Cat.assoc, pushHom_transApp] at h
        simpa only [cN, Cat.assoc] using h
      -- equalizer lift at stage `M`, pushed: `r : F(lW≤N)w ⟶ F hMN Eobj` with `r ≫ map eqMap = cN`.
      obtain ⟨r, hr⟩ := eqData.presLift hMN fM gM (L.F hlWN w) cN hcN
      -- the lift germ and its `lift ≫ m = c` fact (`prUnit`-cancellation, as the product `leg`).
      have hLiftEq : @compL _ _ L hL ⟨lW, w⟩ ⟨M, Eobj⟩ ⟨i, x⟩
            (homInclL L hL w Eobj ⟨N, hlWN, hMN⟩ (r ≫ isoInv (prUnit_isIso L Eobj hMN)))
            (homInclL L hL Eobj x ⟨M, D.refl M, hiM⟩ (reflApp L Eobj ≫ eqMap fM gM))
          = Quotient.mk _ ⟨ac, cc⟩ := by
        show homCompRawL L hL w Eobj x ⟨N, hlWN, hMN⟩ (r ≫ isoInv (prUnit_isIso L Eobj hMN))
            ⟨M, D.refl M, hiM⟩ (reflApp L Eobj ≫ eqMap fM gM) = homInclL L hL w x ac cc
        rw [homCompRawL_eq_compAtL L hL w Eobj x ⟨N, hlWN, hMN⟩ (r ≫ isoInv (prUnit_isIso L Eobj hMN))
              ⟨M, D.refl M, hiM⟩ (reflApp L Eobj ≫ eqMap fM gM) N (D.refl N) hMN]
        unfold compAtL
        rw [hL.push_refl w Eobj hlWN hMN (r ≫ isoInv (prUnit_isIso L Eobj hMN)),
            pushHom_proj L x Eobj hiM hMN (eqMap fM gM),
            Cat.assoc, ← Cat.assoc (isoInv (prUnit_isIso L Eobj hMN)),
            inv_isoInv_comp, Cat.id_comp, ← Cat.assoc, hr,
            Cat.assoc, isoInv_comp, Cat.comp_id]
        exact homInclL_compat L hL w x (a := ac)
          (b := ⟨N, D.trans ac.2.1 hacN, D.trans ac.2.2 hacN⟩) hacN cc
      refine ⟨homInclL L hL w Eobj ⟨N, hlWN, hMN⟩ (r ≫ isoInv (prUnit_isIso L Eobj hMN)),
        hLiftEq, fun l' hl' => ?_⟩
      -- uniqueness: `l'` and the lift agree after `m`; `m` is monic (`eqMono`).
      exact eqMono L hL eqData x y w hiM hjM fM gM l' _ (hl'.trans hLiftEq.symm)
  refine @HasEqualizers.mk (Obj L) (laxColimCat L hL) (fun X Y F G => ?_)
  let E := Classical.choose (hEdata X Y F G)
  let m := Classical.choose (Classical.choose_spec (hEdata X Y F G))
  have hspec := Classical.choose_spec (Classical.choose_spec (hEdata X Y F G))
  exact
    { cone := ⟨E, m, hspec.1⟩
      lift := fun c => Classical.choose (hspec.2 c.dom c.map c.eq)
      fac := fun c => (Classical.choose_spec (hspec.2 c.dom c.map c.eq)).1
      uniq := fun c m' hm' => (Classical.choose_spec (hspec.2 c.dom c.map c.eq)).2 m' hm' }

end LaxEqualizer

/-! ## §M3d (lax) — pullbacks, PullbacksTransferCovers, and the pre-regular assembly

  Mirrors `Colim.colimitHasPullbacks`/`colimitPullbacksTransferCovers`/`colimitPreRegular`.  Pullbacks
  come for free from terminal + products + equalizers via the §1.432 route
  `products_equalizers_implies_pullbacks`.  `PullbacksTransferCovers` compares an arbitrary pullback
  to the canonical one (generic `pullback_comparison_iso`/`cover_precomp_iso`) and reduces to the
  canonical-pullback cover-transfer `hcanon` (the only representative-level hypothesis, TRUE for
  base-change since each fibre is `overPreRegular`).  The final bundle is `PreRegularCategory`. -/
section LaxPreRegular

variable (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L) [hne : Nonempty ι]

/-- **§M3d (lax): the lax colimit category has pullbacks**, via terminal + products + equalizers and
    the §1.432 construction `products_equalizers_implies_pullbacks`.  Mirrors `colimitHasPullbacks`. -/
@[expose] public noncomputable def laxColimHasPullbacks
    -- `_tData` feeds a `HasTerminal` instance the products+equalizers pullback route does not consume,
    -- so the elaborated term drops it (linter flags it); kept for the finite-limit bundle's symmetry.
    (_tData : LaxTerminalData L) (pData : LaxProductData L) (eqData : LaxEqualizerData L) :
    @HasPullbacks (Obj L) (laxColimCat L hL) := by
  letI : Cat (Obj L) := laxColimCat L hL
  letI : HasTerminal (Obj L) := laxColimHasTerminal L hL _tData
  letI : HasBinaryProducts (Obj L) := laxColimHasBinaryProducts L hL pData
  letI : HasEqualizers (Obj L) := laxColimHasEqualizers L hL eqData
  exact ⟨fun f g => products_equalizers_implies_pullbacks f g⟩

/-- Any two pullback cones of the same cospan are connected by a unique compatible iso (generic;
    a local copy of `Colim.pullback_comparison_iso`, which lives in the import-banned strict file). -/
private theorem pullbackComparisonIso {𝒜 : Type w} [Cat.{w} 𝒜] {A B Z : 𝒜}
    {f : A ⟶ Z} {g : B ⟶ Z} {c c' : Cone f g}
    (hc : c.IsPullback) (hc' : c'.IsPullback) :
    ∃ φ : c.pt ⟶ c'.pt, IsIso φ ∧ φ ≫ c'.π₁ = c.π₁ ∧ φ ≫ c'.π₂ = c.π₂ := by
  obtain ⟨φ, ⟨hφ1, hφ2⟩, _⟩ := hc' c
  obtain ⟨ψ, ⟨hψ1, hψ2⟩, _⟩ := hc c'
  obtain ⟨_, _, huniq⟩ := hc c
  have hψφ : ψ ≫ φ = Cat.id c'.pt := by
    obtain ⟨_, _, huniq'⟩ := hc' c'
    rw [huniq' (ψ ≫ φ) (by rw [Cat.assoc, hφ1, hψ1]) (by rw [Cat.assoc, hφ2, hψ2]),
        ← huniq' (Cat.id c'.pt) (by rw [Cat.id_comp]) (by rw [Cat.id_comp])]
  have hφψ : φ ≫ ψ = Cat.id c.pt := by
    rw [huniq (φ ≫ ψ) (by rw [Cat.assoc, hψ1, hφ1]) (by rw [Cat.assoc, hψ2, hφ2]),
        ← huniq (Cat.id c.pt) (by rw [Cat.id_comp]) (by rw [Cat.id_comp])]
  exact ⟨φ, ⟨ψ, hφψ, hψφ⟩, hφ1, hφ2⟩

/-- **§M3d (lax): pullbacks transfer covers**, given the canonical-pullback cover-transfer `hcanon`.
    Mirrors `colimitPullbacksTransferCovers` (generic `pullbackComparisonIso`/`cover_precomp_iso`). -/
public noncomputable def laxColimPullbacksTransferCovers
    (hpull : @HasPullbacks (Obj L) (laxColimCat L hL))
    (hcanon : letI : Cat (Obj L) := laxColimCat L hL
      ∀ {A B Z : Obj L} (f : A ⟶ Z) (g : B ⟶ Z),
        Cover f → Cover (hpull.has f g).cone.π₂) :
    @PullbacksTransferCovers (Obj L) (laxColimCat L hL) := by
  letI : Cat (Obj L) := laxColimCat L hL
  letI : HasPullbacks (Obj L) := hpull
  refine ⟨fun {A B Z f g} c hc hf => ?_⟩
  let pb := hpull.has f g
  have hpbcov : Cover pb.cone.π₂ := hcanon f g hf
  obtain ⟨φ, hφiso, _, hφ2⟩ := pullbackComparisonIso hc pb.cone_isPullback
  rw [← hφ2]
  show Cover (φ ≫ pb.cone.π₂)
  exact cover_precomp_iso hφiso hpbcov

/-- **§M3 assembly (lax): the lax colimit `ratCapCat`-style category is PRE-REGULAR.**  Bundles
    `laxColimHasTerminal`/`…HasBinaryProducts`/`…HasPullbacks`/`…PullbacksTransferCovers` into
    `PreRegularCategory`.  Mirrors `Colim.colimitPreRegular`.  The `hcanon` hypothesis (canonical
    pullback's `π₂` is a cover when `f` is) is the lax analogue of the strict `hcanon`; TRUE for
    base-change (each fibre `Over (listProd U)` is `overPreRegular`), discharged downstream. -/
@[expose] public noncomputable def laxColimPreRegular
    (tData : LaxTerminalData L) (pData : LaxProductData L) (eqData : LaxEqualizerData L)
    (hcanon : letI : Cat (Obj L) := laxColimCat L hL
        letI : HasPullbacks (Obj L) := laxColimHasPullbacks L hL tData pData eqData
      ∀ {A B Z : Obj L} (f : A ⟶ Z) (g : B ⟶ Z),
        Cover f → Cover (HasPullbacks.has f g).cone.π₂) :
    @PreRegularCategory (Obj L) (laxColimCat L hL) := by
  letI : Cat (Obj L) := laxColimCat L hL
  letI hterm : HasTerminal (Obj L) := laxColimHasTerminal L hL tData
  letI hprod : HasBinaryProducts (Obj L) := laxColimHasBinaryProducts L hL pData
  letI hpull : HasPullbacks (Obj L) := laxColimHasPullbacks L hL tData pData eqData
  letI hptc : PullbacksTransferCovers (Obj L) :=
    laxColimPullbacksTransferCovers L hL hpull hcanon
  exact {}

end LaxPreRegular

end Freyd.LaxColim

/-!
════════════════════════════════════════════════════════════════════════════════════════════════
  STATUS (§1.543 — pre-regularity of the filtered lax colimit `ratCapCat P`)  —  GAP 1 COMPLETE
════════════════════════════════════════════════════════════════════════════════════════════════

DONE here (all Sorry-free; every result `#print axioms = propext, Classical.choice, Quot.sound`,
NO `SorryAx`):

  * `laxColimHasTerminal` — `HasTerminal` from a `LaxTerminalData L` (mirrors `colimitHasTerminal`).
  * `reflApp` / `reflApp_isIso` / `reflApp_natural` — the UNIT coherence component (forward of
    `F_refl_iso`), lax companion of `transApp`; conjugator for single-stage germ reps.
  * `homInclL_isIso_of_rep` — a stage iso includes to a colimit iso (lax `colimHom_isIso_of_rep`).
  * `LaxProductData` / `LaxEqualizerData` — the per-fibre-limit + transition-preservation bundles.
  * **`laxColimHasBinaryProducts`** — `HasBinaryProducts` from a `LaxProductData L` (mirrors
    `colimitHasBinaryProducts`).  Product object `⟨k, (hp k).prod (F x)(F y)⟩` at a common bound `k`;
    projections single-stage germs `reflApp ≫ (hp k).fst|snd`; `pair` from `presPair`; `pair_uniq`
    via `prJointMono`.  Key infra: `prUnit` (the unit conjugator iso, baked-in & cancelled since no
    pseudofunctor triangle lives in `Coherent`), `pushHom_proj`, `prCompProj`, `prPsi`, `prPsi_push`
    (level-push coherence = two `push_trans`).
  * **`laxColimHasEqualizers`** — `HasEqualizers` from a `LaxEqualizerData L` (mirrors
    `colimitHasEqualizers`).  `⟨M, eqObj fM gM⟩` at a common stage `M`; `eqMap` a single-stage germ;
    equalizing by `eqMap_eq`; lift by `presLift`; uniqueness by `eqMono` (single-map mirror of
    `prJointMono`).  Reuses the SAME generic `prUnit`/`prCompProj`/`prPsi`/`prPsi_push` helpers.
  * **`laxColimHasPullbacks`** — `HasPullbacks` from terminal+products+equalizers via the §1.432
    `products_equalizers_implies_pullbacks` (mirrors `colimitHasPullbacks`).
  * **`laxColimPullbacksTransferCovers`** — `PullbacksTransferCovers` from the canonical-pullback
    cover-transfer `hcanon` (mirrors `colimitPullbacksTransferCovers`; uses local
    `pullbackComparisonIso` + `cover_precomp_iso`).
  * **`laxColimPreRegular`** — assembles `PreRegularCategory (laxColimCat L hL)` from
    `LaxTerminalData` + `LaxProductData` + `LaxEqualizerData` + `hcanon` (mirrors `colimitPreRegular`).

This FINISHES GAP 1 (`PreRegular A*`) modulo inhabiting the four hypothesis bundles for
`laxOfProjSystem' P` (`LaxTerminalData`/`LaxProductData`/`LaxEqualizerData` — TRUE since each fibre
`Over (listProd U)` is `overPreRegular` and base-change `g*` preserves finite limits — plus the
canonical-pullback cover-transfer `hcanon`).  Remaining downstream: gap 2 (relative-cap via R15) and
the `CofinalCapStep` assembly.
-/
