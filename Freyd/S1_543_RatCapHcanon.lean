/-
  §1.543 — Discharge of `hcanon` for the §1.547 lax base-change slice colimit `ratCapCat P`.

  `RatCapPreReg.lean` proves `PreRegularCategory (ratCapCat P)` GIVEN the canonical-pullback
  cover-transfer `hcanon`: in the lax colimit `laxColimCat (laxOfProjSystem' P)`,
      ∀ {A B Z} (f : A ⟶ Z) (g : B ⟶ Z), Cover f → Cover (HasPullbacks.has f g).cone.π₂.
  This file discharges `hcanon` UNCONDITIONALLY, completing GAP 1.

  The strict analogue is `Colim.colimitCanonicalCover` (`Capitalization.lean`): it assembles the
  M3-cov argument from (i) cospan-alignment to a common stage, (ii) cover REFLECTION through the
  stage inclusion (`homInclObj_cover_reflects`), (iii) per-stage `PullbacksTransferCovers`, (iv) cover
  PRESERVATION (`homInclObj_cover_of_stage`), and (v) the germ-cone-is-a-pullback fact
  (`objIncl_preserves_pullbacks`).  We mirror that here in the LAX germ-algebra of
  `CapitalizationLaxColimit.lean`/`LaxColimitPreReg.lean`.

  Compared with the strict file the bare-Σ object carrier (`objIncl i x = ⟨i,x⟩` definitionally, NO
  `colimOut` quotient) removes ALL object-level representative transport, so the reflection lemmas
  are SHORTER than their strict counterparts.

  For `L := laxOfProjSystem' P` the four ingredient hypotheses are TRUE Sorry-free:
    * cover reflection (`hfaith`/`hcons`/`hmono`): base-change `g*` along the projection is faithful,
      conservative and mono-preserving — `g*` has a left adjoint `Σ_g` (`bcTranspose`), and a functor
      with a left (or right) adjoint that is ALSO full-and-faithful here is even an equivalence onto a
      reflective subcategory; concretely the adjunction transpose `bcTranspose` is a bijection on
      hom-sets, giving faithfulness and conservativity directly.
    * per-stage PTC (`hstagePTC`): each fibre `Over (P.pr i)` is `overPreRegular`.
    * cover preservation (`hcovpres`): base-change of a cover is a cover (`overPreRegular`'s PTC on
      the source fibre, transported across `bcTranspose`).

  Mathlib-free; built on the repo's own `Cat` + `RatCapPreReg` + `CapitalizationLaxColimit` +
  `LaxColimitPreReg` + `SliceRegular`.
-/
module

public import Freyd.S1_543_RatCapPreReg
public import Freyd.S1_543_CatColimitRegular

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

universe u w

variable {ι : Type u} {D : Directed ι}
variable (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L)

/-! ## Composition of stage inclusions

  `compL (homInclL a f) (homInclL b g)` reduces to `homCompRawL a f b g`, which by
  `homCompRawL_eq_compAtL` is `homInclL` of the pushed composite at any common bound.  This is the lax
  `homInclObj_comp` — the workhorse for reflecting factorizations to a stage. -/

/-- `compL` of two stage inclusions is `homCompRawL` of the two representatives (both `homInclL`s are
    `Quotient.mk`, and `compL` is `Quotient.lift₂` of `homCompRawL`). -/
public theorem compL_homInclL {ip iq ir : ι} (xp : L.A ip) (xq : L.A iq) (xr : L.A ir)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : L.F b.2.1 xq ⟶ L.F b.2.2 xr) :
    @compL _ _ L hL ⟨ip, xp⟩ ⟨iq, xq⟩ ⟨ir, xr⟩ (homInclL L hL xp xq a f) (homInclL L hL xq xr b g)
      = homCompRawL L hL xp xq xr a f b g := rfl

/-- `compL` of two stage inclusions equals the inclusion of the pushed composite at any common bound
    `e` (the lax `homInclObj_comp`). -/
public theorem compL_homInclL_compAtL {ip iq ir : ι} (xp : L.A ip) (xq : L.A iq) (xr : L.A ir)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : L.F b.2.1 xq ⟶ L.F b.2.2 xr)
    (e : ι) (hae : D.le a.1 e) (hbe : D.le b.1 e) :
    @compL _ _ L hL ⟨ip, xp⟩ ⟨iq, xq⟩ ⟨ir, xr⟩ (homInclL L hL xp xq a f) (homInclL L hL xq xr b g)
      = homInclL L hL xp xr ⟨e, D.trans a.2.1 hae, D.trans b.2.2 hbe⟩
          (pushHom L xp xq a.2.1 a.2.2 hae f ≫ pushHom L xq xr b.2.1 b.2.2 hbe g) := by
  rw [compL_homInclL L hL, homCompRawL_eq_compAtL L hL xp xq xr a f b g e hae hbe]
  rfl

-- `cover_comp_iso'` (the bare-`Cat` cover-post-composed-with-iso lemma) moved upstream to
-- `Freyd.S1_51` as `cover_comp_iso_cat`, where `Cover` is defined, so the §1.543 lax and cofinal
-- files share one statement of it.

/-- A mono pre-composed with an iso is mono. -/
public theorem mono_precomp_iso' {𝒜 : Type w} [Cat.{w} 𝒜] {X Y Z : 𝒜} {i : X ⟶ Y} {f : Y ⟶ Z}
    (hi : IsIso i) (hf : Monic f) : Monic (i ≫ f) := by
  obtain ⟨ii, hi1, hi2⟩ := hi
  intro W u v huv
  -- u ≫ i ≫ f = v ≫ i ≫ f ⇒ (u ≫ i) ≫ f = (v ≫ i) ≫ f ⇒ u ≫ i = v ≫ i ⇒ u = v.
  have h1 : (u ≫ i) ≫ f = (v ≫ i) ≫ f := by rw [Cat.assoc, Cat.assoc]; exact huv
  have h2 : u ≫ i = v ≫ i := hf _ _ h1
  have := congrArg (fun t => t ≫ ii) h2
  simpa only [Cat.assoc, hi1, Cat.comp_id] using this

/-- A mono post-composed with an iso is mono. -/
public theorem mono_postcomp_iso' {𝒜 : Type w} [Cat.{u} 𝒜] {X Y Z : 𝒜} {f : X ⟶ Y} {j : Y ⟶ Z}
    (hf : Monic f) (hj : IsIso j) : Monic (f ≫ j) := by
  obtain ⟨jj, hj1, hj2⟩ := hj
  intro W u v huv
  apply hf
  -- u ≫ (f ≫ j) = v ≫ (f ≫ j) ⇒ post-compose `jj`: u ≫ f = v ≫ f.
  have := congrArg (fun t => t ≫ jj) huv
  simpa only [Cat.assoc, hj1, Cat.comp_id] using this

/-- **Iso un-conjugation.**  If `i`, `j` are isos and `i ≫ f ≫ j` is an iso, then `f` is an iso
    (`f = i⁻¹ ≫ (i ≫ f ≫ j) ≫ j⁻¹`, a composite of isos).  Used to strip the coherence isos that
    flank `Functor.map` inside `pushHom`. -/
public theorem isIso_unconj {𝒜 : Type w} [Cat.{w} 𝒜] {W X Y Z : 𝒜}
    {i : W ⟶ X} {f : X ⟶ Y} {j : Y ⟶ Z}
    (hi : IsIso i) (hj : IsIso j) (h : IsIso (i ≫ f ≫ j)) : IsIso f := by
  obtain ⟨ii, hi1, hi2⟩ := hi
  obtain ⟨jj, hj1, hj2⟩ := hj
  obtain ⟨w, hw1, hw2⟩ := h
  -- inverse of `f` is `j ≫ w ≫ i`.
  refine ⟨j ≫ w ≫ i, ?_, ?_⟩
  · calc f ≫ j ≫ w ≫ i = (ii ≫ i) ≫ f ≫ j ≫ w ≫ i := by rw [hi2, Cat.id_comp]
      _ = ii ≫ (i ≫ f ≫ j) ≫ w ≫ i := by simp only [Cat.assoc]
      _ = ii ≫ Cat.id W ≫ i := by rw [← Cat.assoc (i ≫ f ≫ j), hw1]
      _ = Cat.id X := by rw [Cat.id_comp, hi2]
  · calc (j ≫ w ≫ i) ≫ f = j ≫ (w ≫ i ≫ f ≫ j) ≫ jj := by
            simp only [Cat.assoc]; rw [hj1, Cat.comp_id]
      _ = j ≫ Cat.id Z ≫ jj := by rw [hw2]
      _ = Cat.id Y := by rw [Cat.id_comp, hj1]

/-! ## Reflection of equalities/monos/covers/isos through the stage inclusion

  These mirror `homIncl_injective` / `colimHom_mono_reflects` / `homInclObj_cover_reflects` /
  `homInclObj_isIso_reflects` of the strict file.  The bare-Σ objects mean `homInclL x y a g` is
  ALREADY a hom `⟨i,x⟩ ⟶ ⟨j,y⟩`; there is no `colimOut`/object-rep transport. -/

/-- `pushHom` is injective when `functF` is faithful: `pushHom = transApp ≫ map · ≫ isoInv transApp`
    is `map ·` flanked by two isos, so equal pushes give equal `map`s, hence (faithfulness) equal
    arrows.  The lax companion of stripping `homTr`'s `castHom`. -/
public theorem pushHom_injective
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        (L.functF hij).map p
          = (L.functF hij).map q → p = q)
    {i j : ι} (x : L.A i) (y : L.A j) {k m : ι}
    (hik : D.le i k) (hjk : D.le j k) (hkm : D.le k m)
    {f g : L.F hik x ⟶ L.F hjk y}
    (h : pushHom L x y hik hjk hkm f = pushHom L x y hik hjk hkm g) : f = g := by
  apply hfaith hkm
  -- strip the flanking isos.  pushHom = transApp ≫ map · ≫ isoInv transApp.
  unfold pushHom at h
  -- left-cancel `transApp` (iso) and right-cancel `isoInv transApp` (iso)
  have hL' := congrArg (fun t => isoInv (transApp_isIso L hik hkm x) ≫ t) h
  simp only at hL'
  rw [← Cat.assoc, ← Cat.assoc, inv_isoInv_comp, Cat.id_comp,
      ← Cat.assoc, ← Cat.assoc, inv_isoInv_comp, Cat.id_comp] at hL'
  have hR' := congrArg (fun t => t ≫ transApp L hjk hkm y) hL'
  simp only at hR'
  rw [Cat.assoc, inv_isoInv_comp, Cat.comp_id, Cat.assoc, inv_isoInv_comp, Cat.comp_id] at hR'
  exact hR'

/-- **`homInclL` is injective on hom-sets when transitions are faithful.**  Two germs at the same
    bound `a` including to the same colimit morphism agree: `Quotient.exact` gives a higher bound
    where the `pushHom`s agree, and `pushHom_injective` strips back.  Lax `homIncl_injective`. -/
public theorem homInclL_injective
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        (L.functF hij).map p
          = (L.functF hij).map q → p = q)
    {i j : ι} (x : L.A i) (y : L.A j) (a : UpperBound D i j)
    {g g' : L.F a.2.1 x ⟶ L.F a.2.2 y}
    (h : homInclL L hL x y a g = homInclL L hL x y a g') : g = g' := by
  obtain ⟨k, hak, hak', heq⟩ := Quotient.exact h
  dsimp only [homSystemL] at heq
  rw [Subsingleton.elim hak' hak] at heq
  exact pushHom_injective L hfaith x y a.2.1 a.2.2 hak heq

/-- **Stage equation from a colimit composite equality.**  If `homInclL a f ⊚ homInclL b g`
    (= `homCompRawL a f b g`) equals `homInclL c hh`, then at a common stage `N` the pushed germs
    compose to the pushed `hh`.  Lax `homCompRaw_eq_stage`. -/
public theorem homCompRawL_eq_stage {ip iq ir : ι} (xp : L.A ip) (xq : L.A iq) (xr : L.A ir)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq)
    (b : UpperBound D iq ir) (g : L.F b.2.1 xq ⟶ L.F b.2.2 xr)
    (c : UpperBound D ip ir) (hh : L.F c.2.1 xp ⟶ L.F c.2.2 xr)
    (h : homCompRawL L hL xp xq xr a f b g = homInclL L hL xp xr c hh) :
    ∃ (N : ι) (haN : D.le a.1 N) (hbN : D.le b.1 N) (hcN : D.le c.1 N),
      pushHom L xp xq a.2.1 a.2.2 haN f ≫ pushHom L xq xr b.2.1 b.2.2 hbN g
        = pushHom L xp xr c.2.1 c.2.2 hcN hh := by
  obtain ⟨M, hfM, hgM⟩ := D.bound a.1 b.1
  rw [homCompRawL_eq_compAtL L hL xp xq xr a f b g M hfM hgM] at h
  unfold compAtL at h
  obtain ⟨N, h1, h2, heq⟩ := Quotient.exact h
  dsimp only [homSystemL] at heq
  rw [pushHom_comp L xp xq xr (D.trans a.2.1 hfM) (D.trans a.2.2 hfM) (D.trans b.2.2 hgM) h1
        (pushHom L xp xq a.2.1 a.2.2 hfM f) (pushHom L xq xr b.2.1 b.2.2 hgM g),
      ← hL.push_trans xp xq a.2.1 a.2.2 hfM h1 f, ← hL.push_trans xq xr b.2.1 b.2.2 hgM h1 g] at heq
  exact ⟨N.1, D.trans hfM h1, D.trans hgM h1, h2, heq⟩

/-- **A colimit composite equal to the identity becomes a stage identity.**  The `homInclL … id`
    special case of `homCompRawL_eq_stage`, finished by `pushHom_id`.  Lax `homCompRaw_eq_id_stage`. -/
public theorem homCompRawL_eq_id_stage {ip iq : ι} (xp : L.A ip) (xq : L.A iq)
    (a : UpperBound D ip iq) (f : L.F a.2.1 xp ⟶ L.F a.2.2 xq)
    (b : UpperBound D iq ip) (g : L.F b.2.1 xq ⟶ L.F b.2.2 xp)
    (h : homCompRawL L hL xp xq xp a f b g
        = homInclL L hL xp xp ⟨ip, D.refl ip, D.refl ip⟩ (Cat.id (L.F (D.refl ip) xp))) :
    ∃ (N : ι) (haN : D.le a.1 N) (hbN : D.le b.1 N),
      pushHom L xp xq a.2.1 a.2.2 haN f ≫ pushHom L xq xp b.2.1 b.2.2 hbN g
        = Cat.id (L.F (D.trans a.2.1 haN) xp) := by
  obtain ⟨N, haN, hbN, hcN, key⟩ := homCompRawL_eq_stage L hL xp xq xp a f b g
    ⟨ip, D.refl ip, D.refl ip⟩ (Cat.id (L.F (D.refl ip) xp)) h
  rw [pushHom_id L xp (D.refl ip) hcN] at key
  exact ⟨N, haN, hbN, key⟩

/-- **Iso reflection through the stage inclusion.**  If `homInclL a g` is iso in the colimit, then
    at some higher stage `L'` the transition `map g` is iso.  Lax `colimHom_isIso_reflects`. -/
public theorem homInclL_isIso_reflects
    {i j : ι} (x : L.A i) (y : L.A j) (a : UpperBound D i j)
    (g : L.F a.2.1 x ⟶ L.F a.2.2 y)
    (hiso : @IsIso (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨j, y⟩ (homInclL L hL x y a g)) :
    ∃ (e : ι) (hae : D.le a.1 e),
      IsIso (pushHom L x y a.2.1 a.2.2 hae g) := by
  letI : Cat (Obj L) := laxColimCat L hL
  obtain ⟨ginv, hl, hr⟩ := hiso
  revert hl hr
  refine Quotient.inductionOn ginv (fun rep => ?_)
  obtain ⟨b, g'⟩ := rep
  intro hl hr
  -- `homInclL a g ⊚ (germ g' at b) = id` etc. are `homCompRawL = idL`
  have hl' : homCompRawL L hL x y x a g b g'
      = homInclL L hL x x ⟨i, D.refl i, D.refl i⟩ (Cat.id (L.F (D.refl i) x)) := hl
  have hr' : homCompRawL L hL y x y b g' a g
      = homInclL L hL y y ⟨j, D.refl j, D.refl j⟩ (Cat.id (L.F (D.refl j) y)) := hr
  obtain ⟨N1, haN1, hbN1, eq1⟩ := homCompRawL_eq_id_stage L hL x y a g b g' hl'
  obtain ⟨N2, hbN2, haN2, eq2⟩ := homCompRawL_eq_id_stage L hL y x b g' a g hr'
  obtain ⟨e, hN1e, hN2e⟩ := D.bound N1 N2
  have hae : D.le a.1 e := D.trans haN1 hN1e
  have hbe : D.le b.1 e := D.trans hbN1 hN1e
  -- push both stage identities to `e` (push_trans on a composite).
  have eq1e : pushHom L x y a.2.1 a.2.2 hae g ≫ pushHom L y x b.2.1 b.2.2 hbe g'
      = Cat.id (L.F (D.trans a.2.1 hae) x) := by
    have t := congrArg (pushHom L x x _ _ hN1e) eq1
    rw [pushHom_comp L x y x (D.trans a.2.1 haN1) (D.trans a.2.2 haN1) (D.trans b.2.2 hbN1) hN1e,
        ← hL.push_trans x y a.2.1 a.2.2 haN1 hN1e g,
        ← hL.push_trans y x b.2.1 b.2.2 hbN1 hN1e g',
        pushHom_id L x (D.trans a.2.1 haN1) hN1e] at t
    exact t
  have eq2e : pushHom L y x b.2.1 b.2.2 hbe g' ≫ pushHom L x y a.2.1 a.2.2 hae g
      = Cat.id (L.F (D.trans b.2.1 hbe) y) := by
    have t := congrArg (pushHom L y y _ _ hN2e) eq2
    rw [pushHom_comp L y x y (D.trans b.2.1 hbN2) (D.trans b.2.2 hbN2) (D.trans a.2.2 haN2) hN2e,
        ← hL.push_trans y x b.2.1 b.2.2 hbN2 hN2e g',
        ← hL.push_trans x y a.2.1 a.2.2 haN2 hN2e g,
        pushHom_id L y (D.trans b.2.1 hbN2) hN2e] at t
    -- `t` and the goal differ only in `D.le` proofs (proof-irrelevant).
    exact t
  exact ⟨e, hae, pushHom L y x b.2.1 b.2.2 hbe g', eq1e, eq2e⟩

/-- **Monic preservation through the stage inclusion.**  If a germ `g` is left-cancellable under
    EVERY transition from `a.1` (`hcancel`), then `homInclL a g` is monic in the colimit.  Reduce a
    colimit cancellation `u ⊚ (homInclL a g) = v ⊚ (homInclL a g)` to a stage equation of pushed
    competitors (`homCompRawL` + `Quotient.exact`), cancel by `hcancel`, repackage as a germ relation.
    Lax `colimHom_mono_of_rep`/`homInclObj_mono_of_stage`. -/
public theorem homInclL_mono_of_stage
    {i j : ι} (x : L.A i) (y : L.A j) (a : UpperBound D i j)
    (g : L.F a.2.1 x ⟶ L.F a.2.2 y)
    (hcancel : ∀ {e : ι} (hae : D.le a.1 e) (z : L.A e)
        (u v : z ⟶ L.F (D.trans a.2.1 hae) x),
        u ≫ pushHom L x y a.2.1 a.2.2 hae g = v ≫ pushHom L x y a.2.1 a.2.2 hae g → u = v) :
    @Monic (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨j, y⟩ (homInclL L hL x y a g) := by
  letI : Cat (Obj L) := laxColimCat L hL
  intro W
  refine Quotient.ind₂ (fun pr qr hpq => ?_)
  obtain ⟨ap, p₀⟩ := pr
  obtain ⟨aq, q₀⟩ := qr
  -- common bound `P` of `ap.1, aq.1, a.1`
  obtain ⟨P0, hP0p, hP0q⟩ := D.bound ap.1 aq.1
  obtain ⟨P, hP0P, haP⟩ := D.bound P0 a.1
  have hapP : D.le ap.1 P := D.trans hP0p hP0P
  have haqP : D.le aq.1 P := D.trans hP0q hP0P
  -- both composites are `homInclL` of the pushed composite at bound `P`.
  change homCompRawL L hL W.2 x y ap p₀ a g = homCompRawL L hL W.2 x y aq q₀ a g at hpq
  rw [homCompRawL_eq_compAtL L hL W.2 x y ap p₀ a g P hapP haP,
      homCompRawL_eq_compAtL L hL W.2 x y aq q₀ a g P haqP haP] at hpq
  unfold compAtL at hpq
  obtain ⟨R, hPR, hPR', heq⟩ := Quotient.exact hpq
  dsimp only [homSystemL] at heq
  rw [Subsingleton.elim hPR' hPR] at heq
  -- split off the common `pushHom g` factor (pushed once more from `P` to `R.1`).
  rw [pushHom_comp L W.2 x y (D.trans ap.2.1 hapP) (D.trans ap.2.2 hapP) (D.trans a.2.2 haP) hPR
        (pushHom L W.2 x ap.2.1 ap.2.2 hapP p₀) (pushHom L x y a.2.1 a.2.2 haP g),
      pushHom_comp L W.2 x y (D.trans aq.2.1 haqP) (D.trans aq.2.2 haqP) (D.trans a.2.2 haP) hPR
        (pushHom L W.2 x aq.2.1 aq.2.2 haqP q₀) (pushHom L x y a.2.1 a.2.2 haP g),
      ← hL.push_trans x y a.2.1 a.2.2 haP hPR g,
      ← hL.push_trans W.2 x ap.2.1 ap.2.2 hapP hPR p₀,
      ← hL.push_trans W.2 x aq.2.1 aq.2.2 haqP hPR q₀] at heq
  -- cancel that common right factor by `hcancel` at `e := R.1`.
  have hu := hcancel (D.trans haP hPR) (L.F (D.trans (D.trans ap.2.1 hapP) hPR) W.2)
    (pushHom L W.2 x ap.2.1 ap.2.2 (D.trans hapP hPR) p₀)
    (pushHom L W.2 x aq.2.1 aq.2.2 (D.trans haqP hPR) q₀)
    heq
  -- repackage `hu` as a germ relation at bound `R.1`.
  refine Quotient.sound ⟨⟨R.1, D.trans (D.trans ap.2.1 hapP) hPR, D.trans (D.trans ap.2.2 hapP) hPR⟩,
    D.trans hapP hPR, D.trans haqP hPR, ?_⟩
  dsimp only [homSystemL]
  -- the goal's `.tr` reduces to the collapsed-bound pushes, matching `hu` directly.
  exact hu

/-- **Monic reflection through the stage inclusion.**  If `homInclL a g` is monic in the colimit and
    transitions are faithful, then the germ `g` is left-cancellable under every transition.  Include
    the two stage competitors `u, v` as colimit germs `⟨e,z⟩ ⟶ ⟨i,x⟩` and compose with `homInclL a g`;
    the colimit mono forces the inclusions equal, and `homInclL_injective`/`pushHom_injective` strip
    back.  Lax `colimHom_mono_reflects`. -/
public theorem homInclL_mono_reflects
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        (L.functF hij).map p
          = (L.functF hij).map q → p = q)
    {i j : ι} (x : L.A i) (y : L.A j) (a : UpperBound D i j)
    (g : L.F a.2.1 x ⟶ L.F a.2.2 y)
    (hmono : @Monic (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨j, y⟩ (homInclL L hL x y a g))
    {e : ι} (hae : D.le a.1 e) (z : L.A e)
    (u v : z ⟶ L.F (D.trans a.2.1 hae) x)
    (huv : u ≫ pushHom L x y a.2.1 a.2.2 hae g = v ≫ pushHom L x y a.2.1 a.2.2 hae g) : u = v := by
  letI : Cat (Obj L) := laxColimCat L hL
  -- include `reflApp z ≫ u`, `reflApp z ≫ v` as germs `⟨e,z⟩ ⟶ ⟨i,x⟩` at bound `⟨e, refl e, i≤e⟩`.
  let bnd : UpperBound D e i := ⟨e, D.refl e, D.trans a.2.1 hae⟩
  let U : @homL _ _ L hL ⟨e, z⟩ ⟨i, x⟩ := homInclL L hL z x bnd (reflApp L z ≫ u)
  let V : @homL _ _ L hL ⟨e, z⟩ ⟨i, x⟩ := homInclL L hL z x bnd (reflApp L z ≫ v)
  have hUV : @compL _ _ L hL ⟨e, z⟩ ⟨i, x⟩ ⟨j, y⟩ U (homInclL L hL x y a g)
      = @compL _ _ L hL ⟨e, z⟩ ⟨i, x⟩ ⟨j, y⟩ V (homInclL L hL x y a g) := by
    rw [compL_homInclL_compAtL L hL z x y bnd _ a g e (D.refl e) hae,
        compL_homInclL_compAtL L hL z x y bnd _ a g e (D.refl e) hae]
    -- the left push at refl is identity (push_refl): both sides `homInclL ((reflApp z ≫ u|v) ≫ pushHom g)`.
    rw [hL.push_refl z x (D.refl e) (D.trans a.2.1 hae) (reflApp L z ≫ u),
        hL.push_refl z x (D.refl e) (D.trans a.2.1 hae) (reflApp L z ≫ v),
        Cat.assoc, Cat.assoc, huv]
  have hUVeq : U = V := hmono U V hUV
  -- strip the inclusion (faithful), then cancel the iso `reflApp z` (mono).
  have hstrip := homInclL_injective L hL hfaith z x bnd hUVeq
  -- `reflApp z ≫ u = reflApp z ≫ v` with `reflApp z` iso ⇒ `u = v`.
  have hiso := reflApp_isIso L z
  obtain ⟨rinv, hr1, hr2⟩ := hiso
  have := congrArg (fun t => rinv ≫ t) hstrip
  simpa only [← Cat.assoc, hr2, Cat.id_comp] using this

/-- **Cover of a germ that is a cover at every stage.**  If `pushHom g` is a cover for every
    transition from `a.1`, then `homInclL a g` is a cover in the colimit.  Given a colimit mono `m`
    and factor `homInclL a g = g' ⊚ m`, reflect the factorization to a stage `N`
    (`homCompRawL_eq_stage`); the stage `pushHom m` is mono (mono reflection) and factors the stage
    cover `pushHom g`, so it is a stage iso; lift to the colimit (`homInclL_isIso_of_rep`) and absorb
    the level shift (`homInclL_compat`).  Lax `colimHom_cover_of_rep`. -/
public theorem homInclL_cover_of_rep
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        (L.functF hij).map p
          = (L.functF hij).map q → p = q)
    {i j : ι} (x : L.A i) (y : L.A j) (a : UpperBound D i j)
    (g : L.F a.2.1 x ⟶ L.F a.2.2 y)
    (hcov : ∀ (e : ι) (hae : D.le a.1 e), Cover (pushHom L x y a.2.1 a.2.2 hae g)) :
    @Cover (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨j, y⟩ (homInclL L hL x y a g) := by
  letI : Cat (Obj L) := laxColimCat L hL
  intro Cobj m g' hm hg'm
  -- `m : Cobj ⟶ ⟨j,y⟩`, `g' : ⟨i,x⟩ ⟶ Cobj`, both germs.
  revert hm hg'm
  refine Quotient.inductionOn₂ m g' (fun mrep grep => ?_)
  obtain ⟨bm, m₀⟩ := mrep
  obtain ⟨bg, g₀⟩ := grep
  obtain ⟨ck, cx⟩ := Cobj
  intro hm hg'm
  -- factorization `g₀ ⊚ m₀ = homInclL a g` ⇒ stage equation at `N`.
  have hg'm' : homCompRawL L hL x cx y bg g₀ bm m₀ = homInclL L hL x y a g := hg'm
  obtain ⟨N, hgN, hmN, hfN, eqN⟩ := homCompRawL_eq_stage L hL x cx y bg g₀ bm m₀ a g hg'm'
  -- `pushHom m₀` is mono at `N` (mono reflection of the colimit mono `m`).
  have hm_mono : Monic (pushHom L cx y bm.2.1 bm.2.2 hmN m₀) := by
    intro Z' u v huv
    exact homInclL_mono_reflects L hL hfaith cx y bm m₀ hm hmN Z' u v huv
  -- `pushHom g` is a cover at `N`; `pushHom m₀` factors it ⇒ `pushHom m₀` iso.
  have hcov_N : Cover (pushHom L x y a.2.1 a.2.2 hfN g) := hcov N hfN
  have hiso_mN : IsIso (pushHom L cx y bm.2.1 bm.2.2 hmN m₀) :=
    hcov_N _ _ hm_mono eqN
  obtain ⟨nN, hn1, hn2⟩ := hiso_mN
  -- lift the stage iso to the colimit; `homInclL_compat` absorbs the level shift `bm → N`.
  have hlift := homInclL_isIso_of_rep L hL cx y ⟨N, D.trans bm.2.1 hmN, D.trans bm.2.2 hmN⟩
    (pushHom L cx y bm.2.1 bm.2.2 hmN m₀) nN hn1 hn2
  rwa [homInclL_compat L hL cx y (a := bm)
    (b := ⟨N, D.trans bm.2.1 hmN, D.trans bm.2.2 hmN⟩) hmN m₀] at hlift

/-- **Cover preservation through the stage inclusion.**  If `g` is a cover stable under every
    transition from `a.1` (each `(functF hij).map g` a cover), then `homInclL a g` is a colimit
    cover.  Feed `homInclL_cover_of_rep` the pushed covers: `pushHom = transApp ≫ map · ≫ isoInv`, and
    pre/post-composing a cover with isos keeps it a cover.  Lax `homInclObj_cover_of_stage`. -/
public theorem homInclL_cover_of_stage
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        (L.functF hij).map p
          = (L.functF hij).map q → p = q)
    {i : ι} (x y : L.A i) (g : x ⟶ y)
    (hcov : ∀ {e : ι} (hie : D.le i e), Cover ((L.functF hie).map g)) :
    @Cover (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨i, y⟩
      (homInclL L hL x y ⟨i, D.refl i, D.refl i⟩ (reflApp L x ≫ g ≫ isoInv (reflApp_isIso L y))) := by
  -- the germ `gᵣ := reflApp x ≫ g ≫ (reflApp y)⁻¹` at the reflexive bound `⟨i, refl i, refl i⟩`.
  apply homInclL_cover_of_rep L hL hfaith x y ⟨i, D.refl i, D.refl i⟩
  intro e hie
  -- `pushHom gᵣ` (along `refl i ≤ e`) is a cover: it is `(functF hie').map g` flanked by isos.
  -- `pushHom x y (refl i)(refl i) hie gᵣ = transApp ≫ map gᵣ ≫ isoInv transApp`; and
  -- `map gᵣ = map (reflApp x) ≫ map g ≫ map (reflApp y)⁻¹`, all but `map g` being isos.
  unfold pushHom
  -- the middle `map gᵣ` factors through `map g` flanked by isos (functor preserves iso & comp).
  rw [(L.functF hie).map_comp (reflApp L x) (g ≫ isoInv (reflApp_isIso L y)),
      (L.functF hie).map_comp g (isoInv (reflApp_isIso L y))]
  -- assemble: cover flanked by four isos (transApp, map reflApp x, map (reflApp y)⁻¹, isoInv transApp).
  have hi1 : IsIso (transApp L (D.refl i) hie x) := transApp_isIso L (D.refl i) hie x
  have hi2 : IsIso ((L.functF hie).map (reflApp L x)) :=
    functor_preserves_iso (F := L.functF hie) (reflApp L x) (reflApp_isIso L x)
  have hi3 : IsIso ((L.functF hie).map (isoInv (reflApp_isIso L y))) :=
    functor_preserves_iso (F := L.functF hie) (isoInv (reflApp_isIso L y))
      ⟨reflApp L y, inv_isoInv_comp _, isoInv_comp _⟩
  have hi4 : IsIso (isoInv (transApp_isIso L (D.refl i) hie y)) :=
    ⟨transApp L (D.refl i) hie y, inv_isoInv_comp _, isoInv_comp _⟩
  -- cover (map g) ⇒ cover of the whole flanked composite (iso pre/post composition).
  have hg_cov : Cover ((L.functF hie).map g) := hcov hie
  -- peel the flanking isos: transApp (pre), isoInv transApp (post), map reflApp x (pre), map isoInv (post).
  have c1 : Cover ((L.functF hie).map g
      ≫ (L.functF hie).map (isoInv (reflApp_isIso L y))) :=
    cover_comp_iso_cat hg_cov hi3
  have c2 : Cover ((L.functF hie).map (reflApp L x)
      ≫ (L.functF hie).map g
      ≫ (L.functF hie).map (isoInv (reflApp_isIso L y))) :=
    cover_precomp_iso hi2 c1
  have c3 : Cover (((L.functF hie).map (reflApp L x)
      ≫ (L.functF hie).map g
      ≫ (L.functF hie).map (isoInv (reflApp_isIso L y)))
      ≫ isoInv (transApp_isIso L (D.refl i) hie y)) :=
    cover_comp_iso_cat c2 hi4
  exact @cover_precomp_iso _ _ _ _ _ _ hi1 _ c3

/-- **Iso reflection (clean form).**  If `homInclL a g` is iso and transitions are conservative,
    then `g` is iso.  `homInclL_isIso_reflects` gives a stage `e` with `pushHom g` iso; `pushHom` is
    `map g` flanked by isos, so `map g` is iso, and `hcons` reflects to `g`.  Lax
    `homInclObj_isIso_reflects`. -/
public theorem homInclL_isIso_reflects'
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (φ : x ⟶ y),
        Monic φ → IsIso ((L.functF hij).map φ) → IsIso φ)
    {i : ι} (x y : L.A i) (g : x ⟶ y) (hgmono : Monic g)
    (hiso : @IsIso (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨i, y⟩
      (homInclL L hL x y ⟨i, D.refl i, D.refl i⟩ (reflApp L x ≫ g ≫ isoInv (reflApp_isIso L y)))) :
    IsIso g := by
  obtain ⟨e, hae, hpiso⟩ := homInclL_isIso_reflects L hL x y ⟨i, D.refl i, D.refl i⟩
    (reflApp L x ≫ g ≫ isoInv (reflApp_isIso L y)) hiso
  apply hcons hae _ hgmono
  -- `pushHom gᵣ = transApp ≫ (map gᵣ) ≫ isoInv transApp`; un-conjugate by the two isos.
  have hi1 : IsIso (transApp L (D.refl i) hae x) := transApp_isIso L (D.refl i) hae x
  have hi1' : IsIso (isoInv (transApp_isIso L (D.refl i) hae y)) :=
    ⟨transApp L (D.refl i) hae y, inv_isoInv_comp _, isoInv_comp _⟩
  have hmapr : IsIso ((L.functF hae).map
      (reflApp L x ≫ g ≫ isoInv (reflApp_isIso L y))) := by
    have := hpiso; unfold pushHom at this
    exact isIso_unconj hi1 hi1' this
  -- `map gᵣ = (map reflApp x) ≫ (map g) ≫ (map isoInv)`; un-conjugate again.
  rw [(L.functF hae).map_comp (reflApp L x) (g ≫ isoInv (reflApp_isIso L y)),
      (L.functF hae).map_comp g (isoInv (reflApp_isIso L y))] at hmapr
  have hi2 : IsIso ((L.functF hae).map (reflApp L x)) :=
    functor_preserves_iso (F := L.functF hae) (reflApp L x) (reflApp_isIso L x)
  have hi3 : IsIso ((L.functF hae).map (isoInv (reflApp_isIso L y))) :=
    functor_preserves_iso (F := L.functF hae) (isoInv (reflApp_isIso L y))
      ⟨reflApp L y, inv_isoInv_comp _, isoInv_comp _⟩
  exact isIso_unconj hi2 hi3 hmapr

/-- The reflexive-bound germ of a stage morphism `g : x ⟶ y` in `L.A i`: the colimit hom
    `⟨i,x⟩ ⟶ ⟨i,y⟩` given by `reflApp x ≫ g ≫ (reflApp y)⁻¹` at the bound `⟨i, refl, refl⟩`.  This is
    the lax stage-inclusion of `g` (the `homInclObj` analogue). -/
@[expose] public noncomputable def stageInclL {i : ι} {x y : L.A i} (g : x ⟶ y) :
    @homL _ _ L hL ⟨i, x⟩ ⟨i, y⟩ :=
  homInclL L hL x y ⟨i, D.refl i, D.refl i⟩ (reflApp L x ≫ g ≫ isoInv (reflApp_isIso L y))

/-- `stageInclL` is functorial on identities: `stageInclL (id) = idL`.  (`reflApp x ≫ id ≫
    (reflApp x)⁻¹ = id`, the reflexive-bound identity germ.) -/
public theorem stageInclL_id {i : ι} (x : L.A i) :
    stageInclL L hL (Cat.id x) = @idL _ _ L hL ⟨i, x⟩ := by
  unfold stageInclL
  rw [Cat.id_comp, isoInv_comp]
  rfl

/-- `stageInclL` preserves composition: `stageInclL (g ≫ h) = compL (stageInclL g) (stageInclL h)`.
    The middle `(reflApp y)⁻¹ ≫ reflApp y = id` cancels (lax functoriality of the inclusion). -/
public theorem stageInclL_comp {i : ι} {x y z : L.A i} (g : x ⟶ y) (h : y ⟶ z) :
    stageInclL L hL (g ≫ h)
      = @compL _ _ L hL ⟨i, x⟩ ⟨i, y⟩ ⟨i, z⟩ (stageInclL L hL g) (stageInclL L hL h) := by
  unfold stageInclL
  rw [compL_homInclL_compAtL L hL x y z ⟨i, D.refl i, D.refl i⟩ _ ⟨i, D.refl i, D.refl i⟩ _ i
    (D.refl i) (D.refl i)]
  -- both pushes at refl are identity (push_refl); the middle isoInv ≫ reflApp cancels.
  rw [hL.push_refl x y (D.refl i) (D.refl i) (reflApp L x ≫ g ≫ isoInv (reflApp_isIso L y)),
      hL.push_refl y z (D.refl i) (D.refl i) (reflApp L y ≫ h ≫ isoInv (reflApp_isIso L z))]
  congr 1
  -- RHS: cancel `isoInv y ≫ reflApp y = id`.
  simp only [Cat.assoc]
  rw [← Cat.assoc (isoInv (reflApp_isIso L y)) (reflApp L y), inv_isoInv_comp, Cat.id_comp]

/-- **Cover reflection through the stage inclusion.**  If `stageInclL g` is a cover in the colimit
    (transitions conservative `hcons`, mono-preserving `hmono`, faithful for the iso reflection), then
    `g` is a cover in its stage `L.A i`.  A stage mono `m'` factoring `g` includes (`stageInclL`) to a
    colimit mono (`homInclL_mono_of_stage` via `hmono`) factoring `stageInclL g`; the colimit cover
    forces it iso; iso reflection (`homInclL_isIso_reflects'` via `hcons`) brings the iso back.  Lax
    `homInclObj_cover_reflects`. -/
public theorem homInclL_cover_reflects
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (φ : x ⟶ y),
        Monic φ → IsIso ((L.functF hij).map φ) → IsIso φ)
    (hmono : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (φ : x ⟶ y),
        Monic φ → Monic ((L.functF hij).map φ))
    {i : ι} {x y : L.A i} (g : x ⟶ y)
    (hcov : @Cover (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨i, y⟩ (stageInclL L hL g)) :
    Cover g := by
  letI : Cat (Obj L) := laxColimCat L hL
  intro c m' g'' hm' hg''m'
  -- include the stage mono `m'` as a colimit mono (mono of stage via hmono).
  have hM_mono : @Monic (Obj L) (laxColimCat L hL) ⟨i, c⟩ ⟨i, y⟩ (stageInclL L hL m') := by
    unfold stageInclL
    apply homInclL_mono_of_stage L hL c y ⟨i, D.refl i, D.refl i⟩
    intro e hie z u v huv
    -- `pushHom (reflApp ≫ m' ≫ isoInv) = transApp ≫ map(reflApp ≫ m' ≫ isoInv) ≫ isoInv`,
    -- all but `map m'` isos, and `map m'` mono (hmono) ⇒ the push is mono.
    -- left/right-cancel the flanking isos in `huv`, apply `hmono`, re-flank.
    have hmono_map : Monic ((L.functF hie).map m') := hmono hie m' hm'
    -- `pushHom = transApp ≫ map(reflApp x ≫ m' ≫ isoInv) ≫ isoInv transApp`; expand `map`.
    revert huv
    unfold pushHom
    rw [(L.functF hie).map_comp (reflApp L c) (m' ≫ isoInv (reflApp_isIso L y)),
        (L.functF hie).map_comp m' (isoInv (reflApp_isIso L y))]
    intro huv
    -- the composite map is mono: map m' mono flanked by isos (pre/post compose mono by iso stays mono).
    have hbig : Monic ((L.functF hie).map (reflApp L c)
          ≫ (L.functF hie).map m'
          ≫ (L.functF hie).map (isoInv (reflApp_isIso L y))) :=
      mono_precomp_iso'
        (functor_preserves_iso (F := L.functF hie) (reflApp L c) (reflApp_isIso L c))
        (mono_postcomp_iso' hmono_map
          (functor_preserves_iso (F := L.functF hie) (isoInv (reflApp_isIso L y))
            ⟨reflApp L y, inv_isoInv_comp _, isoInv_comp _⟩))
    exact mono_precomp_iso' (transApp_isIso L (D.refl i) hie c)
      (mono_postcomp_iso' hbig
        ⟨transApp L (D.refl i) hie y, inv_isoInv_comp _, isoInv_comp _⟩) u v huv
  -- factorization `stageInclL g'' ⊚ stageInclL m' = stageInclL g`.
  have hfac : @compL _ _ L hL ⟨i, x⟩ ⟨i, c⟩ ⟨i, y⟩ (stageInclL L hL g'') (stageInclL L hL m')
      = stageInclL L hL g := by
    rw [← stageInclL_comp L hL g'' m', hg''m']
  have hMiso : @IsIso (Obj L) (laxColimCat L hL) ⟨i, c⟩ ⟨i, y⟩ (stageInclL L hL m') :=
    hcov (stageInclL L hL m') (stageInclL L hL g'') hM_mono hfac
  exact homInclL_isIso_reflects' L hL hcons c y m' hm' hMiso

/-! ## Object realignment: identifying `⟨i,x⟩` with its push `⟨e, F x⟩`

  The bare-Σ objects live at different stages, but `⟨i,x⟩` is ISOMORPHIC in the colimit to
  `⟨e, F (i≤e) x⟩` for any `e ≥ i` (the inclusion of the iso `reflApp`-style germ).  This is the lax
  replacement for the strict `objIncl`-image identification: it lets an arbitrary cospan be aligned to
  a single fibre by transporting along these isos. -/

/-- The realignment germ `⟨i,x⟩ ⟶ ⟨e, F (i≤e) x⟩`: the germ of `reflApp (F x)`-style identity at the
    bound `⟨e, hie, refl e⟩`.  Concretely the identity map `id (F (i≤e) x)` viewed as a germ from `x`
    (at source transition `hie`) to `F x` (at target transition `refl e`). -/
@[expose] public noncomputable def alignGerm {i : ι} (x : L.A i) {e : ι} (hie : D.le i e) :
    @homL _ _ L hL ⟨i, x⟩ ⟨e, L.F hie x⟩ :=
  homInclL L hL x (L.F hie x) ⟨e, hie, D.refl e⟩ (isoInv (reflApp_isIso L (L.F hie x)))

/-- The inverse realignment germ `⟨e, F x⟩ ⟶ ⟨i,x⟩`. -/
@[expose] public noncomputable def alignGermInv {i : ι} (x : L.A i) {e : ι} (hie : D.le i e) :
    @homL _ _ L hL ⟨e, L.F hie x⟩ ⟨i, x⟩ :=
  homInclL L hL (L.F hie x) x ⟨e, D.refl e, hie⟩ (reflApp L (L.F hie x))

/-- `alignGerm` is an iso (the realignment identifies `⟨i,x⟩` with `⟨e, F x⟩`).  Both round-trips
    reduce, at stage `e`, to the included identity via `homInclL_isIso_of_rep`. -/
public theorem alignGerm_isIso {i : ι} (x : L.A i) {e : ι} (hie : D.le i e) :
    @IsIso (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨e, L.F hie x⟩ (alignGerm L hL x hie) := by
  unfold alignGerm
  refine homInclL_isIso_of_rep L hL x (L.F hie x) ⟨e, hie, D.refl e⟩
    (isoInv (reflApp_isIso L (L.F hie x))) (reflApp L (L.F hie x)) ?_ ?_
  · exact inv_isoInv_comp (reflApp_isIso L (L.F hie x))
  · exact isoInv_comp (reflApp_isIso L (L.F hie x))

/-- **Factorization of an arbitrary hom through the realignment isos.**  For `f = homInclL xa xz a f₀`
    and any `U ≥ a.1`, `f = alignGerm xa ⊚ stageInclL (pushHom f₀) ⊚ alignGermInv xz`, where
    `pushHom f₀ : F(ia≤U) xa ⟶ F(iz≤U) xz` is the stage-`U` push.  This expresses any colimit hom as a
    stage-inclusion flanked by the (iso) realignments — the bridge to single-fibre cospans.  Both
    sides reduce, at stage `U`, to the same germ (the `reflApp`/`isoInv` units cancel telescopically). -/
public theorem homInclL_factor {ia iz : ι} (xa : L.A ia) (xz : L.A iz) (a : UpperBound D ia iz)
    (f₀ : L.F a.2.1 xa ⟶ L.F a.2.2 xz) {U : ι} (haU : D.le a.1 U) :
    homInclL L hL xa xz a f₀
      = @compL _ _ L hL ⟨ia, xa⟩ ⟨U, L.F (D.trans a.2.1 haU) xa⟩ ⟨iz, xz⟩
          (alignGerm L hL xa (D.trans a.2.1 haU))
          (@compL _ _ L hL ⟨U, L.F (D.trans a.2.1 haU) xa⟩ ⟨U, L.F (D.trans a.2.2 haU) xz⟩ ⟨iz, xz⟩
            (stageInclL L hL (pushHom L xa xz a.2.1 a.2.2 haU f₀))
            (alignGermInv L hL xz (D.trans a.2.2 haU))) := by
  -- compute the RHS inner `compL (stageInclL ...) (alignGermInv ...)` first, then the outer.
  unfold stageInclL alignGerm alignGermInv
  -- inner: stageInclL pushed-f₀ (bound ⟨U,refl,refl⟩) ⊚ alignGermInv xz (bound ⟨U,refl, iz≤U⟩) at U.
  rw [compL_homInclL_compAtL L hL (L.F (D.trans a.2.1 haU) xa) (L.F (D.trans a.2.2 haU) xz) xz
      ⟨U, D.refl U, D.refl U⟩ _ ⟨U, D.refl U, D.trans a.2.2 haU⟩ _ U (D.refl U) (D.refl U)]
  rw [hL.push_refl (L.F (D.trans a.2.1 haU) xa) (L.F (D.trans a.2.2 haU) xz) (D.refl U) (D.refl U)
        (reflApp L (L.F (D.trans a.2.1 haU) xa) ≫ pushHom L xa xz a.2.1 a.2.2 haU f₀
          ≫ isoInv (reflApp_isIso L (L.F (D.trans a.2.2 haU) xz))),
      hL.push_refl (L.F (D.trans a.2.2 haU) xz) xz (D.refl U) (D.trans a.2.2 haU)
        (reflApp L (L.F (D.trans a.2.2 haU) xz))]
  -- outer: alignGerm xa (bound ⟨U, ia≤U, refl⟩) ⊚ (the inner germ at bound ⟨U, refl, iz≤U⟩) at U.
  rw [compL_homInclL_compAtL L hL xa (L.F (D.trans a.2.1 haU) xa) xz
      ⟨U, D.trans a.2.1 haU, D.refl U⟩ _ ⟨U, D.refl U, D.trans a.2.2 haU⟩ _ U (D.refl U) (D.refl U)]
  rw [hL.push_refl xa (L.F (D.trans a.2.1 haU) xa) (D.trans a.2.1 haU) (D.refl U)
        (isoInv (reflApp_isIso L (L.F (D.trans a.2.1 haU) xa))),
      hL.push_refl (L.F (D.trans a.2.1 haU) xa) xz (D.refl U) (D.trans a.2.2 haU) _]
  -- LHS: include `f₀` at bound `a`, then absorb to stage `U` via `homInclL_compat`.
  rw [← homInclL_compat L hL xa xz (a := a) (b := ⟨U, D.trans a.2.1 haU, D.trans a.2.2 haU⟩) haU f₀]
  -- both sides now `homInclL` at bound `⟨U, ia≤U, iz≤U⟩`; reduce the germ reps.
  congr 1
  -- telescoping cancellation: `isoInv(reflApp ·) ≫ reflApp · = id` on both ends.
  simp only [Cat.assoc]
  rw [← Cat.assoc (isoInv (reflApp_isIso L (L.F (D.trans a.2.1 haU) xa))),
      inv_isoInv_comp, Cat.id_comp, inv_isoInv_comp, Cat.comp_id]

/-! ## Generic finite-limit-preservation ⟹ pullback-cone preservation (ported)

  The generic equalizer/pullback transport lemmas (`Colim.pullback_of_equalizer`,
  `Colim.isEqualizer_comp_iso`, `Colim.isEqualizer_iso_apex`) come straight from
  `S1_543_CatColimitRegular.lean` (imported).  `image_chosenPullback_isPullback` is re-proved
  below at this section's single universe `w` so the lax `stageInclFunctorL`'s preservation can
  be fed through it. -/
section GenericPullbackPres

variable {𝒟 : Type w} [Cat.{w} 𝒟]

/-- **A product- and equalizer-preserving functor sends the §1.432 chosen pullback to a pullback
    cone** (ported verbatim from `CatColimitRegular.image_chosenPullback_isPullback`). -/
public theorem image_chosenPullback_isPullback' {𝒞 : Type w} [Cat.{w} 𝒞]
    [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasEqualizers 𝒞]
    [HasTerminal 𝒟] [HasBinaryProducts 𝒟] [HasEqualizers 𝒟]
    (F : Functor 𝒞 𝒟)
    (hprod : PreservesBinaryProducts F) (hpeq : PreservesEqualizers F)
    {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) :
    (Cone.mk (f := F.map f) (g := F.map g)
      (F.obj (products_equalizers_implies_pullbacks f g).cone.pt)
      (F.map (products_equalizers_implies_pullbacks f g).cone.π₁)
      (F.map (products_equalizers_implies_pullbacks f g).cone.π₂)
      (by rw [← F.map_comp, ← F.map_comp,
              (products_equalizers_implies_pullbacks f g).cone.w])).IsPullback := by
  let eo : 𝒞 := eqObj (fst ≫ f) (snd ≫ g)
  let em : eo ⟶ prod A B := eqMap (fst ≫ f) (snd ≫ g)
  have hFem_eq : F.map em ≫ F.map (fst ≫ f) = F.map em ≫ F.map (snd ≫ g) :=
    (F.map_comp em (fst ≫ f)).symm.trans
      ((congrArg F.map (eqMap_eq (fst ≫ f) (snd ≫ g))).trans (F.map_comp em (snd ≫ g)))
  let cD := HasEqualizers.eq (F.obj (prod A B)) (F.obj C) (F.map (fst ≫ f)) (F.map (snd ≫ g))
  let hcone : EqualizerCone (F.map (fst ≫ f)) (F.map (snd ≫ g)) :=
    { dom := F.obj eo, map := F.map em, eq := hFem_eq }
  let k := cD.lift hcone
  have hk_fac : k ≫ eqMap (F.map (fst ≫ f)) (F.map (snd ≫ g)) = F.map em := cD.fac hcone
  have hk_iso : IsIso k := hpeq (fst ≫ f) (snd ≫ g)
  obtain ⟨k', hkk', hk'k⟩ := hk_iso
  have hFem_isEq : (EqualizerCone.mk (F.obj eo) (F.map em) hFem_eq).IsEqualizer := by
    have h0 := Colim.isEqualizer_iso_apex
      (chosenEqualizer_isEqualizer (F.map (fst ≫ f)) (F.map (snd ≫ g))) k k' hkk' hk'k
    intro d
    obtain ⟨u, hu, huniq⟩ := h0 d
    refine ⟨u, ?_, fun v hv => huniq v ?_⟩
    · exact (congrArg (u ≫ ·) hk_fac).symm.trans hu
    · exact (congrArg (v ≫ ·) hk_fac).trans hv
  let φ : F.obj (prod A B) ⟶ prod (F.obj A) (F.obj B) :=
    pair (F.map (fst (A := A) (B := B))) (F.map snd)
  have hφ_iso : IsIso φ := hprod (A := A) (B := B)
  have hφ_fst : φ ≫ fst = F.map (fst (A := A) (B := B)) := fst_pair _ _
  have hφ_snd : φ ≫ snd = F.map (snd (A := A) (B := B)) := snd_pair _ _
  have hpair_f : F.map (fst ≫ f) = φ ≫ (fst ≫ F.map f) := by
    rw [F.map_comp, ← Cat.assoc, hφ_fst]
  have hpair_g : F.map (snd ≫ g) = φ ≫ (snd ≫ F.map g) := by
    rw [F.map_comp, ← Cat.assoc, hφ_snd]
  have hFem_isEq' : (EqualizerCone.mk (f := φ ≫ (fst ≫ F.map f)) (g := φ ≫ (snd ≫ F.map g))
      (F.obj eo) (F.map em) (by rw [← hpair_f, ← hpair_g]; exact hFem_eq)).IsEqualizer := by
    intro d
    have hd : d.map ≫ F.map (fst ≫ f) = d.map ≫ F.map (snd ≫ g) := by
      rw [hpair_f, hpair_g]; exact d.eq
    obtain ⟨u, hu, huniq⟩ := hFem_isEq (EqualizerCone.mk d.dom d.map hd)
    exact ⟨u, hu, huniq⟩
  have hslid := Colim.isEqualizer_comp_iso hφ_iso
    (by rw [← hpair_f, ← hpair_g]; exact hFem_eq) hFem_isEq'
  have hmeq : (F.map em ≫ φ) ≫ (fst ≫ F.map f) = (F.map em ≫ φ) ≫ (snd ≫ F.map g) := by
    rw [Cat.assoc, Cat.assoc, ← hpair_f, ← hpair_g]; exact hFem_eq
  have hpb := Colim.pullback_of_equalizer hmeq hslid
  intro d
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hpb d
  have hbr₁ : F.map em ≫ φ ≫ fst = F.map (em ≫ fst) := by rw [hφ_fst, ← F.map_comp]
  have hbr₂ : F.map em ≫ φ ≫ snd = F.map (em ≫ snd) := by rw [hφ_snd, ← F.map_comp]
  refine ⟨u, ⟨?_, ?_⟩, ?_⟩
  · show u ≫ F.map (em ≫ fst) = d.π₁
    rw [show F.map (em ≫ fst) = (F.map em ≫ φ) ≫ fst from
      ((Cat.assoc _ _ _).trans hbr₁).symm]; exact hu₁
  · show u ≫ F.map (em ≫ snd) = d.π₂
    rw [show F.map (em ≫ snd) = (F.map em ≫ φ) ≫ snd from
      ((Cat.assoc _ _ _).trans hbr₂).symm]; exact hu₂
  · intro v hv₁ hv₂
    refine huniq v ?_ ?_
    · show v ≫ (F.map em ≫ φ) ≫ fst = d.π₁
      rw [show (F.map em ≫ φ) ≫ fst = F.map (em ≫ fst) from (Cat.assoc _ _ _).trans hbr₁]
      exact hv₁
    · show v ≫ (F.map em ≫ φ) ≫ snd = d.π₂
      rw [show (F.map em ≫ φ) ≫ snd = F.map (em ≫ snd) from (Cat.assoc _ _ _).trans hbr₂]
      exact hv₂

-- A cone with the binary-product universal property has iso comparison map:
-- `Colim.isIso_of_product_up` (`S1_543_CatColimitRegular.lean`), used directly below.

end GenericPullbackPres

/-! ## The lax stage-inclusion functor (single-universe)

  `image_chosenPullback_isPullback` (the §1.45 finite-limit machinery) requires the source and target
  categories at the SAME hom-universe.  The fibre `L.A i` has hom-universe `w`; the colimit `Obj L` has
  `max u w`.  These coincide exactly when the index universe `u ≤ w` — concretely when `ι : Type w`,
  matching the strict `colimitCanonicalCover`'s `CatSystem.{u,u}` constraint.  We therefore package the
  stage-inclusion FUNCTOR (and everything downstream toward `hcanon`) for `ι : Type w`. -/
public theorem stageInclL_mono_of_stage
    (hmono : ∀ {i j : ι} (hij : D.le i j),
        @PreservesMono _ (L.catA i) _ (L.catA j) (L.functF hij))
    {i : ι} {x y : L.A i} (m : x ⟶ y) (hm : @Monic (L.A i) (L.catA i) _ _ m) :
    @Monic (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨i, y⟩ (stageInclL L hL m) := by
  letI : Cat (Obj L) := laxColimCat L hL
  unfold stageInclL
  apply homInclL_mono_of_stage L hL x y ⟨i, D.refl i, D.refl i⟩
  intro e hie z u v huv
  have hmono_map : Monic (L.Fmap hie m) := hmono hie hm
  revert huv
  unfold pushHom
  rw [(L.functF hie).map_comp (reflApp L x) (m ≫ isoInv (reflApp_isIso L y)),
      (L.functF hie).map_comp m (isoInv (reflApp_isIso L y))]
  intro huv
  have hbig : Monic (L.Fmap hie (reflApp L x)
        ≫ L.Fmap hie m
        ≫ L.Fmap hie (isoInv (reflApp_isIso L y))) :=
    mono_precomp_iso'
      (functor_preserves_iso (F := L.functF hie) (reflApp L x) (reflApp_isIso L x))
      (mono_postcomp_iso' hmono_map
        (functor_preserves_iso (F := L.functF hie) (isoInv (reflApp_isIso L y))
          ⟨reflApp L y, inv_isoInv_comp _, isoInv_comp _⟩))
  exact mono_precomp_iso' (transApp_isIso L (D.refl i) hie x)
    (mono_postcomp_iso' hbig
      ⟨transApp L (D.refl i) hie y, inv_isoInv_comp _, isoInv_comp _⟩) u v huv
section SingleUniverse

variable {ι : Type w} {D : Directed ι} (L : LaxCatSystem.{w, w} ι D) (hL : Coherent L)

/-- The lax stage-inclusion functor at stage `i` (object map `⟨i,·⟩`, morphism map `stageInclL`).
    Requires `ι : Type w` so source `L.A i` and target `Obj L` share the hom-universe `w`. -/
@[expose] public noncomputable def stageInclFunctorL (i : ι) :
    @Functor (L.A i) (Obj L) (L.catA i) (laxColimCat L hL) :=
  letI : Cat (Obj L) := laxColimCat L hL
  { obj := fun x => ⟨i, x⟩
    map := fun {_x _y} g => stageInclL L hL g
    map_id := fun x => stageInclL_id L hL x
    map_comp := fun {_x _y _z} g h => stageInclL_comp L hL g h }

/-! ## Cover reflection/preservation for the stage-inclusion functor need faithfulness etc.

  The remaining `hcanon` discharge instantiates the toolkit above (`homInclL_cover_reflects`,
  `homInclL_cover_of_stage`, `homInclL_factor`) at the lax base-change system.  Cover
  reflection/preservation through `stageInclFunctorL` is just `homInclL_cover_reflects` /
  `homInclL_cover_of_stage` since `stageInclFunctorL.map = stageInclL`. -/

/-! ### `stageInclFunctorL` preserves binary products

  The comparison map `pair (F fst) (F snd) : ⟨i, A×B⟩ ⟶ prod_colim (⟨i,A⟩) (⟨i,B⟩)` is iso.  By
  `Colim.isIso_of_product_up` it suffices that the cone `(⟨i, A×B⟩, F fst, F snd)` has the binary-product
  universal property in the colimit: this is the lax mirror of the strict `objIncl_preserves_products`
  mediator construction (push competitors to a common stage `N ≥ i`, use `pData.presPair` there). -/

/-- Universal property of the `F`-image product cone `(⟨i, (hp i).prod x y⟩, F fst, F snd)`. -/
public theorem stageInclL_product_up (pData : LaxProductData L) (i : ι) (x y : L.A i)
    {Z : Obj L}
    (f : homL L hL Z ⟨i, x⟩)
    (g : homL L hL Z ⟨i, y⟩) :
    letI : Cat (Obj L) := laxColimCat L hL
    ∃ u : Z ⟶ (⟨i, (pData.hp i).prod x y⟩ : Obj L),
      (u ≫ stageInclL L hL (pData.hp i).fst = f ∧ u ≫ stageInclL L hL (pData.hp i).snd = g) ∧
      ∀ v : Z ⟶ (⟨i, (pData.hp i).prod x y⟩ : Obj L),
        v ≫ stageInclL L hL (pData.hp i).fst = f →
        v ≫ stageInclL L hL (pData.hp i).snd = g → v = u := by
  letI : Cat (Obj L) := laxColimCat L hL
  obtain ⟨lz, z⟩ := Z
  let p := (pData.hp i).prod x y
  -- The projection germs as `homInclL` of `reflApp p ≫ proj` with `proj : p ⟶ L.F (refl i) ·`.
  have hfst_eq : stageInclL L hL (pData.hp i).fst
      = homInclL L hL p x ⟨i, D.refl i, D.refl i⟩
          (reflApp L p ≫ ((pData.hp i).fst ≫ isoInv (reflApp_isIso L x))) := by
    rfl
  have hsnd_eq : stageInclL L hL (pData.hp i).snd
      = homInclL L hL p y ⟨i, D.refl i, D.refl i⟩
          (reflApp L p ≫ ((pData.hp i).snd ≫ isoInv (reflApp_isIso L y))) := by
    rfl
  -- ===== Joint monicity of the two projections at apex `⟨i,p⟩` (uniqueness ingredient). =====
  have hjm : ∀ h₁ h₂ : homL L hL ⟨lz, z⟩ ⟨i, p⟩,
      compL L hL h₁ (stageInclL L hL (pData.hp i).fst)
        = compL L hL h₂ (stageInclL L hL (pData.hp i).fst) →
      compL L hL h₁ (stageInclL L hL (pData.hp i).snd)
        = compL L hL h₂ (stageInclL L hL (pData.hp i).snd) →
      h₁ = h₂ := by
    -- Same-stage mirror of `prJointMono`: product at stage `i`, projection germs
    -- `homInclL ⟨i,refl,refl⟩ (reflApp p ≫ (proj ≫ isoInv reflApp))`.  Set `k := i`, `hik := refl i`
    -- and `projF := fst ≫ isoInv reflApp`, `projS := snd ≫ isoInv reflApp`.
    intro h₁ h₂ hf hs
    rw [hfst_eq] at hf
    rw [hsnd_eq] at hs
    let hik : D.le i i := D.refl i
    let projF : p ⟶ L.F hik x := (pData.hp i).fst ≫ isoInv (reflApp_isIso L x)
    let projS : p ⟶ L.F hik y := (pData.hp i).snd ≫ isoInv (reflApp_isIso L y)
    revert hf hs
    refine Quotient.inductionOn₂ h₁ h₂ (fun rh₁ rh₂ hf hs => ?_)
    obtain ⟨a₁, m₁⟩ := rh₁
    obtain ⟨a₂, m₂⟩ := rh₂
    -- common bound `e ≥ a₁.1, a₂.1, i`.
    obtain ⟨w0, hw0a, hw0b⟩ := D.bound a₁.1 a₂.1
    obtain ⟨e, hew, hek⟩ := D.bound w0 i
    have ha₁e : D.le a₁.1 e := D.trans hw0a hew
    have ha₂e : D.le a₂.1 e := D.trans hw0b hew
    rw [prCompProj L hL z p x hik projF a₁ m₁ e ha₁e hek,
        prCompProj L hL z p x hik projF a₂ m₂ e ha₂e hek] at hf
    rw [prCompProj L hL z p y hik projS a₁ m₁ e ha₁e hek,
        prCompProj L hL z p y hik projS a₂ m₂ e ha₂e hek] at hs
    obtain ⟨cf, hcf1, hcf2, eqf⟩ := Quotient.exact hf
    obtain ⟨cs, hcs1, hcs2, eqs⟩ := Quotient.exact hs
    obtain ⟨n, hcfn, hcsn⟩ := D.bound cf.1 cs.1
    simp only [homSystemL] at eqf eqs
    rw [prPsi_push L hL z p x hik projF a₁ m₁ e cf.1 ha₁e hek hcf1,
        prPsi_push L hL z p x hik projF a₂ m₂ e cf.1 ha₂e hek hcf2] at eqf
    rw [prPsi_push L hL z p y hik projS a₁ m₁ e cs.1 ha₁e hek hcs1,
        prPsi_push L hL z p y hik projS a₂ m₂ e cs.1 ha₂e hek hcs2] at eqs
    have eqf' := congrArg (pushHom L z x (D.trans a₁.2.1 (D.trans ha₁e hcf1))
        (D.trans hik (D.trans hek hcf1)) hcfn) eqf
    have eqs' := congrArg (pushHom L z y (D.trans a₁.2.1 (D.trans ha₁e hcs1))
        (D.trans hik (D.trans hek hcs1)) hcsn) eqs
    rw [prPsi_push L hL z p x hik projF a₁ m₁ cf.1 n _ _ hcfn,
        prPsi_push L hL z p x hik projF a₂ m₂ cf.1 n _ _ hcfn] at eqf'
    rw [prPsi_push L hL z p y hik projS a₁ m₁ cs.1 n _ _ hcsn,
        prPsi_push L hL z p y hik projS a₂ m₂ cs.1 n _ _ hcsn] at eqs'
    unfold prPsi at eqf' eqs'
    rw [pushHom_proj L x p hik _ projF] at eqf'
    rw [pushHom_proj L y p hik _ projS] at eqs'
    have hkn : D.le i n := D.trans hek (D.trans hcf1 hcfn)
    have ha₁n : D.le a₁.1 n := D.trans ha₁e (D.trans hcf1 hcfn)
    have ha₂n : D.le a₂.1 n := D.trans ha₂e (D.trans hcf1 hcfn)
    let u₁ : L.F (D.trans a₁.2.1 ha₁n) z ⟶ L.F hkn p :=
      pushHom L z p a₁.2.1 a₁.2.2 ha₁n m₁ ≫ prUnit L p hkn
    let u₂ : L.F (D.trans a₂.2.1 ha₂n) z ⟶ L.F hkn p :=
      pushHom L z p a₂.2.1 a₂.2.2 ha₂n m₂ ≫ prUnit L p hkn
    -- strip the trailing `isoInv (transApp)` AND the trailing `map (isoInv reflApp)` (from `projF`).
    have hproj : ∀ (w : L.A i) (pr : p ⟶ w),
        (L.functF hkn).map (pr ≫ isoInv (reflApp_isIso L w))
            ≫ isoInv (transApp_isIso L hik hkn w) ≫ transApp L hik hkn w
              ≫ (L.functF hkn).map (reflApp L w)
          = (L.functF hkn).map pr := by
      intro w pr
      rw [← Cat.assoc (isoInv (transApp_isIso L hik hkn w)), inv_isoInv_comp, Cat.id_comp,
          (L.functF hkn).map_comp pr (isoInv (reflApp_isIso L w)),
          Cat.assoc, ← (L.functF hkn).map_comp (isoInv (reflApp_isIso L w)) (reflApp L w),
          inv_isoInv_comp,
          (L.functF hkn).map_id,
          Cat.comp_id]
    have hfst : u₁ ≫ (L.functF hkn).map (pData.hp i).fst
        = u₂ ≫ (L.functF hkn).map (pData.hp i).fst := by
      have := congrArg (· ≫ transApp L hik hkn x ≫ (L.functF hkn).map (reflApp L x)) eqf'
      simp only [projF, Cat.assoc] at this ⊢
      rw [hproj x (pData.hp i).fst] at this
      simpa only [u₁, u₂, Cat.assoc] using this
    have hsnd : u₁ ≫ (L.functF hkn).map (pData.hp i).snd
        = u₂ ≫ (L.functF hkn).map (pData.hp i).snd := by
      have := congrArg (· ≫ transApp L hik hkn y ≫ (L.functF hkn).map (reflApp L y)) eqs'
      simp only [projS, Cat.assoc] at this ⊢
      rw [hproj y (pData.hp i).snd] at this
      simpa only [u₁, u₂, Cat.assoc] using this
    have huv : u₁ = u₂ :=
      pData.pres hkn x y (L.F (D.trans a₁.2.1 ha₁n) z) u₁ u₂ hfst hsnd
    have hmm : pushHom L z p a₁.2.1 a₁.2.2 ha₁n m₁ = pushHom L z p a₂.2.1 a₂.2.2 ha₂n m₂ := by
      have h2 := congrArg (· ≫ isoInv (prUnit_isIso L p hkn)) huv
      simpa only [u₁, u₂, Cat.assoc, isoInv_comp, Cat.comp_id] using h2
    exact Quotient.sound ⟨⟨n, D.trans a₁.2.1 ha₁n, hkn⟩, ha₁n, ha₂n, hmm⟩
  -- ===== EXISTENCE: build the mediator via `pData.presPair` at a common stage `N ≥ i`. =====
  refine Quotient.inductionOn f (fun rf => ?_)
  refine Quotient.inductionOn g (fun rg => ?_)
  obtain ⟨af, fa⟩ := rf
  obtain ⟨ag, ga⟩ := rg
  -- common stage `N ≥ af.1, ag.1, i`.
  obtain ⟨e1, he1a, he1b⟩ := D.bound af.1 ag.1
  obtain ⟨N, hNe, hNi⟩ := D.bound e1 i
  have hafN : D.le af.1 N := D.trans he1a hNe
  have hagN : D.le ag.1 N := D.trans he1b hNe
  have hiN : D.le i N := hNi
  have hlN : D.le lz N := D.trans af.2.1 hafN
  -- push competitors and convert targets to `F (i≤N) x` / `F (i≤N) y` via `transApp`.
  let p_comp : L.F hlN z ⟶ L.F hiN x :=
    pushHom L z x af.2.1 af.2.2 hafN fa ≫ transApp L (D.refl i) hiN x ≫ (L.functF hiN).map (reflApp L x)
  let q_comp : L.F hlN z ⟶ L.F hiN y :=
    pushHom L z y ag.2.1 ag.2.2 hagN ga ≫ transApp L (D.refl i) hiN y ≫ (L.functF hiN).map (reflApp L y)
  obtain ⟨r, hr_fst, hr_snd⟩ := pData.presPair hiN x y (L.F hlN z) p_comp q_comp
  -- the shared cancellation: `(r ≫ isoInv prUnit) ⊚ stageInclL proj` reduces to the pushed
  -- competitor at stage `N`, hence (homInclL_compat) the original competitor germ.
  have leg : ∀ (w : L.A i) (proj : p ⟶ w) (aw : UpperBound D lz i)
      (wa : L.F aw.2.1 z ⟶ L.F aw.2.2 w) (hawN : D.le aw.1 N),
      r ≫ (L.functF hiN).map proj
          = pushHom L z w aw.2.1 aw.2.2 hawN wa ≫ transApp L (D.refl i) hiN w
              ≫ (L.functF hiN).map (reflApp L w) →
      @compL _ _ L hL ⟨lz, z⟩ ⟨i, p⟩ ⟨i, w⟩
          (homInclL L hL z p ⟨N, hlN, hiN⟩ (r ≫ isoInv (prUnit_isIso L p hiN)))
          (homInclL L hL p w ⟨i, D.refl i, D.refl i⟩
            (reflApp L p ≫ (proj ≫ isoInv (reflApp_isIso L w))))
        = Quotient.mk (setoid (homSystemL L hL z w)) ⟨aw, wa⟩ := by
    intro w proj aw wa hawN hcomp
    show homCompRawL L hL z p w ⟨N, hlN, hiN⟩ (r ≫ isoInv (prUnit_isIso L p hiN))
        ⟨i, D.refl i, D.refl i⟩ (reflApp L p ≫ (proj ≫ isoInv (reflApp_isIso L w)))
      = homInclL L hL z w aw wa
    rw [homCompRawL_eq_compAtL L hL z p w ⟨N, hlN, hiN⟩ (r ≫ isoInv (prUnit_isIso L p hiN))
          ⟨i, D.refl i, D.refl i⟩ (reflApp L p ≫ (proj ≫ isoInv (reflApp_isIso L w))) N (D.refl N) hiN]
    unfold compAtL
    -- left push along `refl N` is the identity; right push by `pushHom_proj` (source `refl i`).
    rw [hL.push_refl z p hlN hiN (r ≫ isoInv (prUnit_isIso L p hiN)),
        pushHom_proj L w p (D.refl i) hiN (proj ≫ isoInv (reflApp_isIso L w))]
    -- cancel `isoInv prUnit ≫ prUnit = id`.
    rw [Cat.assoc, ← Cat.assoc (isoInv (prUnit_isIso L p hiN)),
        inv_isoInv_comp, Cat.id_comp]
    -- distribute `map (proj ≫ isoInv reflApp)` and use `hcomp` to substitute `r ≫ map proj`.
    rw [(L.functF hiN).map_comp proj (isoInv (reflApp_isIso L w)), ← Cat.assoc, ← Cat.assoc r,
        hcomp]
    -- now `pushHom wa ≫ transApp ≫ map(reflApp w) ≫ map(isoInv reflApp w) ≫ isoInv transApp`.
    -- `map(reflApp) ≫ map(isoInv reflApp) = id`, then `transApp ≫ isoInv transApp = id`.
    simp only [Cat.assoc, ← Functor.map_comp, isoInv_comp, Functor.map_id]
    rw [show 𝟙 ((L.functF hiN).obj (L.F (D.refl i) w)) = 𝟙 (L.F hiN (L.F (D.refl i) w))
      from rfl, Cat.id_comp, isoInv_comp, Cat.comp_id]
    -- absorb the level `aw.1 → N` transition by `homInclL_compat`.
    exact homInclL_compat L hL z w (a := aw)
      (b := ⟨N, D.trans aw.2.1 hawN, D.trans aw.2.2 hawN⟩) hawN wa
  -- the mediator `u` (with `isoInv prUnit` baked in to cancel the projection's `prUnit` prefactor).
  refine ⟨homInclL L hL z p ⟨N, hlN, hiN⟩ (r ≫ isoInv (prUnit_isIso L p hiN)), ⟨?_, ?_⟩, ?_⟩
  · rw [hfst_eq]; exact leg x (pData.hp i).fst af fa hafN hr_fst
  · rw [hsnd_eq]; exact leg y (pData.hp i).snd ag ga hagN hr_snd
  · intro v hv1 hv2
    apply hjm
    · show v ≫ stageInclL L hL (pData.hp i).fst = _
      rw [hv1, hfst_eq]; exact (leg x (pData.hp i).fst af fa hafN hr_fst).symm
    · show v ≫ stageInclL L hL (pData.hp i).snd = _
      rw [hv2, hsnd_eq]; exact (leg y (pData.hp i).snd ag ga hagN hr_snd).symm

/-- **`stageInclFunctorL i` preserves binary products** (for the colimit's
    `laxColimHasBinaryProducts`).  The comparison map `pair (F fst) (F snd)` is iso by
    `Colim.isIso_of_product_up`, whose hypothesis is the product universal property `stageInclL_product_up`. -/
public theorem stageInclFunctorL_preservesProducts (pData : LaxProductData L) (i : ι) :
    @PreservesBinaryProducts (L.A i) (Obj L) (L.catA i) (laxColimCat L hL)
      (stageInclFunctorL L hL i) (pData.hp i)
      (laxColimHasBinaryProducts L hL pData) := by
  letI : Cat (Obj L) := laxColimCat L hL
  letI : HasBinaryProducts (Obj L) := laxColimHasBinaryProducts L hL pData
  intro A B
  exact Colim.isIso_of_product_up (𝒞 := Obj L) (stageInclL L hL (pData.hp i).fst)
    (stageInclL L hL (pData.hp i).snd)
    (fun {Z} f g => stageInclL_product_up L hL pData i A B f g)

/-! ### `stageInclFunctorL` preserves equalizers

  Mirror of the product development.  For a stage-`i` parallel pair `f g : x ⟶ y`, the `F`-image of
  the fibre equalizer `(⟨i, eqObj f g⟩, stageInclL (eqMap f g))` has the equalizer universal property
  in the colimit: existence of the mediator uses `eqData.presLift` (push the competitor to a common
  stage, lift there); joint monicity / uniqueness is `eqMono` specialized to the same stage. -/

/-- Universal property of the `F`-image equalizer cone `(⟨i, eqObj f g⟩, stageInclL (eqMap f g))`
    for the stage-`i` parallel pair `f, g`.  A competitor `c : Z ⟶ ⟨i,x⟩` equalizing `stageInclL f`
    and `stageInclL g` factors uniquely through `stageInclL (eqMap f g)`. -/
public theorem stageInclL_equalizer_up (eqData : LaxEqualizerData L) (i : ι) {x y : L.A i}
    (f g : x ⟶ y) {Z : Obj L}
    (c : homL L hL Z ⟨i, x⟩)
    (hc : compL L hL c (stageInclL L hL f) = compL L hL c (stageInclL L hL g)) :
    letI : HasEqualizers (L.A i) := eqData.he i
    letI : Cat (Obj L) := laxColimCat L hL
    ∃ u : Z ⟶ (⟨i, eqObj f g⟩ : Obj L),
      u ≫ stageInclL L hL (eqMap f g) = c ∧
      ∀ v : Z ⟶ (⟨i, eqObj f g⟩ : Obj L),
        v ≫ stageInclL L hL (eqMap f g) = c → v = u := by
  letI : HasEqualizers (L.A i) := eqData.he i
  letI : Cat (Obj L) := laxColimCat L hL
  obtain ⟨lz, z⟩ := Z
  let Eobj : L.A i := eqObj f g
  -- the equalizer projection germ, as `homInclL` of `reflApp Eobj ≫ (eqMap f g ≫ isoInv (reflApp x))`.
  let projE : Eobj ⟶ L.F (D.refl i) x := eqMap f g ≫ isoInv (reflApp_isIso L x)
  have hmap_eq : stageInclL L hL (eqMap f g)
      = homInclL L hL Eobj x ⟨i, D.refl i, D.refl i⟩ (reflApp L Eobj ≫ projE) := rfl
  -- ===== Monicity of the equalizer projection at apex `⟨i,Eobj⟩` (uniqueness ingredient). =====
  have hjm : ∀ h₁ h₂ : homL L hL ⟨lz, z⟩ ⟨i, Eobj⟩,
      compL L hL h₁ (stageInclL L hL (eqMap f g))
        = compL L hL h₂ (stageInclL L hL (eqMap f g)) →
      h₁ = h₂ := by
    intro h₁ h₂ he
    rw [hmap_eq] at he
    let hik : D.le i i := D.refl i
    revert he
    refine Quotient.inductionOn₂ h₁ h₂ (fun rh₁ rh₂ he => ?_)
    obtain ⟨a₁, m₁⟩ := rh₁
    obtain ⟨a₂, m₂⟩ := rh₂
    -- common bound `e ≥ a₁.1, a₂.1, i`.
    obtain ⟨w0, hw0a, hw0b⟩ := D.bound a₁.1 a₂.1
    obtain ⟨e, hew, hek⟩ := D.bound w0 i
    have ha₁e : D.le a₁.1 e := D.trans hw0a hew
    have ha₂e : D.le a₂.1 e := D.trans hw0b hew
    rw [prCompProj L hL z Eobj x hik projE a₁ m₁ e ha₁e hek,
        prCompProj L hL z Eobj x hik projE a₂ m₂ e ha₂e hek] at he
    obtain ⟨c0, hc1, hc2, eqe⟩ := Quotient.exact he
    simp only [homSystemL] at eqe
    rw [prPsi_push L hL z Eobj x hik projE a₁ m₁ e c0.1 ha₁e hek hc1,
        prPsi_push L hL z Eobj x hik projE a₂ m₂ e c0.1 ha₂e hek hc2] at eqe
    unfold prPsi at eqe
    rw [pushHom_proj L x Eobj hik _ projE] at eqe
    let N := c0.1
    have hkn : D.le i N := D.trans hek hc1
    have ha₁n : D.le a₁.1 N := D.trans ha₁e hc1
    have ha₂n : D.le a₂.1 N := D.trans ha₂e hc1
    let u₁ : L.F (D.trans a₁.2.1 ha₁n) z ⟶ L.F hkn Eobj :=
      pushHom L z Eobj a₁.2.1 a₁.2.2 ha₁n m₁ ≫ prUnit L Eobj hkn
    let u₂ : L.F (D.trans a₂.2.1 ha₂n) z ⟶ L.F hkn Eobj :=
      pushHom L z Eobj a₂.2.1 a₂.2.2 ha₂n m₂ ≫ prUnit L Eobj hkn
    -- strip the trailing `isoInv (transApp)` AND the trailing `map (isoInv reflApp)` (from `projE`).
    have hproj : (L.functF hkn).map (eqMap f g ≫ isoInv (reflApp_isIso L x))
            ≫ isoInv (transApp_isIso L hik hkn x) ≫ transApp L hik hkn x
              ≫ (L.functF hkn).map (reflApp L x)
          = (L.functF hkn).map (eqMap f g) := by
      rw [← Cat.assoc (isoInv (transApp_isIso L hik hkn x)), inv_isoInv_comp, Cat.id_comp,
          (L.functF hkn).map_comp (eqMap f g) (isoInv (reflApp_isIso L x)),
          Cat.assoc, ← (L.functF hkn).map_comp (isoInv (reflApp_isIso L x)) (reflApp L x),
          inv_isoInv_comp,
          (L.functF hkn).map_id,
          Cat.comp_id]
    have hmapeq : u₁ ≫ (L.functF hkn).map (eqMap f g)
        = u₂ ≫ (L.functF hkn).map (eqMap f g) := by
      have := congrArg (· ≫ transApp L hik hkn x ≫ (L.functF hkn).map (reflApp L x)) eqe
      simp only [projE, Cat.assoc] at this ⊢
      rw [hproj] at this
      simpa only [u₁, u₂, Cat.assoc] using this
    have huv : u₁ = u₂ :=
      eqData.pres hkn f g (L.F (D.trans a₁.2.1 ha₁n) z) u₁ u₂ hmapeq
    have hmm : pushHom L z Eobj a₁.2.1 a₁.2.2 ha₁n m₁ = pushHom L z Eobj a₂.2.1 a₂.2.2 ha₂n m₂ := by
      have h2 := congrArg (· ≫ isoInv (prUnit_isIso L Eobj hkn)) huv
      simpa only [u₁, u₂, Cat.assoc, isoInv_comp, Cat.comp_id] using h2
    exact Quotient.sound ⟨⟨N, D.trans a₁.2.1 ha₁n, hkn⟩, ha₁n, ha₂n, hmm⟩
  -- ===== EXISTENCE: build the mediator via `eqData.presLift` at the working stage `N = q.1`. =====
  refine Quotient.inductionOn c (fun rc => ?_) hc
  clear hc
  intro hc
  obtain ⟨ac, cc⟩ := rc
  -- `compStage`: composing the competitor germ with `stageInclL m` reduces, at any stage `P ≥ ac.1,i`,
  -- to the single germ `prPsi` of `reflApp x ≫ (m ≫ isoInv reflApp)` (the `stageInclL m` proj germ).
  have compStage : ∀ (m : x ⟶ y) (P : ι) (haP : D.le ac.1 P) (hiP : D.le i P),
      @compL _ _ L hL ⟨lz, z⟩ ⟨i, x⟩ ⟨i, y⟩ (Quotient.mk _ ⟨ac, cc⟩) (stageInclL L hL m)
        = homInclL L hL z y ⟨P, D.trans ac.2.1 haP, D.trans (D.refl i) hiP⟩
            (prPsi L z x y (D.refl i) (m ≫ isoInv (reflApp_isIso L y)) ac cc P haP hiP) := by
    intro m P haP hiP
    exact prCompProj L hL z x y (D.refl i) (m ≫ isoInv (reflApp_isIso L y)) ac cc P haP hiP
  -- first common bound `N0 ≥ ac.1, i`; reduce `hc` to germ equality, extract the working stage `N`.
  obtain ⟨N0, haN0, hiN0⟩ := D.bound ac.1 i
  rw [compStage f N0 haN0 hiN0, compStage g N0 haN0 hiN0] at hc
  obtain ⟨q, hqN, _, qe⟩ := Quotient.exact hc
  simp only [homSystemL] at qe
  -- working stage `N := q.1 ≥ N0`.
  let N : ι := q.1
  have hN0N : D.le N0 N := hqN
  have haN : D.le ac.1 N := D.trans haN0 hN0N
  have hiN : D.le i N := D.trans hiN0 hN0N
  have hlN : D.le lz N := D.trans ac.2.1 haN
  -- push both `prPsi` reps from `N0` to `N` (`prPsi_push`), unfold to two `pushHom`s, refold `proj`.
  rw [prPsi_push L hL z x y (D.refl i) (f ≫ isoInv (reflApp_isIso L y)) ac cc N0 N haN0 hiN0 hN0N,
      prPsi_push L hL z x y (D.refl i) (g ≫ isoInv (reflApp_isIso L y)) ac cc N0 N haN0 hiN0 hN0N] at qe
  unfold prPsi at qe
  rw [pushHom_proj L y x (D.refl i) hiN (f ≫ isoInv (reflApp_isIso L y)),
      pushHom_proj L y x (D.refl i) hiN (g ≫ isoInv (reflApp_isIso L y))] at qe
  -- `cN` is the pushed competitor with target converted to `F hiN x` via `transApp ≫ map reflApp`.
  let cN : L.F hlN z ⟶ L.F hiN x :=
    pushHom L z x ac.2.1 ac.2.2 haN cc ≫ prUnit L x hiN
  -- strip the trailing `map(isoInv reflApp) ≫ isoInv transApp` on both sides of `qe`, giving `hcN`.
  have hstrip : ∀ (m : x ⟶ y),
      cN ≫ (L.functF hiN).map m
        = pushHom L z x ac.2.1 ac.2.2 haN cc ≫ prUnit L x hiN
            ≫ (L.functF hiN).map (m ≫ isoInv (reflApp_isIso L y))
              ≫ isoInv (transApp_isIso L (D.refl i) hiN y)
              ≫ transApp L (D.refl i) hiN y ≫ (L.functF hiN).map (reflApp L y) := by
    intro m
    rw [← Cat.assoc (isoInv (transApp_isIso L (D.refl i) hiN y)), inv_isoInv_comp, Cat.id_comp,
        (L.functF hiN).map_comp m (isoInv (reflApp_isIso L y))]
    rw [Cat.assoc ((L.functF hiN).map m),
        ← (L.functF hiN).map_comp (isoInv (reflApp_isIso L y)) (reflApp L y),
        inv_isoInv_comp,
        (L.functF hiN).map_id,
        Cat.comp_id]
    simp only [cN, Cat.assoc]
  have hcN : cN ≫ (L.functF hiN).map f = cN ≫ (L.functF hiN).map g := by
    have := congrArg (· ≫ transApp L (D.refl i) hiN y ≫ (L.functF hiN).map (reflApp L y)) qe
    simp only [Cat.assoc] at this
    rw [hstrip f, hstrip g]
    simpa only [Cat.assoc] using this
  -- equalizer lift at stage `N`.
  obtain ⟨r, hr⟩ := eqData.presLift hiN f g (L.F hlN z) cN hcN
  -- the lift germ and its `lift ≫ m = c` fact (`prUnit`-cancellation, as the product `leg`).
  have hLiftEq : @compL _ _ L hL ⟨lz, z⟩ ⟨i, Eobj⟩ ⟨i, x⟩
        (homInclL L hL z Eobj ⟨N, hlN, hiN⟩ (r ≫ isoInv (prUnit_isIso L Eobj hiN)))
        (homInclL L hL Eobj x ⟨i, D.refl i, D.refl i⟩ (reflApp L Eobj ≫ projE))
      = Quotient.mk (setoid (homSystemL L hL z x)) ⟨ac, cc⟩ := by
    show homCompRawL L hL z Eobj x ⟨N, hlN, hiN⟩ (r ≫ isoInv (prUnit_isIso L Eobj hiN))
        ⟨i, D.refl i, D.refl i⟩ (reflApp L Eobj ≫ projE) = homInclL L hL z x ac cc
    rw [homCompRawL_eq_compAtL L hL z Eobj x ⟨N, hlN, hiN⟩ (r ≫ isoInv (prUnit_isIso L Eobj hiN))
          ⟨i, D.refl i, D.refl i⟩ (reflApp L Eobj ≫ projE) N (D.refl N) hiN]
    unfold compAtL
    rw [hL.push_refl z Eobj hlN hiN (r ≫ isoInv (prUnit_isIso L Eobj hiN)),
        pushHom_proj L x Eobj (D.refl i) hiN projE]
    -- cancel `isoInv prUnit ≫ prUnit = id`.
    rw [Cat.assoc, ← Cat.assoc (isoInv (prUnit_isIso L Eobj hiN)),
        inv_isoInv_comp, Cat.id_comp]
    -- distribute `map (eqMap ≫ isoInv reflApp)` and use `hr` to substitute `r ≫ map eqMap`.
    rw [show projE = eqMap f g ≫ isoInv (reflApp_isIso L x) from rfl,
        (L.functF hiN).map_comp (eqMap f g) (isoInv (reflApp_isIso L x)), ← Cat.assoc, ← Cat.assoc r, hr]
    -- now `cN ≫ map(isoInv reflApp) ≫ isoInv transApp`; unfold cN and cancel the units.
    simp only [cN, prUnit, Cat.assoc, ← Functor.map_comp, isoInv_comp, Functor.map_id]
    rw [show 𝟙 ((L.functF hiN).obj (L.F (D.refl i) x)) = 𝟙 (L.F hiN (L.F (D.refl i) x))
      from rfl, Cat.id_comp, isoInv_comp, Cat.comp_id]
    exact homInclL_compat L hL z x (a := ac)
      (b := ⟨N, D.trans ac.2.1 haN, D.trans ac.2.2 haN⟩) haN cc
  refine ⟨homInclL L hL z Eobj ⟨N, hlN, hiN⟩ (r ≫ isoInv (prUnit_isIso L Eobj hiN)), ?_, ?_⟩
  · rw [hmap_eq]; exact hLiftEq
  · intro v hv
    apply hjm
    rw [show compL L hL v (stageInclL L hL (eqMap f g)) = _ from hv, ← hLiftEq, hmap_eq]

/-- **`stageInclFunctorL i` preserves equalizers** (for the colimit's `laxColimHasEqualizers`).  The
    `F`-image of the fibre equalizer cone is an equalizer in the colimit (`stageInclL_equalizer_up`),
    so the canonical comparison to the chosen colimit equalizer is iso (`isIso_of_two_equalizers`). -/
public theorem stageInclFunctorL_preservesEqualizers (eqData : LaxEqualizerData L) (i : ι) :
    @PreservesEqualizers (L.A i) (Obj L) (L.catA i) (laxColimCat L hL)
      (stageInclFunctorL L hL i) (eqData.he i)
      (laxColimHasEqualizers L hL eqData) := by
  letI : Cat (Obj L) := laxColimCat L hL
  letI hEq : HasEqualizers (Obj L) := laxColimHasEqualizers L hL eqData
  letI : HasEqualizers (L.A i) := eqData.he i
  intro x y f g
  -- the `F`-image equalizer cone is an equalizer in the colimit.
  have hFeqMap_eq :
      @compL _ _ L hL ⟨i, eqObj f g⟩ ⟨i, x⟩ ⟨i, y⟩ (stageInclL L hL (eqMap f g)) (stageInclL L hL f)
      = @compL _ _ L hL ⟨i, eqObj f g⟩ ⟨i, x⟩ ⟨i, y⟩ (stageInclL L hL (eqMap f g)) (stageInclL L hL g) := by
    rw [← stageInclL_comp L hL (eqMap f g) f, ← stageInclL_comp L hL (eqMap f g) g, eqMap_eq f g]
  have hFeq_isEq :
      (EqualizerCone.mk (f := stageInclL L hL f) (g := stageInclL L hL g)
        (⟨i, eqObj f g⟩ : Obj L) (stageInclL L hL (eqMap f g)) hFeqMap_eq).IsEqualizer := by
    intro d
    obtain ⟨u, hu, huniq⟩ := stageInclL_equalizer_up L hL eqData i f g d.map d.eq
    exact ⟨u, hu, huniq⟩
  -- the canonical comparison to the chosen colimit equalizer is iso.
  refine isIso_of_two_equalizers (c := EqualizerCone.mk _ _ hFeqMap_eq)
    (d := EqualizerCone.mk (@eqObj (Obj L) _ hEq _ _ (stageInclL L hL f) (stageInclL L hL g))
      (@eqMap (Obj L) _ hEq _ _ (stageInclL L hL f) (stageInclL L hL g))
      (@eqMap_eq (Obj L) _ hEq _ _ (stageInclL L hL f) (stageInclL L hL g)))
    hFeq_isEq (@chosenEqualizer_isEqualizer (Obj L) _ hEq _ _
      (stageInclL L hL f) (stageInclL L hL g)) _ ?_
  exact @eqLift_fac (Obj L) _ hEq _ _ _ (stageInclL L hL f) (stageInclL L hL g)
    (stageInclL L hL (eqMap f g)) hFeqMap_eq

/-! ### `stageInclFunctorL` sends chosen pullbacks to pullbacks

  Combining the product- and equalizer-preservation above with the generic §1.45 machinery
  (`image_chosenPullback_isPullback'`), the stage-`i` chosen pullback of any cospan `f g` in `L.A i`
  maps under `stageInclFunctorL` to a pullback cone in the colimit. -/

/-- **`stageInclFunctorL i` sends the §1.432 chosen pullback to a pullback cone in the colimit.**  For
    a cospan `f : A ⟶ C`, `g : B ⟶ C` in `L.A i`, the image under `stageInclFunctorL` of the chosen
    pullback cone of `f, g` is a pullback of `stageInclL f`, `stageInclL g` in the colimit. -/
public theorem stageInclFunctorL_preservesPullbacks [Nonempty ι]
    (tData : LaxTerminalData L) (pData : LaxProductData L) (eqData : LaxEqualizerData L) (i : ι)
    {A B C : L.A i} (f : A ⟶ C) (g : B ⟶ C) :
    letI : HasTerminal (L.A i) := tData.ht i
    letI : HasBinaryProducts (L.A i) := pData.hp i
    letI : HasEqualizers (L.A i) := eqData.he i
    letI : Cat (Obj L) := laxColimCat L hL
    letI : HasTerminal (Obj L) := laxColimHasTerminal L hL tData
    letI : HasBinaryProducts (Obj L) := laxColimHasBinaryProducts L hL pData
    letI : HasEqualizers (Obj L) := laxColimHasEqualizers L hL eqData
    (Cone.mk (f := stageInclL L hL f) (g := stageInclL L hL g)
      ((⟨i, (products_equalizers_implies_pullbacks f g).cone.pt⟩ : Obj L))
      (stageInclL L hL (products_equalizers_implies_pullbacks f g).cone.π₁)
      (stageInclL L hL (products_equalizers_implies_pullbacks f g).cone.π₂)
      ((stageInclL_comp L hL _ f).symm.trans
        ((congrArg (stageInclL L hL ·) (products_equalizers_implies_pullbacks f g).cone.w).trans
          (stageInclL_comp L hL _ g)))).IsPullback := by
  letI : HasTerminal (L.A i) := tData.ht i
  letI : HasBinaryProducts (L.A i) := pData.hp i
  letI : HasEqualizers (L.A i) := eqData.he i
  letI : Cat (Obj L) := laxColimCat L hL
  letI : HasTerminal (Obj L) := laxColimHasTerminal L hL tData
  letI : HasBinaryProducts (Obj L) := laxColimHasBinaryProducts L hL pData
  letI : HasEqualizers (Obj L) := laxColimHasEqualizers L hL eqData
  exact image_chosenPullback_isPullback' (𝒞 := L.A i) (𝒟 := Obj L)
    (stageInclFunctorL L hL i)
    (stageInclFunctorL_preservesProducts L hL pData i)
    (stageInclFunctorL_preservesEqualizers L hL eqData i) f g

/-- **`stageInclFunctorL i` is faithful** (injective on hom-sets), given transition faithfulness
    `hfaith`.  `stageInclL g = stageInclL g'` is an equality of reflexive-bound germs, which
    `homInclL_injective` reduces to `reflApp ≫ g ≫ isoInv = reflApp ≫ g' ≫ isoInv`; cancelling the
    flanking isos `reflApp` gives `g = g'`.  Lax `objIncl_faithful` (embedding part). -/
public theorem stageInclFunctorL_faithful
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        (L.functF hij).map p
          = (L.functF hij).map q → p = q)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (φ : x ⟶ y),
        IsIso ((L.functF hij).map φ) → IsIso φ)
    (i : ι) :
    @Faithful (L.A i) (L.catA i) (Obj L) (laxColimCat L hL)
      (stageInclFunctorL L hL i) := by
  letI : Cat (Obj L) := laxColimCat L hL
  refine ⟨?_, ?_⟩
  · -- Embedding: `stageInclL` injective on hom-sets.
    intro x y g g' hgg'
    -- `stageInclFunctorL.map g = stageInclL g`; unfold to germ equality and strip via injectivity.
    have hgg'' : stageInclL L hL g = stageInclL L hL g' := hgg'
    unfold stageInclL at hgg''
    have hstrip := homInclL_injective L hL hfaith x y ⟨i, D.refl i, D.refl i⟩ hgg''
    -- `reflApp x ≫ g ≫ isoInv = reflApp x ≫ g' ≫ isoInv`; cancel iso `reflApp x` then `isoInv`.
    obtain ⟨rinv, hr1, hr2⟩ := reflApp_isIso L x
    have h2 := congrArg (fun t => rinv ≫ t) hstrip
    simp only [← Cat.assoc, hr2, Cat.id_comp] at h2
    -- now `g ≫ isoInv = g' ≫ isoInv`; cancel the iso `isoInv (reflApp y)`.
    have h3 := congrArg (fun t => t ≫ reflApp L y) h2
    simp only [Cat.assoc, inv_isoInv_comp, Cat.comp_id] at h3
    exact h3
  · -- reflects-iso: `IsIso (stageInclL g) → IsIso g`, via stage iso reflection + conservativity.
    intro x y g hiso
    have hiso' : @IsIso (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨i, y⟩
        (homInclL L hL x y ⟨i, D.refl i, D.refl i⟩
          (reflApp L x ≫ g ≫ isoInv (reflApp_isIso L y))) := hiso
    obtain ⟨e, hae, hpiso⟩ := homInclL_isIso_reflects L hL x y ⟨i, D.refl i, D.refl i⟩
      (reflApp L x ≫ g ≫ isoInv (reflApp_isIso L y)) hiso'
    apply hcons hae
    -- `pushHom gᵣ = transApp ≫ (map gᵣ) ≫ isoInv transApp`; un-conjugate by the two isos.
    have hi1 : IsIso (transApp L (D.refl i) hae x) := transApp_isIso L (D.refl i) hae x
    have hi1' : IsIso (isoInv (transApp_isIso L (D.refl i) hae y)) :=
      ⟨transApp L (D.refl i) hae y, inv_isoInv_comp _, isoInv_comp _⟩
    have hmapr : IsIso ((L.functF hae).map
        (reflApp L x ≫ g ≫ isoInv (reflApp_isIso L y))) := by
      have := hpiso; unfold pushHom at this
      exact isIso_unconj hi1 hi1' this
    -- `map gᵣ = (map reflApp x) ≫ (map g) ≫ (map isoInv)`; un-conjugate again.
    rw [(L.functF hae).map_comp (reflApp L x)
          (g ≫ isoInv (reflApp_isIso L y)),
        (L.functF hae).map_comp g (isoInv (reflApp_isIso L y))] at hmapr
    have hi2 : IsIso ((L.functF hae).map (reflApp L x)) :=
      functor_preserves_iso (F := L.functF hae) (reflApp L x) (reflApp_isIso L x)
    have hi3 : IsIso ((L.functF hae).map (isoInv (reflApp_isIso L y))) :=
      functor_preserves_iso (F := L.functF hae) (isoInv (reflApp_isIso L y))
        ⟨reflApp L y, inv_isoInv_comp _, isoInv_comp _⟩
    exact isIso_unconj hi2 hi3 hmapr

/-- **`stageInclFunctorL i` preserves monos.**  A stage mono `φ` includes to a colimit mono: at the
    reflexive bound `stageInclL φ = homInclL … (reflApp ≫ φ ≫ isoInv)`, and `homInclL_mono_of_stage`
    reduces colimit monicity to per-transition left-cancellability of the pushed germ, where the
    pushed `φ` is `(functF).map φ` (mono by `hmono`) flanked by isos.  Standalone form of the
    `hM_mono` block inside `homInclL_cover_reflects`. -/
public theorem stageInclFunctorL_preservesMono
    (hmono : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (φ : x ⟶ y),
        Monic φ → Monic ((L.functF hij).map φ))
    {i : ι} {x y : L.A i} (φ : x ⟶ y) (hφ : Monic φ) :
    @Monic (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨i, y⟩ (stageInclL L hL φ) := by exact stageInclL_mono_of_stage L hL (fun {i j} hij {x y} {f} hf => hmono hij f hf) φ hφ

/-- **`stageInclFunctorL i` preserves covers.**  A stage cover `φ` includes to a colimit cover: at the
    reflexive bound `stageInclL φ = homInclL … (reflApp ≫ φ ≫ isoInv)`, and `homInclL_cover_of_stage`
    turns a per-transition cover (`hcovpres φ` keeps `(functF).map φ` a cover) into a colimit cover.
    Wrapper of `homInclL_cover_of_stage` at the reflexive bound. -/
public theorem stageInclFunctorL_preservesCover
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        (L.functF hij).map p
          = (L.functF hij).map q → p = q)
    (hcovpres : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (φ : x ⟶ y),
        Cover φ → Cover ((L.functF hij).map φ))
    {i : ι} {x y : L.A i} (φ : x ⟶ y) (hφ : Cover φ) :
    @Cover (Obj L) (laxColimCat L hL) ⟨i, x⟩ ⟨i, y⟩ (stageInclL L hL φ) := by
  unfold stageInclL
  apply homInclL_cover_of_stage L hL hfaith x y φ
  intro e hie
  exact hcovpres hie φ hφ

/-! ## Generic `hcanon` discharge for the lax colimit

  Mirrors the strict `Colim.colimitCanonicalCover` assembly (CatColimitRegular ~2200-2410, import-
  banned).  Given the lax colimit has pullbacks, the canonical pullback's `π₂` of a cospan `(f,g)`
  with `f` a cover is itself a cover.  Assembled from the stage-inclusion toolkit:
  align the cospan to a single fibre (`colimHom_cospan_as_stageInclL`), reflect the cover to the
  fibre (`homInclL_cover_reflects`), apply the fibre's `PullbacksTransferCovers`, push the fibre
  pullback to the colimit (`stageInclFunctorL_preservesPullbacks`), preserve the cover
  (`homInclL_cover_of_stage`), and transfer back across the realignment isos
  (`canonicalPullbackL_cover_of_witness`). -/

/-- Any two pullback cones of the same cospan are connected by a unique compatible iso (generic;
    local copy of `Colim.pullback_comparison_iso`, which lives in the import-banned strict file;
    `LaxColimitPreReg.pullbackComparisonIso` is `private` so re-derived here). -/
private theorem pullbackComparisonIsoL {𝒜 : Type w} [Cat.{w} 𝒜] {A B Z : 𝒜}
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

/-- **Cover of the canonical pullback's `π₂` from *any* witnessing pullback cone** (generic, lax
    copy of `Colim.canonicalPullback_cover_of_witness`).  Reduces `hcanon` to: exhibit one pullback
    cone of `(f,g)` whose `π₂` is a cover. -/
public theorem canonicalPullbackL_cover_of_witness {𝒜 : Type w} [Cat.{w} 𝒜] [HasPullbacks 𝒜]
    {A B Z : 𝒜} (f : A ⟶ Z) (g : B ⟶ Z)
    (c : Cone f g) (hc : c.IsPullback) (hcov : Cover c.π₂) :
    Cover (HasPullbacks.has f g).cone.π₂ := by
  obtain ⟨φ, hφiso, _, hφ2⟩ := pullbackComparisonIsoL (HasPullbacks.has f g).cone_isPullback hc
  rw [← hφ2]
  exact cover_precomp_iso hφiso hcov

/-- **Pullback transfer along an iso re-coordinatization of a cospan** (generic, reusable in any
    `[Cat]`).  Given a cospan `(f,g)` with `f : A ⟶ Z`, `g : B ⟶ Z` whose legs factor through isos
    `eA : A ⟶ A'`, `eB : B ⟶ B'`, `eZinv : Z' ⟶ Z` as `f = eA ≫ f' ≫ eZinv`, `g = eB ≫ g' ≫ eZinv`,
    a pullback cone `c'` of the re-coordinatized cospan `(f', g')` transfers to a pullback cone of
    `(f,g)` with `π₁ = c'.π₁ ≫ eA⁻¹`, `π₂ = c'.π₂ ≫ eB⁻¹` (same apex).  Used to push the fibre
    pullback back onto the original colimit cospan. -/
public theorem cospanIsoTransferPullback {𝒜 : Type w} [Cat.{w} 𝒜]
    {A B Z A' B' Z' : 𝒜} {f : A ⟶ Z} {g : B ⟶ Z} {f' : A' ⟶ Z'} {g' : B' ⟶ Z'}
    {eA : A ⟶ A'} {eB : B ⟶ B'} {eZinv : Z' ⟶ Z}
    (hAiso : IsIso eA) (hBiso : IsIso eB) (hZiso : IsIso eZinv)
    (hf : f = eA ≫ f' ≫ eZinv) (hg : g = eB ≫ g' ≫ eZinv)
    (c' : Cone f' g') (hc' : c'.IsPullback) (hcov : Cover c'.π₂) :
    ∃ c : Cone f g, c.IsPullback ∧ Cover c.π₂ := by
  -- the transferred cone: π₁ := c'.π₁ ≫ eA⁻¹, π₂ := c'.π₂ ≫ eB⁻¹.
  have hw : (c'.π₁ ≫ isoInv hAiso) ≫ f = (c'.π₂ ≫ isoInv hBiso) ≫ g := by
    rw [hf, hg]
    -- `(c'.π₁ ≫ eA⁻¹) ≫ (eA ≫ f' ≫ eZinv) = c'.π₁ ≫ f' ≫ eZinv`, ditto for g; use c'.w.
    rw [Cat.assoc, ← Cat.assoc (isoInv hAiso), inv_isoInv_comp, Cat.id_comp,
        Cat.assoc, ← Cat.assoc (isoInv hBiso), inv_isoInv_comp, Cat.id_comp,
        ← Cat.assoc c'.π₁, ← Cat.assoc c'.π₂, c'.w]
  -- the leg-cancellation facts `eA ≫ f' = f ≫ eZinv⁻¹`, `eB ≫ g' = g ≫ eZinv⁻¹`.
  have hAf : eA ≫ f' = f ≫ isoInv hZiso := by
    rw [hf, Cat.assoc, Cat.assoc, isoInv_comp, Cat.comp_id]
  have hBg : eB ≫ g' = g ≫ isoInv hZiso := by
    rw [hg, Cat.assoc, Cat.assoc, isoInv_comp, Cat.comp_id]
  let c : Cone f g := ⟨c'.pt, c'.π₁ ≫ isoInv hAiso, c'.π₂ ≫ isoInv hBiso, hw⟩
  refine ⟨c, ?_, cover_comp_iso_cat hcov ⟨eB, inv_isoInv_comp hBiso, isoInv_comp hBiso⟩⟩
  -- universal property: a competitor `d` of `(f,g)` becomes a competitor of `(f',g')` by
  -- post-composing the legs with `eA, eB` (`hAf`/`hBg` + `d.w`); lift through `c'`.
  show c.IsPullback
  intro d
  have hd' : (d.π₁ ≫ eA) ≫ f' = (d.π₂ ≫ eB) ≫ g' := by
    rw [Cat.assoc, hAf, Cat.assoc, hBg, ← Cat.assoc d.π₁, ← Cat.assoc d.π₂, d.w]
  obtain ⟨u, ⟨hu1, hu2⟩, huuniq⟩ := hc' ⟨d.pt, d.π₁ ≫ eA, d.π₂ ≫ eB, hd'⟩
  refine ⟨u, ⟨?_, ?_⟩, ?_⟩
  · -- u ≫ (c'.π₁ ≫ eA⁻¹) = d.π₁ : use hu1 : u ≫ c'.π₁ = d.π₁ ≫ eA, cancel eA.
    show u ≫ c'.π₁ ≫ isoInv hAiso = d.π₁
    rw [← Cat.assoc, hu1, Cat.assoc, isoInv_comp, Cat.comp_id]
  · show u ≫ c'.π₂ ≫ isoInv hBiso = d.π₂
    rw [← Cat.assoc, hu2, Cat.assoc, isoInv_comp, Cat.comp_id]
  · -- uniqueness: a `v` with the transferred fac is a competitor lift for the `(f',g')` problem.
    intro v hv1 hv2
    apply huuniq
    · -- v ≫ c'.π₁ = d.π₁ ≫ eA : from hv1 : v ≫ (c'.π₁ ≫ eA⁻¹) = d.π₁, post-compose eA.
      show v ≫ c'.π₁ = d.π₁ ≫ eA
      have h : (v ≫ c'.π₁ ≫ isoInv hAiso) ≫ eA = d.π₁ ≫ eA := congrArg (fun t => t ≫ eA) hv1
      rwa [Cat.assoc, Cat.assoc, inv_isoInv_comp, Cat.comp_id] at h
    · show v ≫ c'.π₂ = d.π₂ ≫ eB
      have h : (v ≫ c'.π₂ ≫ isoInv hBiso) ≫ eB = d.π₂ ≫ eB := congrArg (fun t => t ≫ eB) hv2
      rwa [Cat.assoc, Cat.assoc, inv_isoInv_comp, Cat.comp_id] at h

/-- `alignGermInv` is an iso (inverse realignment `⟨e, F x⟩ ⟶ ⟨i,x⟩`).  Mirror of `alignGerm_isIso`
    with the two round-trip reps (`reflApp`/`isoInv reflApp`) swapped. -/
public theorem alignGermInv_isIso {i : ι} (x : L.A i) {e : ι} (hie : D.le i e) :
    @IsIso (Obj L) (laxColimCat L hL) ⟨e, L.F hie x⟩ ⟨i, x⟩ (alignGermInv L hL x hie) := by
  unfold alignGermInv
  refine homInclL_isIso_of_rep L hL (L.F hie x) x ⟨e, D.refl e, hie⟩
    (reflApp L (L.F hie x)) (isoInv (reflApp_isIso L (L.F hie x))) ?_ ?_
  · exact isoInv_comp (reflApp_isIso L (L.F hie x))
  · exact inv_isoInv_comp (reflApp_isIso L (L.F hie x))

/-- **Lax cospan alignment.**  A cospan `f : A ⟶ Z`, `g : B ⟶ Z` in `laxColimCat` is, after
    identifying `A, B, Z` with stage objects via realignment isos, the stage inclusion of a genuine
    single-fibre cospan `fN : xA ⟶ xZ`, `gN : xB ⟶ xZ` in one `L.A N` (sharing the codomain object
    `xZ`).  Each leg factors as `alignGerm ⊚ stageInclL · ⊚ alignGermInv` (`homInclL_factor`), so the
    realignment isos `alignGerm xA`, `alignGerm xB`, `alignGerm xZ` identify the stage objects with
    `A, B, Z`; the SHARED codomain rep `xZ` is the common bound `U ≥ a.1, b.1` push of `Z`'s rep.
    Lax analogue of the strict `colimHom_cospan_as_homInclObj`. -/
public theorem colimHom_cospan_as_stageInclL {A B Z : Obj L}
    (f : @homL _ _ L hL A Z) (g : @homL _ _ L hL B Z) :
    ∃ (N : ι) (xA xB xZ : L.A N) (fN : xA ⟶ xZ) (gN : xB ⟶ xZ)
      (eA : @homL _ _ L hL A ⟨N, xA⟩) (eB : @homL _ _ L hL B ⟨N, xB⟩)
      (eZinv : @homL _ _ L hL ⟨N, xZ⟩ Z),
      @IsIso (Obj L) (laxColimCat L hL) A ⟨N, xA⟩ eA ∧
      @IsIso (Obj L) (laxColimCat L hL) B ⟨N, xB⟩ eB ∧
      @IsIso (Obj L) (laxColimCat L hL) ⟨N, xZ⟩ Z eZinv ∧
      f = @compL _ _ L hL A ⟨N, xA⟩ Z eA
            (@compL _ _ L hL ⟨N, xA⟩ ⟨N, xZ⟩ Z (stageInclL L hL fN) eZinv) ∧
      g = @compL _ _ L hL B ⟨N, xB⟩ Z eB
            (@compL _ _ L hL ⟨N, xB⟩ ⟨N, xZ⟩ Z (stageInclL L hL gN) eZinv) := by
  letI : Cat (Obj L) := laxColimCat L hL
  obtain ⟨ia, xa⟩ := A
  obtain ⟨ib, xb⟩ := B
  obtain ⟨iz, xz⟩ := Z
  -- representatives of `f, g` at bounds `a, b`
  obtain ⟨a, f₀, hf₀⟩ := incl_surjective (homSystemL L hL xa xz) f
  obtain ⟨b, g₀, hg₀⟩ := incl_surjective (homSystemL L hL xb xz) g
  -- common stage `U ≥ a.1, b.1`
  obtain ⟨U, haU, hbU⟩ := D.bound a.1 b.1
  refine ⟨U, L.F (D.trans a.2.1 haU) xa, L.F (D.trans b.2.1 hbU) xb, L.F (D.trans a.2.2 haU) xz,
    pushHom L xa xz a.2.1 a.2.2 haU f₀, pushHom L xb xz b.2.1 b.2.2 hbU g₀,
    alignGerm L hL xa (D.trans a.2.1 haU), alignGerm L hL xb (D.trans b.2.1 hbU),
    alignGermInv L hL xz (D.trans a.2.2 haU), ?_, ?_, ?_, ?_, ?_⟩
  · exact alignGerm_isIso L hL xa (D.trans a.2.1 haU)
  · exact alignGerm_isIso L hL xb (D.trans b.2.1 hbU)
  · exact alignGermInv_isIso L hL xz (D.trans a.2.2 haU)
  · -- `f = homInclL xa xz a f₀` (from `hf₀`), then `homInclL_factor` at bound `U`.
    rw [← hf₀]; exact homInclL_factor L hL xa xz a f₀ haU
  · rw [← hg₀]; exact homInclL_factor L hL xb xz b g₀ hbU

/-- **Generic `hcanon` discharge for the lax colimit.**  Given that each transition is conservative
    (`hcons`) and mono-preserving (`hmono`) and faithful (`hfaith`), that each transition preserves
    covers (`hcovpres`), and that each fibre `L.A i` satisfies `PullbacksTransferCovers`
    (`hstagePTC`), the canonical pullback's `π₂` of a cospan `(f,g)` with `f` a cover is itself a
    cover in the lax colimit `laxColimCat L hL`.  This is exactly the `hcanon` hypothesis consumed by
    `laxColimPreRegular`.

    Assembly (mirrors the strict `Colim.colimitCanonicalCover`):
    1. align `(f,g)` to a single-fibre cospan `(fN,gN)` in `L.A N` flanked by realignment isos
       (`colimHom_cospan_as_stageInclL`);
    2. transfer `Cover f` backward across the iso flanks to `Cover (stageInclL fN)`, then reflect to
       `Cover fN` in the fibre (`homInclL_cover_reflects`);
    3. the fibre's `PullbacksTransferCovers` gives `Cover` of the fibre chosen-pullback `π₂`;
    4. push that fibre pullback to a colimit pullback of `(stageInclL fN, stageInclL gN)`
       (`stageInclFunctorL_preservesPullbacks`) and its `π₂`-cover to the colimit
       (`homInclL_cover_of_stage`, with `hcovpres`);
    5. transfer the colimit pullback back onto `(f,g)` across the realignment isos
       (`cospanIsoTransferPullback`), giving a witness pullback of `(f,g)` with `π₂` a cover;
    6. `canonicalPullbackL_cover_of_witness` closes. -/
public theorem laxColim_hcanon_of_stage [Nonempty ι]
    (tData : LaxTerminalData L) (pData : LaxProductData L) (eqData : LaxEqualizerData L)
    (hfaith : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (p q : x ⟶ y),
        (L.functF hij).map p
          = (L.functF hij).map q → p = q)
    (hcons : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (φ : x ⟶ y),
        Monic φ → IsIso ((L.functF hij).map φ) → IsIso φ)
    (hmono : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (φ : x ⟶ y),
        Monic φ → Monic ((L.functF hij).map φ))
    (hcovpres : ∀ {i j : ι} (hij : D.le i j) {x y : L.A i} (φ : x ⟶ y),
        Cover φ → Cover ((L.functF hij).map φ))
    (hstagePTC : ∀ i, @PullbacksTransferCovers (L.A i) (L.catA i)) :
    letI : Cat (Obj L) := laxColimCat L hL
    letI : HasPullbacks (Obj L) := laxColimHasPullbacks L hL tData pData eqData
    ∀ {A B Z : Obj L} (f : A ⟶ Z) (g : B ⟶ Z), Cover f →
      Cover (HasPullbacks.has f g).cone.π₂ := by
  letI : Cat (Obj L) := laxColimCat L hL
  letI : HasPullbacks (Obj L) := laxColimHasPullbacks L hL tData pData eqData
  intro A B Z f g hfcov
  -- 1. align the cospan to a single fibre `L.A N`.
  obtain ⟨N, xA, xB, xZ, fN, gN, eA, eB, eZinv, hAiso, hBiso, hZiso, hfeq, hgeq⟩ :=
    colimHom_cospan_as_stageInclL L hL f g
  -- per-fibre finite-limit instances at `N`.
  letI : HasTerminal (L.A N) := tData.ht N
  letI : HasBinaryProducts (L.A N) := pData.hp N
  letI : HasEqualizers (L.A N) := eqData.he N
  -- 2. transfer `Cover f` backward across the iso flanks to `Cover (stageInclL fN)`.
  -- `stageInclL fN = eA⁻¹ ≫ f ≫ eZinv⁻¹` (cancel the iso flanks in `hfeq`).
  have hrw : stageInclL L hL fN = isoInv hAiso ≫ f ≫ isoInv hZiso := by
    have hf' : f = eA ≫ stageInclL L hL fN ≫ eZinv := hfeq
    rw [hf']
    simp only [Cat.assoc]
    rw [← Cat.assoc (isoInv hAiso) eA, inv_isoInv_comp, Cat.id_comp,
        isoInv_comp, Cat.comp_id]
  have hstagefN_cov : @Cover (Obj L) (laxColimCat L hL) _ _ (stageInclL L hL fN) := by
    rw [hrw]
    exact cover_precomp_iso ⟨eA, inv_isoInv_comp hAiso, isoInv_comp hAiso⟩
      (cover_comp_iso_cat hfcov ⟨eZinv, inv_isoInv_comp hZiso, isoInv_comp hZiso⟩)
  -- reflect to a fibre cover `Cover fN`.
  have hfN_cov : Cover fN := homInclL_cover_reflects L hL hcons hmono fN hstagefN_cov
  -- 3. fibre PTC on the chosen pullback of `(fN, gN)` gives `Cover (chosen π₂)`.
  have hstagePB_cov : Cover (products_equalizers_implies_pullbacks fN gN).cone.π₂ :=
    (hstagePTC N).pullbacks_transfer_covers _
      (products_equalizers_implies_pullbacks fN gN).cone_isPullback hfN_cov
  -- 4. push the fibre pullback to a colimit pullback of `(stageInclL fN, stageInclL gN)`.
  have hPBcolim := stageInclFunctorL_preservesPullbacks L hL tData pData eqData N fN gN
  -- the image cone's `π₂` is a cover in the colimit (cover preservation `homInclL_cover_of_stage`).
  have hπ₂colim_cov : @Cover (Obj L) _ _ _
      (stageInclL L hL (products_equalizers_implies_pullbacks fN gN).cone.π₂) := by
    apply homInclL_cover_of_stage L hL hfaith
    intro e hie
    exact hcovpres hie _ hstagePB_cov
  -- 5. transfer the colimit pullback back onto `(f,g)` across the realignment isos.
  obtain ⟨c, hc_pb, hc_cov⟩ := cospanIsoTransferPullback (𝒜 := Obj L)
    hAiso hBiso hZiso hfeq hgeq _ hPBcolim hπ₂colim_cov
  -- 6. canonical-pullback cover from the witness.
  exact @canonicalPullbackL_cover_of_witness (Obj L) (laxColimCat L hL)
    (laxColimHasPullbacks L hL tData pData eqData) A B Z f g c hc_pb hc_cov

end SingleUniverse



end Freyd.LaxColim
