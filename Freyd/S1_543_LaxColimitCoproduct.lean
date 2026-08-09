/-
  §M3b' (lax) — binary COPRODUCTS of the FILTERED lax colimit category `laxColimCat L hL`.

  ════════════════════════════════════════════════════════════════════════════════════════════
  This is the EXACT DUAL of the lax binary-PRODUCT development `laxColimHasBinaryProducts`
  (`Freyd/LaxColimitPreReg.lean`, section `LaxProduct`), and the lax analogue of the STRICT
  `Colim.colimitHasBinaryCoproducts` (`Freyd/CatColimitRegular.lean`).

  For `⟨i,x⟩ ⊔ ⟨j,y⟩` pick a common bound `k` (filtered); the coproduct object is the bare
  `⟨k, (hcop k).coprod (F x) (F y)⟩`.  Where products have projections `fst`/`snd` going OUT and the
  mediator `pair` going IN, coproducts FLIP every arrow: the injections `inl`/`inr` go INTO the
  coproduct and the mediator `case` comes OUT.  Concretely the single-stage germs are
  `inl ≫ isoInv reflApp` (the DUAL of the projection germ `reflApp ≫ fst`); the unit conjugator that
  appears when pushing them is `isoInv prUnit` (the inverse of the product's `prUnit`), so the SAME
  `prUnit`/`prUnit_isIso` infrastructure is reused — only the side on which it is cancelled flips.

  Reuses verbatim (from `LaxColimitPreReg`): `prK`/`prK_le` (the chosen common bound), `prUnit`/
  `prUnit_isIso` (the unit conjugator iso), and the lax germ algebra of `CapitalizationLaxColimit`.

  Mathlib-free; built on the repo's own `Cat` + `Freyd.LaxColim`.
-/
module

public import Freyd.S1_543_LaxColimitPreReg
public import Freyd.S1_58

open Freyd
open Freyd.Colim
open Freyd.LaxColim

namespace Freyd.LaxColim

universe u w

variable {ι : Type u} {D : Directed ι}

/-! ## Generic coproduct-germ helpers (`isoInv_prUnit`, `pushHom_inj`)

  These dualize `pushHom_proj` (the product's projection-germ push law).  Pushing the COPRODUCT
  inclusion germ `inj ≫ isoInv reflApp` from `k` to `m` produces the trailing factor
  `isoInv (prUnit_isIso L p hkm)` — the INVERSE of the product's `prUnit` — which we identify
  explicitly (`isoInv_prUnit`) so the cancellation in the universal-property proofs is the clean
  `inv_isoInv_comp`/`isoInv_comp`. -/
section CoprGeneric

variable (L : LaxCatSystem.{u, w} ι D)

/-- The inverse of the product's unit conjugator `prUnit` decomposes as `map (isoInv reflApp) ≫
    isoInv transApp` — the reversed composite of the two coherence isos.  Proven by uniqueness of
    two-sided inverses (`prUnit ≫ (that) = id`). -/
public theorem isoInv_prUnit {k m : ι} (p : L.A k) (hkm : D.le k m) :
    isoInv (prUnit_isIso L p hkm)
      = (L.functF hkm).map (isoInv (reflApp_isIso L p))
        ≫ isoInv (transApp_isIso L (D.refl k) hkm p) := by
  have hcancel : prUnit L p hkm
      ≫ ((L.functF hkm).map (isoInv (reflApp_isIso L p))
        ≫ isoInv (transApp_isIso L (D.refl k) hkm p)) = Cat.id _ := by
    unfold prUnit
    rw [Cat.assoc, ← Cat.assoc ((L.functF hkm).map (reflApp L p)),
        ← (L.functF hkm).map_comp (reflApp L p) (isoInv (reflApp_isIso L p)),
        isoInv_comp (reflApp_isIso L p),
        (L.functF hkm).map_id,
        Cat.id_comp, isoInv_comp (transApp_isIso L (D.refl k) hkm p)]
  calc isoInv (prUnit_isIso L p hkm)
      = isoInv (prUnit_isIso L p hkm) ≫ Cat.id _ := (Cat.comp_id _).symm
    _ = isoInv (prUnit_isIso L p hkm)
          ≫ (prUnit L p hkm
            ≫ ((L.functF hkm).map (isoInv (reflApp_isIso L p))
              ≫ isoInv (transApp_isIso L (D.refl k) hkm p))) := by rw [hcancel]
    _ = (isoInv (prUnit_isIso L p hkm) ≫ prUnit L p hkm)
          ≫ ((L.functF hkm).map (isoInv (reflApp_isIso L p))
            ≫ isoInv (transApp_isIso L (D.refl k) hkm p)) := (Cat.assoc _ _ _).symm
    _ = (L.functF hkm).map (isoInv (reflApp_isIso L p))
          ≫ isoInv (transApp_isIso L (D.refl k) hkm p) := by
      rw [inv_isoInv_comp (prUnit_isIso L p hkm), Cat.id_comp]

/-- **Pushing a single-stage INJECTION germ** `inj ≫ isoInv reflApp` from `k` to `m` (along `hkm`)
    equals `transApp ≫ (functF hkm).map inj ≫ isoInv (prUnit_isIso L p hkm)`.  The exact dual of
    `pushHom_proj`: where the projection's push has `prUnit` LEADING, the injection's push has its
    inverse TRAILING. -/
public theorem pushHom_inj {i k m : ι} (x : L.A i) (p : L.A k) (hik : D.le i k) (hkm : D.le k m)
    (inj : L.F hik x ⟶ p) :
    pushHom L x p hik (D.refl k) hkm (inj ≫ isoInv (reflApp_isIso L p))
      = transApp L hik hkm x ≫ (L.functF hkm).map inj ≫ isoInv (prUnit_isIso L p hkm) := by
  unfold pushHom
  rw [(L.functF hkm).map_comp inj (isoInv (reflApp_isIso L p)),
      isoInv_prUnit L p hkm, Cat.assoc]

end CoprGeneric

/-! ## LAX binary-coproduct preservation bundle

  Mirrors `LaxProductData` (and the strict `colimitHasBinaryCoproducts`'s `hcoppres`/`hcoppres_case`):
  `hcop` gives per-fibre coproducts; `pres` is joint-EPIC preservation under a transition; `presCase`
  is copairing preservation under a transition.  TRUE for base-change (`g*` is a right adjoint, so it
  preserves all finite *limits*; coproducts in each slice `Over (listProd U)` are computed in the
  base and `g*` preserves THEM via the comparison — discharged downstream). -/
public structure LaxCoproductData (L : LaxCatSystem.{u, w} ι D) where
  hcop : ∀ i, HasBinaryCoproducts (L.A i)
  pres : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
      (u v : L.F hij ((hcop i).coprod a b) ⟶ z),
      (L.functF hij).map (hcop i).inl ≫ u = (L.functF hij).map (hcop i).inl ≫ v →
      (L.functF hij).map (hcop i).inr ≫ u = (L.functF hij).map (hcop i).inr ≫ v → u = v
  presCase : ∀ {i j} (hij : D.le i j) (a b : L.A i) (z : L.A j)
      (p : L.F hij a ⟶ z) (q : L.F hij b ⟶ z),
      ∃ r : L.F hij ((hcop i).coprod a b) ⟶ z,
        (L.functF hij).map (hcop i).inl ≫ r = p ∧ (L.functF hij).map (hcop i).inr ≫ r = q

/-! ## §M3b' (lax) — binary coproducts of the lax colimit category -/
section LaxCoproduct

variable (L : LaxCatSystem.{u, w} ι D) (hL : Coherent L) (data : LaxCoproductData L)

/-- The coproduct object `⟨k, (hcop k).coprod (F x) (F y)⟩` in `Obj L`. -/
@[expose] public noncomputable def coprObj {i j : ι} (x : L.A i) (y : L.A j) : Obj L :=
  ⟨prK D i j, (data.hcop (prK D i j)).coprod (L.F (prK_le D i j).1 x) (L.F (prK_le D i j).2 y)⟩

/-- The `inl` injection germ `inl ≫ isoInv reflApp` at bound `⟨k, hik, refl k⟩` (dual of `prFst`). -/
@[expose] public noncomputable def coprInl {i j : ι} (x : L.A i) (y : L.A j) :
    homL L hL ⟨i, x⟩ (coprObj L data x y) :=
  homInclL L hL x ((data.hcop (prK D i j)).coprod (L.F (prK_le D i j).1 x) (L.F (prK_le D i j).2 y))
    ⟨prK D i j, (prK_le D i j).1, D.refl (prK D i j)⟩
    ((data.hcop (prK D i j)).inl ≫ isoInv (reflApp_isIso L _))

/-- The `inr` injection germ (dual of `prSnd`). -/
@[expose] public noncomputable def coprInr {i j : ι} (x : L.A i) (y : L.A j) :
    homL L hL ⟨j, y⟩ (coprObj L data x y) :=
  homInclL L hL y ((data.hcop (prK D i j)).coprod (L.F (prK_le D i j).1 x) (L.F (prK_le D i j).2 y))
    ⟨prK D i j, (prK_le D i j).2, D.refl (prK D i j)⟩
    ((data.hcop (prK D i j)).inr ≫ isoInv (reflApp_isIso L _))

/-- The single-germ representative `Ψ` produced by `coprCompProj`: the injection germ folded back by
    `pushHom_inj`, as TWO `pushHom`s (dual of `prPsi`).  Here the injection germ is the LEFT factor. -/
@[expose] public noncomputable def coprPsi {i k : ι} {l : ι} (x : L.A i) (p : L.A k) (z : L.A l)
    (hik : D.le i k) (inj : L.F hik x ⟶ p)
    (aw : UpperBound D k l) (m : L.F aw.2.1 p ⟶ L.F aw.2.2 z)
    (v : ι) (hkv : D.le k v) (hawv : D.le aw.1 v) :
    L.F (D.trans hik hkv) x ⟶ L.F (D.trans aw.2.2 hawv) z :=
  pushHom L x p hik (D.refl k) hkv (inj ≫ isoInv (reflApp_isIso L p))
    ≫ pushHom L p z aw.2.1 aw.2.2 hawv m

/-- Composing the injection germ (at `⟨k, hik, refl k⟩`, LEFT) with a stage-germ `⟨a₁, m₁⟩` reduces to
    a single germ `coprPsi` at the common bound `e` (dual of `prCompProj`). -/
public theorem coprCompProj {i k : ι} {l : ι} (x : L.A i) (p : L.A k) (z : L.A l)
    (hik : D.le i k) (inj : L.F hik x ⟶ p)
    (a₁ : UpperBound D k l) (m₁ : L.F a₁.2.1 p ⟶ L.F a₁.2.2 z)
    (e : ι) (hke : D.le k e) (ha₁e : D.le a₁.1 e) :
    @compL _ _ L hL ⟨i, x⟩ ⟨k, p⟩ ⟨l, z⟩
        (homInclL L hL x p ⟨k, hik, D.refl k⟩ (inj ≫ isoInv (reflApp_isIso L p)))
        (Quotient.mk _ ⟨a₁, m₁⟩)
      = homInclL L hL x z ⟨e, D.trans hik hke, D.trans a₁.2.2 ha₁e⟩
          (coprPsi L x p z hik inj a₁ m₁ e hke ha₁e) := by
  show homCompRawL L hL x p z ⟨k, hik, D.refl k⟩ (inj ≫ isoInv (reflApp_isIso L p)) a₁ m₁ = _
  rw [homCompRawL_eq_compAtL L hL x p z ⟨k, hik, D.refl k⟩ (inj ≫ isoInv (reflApp_isIso L p))
        a₁ m₁ e hke ha₁e]
  rfl

/-- **Level-push coherence of `coprPsi`** (dual of `prPsi_push`): pushing from `v` to `n` recomputes
    the rep at `n`; both `pushHom`s merge by `push_trans`. -/
public theorem coprPsi_push (hL : Coherent L) {i k : ι} {l : ι} (x : L.A i) (p : L.A k) (z : L.A l)
    (hik : D.le i k) (inj : L.F hik x ⟶ p)
    (aw : UpperBound D k l) (m : L.F aw.2.1 p ⟶ L.F aw.2.2 z)
    (v n : ι) (hkv : D.le k v) (hawv : D.le aw.1 v) (hvn : D.le v n) :
    pushHom L x z (D.trans hik hkv) (D.trans aw.2.2 hawv) hvn
        (coprPsi L x p z hik inj aw m v hkv hawv)
      = coprPsi L x p z hik inj aw m n (D.trans hkv hvn) (D.trans hawv hvn) := by
  unfold coprPsi
  rw [pushHom_comp L x p z (D.trans hik hkv) (D.trans (D.refl k) hkv) (D.trans aw.2.2 hawv) hvn
        (pushHom L x p hik (D.refl k) hkv (inj ≫ isoInv (reflApp_isIso L p)))
        (pushHom L p z aw.2.1 aw.2.2 hawv m),
      ← hL.push_trans x p hik (D.refl k) hkv hvn (inj ≫ isoInv (reflApp_isIso L p)),
      ← hL.push_trans p z aw.2.1 aw.2.2 hawv hvn m]

/-- **Existence of the case mediator** (dual of `prPairExists`).  For competitor germs
    `f : ⟨i,x⟩ ⟶ ⟨l,z⟩`, `g : ⟨j,y⟩ ⟶ ⟨l,z⟩`, push both to a common stage `m ≥ k`, convert their
    SOURCES to `F hkm (F hik x)`/`F hkm (F hjk y)` by `isoInv transApp`, apply `presCase`, and bake
    `prUnit` into the resulting germ so the injection's `isoInv prUnit` factor cancels. -/
public theorem coprCaseExists {i j : ι} (x : L.A i) (y : L.A j) {l : ι} (z : L.A l)
    (f : @Quotient _ (setoid (homSystemL L hL x z)))
    (g : @Quotient _ (setoid (homSystemL L hL y z))) :
    ∃ h : homL L hL (coprObj L data x y) ⟨l, z⟩,
      compL L hL (coprInl L hL data x y) h = f ∧ compL L hL (coprInr L hL data x y) h = g := by
  refine Quotient.inductionOn f (fun rf => ?_)
  refine Quotient.inductionOn g (fun rg => ?_)
  obtain ⟨af, fa⟩ := rf
  obtain ⟨ag, ga⟩ := rg
  let k := prK D i j
  have hik : D.le i k := (prK_le D i j).1
  have hjk : D.le j k := (prK_le D i j).2
  let ak := L.F hik x
  let bk := L.F hjk y
  let p := (data.hcop k).coprod ak bk
  -- common stage `m ≥ af.1, ag.1, k`.
  obtain ⟨e1, he1a, he1b⟩ := D.bound af.1 ag.1
  obtain ⟨m, hme, hmk⟩ := D.bound e1 k
  have hafm : D.le af.1 m := D.trans he1a hme
  have hagm : D.le ag.1 m := D.trans he1b hme
  have hkm : D.le k m := hmk
  have hlm : D.le l m := D.trans af.2.2 hafm
  -- convert pushed competitors' SOURCES to `F hkm ak` / `F hkm bk` via `isoInv transApp`.
  let p_case : L.F hkm ak ⟶ L.F hlm z :=
    isoInv (transApp_isIso L hik hkm x) ≫ pushHom L x z af.2.1 af.2.2 hafm fa
  let q_case : L.F hkm bk ⟶ L.F hlm z :=
    isoInv (transApp_isIso L hjk hkm y) ≫ pushHom L y z ag.2.1 ag.2.2 hagm ga
  obtain ⟨r, hr_inl, hr_inr⟩ := data.presCase hkm ak bk (L.F hlm z) p_case q_case
  -- both legs share the cancellation; the case germ rep `prUnit ≫ r` bakes in `prUnit` so the
  -- injection's trailing `isoInv prUnit` cancels.
  have leg : ∀ (i' : ι) (w : L.A i') (hi'k : D.le i' k) (inj : L.F hi'k w ⟶ p)
      (aw : UpperBound D i' l) (wa : L.F aw.2.1 w ⟶ L.F aw.2.2 z) (hawm : D.le aw.1 m),
      (L.functF hkm).map inj ≫ r
          = isoInv (transApp_isIso L hi'k hkm w) ≫ pushHom L w z aw.2.1 aw.2.2 hawm wa →
      @compL _ _ L hL ⟨i', w⟩ ⟨k, p⟩ ⟨l, z⟩
          (homInclL L hL w p ⟨k, hi'k, D.refl k⟩ (inj ≫ isoInv (reflApp_isIso L p)))
          (homInclL L hL p z ⟨m, hkm, hlm⟩ (prUnit L p hkm ≫ r))
        = Quotient.mk (setoid (homSystemL L hL w z)) ⟨aw, wa⟩ := by
    intro i' w hi'k inj aw wa hawm hcomp
    -- reduce the colimit composite to a stage composite at level `m`.
    show homCompRawL L hL w p z ⟨k, hi'k, D.refl k⟩ (inj ≫ isoInv (reflApp_isIso L p))
        ⟨m, hkm, hlm⟩ (prUnit L p hkm ≫ r)
      = homInclL L hL w z aw wa
    rw [homCompRawL_eq_compAtL L hL w p z ⟨k, hi'k, D.refl k⟩ (inj ≫ isoInv (reflApp_isIso L p))
          ⟨m, hkm, hlm⟩ (prUnit L p hkm ≫ r) m hkm (D.refl m)]
    unfold compAtL
    -- left push is `pushHom_inj`; right push along `refl m` is the identity (`push_refl`).
    rw [hL.push_refl p z hkm hlm (prUnit L p hkm ≫ r),
        pushHom_inj L w p hi'k hkm inj]
    -- cancel `isoInv prUnit ≫ prUnit = id`, then apply `hcomp`, then `transApp ≫ isoInv transApp = id`.
    rw [Cat.assoc, Cat.assoc, ← Cat.assoc (isoInv (prUnit_isIso L p hkm)),
        inv_isoInv_comp, Cat.id_comp, hcomp, ← Cat.assoc, isoInv_comp, Cat.id_comp]
    -- absorb the level `aw.1 → m` transition by `homInclL_compat`.
    exact homInclL_compat L hL w z (a := aw)
      (b := ⟨m, D.trans aw.2.1 hawm, D.trans aw.2.2 hawm⟩) hawm wa
  refine ⟨homInclL L hL p z ⟨m, hkm, hlm⟩ (prUnit L p hkm ≫ r), ?_, ?_⟩
  · exact leg i x hik (data.hcop k).inl af fa hafm hr_inl
  · exact leg j y hjk (data.hcop k).inr ag ga hagm hr_inr

/-- **Joint epimorphy of the two injections** (dual of `prJointMono`).  Two germs `⟨k,p⟩ ⟶ ⟨l,z⟩`
    that agree after `coprInl` and after `coprInr` are equal. -/
public theorem coprJointEpi {i j : ι} (x : L.A i) (y : L.A j) {l : ι} (z : L.A l)
    (h₁ h₂ : homL L hL (coprObj L data x y) ⟨l, z⟩)
    (hf : compL L hL (coprInl L hL data x y) h₁ = compL L hL (coprInl L hL data x y) h₂)
    (hs : compL L hL (coprInr L hL data x y) h₁ = compL L hL (coprInr L hL data x y) h₂) :
    h₁ = h₂ := by
  have hik : D.le i (prK D i j) := (prK_le D i j).1
  have hjk : D.le j (prK D i j) := (prK_le D i j).2
  revert hf hs
  refine Quotient.inductionOn₂ h₁ h₂ (fun rh₁ rh₂ hf hs => ?_)
  obtain ⟨a₁, m₁⟩ := rh₁
  obtain ⟨a₂, m₂⟩ := rh₂
  simp only [coprInl, coprInr, coprObj] at hf hs ⊢
  -- common bound `e ≥ a₁.1, a₂.1, k`.
  obtain ⟨w0, hw0a, hw0b⟩ := D.bound a₁.1 a₂.1
  obtain ⟨e, hew, hek⟩ := D.bound w0 (prK D i j)
  have ha₁e : D.le a₁.1 e := D.trans hw0a hew
  have ha₂e : D.le a₂.1 e := D.trans hw0b hew
  rw [coprCompProj L hL x _ z hik (data.hcop (prK D i j)).inl a₁ m₁ e hek ha₁e,
      coprCompProj L hL x _ z hik (data.hcop (prK D i j)).inl a₂ m₂ e hek ha₂e] at hf
  rw [coprCompProj L hL y _ z hjk (data.hcop (prK D i j)).inr a₁ m₁ e hek ha₁e,
      coprCompProj L hL y _ z hjk (data.hcop (prK D i j)).inr a₂ m₂ e hek ha₂e] at hs
  -- extract germ relations from `hf`/`hs`, then a common bound `n`.
  obtain ⟨cf, hcf1, hcf2, eqf⟩ := Quotient.exact hf
  obtain ⟨cs, hcs1, hcs2, eqs⟩ := Quotient.exact hs
  obtain ⟨n, hcfn, hcsn⟩ := D.bound cf.1 cs.1
  simp only [homSystemL] at eqf eqs
  rw [coprPsi_push L hL x _ z hik (data.hcop (prK D i j)).inl a₁ m₁ e cf.1 hek ha₁e hcf1,
      coprPsi_push L hL x _ z hik (data.hcop (prK D i j)).inl a₂ m₂ e cf.1 hek ha₂e hcf2] at eqf
  rw [coprPsi_push L hL y _ z hjk (data.hcop (prK D i j)).inr a₁ m₁ e cs.1 hek ha₁e hcs1,
      coprPsi_push L hL y _ z hjk (data.hcop (prK D i j)).inr a₂ m₂ e cs.1 hek ha₂e hcs2] at eqs
  have eqf' := congrArg (pushHom L x z (D.trans hik (D.trans hek hcf1))
      (D.trans a₁.2.2 (D.trans ha₁e hcf1)) hcfn) eqf
  have eqs' := congrArg (pushHom L y z (D.trans hjk (D.trans hek hcs1))
      (D.trans a₁.2.2 (D.trans ha₁e hcs1)) hcsn) eqs
  rw [coprPsi_push L hL x _ z hik (data.hcop (prK D i j)).inl a₁ m₁ cf.1 n _ _ hcfn,
      coprPsi_push L hL x _ z hik (data.hcop (prK D i j)).inl a₂ m₂ cf.1 n _ _ hcfn] at eqf'
  rw [coprPsi_push L hL y _ z hjk (data.hcop (prK D i j)).inr a₁ m₁ cs.1 n _ _ hcsn,
      coprPsi_push L hL y _ z hjk (data.hcop (prK D i j)).inr a₂ m₂ cs.1 n _ _ hcsn] at eqs'
  -- unfold `coprPsi` and fold the injection germ to `transApp ≫ map inj ≫ isoInv prUnit`.
  unfold coprPsi at eqf' eqs'
  rw [pushHom_inj L x _ hik _ (data.hcop (prK D i j)).inl] at eqf'
  rw [pushHom_inj L y _ hjk _ (data.hcop (prK D i j)).inr] at eqs'
  -- level data at `n`.
  have hkn : D.le (prK D i j) n := D.trans hek (D.trans hcf1 hcfn)
  have ha₁n : D.le a₁.1 n := D.trans ha₁e (D.trans hcf1 hcfn)
  have ha₂n : D.le a₂.1 n := D.trans ha₂e (D.trans hcf1 hcfn)
  -- the `isoInv prUnit`-conjugated reps `u₁,u₂ : F hkn p ⟶ F(l≤n)z`.
  let u₁ : L.F hkn ((data.hcop (prK D i j)).coprod (L.F hik x) (L.F hjk y))
      ⟶ L.F (D.trans a₁.2.2 ha₁n) z :=
    isoInv (prUnit_isIso L _ hkn) ≫ pushHom L _ z a₁.2.1 a₁.2.2 ha₁n m₁
  let u₂ : L.F hkn ((data.hcop (prK D i j)).coprod (L.F hik x) (L.F hjk y))
      ⟶ L.F (D.trans a₂.2.2 ha₂n) z :=
    isoInv (prUnit_isIso L _ hkn) ≫ pushHom L _ z a₂.2.1 a₂.2.2 ha₂n m₂
  -- cancel the leading `transApp` (pre-compose with `isoInv transApp`).
  have hinl : (L.functF hkn).map (data.hcop (prK D i j)).inl ≫ u₁
      = (L.functF hkn).map (data.hcop (prK D i j)).inl ≫ u₂ := by
    have := congrArg (isoInv (transApp_isIso L hik hkn x) ≫ ·) eqf'
    simp only [← Cat.assoc, inv_isoInv_comp, Cat.id_comp] at this
    simpa only [u₁, u₂, Cat.assoc] using this
  have hinr : (L.functF hkn).map (data.hcop (prK D i j)).inr ≫ u₁
      = (L.functF hkn).map (data.hcop (prK D i j)).inr ≫ u₂ := by
    have := congrArg (isoInv (transApp_isIso L hjk hkn y) ≫ ·) eqs'
    simp only [← Cat.assoc, inv_isoInv_comp, Cat.id_comp] at this
    simpa only [u₁, u₂, Cat.assoc] using this
  -- joint-epic preservation gives `u₁ = u₂`; cancel `isoInv prUnit` to get the germ witness.
  have huv : u₁ = u₂ :=
    data.pres hkn (L.F hik x) (L.F hjk y) (L.F (D.trans a₁.2.2 ha₁n) z) u₁ u₂ hinl hinr
  have hmm : pushHom L _ z a₁.2.1 a₁.2.2 ha₁n m₁ = pushHom L _ z a₂.2.1 a₂.2.2 ha₂n m₂ := by
    have h2 := congrArg (prUnit L _ hkn ≫ ·) huv
    simpa only [u₁, u₂, ← Cat.assoc, isoInv_comp, Cat.id_comp] using h2
  exact Quotient.sound ⟨⟨n, hkn, D.trans a₁.2.2 ha₁n⟩, ha₁n, ha₂n, hmm⟩

/-- **§M3b' (lax): the lax colimit category has binary coproducts.**  The coproduct of `⟨i,x⟩`,
    `⟨j,y⟩` is `coprObj = ⟨k, (hcop k).coprod (F x) (F y)⟩` at a common bound `k`; injections are
    `coprInl`/`coprInr`; `case` is the mediator from `coprCaseExists`; the laws are its spec plus
    `coprJointEpi`. -/
@[expose] public noncomputable def laxColimHasBinaryCoproducts :
    @HasBinaryCoproducts (Obj L) (laxColimCat L hL) := by
  letI : Cat (Obj L) := laxColimCat L hL
  refine @HasBinaryCoproducts.mk (Obj L) (laxColimCat L hL)
    (fun X Y => coprObj L data X.2 Y.2)
    (fun {X Y} => coprInl L hL data X.2 Y.2)
    (fun {X Y} => coprInr L hL data X.2 Y.2)
    (fun {X A B} f g => Classical.choose (coprCaseExists L hL data A.2 B.2 X.2 f g))
    (fun {X A B} f g => (Classical.choose_spec (coprCaseExists L hL data A.2 B.2 X.2 f g)).1)
    (fun {X A B} f g => (Classical.choose_spec (coprCaseExists L hL data A.2 B.2 X.2 f g)).2)
    (fun {X A B} f g h hinl hinr => ?_)
  -- `h` and `case f g` agree after both injections ⇒ equal by `coprJointEpi`.
  refine coprJointEpi L hL data A.2 B.2 X.2 h _ ?_ ?_
  · exact hinl.trans (Classical.choose_spec (coprCaseExists L hL data A.2 B.2 X.2 f g)).1.symm
  · exact hinr.trans (Classical.choose_spec (coprCaseExists L hL data A.2 B.2 X.2 f g)).2.symm

end LaxCoproduct

end Freyd.LaxColim
