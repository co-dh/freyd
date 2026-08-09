/-
  Freyd & Scedrov, *Categories and Allegories* — §1.625 / §1.634 / §1.635.

  **K1 — the stalk functor `T_F̂ : 𝒞 → Set` is a representation of REGULAR categories.**

  For a proper pre-filter `F̂` of subterminators in a positive pre-logos `𝒞`, the colimit
  functor `T_F̂ A = colim_{U∈F̂} Hom(U, A)` (built in `S1_62` as `TF`) is a filtered (↓-directed)
  colimit of representables.  As such it preserves all *finite limits* UNCONDITIONALLY — the
  "directed colimit commutes with finite limit in Set" theorem — which we prove here for binary
  products, equalizers and pullbacks.

  Freyd's §1.635 (book p.123, "BECAUSE") proves cover-preservation only AFTER concentrating on a
  CAPITAL positive pre-logos, where the elements of `F̂` (complemented subterminators) are
  PROJECTIVE (§1.633); the verbatim sentence is *"we obtain a representation `T_F : A → S` of
  regular categories SINCE the elements of `F` are projective"* and §1.634 records *"`T_F`
  preserves finite products and equalizers; if the elements of `F` are projective then `T_F`
  preserves covers."*  So cover-preservation is genuinely CONDITIONAL on projectivity of `F̂`'s
  elements — it is NOT a free consequence of filteredness (covers/epis are not a finite-limit
  notion).  We therefore prove cover-preservation as a lemma taking projectivity of `F̂`'s
  elements as an explicit hypothesis, and package `RegularFunctor (TF F̂)` from it.

  This file is downstream of `S1_62` (it uses `RelFunctor.RegularFunctor` from `RelCat`, which
  imports `S1_62`), so K1 cannot live in `S1_62` (cycle).
-/

module

public import Freyd.S2_111_RelCat

universe u

namespace Freyd.PreLogosHorn.Stalk

open Cat SetRegular RelFunctor

variable {𝒞 : Type u} [Cat.{u} 𝒞] [PreLogos 𝒞]

/-! ## Directed-colimit bookkeeping: restriction of a `PrefilterMap` to a refinement.

  A `PrefilterMap F̂ A` is a name `(U, g : U.dom → A)` with `U ∈ F̂`.  Given `W ∈ F̂` with a
  factorization `c : W.dom → U.dom`, `c ≫ g : W.dom → A` names the SAME class (refinement).  The
  two facts we use constantly: (i) the refined name is `PrefRel`-equal to the original, and (ii)
  refinement factorizations are unique because `U.arr` is monic. -/

/-- The restriction of a name `p = (U,g)` to a refinement `W ≤ U` (witnessed by `c≫U.arr=W.arr`)
    is `PrefRel`-equal to `p`. -/
public theorem prefRel_restrict (ℱ : Subobject 𝒞 one → Prop) {A : 𝒞} (p : PrefilterMap ℱ A)
    {W : Subobject 𝒞 one} (hW : ℱ W) (c : W.dom ⟶ p.U.dom) (hc : c ≫ p.U.arr = W.arr) :
    PrefRel ℱ (⟨W, hW, c ≫ p.map⟩ : PrefilterMap ℱ A) p :=
  ⟨W, hW, Cat.id _, c, Cat.id_comp _, hc, by rw [Cat.id_comp]⟩

/-- A bijection of types is an `IsIso` in `Type u`: assemble the two-sided inverse from
    `Function.surjective`/`injective`. -/
public theorem isIso_of_bijective {X Y : Type u} (f : X ⟶ Y)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f) : IsIso f := by
  refine ⟨fun y => (hsurj y).choose, ?_, ?_⟩
  · funext x
    exact hinj (by show f ((hsurj (f x)).choose) = f x; exact (hsurj (f x)).choose_spec)
  · funext y; exact (hsurj y).choose_spec

/-! ## §1.634 (finite-product half) — `T_F̂` preserves binary products.

  An element of `T_F̂(A×B)` is a class `(U, h : U.dom → A×B)`; the comparison sends it to
  `((U, h≫fst), (U, h≫snd))`.  SURJECTIVITY pairs two names over a common ↓-refinement; INJECTIVITY
  re-pairs an `fst`-agreement and an `snd`-agreement over a common refinement and cancels the
  jointly-monic `(fst,snd)`.  No projectivity used — this is "directed colimit commutes with finite
  product in Set". -/

/-- INJECTIVITY core.  Two names `p, q : PrefilterMap ℱ (A×B)` whose `fst`-restrictions are
    `PrefRel` and whose `snd`-restrictions are `PrefRel` are themselves `PrefRel`.  Merge the two
    refinements over a common ↓-refinement `W`, then cancel the jointly-monic pair `(fst,snd)`. -/
public theorem prefRel_of_legs {ℱ : Subobject 𝒞 one → Prop} (hℱ : IsPreFilter ℱ)
    {A B : 𝒞} {p q : PrefilterMap ℱ (prod A B)}
    (hf : PrefRel ℱ (⟨p.U, p.hU, p.map ≫ fst⟩ : PrefilterMap ℱ A) ⟨q.U, q.hU, q.map ≫ fst⟩)
    (hs : PrefRel ℱ (⟨p.U, p.hU, p.map ≫ snd⟩ : PrefilterMap ℱ B) ⟨q.U, q.hU, q.map ≫ snd⟩) :
    PrefRel ℱ p q := by
  obtain ⟨Wf, hWf, af, bf, hafW, hbfW, habf⟩ := hf
  obtain ⟨Ws, hWs, as', bs, hasW, hbsW, habs⟩ := hs
  obtain ⟨W, hW, ⟨cf, hcf⟩, ⟨cs, hcs⟩⟩ := hℱ.2 Wf Ws hWf hWs
  -- common a : W → p.U.dom (= cf≫af), and the two routes to p.U.dom over W agree (monic p.U.arr)
  have hpa : cf ≫ af = cs ≫ as' := by
    apply p.U.monic
    calc (cf ≫ af) ≫ p.U.arr = cf ≫ (af ≫ p.U.arr) := Cat.assoc _ _ _
      _ = cf ≫ Wf.arr := by rw [hafW]
      _ = W.arr := hcf
      _ = cs ≫ Ws.arr := hcs.symm
      _ = cs ≫ (as' ≫ p.U.arr) := by rw [hasW]
      _ = (cs ≫ as') ≫ p.U.arr := (Cat.assoc _ _ _).symm
  have hqb : cf ≫ bf = cs ≫ bs := by
    apply q.U.monic
    calc (cf ≫ bf) ≫ q.U.arr = cf ≫ (bf ≫ q.U.arr) := Cat.assoc _ _ _
      _ = cf ≫ Wf.arr := by rw [hbfW]
      _ = W.arr := hcf
      _ = cs ≫ Ws.arr := hcs.symm
      _ = cs ≫ (bs ≫ q.U.arr) := by rw [hbsW]
      _ = (cs ≫ bs) ≫ q.U.arr := (Cat.assoc _ _ _).symm
  refine ⟨W, hW, cf ≫ af, cf ≫ bf, ?_, ?_, ?_⟩
  · rw [Cat.assoc, hafW]; exact hcf
  · rw [Cat.assoc, hbfW]; exact hcf
  · -- (cf≫af)≫p.map = (cf≫bf)≫q.map : agree on fst and on snd, cancel (fst,snd) via pair_uniq
    have legA : ((cf ≫ af) ≫ p.map) ≫ fst = ((cf ≫ bf) ≫ q.map) ≫ fst := by
      calc ((cf ≫ af) ≫ p.map) ≫ fst = cf ≫ (af ≫ (p.map ≫ fst)) := by
            rw [Cat.assoc, Cat.assoc]
        _ = cf ≫ (bf ≫ (q.map ≫ fst)) := by rw [habf]
        _ = ((cf ≫ bf) ≫ q.map) ≫ fst := by rw [Cat.assoc, Cat.assoc]
    have legB : ((cf ≫ af) ≫ p.map) ≫ snd = ((cf ≫ bf) ≫ q.map) ≫ snd := by
      calc ((cf ≫ af) ≫ p.map) ≫ snd = cs ≫ (as' ≫ (p.map ≫ snd)) := by
            rw [hpa, Cat.assoc, Cat.assoc]
        _ = cs ≫ (bs ≫ (q.map ≫ snd)) := by rw [habs]
        _ = ((cs ≫ bs) ≫ q.map) ≫ snd := by rw [Cat.assoc, Cat.assoc]
        _ = ((cf ≫ bf) ≫ q.map) ≫ snd := by rw [hqb]
    -- both legs land in A×B; (fst,snd) jointly monic: pair_uniq forces the two maps equal.
    have e1 : (cf ≫ af) ≫ p.map = pair (((cf ≫ af) ≫ p.map) ≫ fst) (((cf ≫ af) ≫ p.map) ≫ snd) :=
      pair_uniq _ _ _ rfl rfl
    have e2 : (cf ≫ bf) ≫ q.map = pair (((cf ≫ af) ≫ p.map) ≫ fst) (((cf ≫ af) ≫ p.map) ≫ snd) :=
      pair_uniq _ _ _ legA.symm legB.symm
    rw [e1, e2]

/-! ### `T_F̂` preserves binary products. -/

public theorem TF_preserves_binaryProducts (ℱ : Subobject 𝒞 one → Prop) (hℱ : IsPreFilter ℱ) :
    PreservesBinaryProducts (TF_functor ℱ) := by
  intro A B
  apply isIso_of_bijective
  · -- INJECTIVE: comparison `φ t = (TF.map fst t, TF.map snd t)`
    refine Quot.ind (fun p => Quot.ind (fun q hpq => ?_))
    have hfst : TF.mk ℱ ⟨p.U, p.hU, p.map ≫ fst⟩ = TF.mk ℱ ⟨q.U, q.hU, q.map ≫ fst⟩ :=
      congrArg Prod.fst hpq
    have hsnd : TF.mk ℱ ⟨p.U, p.hU, p.map ≫ snd⟩ = TF.mk ℱ ⟨q.U, q.hU, q.map ≫ snd⟩ :=
      congrArg Prod.snd hpq
    exact Quot.sound (prefRel_of_legs hℱ (PrefRel_of_TF_eq ℱ hℱ hfst) (PrefRel_of_TF_eq ℱ hℱ hsnd))
  · -- SURJECTIVE: pair two names over a common ↓-refinement
    rintro ⟨s, t⟩
    induction s using Quot.ind with | _ p => ?_
    induction t using Quot.ind with | _ q => ?_
    -- `(s,t) = (TF.mk p, TF.mk q)`, p:U₁→A, q:U₂→B
    obtain ⟨W, hW, ⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ := hℱ.2 p.U q.U p.hU q.hU
    refine ⟨TF.mk ℱ ⟨W, hW, pair (c₁ ≫ p.map) (c₂ ≫ q.map)⟩, ?_⟩
    refine Prod.ext ?_ ?_
    · -- TF.map fst (mk ⟨W, pair…⟩) = TF.mk p
      show TF.mk ℱ ⟨W, hW, pair (c₁ ≫ p.map) (c₂ ≫ q.map) ≫ fst⟩ = Quot.mk _ p
      refine Quot.sound ?_
      have : pair (c₁ ≫ p.map) (c₂ ≫ q.map) ≫ fst = c₁ ≫ p.map := fst_pair _ _
      rw [this]; exact prefRel_restrict ℱ p hW c₁ hc₁
    · show TF.mk ℱ ⟨W, hW, pair (c₁ ≫ p.map) (c₂ ≫ q.map) ≫ snd⟩ = Quot.mk _ q
      refine Quot.sound ?_
      have : pair (c₁ ≫ p.map) (c₂ ≫ q.map) ≫ snd = c₂ ≫ q.map := snd_pair _ _
      rw [this]; exact prefRel_restrict ℱ q hW c₂ hc₂

/-- The legs of a pullback cone are jointly monic. -/
public theorem pullback_monicPair {A B C : 𝒞} {f : A ⟶ C} {g : B ⟶ C} (c : Cone f g)
    (hc : c.IsPullback) : MonicPair c.π₁ c.π₂ := by
  intro W p q hp hq
  have hw : (p ≫ c.π₁) ≫ f = (p ≫ c.π₂) ≫ g := by
    rw [Cat.assoc, Cat.assoc, c.w]
  obtain ⟨_, _, huniq⟩ := hc ⟨W, p ≫ c.π₁, p ≫ c.π₂, hw⟩
  exact (huniq p rfl rfl).trans (huniq q hp.symm hq.symm).symm

/-- `T_F̂` carries a jointly-monic pair `(m,n)` in `𝒞` to a jointly-monic pair in `Set`: two
    classes agreeing after `≫m` and after `≫n` are equal.  Merge the two refinements over a common
    ↓-refinement and cancel `(m,n)`. -/
public theorem TF_jointly_monic {ℱ : Subobject 𝒞 one → Prop} (hℱ : IsPreFilter ℱ)
    {Z A B : 𝒞} {m : Z ⟶ A} {n : Z ⟶ B} (hjm : MonicPair m n)
    (x y : TF ℱ Z) (hA : TF.map ℱ m x = TF.map ℱ m y) (hB : TF.map ℱ n x = TF.map ℱ n y) :
    x = y := by
  revert hA hB
  induction x using Quot.ind with | _ p => ?_
  induction y using Quot.ind with | _ q => ?_
  intro hA hB
  have hAm : TF.mk ℱ ⟨p.U, p.hU, p.map ≫ m⟩ = TF.mk ℱ ⟨q.U, q.hU, q.map ≫ m⟩ := hA
  have hBn : TF.mk ℱ ⟨p.U, p.hU, p.map ≫ n⟩ = TF.mk ℱ ⟨q.U, q.hU, q.map ≫ n⟩ := hB
  obtain ⟨Wf, hWf, af, bf, hafW, hbfW, habf⟩ := PrefRel_of_TF_eq ℱ hℱ hAm
  obtain ⟨Ws, hWs, as', bs, hasW, hbsW, habs⟩ := PrefRel_of_TF_eq ℱ hℱ hBn
  obtain ⟨W, hW, ⟨cf, hcf⟩, ⟨cs, hcs⟩⟩ := hℱ.2 Wf Ws hWf hWs
  have hpa : cf ≫ af = cs ≫ as' := by
    apply p.U.monic
    calc (cf ≫ af) ≫ p.U.arr = cf ≫ (af ≫ p.U.arr) := Cat.assoc _ _ _
      _ = cf ≫ Wf.arr := by rw [hafW]
      _ = W.arr := hcf
      _ = cs ≫ Ws.arr := hcs.symm
      _ = cs ≫ (as' ≫ p.U.arr) := by rw [hasW]
      _ = (cs ≫ as') ≫ p.U.arr := (Cat.assoc _ _ _).symm
  have hqb : cf ≫ bf = cs ≫ bs := by
    apply q.U.monic
    calc (cf ≫ bf) ≫ q.U.arr = cf ≫ (bf ≫ q.U.arr) := Cat.assoc _ _ _
      _ = cf ≫ Wf.arr := by rw [hbfW]
      _ = W.arr := hcf
      _ = cs ≫ Ws.arr := hcs.symm
      _ = cs ≫ (bs ≫ q.U.arr) := by rw [hbsW]
      _ = (cs ≫ bs) ≫ q.U.arr := (Cat.assoc _ _ _).symm
  -- (cf≫af)≫p.map and (cf≫bf)≫q.map agree after ≫m and ≫n, so equal by hjm; classes equal.
  apply Quot.sound
  refine ⟨W, hW, cf ≫ af, cf ≫ bf, by rw [Cat.assoc, hafW]; exact hcf,
    by rw [Cat.assoc, hbfW]; exact hcf, ?_⟩
  -- goal: (cf≫af) ≫ p.map = (cf≫bf) ≫ q.map
  refine hjm ((cf ≫ af) ≫ p.map) ((cf ≫ bf) ≫ q.map) ?_ ?_
  · -- ≫m agreement (from habf : af ≫ (p.map ≫ m) = bf ≫ (q.map ≫ m))
    have : cf ≫ (af ≫ (p.map ≫ m)) = cf ≫ (bf ≫ (q.map ≫ m)) := by rw [habf]
    simpa only [Cat.assoc] using this
  · -- ≫n agreement (from habs, via hpa/hqb)
    have step : cs ≫ (as' ≫ (p.map ≫ n)) = cs ≫ (bs ≫ (q.map ≫ n)) := by rw [habs]
    have hpa' : cf ≫ (af ≫ (p.map ≫ n)) = cs ≫ (as' ≫ (p.map ≫ n)) := by
      have : cf ≫ af = cs ≫ as' := hpa
      simp only [← Cat.assoc, this]
    have hqb' : cs ≫ (bs ≫ (q.map ≫ n)) = cf ≫ (bf ≫ (q.map ≫ n)) := by
      have : cs ≫ bs = cf ≫ bf := hqb.symm
      simp only [← Cat.assoc, this]
    have : cf ≫ (af ≫ (p.map ≫ n)) = cf ≫ (bf ≫ (q.map ≫ n)) := hpa'.trans (step.trans hqb')
    simpa only [Cat.assoc] using this

/-! ## §1.634 — `T_F̂` preserves pullbacks (a finite limit).

  Given a pullback square `c` over `(f,g)` in `𝒞`, the `T_F̂`-image cone in `Set` is a pullback:
  a `Set`-cone `d` over `(T_F̂ f, T_F̂ g)` is, per element `δ`, two names agreeing after `≫f`/`≫g`
  in the colimit; ↓-directedness pulls them to a common `W` where they agree on the nose, giving a
  `𝒞`-cone from `W.dom` that `c.IsPullback` lifts to `c.pt`.  No projectivity. -/

/-- Per-element cone data: if `TF.map f x = TF.map g y` then there is a common refinement `W ∈ ℱ`
    and maps `a : W→A`, `b : W→B` representing `x, y` with `a≫f = b≫g` (a `𝒞`-cone from `W.dom`). -/
public theorem cone_data_of_eq {ℱ : Subobject 𝒞 one → Prop} (hℱ : IsPreFilter ℱ)
    {A B C : 𝒞} (f : A ⟶ C) (g : B ⟶ C) (x : TF ℱ A) (y : TF ℱ B)
    (hxy : TF.map ℱ f x = TF.map ℱ g y) :
    ∃ (W : Subobject 𝒞 one) (hW : ℱ W), ∃ (a : W.dom ⟶ A) (b : W.dom ⟶ B),
      a ≫ f = b ≫ g ∧ TF.mk ℱ ⟨W, hW, a⟩ = x ∧ TF.mk ℱ ⟨W, hW, b⟩ = y := by
  revert hxy
  induction x using Quot.ind with | _ p => ?_
  induction y using Quot.ind with | _ q => ?_
  intro hxy
  -- `hxy : TF.mk (p.U, p.map≫f) = TF.mk (q.U, q.map≫g)`
  have h : TF.mk ℱ ⟨p.U, p.hU, p.map ≫ f⟩ = TF.mk ℱ ⟨q.U, q.hU, q.map ≫ g⟩ := hxy
  obtain ⟨W, hW, wa, wb, hwa, hwb, hagree⟩ := PrefRel_of_TF_eq ℱ hℱ h
  -- wa : W→p.U.dom, wb : W→q.U.dom; agree : wa≫(p.map≫f) = wb≫(q.map≫g)
  refine ⟨W, hW, wa ≫ p.map, wb ≫ q.map, ?_, ?_, ?_⟩
  · -- (wa≫p.map)≫f = (wb≫q.map)≫g
    calc (wa ≫ p.map) ≫ f = wa ≫ (p.map ≫ f) := Cat.assoc _ _ _
      _ = wb ≫ (q.map ≫ g) := hagree
      _ = (wb ≫ q.map) ≫ g := (Cat.assoc _ _ _).symm
  · exact Quot.sound (prefRel_restrict ℱ p hW wa hwa)
  · exact Quot.sound (prefRel_restrict ℱ q hW wb hwb)

public theorem TF_preserves_pullbacks (ℱ : Subobject 𝒞 one → Prop) (hℱ : IsPreFilter ℱ) :
    PreservesPullbacks (TF_functor ℱ) := by
  intro A B C f g c hc d
  -- For each δ : d.pt, get a representing `𝒞`-cone over `(f,g)`, lift through `c`.
  -- existence of `u : d.pt → TF c.pt`
  have hcone : ∀ δ : d.pt, TF.map ℱ f (d.π₁ δ) = TF.map ℱ g (d.π₂ δ) := by
    intro δ
    have := congrFun d.w δ
    simpa using this
  -- per-element cone data via `.choose` (no Mathlib `choose` tactic in this repo)
  let dat : ∀ δ : d.pt, _ := fun δ => cone_data_of_eq hℱ f g (d.π₁ δ) (d.π₂ δ) (hcone δ)
  let W : d.pt → Subobject 𝒞 one := fun δ => (dat δ).choose
  let hW : ∀ δ, ℱ (W δ) := fun δ => (dat δ).choose_spec.choose
  let a : ∀ δ, (W δ).dom ⟶ A := fun δ => (dat δ).choose_spec.choose_spec.choose
  let b : ∀ δ, (W δ).dom ⟶ B := fun δ => (dat δ).choose_spec.choose_spec.choose_spec.choose
  have hcomm : ∀ δ, a δ ≫ f = b δ ≫ g := fun δ =>
    (dat δ).choose_spec.choose_spec.choose_spec.choose_spec.1
  have hxa : ∀ δ, TF.mk ℱ ⟨W δ, hW δ, a δ⟩ = d.π₁ δ := fun δ =>
    (dat δ).choose_spec.choose_spec.choose_spec.choose_spec.2.1
  have hyb : ∀ δ, TF.mk ℱ ⟨W δ, hW δ, b δ⟩ = d.π₂ δ := fun δ =>
    (dat δ).choose_spec.choose_spec.choose_spec.choose_spec.2.2
  -- the `𝒞`-cone from W.dom δ and its lift through the pullback c
  let lift : ∀ δ, (W δ).dom ⟶ c.pt := fun δ => (hc ⟨(W δ).dom, a δ, b δ, hcomm δ⟩).choose
  have hlift₁ : ∀ δ, lift δ ≫ c.π₁ = a δ := fun δ => (hc ⟨(W δ).dom, a δ, b δ, hcomm δ⟩).choose_spec.1.1
  have hlift₂ : ∀ δ, lift δ ≫ c.π₂ = b δ := fun δ => (hc ⟨(W δ).dom, a δ, b δ, hcomm δ⟩).choose_spec.1.2
  refine ⟨fun δ => TF.mk ℱ ⟨W δ, hW δ, lift δ⟩, ⟨?_, ?_⟩, ?_⟩
  · -- u ≫ TF.map c.π₁ = d.π₁
    funext δ
    show TF.map ℱ c.π₁ (TF.mk ℱ ⟨W δ, hW δ, lift δ⟩) = d.π₁ δ
    rw [TF.map_mk]
    -- TF.mk (W, lift≫c.π₁) = TF.mk (W, a) = d.π₁ δ
    have : (⟨W δ, hW δ, lift δ ≫ c.π₁⟩ : PrefilterMap ℱ A) = ⟨W δ, hW δ, a δ⟩ := by
      rw [hlift₁]
    rw [this]; exact hxa δ
  · funext δ
    show TF.map ℱ c.π₂ (TF.mk ℱ ⟨W δ, hW δ, lift δ⟩) = d.π₂ δ
    rw [TF.map_mk]
    have : (⟨W δ, hW δ, lift δ ≫ c.π₂⟩ : PrefilterMap ℱ B) = ⟨W δ, hW δ, b δ⟩ := by
      rw [hlift₂]
    rw [this]; exact hyb δ
  · -- UNIQUENESS: `(c.π₁,c.π₂)` is jointly monic (pullback cone), preserved by `T_F̂`.
    intro v hv₁ hv₂
    have hjm : MonicPair c.π₁ c.π₂ := pullback_monicPair c hc
    funext δ
    refine TF_jointly_monic hℱ hjm _ _ ?_ ?_
    · -- TF.map c.π₁ (v δ) = TF.map c.π₁ (u δ)
      have h1 : TF.map ℱ c.π₁ (v δ) = d.π₁ δ := congrFun hv₁ δ
      show TF.map ℱ c.π₁ (v δ) = TF.map ℱ c.π₁ (TF.mk ℱ ⟨W δ, hW δ, lift δ⟩)
      rw [h1, TF.map_mk]
      have : (⟨W δ, hW δ, lift δ ≫ c.π₁⟩ : PrefilterMap ℱ A) = ⟨W δ, hW δ, a δ⟩ := by rw [hlift₁]
      rw [this]; exact (hxa δ).symm
    · have h2 : TF.map ℱ c.π₂ (v δ) = d.π₂ δ := congrFun hv₂ δ
      show TF.map ℱ c.π₂ (v δ) = TF.map ℱ c.π₂ (TF.mk ℱ ⟨W δ, hW δ, lift δ⟩)
      rw [h2, TF.map_mk]
      have : (⟨W δ, hW δ, lift δ ≫ c.π₂⟩ : PrefilterMap ℱ B) = ⟨W δ, hW δ, b δ⟩ := by rw [hlift₂]
      rw [this]; exact (hyb δ).symm

/-! ## §1.634 — `T_F̂` preserves monos.

  `T_F̂(m)` is injective when `m` is monic: equality of classes `(U, a≫m) ~ (U', a'≫m)` reflects to
  `(U,a) ~ (U',a')` by cancelling the monic `m` (`PrefRel_reflect_monic`). -/

/-! ## §1.634 / §1.633 — `T_F̂` preserves covers WHEN the elements of `ℱ` are PROJECTIVE.

  This is Freyd's §1.635 step: *"we obtain a representation `T_F : A → S` of regular categories
  SINCE the elements of `F` are projective"* (book p.123), and §1.634: *"if the elements of `F` are
  projective then `T_F` preserves covers."*  In a CAPITAL positive pre-logos the complemented
  subterminators (= the members of an ultra-filter) are projective (§1.633), so the hypothesis is
  exactly met after capitalizing.  It is NOT a free consequence of filteredness: covers are not a
  finite-limit notion. -/

public theorem TF_preserves_covers_of_projective (ℱ : Subobject 𝒞 one → Prop)
    (hproj : ∀ U : Subobject 𝒞 one, ℱ U → Projective U.dom) :
    PreservesCovers (TF_functor ℱ) := by
  intro A B e he
  -- `TF.map e` surjective ⟹ cover in `Set` (`set_cover_iff_surjective`)
  refine (set_cover_iff_surjective (TF.map ℱ e)).2 ?_
  intro bb
  induction bb using Quot.ind with | _ p => ?_
  -- p = (U, g : U.dom → B), U ∈ ℱ.  Pull `e` back along `g`.
  let pb := HasPullbacks.has e p.map
  -- the projection `pb.π₂ : P → U.dom` is a cover (covers transfer along pullback of `e`)
  have hcov : Cover pb.cone.π₂ := cover_pullback (f := e) p.map he
  -- U projective ⟹ the cover `pb.cone.π₂` splits
  obtain ⟨s, hs⟩ := hproj p.U p.hU pb.cone.π₂ hcov
  -- lift name `(U, s ≫ pb.π₁ ≫ e) = (U, g)` so `TF.map e` hits `[p]`
  refine ⟨TF.mk ℱ ⟨p.U, p.hU, s ≫ pb.cone.π₁⟩, ?_⟩
  show TF.mk ℱ ⟨p.U, p.hU, (s ≫ pb.cone.π₁) ≫ e⟩ = Quot.mk _ p
  -- (s≫π₁)≫e = s≫(π₁≫e) = s≫(π₂≫g) = (s≫π₂)≫g = g
  refine Quot.sound ?_
  have hsq : (s ≫ pb.cone.π₁) ≫ e = p.map := by
    calc (s ≫ pb.cone.π₁) ≫ e = s ≫ (pb.cone.π₁ ≫ e) := Cat.assoc _ _ _
      _ = s ≫ (pb.cone.π₂ ≫ p.map) := by rw [pb.cone.w]
      _ = (s ≫ pb.cone.π₂) ≫ p.map := (Cat.assoc _ _ _).symm
      _ = Cat.id _ ≫ p.map := by rw [hs]
      _ = p.map := Cat.id_comp _
  -- `(U, (s≫π₁)≫e) ~ p` : same `U`, identity refinement, maps equal by `hsq`
  exact ⟨p.U, p.hU, Cat.id _, Cat.id _, Cat.id_comp _, Cat.id_comp _, by
    rw [Cat.id_comp, Cat.id_comp]; exact hsq⟩

public theorem TF_preserves_mono (ℱ : Subobject 𝒞 one → Prop) (hℱ : IsPreFilter ℱ) :
    PreservesMono (TF_functor ℱ) := by
  intro X Y m hm
  -- `TF.map m` injective ⟹ monic in `Type u` (`set_monic_iff_injective`)
  refine (set_monic_iff_injective (TF.map ℱ m)).2 ?_
  refine Quot.ind (fun p => Quot.ind (fun q hpq => ?_))
  -- `hpq : TF.mk (U, p.map≫m) = TF.mk (U', q.map≫m)`
  have h : TF.mk ℱ ⟨p.U, p.hU, p.map ≫ m⟩ = TF.mk ℱ ⟨q.U, q.hU, q.map ≫ m⟩ := hpq
  exact Quot.sound (PrefRel_reflect_monic ℱ hm (PrefRel_of_TF_eq ℱ hℱ h))

/-! ## §1.634 — `T_F̂` preserves images (cover-then-mono), given projectivity.

  Mirrors `homRep_preserves_images`: in a regular category `image f = (image.lift f) ; (image.arr)`
  with the lift a cover; `T_F̂` preserves the cover (projectivity) and the mono, and a cover-then-mono
  factorization in `Set` is an image.  Minimality uses surjectivity of `T_F̂(ℓ)` + fibre choice. -/

public theorem TF_preserves_images (ℱ : Subobject 𝒞 one → Prop) (hℱ : IsPreFilter ℱ)
    (hproj : ∀ U : Subobject 𝒞 one, ℱ U → Projective U.dom) :
    PreservesImages (TF_functor ℱ) (TF_preserves_mono ℱ hℱ) := by
  intro A B f I hI
  obtain ⟨ℓ, hℓ⟩ := hI.1
  -- `ℓ : A → I.dom`, `ℓ ≫ I.arr = f`; `ℓ` is a cover (image lift, transported across `image f ≅ I`).
  have hℓcov : Cover ℓ := by
    have hImg : IsImage f (image f) := HasImages.isImage f
    obtain ⟨k, hk⟩ := hImg.2 I hI.1
    obtain ⟨k', hk'⟩ := hI.2 (image f) hImg.1
    have hkk' : k ≫ k' = Cat.id (image f).dom := by
      apply (image f).monic; rw [Cat.assoc, hk', hk, Cat.id_comp]
    have hk'k : k' ≫ k = Cat.id I.dom := by
      apply I.monic; rw [Cat.assoc, hk, hk', Cat.id_comp]
    have hlift : image.lift f ≫ k = ℓ := by
      apply I.monic; rw [Cat.assoc, hk, image.lift_fac, hℓ]
    have hkcov : Cover k := iso_cover k ⟨k', hkk', hk'k⟩
    have : Cover (image.lift f ≫ k) := cover_comp (image_lift_cover f) hkcov
    rwa [hlift] at this
  -- `TF.map ℓ` is a cover in `Set`, hence surjective.
  have hℓcov' : Cover ((TF_functor ℱ).map ℓ) :=
    TF_preserves_covers_of_projective ℱ hproj ℓ hℓcov
  have hℓsurj : Function.Surjective (TF.map ℱ ℓ) := (set_cover_iff_surjective _).1 hℓcov'
  -- Build `IsImage (TF.map f) (Subobject.map (TF ℱ) _ I)`.
  refine ⟨⟨TF.map ℱ ℓ, ?_⟩, ?_⟩
  · -- allows: `TF.map ℓ ≫ TF.map I.arr = TF.map f` (fibrewise, as functions)
    funext z
    show TF.map ℱ I.arr (TF.map ℱ ℓ z) = TF.map ℱ f z
    rw [← TF.map_comp ℱ ℓ I.arr, hℓ]
  · -- minimality: any `S` allowing `TF.map f` receives `Subobject.map _ I`.
    intro S hS
    obtain ⟨t, ht⟩ := hS
    -- `t ≫ S.arr = TF.map f`.  Goal: `(Subobject.map _ I).le S`, i.e. `r ≫ S.arr = TF.map I.arr`.
    -- `TF.map ℓ` is onto `TF I.dom`; pick a preimage `pre y` and set `r y = t (pre y)`.
    let pre : (TF ℱ I.dom) → (TF ℱ A) := fun y => (hℓsurj y).choose
    have hpre : ∀ y, TF.map ℱ ℓ (pre y) = y := fun y => (hℓsurj y).choose_spec
    have ht' : ∀ z, S.arr (t z) = TF.map ℱ I.arr (TF.map ℱ ℓ z) := by
      intro z
      have e2 : S.arr (t z) = TF.map ℱ f z := congrFun ht z
      rw [e2, ← TF.map_comp ℱ ℓ I.arr, hℓ]
    refine ⟨fun y => t (pre y), ?_⟩
    funext y
    show S.arr (t (pre y)) = TF.map ℱ I.arr y
    rw [ht' (pre y), hpre y]

/-! ## §1.634 / §1.635 — `T_F̂` is a `RegularFunctor`, given projectivity of `ℱ`'s elements.

  This is exactly Freyd's §1.635 *"representation of regular categories"* for the stalk functor.
  The finite-limit fields (`pres_prod`, `pres_pullback`, `pres_mono`) hold for ANY pre-filter; the
  cover/image fields require — as the book demands — that the elements of `ℱ` are PROJECTIVE
  (automatic in a CAPITAL positive pre-logos, §1.633).  The structure lives in `RelCat`, so this
  packaging is the natural home (downstream of both `S1_62` and `RelCat`). -/

public theorem TF_regularFunctor (ℱ : Subobject 𝒞 one → Prop) (hℱ : IsPreFilter ℱ)
    (hproj : ∀ U : Subobject 𝒞 one, ℱ U → Projective U.dom) :
    RelFunctor.RegularFunctor (TF_functor ℱ) where
  pres_prod := TF_preserves_binaryProducts ℱ hℱ
  pres_pullback := TF_preserves_pullbacks ℱ hℱ
  pres_covers := TF_preserves_covers_of_projective ℱ hproj
  pres_mono := TF_preserves_mono ℱ hℱ
  pres_image := TF_preserves_images ℱ hℱ hproj

end Freyd.PreLogosHorn.Stalk
