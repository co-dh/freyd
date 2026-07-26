/-
  §1.967 — Building a genuine copower-of-1 `∐ᵢ1` in a locally small topos with arbitrary powers.

  The EFFECTIVE DISJOINT UNION route.  In a topos `1+1` exists (`topos_is_positive`) and, given
  arbitrary powers `hpow`, the power `∏ᵢ(1+1)` exists.  The copower object is carved as the
  subobject `obj := ⋁ᵢ imᵢ ⊆ ∏ᵢ(1+1)`, the JOIN (`extJoin`) of the images of the candidate
  injections `cand i : 1 → ∏ᵢ(1+1)` — the tuple that is `inr` (true) at coordinate `i` and `inl`
  (false) elsewhere.  The `imᵢ` are pairwise disjoint (`1+1` disjointness), each `≅ 1`.

  STATUS: SORRY-FREE.  `inj`, `inj_cotup`, `cotup_uniq`, AND `cotup` (map-OUT existence) are all
  built without `Sorry` (`#print axioms Freyd.toposCopowerOfOne = [propext, Classical.choice,
  Quot.sound]`).

  * `cotup_uniq` (map-OUT uniqueness / jointly-epic injections) is the infinitary analogue of
    `coprod_jointly_epi` with `extJoin_least` (S1_95) for the binary `union_min`: form the
    equalizer `E = {h=k}`, show each `imᵢ ≤ E`, then `extJoin_least` forces `obj ≤ E`.  Banked as
    `copowerImages_jointly_epi`.
  * `cotup` (map-OUT EXISTENCE) is the infinitary disjoint GLUING, done honestly (no circular
    bootstrap through the binary `disjoint_cover_is_coproduct`).  The copairing is the map whose
    GRAPH is the join `G := ⋁ᵢ relSub P_i ⊆ obj × X` of the partial graphs
    `P_i := (graph (inj i))° ⊚ graph (f i)`, tabulated as a relation `obj ⇸ X`, shown TOTAL
    (`copowUnion_total`, via `copowInj_jointly_cover`) and SIMPLE (`copowUnion_simple`).
    FUNCTIONALITY is the genuine infinitary content: the §1.616 composition-over-join
    distributivity `compose_extJoin_right` (built here from STEP 1 `existsAlong_extJoin_le` +
    the §1.84 frame law `extJoin_invImage_le`) distributes `G° ⊚ G` over the join into
    `⋁ᵢⱼ (P_i° ⊚ P_j)`; the diagonal/off-diagonal bounds `P_i° ⊚ P_j ≤ 1`
    (`copowPartial_pair_le`, from `diag_le_one`/`cross_le_one` with `1+1` disjointness
    `copowInj_disjoint_maps_agree`) collapse the join into `graph (id X)`.

  Reusable lemmas banked here: `existsAlong_extJoin_le` (∃ preserves joins), `compose_extJoin_right`
  (composition distributes over arbitrary joins), `binRelSub` (subobject-as-relation).
-/
import Freyd.S1_95
import Freyd.S1_967_ToposExists
import Freyd.S1_97_ToposDistributive
import Freyd.S1_967_ToposIndexedJoins

universe u v w

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞] [LocallySmallTopos 𝒞]

open Classical

/-! ## §1.843 — `WellPoweredSub` from the subobject classifier

  Freyd §1.843: a topos is well-powered.  The cleanest elementary route does NOT need a
  progenitor or copowers: the subobject classifier gives `Sub(A) ↪ Hom(A, Ω)` directly, since
  `χ : Sub(A) → Hom(A,Ω)` is injective up to subobject-equality (`subChar S = subChar T ⟹ S ≅ T`
  via `le_iff_classify` both ways).  `Hom(A,Ω) : Type v`, so it is a `Type v` enumeration.

  This BANKS `wellPoweredSub_of_topos : WellPoweredSub 𝒞` for any `[Topos 𝒞]`, hence the
  `LocallySmallTopos.wellPowered` datum from bare Tierney data — making every copower lemma here
  (which assumes `[LocallySmallTopos 𝒞]`) applicable from just `Topos`.  Axioms:
  `[propext, Classical.choice, Quot.sound]`. -/
section WellPoweredFromClassifier
variable (𝒟 : Type u) [Cat.{v} 𝒟] [Topos 𝒟]

/-- A subobject is detected by its characteristic map: equal `χ` forces `≤` in both directions.
    `S.arr ≫ χ_S = term ≫ true` always (`le_iff_classify` at `S ≤ S`); substituting `χ_S = χ_T`
    gives `S.arr ≫ χ_T = term ≫ true`, i.e. `S ≤ T`. -/
theorem le_of_subChar_eq {A : 𝒟} {S T : Subobject 𝒟 A} (h : subChar S = subChar T) :
    S.le T := by
  have hSS : S.arr ≫ subChar S = term S.dom ≫ HasSubobjectClassifier.true :=
    (le_iff_classify S S).mp (Subobject.le_refl S)
  rw [h] at hSS
  exact (le_iff_classify S T).mpr hSS

/-- **§1.843**: every topos is well-powered.  Index `Sub(A)` by `Hom(A, Ω) : Type v`; enumerate a
    characteristic map `c` by SOME subobject with `χ = c` (if any), else the entire subobject.
    `surj S` uses `c := subChar S`, and `le_of_subChar_eq` (both ways) makes the chosen
    representative `≤`-equal to `S`. -/
noncomputable def wellPoweredSub_of_topos : WellPoweredSub.{v} 𝒟 where
  idx A := A ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒟)
  enum {A} c := if h : ∃ S : Subobject 𝒟 A, subChar S = c then h.choose else Subobject.entire A
  surj {A} S := by
    refine ⟨subChar S, ?_, ?_⟩
    · -- S ≤ enum (χ_S): the chosen rep S' has χ_S' = χ_S, so S ≤ S' by `le_of_subChar_eq`.
      have hex : ∃ S' : Subobject 𝒟 A, subChar S' = subChar S := ⟨S, rfl⟩
      show S.le (if h : ∃ S' : Subobject 𝒟 A, subChar S' = subChar S then h.choose else _)
      rw [dif_pos hex]
      exact le_of_subChar_eq 𝒟 hex.choose_spec.symm
    · have hex : ∃ S' : Subobject 𝒟 A, subChar S' = subChar S := ⟨S, rfl⟩
      show (if h : ∃ S' : Subobject 𝒟 A, subChar S' = subChar S then h.choose else _).le S
      rw [dif_pos hex]
      exact le_of_subChar_eq 𝒟 hex.choose_spec

end WellPoweredFromClassifier

section CopowerBuild

variable (hpow : HasArbitraryPowers (𝒞 := 𝒞)) (I : Type v)

/-- The ambient power `∏ᵢ(1+1)`.  `1+1` exists by `topos_is_positive`; the `I`-fold power by
    `hpow`.  The copower object will be carved as a subobject of this. -/
noncomputable def copowAmbient : 𝒞 :=
  hpow.pow I (coprodObj (one : 𝒞) (one : 𝒞))

/-- The candidate `i`-th injection `1 → ∏ᵢ(1+1)`: the tuple that is `inr` (true) at coordinate
    `i` and `inl` (false) at every other coordinate. -/
noncomputable def copowCand (i : I) : (one : 𝒞) ⟶ copowAmbient hpow I :=
  hpow.tupling (fun j => term (one : 𝒞) ≫
    (if j = i then coprodInr (one : 𝒞) (one : 𝒞) else coprodInl (one : 𝒞) (one : 𝒞)))

/-- The `i`-th injection-image `imᵢ ⊆ ∏ᵢ(1+1)`. -/
noncomputable def copowImg (i : I) : Subobject 𝒞 (copowAmbient hpow I) :=
  image (copowCand hpow I i)

/-- The carving predicate: "is one of the injection-images `imᵢ`". -/
def copowImgPred (S : Subobject 𝒞 (copowAmbient hpow I)) : Prop := ∃ i, S = copowImg hpow I i

/-- The copower object `obj := ⋁ᵢ imᵢ`, as the `extJoin` subobject of `∏ᵢ(1+1)`. -/
noncomputable def copowSub : Subobject 𝒞 (copowAmbient hpow I) :=
  extJoin hpow LocallySmallTopos.wellPowered (copowImgPred hpow I)

noncomputable def copowObj : 𝒞 := (copowSub hpow I).dom

/-- The `i`-th injection `1 → obj`.  `cand i` factors through `imᵢ` (image lift), and
    `imᵢ ≤ obj` (`extJoin_upper`), so it factors through `obj`. -/
noncomputable def copowInj (i : I) : (one : 𝒞) ⟶ copowObj hpow I :=
  image.lift (copowCand hpow I i) ≫
    (show (copowImg hpow I i).le (copowSub hpow I) from
      extJoin_upper hpow LocallySmallTopos.wellPowered _ _ ⟨i, rfl⟩).choose

/-- `inj i ≫ obj.arr = cand i`. -/
theorem copowInj_arr (i : I) :
    copowInj hpow I i ≫ (copowSub hpow I).arr = copowCand hpow I i := by
  unfold copowInj
  rw [Cat.assoc, (show (copowImg hpow I i).le (copowSub hpow I) from
    extJoin_upper hpow LocallySmallTopos.wellPowered _ _ ⟨i, rfl⟩).choose_spec]
  exact image.lift_fac (copowCand hpow I i)

/-- **`cotup_uniq` (jointly-epic injections).**  Two maps `obj → X` agreeing on every `inj i`
    are equal.  This is the infinitary analogue of `coprod_jointly_epi` (ToposExists): form the
    equalizer `E = {h=k} ↪ obj`; each `imᵢ` (as a subobject of the ambient `∏ᵢ(1+1)`) lies in
    the push-forward `EP` of `E` (because `inj i` factors through `E` by agreement); then
    `extJoin_least` forces `obj = ⋁ᵢ imᵢ ≤ EP`, exhibiting `eqMap h k` as split epi — hence an
    iso (it is monic), so `h = k`.  Bankable, Sorry-free. -/
theorem copowerImages_jointly_epi {X : 𝒞} (h k : copowObj hpow I ⟶ X)
    (hagree : ∀ i, copowInj hpow I i ≫ h = copowInj hpow I i ≫ k) : h = k := by
  -- E = equalizer of h, k, with monic inclusion `eqMap h k : E ↪ obj`.
  have heM : Monic (eqMap h k) := by
    intro W u v huv
    have hc : (u ≫ eqMap h k) ≫ h = (u ≫ eqMap h k) ≫ k := by
      rw [Cat.assoc, Cat.assoc, eqMap_eq]
    rw [eqLift_uniq h k _ hc u rfl, eqLift_uniq h k _ hc v huv.symm]
  -- push E forward into the ambient `∏ᵢ(1+1)`:  EP = ⟨E, eqMap ≫ obj.arr⟩.
  have hEPm : Monic (eqMap h k ≫ (copowSub hpow I).arr) := by
    intro W u v huv
    refine heM u v ((copowSub hpow I).monic _ _ ?_)
    rw [Cat.assoc, Cat.assoc, huv]
  let EP : Subobject 𝒞 (copowAmbient hpow I) := ⟨eqObj h k, eqMap h k ≫ (copowSub hpow I).arr, hEPm⟩
  -- each `imᵢ ≤ EP`: `inj i` factors through E (agreement), so `cand i` factors through EP.
  have himg_le : ∀ i, (copowImg hpow I i).le EP := by
    intro i
    -- li : 1 → E with li ≫ eqMap = inj i.
    let li : (one : 𝒞) ⟶ eqObj h k := eqLift h k (copowInj hpow I i) (hagree i)
    have hli : li ≫ eqMap h k = copowInj hpow I i := eqLift_fac h k _ (hagree i)
    -- cand i factors through EP directly via `li` (EP.dom = eqObj h k).
    refine image_min (copowCand hpow I i) EP ⟨li, ?_⟩
    show li ≫ (eqMap h k ≫ (copowSub hpow I).arr) = copowCand hpow I i
    -- li ≫ (eqMap ≫ obj.arr) = inj i ≫ obj.arr = cand i.
    rw [← Cat.assoc, hli, copowInj_arr]
  -- extJoin_least: obj = ⋁ᵢ imᵢ ≤ EP.
  have hobj_le : (copowSub hpow I).le EP :=
    extJoin_least hpow LocallySmallTopos.wellPowered _ EP
      (fun s ⟨i, hsi⟩ => hsi ▸ himg_le i)
  obtain ⟨w, hw⟩ := hobj_le
  -- hw : w ≫ (eqMap h k ≫ obj.arr) = obj.arr.  Cancel the monic obj.arr ⟹ w ≫ eqMap = id.
  have hwe : w ≫ eqMap h k = Cat.id (copowObj hpow I) := by
    apply (copowSub hpow I).monic
    rw [Cat.assoc]
    show w ≫ (eqMap h k ≫ (copowSub hpow I).arr) = Cat.id (copowObj hpow I) ≫ (copowSub hpow I).arr
    rw [Cat.id_comp]; exact hw
  -- w ≫ eqMap = id obj ⟹ split epi; with the equalizer law cancel to h = k.
  have heq_hk : eqMap h k ≫ h = eqMap h k ≫ k := eqMap_eq h k
  calc h = (w ≫ eqMap h k) ≫ h := by rw [hwe]; exact (Cat.id_comp h).symm
    _ = w ≫ (eqMap h k ≫ h) := Cat.assoc _ _ _
    _ = w ≫ (eqMap h k ≫ k) := by rw [heq_hk]
    _ = (w ≫ eqMap h k) ≫ k := (Cat.assoc _ _ _).symm
    _ = k := by rw [hwe]; exact Cat.id_comp k

/-- **TOTALITY — the injections jointly cover `obj`.**  A monic `m : C ↣ obj` through which
    every `inj i` factors is an isomorphism.  Same `extJoin_least` argument as
    `copowerImages_jointly_epi`: push `m` forward to the ambient `∏ᵢ(1+1)`, each `imᵢ` lies in
    the push-forward (the lift of `inj i` through `m`), so `extJoin_least` forces `obj ≤`
    push-forward, exhibiting `m` as split epi — hence iso.  Bankable, Sorry-free. -/
theorem copowInj_jointly_cover {C : 𝒞} (m : C ⟶ copowObj hpow I) (hm : Monic m)
    (s : I → ((one : 𝒞) ⟶ C)) (hs : ∀ i, s i ≫ m = copowInj hpow I i) : IsIso m := by
  -- push `m` (subobject of obj) forward to the ambient: MP = ⟨C, m ≫ obj.arr⟩.
  have hMPm : Monic (m ≫ (copowSub hpow I).arr) := by
    intro W u v huv
    refine hm u v ((copowSub hpow I).monic _ _ ?_)
    rw [Cat.assoc, Cat.assoc, huv]
  let MP : Subobject 𝒞 (copowAmbient hpow I) := ⟨C, m ≫ (copowSub hpow I).arr, hMPm⟩
  -- each imᵢ ≤ MP: cand i factors through MP via s i (since s i ≫ m ≫ obj.arr = inj i ≫ obj.arr).
  have himg_le : ∀ i, (copowImg hpow I i).le MP := by
    intro i
    refine image_min (copowCand hpow I i) MP ⟨s i, ?_⟩
    show s i ≫ (m ≫ (copowSub hpow I).arr) = copowCand hpow I i
    rw [← Cat.assoc, hs i, copowInj_arr]
  -- extJoin_least: obj ≤ MP.
  have hobj_le : (copowSub hpow I).le MP :=
    extJoin_least hpow LocallySmallTopos.wellPowered _ MP
      (fun t ⟨i, hti⟩ => hti ▸ himg_le i)
  obtain ⟨w, hw⟩ := hobj_le
  -- hw : w ≫ (m ≫ obj.arr) = obj.arr.  Cancel monic obj.arr ⟹ w ≫ m = id obj.
  have hwm : w ≫ m = Cat.id (copowObj hpow I) := by
    apply (copowSub hpow I).monic
    rw [Cat.assoc]
    show w ≫ (m ≫ (copowSub hpow I).arr) = Cat.id (copowObj hpow I) ≫ (copowSub hpow I).arr
    rw [Cat.id_comp]; exact hw
  -- m ≫ w = id C: cancel monic m on (m ≫ w) ≫ m = m ≫ (w ≫ m) = m = id ≫ m.
  have hmw : m ≫ w = Cat.id C :=
    hm _ _ (by rw [Cat.assoc, hwm, Cat.comp_id, Cat.id_comp])
  exact ⟨w, hmw, hwm⟩

/-! ### STEP 1 — direct image preserves arbitrary joins

  `∃_g (⋁ S) ≤ ⋁ (∃_g '' S)`.  The infinitary analogue of `existsAlong_union_le` (S1_60),
  proven via the `∃_g ⊣ g#` Galois connection (`existsAlong_adj`, S1_60) with
  `extJoin_upper`/`extJoin_least` (S1_95) in place of the binary union laws. -/
theorem existsAlong_extJoin_le {A B : 𝒞} (g : A ⟶ B) (S : Subobject 𝒞 A → Prop) :
    (existsAlong g (extJoin hpow LocallySmallTopos.wellPowered S)).le
      (extJoin hpow LocallySmallTopos.wellPowered
        (fun V => ∃ s, S s ∧ V = existsAlong g s)) := by
  let V := extJoin hpow LocallySmallTopos.wellPowered (fun V => ∃ s, S s ∧ V = existsAlong g s)
  -- By the adjunction: suffices  extJoin S ≤ g# V.
  refine (existsAlong_adj g (extJoin hpow LocallySmallTopos.wellPowered S) V).2 ?_
  -- `extJoin_least`: each member `s` of `S` lies below `g# V`.
  refine extJoin_least hpow LocallySmallTopos.wellPowered S _ (fun s hs => ?_)
  -- s ≤ g# V  ↔  ∃_g s ≤ V; and ∃_g s IS a member of the image-predicate, so `extJoin_upper`.
  exact (existsAlong_adj g s V).1
    (extJoin_upper hpow LocallySmallTopos.wellPowered _ (existsAlong g s) ⟨s, hs, rfl⟩)

/-- A subobject of `A × B` viewed as a relation `A ⇸ B` (legs = `arr ≫ fst`, `arr ≫ snd`). -/
noncomputable def binRelSub {A B : 𝒞} (W : Subobject 𝒞 (prod A B)) : BinRel 𝒞 A B := subRel W

theorem relSub_binRelSub_le {A B : 𝒞} (W : Subobject 𝒞 (prod A B)) :
    (relSub (binRelSub W)).le W :=
  ⟨Cat.id _, by rw [Cat.id_comp, show (relSub (binRelSub W)).arr = W.arr from relSub_subRel_arr W]⟩

theorem binRelSub_relSub_le {A B : 𝒞} (W : Subobject 𝒞 (prod A B)) :
    W.le (relSub (binRelSub W)) :=
  ⟨Cat.id _, by rw [Cat.id_comp, show (relSub (binRelSub W)).arr = W.arr from relSub_subRel_arr W]⟩

/-- **Monotone in the predicate** for `extJoin`: if every member of `P` lies below some member of
    `Q`, then `extJoin P ≤ extJoin Q`. -/
theorem extJoin_mono_pred {A : 𝒞} {P Q : Subobject 𝒞 A → Prop}
    (h : ∀ s, P s → ∃ t, Q t ∧ s.le t) :
    (extJoin hpow LocallySmallTopos.wellPowered P).le
      (extJoin hpow LocallySmallTopos.wellPowered Q) := by
  refine extJoin_least hpow LocallySmallTopos.wellPowered P _ (fun s hs => ?_)
  obtain ⟨t, hQt, hst⟩ := h s hs
  exact Subobject.le_trans hst (extJoin_upper hpow LocallySmallTopos.wellPowered Q t hQt)

/-! ### STEP 2 — composition distributes over arbitrary joins (right)

  `R ⊚ (⋁ᵢ Wᵢ) ≤ ⋁ᵢ (R ⊚ Wᵢ)` at the subobject level, where `Wᵢ ⊆ B × C` range over the
  predicate `S`, `extJoin S ⊆ B × C` is their join, and a subobject of a product is read as a
  relation via `binRelSub`.  The infinitary analogue of `compose_union_right` (S1_60): both
  factors of `compose = ∃_ω ∘ θ#` (`relSub_compose_eq`) preserve arbitrary joins —
  `θ#` by the §1.84 frame law `extJoin_invImage_le` (S1_95), `∃_ω` by STEP 1. -/
theorem compose_extJoin_right {A B C : 𝒞} (R : BinRel 𝒞 A B)
    (S : Subobject 𝒞 (prod B C) → Prop) :
    (relSub (R ⊚ binRelSub (extJoin hpow LocallySmallTopos.wellPowered S))).le
      (extJoin hpow LocallySmallTopos.wellPowered
        (fun U => ∃ W, S W ∧ U = relSub (R ⊚ binRelSub W))) := by
  let wp := LocallySmallTopos.wellPowered (𝒞 := 𝒞)
  -- LHS = ∃_ω (θ# relSub(binRelSub (extJoin S))) = ∃_ω (θ# (extJoin S)).
  have hL := (relSub_compose_eq R (binRelSub (extJoin hpow wp S))).1
  -- relSub(binRelSub (extJoin S)) ≤ extJoin S, so θ# of it ≤ θ#(extJoin S), and ∃_ω monotone.
  have hstep : (existsAlong (omegaR R C)
        (InverseImage (thetaR R C) (relSub (binRelSub (extJoin hpow wp S))))).le
      (existsAlong (omegaR R C)
        (InverseImage (thetaR R C) (extJoin hpow wp S))) :=
    existsAlong_mono (omegaR R C)
      (inverseImage_mono (thetaR R C) (relSub_binRelSub_le (extJoin hpow wp S)))
  -- θ#(extJoin S) ≤ extJoin {θ# W}.
  have hframe := extJoin_invImage_le hpow wp (thetaR R C) S
  have h2 : (existsAlong (omegaR R C) (InverseImage (thetaR R C) (extJoin hpow wp S))).le
      (existsAlong (omegaR R C)
        (extJoin hpow wp
          (fun A' => ∃ W, S W ∧ A' = InverseImage (thetaR R C) (relSub (binRelSub W))))) := by
    refine existsAlong_mono (omegaR R C) (Subobject.le_trans hframe ?_)
    -- rewrite the inner predicate (θ# W vs θ#(relSub(binRelSub W))) — they coincide since
    -- relSub(binRelSub W) = W as subobjects.  Use `extJoin_mono_pred`.
    refine extJoin_mono_pred hpow (fun s ⟨W, hSW, hs⟩ => ?_)
    exact ⟨_, ⟨W, hSW, rfl⟩,
      hs ▸ inverseImage_mono (thetaR R C) (binRelSub_relSub_le W)⟩
  -- ∃_ω (extJoin {θ#(relSub(binRelSub W))}) ≤ extJoin {∃_ω (θ#(relSub(binRelSub W)))}.
  have h3 := existsAlong_extJoin_le hpow (omegaR R C)
    (fun A' => ∃ W, S W ∧ A' = InverseImage (thetaR R C) (relSub (binRelSub W)))
  -- each ∃_ω (θ#(relSub(binRelSub W))) = relSub(R ⊚ binRelSub W)  (reverse `relSub_compose_eq`).
  have h4 : (extJoin hpow wp
        (fun V => ∃ s,
          (∃ W, S W ∧ s = InverseImage (thetaR R C) (relSub (binRelSub W)))
          ∧ V = existsAlong (omegaR R C) s)).le
      (extJoin hpow wp (fun U => ∃ W, S W ∧ U = relSub (R ⊚ binRelSub W))) := by
    refine extJoin_mono_pred hpow (fun V ⟨s, ⟨W, hSW, hsW⟩, hV⟩ => ?_)
    refine ⟨relSub (R ⊚ binRelSub W), ⟨W, hSW, rfl⟩, ?_⟩
    -- V = ∃_ω s = ∃_ω(θ#(relSub(binRelSub W))) ≤ relSub(R ⊚ binRelSub W) by reverse compose_eq.
    rw [hV, hsW]
    exact (relSub_compose_eq R (binRelSub W)).2
  exact Subobject.le_trans hL (Subobject.le_trans hstep (Subobject.le_trans h2 (Subobject.le_trans h3 h4)))

/-- `binRelSub (relSub R)` is relationally equal to `R` (round-trip). -/
theorem binRelSub_relSub_relLe {A B : 𝒞} (R : BinRel 𝒞 A B) :
    RelLe (binRelSub (relSub R)) R ∧ RelLe R (binRelSub (relSub R)) :=
  ⟨(relLe_iff_subLe (binRelSub (relSub R)) R).2 (relSub_binRelSub_le (relSub R)),
   (relLe_iff_subLe R (binRelSub (relSub R))).2 (binRelSub_relSub_le (relSub R))⟩

/-! ### STEP 3 — disjointness of distinct injection-images

  For `i ≠ j` the candidate points `cand i`, `cand j` differ at coordinate `i` (`inr` vs `inl`),
  so a common point of `inj i`, `inj j` maps to the pullback of `coprodInl`/`coprodInr` at that
  coordinate — which is `≅ 0` (`coprodInjections_disjoint`).  Hence the apex of the pullback of
  `(inj i, inj j)` admits a map to `0`, so it is `≅ 0`, so any two maps out of it agree.  This
  supplies the cocone equation `π₁ ≫ f i = π₂ ≫ f j` that the cross-term `cross_le_one` needs. -/

/-- A common point of `inj i`, `inj j` (`i ≠ j`) yields a map from the pullback apex to the
    `(coprodInl, coprodInr)` pullback apex: at coordinate `i`, `cand i` is `inr` and `cand j` is
    `inl`. -/
theorem copowInj_disjoint_apex_map {i j : I} (hij : i ≠ j) :
    ∃ _ : (HasPullbacks.has (copowInj hpow I i) (copowInj hpow I j)).cone.pt ⟶
        (HasPullbacks.has (coprodInl (one : 𝒞) (one : 𝒞))
          (coprodInr (one : 𝒞) (one : 𝒞))).cone.pt, True := by
  let pb := HasPullbacks.has (copowInj hpow I i) (copowInj hpow I j)
  let P := pb.cone.pt
  -- π₁ ≫ inj i = π₂ ≫ inj j, post-compose obj.arr ⟹ π₁ ≫ cand i = π₂ ≫ cand j.
  have hsq : pb.cone.π₁ ≫ copowInj hpow I i = pb.cone.π₂ ≫ copowInj hpow I j := pb.cone.w
  have hcand : pb.cone.π₁ ≫ copowCand hpow I i = pb.cone.π₂ ≫ copowCand hpow I j := by
    rw [← copowInj_arr hpow I i, ← copowInj_arr hpow I j, ← Cat.assoc, ← Cat.assoc, hsq]
  -- project to coordinate i.
  have hproj : (pb.cone.π₁ ≫ term (one : 𝒞)) ≫ coprodInr (one : 𝒞) (one : 𝒞)
      = (pb.cone.π₂ ≫ term (one : 𝒞)) ≫ coprodInl (one : 𝒞) (one : 𝒞) := by
    have h := congrArg (· ≫ hpow.proj i) hcand
    simp only at h
    rw [Cat.assoc, Cat.assoc, copowCand, copowCand, hpow.tupling_proj, hpow.tupling_proj] at h
    simp only [if_neg hij] at h
    -- h : π₁ ≫ (term ≫ inr) = π₂ ≫ (term ≫ inl)
    rw [← Cat.assoc, ← Cat.assoc] at h
    exact h
  -- term P collapses both prefactors; produce a cone over (inl, inr).
  have hcollapse : term P ≫ coprodInr (one : 𝒞) (one : 𝒞)
      = term P ≫ coprodInl (one : 𝒞) (one : 𝒞) := by
    rw [show (term P : P ⟶ (one : 𝒞)) = pb.cone.π₁ ≫ term (one : 𝒞) from term_uniq _ _] at *
    rw [show (pb.cone.π₂ ≫ term (one : 𝒞) : P ⟶ (one : 𝒞)) = pb.cone.π₁ ≫ term (one : 𝒞)
        from term_uniq _ _] at hproj
    exact hproj
  let pbC := HasPullbacks.has (coprodInl (one : 𝒞) (one : 𝒞)) (coprodInr (one : 𝒞) (one : 𝒞))
  let c : Cone (coprodInl (one : 𝒞) (one : 𝒞)) (coprodInr (one : 𝒞) (one : 𝒞)) :=
    ⟨P, term P, term P, hcollapse.symm⟩
  exact ⟨pbC.lift c, trivial⟩

/-- For `i ≠ j`, any two maps out of the `(inj i, inj j)` pullback apex agree (the apex is `≅ 0`
    via `coprodInjections_disjoint` + `any_map_to_zero_is_iso`). -/
theorem copowInj_disjoint_maps_agree {i j : I} (hij : i ≠ j) {Z : 𝒞}
    (u v : (HasPullbacks.has (copowInj hpow I i) (copowInj hpow I j)).cone.pt ⟶ Z) : u = v := by
  obtain ⟨δ, _⟩ := copowInj_disjoint_apex_map hpow I hij
  -- apex of (inl, inr) pullback ≅ bottomSub(coprodObj 1 1).dom ≅ 0; compose δ to land in 0.
  obtain ⟨e, he_iso⟩ := coprodInjections_disjoint (one : 𝒞) (one : 𝒞)
  -- e : pbC.apex → (bottomSub (coprodObj 1 1)).dom ;  then to (bottomSub 1).dom via dom-iso.
  obtain ⟨θ, hθ⟩ := bottomSub_dom_iso (coprodObj (one : 𝒞) (one : 𝒞)) (one : 𝒞)
  let z : (HasPullbacks.has (copowInj hpow I i) (copowInj hpow I j)).cone.pt
      ⟶ (bottomSub (one : 𝒞)).dom := δ ≫ e ≫ θ
  -- (bottomSub 1).dom = (PreLogos.bottom 1).dom = coterminator zero;  any map to 0 is iso.
  have hz_iso : IsIso z := any_map_to_zero_is_iso (inferInstance : PreLogos 𝒞) z
  -- z iso ⟹ apex ≅ 0 ⟹ any two maps out agree (precompose z⁻¹ and use init_uniq).
  obtain ⟨zinv, hzz, hzinv⟩ := hz_iso
  let ct := minimal_subobject_of_one_is_coterminator (inferInstance : PreLogos 𝒞)
  calc u = (z ≫ zinv) ≫ u := by rw [hzz, Cat.id_comp]
    _ = z ≫ (zinv ≫ u) := Cat.assoc _ _ _
    _ = z ≫ (zinv ≫ v) := by rw [ct.init_uniq (zinv ≫ u) (zinv ≫ v)]
    _ = (z ≫ zinv) ≫ v := (Cat.assoc _ _ _).symm
    _ = v := by rw [hzz, Cat.id_comp]

/-- **Generic collapse.**  An object `P` whose terminal map collapses the distinct copower
    injections (`term P ≫ inj i = term P ≫ inj j`, `i ≠ j`) is zero-like: any two maps out of `P`
    agree.  The apex-of-pullback case (`copowInj_disjoint_maps_agree`) is the instance
    `P = pullback(inj i, inj j).pt`.  Used to transport copower disjointness to ambient products in
    the general-coproduct carving. -/
theorem copowInj_collapse_maps_agree {i j : I} (hij : i ≠ j) {P : 𝒞}
    (hcol : term P ≫ copowInj hpow I i = term P ≫ copowInj hpow I j) {Z : 𝒞}
    (u v : P ⟶ Z) : u = v := by
  -- project the collapse to coordinate i: term P ≫ inr = term P ≫ inl in `1+1`.
  have hcand : term P ≫ copowCand hpow I i = term P ≫ copowCand hpow I j := by
    rw [← copowInj_arr hpow I i, ← copowInj_arr hpow I j, ← Cat.assoc, ← Cat.assoc, hcol]
  have hproj : (term P ≫ term (one : 𝒞)) ≫ coprodInr (one : 𝒞) (one : 𝒞)
      = (term P ≫ term (one : 𝒞)) ≫ coprodInl (one : 𝒞) (one : 𝒞) := by
    have h := congrArg (· ≫ hpow.proj i) hcand
    simp only at h
    rw [Cat.assoc, Cat.assoc, copowCand, copowCand, hpow.tupling_proj, hpow.tupling_proj] at h
    simp only [if_neg hij] at h
    rw [← Cat.assoc, ← Cat.assoc] at h
    exact h
  have hcollapse : term P ≫ coprodInr (one : 𝒞) (one : 𝒞)
      = term P ≫ coprodInl (one : 𝒞) (one : 𝒞) := by
    rw [show (term P ≫ term (one : 𝒞) : P ⟶ (one : 𝒞)) = term P from term_uniq _ _] at hproj
    exact hproj
  let pbC := HasPullbacks.has (coprodInl (one : 𝒞) (one : 𝒞)) (coprodInr (one : 𝒞) (one : 𝒞))
  let c : Cone (coprodInl (one : 𝒞) (one : 𝒞)) (coprodInr (one : 𝒞) (one : 𝒞)) :=
    ⟨P, term P, term P, hcollapse.symm⟩
  let δ : P ⟶ pbC.cone.pt := pbC.lift c
  obtain ⟨e, _⟩ := coprodInjections_disjoint (one : 𝒞) (one : 𝒞)
  obtain ⟨θ, _⟩ := bottomSub_dom_iso (coprodObj (one : 𝒞) (one : 𝒞)) (one : 𝒞)
  let z : P ⟶ (bottomSub (one : 𝒞)).dom := δ ≫ e ≫ θ
  obtain ⟨zinv, hzz, _⟩ := any_map_to_zero_is_iso (inferInstance : PreLogos 𝒞) z
  let ct := minimal_subobject_of_one_is_coterminator (inferInstance : PreLogos 𝒞)
  calc u = (z ≫ zinv) ≫ u := by rw [hzz, Cat.id_comp]
    _ = z ≫ (zinv ≫ u) := Cat.assoc _ _ _
    _ = z ≫ (zinv ≫ v) := by rw [ct.init_uniq (zinv ≫ u) (zinv ≫ v)]
    _ = (z ≫ zinv) ≫ v := (Cat.assoc _ _ _).symm
    _ = v := by rw [hzz, Cat.id_comp]

/-! ### STEP 4 — the map-OUT (cotupling) via the infinitary disjoint gluing

  `cotup f : obj → X` is built as the unique map whose GRAPH is the join of the `I` partial
  graphs.  Each partial graph is the relation `P_i := (graph (inj i))° ⊚ graph (f i) : obj ⇸ X`
  (the graph of "defined on `imᵢ`, value `f i`").  The relation `G := binRelSub (⋁ᵢ relSub P_i)`
  tabulated by their join is shown TOTAL (left leg a cover — `copowInj_jointly_cover`) and SIMPLE
  (left leg monic — functionality).

  Functionality is the honest infinitary content: `compose_extJoin_right` (STEP 2) distributes
  `G° ⊚ G` over the join into `⋁ⱼ (G° ⊚ P_j)`, and a second distribution reduces each
  `G° ⊚ P_j` to `⋁ᵢ (P_i° ⊚ P_j)` (via reciprocals); the diagonal terms `P_i° ⊚ P_i ≤ 1`
  (`diag_le_one`, `inj i` monic) and the off-diagonal `P_i° ⊚ P_j ≤ 1` (`cross_le_one`, from
  `1+1` disjointness `copowInj_disjoint_maps_agree`) collapse the join into `graph (id X)`. -/

/-- The `i`-th partial-graph relation `obj ⇸ X`: graph of "defined on `imᵢ`, value `f i`". -/
noncomputable def copowPartial {X : 𝒞} (f : I → ((one : 𝒞) ⟶ X)) (i : I) :
    BinRel 𝒞 (copowObj hpow I) X :=
  (graph (copowInj hpow I i))° ⊚ graph (f i)

/-- **The canonical point** of the partial graph `P_i = (graph (inj i))° ⊚ graph (f i)`:
    the pullback over `(id_1, id_1)` has the obvious point `id_1`, whose span value is
    `pair (inj i) (f i)`.  Gives `q : 1 → P_i.src` with `q ≫ pair P_i.colA P_i.colB
    = pair (inj i) (f i)` (so `P_i` "contains" the point `(inj i, f i)`). -/
theorem copowPartial_point {X : 𝒞} (f : I → ((one : 𝒞) ⟶ X)) (i : I) :
    ∃ q : (one : 𝒞) ⟶ (copowPartial hpow I f i).src,
      q ≫ (copowPartial hpow I f i).colA = copowInj hpow I i ∧
      q ≫ (copowPartial hpow I f i).colB = f i := by
  -- unfold the composition `(graph (inj i))° ⊚ graph (f i)`.
  let xr : BinRel 𝒞 (copowObj hpow I) (one : 𝒞) := (graph (copowInj hpow I i))°
  let yr : BinRel 𝒞 (one : 𝒞) X := graph (f i)
  -- pb = pullback (xr.colB, yr.colA) = pullback (id_1, id_1).
  let pb := HasPullbacks.has xr.colB yr.colA
  have hcw : (Cat.id (one : 𝒞)) ≫ xr.colB = (Cat.id (one : 𝒞)) ≫ yr.colA := by
    show (Cat.id (one : 𝒞)) ≫ Cat.id (one : 𝒞) = (Cat.id (one : 𝒞)) ≫ Cat.id (one : 𝒞); rfl
  let c : Cone xr.colB yr.colA := ⟨(one : 𝒞), Cat.id (one : 𝒞), Cat.id (one : 𝒞), hcw⟩
  let u : (one : 𝒞) ⟶ pb.cone.pt := pb.lift c
  have hu₁ : u ≫ pb.cone.π₁ = Cat.id (one : 𝒞) := pb.lift_fst c
  have hu₂ : u ≫ pb.cone.π₂ = Cat.id (one : 𝒞) := pb.lift_snd c
  let span : pb.cone.pt ⟶ prod (copowObj hpow I) X :=
    pair (pb.cone.π₁ ≫ xr.colA) (pb.cone.π₂ ≫ yr.colB)
  refine ⟨u ≫ image.lift span, ?_, ?_⟩
  · -- (u ≫ lift) ≫ (P_i.colA = (image span).arr ≫ fst) = u ≫ span ≫ fst = u ≫ π₁ ≫ inj i = inj i.
    show (u ≫ image.lift span) ≫ ((image span).arr ≫ fst) = copowInj hpow I i
    have hfac : (u ≫ image.lift span) ≫ ((image span).arr ≫ fst) = u ≫ (span ≫ fst) := by
      rw [← Cat.assoc, Cat.assoc u, image.lift_fac, Cat.assoc]
    rw [hfac, show span ≫ fst = pb.cone.π₁ ≫ xr.colA from fst_pair _ _, ← Cat.assoc, hu₁,
      Cat.id_comp]
    rfl
  · show (u ≫ image.lift span) ≫ ((image span).arr ≫ snd) = f i
    have hfac : (u ≫ image.lift span) ≫ ((image span).arr ≫ snd) = u ≫ (span ≫ snd) := by
      rw [← Cat.assoc, Cat.assoc u, image.lift_fac, Cat.assoc]
    rw [hfac, show span ≫ snd = pb.cone.π₂ ≫ yr.colB from snd_pair _ _, ← Cat.assoc, hu₂,
      Cat.id_comp]
    rfl

/-- **Per-pair atomic bound.**  `P_i° ⊚ P_j ≤ graph (id X)` for all `i, j` — single-valuedness of
    the union of partial graphs.  Diagonal: `diag_le_one`.  Off-diagonal: `cross_le_one` with the
    cocone equation from disjointness (`copowInj_disjoint_maps_agree`). -/
theorem copowPartial_pair_le {X : 𝒞} (f : I → ((one : 𝒞) ⟶ X)) (i j : I) :
    RelLe ((copowPartial hpow I f i)° ⊚ (copowPartial hpow I f j)) (graph (Cat.id X)) := by
  by_cases hij : i = j
  · subst hij
    -- diagonal: P_i° ⊚ P_i ≤ 1  with  P_i = (inj i)° ⊚ (f i).
    exact diag_le_one (copowInj hpow I i) (f i) (fun u v _ => term_uniq u v)
  · -- cross term: needs `hxyg : (inj i ⊚ (inj j)°) ⊚ (f j) ≤ (f i)` from disjointness.
    let pb := HasPullbacks.has (copowInj hpow I i) (copowInj hpow I j)
    have hinter : RelLe (graph (copowInj hpow I i) ⊚ (graph (copowInj hpow I j))°)
        ((graph pb.cone.π₁)° ⊚ graph pb.cone.π₂) :=
      inter_lemma (copowInj hpow I i) (copowInj hpow I j) (Cat.id (copowObj hpow I))
        (copowInj hpow I i) (copowInj hpow I j) (Cat.comp_id _) (Cat.comp_id _)
    have hw : pb.cone.π₁ ≫ f i = pb.cone.π₂ ≫ f j :=
      copowInj_disjoint_maps_agree hpow I hij _ _
    have hxyg : RelLe ((graph (copowInj hpow I i) ⊚ (graph (copowInj hpow I j))°) ⊚ graph (f j))
        (graph (f i)) :=
      hxyg_lemma (f i) (f j) pb.cone.π₁ pb.cone.π₂
        (graph (copowInj hpow I i) ⊚ (graph (copowInj hpow I j))°) hinter hw
    exact cross_le_one (copowInj hpow I i) (copowInj hpow I j) (f i) (f j) hxyg

/-- **FUNCTIONALITY (simplicity).**  The union relation `G = binRelSub (⋁ᵢ relSub P_i)` is simple:
    `G° ⊚ G ≤ graph (id X)`.  Distribute the join twice (STEP 2 `compose_extJoin_right`), collapse
    each `P_i° ⊚ P_j` by `copowPartial_pair_le`. -/
theorem copowUnion_simple {X : 𝒞} (f : I → ((one : 𝒞) ⟶ X)) :
    Simple (binRelSub (extJoin hpow LocallySmallTopos.wellPowered
      (fun U => ∃ i, U = relSub (copowPartial hpow I f i)))) := by
  let wp := LocallySmallTopos.wellPowered (𝒞 := 𝒞)
  let S : Subobject 𝒞 (prod (copowObj hpow I) X) → Prop :=
    fun U => ∃ i, U = relSub (copowPartial hpow I f i)
  let G : BinRel 𝒞 (copowObj hpow I) X := binRelSub (extJoin hpow wp S)
  -- A reusable bound: `T ⊚ binRelSub W ≤ graph id` whenever each `T ⊚ P_i ≤ graph id` and W∈S.
  -- We need: for each W with S W, `G° ⊚ binRelSub W ≤ graph (id X)`.
  -- Reduce via reciprocal to `(binRelSub W)° ⊚ G ≤ graph id`, then distribute G's join.
  have key : ∀ (T : BinRel 𝒞 X (copowObj hpow I)),
      (∀ i, RelLe (T ⊚ binRelSub (relSub (copowPartial hpow I f i)))
        (graph (Cat.id X))) →
      RelLe (T ⊚ G) (graph (Cat.id X)) := by
    intro T hpieces
    -- T ⊚ G = T ⊚ binRelSub(extJoin S) ≤ ⋁ {relSub (T ⊚ binRelSub W) | S W}  (STEP 2).
    have hdist := compose_extJoin_right hpow T S
    -- the join ≤ relSub(graph id), since each member ≤ relSub(graph id).
    have hbound : (extJoin hpow wp
          (fun U => ∃ W, S W ∧ U = relSub (T ⊚ binRelSub W))).le
        (relSub (graph (Cat.id X))) := by
      refine extJoin_least hpow wp _ (relSub (graph (Cat.id X))) (fun U hmem => ?_)
      obtain ⟨W, ⟨i, hWi⟩, hU⟩ := hmem
      rw [hU, hWi]
      exact subLe_of_relLe (hpieces i)
    exact (relLe_iff_subLe (T ⊚ G) (graph (Cat.id X))).2 (Subobject.le_trans hdist hbound)
  -- Now Simple G : G° ⊚ G ≤ graph (id X).  Apply `key` with T := G°.
  show RelLe (G° ⊚ G) (graph (Cat.id X))
  refine key (G°) (fun i => ?_)
  -- G° ⊚ binRelSub(relSub P_i) ≤ graph id  via reciprocal + a second distribution.
  -- reciprocal: (G° ⊚ binRelSub(relSub P_i))° = (binRelSub(relSub P_i))° ⊚ G.
  have hrecip : RelLe ((G° ⊚ binRelSub (relSub (copowPartial hpow I f i)))°)
      ((binRelSub (relSub (copowPartial hpow I f i)))° ⊚ G) := by
    have h := (reciprocal_comp (G°) (binRelSub (relSub (copowPartial hpow I f i)))).1
    rwa [reciprocal_invol] at h
  -- (binRelSub(relSub P_i))° ⊚ G ≤ graph id  via `key` with T := (binRelSub(relSub P_i))°.
  have hPiG : RelLe ((binRelSub (relSub (copowPartial hpow I f i)))° ⊚ G)
      (graph (Cat.id X)) := by
    refine key ((binRelSub (relSub (copowPartial hpow I f i)))°) (fun j => ?_)
    -- (binRelSub(relSub P_i))° ⊚ binRelSub(relSub P_j) ≤ P_i° ⊚ P_j ≤ graph id.
    refine rel_le_trans (compose_le (reciprocal_mono (binRelSub_relSub_relLe _).1)
      (binRelSub_relSub_relLe _).1) ?_
    exact copowPartial_pair_le hpow I f i j
  -- so (G° ⊚ binRelSub(relSub P_i))° ≤ graph id; take reciprocal, (graph id)° = graph id.
  have hco : RelLe ((G° ⊚ binRelSub (relSub (copowPartial hpow I f i)))°)
      (graph (Cat.id X)) := rel_le_trans hrecip hPiG
  have h2 := reciprocal_mono hco
  rwa [reciprocal_invol, show (graph (Cat.id X))° = graph (Cat.id X) from rfl] at h2

/-- **TOTALITY.**  The left leg of `G` is a cover: each `inj i` factors through it (`P_i`'s
    first leg lifts into the join), and `copowInj_jointly_cover` forces iso. -/
theorem copowUnion_total {X : 𝒞} (f : I → ((one : 𝒞) ⟶ X)) :
    Cover (binRelSub (extJoin hpow LocallySmallTopos.wellPowered
      (fun U => ∃ i, U = relSub (copowPartial hpow I f i)))).colA := by
  let wp := LocallySmallTopos.wellPowered (𝒞 := 𝒞)
  let S : Subobject 𝒞 (prod (copowObj hpow I) X) → Prop :=
    fun U => ∃ i, U = relSub (copowPartial hpow I f i)
  let G : BinRel 𝒞 (copowObj hpow I) X := binRelSub (extJoin hpow wp S)
  -- factor each `inj i` through `G.colA`.  P_i = (inj i)° ⊚ (f i): its image contains the point
  -- (inj i, f i); so `pair (inj i) (f i)` factors through relSub P_i ≤ extJoin S = G.src, and
  -- the first leg recovers `inj i`.
  -- A direct factorization: `s i : 1 → G.src` with `s i ≫ G.colA = inj i`.
  have hfactor : ∀ i, ∃ s : (one : 𝒞) ⟶ G.src, s ≫ G.colA = copowInj hpow I i := by
    intro i
    -- the canonical point of P_i, with `q ≫ P_i.colA = inj i`, `q ≫ P_i.colB = f i`.
    obtain ⟨q, hqA, hqB⟩ := copowPartial_point hpow I f i
    have hq : q ≫ (relSub (copowPartial hpow I f i)).arr = pair (copowInj hpow I i) (f i) := by
      show q ≫ pair (copowPartial hpow I f i).colA (copowPartial hpow I f i).colB = _
      exact pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]; exact hqA)
        (by rw [Cat.assoc, snd_pair]; exact hqB)
    -- relSub P_i ≤ extJoin S, giving l with l ≫ (extJoin S).arr = (relSub P_i).arr.
    obtain ⟨l, hl⟩ := extJoin_upper hpow wp S (relSub (copowPartial hpow I f i)) ⟨i, rfl⟩
    refine ⟨q ≫ l, ?_⟩
    show (q ≫ l) ≫ ((extJoin hpow wp S).arr ≫ fst) = copowInj hpow I i
    have hpt : (q ≫ l) ≫ (extJoin hpow wp S).arr = pair (copowInj hpow I i) (f i) := by
      rw [Cat.assoc, hl]; exact hq
    rw [← Cat.assoc, hpt, fst_pair]
  -- now run the cover criterion through `copowInj_jointly_cover`.
  intro C m gg hm hgm
  refine copowInj_jointly_cover hpow I m hm (fun i => (hfactor i).choose ≫ gg) (fun i => ?_)
  rw [Cat.assoc, hgm, (hfactor i).choose_spec]

/-- The map-OUT (cotupling) — built Sorry-free as the unique morphism whose graph is the join of
    the partial graphs `P_i`, shown TOTAL + SIMPLE, hence a map by
    `functional_total_relation_is_graph`; the β-law `inj i ≫ c = f i` from `relSub P_i ≤ join`. -/
theorem copowCotup_exists {X : 𝒞} (f : I → ((one : 𝒞) ⟶ X)) :
    ∃ c : copowObj hpow I ⟶ X, ∀ i, copowInj hpow I i ≫ c = f i := by
  let wp := LocallySmallTopos.wellPowered (𝒞 := 𝒞)
  let S : Subobject 𝒞 (prod (copowObj hpow I) X) → Prop :=
    fun U => ∃ i, U = relSub (copowPartial hpow I f i)
  let G : BinRel 𝒞 (copowObj hpow I) X := binRelSub (extJoin hpow wp S)
  have hsimple : Monic G.colA :=
    (tabulated_is_simple_iff_left_monic G.colA G.colB G.isMonicPair).1 (copowUnion_simple hpow I f)
  have htotal : Cover G.colA := copowUnion_total hpow I f
  obtain ⟨c, ⟨⟨h, hhA, hhB⟩, _⟩, _⟩ :=
    functional_total_relation_is_graph G hsimple htotal
  -- key: G.colA ≫ c = G.colB.
  have hkey : G.colA ≫ c = G.colB := by
    have hh : h = G.colA := by
      have := hhA; dsimp [graph] at this; rwa [Cat.comp_id] at this
    have := hhB; dsimp [graph] at this; rw [hh] at this; exact this
  refine ⟨c, fun i => ?_⟩
  -- inj i factors through G.colA (totality factorization), and G.colA ≫ c = G.colB, so
  -- inj i ≫ c = (s ≫ G.colA) ≫ c = s ≫ G.colB = f i.
  obtain ⟨q, hq⟩ : ∃ q : (one : 𝒞) ⟶ G.src,
      q ≫ (extJoin hpow wp S).arr = pair (copowInj hpow I i) (f i) := by
    -- the canonical point of P_i (same as in `copowUnion_total`).
    obtain ⟨qp, hqA, hqB⟩ := copowPartial_point hpow I f i
    have hqp : qp ≫ pair (copowPartial hpow I f i).colA (copowPartial hpow I f i).colB
        = pair (copowInj hpow I i) (f i) :=
      pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]; exact hqA)
        (by rw [Cat.assoc, snd_pair]; exact hqB)
    obtain ⟨l, hl⟩ := extJoin_upper hpow wp S (relSub (copowPartial hpow I f i)) ⟨i, rfl⟩
    refine ⟨qp ≫ l, ?_⟩
    rw [Cat.assoc, hl]
    show qp ≫ pair (copowPartial hpow I f i).colA (copowPartial hpow I f i).colB = _
    exact hqp
  have hA : q ≫ G.colA = copowInj hpow I i := by
    show q ≫ ((extJoin hpow wp S).arr ≫ fst) = copowInj hpow I i
    rw [← Cat.assoc, hq, fst_pair]
  have hB : q ≫ G.colB = f i := by
    show q ≫ ((extJoin hpow wp S).arr ≫ snd) = f i
    rw [← Cat.assoc, hq, snd_pair]
  calc copowInj hpow I i ≫ c = (q ≫ G.colA) ≫ c := by rw [hA]
    _ = q ≫ (G.colA ≫ c) := Cat.assoc _ _ _
    _ = q ≫ G.colB := by rw [hkey]
    _ = f i := hB

/-- **Copower-of-1 from arbitrary powers** — the effective-disjoint-union carving of `∐ᵢ1` as a
    subobject of `∏ᵢ(1+1)`.  Fully SORRY-FREE: `obj`, `inj`, `inj_cotup`, `cotup_uniq`, and
    `cotup` (map-OUT existence, `copowCotup_exists`) are all built; the latter via the honest
    infinitary disjoint gluing (TOTAL + SIMPLE union-of-partial-graphs, functionality from the
    §1.616/§1.84 composition-over-join distributivity).  Axioms `[propext, Classical.choice,
    Quot.sound]`.  See the module doc above. -/
noncomputable def toposCopowerOfOne (hpow : HasArbitraryPowers (𝒞 := 𝒞)) (I : Type v) :
    CopowerOfOne I 𝒞 where
  obj := copowObj hpow I
  inj := copowInj hpow I
  cotup {X} f := (copowCotup_exists hpow I f).choose
  inj_cotup {X} f i := (copowCotup_exists hpow I f).choose_spec i
  cotup_uniq {X} f h hh :=
    copowerImages_jointly_epi hpow I h (copowCotup_exists hpow I f).choose
      (fun i => by rw [hh i, (copowCotup_exists hpow I f).choose_spec i])

end CopowerBuild

/-! ## §1.968 — general-family coproducts by carving inside an ambient

  The GENERIC effective-disjoint-union carving.  Given a family `A : I → 𝒞`, an ambient object
  `B`, and monic candidate embeddings `cand i : A i ↣ B` whose distinct images are DISJOINT (any
  two maps out of the `(cand i, cand j)` pullback agree, `i ≠ j`), the coproduct `∐ᵢAᵢ` is carved
  as the subobject `obj := ⋁ᵢ image(cand i) ⊆ B` (the `extJoin`), with injections, cotupling and
  its uniqueness all built Sorry-free — the same TOTAL+SIMPLE union-of-partial-graphs gluing as the
  copower-of-1 build (`CopowerBuild`), but with `A i`/`B` in place of `1`/`∏ᵢ(1+1)` and the abstract
  disjointness hypothesis in place of `1+1` separation.  The copower-of-1 build IS the special case
  `A i = 1`, `B = ∏ᵢ(1+1)`, `cand = copowCand`. -/
section GenCoprodBuild

variable (hpow : HasArbitraryPowers (𝒞 := 𝒞)) {I : Type v} {A : I → 𝒞} {B : 𝒞}
  (cand : ∀ i, A i ⟶ B) (hcandMono : ∀ i, Monic (cand i))

/-- The `i`-th candidate image `imᵢ ⊆ B`. -/
noncomputable def gcoImg (i : I) : Subobject 𝒞 B := image (cand i)

/-- "is one of the candidate images `imᵢ`". -/
def gcoImgPred (S : Subobject 𝒞 B) : Prop := ∃ i, S = gcoImg cand i

/-- The coproduct object `obj := ⋁ᵢ imᵢ ⊆ B`. -/
noncomputable def gcoSub : Subobject 𝒞 B :=
  extJoin hpow LocallySmallTopos.wellPowered (gcoImgPred cand)

noncomputable def gcoObj : 𝒞 := (gcoSub hpow cand).dom

/-- The `i`-th injection `A i ⟶ obj`: `imᵢ ≤ obj` by `extJoin_upper`. -/
noncomputable def gcoInj (i : I) : A i ⟶ gcoObj hpow cand :=
  image.lift (cand i) ≫
    (show (gcoImg cand i).le (gcoSub hpow cand) from
      extJoin_upper hpow LocallySmallTopos.wellPowered _ _ ⟨i, rfl⟩).choose

theorem gcoInj_arr (i : I) : gcoInj hpow cand i ≫ (gcoSub hpow cand).arr = cand i := by
  unfold gcoInj
  rw [Cat.assoc, (show (gcoImg cand i).le (gcoSub hpow cand) from
    extJoin_upper hpow LocallySmallTopos.wellPowered _ _ ⟨i, rfl⟩).choose_spec]
  exact image.lift_fac (cand i)

include hcandMono in
/-- Each injection is monic: `inj i ≫ obj.arr = cand i` is monic, so `inj i` is. -/
theorem gcoInj_monic (i : I) : Monic (gcoInj hpow cand i) := by
  intro W u v huv
  refine (hcandMono i) u v ?_
  rw [← gcoInj_arr hpow cand i, ← Cat.assoc, ← Cat.assoc, huv]

/-- **`cotup_uniq` (jointly-epic injections).**  Mirrors `copowerImages_jointly_epi`. -/
theorem gcoImages_jointly_epi {X : 𝒞} (h k : gcoObj hpow cand ⟶ X)
    (hagree : ∀ i, gcoInj hpow cand i ≫ h = gcoInj hpow cand i ≫ k) : h = k := by
  have heM : Monic (eqMap h k) := by
    intro W u v huv
    have hc : (u ≫ eqMap h k) ≫ h = (u ≫ eqMap h k) ≫ k := by
      rw [Cat.assoc, Cat.assoc, eqMap_eq]
    rw [eqLift_uniq h k _ hc u rfl, eqLift_uniq h k _ hc v huv.symm]
  have hEPm : Monic (eqMap h k ≫ (gcoSub hpow cand).arr) := by
    intro W u v huv
    refine heM u v ((gcoSub hpow cand).monic _ _ ?_)
    rw [Cat.assoc, Cat.assoc, huv]
  let EP : Subobject 𝒞 B := ⟨eqObj h k, eqMap h k ≫ (gcoSub hpow cand).arr, hEPm⟩
  have himg_le : ∀ i, (gcoImg cand i).le EP := by
    intro i
    let li : A i ⟶ eqObj h k := eqLift h k (gcoInj hpow cand i) (hagree i)
    have hli : li ≫ eqMap h k = gcoInj hpow cand i := eqLift_fac h k _ (hagree i)
    refine image_min (cand i) EP ⟨li, ?_⟩
    show li ≫ (eqMap h k ≫ (gcoSub hpow cand).arr) = cand i
    rw [← Cat.assoc, hli, gcoInj_arr]
  have hobj_le : (gcoSub hpow cand).le EP :=
    extJoin_least hpow LocallySmallTopos.wellPowered _ EP
      (fun s ⟨i, hsi⟩ => hsi ▸ himg_le i)
  obtain ⟨w, hw⟩ := hobj_le
  have hwe : w ≫ eqMap h k = Cat.id (gcoObj hpow cand) := by
    apply (gcoSub hpow cand).monic
    rw [Cat.assoc]
    show w ≫ (eqMap h k ≫ (gcoSub hpow cand).arr) = Cat.id (gcoObj hpow cand) ≫ (gcoSub hpow cand).arr
    rw [Cat.id_comp]; exact hw
  have heq_hk : eqMap h k ≫ h = eqMap h k ≫ k := eqMap_eq h k
  calc h = (w ≫ eqMap h k) ≫ h := by rw [hwe]; exact (Cat.id_comp h).symm
    _ = w ≫ (eqMap h k ≫ h) := Cat.assoc _ _ _
    _ = w ≫ (eqMap h k ≫ k) := by rw [heq_hk]
    _ = (w ≫ eqMap h k) ≫ k := (Cat.assoc _ _ _).symm
    _ = k := by rw [hwe]; exact Cat.id_comp k

/-- **TOTALITY criterion** — a monic `m : C ↣ obj` through which every `inj i` factors is iso.
    Mirrors `copowInj_jointly_cover`. -/
theorem gcoInj_jointly_cover {C : 𝒞} (m : C ⟶ gcoObj hpow cand) (hm : Monic m)
    (s : ∀ i, A i ⟶ C) (hs : ∀ i, s i ≫ m = gcoInj hpow cand i) : IsIso m := by
  have hMPm : Monic (m ≫ (gcoSub hpow cand).arr) := by
    intro W u v huv
    refine hm u v ((gcoSub hpow cand).monic _ _ ?_)
    rw [Cat.assoc, Cat.assoc, huv]
  let MP : Subobject 𝒞 B := ⟨C, m ≫ (gcoSub hpow cand).arr, hMPm⟩
  have himg_le : ∀ i, (gcoImg cand i).le MP := by
    intro i
    refine image_min (cand i) MP ⟨s i, ?_⟩
    show s i ≫ (m ≫ (gcoSub hpow cand).arr) = cand i
    rw [← Cat.assoc, hs i, gcoInj_arr]
  have hobj_le : (gcoSub hpow cand).le MP :=
    extJoin_least hpow LocallySmallTopos.wellPowered _ MP
      (fun t ⟨i, hti⟩ => hti ▸ himg_le i)
  obtain ⟨w, hw⟩ := hobj_le
  have hwm : w ≫ m = Cat.id (gcoObj hpow cand) := by
    apply (gcoSub hpow cand).monic
    rw [Cat.assoc]
    show w ≫ (m ≫ (gcoSub hpow cand).arr) = Cat.id (gcoObj hpow cand) ≫ (gcoSub hpow cand).arr
    rw [Cat.id_comp]; exact hw
  have hmw : m ≫ w = Cat.id C :=
    hm _ _ (by rw [Cat.assoc, hwm, Cat.comp_id, Cat.id_comp])
  exact ⟨w, hmw, hwm⟩

/-! ### map-OUT (cotupling) via the infinitary disjoint gluing — generic.

  Reuses the GENERIC relational engine of `CopowerBuild` (`compose_extJoin_right`,
  `existsAlong_extJoin_le`, `binRelSub`) which are family-agnostic.  The partial graphs are
  `P_i := (graph (inj i))° ⊚ graph (f i)` with `f i : A i ⟶ X`; the per-pair bound
  `P_i° ⊚ P_j ≤ 1` is `diag_le_one` (diagonal, `inj i` monic) / `cross_le_one` (off-diagonal, the
  abstract disjointness `hcandDisj`). -/

variable (hcandDisj : ∀ i j, i ≠ j →
  ∀ {Z : 𝒞} (u v : (HasPullbacks.has (cand i) (cand j)).cone.pt ⟶ Z), u = v)

/-- The `i`-th partial-graph relation `obj ⇸ X`. -/
noncomputable def gcoPartial {X : 𝒞} (f : ∀ i, A i ⟶ X) (i : I) :
    BinRel 𝒞 (gcoObj hpow cand) X :=
  (graph (gcoInj hpow cand i))° ⊚ graph (f i)

/-- **The canonical sub-relation point** of `P_i`: a map `A i → P_i.src` whose span value is
    `pair (inj i) (f i)`, i.e. `P_i` "contains" the graph of `(inj i, f i)`. -/
theorem gcoPartial_point {X : 𝒞} (f : ∀ i, A i ⟶ X) (i : I) :
    ∃ q : A i ⟶ (gcoPartial hpow cand f i).src,
      q ≫ (gcoPartial hpow cand f i).colA = gcoInj hpow cand i ∧
      q ≫ (gcoPartial hpow cand f i).colB = f i := by
  let xr : BinRel 𝒞 (gcoObj hpow cand) (A i) := (graph (gcoInj hpow cand i))°
  let yr : BinRel 𝒞 (A i) X := graph (f i)
  let pb := HasPullbacks.has xr.colB yr.colA
  have hcw : (Cat.id (A i)) ≫ xr.colB = (Cat.id (A i)) ≫ yr.colA := by
    show (Cat.id (A i)) ≫ Cat.id (A i) = (Cat.id (A i)) ≫ Cat.id (A i); rfl
  let c : Cone xr.colB yr.colA := ⟨A i, Cat.id (A i), Cat.id (A i), hcw⟩
  let u : A i ⟶ pb.cone.pt := pb.lift c
  have hu₁ : u ≫ pb.cone.π₁ = Cat.id (A i) := pb.lift_fst c
  have hu₂ : u ≫ pb.cone.π₂ = Cat.id (A i) := pb.lift_snd c
  let span : pb.cone.pt ⟶ prod (gcoObj hpow cand) X :=
    pair (pb.cone.π₁ ≫ xr.colA) (pb.cone.π₂ ≫ yr.colB)
  refine ⟨u ≫ image.lift span, ?_, ?_⟩
  · show (u ≫ image.lift span) ≫ ((image span).arr ≫ fst) = gcoInj hpow cand i
    have hfac : (u ≫ image.lift span) ≫ ((image span).arr ≫ fst) = u ≫ (span ≫ fst) := by
      rw [← Cat.assoc, Cat.assoc u, image.lift_fac, Cat.assoc]
    rw [hfac, show span ≫ fst = pb.cone.π₁ ≫ xr.colA from fst_pair _ _, ← Cat.assoc, hu₁,
      Cat.id_comp]
    rfl
  · show (u ≫ image.lift span) ≫ ((image span).arr ≫ snd) = f i
    have hfac : (u ≫ image.lift span) ≫ ((image span).arr ≫ snd) = u ≫ (span ≫ snd) := by
      rw [← Cat.assoc, Cat.assoc u, image.lift_fac, Cat.assoc]
    rw [hfac, show span ≫ snd = pb.cone.π₂ ≫ yr.colB from snd_pair _ _, ← Cat.assoc, hu₂,
      Cat.id_comp]
    rfl

include hcandMono hcandDisj in
/-- **Per-pair atomic bound.**  `P_i° ⊚ P_j ≤ graph (id X)`.  Diagonal `diag_le_one` (inj i monic),
    off-diagonal `cross_le_one` with the cocone equation from `hcandDisj`. -/
theorem gcoPartial_pair_le {X : 𝒞} (f : ∀ i, A i ⟶ X) (i j : I) :
    RelLe ((gcoPartial hpow cand f i)° ⊚ (gcoPartial hpow cand f j)) (graph (Cat.id X)) := by
  by_cases hij : i = j
  · subst hij
    exact diag_le_one (gcoInj hpow cand i) (f i) (gcoInj_monic hpow cand hcandMono i)
  · -- the disjointness cocone `π₁ ≫ f i = π₂ ≫ f j` comes from `hcandDisj` on the `(cand i,cand j)`
    -- pullback; transport it to the `(inj i, inj j)` pullback via `obj.arr`.
    let pbI := HasPullbacks.has (gcoInj hpow cand i) (gcoInj hpow cand j)
    have hinter : RelLe (graph (gcoInj hpow cand i) ⊚ (graph (gcoInj hpow cand j))°)
        ((graph pbI.cone.π₁)° ⊚ graph pbI.cone.π₂) :=
      inter_lemma (gcoInj hpow cand i) (gcoInj hpow cand j) (Cat.id (gcoObj hpow cand))
        (gcoInj hpow cand i) (gcoInj hpow cand j) (Cat.comp_id _) (Cat.comp_id _)
    -- the `(inj i, inj j)` pullback cone is a cone of `(cand i, cand j)` (post-compose obj.arr),
    -- so `hcandDisj` collapses any two maps out of `pbI.cone.pt`.
    have hagreeI : ∀ {Z : 𝒞} (u v : pbI.cone.pt ⟶ Z), u = v := by
      intro Z u v
      -- The `(inj i,inj j)` and `(cand i,cand j)` pullbacks coincide because `obj.arr` is monic:
      -- `inj i a = inj j a' ⟺ cand i a = cand j a'`.  Build maps both ways.
      let pbC := HasPullbacks.has (cand i) (cand j)
      -- δ : pbI.pt → pbC.pt  (the `(inj i,inj j)` cone is a `(cand i,cand j)` cone, post obj.arr).
      have hconeC : pbI.cone.π₁ ≫ cand i = pbI.cone.π₂ ≫ cand j := by
        rw [← gcoInj_arr hpow cand i, ← gcoInj_arr hpow cand j, ← Cat.assoc, ← Cat.assoc, pbI.cone.w]
      let cC : Cone (cand i) (cand j) := ⟨pbI.cone.pt, pbI.cone.π₁, pbI.cone.π₂, hconeC⟩
      let δ : pbI.cone.pt ⟶ pbC.cone.pt := pbC.lift cC
      -- ε : pbC.pt → pbI.pt  (the `(cand i,cand j)` cone is a `(inj i,inj j)` cone, cancel monic arr).
      have hconeI : pbC.cone.π₁ ≫ gcoInj hpow cand i = pbC.cone.π₂ ≫ gcoInj hpow cand j := by
        apply (gcoSub hpow cand).monic
        rw [Cat.assoc, Cat.assoc, gcoInj_arr, gcoInj_arr]; exact pbC.cone.w
      let cI : Cone (gcoInj hpow cand i) (gcoInj hpow cand j) :=
        ⟨pbC.cone.pt, pbC.cone.π₁, pbC.cone.π₂, hconeI⟩
      let ε : pbC.cone.pt ⟶ pbI.cone.pt := pbI.lift cI
      -- δ ≫ ε = id pbI.pt: both agree with `id` on the (inj i,inj j) projections.
      have hε₁ : ε ≫ pbI.cone.π₁ = pbC.cone.π₁ := pbI.lift_fst cI
      have hε₂ : ε ≫ pbI.cone.π₂ = pbC.cone.π₂ := pbI.lift_snd cI
      have hδ₁ : δ ≫ pbC.cone.π₁ = pbI.cone.π₁ := pbC.lift_fst cC
      have hδ₂ : δ ≫ pbC.cone.π₂ = pbI.cone.π₂ := pbC.lift_snd cC
      have hδε : δ ≫ ε = Cat.id pbI.cone.pt := by
        refine (pbI.lift_uniq ⟨pbI.cone.pt, pbI.cone.π₁, pbI.cone.π₂, pbI.cone.w⟩ (δ ≫ ε) ?_ ?_).trans
          (pbI.lift_uniq ⟨pbI.cone.pt, pbI.cone.π₁, pbI.cone.π₂, pbI.cone.w⟩
            (Cat.id pbI.cone.pt) (Cat.id_comp _) (Cat.id_comp _)).symm
        · rw [Cat.assoc, hε₁, hδ₁]
        · rw [Cat.assoc, hε₂, hδ₂]
      -- u = (δ≫ε)≫u = δ≫(ε≫u) = δ≫(ε≫v) = v, using hcandDisj on (ε≫u), (ε≫v) out of pbC.pt.
      calc u = (δ ≫ ε) ≫ u := by rw [hδε, Cat.id_comp]
        _ = δ ≫ (ε ≫ u) := Cat.assoc _ _ _
        _ = δ ≫ (ε ≫ v) := by rw [hcandDisj i j hij (ε ≫ u) (ε ≫ v)]
        _ = (δ ≫ ε) ≫ v := (Cat.assoc _ _ _).symm
        _ = v := by rw [hδε, Cat.id_comp]
    have hw : pbI.cone.π₁ ≫ f i = pbI.cone.π₂ ≫ f j := hagreeI _ _
    have hxyg : RelLe ((graph (gcoInj hpow cand i) ⊚ (graph (gcoInj hpow cand j))°) ⊚ graph (f j))
        (graph (f i)) :=
      hxyg_lemma (f i) (f j) pbI.cone.π₁ pbI.cone.π₂
        (graph (gcoInj hpow cand i) ⊚ (graph (gcoInj hpow cand j))°) hinter hw
    exact cross_le_one (gcoInj hpow cand i) (gcoInj hpow cand j) (f i) (f j) hxyg

include hcandMono hcandDisj in
/-- **FUNCTIONALITY (simplicity).**  Mirrors `copowUnion_simple`. -/
theorem gcoUnion_simple {X : 𝒞} (f : ∀ i, A i ⟶ X) :
    Simple (binRelSub (extJoin hpow LocallySmallTopos.wellPowered
      (fun U => ∃ i, U = relSub (gcoPartial hpow cand f i)))) := by
  let wp := LocallySmallTopos.wellPowered (𝒞 := 𝒞)
  let S : Subobject 𝒞 (prod (gcoObj hpow cand) X) → Prop :=
    fun U => ∃ i, U = relSub (gcoPartial hpow cand f i)
  let G : BinRel 𝒞 (gcoObj hpow cand) X := binRelSub (extJoin hpow wp S)
  have key : ∀ (T : BinRel 𝒞 X (gcoObj hpow cand)),
      (∀ i, RelLe (T ⊚ binRelSub (relSub (gcoPartial hpow cand f i)))
        (graph (Cat.id X))) →
      RelLe (T ⊚ G) (graph (Cat.id X)) := by
    intro T hpieces
    have hdist := compose_extJoin_right hpow T S
    have hbound : (extJoin hpow wp
          (fun U => ∃ W, S W ∧ U = relSub (T ⊚ binRelSub W))).le
        (relSub (graph (Cat.id X))) := by
      refine extJoin_least hpow wp _ (relSub (graph (Cat.id X))) (fun U hmem => ?_)
      obtain ⟨W, ⟨i, hWi⟩, hU⟩ := hmem
      rw [hU, hWi]
      exact subLe_of_relLe (hpieces i)
    exact (relLe_iff_subLe (T ⊚ G) (graph (Cat.id X))).2 (Subobject.le_trans hdist hbound)
  show RelLe (G° ⊚ G) (graph (Cat.id X))
  refine key (G°) (fun i => ?_)
  have hrecip : RelLe ((G° ⊚ binRelSub (relSub (gcoPartial hpow cand f i)))°)
      ((binRelSub (relSub (gcoPartial hpow cand f i)))° ⊚ G) := by
    have h := (reciprocal_comp (G°) (binRelSub (relSub (gcoPartial hpow cand f i)))).1
    rwa [reciprocal_invol] at h
  have hPiG : RelLe ((binRelSub (relSub (gcoPartial hpow cand f i)))° ⊚ G)
      (graph (Cat.id X)) := by
    refine key ((binRelSub (relSub (gcoPartial hpow cand f i)))°) (fun j => ?_)
    refine rel_le_trans (compose_le (reciprocal_mono (binRelSub_relSub_relLe _).1)
      (binRelSub_relSub_relLe _).1) ?_
    exact gcoPartial_pair_le hpow cand hcandMono hcandDisj f i j
  have hco : RelLe ((G° ⊚ binRelSub (relSub (gcoPartial hpow cand f i)))°)
      (graph (Cat.id X)) := rel_le_trans hrecip hPiG
  have h2 := reciprocal_mono hco
  rwa [reciprocal_invol, show (graph (Cat.id X))° = graph (Cat.id X) from rfl] at h2

/-- **TOTALITY.**  Mirrors `copowUnion_total`. -/
theorem gcoUnion_total {X : 𝒞} (f : ∀ i, A i ⟶ X) :
    Cover (binRelSub (extJoin hpow LocallySmallTopos.wellPowered
      (fun U => ∃ i, U = relSub (gcoPartial hpow cand f i)))).colA := by
  let wp := LocallySmallTopos.wellPowered (𝒞 := 𝒞)
  let S : Subobject 𝒞 (prod (gcoObj hpow cand) X) → Prop :=
    fun U => ∃ i, U = relSub (gcoPartial hpow cand f i)
  let G : BinRel 𝒞 (gcoObj hpow cand) X := binRelSub (extJoin hpow wp S)
  have hfactor : ∀ i, ∃ s : A i ⟶ G.src, s ≫ G.colA = gcoInj hpow cand i := by
    intro i
    obtain ⟨q, hqA, hqB⟩ := gcoPartial_point hpow cand f i
    have hq : q ≫ (relSub (gcoPartial hpow cand f i)).arr = pair (gcoInj hpow cand i) (f i) := by
      show q ≫ pair (gcoPartial hpow cand f i).colA (gcoPartial hpow cand f i).colB = _
      exact pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]; exact hqA)
        (by rw [Cat.assoc, snd_pair]; exact hqB)
    obtain ⟨l, hl⟩ := extJoin_upper hpow wp S (relSub (gcoPartial hpow cand f i)) ⟨i, rfl⟩
    refine ⟨q ≫ l, ?_⟩
    show (q ≫ l) ≫ ((extJoin hpow wp S).arr ≫ fst) = gcoInj hpow cand i
    have hpt : (q ≫ l) ≫ (extJoin hpow wp S).arr = pair (gcoInj hpow cand i) (f i) := by
      rw [Cat.assoc, hl]; exact hq
    rw [← Cat.assoc, hpt, fst_pair]
  intro C m gg hm hgm
  refine gcoInj_jointly_cover hpow cand m hm (fun i => (hfactor i).choose ≫ gg) (fun i => ?_)
  rw [Cat.assoc, hgm, (hfactor i).choose_spec]

include hcandMono hcandDisj in
/-- The map-OUT (cotupling) — mirrors `copowCotup_exists`. -/
theorem gcoCotup_exists {X : 𝒞} (f : ∀ i, A i ⟶ X) :
    ∃ c : gcoObj hpow cand ⟶ X, ∀ i, gcoInj hpow cand i ≫ c = f i := by
  let wp := LocallySmallTopos.wellPowered (𝒞 := 𝒞)
  let S : Subobject 𝒞 (prod (gcoObj hpow cand) X) → Prop :=
    fun U => ∃ i, U = relSub (gcoPartial hpow cand f i)
  let G : BinRel 𝒞 (gcoObj hpow cand) X := binRelSub (extJoin hpow wp S)
  have hsimple : Monic G.colA :=
    (tabulated_is_simple_iff_left_monic G.colA G.colB G.isMonicPair).1
      (gcoUnion_simple hpow cand hcandMono hcandDisj f)
  have htotal : Cover G.colA := gcoUnion_total hpow cand f
  obtain ⟨c, ⟨⟨h, hhA, hhB⟩, _⟩, _⟩ :=
    functional_total_relation_is_graph G hsimple htotal
  have hkey : G.colA ≫ c = G.colB := by
    have hh : h = G.colA := by
      have := hhA; dsimp [graph] at this; rwa [Cat.comp_id] at this
    have := hhB; dsimp [graph] at this; rw [hh] at this; exact this
  refine ⟨c, fun i => ?_⟩
  obtain ⟨q, hq⟩ : ∃ q : A i ⟶ G.src,
      q ≫ (extJoin hpow wp S).arr = pair (gcoInj hpow cand i) (f i) := by
    obtain ⟨qp, hqA, hqB⟩ := gcoPartial_point hpow cand f i
    have hqp : qp ≫ pair (gcoPartial hpow cand f i).colA (gcoPartial hpow cand f i).colB
        = pair (gcoInj hpow cand i) (f i) :=
      pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair]; exact hqA)
        (by rw [Cat.assoc, snd_pair]; exact hqB)
    obtain ⟨l, hl⟩ := extJoin_upper hpow wp S (relSub (gcoPartial hpow cand f i)) ⟨i, rfl⟩
    refine ⟨qp ≫ l, ?_⟩
    rw [Cat.assoc, hl]
    show qp ≫ pair (gcoPartial hpow cand f i).colA (gcoPartial hpow cand f i).colB = _
    exact hqp
  have hA : q ≫ G.colA = gcoInj hpow cand i := by
    show q ≫ ((extJoin hpow wp S).arr ≫ fst) = gcoInj hpow cand i
    rw [← Cat.assoc, hq, fst_pair]
  have hB : q ≫ G.colB = f i := by
    show q ≫ ((extJoin hpow wp S).arr ≫ snd) = f i
    rw [← Cat.assoc, hq, snd_pair]
  calc gcoInj hpow cand i ≫ c = (q ≫ G.colA) ≫ c := by rw [hA]
    _ = q ≫ (G.colA ≫ c) := Cat.assoc _ _ _
    _ = q ≫ G.colB := by rw [hkey]
    _ = f i := hB

include hcandMono hcandDisj in
/-- **The general-family coproduct datum** `∐ᵢAᵢ`, carved as `⋁ᵢ image(cand i) ⊆ B` with the
    map-OUT universal property from the infinitary disjoint gluing.  Sorry-free given monic +
    pairwise-disjoint candidate embeddings. -/
noncomputable def gcoCoproduct : Coproduct A :=
  { obj := gcoObj hpow cand
    inj := gcoInj hpow cand
    desc := fun {X} f => (gcoCotup_exists hpow cand hcandMono hcandDisj f).choose
    fac := fun {X} f i => (gcoCotup_exists hpow cand hcandMono hcandDisj f).choose_spec i
    uniq := fun {X} f h hh =>
      gcoImages_jointly_epi hpow cand h
        (gcoCotup_exists hpow cand hcandMono hcandDisj f).choose
        (fun i => by rw [hh i, (gcoCotup_exists hpow cand hcandMono hcandDisj f).choose_spec i]) }

end GenCoprodBuild

/-! ## §1.968 — `Cocomplete` from general coproducts + coequalizers

  The colimit-dual of `eq_prod_complete` (S1_82:291).  Every small colimit is the COEQUALIZER of
  two maps between coproducts: `colim D = coeq( ∐_{arrows a} D(src a) ⇉ ∐_{objects i} D i )`, where
  the two maps send the `a`-injection to `D(arr a) ≫ inj(tgt a)` and `inj(src a)` respectively.
  Reuses the EXISTING general-family `Coproduct`/`HasAllCoproducts` (S1_84) and `HasCoequalizer`
  (S1_58).  Banked as `cocomplete_of_coproducts_coequalizers` — reusable infra (S1_97's ∐ₙAⁿ).
  Axioms: `[propext, Classical.choice, Quot.sound]` (inherited from its inputs only). -/
section CocompleteFromCoprodCoeq
variable {ℬ : Type u} [Cat.{v} ℬ]

/-- **§1.968**: general coproducts + coequalizers ⟹ cocomplete (dual of `eq_prod_complete`). -/
noncomputable def cocomplete_of_coproducts_coequalizers
    (hcp : HasAllCoproducts ℬ) (hce : HasCoequalizers ℬ) : Cocomplete ℬ where
  hasColimit {𝒟} _ D := by
    classical
    -- Σ of arrows in 𝒟; coproduct of sources over arrows, and of objects.
    let Arr := Σ (i : 𝒟) (j : 𝒟), (i ⟶ j)
    let srcOf : Arr → 𝒟 := fun a => a.fst
    let tgtOf : Arr → 𝒟 := fun a => a.snd.fst
    let arrOf : (a : Arr) → srcOf a ⟶ tgtOf a := fun a => a.snd.snd
    let P := hcp.coprod D.obj                                  -- ∐_objects D
    let Q := hcp.coprod (fun a : Arr => D.obj (srcOf a))       -- ∐_arrows D(src)
    -- mapF's a-leg = D(arr a) ≫ inj(tgt a); mapG's = inj(src a).
    let mapF : Q.obj ⟶ P.obj := Q.desc (fun a => D.map (arrOf a) ≫ P.inj (tgtOf a))
    let mapG : Q.obj ⟶ P.obj := Q.desc (fun a => P.inj (srcOf a))
    let ce := hce.coeq mapF mapG
    let ιi : (i : 𝒟) → D.obj i ⟶ ce.obj := fun i => P.inj i ≫ ce.map
    -- Cocone naturality: D(x) ≫ ιj = ιi.  From `inj(src⟨i,j,x⟩) ≫ map = D(x) ≫ inj(tgt) ≫ map`
    -- (the a=⟨i,j,x⟩ component of `mapG ≫ ce.map = mapF ≫ ce.map`).
    have nat_pf : ∀ {i j : 𝒟} (x : i ⟶ j), D.map x ≫ ιi j = ιi i := by
      intro i j x
      let a : Arr := ⟨i, j, x⟩
      have hFG : mapF ≫ ce.map = mapG ≫ ce.map := by
        rw [ce.eq]
      -- a-leg of both sides of hFG.
      have hstep := congrArg (fun t => Q.inj a ≫ t) hFG
      simp only [mapF, mapG] at hstep
      rw [← Cat.assoc, ← Cat.assoc, Q.fac, Q.fac] at hstep
      -- hstep : (D(arr a) ≫ inj(tgt a)) ≫ map = inj(src a) ≫ map
      show D.map x ≫ P.inj j ≫ ce.map = P.inj i ≫ ce.map
      calc D.map x ≫ P.inj j ≫ ce.map
          = (D.map (arrOf a) ≫ P.inj (tgtOf a)) ≫ ce.map := by rw [Cat.assoc]
        _ = P.inj (srcOf a) ≫ ce.map := hstep
        _ = P.inj i ≫ ce.map := rfl
    -- Given a cocone c, `P.desc c.ι` coequalizes mapF and mapG.
    have desc_eq : ∀ (c : DiagCocone D), mapF ≫ P.desc c.ι = mapG ≫ P.desc c.ι := by
      intro c
      have hF : mapF ≫ P.desc c.ι = Q.desc (fun a => D.map (arrOf a) ≫ c.ι (tgtOf a)) := by
        apply Q.uniq; intro a
        rw [← Cat.assoc, Q.fac, Cat.assoc, P.fac]
      have hG : mapG ≫ P.desc c.ι = Q.desc (fun a => c.ι (srcOf a)) := by
        apply Q.uniq; intro a
        rw [← Cat.assoc, Q.fac, P.fac]
      rw [hF, hG]; congr 1; funext a; exact c.nat (arrOf a)
    exact
      { cocone := { nadir := ce.obj, ι := ιi, nat := nat_pf }
        lift := fun c => ce.desc (P.desc c.ι) (desc_eq c)
        fac := fun c i => by
          show (P.inj i ≫ ce.map) ≫ ce.desc (P.desc c.ι) (desc_eq c) = c.ι i
          rw [Cat.assoc, ce.fac, P.fac]
        uniq := fun c u hu => by
          apply ce.uniq
          apply P.uniq
          intro i
          rw [← Cat.assoc]; exact hu i }

/-- The DISCRETE CATEGORY on `I` (local copy; the S1_82 `discCat82` is private). -/
private instance discCatTC {I : Type v} : Cat.{v} I where
  Hom i j     := ULift.{v} (PLift (i = j))
  id _        := ⟨⟨rfl⟩⟩
  comp f g    := ⟨⟨f.down.down.trans g.down.down⟩⟩
  id_comp _   := rfl
  comp_id _   := rfl
  assoc _ _ _ := rfl

/-- Every `A : I → ℬ` is a functor on the discrete category (local copy). -/
private def discFunTC {I : Type v} (A : I → ℬ) : @Functor I ℬ discCatTC _ where
  obj          := A
  map {i j} h  := h.down.down ▸ Cat.id (A i)
  map_id _     := rfl
  map_comp f g := by
    obtain ⟨⟨hij⟩⟩ := f; obtain ⟨⟨hjk⟩⟩ := g; subst hij; subst hjk; exact (Cat.id_comp _).symm

/-- **Cocomplete ⟹ all coproducts** (colimit-dual of `complete_hasProducts`).  A coproduct is the
    colimit of the discrete diagram; reusable infra (e.g. Lawvere→Tierney's `∐(gen set)`). -/
noncomputable def cocompleteCoconeOf {I : Type v} (A : I → ℬ) (X : ℬ) (f : ∀ i, A i ⟶ X) :
    @DiagCocone I discCatTC ℬ _ (discFunTC A) :=
  { nadir := X, ι := f,
    nat := by intro i j x; obtain ⟨⟨hij⟩⟩ := x; subst hij; simp [discFunTC, Cat.id_comp] }

noncomputable def cocomplete_hasAllCoproducts (hc : Cocomplete ℬ) : HasAllCoproducts ℬ where
  coprod {I} A :=
    { obj  := (@hc.hasColimit I discCatTC (discFunTC A)).cocone.nadir
      inj  := (@hc.hasColimit I discCatTC (discFunTC A)).cocone.ι
      desc := fun {X} f => (@hc.hasColimit I discCatTC (discFunTC A)).lift (cocompleteCoconeOf A X f)
      fac  := fun {X} f i => (@hc.hasColimit I discCatTC (discFunTC A)).fac (cocompleteCoconeOf A X f) i
      uniq := fun {X} f h hh => (@hc.hasColimit I discCatTC (discFunTC A)).uniq (cocompleteCoconeOf A X f) h hh }

end CocompleteFromCoprodCoeq

/-! ## §1.967 powers ↔ copowers, §1.968 complete ↔ cocomplete, §1.969 Lawvere = Tierney

  Relocated here from `Freyd/S1_95.lean` (which this file imports): the powers↔copowers
  equivalence is CLOSED Sorry-free because its sole residual — the (a)→(b) carving
  `∐ᵢ1 ⊂ ∏ᵢ(1+1)` (`toposCopowerOfOne`) — is built above.  §1.968 (`topos_complete_iff_cocomplete`)
  is now ALSO CLOSED Sorry-free and COGENERATOR-FREE (faithful to Freyd's bare statement) via the
  `CompleteCocompleteFree` section: `hasProducts_of_coproducts` (←, `∏ᵢAᵢ = ⋂ᵢ Pᵢ ⊆ Sᴵ`) and
  `hasAllCoproducts_of_products` (→, `∐ᵢAᵢ ⊆ ∏ⱼ(Aⱼ+1)`).  §1.969 (`lawvere_eq_tierney`) is closed
  with its progenitor datum.  BANKED Sorry-free here: `wellPoweredSub_of_topos` (§1.843),
  `cocomplete_of_coproducts_coequalizers`, `cocomplete_hasAllCoproducts`, and the §1.967 join
  engine `familyMeet`/`familyMeet_lift` (S1_95). -/

-- Make the GENUINE `Topos.toHasBinaryProducts` win instance search for `HasBinaryProducts 𝒞`
-- (the §1.92 `topos_has_exponentials.toHasBinaryProducts` is deprioritised but could still be
-- picked, making otherwise-computable defs noncomputable via `Classical.choice`).  Mirroring
-- the §1.92 `attribute [local instance]` pattern.
attribute [local instance 10000] Topos.toHasBinaryProducts

/-- **§1.967**: In a locally small topos, arbitrary powers exist iff arbitrary copowers exist.

    * **(a)→(b)** CLOSED Sorry-free.  Build a copower-of-1 datum `CopowerOfOne I 𝒞` for every `I`
      via `toposCopowerOfOne` (the effective-disjoint-union carving `∐ᵢ1 ⊂ ∏ᵢ(1+1)`, with the
      map-OUT universal property supplied by the infinitary disjoint gluing above), then
      `topos_copowers_equiv_copowers_of_one` assembles `HasArbitraryCopowers`.
    * **(b)→(a)** CLOSED Sorry-free.  Reduce to copowers-of-1 (sibling iff), then set
      `∏ᵢ A := A^(∐ᵢ1)` (`powersOfCopowersOfOne`); the power UP is the exponential law
      `Hom(X, A^cI) ≅ Hom(cI×X, A) ≅ ∏ᵢ Hom(X,A)` (`prod_distrib_copow`). -/
theorem topos_powers_copowers_equiv [LocallySmallTopos 𝒞] [HasBinaryCoproducts 𝒞] :
    (Nonempty (@HasArbitraryPowers 𝒞 _ Topos.toHasBinaryProducts)) ↔
    (Nonempty (HasArbitraryCopowers (𝒞 := 𝒞))) :=
  -- TERM MODE (not `by constructor`): the tactic `constructor` re-synthesizes the iff's
  -- `HasBinaryProducts` per goal, which can route the type through the §1.92
  -- `topos_has_exponentials.toHasBinaryProducts` and make the products noncomputable via
  -- `Classical.choice`; the explicit `⟨forward, backward⟩` shares ONE elaboration.
  ⟨fun ⟨hpow⟩ =>
      -- (a)→(b): every `I` has a copower-of-1 (`toposCopowerOfOne`), so the sibling iff yields
      -- `HasArbitraryCopowers`.
      (topos_copowers_equiv_copowers_of_one).mpr (fun I => ⟨toposCopowerOfOne hpow I⟩),
   fun hcop =>
      -- (b)→(a): reduce to copowers-of-1 (sibling iff), then `A^(∐ᵢ1)`.
      let hone : ∀ (I : Type v), Nonempty (CopowerOfOne I 𝒞) :=
        (topos_copowers_equiv_copowers_of_one).mp hcop
      let pw := powersOfCopowersOfOne (fun I => Classical.choice (hone I))
      ⟨{ pow := pw.pow, proj := fun {_I _A} => pw.proj, tupling := fun {_I _A _X} => pw.tupling,
         tupling_proj := fun {_I _A _X} => pw.tupling_proj,
         tupling_uniq := fun {_I _A _X} => pw.tupling_uniq }⟩⟩

/-! ## §1.968 — `HasAllCoproducts` by the cogenerator carving

  Given a progenitor `G` (so `C := Ω^G` cogenerates, `progenitor_omega_exp_cogenerates`) and
  arbitrary powers `hpow` (from copowers-of-1), every family `A : I → 𝒞` has a coproduct.  Ambient
  `B := C^K × cI.obj` where `K := Σ i, (A i ⟶ C)` (a `Type v` index) and `cI := toposCopowerOfOne`
  is the copower-of-1 supplying DISJOINT injections.  Embed
  `cand i := pair (jᵢ) (term ≫ cI.inj i)` where `jᵢ : A i ↣ C^K` is the cogenerator-evaluation
  tuple (monic by cogeneration) — so `cand i` is monic (its `C^K` leg is) and the images are
  pairwise disjoint (the `cI`-leg separates by `copowInj_collapse_maps_agree`).  Then `gcoCoproduct`
  carves `∐ᵢAᵢ = ⋁ᵢ image(cand i) ⊆ B`. -/
section CogeneratorCarving

variable [LocallySmallTopos 𝒞] (G : 𝒞) (hG : IsProgenitor G)

local notation "Cg" => HasSubobjectClassifier.omega (𝒞 := 𝒞) ^^ G

/-- A default map `A ⟶ Cg` (the cogenerator has a point: `curry (term ≫ true)`), so `Hom(A, Cg)` is
    always nonempty — needed to fill the off-diagonal coordinates of the evaluation tuple. -/
noncomputable def cogenDefault (A : 𝒞) : A ⟶ Cg :=
  curry (term (prod G A) ≫ HasSubobjectClassifier.true)

/-- The cogenerator-evaluation tuple `jᵢ : A i ↣ C^K`, `K := Σ i, (A i ⟶ Cg)`.  Coordinate
    `⟨i', φ⟩` is `φ` when `i' = i`, else the default.  Monic by cogeneration. -/
noncomputable def cogenEmbed (hpow : HasArbitraryPowers (𝒞 := 𝒞)) {I : Type v} (A : I → 𝒞)
    (i : I) : A i ⟶ hpow.pow (Σ i : I, (A i ⟶ Cg)) Cg :=
  hpow.tupling (fun k : Σ i : I, (A i ⟶ Cg) =>
    if h : k.1 = i then (h ▸ k.2 : A i ⟶ Cg) else cogenDefault G (A i))

include hG in
/-- `cogenEmbed` is monic: `u ≫ j = v ≫ j` projects (at coordinate `⟨i, φ⟩`) to `u ≫ φ = v ≫ φ` for
    every `φ : A i ⟶ Cg`, so `u = v` by cogeneration (separation by `Cg = Ω^G`). -/
theorem cogenEmbed_monic (hpow : HasArbitraryPowers (𝒞 := 𝒞)) {I : Type v} (A : I → 𝒞) (i : I) :
    Monic (cogenEmbed G hpow A i) := by
  intro W u v huv
  refine Classical.byContradiction (fun hne => ?_)
  -- cogeneration: u ≠ v ⟹ ∃ φ : A i → Cg with u ≫ φ ≠ v ≫ φ.
  obtain ⟨φ, hφ⟩ := progenitor_omega_exp_cogenerates G hG u v hne
  -- project both sides at coordinate ⟨i, φ⟩ — the tuple value there is `φ`.
  refine hφ ?_
  have hk : (⟨i, φ⟩ : Σ i : I, (A i ⟶ Cg)).1 = i := rfl
  have hpr := congrArg (· ≫ hpow.proj (⟨i, φ⟩ : Σ i : I, (A i ⟶ Cg))) huv
  simp only [cogenEmbed, Cat.assoc, hpow.tupling_proj] at hpr
  simpa [dif_pos hk] using hpr

include hG in
/-- **§1.968: general-family coproducts.**  From a progenitor `G` and arbitrary powers `hpow`
    (e.g. from copowers-of-1), every `Type v`-indexed family has a coproduct. -/
noncomputable def hasAllCoproducts_of_progenitor (hpow : HasArbitraryPowers (𝒞 := 𝒞)) :
    HasAllCoproducts 𝒞 where
  coprod {I} A := by
    classical
    let cI := toposCopowerOfOne hpow I
    let K := Σ i : I, (A i ⟶ Cg)
    let Bamb := prod (hpow.pow K Cg) cI.obj
    -- candidate embedding: pair (cogenerator tuple) (copower coordinate).
    let cand : ∀ i, A i ⟶ Bamb :=
      fun i => pair (cogenEmbed G hpow A i) (term (A i) ≫ cI.inj i)
    -- monicity: the `C^K` leg `cogenEmbed` is monic, so the pair is.
    have hcandMono : ∀ i, Monic (cand i) := by
      intro i
      intro W u v huv
      refine (cogenEmbed_monic G hG hpow A i) u v ?_
      have hf := congrArg (· ≫ fst) huv
      simp only [cand, Cat.assoc, fst_pair] at hf
      exact hf
    -- disjointness: the `cI`-coordinate separates distinct injections via the copower collapse.
    have hcandDisj : ∀ i j, i ≠ j →
        ∀ {Z : 𝒞} (u v : (HasPullbacks.has (cand i) (cand j)).cone.pt ⟶ Z), u = v := by
      intro i j hij Z u v
      let pb := HasPullbacks.has (cand i) (cand j)
      -- project the pullback square to the `cI` coordinate: term ≫ inj i = term ≫ inj j on the apex.
      have hsnd : pb.cone.π₁ ≫ (cand i ≫ snd) = pb.cone.π₂ ≫ (cand j ≫ snd) := by
        rw [← Cat.assoc, ← Cat.assoc, pb.cone.w]
      have hcol : term pb.cone.pt ≫ cI.inj i = term pb.cone.pt ≫ cI.inj j := by
        have h := hsnd
        rw [show cand i ≫ snd = term (A i) ≫ cI.inj i from snd_pair _ _,
            show cand j ≫ snd = term (A j) ≫ cI.inj j from snd_pair _ _] at h
        rw [← Cat.assoc, ← Cat.assoc] at h
        rw [show (pb.cone.π₁ ≫ term (A i) : pb.cone.pt ⟶ (one : 𝒞)) = term pb.cone.pt
              from term_uniq _ _,
            show (pb.cone.π₂ ≫ term (A j) : pb.cone.pt ⟶ (one : 𝒞)) = term pb.cone.pt
              from term_uniq _ _] at h
        exact h
      exact copowInj_collapse_maps_agree hpow I hij hcol u v
    exact gcoCoproduct hpow cand hcandMono hcandDisj

end CogeneratorCarving

/-! ## §1.968 — `Complete ↔ Cocomplete`, the COGENERATOR-FREE route (Freyd's actual proof)

  Freyd §1.968 ("a locally small topos is complete iff it is cocomplete") is FAITHFUL as a BARE
  statement — no progenitor/cogenerator hypothesis.  His proof builds the embeddings each direction
  needs *directly*, with NO cogenerator:

  * **Cocomplete → Complete** (Freyd's "easy" half).  Coproducts give `S := ∐ᵢAᵢ` with MONIC
    injections `uᵢ : Aᵢ ↣ S` (`coproduct_inj_monic`); powers exist (§1.967).  For each `i` form the
    pullback `Pᵢ` of `uᵢ` along the `i`-th power-projection `pᵢ : Sᴵ → S` (a subobject of `Sᴵ`,
    monic since `uᵢ` is), and `∏ᵢAᵢ := ⋂ᵢ Pᵢ` (`familyMeet`).  The product UMP is `familyMeet_lift`.

  * **Complete → Cocomplete** (the "slight modification of §1.967 copowers-from-powers").  Products
    give the ambient `B := ∏ⱼ(Aⱼ+1)` and MONIC embeddings `uᵢ : Aᵢ ↣ B` whose `i`-th coordinate is
    `inl : Aᵢ ↣ Aᵢ+1` and whose `j`-th (`j≠i`) is the constant `Aᵢ → 1 →inr Aⱼ+1`.  Distinct images
    are DISJOINT (separated by coordinate `i`: `inl ⊥ inr`, `coprodInjections_disjoint`), so the
    banked `gcoCoproduct` carving (`∐ᵢAᵢ = ⋁ᵢ image uᵢ ⊆ B`) applies — NO cogenerator.  Then
    `cocomplete_of_coproducts_coequalizers`.

  The two embedding-families replace the single cogenerator `Ω^G` of `hasAllCoproducts_of_progenitor`
  (§1.969, which is for the Grothendieck/Tierney setting).  This section is Sorry-free. -/
section CompleteCocompleteFree

/-- **§1.845: general coproduct injections are monic in a topos.**  Given a coproduct `cop` of a
    `Type v`-indexed family `A` and any index `k`, the injection `cop.inj k : A k ⟶ ∐ᵢ Aᵢ` is monic.

    PROOF (binary regrouping).  Let `R := ∐_{i≠k} Aᵢ` (from `HasAllCoproducts`) and form the binary
    coproduct `A k ⊔ R` (the topos has binary coproducts, with monic left injection `coprodInl`).
    The cocone sending `inj k ↦ inl` and `inj i ↦ R.inj⟨i,_⟩ ≫ inr` (`i≠k`) descends to a map
    `Φ : cop.obj ⟶ A k ⊔ R` with `cop.inj k ≫ Φ = inl`.  As `inl` is monic and factors through
    `cop.inj k`, the injection is monic. -/
theorem coproduct_inj_monic [Topos 𝒞] (hca : HasAllCoproducts 𝒞)
    {I : Type v} {A : I → 𝒞} (cop : Coproduct A) (k : I) : Monic (cop.inj k) := by
  classical
  -- `R := ∐_{i≠k} Aᵢ`; binary coproduct `A k ⊔ R` with monic left injection.
  let R : Coproduct (fun j : {i : I // i ≠ k} => A j.1) := hca.coprod _
  let cR : 𝒞 := HasBinaryCoproducts.coprod (A k) R.obj
  let inl : A k ⟶ cR := HasBinaryCoproducts.inl
  let inr : R.obj ⟶ cR := HasBinaryCoproducts.inr
  have hinl_monic : Monic inl := coprodInl_monic (A k) R.obj
  -- the cocone `{f i}` over the full family `A`, valued in `A k ⊔ R`.
  let f : ∀ i, A i ⟶ cR := fun i =>
    if h : i = k then (h ▸ inl : A i ⟶ cR) else R.inj ⟨i, h⟩ ≫ inr
  let Φ : cop.obj ⟶ cR := cop.desc f
  -- `cop.inj k ≫ Φ = f k = inl` (the `dite` at `k` is the diagonal branch).
  have hk : cop.inj k ≫ Φ = inl := by
    rw [cop.fac f k]; show (if h : k = k then (h ▸ inl : A k ⟶ cR) else _) = inl
    rw [dif_pos rfl]
  -- monic `inl` factoring through `cop.inj k` ⟹ `cop.inj k` monic.
  intro W u v huv
  refine hinl_monic u v ?_
  rw [← hk, ← Cat.assoc, ← Cat.assoc, huv]

/-- `HasArbitraryPowers` from `HasProducts`: the `I`-fold power of `A` is the product of the
    constant family `fun _:I => A`.  (Needed to feed the §1.967 join engine `familyMeet`/`extJoin`,
    which the carvings consume, from bare `HasProducts`.) -/
noncomputable def powersOfProducts (hp : HasProducts 𝒞) :
    @HasArbitraryPowers 𝒞 _ Topos.toHasBinaryProducts where
  pow I A := (hp.prod (fun _ : I => A)).prod
  proj {I A} i := (hp.prod (fun _ : I => A)).proj i
  tupling {I A _X} f := (hp.prod (fun _ : I => A)).lift f
  tupling_proj {I A _X} f i := (hp.prod (fun _ : I => A)).lift_π f i
  tupling_uniq {I A _X} f h hh := (hp.prod (fun _ : I => A)).lift_uniq f h hh

/-! ### Cocomplete → Complete: `HasProducts` from `HasAllCoproducts`.

  `∏ᵢAᵢ := ⋂ᵢ Pᵢ ⊆ Sᴵ`, `S := ∐ᵢAᵢ`, `Pᵢ :=` pullback of the `i`-th power projection
  `pᵢ : Sᴵ → S` along the MONIC injection `uᵢ : Aᵢ ↣ S` — pullback orientation
  `HasPullbacks.has pᵢ uᵢ`, so the SUBOBJECT leg `π₁ : Pᵢ ↣ Sᴵ` is monic (`mono_pullback`,
  the SECOND map `uᵢ` is monic) and the PRODUCT-projection leg is `π₂ : Pᵢ → Aᵢ`. -/
section ProductsFromCoproducts
variable (hpow : @HasArbitraryPowers 𝒞 _ Topos.toHasBinaryProducts) (hca : HasAllCoproducts 𝒞)
  {I : Type v} (A : I → 𝒞)

/-- `S := ∐ᵢAᵢ`. -/
private noncomputable def pfcS : 𝒞 := (hca.coprod A).obj
/-- The `i`-th injection `uᵢ : Aᵢ ↣ S`, monic. -/
private noncomputable def pfcInj (i : I) : A i ⟶ pfcS hca A := (hca.coprod A).inj i
private theorem pfcInj_monic (i : I) : Monic (pfcInj hca A i) :=
  coproduct_inj_monic hca (hca.coprod A) i
/-- The `i`-th pullback `Pᵢ` (cospan `Sᴵ —pᵢ→ S ←uᵢ— Aᵢ`). -/
private noncomputable def pfcPb (i : I) :=
  HasPullbacks.has (hpow.proj (A := pfcS hca A) i) (pfcInj hca A i)
/-- `Pᵢ` as a SUBOBJECT of `Sᴵ` (leg `π₁`, monic since `uᵢ` is). -/
private noncomputable def pfcSub (i : I) : Subobject 𝒞 (hpow.pow I (pfcS hca A)) :=
  ⟨(pfcPb hpow hca A i).cone.pt, (pfcPb hpow hca A i).cone.π₁,
    mono_pullback _ _ (pfcInj_monic hca A i) (pfcPb hpow hca A i)⟩
/-- The product object `∏ᵢAᵢ := ⋂ᵢ Pᵢ`. -/
private noncomputable def pfcProd : 𝒞 := (familyMeet hpow (pfcSub hpow hca A)).dom
/-- The witness `wᵢ : (⋂).dom → Pᵢ.pt` of `⋂ ≤ Pᵢ`. -/
private noncomputable def pfcW (i : I) : pfcProd hpow hca A ⟶ (pfcPb hpow hca A i).cone.pt :=
  (familyMeet_le hpow (pfcSub hpow hca A) i).choose
private theorem pfcW_spec (i : I) :
    pfcW hpow hca A i ≫ (pfcSub hpow hca A i).arr = (familyMeet hpow (pfcSub hpow hca A)).arr :=
  (familyMeet_le hpow (pfcSub hpow hca A) i).choose_spec
/-- The product projection `π i := wᵢ ≫ π₂ : (⋂).dom → Aᵢ`. -/
private noncomputable def pfcProj (i : I) : pfcProd hpow hca A ⟶ A i :=
  pfcW hpow hca A i ≫ (pfcPb hpow hca A i).cone.π₂

/-- The tuple `t := ⟨g i ≫ uᵢ⟩ᵢ : X ⟶ Sᴵ` for a cone `g : ∀i, X ⟶ Aᵢ`. -/
private noncomputable def pfcT {X : 𝒞} (g : ∀ i, X ⟶ A i) : X ⟶ hpow.pow I (pfcS hca A) :=
  hpow.tupling (fun i => g i ≫ pfcInj hca A i)
private theorem pfcT_proj {X : 𝒞} (g : ∀ i, X ⟶ A i) (i : I) :
    pfcT hpow hca A g ≫ hpow.proj i = g i ≫ pfcInj hca A i := hpow.tupling_proj _ i

/-- `t` factors through each `Pᵢ` via `pb.lift (X, g i, t)`. -/
private noncomputable def pfcLt {X : 𝒞} (g : ∀ i, X ⟶ A i) (i : I) :
    X ⟶ (pfcPb hpow hca A i).cone.pt :=
  (pfcPb hpow hca A i).lift ⟨X, pfcT hpow hca A g, g i,
    by rw [pfcT_proj]⟩
private theorem pfcLt_fst {X : 𝒞} (g : ∀ i, X ⟶ A i) (i : I) :
    pfcLt hpow hca A g i ≫ (pfcPb hpow hca A i).cone.π₁ = pfcT hpow hca A g :=
  (pfcPb hpow hca A i).lift_fst _
private theorem pfcLt_snd {X : 𝒞} (g : ∀ i, X ⟶ A i) (i : I) :
    pfcLt hpow hca A g i ≫ (pfcPb hpow hca A i).cone.π₂ = g i :=
  (pfcPb hpow hca A i).lift_snd _

private theorem pfcT_factors {X : 𝒞} (g : ∀ i, X ⟶ A i) :
    ∀ i, ∃ l, l ≫ (pfcSub hpow hca A i).arr = pfcT hpow hca A g :=
  fun i => ⟨pfcLt hpow hca A g i, pfcLt_fst hpow hca A g i⟩

/-- The tupling `tup := X ⟶ (⋂).dom` from `familyMeet_lift`. -/
private noncomputable def pfcTup {X : 𝒞} (g : ∀ i, X ⟶ A i) : X ⟶ pfcProd hpow hca A :=
  (familyMeet_lift hpow (pfcSub hpow hca A) (pfcT hpow hca A g) (pfcT_factors hpow hca A g)).choose
private theorem pfcTup_arr {X : 𝒞} (g : ∀ i, X ⟶ A i) :
    pfcTup hpow hca A g ≫ (familyMeet hpow (pfcSub hpow hca A)).arr = pfcT hpow hca A g :=
  (familyMeet_lift hpow (pfcSub hpow hca A) (pfcT hpow hca A g) (pfcT_factors hpow hca A g)).choose_spec

end ProductsFromCoproducts

/-- **§1.968 (Cocomplete → Complete): `HasProducts` from `HasAllCoproducts`** (cogenerator-free). -/
noncomputable def hasProducts_of_coproducts
    (hpow : @HasArbitraryPowers 𝒞 _ Topos.toHasBinaryProducts)
    (hca : HasAllCoproducts 𝒞) : HasProducts 𝒞 where
  prod {I} A :=
  { prod := pfcProd hpow hca A
    proj := fun i => pfcProj hpow hca A i
    lift := fun {X} g => pfcTup hpow hca A g
    lift_π := fun {X} g i => by
      -- `tup ≫ proj i = tup ≫ (wᵢ ≫ π₂)`.  Show `tup ≫ wᵢ = lt i` (both factor `t` through the
      -- monic `Pᵢ.π₁`), then `≫ π₂` gives `lt i ≫ π₂ = g i`.
      show pfcTup hpow hca A g ≫ (pfcW hpow hca A i ≫ (pfcPb hpow hca A i).cone.π₂) = g i
      have hagree : pfcTup hpow hca A g ≫ pfcW hpow hca A i = pfcLt hpow hca A g i := by
        refine (pfcSub hpow hca A i).monic _ _ ?_
        rw [Cat.assoc, pfcW_spec, pfcTup_arr]
        exact (pfcLt_fst hpow hca A g i).symm
      calc pfcTup hpow hca A g ≫ (pfcW hpow hca A i ≫ (pfcPb hpow hca A i).cone.π₂)
          = (pfcTup hpow hca A g ≫ pfcW hpow hca A i) ≫ (pfcPb hpow hca A i).cone.π₂ :=
            (Cat.assoc _ _ _).symm
        _ = pfcLt hpow hca A g i ≫ (pfcPb hpow hca A i).cone.π₂ := by rw [hagree]
        _ = g i := pfcLt_snd hpow hca A g i
    lift_uniq := fun {X} g h hh => by
      -- `⋂Pᵢ ↣ Sᴵ` monic: compare `h ≫ familyMeet.arr` and `tup ≫ familyMeet.arr = t`.
      refine (familyMeet hpow (pfcSub hpow hca A)).monic _ _ ?_
      rw [pfcTup_arr]
      -- `h ≫ familyMeet.arr = t`:  coordinatewise `(h ≫ familyMeet.arr) ≫ pⱼ = g j ≫ uⱼ`.
      refine hpow.tupling_uniq (fun j => g j ≫ pfcInj hca A j) _ (fun i => ?_)
      -- route `familyMeet.arr` through `Pᵢ`:  `= wᵢ ≫ π₁`, and `π₁ ≫ pᵢ = π₂ ≫ uᵢ`.
      have hpb_w : (pfcPb hpow hca A i).cone.π₁ ≫ hpow.proj (A := pfcS hca A) i
          = (pfcPb hpow hca A i).cone.π₂ ≫ pfcInj hca A i := (pfcPb hpow hca A i).cone.w
      -- `h ≫ proj(product) i = g i`, where `proj(product) i = wᵢ ≫ π₂`.
      have hhi : h ≫ (pfcW hpow hca A i ≫ (pfcPb hpow hca A i).cone.π₂) = g i := hh i
      calc (h ≫ (familyMeet hpow (pfcSub hpow hca A)).arr) ≫ hpow.proj i
          = (h ≫ (pfcW hpow hca A i ≫ (pfcSub hpow hca A i).arr)) ≫ hpow.proj i := by
              rw [pfcW_spec]
        _ = (h ≫ (pfcW hpow hca A i ≫ (pfcPb hpow hca A i).cone.π₁)) ≫ hpow.proj (A := pfcS hca A) i := rfl
        _ = (h ≫ pfcW hpow hca A i) ≫ ((pfcPb hpow hca A i).cone.π₁ ≫ hpow.proj (A := pfcS hca A) i) := by
              simp only [Cat.assoc]
        _ = (h ≫ pfcW hpow hca A i) ≫ ((pfcPb hpow hca A i).cone.π₂ ≫ pfcInj hca A i) := by rw [hpb_w]
        _ = (h ≫ (pfcW hpow hca A i ≫ (pfcPb hpow hca A i).cone.π₂)) ≫ pfcInj hca A i := by
              rw [Cat.assoc, Cat.assoc, Cat.assoc]
        _ = g i ≫ pfcInj hca A i := by rw [hhi] }

/-! ### Complete → Cocomplete: monic, pairwise-disjoint embeddings `Aᵢ ↣ ∏ⱼ(Aⱼ+1)`. -/

section CoproductsFromProducts
variable (hp : HasProducts 𝒞)

/-- Ambient `B := ∏ⱼ(Aⱼ+1)`. -/
noncomputable def cfpAmb {I : Type v} (A : I → 𝒞) : 𝒞 :=
  (hp.prod (fun j => coprodObj (A j) (one : 𝒞))).prod

/-- `j`-th coordinate of the embedding `uᵢ`: `inl : Aᵢ↣Aᵢ+1` at `j=i`, else `Aᵢ→1→inr Aⱼ+1`. -/
noncomputable def cfpCoord {I : Type v} (A : I → 𝒞) (i j : I) :
    A i ⟶ coprodObj (A j) (one : 𝒞) :=
  if h : j = i then (h ▸ coprodInl (A i) (one : 𝒞) : A i ⟶ coprodObj (A j) (one : 𝒞))
  else term (A i) ≫ coprodInr (A j) (one : 𝒞)

/-- The embedding `uᵢ : Aᵢ ⟶ ∏ⱼ(Aⱼ+1)`. -/
noncomputable def cfpEmbed {I : Type v} (A : I → 𝒞) (i : I) : A i ⟶ cfpAmb hp A :=
  (hp.prod (fun j => coprodObj (A j) (one : 𝒞))).lift (fun j => cfpCoord A i j)

/-- `uᵢ ≫ projⱼ = cfpCoord A i j`. -/
theorem cfpEmbed_proj {I : Type v} (A : I → 𝒞) (i j : I) :
    cfpEmbed hp A i ≫ (hp.prod (fun j => coprodObj (A j) (one : 𝒞))).proj j = cfpCoord A i j :=
  (hp.prod (fun j => coprodObj (A j) (one : 𝒞))).lift_π _ j

/-- `uᵢ` is MONIC: its `i`-th coordinate is `coprodInl (Aᵢ) 1`, which is monic. -/
theorem cfpEmbed_monic {I : Type v} (A : I → 𝒞) (i : I) : Monic (cfpEmbed hp A i) := by
  intro W u v huv
  have hi : (u ≫ cfpEmbed hp A i) ≫ (hp.prod (fun j => coprodObj (A j) (one : 𝒞))).proj i
      = (v ≫ cfpEmbed hp A i) ≫ (hp.prod (fun j => coprodObj (A j) (one : 𝒞))).proj i := by
    rw [huv]
  rw [Cat.assoc, Cat.assoc, cfpEmbed_proj, cfpCoord, dif_pos rfl] at hi
  -- `u ≫ inl = v ≫ inl` (the `i=i` branch); `inl` monic ⟹ `u = v`.
  exact coprodInl_monic (A i) (one : 𝒞) u v (by simpa using hi)

include hp in
/-- **DISJOINTNESS.**  For `i ≠ j`, any two maps out of the `(uᵢ, uⱼ)` pullback apex agree.
    Project to coordinate `i`: `uᵢ` is `inl`, `uⱼ` is `term ≫ inr`, so the apex is a common point
    of `inl, inr : · → Aᵢ+1` — its pullback is `≅ 0` (`coprodInjections_disjoint`), hence the apex
    maps to `0` and is zero-like (any two maps out agree). -/
theorem cfpEmbed_disjoint {I : Type v} (A : I → 𝒞) {i j : I} (hij : i ≠ j) {Z : 𝒞}
    (u v : (HasPullbacks.has (cfpEmbed hp A i) (cfpEmbed hp A j)).cone.pt ⟶ Z) : u = v := by
  let pb := HasPullbacks.has (cfpEmbed hp A i) (cfpEmbed hp A j)
  let P : 𝒞 := pb.cone.pt
  -- project the pullback square to coordinate i.
  have hcoord : pb.cone.π₁ ≫ coprodInl (A i) (one : 𝒞)
      = pb.cone.π₂ ≫ (term (A j) ≫ coprodInr (A i) (one : 𝒞)) := by
    have h : pb.cone.π₁ ≫ (cfpEmbed hp A i ≫ (hp.prod (fun j => coprodObj (A j) (one : 𝒞))).proj i)
        = pb.cone.π₂ ≫ (cfpEmbed hp A j ≫ (hp.prod (fun j => coprodObj (A j) (one : 𝒞))).proj i) := by
      rw [← Cat.assoc, ← Cat.assoc, pb.cone.w]
    rw [cfpEmbed_proj, cfpEmbed_proj, cfpCoord, cfpCoord, dif_pos rfl, dif_neg hij] at h
    exact h
  -- collapse to a cone over `(coprodInl (A i) 1, coprodInr (A i) 1)` with apex `P`.
  have hcollapse : pb.cone.π₁ ≫ coprodInl (A i) (one : 𝒞)
      = (pb.cone.π₂ ≫ term (A j)) ≫ coprodInr (A i) (one : 𝒞) := by
    rw [Cat.assoc]; exact hcoord
  let pbC := HasPullbacks.has (coprodInl (A i) (one : 𝒞)) (coprodInr (A i) (one : 𝒞))
  let c : Cone (coprodInl (A i) (one : 𝒞)) (coprodInr (A i) (one : 𝒞)) :=
    ⟨P, pb.cone.π₁, pb.cone.π₂ ≫ term (A j), hcollapse⟩
  let δ : P ⟶ pbC.cone.pt := pbC.lift c
  obtain ⟨e, _⟩ := coprodInjections_disjoint (A i) (one : 𝒞)
  obtain ⟨θ, _⟩ := bottomSub_dom_iso (coprodObj (A i) (one : 𝒞)) (one : 𝒞)
  let z : P ⟶ (bottomSub (one : 𝒞)).dom := δ ≫ e ≫ θ
  obtain ⟨zinv, hzz, _⟩ := any_map_to_zero_is_iso (inferInstance : PreLogos 𝒞) z
  let ct := minimal_subobject_of_one_is_coterminator (inferInstance : PreLogos 𝒞)
  calc u = (z ≫ zinv) ≫ u := by rw [hzz, Cat.id_comp]
    _ = z ≫ (zinv ≫ u) := Cat.assoc _ _ _
    _ = z ≫ (zinv ≫ v) := by rw [ct.init_uniq (zinv ≫ u) (zinv ≫ v)]
    _ = (z ≫ zinv) ≫ v := (Cat.assoc _ _ _).symm
    _ = v := by rw [hzz, Cat.id_comp]

end CoproductsFromProducts

/-- **§1.968 (Complete → Cocomplete): `HasAllCoproducts` from `HasProducts`** (cogenerator-free).
    Embeds each `Aᵢ` into the ambient `∏ⱼ(Aⱼ+1)` (monic `cfpEmbed`, pairwise-disjoint
    `cfpEmbed_disjoint`) and applies the banked `gcoCoproduct` carving — Freyd's "slight
    modification of §1.967 copowers-from-powers". -/
noncomputable def hasAllCoproducts_of_products (hp : HasProducts 𝒞) :
    HasAllCoproducts 𝒞 where
  coprod {_I} A :=
    gcoCoproduct (powersOfProducts hp) (cfpEmbed hp A) (cfpEmbed_monic hp A)
      (fun _ _ hij _ u v => cfpEmbed_disjoint hp A hij u v)

end CompleteCocompleteFree

/-- **§1.968** (Freyd, p. 130): *A locally small topos is complete iff it is cocomplete.*

    CLOSED Sorry-free, COGENERATOR-FREE, faithful to Freyd's BARE statement (no progenitor
    hypothesis) — see the `CompleteCocompleteFree` section header for the route.  Each direction
    builds its embeddings directly:

    * **→** (Freyd: "slight modification of §1.967").  `Complete` gives `HasProducts`
      (`complete_iff_eq_prod`); embed `Aᵢ ↣ ∏ⱼ(Aⱼ+1)` (`hasAllCoproducts_of_products`) → all
      coproducts; `cocomplete_of_coproducts_coequalizers` with the topos's `topos_has_coequalizers`.

    * **←** (Freyd's "easy" half).  `Cocomplete` gives `HasAllCoproducts`
      (`cocomplete_hasAllCoproducts`), hence copowers-of-1 → arbitrary powers
      (`powersOfCopowersOfOne`); carve each `∏ᵢAᵢ = ⋂ᵢ Pᵢ ⊆ Sᴵ` (`hasProducts_of_coproducts`,
      `S := ∐ᵢAᵢ`) → `HasProducts`; `complete_iff_eq_prod` with the topos's equalizers.

    The progenitor-using `hasAllCoproducts_of_progenitor` is the §1.969 Grothendieck route; it is
    NOT needed for the bare §1.968 — the coproduct/product themselves supply the embeddings. -/
theorem topos_complete_iff_cocomplete [LocallySmallTopos 𝒞]
    [HasBinaryProducts 𝒞] [HasBinaryCoproducts 𝒞] [HasEqualizers 𝒞] :
    Nonempty (Complete 𝒞) ↔ Nonempty (Cocomplete 𝒞) := by
  constructor
  · -- Complete → Cocomplete.
    rintro ⟨hc⟩
    obtain ⟨_, ⟨hp⟩⟩ := (complete_iff_eq_prod 𝒞).mp ⟨hc⟩
    let hca : HasAllCoproducts 𝒞 := hasAllCoproducts_of_products hp
    exact ⟨cocomplete_of_coproducts_coequalizers hca topos_has_coequalizers⟩
  · -- Cocomplete → Complete.
    rintro ⟨hc⟩
    let hca : HasAllCoproducts 𝒞 := cocomplete_hasAllCoproducts hc
    -- copowers-of-1 from the constant-`one` coproduct (cf. `lawvere_eq_tierney`).
    let cpo : (I : Type v) → CopowerOfOne I 𝒞 := fun I =>
      { obj := (hca.coprod (fun _ : I => (one : 𝒞))).obj
        inj := fun i => (hca.coprod (fun _ : I => (one : 𝒞))).inj i
        cotup := fun {X} f => (hca.coprod (fun _ : I => (one : 𝒞))).desc f
        inj_cotup := fun {X} f i => (hca.coprod (fun _ : I => (one : 𝒞))).fac f i
        cotup_uniq := fun {X} f h hh => (hca.coprod (fun _ : I => (one : 𝒞))).uniq f h hh }
    let hpow : @HasArbitraryPowers 𝒞 _ Topos.toHasBinaryProducts := powersOfCopowersOfOne cpo
    let hp : HasProducts 𝒞 := hasProducts_of_coproducts hpow hca
    exact (complete_iff_eq_prod 𝒞).mpr ⟨⟨inferInstance⟩, ⟨hp⟩⟩

/-- **§1.969**: The LAWVERE DEFINITION of a Grothendieck topos: a cocomplete topos with a
    generating set. -/
class LawvereGrothendieckTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends Topos 𝒞 where
  /-- Arbitrary coproducts exist. -/
  cocomplete : Cocomplete 𝒞
  /-- A SMALL generating set (§1.84, §1.632, §1.969), presented as a `Type v`-indexed family
      `gen_obj : gen_idx → 𝒞` — exactly the Giraud/`GrothendieckTopos` (S1_84) presentation.
      FIDELITY (§1.969): "a generating SET" is SMALL by definition (an index in universe `v`); the
      earlier bare `gen_set : 𝒞 → Prop` dropped that smallness, so `∐(gen set)` — hence a single
      progenitor `G := ∐(gen set)` (the Lawvere→Tierney bridge) — could not even be FORMED
      (`cocomplete_hasAllCoproducts` needs a `Type v` index).  Carrying the small index is the
      faithful presentation, parallel to the `copow_one` fidelity fix below. -/
  gen_idx : Type v
  gen_obj : gen_idx → 𝒞
  has_gen_set : IsGeneratingSet (fun X => ∃ k, gen_obj k = X)

/-- The underlying predicate of the Lawvere generating set: `X` is a generator iff it is
    `gen_obj k` for some index `k`. -/
def LawvereGrothendieckTopos.gen_set (𝒞 : Type u) [Cat.{v} 𝒞] [LawvereGrothendieckTopos 𝒞] :
    𝒞 → Prop := fun X => ∃ k, LawvereGrothendieckTopos.gen_obj (𝒞 := 𝒞) k = X

/-- **§1.969**: The TIERNEY DEFINITION of a Grothendieck topos: a topos with a progenitor and
    arbitrary copowers of 1. -/
class TierneyGrothendieckTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends Topos 𝒞,
    HasBinaryCoproducts 𝒞 where
  /-- A progenitor exists. -/
  progenitor : 𝒞
  is_progenitor : IsProgenitor progenitor
  /-- Arbitrary copowers of 1 exist.  FIDELITY (§1.969): a copower IS a colimit and carries the
      FULL universal property — existence AND uniqueness of the cotupling.  The earlier bare
      `∃ h, ∀ i, inj i ≫ h = f i` dropped uniqueness, under-specifying "copower"; a genuine
      `CopowerOfOne I 𝒞` (with `cotup_uniq`, i.e. the injections jointly epic) is what
      "arbitrary copowers of 1" means and what `powersOfCopowersOfOne` (hence the cogenerator
      route) consumes. -/
  copow_one : (I : Type v) → CopowerOfOne I 𝒞


/-- **§1.969**: The Lawvere and Tierney definitions yield the same notion.

    CLOSED Sorry-free (axioms `[propext, Classical.choice, Quot.sound]`).  Both directions go
    through the banked coproduct-assembly infra below; the last residual — Lawvere→Tierney's
    progenitor needing each general coproduct injection `gen_obj k ↣ ∐ gen_obj` MONIC — is now
    discharged by `coproduct_inj_monic` (§1.845, binary regrouping; see its docstring).

    BANKED (reusable, Sorry-free):
    * **`wellPoweredSub_of_topos`** (§1.843, above) — `WellPoweredSub 𝒞` from the classifier alone,
      so `LocallySmallTopos.wellPowered` (hence every copower lemma here) is available from bare
      Tierney/Lawvere data.  (Old blocker 2 CLOSED.)
    * **`copow_one`** now delivers a genuine `CopowerOfOne I 𝒞` (with `cotup_uniq`), so the
      copower-of-1 → `HasArbitraryPowers` (`powersOfCopowersOfOne`) → cogenerator route is
      unobstructed.  (Old blocker 1 CLOSED, by the fidelity strengthening of the class field.)
    * **`cocomplete_of_coproducts_coequalizers`** (§1.968, above) — `Cocomplete` reduces to
      `HasAllCoproducts` + `HasCoequalizers`; the topos supplies `topos_has_coequalizers`.  (The
      `coeq + coproducts ⟹ Cocomplete` part of old blocker 3 CLOSED.)
    * **`cocomplete_hasAllCoproducts`** (above) — `Cocomplete ⟹ HasAllCoproducts` (discrete-diagram
      colimit), so the Lawvere side's bundled `cocomplete` field DOES give all coproducts directly.
    * Tierney→Lawvere generating set: `IsProgenitor G` IS `IsGeneratingSet (fun X => ∃ m:X⟶G, Monic m)`
      definitionally.  Lawvere→Tierney `copow_one`: `∐ᵢ1` is the `cocomplete_hasAllCoproducts`
      coproduct of the constant-`one` family, which IS a `CopowerOfOne` (`cotup_uniq` = `Coproduct.uniq`).

    (HISTORICAL — the two blockers below are now mostly resolved; see UPDATE.)  The former
    blockers were (1) the general-family cogenerator-carving `∐ᵢAᵢ ⊆ C^K`, and (2) the
    Lawvere→Tierney progenitor (then blocked on `gen_set`'s missing `Type v` smallness index).

    UPDATE — general-coproduct carving (1) NOW BANKED (`hasAllCoproducts_of_progenitor`); the
    `gen_set` smallness index (2) is now a class field (the permitted fidelity fix).
    Tierney→Lawvere CLOSES Sorry-free (general coproducts + coequalizers ⟹ cocomplete; the
    progenitor's well-powered subobject family is the small generating set).  Lawvere→Tierney's
    `copow_one` also closes (constant-`one` coproduct), and its PROGENITOR `G := ∐(gen set)` closes
    via `coproduct_inj_monic`: each general coproduct injection `gen_obj k ↣ ∐` is MONIC (§1.845
    binary regrouping `gen_obj k ⊔ ∐_{i≠k}` + `coprodInl_monic`), so each generator is a SUBOBJECT
    of `G`, as `IsProgenitor` demands. -/
theorem lawvere_eq_tierney (𝒞 : Type u) [Cat.{v} 𝒞] :
    Nonempty (LawvereGrothendieckTopos 𝒞) ↔ Nonempty (TierneyGrothendieckTopos 𝒞) := by
  constructor
  · -- Lawvere → Tierney.
    rintro ⟨L⟩
    letI : Topos 𝒞 := L.toTopos
    letI lst : LocallySmallTopos 𝒞 := { toTopos := L.toTopos, wellPowered := wellPoweredSub_of_topos 𝒞 }
    -- `Cocomplete ⟹ HasAllCoproducts ⟹ copowers-of-1`.
    let hca : HasAllCoproducts 𝒞 := cocomplete_hasAllCoproducts L.cocomplete
    refine ⟨{
      toTopos := L.toTopos
      toHasBinaryCoproducts := inferInstance
      -- copow_one I: the constant-`one`-family coproduct IS a copower-of-1.
      copow_one := fun I =>
        { obj := (hca.coprod (fun _ : I => (one : 𝒞))).obj
          inj := fun i => (hca.coprod (fun _ : I => (one : 𝒞))).inj i
          cotup := fun {X} f => (hca.coprod (fun _ : I => (one : 𝒞))).desc f
          inj_cotup := fun {X} f i => (hca.coprod (fun _ : I => (one : 𝒞))).fac f i
          cotup_uniq := fun {X} f h hh => (hca.coprod (fun _ : I => (one : 𝒞))).uniq f h hh }
      -- progenitor: G := ∐(gen set).  CLOSED: `IsProgenitor (∐ gen_obj)` = subobjects of
      -- `∐ gen_obj` generate.  The family `gen_obj` generates (`has_gen_set`), and each generator
      -- `gen_obj k` is a SUBOBJECT of `∐ gen_obj` via its injection `inj k`, which is MONIC by
      -- `coproduct_inj_monic` (§1.845, binary regrouping `gen_obj k ⊔ ∐_{i≠k}` + `coprodInl_monic`).
      progenitor := (hca.coprod L.gen_obj).obj
      is_progenitor := by
        -- `IsProgenitor G` = `IsGeneratingSet (fun X => ∃ m : X ⟶ G, Monic m)`.  The family
        -- `gen_obj` generates (`has_gen_set`); each `gen_obj k` is a SUBOBJECT of `G := ∐ gen_obj`
        -- via the monic injection `inj k` (`coproduct_inj_monic`), so the progenitor's subobjects
        -- generate too: relay the separation hypothesis from subobjects to generators.
        intro A B f g hsep
        refine L.has_gen_set f g (fun X ⟨k, hk⟩ h => ?_)
        -- `X = gen_obj k`; its injection `inj k : gen_obj k ↣ G` is monic, so `X ∈ Sub(G)`.
        subst hk
        exact hsep _ ⟨(hca.coprod L.gen_obj).inj k, coproduct_inj_monic hca (hca.coprod L.gen_obj) k⟩ h }⟩
  · -- Tierney → Lawvere.
    rintro ⟨T⟩
    letI : Topos 𝒞 := T.toTopos
    letI lst : LocallySmallTopos 𝒞 := { toTopos := T.toTopos, wellPowered := wellPoweredSub_of_topos 𝒞 }
    letI : HasBinaryCoproducts 𝒞 := T.toHasBinaryCoproducts
    -- arbitrary powers from copowers-of-1; re-wrap the fields inline so the products instance is
    -- unified to whatever `hasAllCoproducts_of_progenitor` expects (mirrors `topos_powers_copowers_equiv`).
    let pw := powersOfCopowersOfOne T.copow_one
    let hca : HasAllCoproducts 𝒞 := hasAllCoproducts_of_progenitor T.progenitor T.is_progenitor
      { pow := pw.pow, proj := fun {I A} => pw.proj, tupling := fun {I A X} => pw.tupling,
        tupling_proj := fun {I A X} => pw.tupling_proj,
        tupling_uniq := fun {I A X} => pw.tupling_uniq }
    let hce : HasCoequalizers 𝒞 := topos_has_coequalizers
    -- small generating set = the well-powered enumeration of `Sub(progenitor)`.
    let wp := wellPoweredSub_of_topos 𝒞
    refine ⟨{
      toTopos := T.toTopos
      cocomplete := cocomplete_of_coproducts_coequalizers hca hce
      gen_idx := wp.idx T.progenitor
      gen_obj := fun k => (wp.enum k).dom
      has_gen_set := by
        -- `is_progenitor` = subobjects of `G` generate; the small family enumerates
        -- representatives of all of `Sub(G)`, so it generates (transport across the
        -- subobject iso `enum k ≅ ⟨X,m⟩`).
        intro X Y f g hsep
        refine T.is_progenitor f g (fun X' ⟨m, hm⟩ h => ?_)
        -- `⟨X', m, hm⟩ : Sub(G)`; `wp.surj` gives `k` with `enum k ≅ ⟨X',m⟩`.
        obtain ⟨k, hle, hge⟩ := wp.surj ⟨X', m, hm⟩
        -- iso of domains: `w : X' → dom(enum k)`, `w' : dom(enum k) → X'`, mutually inverse.
        obtain ⟨w, hw⟩ := hle    -- w ≫ (enum k).arr = m
        obtain ⟨w', hw'⟩ := hge  -- w' ≫ m = (enum k).arr
        -- w' is iso (w'≫w = id, w≫w' = id via cancelling the monics m, (enum k).arr).
        have hwid : w ≫ w' = Cat.id X' :=
          hm _ _ (by rw [Cat.assoc, hw', hw, Cat.id_comp])
        have hwid' : w' ≫ w = Cat.id (wp.enum k).dom :=
          (wp.enum k).monic _ _ (by rw [Cat.assoc, hw, hw', Cat.id_comp])
        -- the gen family contains `dom(enum k)`; the hypothesis gives `(w'≫h)≫f = (w'≫h)≫g`.
        have hwh := hsep (wp.enum k).dom ⟨k, rfl⟩ (w' ≫ h)
        -- precompose by `w` (w≫w'=id) to recover `h≫f = h≫g`.
        have key : w ≫ ((w' ≫ h) ≫ f) = w ≫ ((w' ≫ h) ≫ g) := by rw [hwh]
        calc h ≫ f = (Cat.id X' ≫ h) ≫ f := by rw [Cat.id_comp]
          _ = ((w ≫ w') ≫ h) ≫ f := by rw [hwid]
          _ = w ≫ ((w' ≫ h) ≫ f) := by simp only [Cat.assoc]
          _ = w ≫ ((w' ≫ h) ≫ g) := key
          _ = ((w ≫ w') ≫ h) ≫ g := by simp only [Cat.assoc]
          _ = (Cat.id X' ≫ h) ≫ g := by rw [hwid]
          _ = h ≫ g := by rw [Cat.id_comp] }⟩

end Freyd
