/-
  Freyd & Scedrov, *Categories and Allegories* §1.944 — a topos has a STRICT
  COTERMINATOR (initial object `0`).

  The carrier is `Z := (bottomSub one).dom`, the domain of the empty/bottom
  subobject `∅_1 ↪ 1` built (Sorry-free) in `Freyd/ToposColimits.lean` as the
  family-glb `⋂{all σ ⊆ 1}`.  We show `StrictCoterminator Z`: every `f : X → Z`
  is an isomorphism, hence (via `HasCoterminator.ofStrict`, S1_58) `Z` is initial.

  The proof mirrors `Freyd.any_map_to_zero_is_iso` (S1_61), but replaces the
  `PreLogos.bottom` field — which a topos does NOT carry (that route is circular
  on §1.543) — by `bottomSub` plus the §1.946 right-adjoint EMPTINESS lemma
  `g*(∅) ≤ ∅` (`invImage_bottomSub_le`), proved from `radjImage_adjunction`.

  The one cross-base seed `∅_A.dom ≅ ∅_B.dom` (`bottomSub_dom_iso`, ⇔ existence of
  `0 → A`) is closed Sorry-free by the EMPTY-SINGLETON argument (`bottomSub_dom_iso_one`):
  `K := {a | {a} = ∅}` (pullback of `singletonMap A` along `nameOf ∅_A`) is subterminal,
  and the pullback square forces `a ∈ {a} = a ∈ ∅`, so the classifier UMP factors `K`
  through `∅_A`, yielding `∅_A.dom ≅ K ≅ Z₁`.  Axioms: `[propext, Classical.choice]`.
-/

module

public import Freyd.S1_946_RightAdjointImage
public import Freyd.S1_95_ToposColimits
public import Freyd.S1_58
public import Freyd.S1_61

open Freyd HasSubobjectClassifier

universe v u
variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

namespace Freyd

/-- **§1.946 emptiness.** Inverse image carries the bottom subobject to (below) the
    bottom subobject: `g*(∅_B) ≤ ∅_A`.  This is the backward direction of the
    `f* ⊣ f##` adjunction applied to `∅_B ≤ f##(∅_A)` (= `bottomSub_le`, ⊥ ≤ anything). -/
public theorem invImage_bottomSub_le {A B : 𝒞} (g : A ⟶ B) :
    (InverseImage g (bottomSub B)).le (bottomSub A) :=
  (radjImage_adjunction g (bottomSub B) (bottomSub A)).2
    (bottomSub_le (radjImage g (bottomSub A)))

/-- Two subobjects of a common base that are mutually `≤` have isomorphic domains:
    the factoring maps `h : S.dom → T.dom`, `k : T.dom → S.dom` are mutual inverses
    (by left-cancelling the monics `S.arr`, `T.arr`). -/
public theorem le_le_dom_iso {A : 𝒞} (S T : Subobject 𝒞 A) (hST : S.le T) (hTS : T.le S) :
    Isomorphic S.dom T.dom := by
  obtain ⟨h, hh⟩ := hST
  obtain ⟨k, hk⟩ := hTS
  refine ⟨h, k, ?_, ?_⟩
  · apply S.monic; rw [Cat.assoc, hk, hh, Cat.id_comp]
  · apply T.monic; rw [Cat.assoc, hh, hk, Cat.id_comp]

/-- The inverse image `g*(∅_B)` of the bottom has the SAME domain (up to iso) as
    `∅_A`: `≤` holds both ways (emptiness lemma + `bottomSub_le`). -/
public theorem invImage_bottomSub_dom_iso {A B : 𝒞} (g : A ⟶ B) :
    Isomorphic (InverseImage g (bottomSub B)).dom (bottomSub A).dom :=
  le_le_dom_iso _ _ (invImage_bottomSub_le g) (bottomSub_le _)

/-! ### The empty-singleton contradiction: closing the seed `∅_A.dom ≅ Z₁`

  The seed reduces (via `isomorphic_symm`/`isomorphic_trans`) to `bottomSub_dom_iso A one`, i.e.
  `∅_A.dom ≅ Z₁` where `Z₁ := (bottomSub one).dom`.  The previous obstruction was the
  EXISTENCE of `0 ⟶ A`.  We close it by the **empty-singleton** argument, entirely inside
  the §1.92/§1.94 exponential power-object framework (`singletonMap`, `membershipMap`,
  `diag_classify_iff`), all Sorry-free:

  Let `K := pullback of {·}=singletonMap A : A → [A] along the empty-set name
  u := nameOf ∅_A : 1 → [A]` — i.e. `K = {a : A | {a} = ∅}`.  Then:
  * `K` is SUBTERMINAL (`k1 : K ↪ 1` is the pullback of the monic `singletonMap A`), so every
    map out of `K` is forced-unique; in particular `kA : K → A` is monic.
  * On `K` the pullback square `kA ≫ {·} = k1 ≫ u` makes `a ∈ {a}` equal to `a ∈ ∅`.  But
    `a ∈ {a} = ⊤` (`mem_singleton_self`, from `diag_classify_iff`) while `a ∈ ∅ = χ_{∅_A}` at
    `a`, so `kA ≫ χ_{∅_A} = ⊤∘!`; the classifier UMP (`classify_pullback`) factors `kA`
    through `∅_A`, giving `K ≤ ∅_A`.  With `bottomSub_le` (`∅_A ≤ K`) this is `∅_A.dom ≅ K`.
  * `K ↪ 1` gives `Z₁ ≤ K` (`bottomSub_le`); and `∅_A.dom ≅ K` composed with the canonical
    `∅_A.dom → Z₁` (the pullback leg `π₂` of `invImage_bottomSub_dom_iso (term A)`) gives
    `K ≤ Z₁`.  Hence `K ≅ Z₁`, so `∅_A.dom ≅ Z₁`. -/

/-- `a ∈ {a} = ⊤`: the singleton of a (generalized) point contains that point.  The membership
    test `⟨a, a ≫ {·}⟩ ≫ eval` of `a` in `{a} = a ≫ singletonMap A` is `⊤∘!`, since
    `singletonMap A = curry χ_Δ` and `χ_Δ ⟨a,a⟩ = ⊤` (`diag_classify_iff`, reflexivity). -/
public theorem mem_singleton_self {X A : 𝒞} (a : X ⟶ A) :
    pair a (a ≫ singletonMap A) ≫ eval_exp A (omega (𝒞 := 𝒞))
      = term X ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
  -- singletonMap A = curry χ_Δ;  ⟨a, a ≫ curry χ_Δ⟩ = ⟨a,a⟩ ≫ ⟨fst, snd ≫ curry χ_Δ⟩
  -- and (A × curry χ_Δ) ≫ eval = χ_Δ, so the whole composite is ⟨a,a⟩ ≫ χ_Δ = ⊤∘! (a = a).
  have hev : pair a (a ≫ singletonMap A) ≫ eval_exp A (omega (𝒞 := 𝒞))
      = pair a a ≫ HasSubobjectClassifier.classify (diag A) (diag_mono A) := by
    rw [singletonMap, singletonMapCat]
    have hp : pair a (a ≫ curry (HasSubobjectClassifier.classify (diag A) (diag_mono A)))
        = pair a a ≫ prodMap A A (omega (𝒞 := 𝒞) ^^ A)
            (curry (HasSubobjectClassifier.classify (diag A) (diag_mono A))) :=
      (pair_uniq _ _ _
        (by rw [Cat.assoc, prodMap_fst, fst_pair])
        (by rw [Cat.assoc, prodMap_snd, ← Cat.assoc, snd_pair])).symm
    rw [hp, Cat.assoc, curry_eval_eq]
  rw [hev]
  exact (diag_classify_iff a a).2 rfl

/-- **Cross-base bottom-domain iso** (§1.944) — CLOSED.  `∅_A.dom ≅ ∅_B.dom` for all `A B`,
    via `bottomSub_dom_iso_one` and `isomorphic_symm`/`isomorphic_trans`. -/
public theorem bottomSub_dom_iso_one (A : 𝒞) :
    Isomorphic (bottomSub A).dom (bottomSub (one : 𝒞)).dom := by
  -- u : 1 → [A] is the name of the empty subobject ∅_A.  membershipMap u = χ_{∅_A}.
  let u : one ⟶ powObj A := nameOf (bottomSub A).arr (bottomSub A).monic
  have hmem : membershipMap u = HasSubobjectClassifier.classify (bottomSub A).arr (bottomSub A).monic :=
    membershipMap_nameOf _ _
  -- K := pullback of {·} = singletonMap A along u.
  let pb := HasPullbacks.has u (singletonMap A)
  let K : 𝒞 := pb.cone.pt
  let k1 : K ⟶ one := pb.cone.π₁
  let kA : K ⟶ A := pb.cone.π₂
  -- pullback square: kA ≫ {·} = k1 ≫ u.
  have hsq : kA ≫ singletonMap A = k1 ≫ u := pb.cone.w.symm
  -- k1 is monic (pullback of the monic singletonMap A), hence K is SUBTERMINAL.
  have hk1_mono : Monic k1 := by
    intro W g h hgh
    -- agree on the {·}-leg via the pullback square + singletonMap A monic
    have hleg : (g ≫ kA) ≫ singletonMap A = (h ≫ kA) ≫ singletonMap A := by
      rw [Cat.assoc, Cat.assoc, hsq, ← Cat.assoc, ← Cat.assoc, hgh]
    have hkA : g ≫ kA = h ≫ kA := singletonMap_monic A _ _ hleg
    -- pullback uniqueness from agreement on both legs (π₁ via hgh, π₂ via hkA)
    have hw : (g ≫ k1) ≫ u = (g ≫ kA) ≫ singletonMap A := by
      rw [Cat.assoc, Cat.assoc, ← hsq]
    exact (pb.lift_uniq ⟨W, g ≫ k1, g ≫ kA, hw⟩ g rfl rfl).trans
      (pb.lift_uniq ⟨W, g ≫ k1, g ≫ kA, hw⟩ h hgh.symm hkA.symm).symm
  -- k1 = term K (the only map K → 1).
  have hk1_term : k1 = term K := term_uniq _ _
  -- On K, "a ∈ {a}" = "a ∈ ∅", so kA ≫ χ_{∅_A} = ⊤∘!.
  have hkA_class : kA ≫ HasSubobjectClassifier.classify (bottomSub A).arr (bottomSub A).monic
      = term K ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
    -- kA ≫ χ_{∅_A} = kA ≫ membershipMap u = ⟨kA, term K ≫ u⟩ ≫ eval
    have h1 : kA ≫ HasSubobjectClassifier.classify (bottomSub A).arr (bottomSub A).monic
        = pair kA (term K ≫ u) ≫ eval_exp A (omega (𝒞 := 𝒞)) := by
      rw [← hmem, membershipMap, ← Cat.assoc]
      congr 1
      exact pair_uniq _ _ _
        (by rw [Cat.assoc, fst_pair, Cat.comp_id])
        (by rw [Cat.assoc, snd_pair, ← Cat.assoc, term_uniq (kA ≫ term A) (term K)])
    -- term K ≫ u = k1 ≫ u = kA ≫ {·}, so the eval = ⟨kA, kA ≫ {·}⟩ ≫ eval = ⊤∘! (mem_singleton_self)
    have hsub : term K ≫ u = kA ≫ singletonMap A := by rw [← hk1_term, hsq]
    rw [h1, hsub, mem_singleton_self]
  -- classifier UMP: kA factors through ∅_A.arr — gives K ≤ ∅_A (as subobjects of A via kA).
  have hkA_mono : Monic kA := by
    -- K is subterminal (k1 monic), so any two maps W → K agree (via term-uniqueness on the k1-leg).
    intro W g h _; exact hk1_mono g h (term_uniq (g ≫ k1) (h ≫ k1))
  -- the classifying pullback of ∅_A lifts ⟨K, kA, term K⟩.
  obtain ⟨w, ⟨hw_arr, _⟩, _⟩ :=
    HasSubobjectClassifier.classify_pullback (bottomSub A).arr (bottomSub A).monic
      ⟨K, kA, term K, hkA_class⟩
  -- K ≤ ∅_A : the lift w : K → ∅_A.dom with w ≫ ∅_A.arr = kA.
  have hKsubA : (⟨K, kA, hkA_mono⟩ : Subobject 𝒞 A).le (bottomSub A) := ⟨w, hw_arr⟩
  -- ∅_A ≤ K : bottomSub is least.
  have hAsubK : (bottomSub A).le (⟨K, kA, hkA_mono⟩ : Subobject 𝒞 A) := bottomSub_le _
  -- hence ∅_A.dom ≅ K.
  have hiso_AK : Isomorphic (bottomSub A).dom K := le_le_dom_iso (bottomSub A) ⟨K, kA, hkA_mono⟩ hAsubK hKsubA
  -- Now view K and Z₁ as subobjects of 1 (both subterminal) and show K ≅ Z₁.
  -- Z₁ ≤ K : bottomSub one is least among subobjects of 1.
  have hZsubK : (bottomSub (one : 𝒞)).le (⟨K, k1, hk1_mono⟩ : Subobject 𝒞 one) := bottomSub_le _
  -- K ≤ Z₁ : compose ∅_A.dom ≅ K with the canonical ∅_A.dom → Z₁ (pullback π₂ leg of invImage).
  -- The InverseImage pullback `ipb` of (term A) and ∅_1.arr; its π₂ leg lands in Z₁,
  -- and `ipb.cone.pt` is DEFEQ to (InverseImage (term A) ∅_1).dom.
  let ipb := HasPullbacks.has (term A) (bottomSub (one : 𝒞)).arr
  have hinv : Isomorphic (InverseImage (term A) (bottomSub one)).dom (bottomSub A).dom :=
    invImage_bottomSub_dom_iso (term A)
  obtain ⟨ψ, _hφψ, _hψφ⟩ := hinv.choose_spec
  -- q : ∅_A.dom → Z₁  via ψ : ∅_A.dom → ipb.pt then the π₂ leg ipb.cone.π₂ : ipb.pt → Z₁.
  let q : (bottomSub A).dom ⟶ (bottomSub (one : 𝒞)).dom := ψ ≫ ipb.cone.π₂
  -- w : K → ∅_A.dom (the lift from hKsubA); then w ≫ q : K → Z₁ witnesses K ≤ Z₁.
  have hKsubZ : (⟨K, k1, hk1_mono⟩ : Subobject 𝒞 one).le (bottomSub (one : 𝒞)) := by
    refine ⟨w ≫ q, ?_⟩
    -- (w ≫ q) ≫ ∅_1.arr = k1 : both are maps K → 1, equal by terminal-uniqueness.
    exact term_uniq ((w ≫ q) ≫ (bottomSub (one : 𝒞)).arr) k1
  -- K ≅ Z₁, then ∅_A.dom ≅ K ≅ Z₁.
  have hiso_KZ : Isomorphic K (bottomSub (one : 𝒞)).dom :=
    le_le_dom_iso (⟨K, k1, hk1_mono⟩ : Subobject 𝒞 one) (bottomSub one) hKsubZ hZsubK
  exact isomorphic_trans hiso_AK hiso_KZ

/-- **Cross-base bottom-domain iso** (§1.944) — CLOSED.  `∅_A.dom ≅ ∅_B.dom` for all `A B`. -/
public theorem bottomSub_dom_iso (A B : 𝒞) :
    Isomorphic (bottomSub A).dom (bottomSub B).dom :=
  isomorphic_trans (bottomSub_dom_iso_one A) (isomorphic_symm (bottomSub_dom_iso_one B))

/-- **§1.944 strictness.** Every map into `Z := ∅_1.dom` is an isomorphism.
    Mirror of `any_map_to_zero_is_iso` (S1_61), with `bottomSub` for `PreLogos.bottom`,
    `invImage_bottomSub_dom_iso` for `invImage_preserves_bottom`, and
    `bottomSub_dom_iso` for `bottom_dom_iso`. -/
public theorem strict_coterminator_bottomSub_one :
    StrictCoterminator (bottomSub (one : 𝒞)).dom := by
  intro X f
  have hzeroMonic_mono : Monic (bottomSub (one : 𝒞)).arr := (bottomSub one).monic
  let p : X ⟶ one := term X
  -- f·∅₁.arr = p (both the unique map X → 1)
  have hp_eq : f ≫ (bottomSub (one : 𝒞)).arr = p := term_uniq _ _
  let pb := HasPullbacks.has p (bottomSub (one : 𝒞)).arr
  let c : Cone p (bottomSub (one : 𝒞)).arr := ⟨X, Cat.id X, f, by
    calc Cat.id X ≫ p = p := Cat.id_comp _
      _ = f ≫ (bottomSub one).arr := hp_eq.symm⟩
  let u : X ⟶ pb.cone.pt := pb.lift c
  have hu₁ : u ≫ pb.cone.π₁ = Cat.id X := pb.lift_fst c
  have hu₂ : u ≫ pb.cone.π₂ = f := pb.lift_snd c
  -- π₁ is monic (pullback of monic) = the inverse-image arr
  have hπ₁_mono : Monic pb.cone.π₁ := (InverseImage p (bottomSub one)).monic
  have hπ₁_iso : IsIso pb.cone.π₁ :=
    ⟨u, hπ₁_mono (pb.cone.π₁ ≫ u) (Cat.id pb.cone.pt) (by
      calc (pb.cone.π₁ ≫ u) ≫ pb.cone.π₁ = pb.cone.π₁ ≫ (u ≫ pb.cone.π₁) := Cat.assoc _ _ _
        _ = pb.cone.π₁ ≫ Cat.id X := by rw [hu₁]
        _ = pb.cone.π₁ := Cat.comp_id _
        _ = (Cat.id pb.cone.pt) ≫ pb.cone.π₁ := (Cat.id_comp _).symm), hu₁⟩
  have hu_iso : IsIso u := by
    rcases hπ₁_iso with ⟨inv, hπ₁_inv, hinv_π₁⟩
    have hu_eq_inv : u = inv := hπ₁_mono u inv (by rw [hu₁, hinv_π₁])
    rw [hu_eq_inv]; exact ⟨pb.cone.π₁, hinv_π₁, hπ₁_inv⟩
  -- emptiness iso + cross-base iso: pb.cone.pt ≅ ∅₁.dom
  have hinv : Isomorphic (InverseImage p (bottomSub one)).dom (bottomSub X).dom :=
    invImage_bottomSub_dom_iso p
  have hbot : Isomorphic (bottomSub X).dom (bottomSub (one : 𝒞)).dom :=
    bottomSub_dom_iso X one
  let φ : (InverseImage p (bottomSub one)).dom ⟶ (bottomSub X).dom := hinv.choose
  have hφ_iso : IsIso φ := hinv.choose_spec
  let ψ : (bottomSub X).dom ⟶ (bottomSub (one : 𝒞)).dom := hbot.choose
  have hψ_iso : IsIso ψ := hbot.choose_spec
  have hπ₂_eq : pb.cone.π₂ = φ ≫ ψ := by
    apply hzeroMonic_mono (pb.cone.π₂) (φ ≫ ψ)
    have h₁ : pb.cone.π₂ ≫ (bottomSub one).arr = pb.cone.π₁ ≫ p := pb.cone.w.symm
    have h₂ : (φ ≫ ψ) ≫ (bottomSub one).arr = pb.cone.π₁ ≫ p :=
      term_uniq ((φ ≫ ψ) ≫ (bottomSub one).arr) (pb.cone.π₁ ≫ p)
    calc pb.cone.π₂ ≫ (bottomSub one).arr = pb.cone.π₁ ≫ p := h₁
      _ = (φ ≫ ψ) ≫ (bottomSub one).arr := by rw [h₂]
  have hπ₂_iso : IsIso pb.cone.π₂ := by rw [hπ₂_eq]; exact isIso_comp hφ_iso hψ_iso
  rw [← hu₂]; exact isIso_comp hu_iso hπ₂_iso

/-- **§1.944** — a topos has a (strict) coterminator `Z := ∅_1.dom`.  Assembled from
    the strict-coterminator witness via `HasCoterminator.ofStrict` (S1_58), using the
    `[Topos 𝒞]`-supplied `HasBinaryProducts`.  Fully Sorry-free: the former seed
    `bottomSub_dom_iso` is now closed by the empty-singleton argument above. -/
public theorem topos_has_coterminator : Nonempty (HasCoterminator 𝒞) :=
  ⟨HasCoterminator.ofStrict strict_coterminator_bottomSub_one⟩

end Freyd
