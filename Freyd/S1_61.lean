import Freyd.S1_60 open Freyd
universe v u variable {𝒞 : Type u} [Cat.{v} 𝒞]
namespace Freyd

/-- **§1.61**: 0 is a coterminator (initial object). -/
noncomputable def minimal_subobject_of_one_is_coterminator (h : PreLogos 𝒞) : HasCoterminator 𝒞 :=
  let one : 𝒞 := h.toHasTerminal.one
  let zeroSub : Subobject 𝒞 one := h.bottom one
  let zeroObj : 𝒞 := zeroSub.dom
  let zeroMonic : zeroObj ⟶ one := zeroSub.arr
  let bot (A : 𝒞) : Subobject 𝒞 A := h.bottom A
  have bot_min {A : 𝒞} (S : Subobject 𝒞 A) : (bot A).le S := h.bottom_min S
  have bot_dom_iso (A : 𝒞) : Isomorphic (bot A).dom zeroObj := h.bottom_dom_iso A one
  have hzeroMonic_mono : Monic zeroMonic := (h.bottom one).monic
  -- coterminator maps
  have mk (A : 𝒞) : zeroObj ⟶ A :=
    let iso := bot_dom_iso A
    let inv : zeroObj ⟶ (bot A).dom := iso.choose_spec.choose
    inv ≫ (bot A).arr
  -- uniqueness: any two maps from 0 to A are equal
  have uniq {A : 𝒞} (f g : zeroObj ⟶ A) : f = g := by
    haveI : HasTerminal 𝒞 := h.toHasTerminal
    haveI : HasBinaryProducts 𝒞 := h.toHasBinaryProducts
    haveI : HasPullbacks 𝒞 := h.toHasPullbacks
    letI : HasEqualizers 𝒞 := products_pullbacks_implies_equalizers
    let eq := HasEqualizers.eq zeroObj A f g
    let e : eq.cone.dom ⟶ zeroObj := eq.cone.map
    have he_eq : e ≫ f = e ≫ g := eq.cone.eq
    have he_mono : Monic e := by
      intro W x y h
      let ec : EqualizerCone f g := ⟨W, x ≫ e, by
        calc (x ≫ e) ≫ f = x ≫ (e ≫ f) := Cat.assoc _ _ _
          _ = x ≫ (e ≫ g) := by rw [he_eq]
          _ = (x ≫ e) ≫ g := (Cat.assoc _ _ _).symm⟩
      have hx : x = eq.lift ec := eq.uniq ec x rfl
      have hy : y = eq.lift ec := eq.uniq ec y (by
        dsimp [ec]; rw [h])
      rw [hx, hy]
    have hez_mono : Monic (e ≫ zeroMonic) := by
      intro W x y hz
      apply he_mono x y
      apply hzeroMonic_mono (x ≫ e) (y ≫ e)
      calc (x ≫ e) ≫ zeroMonic = x ≫ (e ≫ zeroMonic) := Cat.assoc _ _ _
        _ = y ≫ (e ≫ zeroMonic) := by rw [hz]
        _ = (y ≫ e) ≫ zeroMonic := (Cat.assoc _ _ _).symm
    let S : Subobject 𝒞 one := ⟨eq.cone.dom, e ≫ zeroMonic, hez_mono⟩
    have hle : zeroSub.le S := bot_min S
    rcases hle with ⟨u, hu⟩
    have hue : u ≫ e = Cat.id zeroObj := by
      apply hzeroMonic_mono (u ≫ e) (Cat.id zeroObj)
      dsimp [S, zeroSub, zeroMonic] at hu
      calc (u ≫ e) ≫ zeroMonic = u ≫ (e ≫ zeroMonic) := Cat.assoc _ _ _
        _ = zeroMonic := by rw [hu]
        _ = (Cat.id zeroObj) ≫ zeroMonic := (Cat.id_comp _).symm
    have he_iso : IsIso e := by
      refine ⟨u, ?_, hue⟩
      apply he_mono (e ≫ u) (Cat.id eq.cone.dom)
      calc (e ≫ u) ≫ e = e ≫ (u ≫ e) := Cat.assoc _ _ _
        _ = e ≫ Cat.id zeroObj := by rw [hue]
        _ = e := Cat.comp_id _
        _ = (Cat.id eq.cone.dom) ≫ e := (Cat.id_comp _).symm
    rcases he_iso with ⟨_, _, h⟩
    calc f = (Cat.id zeroObj) ≫ f := (Cat.id_comp _).symm
      _ = (u ≫ e) ≫ f := by rw [hue]
      _ = u ≫ (e ≫ f) := Cat.assoc _ _ _
      _ = u ≫ (e ≫ g) := by rw [he_eq]
      _ = (u ≫ e) ≫ g := (Cat.assoc _ _ _).symm
      _ = (Cat.id zeroObj) ≫ g := by rw [hue]
      _ = g := Cat.id_comp _
  { zero := zeroObj
    init := mk
    init_uniq := uniq }

/-- **§1.61**: Any morphism to 0 is an isomorphism. -/
theorem any_map_to_zero_is_iso (h : PreLogos 𝒞) {A : 𝒞} (f : A ⟶ (minimal_subobject_of_one_is_coterminator h).zero) :
    IsIso f := by
  let zeroObj := (minimal_subobject_of_one_is_coterminator h).zero
  let one : 𝒞 := h.toHasTerminal.one
  have hzeroMonic_mono : Monic (h.bottom one).arr := (h.bottom one).monic
  letI : HasTerminal 𝒞 := h.toHasTerminal
  letI : HasPullbacks 𝒞 := h.toHasPullbacks
  letI : HasImages 𝒞 := h.toHasImages
  let p : A ⟶ one := h.toHasTerminal.trm A
  -- f·zeroMonic = p (both the unique map A → 1)
  have hp_eq : f ≫ (h.bottom one).arr = p := h.toHasTerminal.uniq _ _
  let pb := h.toHasPullbacks.has p (h.bottom one).arr
  let c : Cone p (h.bottom one).arr := ⟨A, Cat.id A, f, by
    calc Cat.id A ≫ p = p := Cat.id_comp _
      _ = f ≫ (h.bottom one).arr := hp_eq.symm⟩
  let u : A ⟶ pb.cone.pt := pb.lift c
  have hu₁ : u ≫ pb.cone.π₁ = Cat.id A := pb.lift_fst c
  have hu₂ : u ≫ pb.cone.π₂ = f := pb.lift_snd c
  -- π₁ is monic (pullback of monic)
  have hπ₁_mono : Monic pb.cone.π₁ :=
    (InverseImage p (h.bottom one)).monic
  -- π₁ split epi + monic ⇒ iso
  have hπ₁_iso : IsIso pb.cone.π₁ :=
    ⟨u, hπ₁_mono (pb.cone.π₁ ≫ u) (Cat.id pb.cone.pt) (by
      calc (pb.cone.π₁ ≫ u) ≫ pb.cone.π₁ = pb.cone.π₁ ≫ (u ≫ pb.cone.π₁) := Cat.assoc _ _ _
        _ = pb.cone.π₁ ≫ Cat.id A := by rw [hu₁]
        _ = pb.cone.π₁ := Cat.comp_id _
        _ = (Cat.id pb.cone.pt) ≫ pb.cone.π₁ := (Cat.id_comp _).symm), hu₁⟩
  -- π₁ iso ⇒ its section u is iso (u = π₁⁻¹)
  have hu_iso : IsIso u := by
    rcases hπ₁_iso with ⟨inv, hπ₁_inv, hinv_π₁⟩
    -- hπ₁_inv: π₁ ≫ inv = id_pb,  hinv_π₁: inv ≫ π₁ = id_A
    -- hu₁: u ≫ π₁ = id_A.  Since π₁ is monic, u = inv.
    have hu_eq_inv : u = inv := hπ₁_mono u inv (by rw [hu₁, hinv_π₁])
    rw [hu_eq_inv]; exact ⟨pb.cone.π₁, hinv_π₁, hπ₁_inv⟩
  -- invImage_preserves_bottom + bottom_dom_iso: pb.cone.pt ≅ zeroObj
  have hinv : Isomorphic (InverseImage p (h.bottom one)).dom (h.bottom A).dom :=
    h.invImage_preserves_bottom p
  have hbot : Isomorphic (h.bottom A).dom zeroObj := h.bottom_dom_iso A one
  let φ : (InverseImage p (h.bottom one)).dom ⟶ (h.bottom A).dom := hinv.choose
  have hφ_iso : IsIso φ := hinv.choose_spec
  let ψ : (h.bottom A).dom ⟶ zeroObj := hbot.choose
  have hψ_iso : IsIso ψ := hbot.choose_spec
  -- π₂ = φ·ψ (both equal as maps to zeroObj, by monicity of zeroMonic)
  have hπ₂_eq : pb.cone.π₂ = φ ≫ ψ := by
    apply hzeroMonic_mono (pb.cone.π₂) (φ ≫ ψ)
    -- Both sides compose with zeroMonic to the unique map pb.cone.pt → 1
    have h₁ : pb.cone.π₂ ≫ (h.bottom one).arr = pb.cone.π₁ ≫ p := pb.cone.w.symm
    have h₂ : (φ ≫ ψ) ≫ (h.bottom one).arr = pb.cone.π₁ ≫ p :=
      h.toHasTerminal.uniq ((φ ≫ ψ) ≫ (h.bottom one).arr) (pb.cone.π₁ ≫ p)
    calc pb.cone.π₂ ≫ (h.bottom one).arr = pb.cone.π₁ ≫ p := h₁
      _ = (φ ≫ ψ) ≫ (h.bottom one).arr := by rw [h₂]
  have hπ₂_iso : IsIso pb.cone.π₂ := by rw [hπ₂_eq]; exact isIso_comp hφ_iso hψ_iso
  -- f = u·π₂, composition of isos
  rw [← hu₂]; exact isIso_comp hu_iso hπ₂_iso

/-- In a pre-logos, the bottom subobject's domain is a strict coterminator (§1.61). -/
theorem prelogos_bottom_strict (h : PreLogos 𝒞) (B : 𝒞) :
    StrictCoterminator (h.bottom B).dom := by
  intro X f
  obtain ⟨e, ei, hei1, hei2⟩ := h.bottom_dom_iso B h.toHasTerminal.one
  have hfe : IsIso (f ≫ e) := any_map_to_zero_is_iso h (f ≫ e)
  have hf_eq : f = (f ≫ e) ≫ ei := by rw [Cat.assoc, hei1, Cat.comp_id]
  rw [hf_eq]
  exact isIso_comp hfe ⟨e, hei2, hei1⟩

/-- **§1.61**: Degenerate iff 0 ≅ 1. -/
theorem degenerate_iff_zero_iso_one (h : PreLogos 𝒞) :
    (Nonempty (h.toHasTerminal.one ⟶ (minimal_subobject_of_one_is_coterminator h).zero)) ↔
    Isomorphic (minimal_subobject_of_one_is_coterminator h).zero h.toHasTerminal.one := by
  constructor
  · rintro ⟨f⟩; have hf := any_map_to_zero_is_iso h f
    rcases hf with ⟨g, hfg, hgf⟩; exact ⟨g, ⟨f, hgf, hfg⟩⟩
  · rintro ⟨f, hf⟩; rcases hf with ⟨g, hfg, hgf⟩; exact ⟨g⟩

/-! ### §1.611  The three definitions of a pre-logos and their equivalence

  Freyd §1.6 gives three descriptions of a pre-logos over a regular category:

    DEF 1 (full):   each `𝒮ub(A)` is a *lattice* and each `f# : 𝒮ub(B)→𝒮ub(A)` is a
                    *lattice homomorphism*.
    DEF 2 (elem.):  each pair of subobjects has a *union preserved under inverse image*.
    DEF 3 (§1.611): a Cartesian category with images in which *pullbacks transfer finite
                    covers* — a finite jointly-covering family `{Bᵢ↣B}` pulls back, along
                    any `A→B`, to a jointly-covering family `{Aᵢ↣A}`.

  **Defs 1 ≡ 2** are identified already in `S1_60`: in *any* regular category `f#` preserves
  meets/intersections (`invImg_preserves_inter`, S1_45) and the order (`inverseImage_mono`), so
  "lattice homomorphism" reduces to "preserves binary unions and the empty union (bottom)" —
  which is exactly Def 2.  The `PreLogos` class bundles precisely this: `HasSubobjectUnions`
  (the lattice data, Def 1's "each `𝒮ub(A)` is a lattice") plus `invImage_preserves_union` and
  `invImage_preserves_bottom` (Def 2's preservation).  So `PreLogos` *is* Defs 1&2.

  **Def 3 is the genuine extra axiom.**  The binary instance of "pullbacks transfer finite
  covers" is: for `f : A→B` and subobjects `S,T` of `B`, pulling the jointly-covering family
  `{S↣S∪T, T↣S∪T}` back along `f#(S∪T) → S∪T` yields `{f#S, f#T}` *jointly covering* `f#(S∪T)`,
  i.e. `f#(S∪T) ≤ f#S ∪ f#T`.  This forward inclusion is **NOT** a theorem of bare regular
  structure (the reverse always holds, from monotonicity): producing the descent map needs the
  coproduct presenting `S∪T` to be *extensive* (disjoint + universal), equivalently the pre-logos
  to be POSITIVE (§1.623).  Concretely, `case cS cT : S.dom + T.dom → (S∪T).dom` is a cover
  (`union_inclusions_cover` below, proved Sorry-free), and `cover_pullback` keeps its pullback a
  cover; but turning that pulled-back cover into a factorization through `f#S ∪ f#T` requires
  splitting its domain `pullback(S.dom+T.dom, π₂)` along the coproduct — exactly coproduct
  universality.  So Def 3 carries content beyond `RegularCategory`, and we record it as a class.

  We then prove **Def 3 ⟺ Defs 1&2** (`prelogos_of_transfersFiniteUnions` and
  `transfersFiniteUnions_of_prelogos`): given a fixed lattice structure (`HasSubobjectUnions`
  + a `bottom`), the finite-cover-transfer condition holds iff `f#` preserves unions and bottom.
  Both directions are Sorry-free; the three definitions coincide. -/

section PreLogosEquivalence
variable [HasBinaryCoproducts 𝒞]

/-- The two inclusions `S ↣ S∪T`, `T ↣ S∪T` are **jointly covering**: their copairing
    `case cS cT : S.dom + T.dom → (S∪T).dom` is a cover.  This is §1.615 ("the union of two
    subobjects is the image of their copairing") read off the lattice UMP.

    Proof (no extra axiom): let `m : C ↣ (S∪T).dom` be any monic that `case cS cT` factors
    through.  Then `⟨C, m ≫ (S∪T).arr⟩` is a subobject of `B` allowing both `S.arr` and `T.arr`
    (since `cS ≫ U.arr = S.arr`, `cT ≫ U.arr = T.arr` factor through it), so `S∪T ≤ ⟨C, m ≫ U.arr⟩`
    by `union_min`; the factorization `j` satisfies `j ≫ m = id` (cancel the monic `U.arr`), so
    `m` is split epi and monic, hence iso. -/
theorem union_inclusions_cover [HasImages 𝒞] [HasSubobjectUnions 𝒞] {B : 𝒞} (S T : Subobject 𝒞 B)
    (cS : S.dom ⟶ (HasSubobjectUnions.union S T).dom)
    (cT : T.dom ⟶ (HasSubobjectUnions.union S T).dom)
    (hcS_fac : cS ≫ (HasSubobjectUnions.union S T).arr = S.arr)
    (hcT_fac : cT ≫ (HasSubobjectUnions.union S T).arr = T.arr) :
    Cover (HasBinaryCoproducts.case cS cT) := by
  let U := HasSubobjectUnions.union S T
  intro C m g hm hgm
  -- the subobject `M := ⟨C, m ≫ U.arr⟩` of `B`.
  have hmU_mono : Monic (m ≫ U.arr) := by
    intro W u v huv
    exact hm u v (U.monic _ _ (by rw [Cat.assoc, Cat.assoc]; exact huv))
  let M : Subobject 𝒞 B := ⟨C, m ≫ U.arr, hmU_mono⟩
  -- both S and T are ≤ M (S.arr, T.arr factor through `m ≫ U.arr`).
  have hSM : S.le M := ⟨HasBinaryCoproducts.inl ≫ g, by
    show (HasBinaryCoproducts.inl ≫ g) ≫ (m ≫ U.arr) = S.arr
    rw [Cat.assoc, ← Cat.assoc g m U.arr, hgm, ← Cat.assoc, HasBinaryCoproducts.case_inl, hcS_fac]⟩
  have hTM : T.le M := ⟨HasBinaryCoproducts.inr ≫ g, by
    show (HasBinaryCoproducts.inr ≫ g) ≫ (m ≫ U.arr) = T.arr
    rw [Cat.assoc, ← Cat.assoc g m U.arr, hgm, ← Cat.assoc, HasBinaryCoproducts.case_inr, hcT_fac]⟩
  -- so U = S∪T ≤ M; the factorization `j` retracts `m`.
  obtain ⟨j, hj⟩ := HasSubobjectUnions.union_min S T M hSM hTM
  have hjm : j ≫ m = Cat.id U.dom := by
    apply U.monic
    rw [Cat.assoc]; show j ≫ (m ≫ U.arr) = Cat.id U.dom ≫ U.arr
    rw [hj, Cat.id_comp]
  -- `m` split-epi (section `j`) and monic ⇒ iso.
  exact ⟨j, hm (m ≫ j) (Cat.id C) (by rw [Cat.assoc, hjm, Cat.comp_id, Cat.id_comp]), hjm⟩

/-- **§1.611, Def 3**: a regular category with binary coproducts in which *pullbacks transfer
    finite covers*.  Stated, faithful to Freyd, in its binary subobject instance: for every
    `f : A→B` and pair `S,T : 𝒮ub B`, the inverse image of the union is jointly covered by the
    inverse images (`invImage_union_le`), and the empty union (bottom) is preserved
    (`invImage_bottom`).  These are genuinely stronger than regular structure (they fail unless
    the coproducts presenting unions are extensive / the pre-logos is positive, §1.623); the
    reverse inclusion `f#S ∪ f#T ≤ f#(S∪T)` is automatic (`inverseImage_mono`) and so omitted. -/
class TransfersFiniteUnions (𝒞 : Type u) [Cat.{v} 𝒞] extends
    RegularCategory 𝒞, HasBinaryCoproducts 𝒞, HasSubobjectUnions 𝒞 where
  /-- the chosen least subobject (empty union) of each object -/
  bottom : ∀ (A : 𝒞), Subobject 𝒞 A
  bottom_min : ∀ {A : 𝒞} (S : Subobject 𝒞 A), (bottom A).le S
  bottom_dom_iso : ∀ (A B : 𝒞), Isomorphic (bottom A).dom (bottom B).dom
  /-- finite (binary) covers transfer: `f#(S∪T) ≤ f#S ∪ f#T`. -/
  invImage_union_le : ∀ {A B : 𝒞} (f : A ⟶ B) (S T : Subobject 𝒞 B),
    (InverseImage f (HasSubobjectUnions.union S T)).le
      (HasSubobjectUnions.union (InverseImage f S) (InverseImage f T))
  /-- the empty cover transfers: `f#(⊥_B) ≅ ⊥_A`. -/
  invImage_bottom : ∀ {A B : 𝒞} (f : A ⟶ B),
    Isomorphic (InverseImage f (bottom B)).dom (bottom A).dom

/-- **Def 3 ⟹ Defs 1&2** (`§1.611 ⟹ §1.6`): a category in which pullbacks transfer finite
    covers is a pre-logos.  The forward union inclusion is `invImage_union_le`; the reverse is
    automatic from `inverseImage_mono`; bottom preservation is `invImage_bottom`. -/
def prelogos_of_transfersFiniteUnions [hT : TransfersFiniteUnions 𝒞] : PreLogos 𝒞 :=
  { hT.toRegularCategory with
    union := HasSubobjectUnions.union
    union_left := HasSubobjectUnions.union_left
    union_right := HasSubobjectUnions.union_right
    union_min := HasSubobjectUnions.union_min
    bottom := hT.bottom
    bottom_min := hT.bottom_min
    bottom_dom_iso := hT.bottom_dom_iso
    invImage_preserves_union := fun {_A _B} f S T =>
      ⟨hT.invImage_union_le f S T,
       HasSubobjectUnions.union_min _ _ _
         (inverseImage_mono f (HasSubobjectUnions.union_left S T))
         (inverseImage_mono f (HasSubobjectUnions.union_right S T))⟩
    invImage_preserves_bottom := fun {_A _B} f => hT.invImage_bottom f }

/-- **Defs 1&2 ⟹ Def 3** (`§1.6 ⟹ §1.611`): a pre-logos with binary coproducts transfers
    finite covers.  Both fields read straight off the pre-logos axioms — the forward union
    inclusion is `invImage_preserves_union .1`, the bottom is `invImage_preserves_bottom`. -/
def transfersFiniteUnions_of_prelogos [hP : PreLogos 𝒞] : TransfersFiniteUnions 𝒞 :=
  { hP.toRegularCategory, (inferInstance : HasBinaryCoproducts 𝒞),
    hP.toHasSubobjectUnions with
    bottom := PreLogos.bottom
    bottom_min := PreLogos.bottom_min
    bottom_dom_iso := PreLogos.bottom_dom_iso
    invImage_union_le := fun {_A _B} f S T => (PreLogos.invImage_preserves_union f S T).1
    invImage_bottom := fun {_A _B} f => PreLogos.invImage_preserves_bottom f }

/-- **§1.6 / §1.611 — the three definitions coincide.**  Over a regular category with binary
    coproducts and the lattice data, "pullbacks transfer finite covers" (Def 3,
    `TransfersFiniteUnions`) is *equivalent* to "inverse image preserves unions and bottom"
    (Defs 1&2, `PreLogos`).  The two builders `prelogos_of_transfersFiniteUnions` and
    `transfersFiniteUnions_of_prelogos` exhibit the bi-implication.  (The class data — chosen
    unions/bottom — is shared, so this is a genuine logical equivalence of the *axioms*, not
    merely of "some such structure exists".) -/
theorem prelogos_iff_transfersFiniteUnions :
    Nonempty (PreLogos 𝒞 → TransfersFiniteUnions 𝒞) ∧
    Nonempty (TransfersFiniteUnions 𝒞 → PreLogos 𝒞) :=
  ⟨⟨fun hP => letI := hP; transfersFiniteUnions_of_prelogos⟩,
   ⟨fun hT => letI := hT; prelogos_of_transfersFiniteUnions⟩⟩

end PreLogosEquivalence

/-- **§1.612**: For monic f : A ↣ B, f# : Sub(B) → Sub(A) preserves binary
    unions (for every monic f targeted at B) iff Sub(B) is a distributive lattice,
    i.e. for all subobjects A, S, T of B:
        A ∩ (S ∪ T) ≅ (A ∩ S) ∪ (A ∩ T)
    where A ∩ S := InverseImage A.arr S is the pullback of A.arr along S.arr. -/
theorem monic_inverseImage_iff_distributive [HasImages 𝒞] [HasSubobjectUnions 𝒞] [HasPullbacks 𝒞] {B : 𝒞} :
    (∀ {A : 𝒞} (f : A ⟶ B) (_hf : Monic f) (S T : Subobject 𝒞 B),
      Isomorphic (InverseImage f (HasSubobjectUnions.union S T)).dom
                 (HasSubobjectUnions.union (InverseImage f S) (InverseImage f T)).dom) ↔
    (∀ (A S T : Subobject 𝒞 B),
      Isomorphic (InverseImage A.arr (HasSubobjectUnions.union S T)).dom
                 (HasSubobjectUnions.union (InverseImage A.arr S) (InverseImage A.arr T)).dom) := by
  constructor
  · intro h A S T; exact h A.arr A.monic S T
  · intro _h _ _f _hf _S _T
    -- ← direction: a monic f : A ↣ B *is* a subobject ⟨A, f, hf⟩ of B, and
    -- InverseImage f S is by definition InverseImage ⟨A, f, hf⟩.arr S.  So the
    -- distributivity of Sub(B) applied to that very subobject is exactly the claim.
    exact _h ⟨_, _f, _hf⟩ _S _T

/-- **§1.614**: A REPRESENTATION OF PRE-LOGOI is a functor T : 𝒜 → ℬ between pre-logoi
    that preserves Cartesian structure, images, and finite unions (including empty unions).
    Preserving finite unions means: T carries binary unions to binary unions, and the
    bottom (empty union / initial subobject) to the bottom. -/
class PreLogosFunctor {𝒜 ℬ : Type u} [Cat.{v} 𝒜] [Cat.{v} ℬ] [PreLogos 𝒜] [PreLogos ℬ]
    (T : Functor 𝒜 ℬ) (hpm : PreservesMono T) where
  /-- T maps the binary union of S,U in Sub(A) to the union of T(S), T(U) in Sub(T(A)). -/
  preserves_union : ∀ {A : 𝒜} (S U : Subobject 𝒜 A),
    Isomorphic (Subobject.map T hpm (HasSubobjectUnions.union S U)).dom
               (HasSubobjectUnions.union (Subobject.map T hpm S) (Subobject.map T hpm U)).dom
  /-- T maps the bottom (empty union) to the bottom. -/
  preserves_bottom : ∀ (A : 𝒜),
    Isomorphic (Subobject.map T hpm (PreLogos.bottom A)).dom (PreLogos.bottom (T.obj A)).dom

/-- In a thin category (at most one morphism per hom-set), any pair of objects with
    morphisms going both ways are isomorphic: the round-trips are forced to be identities. -/
theorem thin_iso_of_maps (hThin : ∀ {A B : 𝒞} (f g : A ⟶ B), f = g)
    {X Y : 𝒞} (u : X ⟶ Y) (v : Y ⟶ X) : Isomorphic X Y :=
  ⟨u, v, hThin (u ≫ v) (Cat.id X), hThin (v ≫ u) (Cat.id Y)⟩

/-- **§1.613 (converse)**: A thin category (poset) with binary unions and intersections
    that is a distributive lattice is a pre-logos.  The thinness makes all morphism
    conditions automatic; distributivity makes invImage preserve unions. -/
/- Uses `def` not `theorem`: `PreLogos 𝒞` is a class/structure, not a proposition. -/
def distributive_poset_is_prelogos [hReg : RegularCategory 𝒞] [HasSubobjectUnions 𝒞]
    (hThin : ∀ {A B : 𝒞} (f g : A ⟶ B), f = g)
    -- In the thin (poset) case, distributivity is: for any A,S,T subobjects of B,
    -- A ∩ (S ∪ T) ≅ (A ∩ S) ∪ (A ∩ T), where A ∩ S = InverseImage A.arr S.
    -- `hReg` is an instance so its `HasPullbacks` is the canonical one `InverseImage`
    -- resolves against, in both `hDist` and the PreLogos fields below (no instance-coherence gap).
    (hDist : ∀ {B : 𝒞} (A S T : Subobject 𝒞 B),
      Isomorphic (InverseImage A.arr (HasSubobjectUnions.union S T)).dom
                 (HasSubobjectUnions.union (InverseImage A.arr S) (InverseImage A.arr T)).dom)
    (hBottom : ∀ (A : 𝒞), Subobject 𝒞 A)
    (hBottom_min : ∀ {A : 𝒞} (S : Subobject 𝒞 A), (hBottom A).le S)
    (hBottom_dom_iso : ∀ (A B : 𝒞), Isomorphic (hBottom A).dom (hBottom B).dom) :
    PreLogos 𝒞 :=
  { hReg with
    union        := HasSubobjectUnions.union
    union_left   := HasSubobjectUnions.union_left
    union_right  := HasSubobjectUnions.union_right
    union_min    := HasSubobjectUnions.union_min
    bottom                    := hBottom
    bottom_min                := hBottom_min
    bottom_dom_iso            := hBottom_dom_iso
    -- In the thin/poset case every morphism _f : _A → _B is automatically monic (hThin makes
    -- left-cancellation trivial), so ⟨_A, _f, _⟩ is a subobject of _B whose `.arr` is *definitionally*
    -- _f.  Then `hDist` on that subobject IS this goal: `InverseImage ⟨_A,_f,_⟩.arr = InverseImage _f`.
    invImage_preserves_union  := fun {_A _B} _f _S _T => by
      -- hDist gives an Isomorphic of the two domains; in a thin category any map between
      -- subobjects of a fixed object commutes with their monics (hThin), so the iso's two
      -- legs supply BOTH `Subobject.le` directions the strengthened axiom now demands.
      obtain ⟨u, v, _, _⟩ := hDist ⟨_A, _f, fun {_} g h _ => hThin g h⟩ _S _T
      refine And.intro ?_ ?_
      · exact Exists.intro u (hThin _ _)
      · exact Exists.intro v (hThin _ _)
    -- invImage_preserves_bottom: InverseImage f (⊥_B) ≅ ⊥_A.  In the thin case it suffices
    -- to exhibit maps both ways: ⊥_A ≤ InverseImage f ⊥_B (by minimality of ⊥_A), and
    -- InverseImage f ⊥_B → ⊥_B → ⊥_A via the pullback's π₂ and bottom_dom_iso.
    invImage_preserves_bottom := fun {_A _B} _f => by
      letI : HasPullbacks 𝒞 := hReg.toHasPullbacks
      refine thin_iso_of_maps hThin ?fwd (hBottom_min (InverseImage _f (hBottom _B))).choose
      case fwd =>
        exact (HasPullbacks.has _f (hBottom _B).arr).cone.π₂ ≫ (hBottom_dom_iso _B _A).choose }

/-- **§1.615**: In a bicartesian category with images, given x₁ : A₁ → A and
    x₂ : A₂ → A, their union (image of x₁ joined with image of x₂) equals the image of
    the coproduct map [x₁, x₂] = case x₁ x₂ : A₁ + A₂ → A. -/
theorem union_via_coproduct_image [HasImages 𝒞] [HasSubobjectUnions 𝒞] [HasBinaryCoproducts 𝒞]
    {A₁ A₂ A : 𝒞} (x₁ : A₁ ⟶ A) (x₂ : A₂ ⟶ A) :
    IsImage (HasBinaryCoproducts.case x₁ x₂) (HasSubobjectUnions.union (image x₁) (image x₂)) := by
  -- inclusions of the two image-pieces into the union
  obtain ⟨l₁, hl₁⟩ := HasSubobjectUnions.union_left (image x₁) (image x₂)
  obtain ⟨l₂, hl₂⟩ := HasSubobjectUnions.union_right (image x₁) (image x₂)
  refine ⟨⟨HasBinaryCoproducts.case (image.lift x₁ ≫ l₁) (image.lift x₂ ≫ l₂), ?_⟩, ?_⟩
  · -- Allows: the assembled map composed with U.arr equals `case x₁ x₂` (check on inl, inr).
    refine HasBinaryCoproducts.case_uniq x₁ x₂ _ ?_ ?_
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inl, Cat.assoc, hl₁, image.lift_fac]
    · rw [← Cat.assoc, HasBinaryCoproducts.case_inr, Cat.assoc, hl₂, image.lift_fac]
  · -- Minimality: any subobject allowing `case x₁ x₂` allows both x₁ and x₂, hence ≥ both images.
    rintro S ⟨k, hk⟩
    refine HasSubobjectUnions.union_min _ _ _
      (image_min x₁ S ⟨HasBinaryCoproducts.inl ≫ k, ?_⟩)
      (image_min x₂ S ⟨HasBinaryCoproducts.inr ≫ k, ?_⟩)
    · rw [Cat.assoc, hk, HasBinaryCoproducts.case_inl]
    · rw [Cat.assoc, hk, HasBinaryCoproducts.case_inr]

/-! ## §1.616  Relations in a pre-logos form a distributive lattice

  Freyd §1.616 records that in a pre-logos the relations `B&(A,B)` (subobjects of the
  product `A × B`) inherit the distributive-lattice structure of the subobject lattices:
  for relations `R, S, T`,
      `R ∩ (S ∪ T) = (R ∩ S) ∪ (R ∩ T)`  and  `R(S ∪ T) = RS ∪ RT`,
  the second being distributivity of relational composition over union.  The lattice
  (`∩`) half is exactly `monic_inverseImage_iff_distributive` above together with the union
  preservation of inverse images packaged into `PreLogos`.

  The *relational* (composition) half is proved CONSTRUCTIVELY IN CHAPTER 1 — see
  `S1_60.lean` §1.616 (`compose_union_right` and `compose_union_right_le`, giving the
  equality `R ⊚ (S ∪ T) = (R ⊚ S) ∪ (R ⊚ T)`), with reciprocation-over-union in
  `relUnion_le_reciprocal`/`relUnion_reciprocal_le`.  That proof is FAITHFUL to Freyd and
  uses NO allegory axiom: it is coproduct-free, reducing `relSub (R ⊚ X) = ∃_{ω_R}(θ_R# (relSub X))`
  to two pre-logos primitives that each preserve unions — inverse image `θ_R#`
  (`PreLogos.invImage_preserves_union`) and direct image `∃_{ω_R}` (`existsAlong_union_le`).
  This is the Chapter-1 content; the Chapter-2 `DistributiveAllegory.comp_union_distrib`
  axiom is the *abstraction* of it, not its proof.  (Still open: the LEFT form
  `(S ∪ T) ⊚ R = S⊚R ∪ T⊚R`, awaiting reciprocation-of-composition `(R⊚S)° = S°⊚R°`.) -/

/-! ## §1.621 — coproduct-free relational gluing

  The §1.62 Pasting Lemma builds, for any cocone `(Q,f,g)` over the intersection of two
  subobjects, the descent map by forming the relation `R = x°⊚f ∪ y°⊚g`, showing it is a MAP
  (entire + simple), and reading off the morphism.  In `S1_62` that proof carries
  `[HasBinaryCoproducts 𝒞]` because the *relational union* `∪ᵣ` is presented as the image of a
  copairing.  Here we redo the union COPRODUCT-FREE via the subobject-union bridge `relSub`
  (now usable from bare `[PreLogos 𝒞]`, see §1.616 refactor in `S1_60`), so the whole
  construction lives in a bare pre-logos.  This closes §1.621 directly, with no coproduct and no
  appeal to the downstream §1.62/§1.64 layers. -/

/-! ### Relational helpers for the Pasting Lemma (§1.62)

  The book's proof builds, for any cocone `(Q, f, g)`, the relation
  `R = x°⊚f ∪ y°⊚g : U → Q` (with `x, y` the union inclusions), shows it is a
  map (entire + simple), and reads off the descent morphism.  These helpers
  package the pieces that are general enough to live on their own. -/

section RelationalHelpers62
variable [PreLogos 𝒞]

/-- Any MAP relation is the graph of a morphism (mutual containment).  Extract the
    morphism via `tabulated_is_map_iff_left_iso` (left leg is iso) and
    `tabulated_left_iso_eq_graph`. -/
theorem map_to_graph {A B : 𝒞} (R : BinRel 𝒞 A B) (hR : Map R) :
    ∃ q : A ⟶ B, RelLe R (graph q) ∧ RelLe (graph q) R := by
  have heq : R = BinRel.mk R.src R.colA R.colB R.isMonicPair := rfl
  rw [heq] at hR
  have hiso : IsIso R.colA := (tabulated_is_map_iff_left_iso R.colA R.colB R.isMonicPair).mp hR
  obtain ⟨ainv, ha_ainv, hainv_a⟩ := hiso
  refine ⟨ainv ≫ R.colB, ?_, ?_⟩
  · have h := (tabulated_left_iso_eq_graph R.colA R.colB R.isMonicPair ainv ha_ainv hainv_a).1
    rw [← heq] at h; exact h
  · have h := (tabulated_left_iso_eq_graph R.colA R.colB R.isMonicPair ainv ha_ainv hainv_a).2
    rw [← heq] at h; exact h

/-- `pair x x` factors through the relation `x° ⊚ x` — the witness used to push the
    joint cover `j° ⊚ j` down into `x° ⊚ x ∪ y° ⊚ y`. -/
theorem pairxx_factor {C₁ U : 𝒞} (x : C₁ ⟶ U) :
    ∃ α : C₁ ⟶ ((graph x)° ⊚ (graph x)).src,
      α ≫ ((graph x)° ⊚ (graph x)).colA = x ∧ α ≫ ((graph x)° ⊚ (graph x)).colB = x := by
  let pbx := HasPullbacks.has ((graph x)°).colB ((graph x)).colA
  have hcw : (Cat.id C₁) ≫ ((graph x)°).colB = (Cat.id C₁) ≫ (graph x).colA := by
    simp [graph, reciprocal]
  let c : Cone ((graph x)°).colB ((graph x)).colA := ⟨C₁, Cat.id C₁, Cat.id C₁, hcw⟩
  let u := pbx.lift c
  have hu₁ : u ≫ pbx.cone.π₁ = Cat.id C₁ := pbx.lift_fst c
  have hu₂ : u ≫ pbx.cone.π₂ = Cat.id C₁ := pbx.lift_snd c
  let spanx : pbx.cone.pt ⟶ prod U U :=
    pair (pbx.cone.π₁ ≫ ((graph x)°).colA) (pbx.cone.π₂ ≫ (graph x).colB)
  refine ⟨u ≫ image.lift spanx, ?_, ?_⟩
  · show (u ≫ image.lift spanx) ≫ ((image spanx).arr ≫ fst) = x
    rw [Cat.assoc, ← Cat.assoc (image.lift spanx), image.lift_fac]
    show u ≫ spanx ≫ fst = x
    rw [show spanx ≫ fst = pbx.cone.π₁ ≫ ((graph x)°).colA from fst_pair _ _,
        ← Cat.assoc, hu₁, show ((graph x)°).colA = x from rfl, Cat.id_comp]
  · show (u ≫ image.lift spanx) ≫ ((image spanx).arr ≫ snd) = x
    rw [Cat.assoc, ← Cat.assoc (image.lift spanx), image.lift_fac]
    show u ≫ spanx ≫ snd = x
    rw [show spanx ≫ snd = pbx.cone.π₂ ≫ (graph x).colB from snd_pair _ _,
        ← Cat.assoc, hu₂, show (graph x).colB = x from rfl, Cat.id_comp]

/-- `graph x ⊚ (graph x)° ⊆ 1` when `x` is monic — the reciprocal self-composite of a
    monic graph is contained in the identity (`Simple` of `(graph x)°`). -/
theorem graph_comp_recip_le_one_of_mono {A B : 𝒞} (x : A ⟶ B) (hx : Monic x) :
    RelLe (graph x ⊚ (graph x)°) (graph (Cat.id A)) := by
  have hp : MonicPair (x : A ⟶ B) (Cat.id A) := by
    intro W f g _ hid; simpa [Cat.comp_id] using hid
  have hsimp : Simple (BinRel.mk A x (Cat.id A) hp) :=
    (tabulated_is_simple_iff_left_monic x (Cat.id A) hp).mpr hx
  have heq : BinRel.mk A x (Cat.id A) hp = (graph x)° := rfl
  rw [heq] at hsimp
  unfold Simple at hsimp
  rw [reciprocal_invol] at hsimp
  exact hsimp

/-- The intersection relation: `graph x ⊚ (graph y)° ⊆ π₁° ⊚ π₂`, where `(π₁, π₂)` is the
    pullback of `(a1, a2)` and `x, y` factor `a1, a2` through a common `uarr`.  Pointwise:
    two points sit over the same union point exactly when they come from the intersection. -/
theorem inter_lemma {A₁ A₂ U A : 𝒞} (x : A₁ ⟶ U) (y : A₂ ⟶ U) (uarr : U ⟶ A)
    (a1 : A₁ ⟶ A) (a2 : A₂ ⟶ A)
    (hx : x ≫ uarr = a1) (hy : y ≫ uarr = a2) :
    RelLe (graph x ⊚ (graph y)°)
      ((graph (HasPullbacks.has a1 a2).cone.π₁)° ⊚ (graph (HasPullbacks.has a1 a2).cone.π₂)) := by
  let pxy := HasPullbacks.has ((graph x).colB) (((graph y)°).colA)
  have hwxy : pxy.cone.π₁ ≫ x = pxy.cone.π₂ ≫ y := pxy.cone.w
  let pI := HasPullbacks.has a1 a2
  have hconeI : pxy.cone.π₁ ≫ a1 = pxy.cone.π₂ ≫ a2 := by
    rw [← hx, ← hy, ← Cat.assoc, ← Cat.assoc, hwxy]
  let cI : Cone a1 a2 := ⟨pxy.cone.pt, pxy.cone.π₁, pxy.cone.π₂, hconeI⟩
  let m := pI.lift cI
  have hm1 : m ≫ pI.cone.π₁ = pxy.cone.π₁ := pI.lift_fst cI
  have hm2 : m ≫ pI.cone.π₂ = pxy.cone.π₂ := pI.lift_snd cI
  let RHS := (graph pI.cone.π₁)° ⊚ (graph pI.cone.π₂)
  let pR : RHS.src ⟶ prod A₁ A₂ := pair RHS.colA RHS.colB
  have hpR_mono : Monic pR := monic_pair_of_monicPair RHS.colA RHS.colB RHS.isMonicPair
  let pbR := HasPullbacks.has (((graph pI.cone.π₁)°).colB) ((graph pI.cone.π₂).colA)
  have hcwR : (Cat.id pI.cone.pt) ≫ (((graph pI.cone.π₁)°).colB) =
      (Cat.id pI.cone.pt) ≫ ((graph pI.cone.π₂).colA) := by simp [graph, reciprocal]
  let cR : Cone (((graph pI.cone.π₁)°).colB) ((graph pI.cone.π₂).colA) :=
    ⟨pI.cone.pt, Cat.id pI.cone.pt, Cat.id pI.cone.pt, hcwR⟩
  let uR := pbR.lift cR
  have huR1 : uR ≫ pbR.cone.π₁ = Cat.id pI.cone.pt := pbR.lift_fst cR
  have huR2 : uR ≫ pbR.cone.π₂ = Cat.id pI.cone.pt := pbR.lift_snd cR
  let spanR : pbR.cone.pt ⟶ prod A₁ A₂ :=
    pair (pbR.cone.π₁ ≫ (((graph pI.cone.π₁)°).colA)) (pbR.cone.π₂ ≫ ((graph pI.cone.π₂).colB))
  let αR : pI.cone.pt ⟶ RHS.src := uR ≫ image.lift spanR
  have hαR : αR ≫ pR = pair pI.cone.π₁ pI.cone.π₂ := by
    show (uR ≫ image.lift spanR) ≫ pair RHS.colA RHS.colB = pair pI.cone.π₁ pI.cone.π₂
    apply pair_uniq
    · rw [Cat.assoc, fst_pair]
      show (uR ≫ image.lift spanR) ≫ ((image spanR).arr ≫ fst) = pI.cone.π₁
      rw [Cat.assoc, ← Cat.assoc (image.lift spanR), image.lift_fac]
      rw [show spanR ≫ fst = pbR.cone.π₁ ≫ (((graph pI.cone.π₁)°).colA) from fst_pair _ _,
          ← Cat.assoc, huR1, Cat.id_comp, show (((graph pI.cone.π₁)°).colA) = pI.cone.π₁ from rfl]
    · rw [Cat.assoc, snd_pair]
      show (uR ≫ image.lift spanR) ≫ ((image spanR).arr ≫ snd) = pI.cone.π₂
      rw [Cat.assoc, ← Cat.assoc (image.lift spanR), image.lift_fac]
      rw [show spanR ≫ snd = pbR.cone.π₂ ≫ ((graph pI.cone.π₂).colB) from snd_pair _ _,
          ← Cat.assoc, huR2, Cat.id_comp, show ((graph pI.cone.π₂).colB) = pI.cone.π₂ from rfl]
  let spanL : pxy.cone.pt ⟶ prod A₁ A₂ :=
    pair (pxy.cone.π₁ ≫ (graph x).colA) (pxy.cone.π₂ ≫ ((graph y)°).colB)
  have hspanL_eq : spanL = (m ≫ αR) ≫ pR := by
    rw [Cat.assoc, hαR]
    show pair (pxy.cone.π₁ ≫ (graph x).colA) (pxy.cone.π₂ ≫ ((graph y)°).colB)
      = m ≫ pair pI.cone.π₁ pI.cone.π₂
    refine (pair_uniq (pxy.cone.π₁ ≫ (graph x).colA) (pxy.cone.π₂ ≫ ((graph y)°).colB)
      (m ≫ pair pI.cone.π₁ pI.cone.π₂) ?_ ?_).symm
    · rw [Cat.assoc, fst_pair, hm1, show (graph x).colA = Cat.id A₁ from rfl]; exact (Cat.comp_id _).symm
    · rw [Cat.assoc, snd_pair, hm2, show ((graph y)°).colB = Cat.id A₂ from rfl]; exact (Cat.comp_id _).symm
  let RHSsub : Subobject 𝒞 (prod A₁ A₂) := ⟨RHS.src, pR, hpR_mono⟩
  have hallows : Allows RHSsub spanL := ⟨m ≫ αR, hspanL_eq.symm⟩
  obtain ⟨w, hw⟩ := image_min spanL RHSsub hallows
  refine ⟨⟨w, ?_, ?_⟩⟩
  · show w ≫ RHS.colA = (image spanL).arr ≫ fst
    calc w ≫ RHS.colA = (w ≫ pR) ≫ fst := by rw [Cat.assoc, fst_pair]
      _ = (image spanL).arr ≫ fst := by rw [hw]
  · show w ≫ RHS.colB = (image spanL).arr ≫ snd
    calc w ≫ RHS.colB = (w ≫ pR) ≫ snd := by rw [Cat.assoc, snd_pair]
      _ = (image spanL).arr ≫ snd := by rw [hw]

/-- Compatibility consequence: `(graph x ⊚ (graph y)°) ⊚ graph g ⊆ graph f`, using the
    intersection relation and the cocone equation `π₁ ≫ f = π₂ ≫ g`. -/
theorem hxyg_lemma {A₁ A₂ Q I : 𝒞} (f : A₁ ⟶ Q) (g : A₂ ⟶ Q)
    (π₁ : I ⟶ A₁) (π₂ : I ⟶ A₂) (xrel : BinRel 𝒞 A₁ A₂)
    (hinter : RelLe xrel ((graph π₁)° ⊚ graph π₂))
    (hcocone : π₁ ≫ f = π₂ ≫ g) :
    RelLe (xrel ⊚ graph g) (graph f) := by
  -- Book §1.62, in Freyd's notation (a map IS its graph relation, via the `↑`
  -- coercion):  xrel·g ⊆ π₁°π₂·g = π₁°(π₂g) = π₁°(π₁f) = (π₁°π₁)f ⊆ 1·f = f,
  -- using the cocone equation π₁f = π₂g and π₁ monic (π₁°π₁ ⊆ 1).
  let p₁ : BinRel 𝒞 I A₁ := π₁          -- ↑π₁
  let p₂ : BinRel 𝒞 I A₂ := π₂          -- ↑π₂
  let fr : BinRel 𝒞 A₁ Q := f           -- ↑f
  let gr : BinRel 𝒞 A₂ Q := g           -- ↑g
  calc xrel ⊚ gr
      ⊂ (p₁° ⊚ p₂) ⊚ gr := compose_le hinter (rel_le_refl _)
    _ ⊂ p₁° ⊚ (p₂ ⊚ gr) := (compose_assoc_of_regular (p₁°) p₂ gr).1
    _ ⊂ p₁° ⊚ graph (π₂ ≫ g) := compose_le (rel_le_refl _) (comp_graph π₂ g)
    _ ⊂ p₁° ⊚ graph (π₁ ≫ f) := hcocone ▸ rel_le_refl _
    _ ⊂ p₁° ⊚ (p₁ ⊚ fr) := compose_le (rel_le_refl _) (graph_comp π₁ f)
    _ ⊂ (p₁° ⊚ p₁) ⊚ fr := (compose_assoc_of_regular (p₁°) p₁ fr).2
    _ ⊂ graph (Cat.id A₁) ⊚ fr := compose_le (reciprocal_comp_self_le_one π₁) (rel_le_refl _)
    _ ⊂ fr := graph_id_comp fr

/-- Diagonal term: `P° ⊚ P ⊆ 1_Q` where `P = (graph x)° ⊚ graph f` and `x` is monic. -/
theorem diag_le_one {A₁ U Q : 𝒞} (x : A₁ ⟶ U) (f : A₁ ⟶ Q) (hx : Monic x) :
    RelLe (((graph x)° ⊚ graph f)° ⊚ ((graph x)° ⊚ graph f)) (graph (Cat.id Q)) := by
  -- Book §1.62 (maps as relations via `↑`):  P°P = (x°f)°(x°f) ⊆ f°x·x°f
  --   = f°(xx°)f ⊆ f°·1·f = f°f ⊆ 1, the middle step using x monic (xx° ⊆ 1).
  let xr : BinRel 𝒞 A₁ U := x          -- ↑x
  let fr : BinRel 𝒞 A₁ Q := f          -- ↑f
  have hPr : RelLe ((xr° ⊚ fr)°) (fr° ⊚ xr) := by
    have h := reciprocal_comp_le (xr°) fr
    rw [reciprocal_invol] at h; exact h
  let Pr := xr° ⊚ fr
  calc Pr° ⊚ Pr
      ⊂ (fr° ⊚ xr) ⊚ Pr := compose_le hPr (rel_le_refl _)
    _ ⊂ fr° ⊚ (xr ⊚ Pr) := (compose_assoc_of_regular (fr°) xr Pr).1
    _ ⊂ fr° ⊚ ((xr ⊚ xr°) ⊚ fr) :=
          compose_le (rel_le_refl _) (compose_assoc_of_regular xr (xr°) fr).2
    _ ⊂ fr° ⊚ (graph (Cat.id A₁) ⊚ fr) :=
          compose_le (rel_le_refl _) (compose_le (graph_comp_recip_le_one_of_mono x hx) (rel_le_refl _))
    _ ⊂ fr° ⊚ fr := compose_le (rel_le_refl _) (graph_id_comp fr)
    _ ⊂ graph (Cat.id Q) := reciprocal_comp_self_le_one f

/-- Cross term: `P° ⊚ Q ⊆ 1_Q` for `P = (graph x)° ⊚ graph f`, `Q = (graph y)° ⊚ graph g`,
    given the compatibility consequence `hxyg`. -/
theorem cross_le_one {A₁ A₂ U Q : 𝒞} (x : A₁ ⟶ U) (y : A₂ ⟶ U) (f : A₁ ⟶ Q) (g : A₂ ⟶ Q)
    (hxyg : RelLe ((graph x ⊚ (graph y)°) ⊚ graph g) (graph f)) :
    RelLe (((graph x)° ⊚ graph f)° ⊚ ((graph y)° ⊚ graph g)) (graph (Cat.id Q)) := by
  -- Book §1.62 (maps as relations via `↑`):  P°Q = (x°f)°(y°g) ⊆ f°x·y°g
  --   = f°(xy°g) ⊆ f°f ⊆ 1, where the bracket xy°g ⊆ f is exactly `hxyg`.
  let xr : BinRel 𝒞 A₁ U := x          -- ↑x
  let yr : BinRel 𝒞 A₂ U := y          -- ↑y
  let fr : BinRel 𝒞 A₁ Q := f          -- ↑f
  let gr : BinRel 𝒞 A₂ Q := g          -- ↑g
  have hPr : RelLe ((xr° ⊚ fr)°) (fr° ⊚ xr) := by
    have h := reciprocal_comp_le (xr°) fr
    rw [reciprocal_invol] at h; exact h
  let Qr := yr° ⊚ gr
  calc (xr° ⊚ fr)° ⊚ Qr
      ⊂ (fr° ⊚ xr) ⊚ Qr := compose_le hPr (rel_le_refl _)
    _ ⊂ fr° ⊚ (xr ⊚ Qr) := (compose_assoc_of_regular (fr°) xr Qr).1
    _ ⊂ fr° ⊚ ((xr ⊚ yr°) ⊚ gr) :=
          compose_le (rel_le_refl _) (compose_assoc_of_regular xr (yr°) gr).2
    _ ⊂ fr° ⊚ fr := compose_le (rel_le_refl _) hxyg
    _ ⊂ graph (Cat.id Q) := reciprocal_comp_self_le_one f

/-- Entirety ingredient: `x° ⊚ x ⊆ R ⊚ R°` when `P = (graph x)° ⊚ graph f ⊆ R`. -/
theorem xx_le_RRrecip {A₁ U Q : 𝒞} (x : A₁ ⟶ U) (f : A₁ ⟶ Q)
    (R : BinRel 𝒞 U Q) (hPR : RelLe ((graph x)° ⊚ graph f) R) :
    RelLe ((graph x)° ⊚ graph x) (R ⊚ R°) := by
  -- Book §1.62 entire step (maps as relations via `↑`):  x°x ⊆ x°(ff°)x = (x°f)(f°x)
  --   = P·(f°x) ⊆ R·R°, since f is entire (1 ⊆ ff°) and f°x ⊆ (x°f)° = P° ⊆ R°.
  let xr : BinRel 𝒞 A₁ U := x          -- ↑x
  let fr : BinRel 𝒞 A₁ Q := f          -- ↑f
  have hEntf : RelLe (graph (Cat.id A₁)) (fr ⊚ fr°) := (graph_is_map f).1
  have hA : RelLe xr ((fr ⊚ fr°) ⊚ xr) :=
    rel_le_trans (comp_graph_id_left xr) (compose_le hEntf (rel_le_refl _))
  have hPrecip : RelLe (fr° ⊚ xr) (R°) := by
    have hsub : RelLe (fr° ⊚ xr) ((xr° ⊚ fr)°) := by
      have h := (reciprocal_comp (xr°) fr).2
      rw [reciprocal_invol] at h; exact h
    exact rel_le_trans hsub (reciprocal_mono hPR)
  calc xr° ⊚ xr
      ⊂ xr° ⊚ ((fr ⊚ fr°) ⊚ xr) := compose_le (rel_le_refl _) hA
    _ ⊂ xr° ⊚ (fr ⊚ (fr° ⊚ xr)) :=
          compose_le (rel_le_refl _) (compose_assoc_of_regular fr (fr°) xr).1
    _ ⊂ (xr° ⊚ fr) ⊚ (fr° ⊚ xr) :=
          (compose_assoc_of_regular (xr°) fr (fr° ⊚ xr)).2
    _ ⊂ R ⊚ R° := compose_le hPR hPrecip

end RelationalHelpers62

namespace DisjointGluing

variable [PreLogos 𝒞]

-- `subRel`, `relSub_subRel_arr`, and the coproduct-free relational union all now live in S1_60
-- (where `relUnion` was re-based on the subobject-union, so it needs only `[HasSubobjectUnions]`).
-- `relUnionSub` is therefore DEFINITIONALLY `relUnion`; we keep the name as a thin alias plus
-- forwarding lemmas so the §1.621 descent proofs below read unchanged.

/-- COPRODUCT-FREE relational union — now an alias of the unified `relUnion` (S1_60 §1.616). -/
abbrev relUnionSub {A B : 𝒞} (R S : BinRel 𝒞 A B) : BinRel 𝒞 A B := relUnion R S

/-- Universal property: `R ≤ U → S ≤ U → relUnionSub R S ≤ U`. -/
theorem le_relUnionSub {A B : 𝒞} {R S U : BinRel 𝒞 A B}
    (hR : RelLe R U) (hS : RelLe S U) : RelLe (relUnionSub R S) U :=
  le_relUnion hR hS

/-- Simplicity of the descent relation `R = relUnionSub P Q` from the four atomic bounds
    (coproduct-free port of `S1_62.simple_R`). -/
theorem simple_relUnionSub {U Q : 𝒞} (P Qr : BinRel 𝒞 U Q)
    (hPP : RelLe (P° ⊚ P) (graph (Cat.id Q)))
    (hQQ : RelLe (Qr° ⊚ Qr) (graph (Cat.id Q)))
    (hPQ : RelLe (P° ⊚ Qr) (graph (Cat.id Q)))
    (hQP : RelLe (Qr° ⊚ P) (graph (Cat.id Q))) :
    RelLe ((relUnionSub P Qr)° ⊚ (relUnionSub P Qr)) (graph (Cat.id Q)) := by
  have step1 : RelLe ((relUnionSub P Qr)° ⊚ (relUnionSub P Qr))
      (relUnionSub ((relUnionSub P Qr)° ⊚ P) ((relUnionSub P Qr)° ⊚ Qr)) :=
    compose_union_right ((relUnionSub P Qr)°) P Qr
  refine rel_le_trans step1 (le_relUnionSub ?_ ?_)
  · have hP_R : RelLe (P° ⊚ (relUnionSub P Qr)) (graph (Cat.id Q)) :=
      rel_le_trans (compose_union_right (P°) P Qr) (le_relUnionSub hPP hPQ)
    have hrecip : RelLe ((relUnionSub P Qr)° ⊚ P) ((P° ⊚ (relUnionSub P Qr))°) := by
      have h := (reciprocal_comp (P°) (relUnionSub P Qr)).2
      rw [reciprocal_invol] at h; exact h
    refine rel_le_trans hrecip ?_
    have h := reciprocal_mono hP_R
    rwa [show (graph (Cat.id Q))° = graph (Cat.id Q) from rfl] at h
  · have hQ_R : RelLe (Qr° ⊚ (relUnionSub P Qr)) (graph (Cat.id Q)) :=
      rel_le_trans (compose_union_right (Qr°) P Qr) (le_relUnionSub hQP hQQ)
    have hrecip : RelLe ((relUnionSub P Qr)° ⊚ Qr) ((Qr° ⊚ (relUnionSub P Qr))°) := by
      have h := (reciprocal_comp (Qr°) (relUnionSub P Qr)).2
      rw [reciprocal_invol] at h; exact h
    refine rel_le_trans hrecip ?_
    have h := reciprocal_mono hQ_R
    rwa [show (graph (Cat.id Q))° = graph (Cat.id Q) from rfl] at h

/-- For a subobject `S ↣ A`, the diagonal push `⟨S.dom, S.arr ≫ diag A⟩` factors through
    `relSub (S.arr° ⊚ S.arr)`.  Coproduct-free witness via `pairxx_factor`. -/
theorem diagSub_le_relSub_xx {A : 𝒞} (S : Subobject 𝒞 A) :
    (pushMono (diag A) (diag_mono A) S).le (relSub ((graph S.arr)° ⊚ graph S.arr)) := by
  obtain ⟨α, hα1, hα2⟩ := pairxx_factor S.arr
  refine ⟨α, ?_⟩
  show α ≫ pair ((graph S.arr)° ⊚ graph S.arr).colA ((graph S.arr)° ⊚ graph S.arr).colB
      = S.arr ≫ diag A
  rw [show S.arr ≫ diag A = pair S.arr S.arr from (pair_diag_eq S.arr).symm]
  exact pair_uniq _ _ _ (by rw [Cat.assoc, fst_pair, hα1]) (by rw [Cat.assoc, snd_pair, hα2])

/-- **Joint cover** (coproduct-free): when `A₁ ∪ A₂` is entire (`hCover`), the two inclusions
    jointly cover `A`: `1_A ⊆ A₁.arr° ⊚ A₁.arr ∪ᵣ A₂.arr° ⊚ A₂.arr` (with `relUnionSub`).
    Proof: the diagonal `Δ_A` is the push of `union A₁ A₂` (entire, so `≅ A`) along `diag A`;
    `pushMono_union_le` splits it into the two diagonal pieces, each below `relSub (Aᵢ.arr°Aᵢ.arr)`
    via `diagSub_le_relSub_xx`. -/
theorem union_joint_cover_sub {A : 𝒞} (A₁ A₂ : Subobject 𝒞 A)
    (hCover : (HasSubobjectUnions.union A₁ A₂).IsEntire) :
    RelLe (graph (Cat.id A))
      (relUnionSub ((graph A₁.arr)° ⊚ graph A₁.arr) ((graph A₂.arr)° ⊚ graph A₂.arr)) := by
  let R₁ := (graph A₁.arr)° ⊚ graph A₁.arr
  let R₂ := (graph A₂.arr)° ⊚ graph A₂.arr
  let U := HasSubobjectUnions.union A₁ A₂
  apply (relLe_iff_subLe _ _).2
  -- Δ_A ≤ pushMono diag U ≤ union(pushMono diag A₁)(pushMono diag A₂)
  --       ≤ union(relSub R₁)(relSub R₂) ≤ relSub (relUnionSub R₁ R₂)
  -- step 0: relSub (graph (id A)) = ⟨A, diag A⟩ = pushMono diag ⟨A, id A⟩  (the entire subobject)
  obtain ⟨Uinv, hUinv1, hUinv2⟩ := hCover
  have hΔ : (relSub (graph (Cat.id A))).le (pushMono (diag A) (diag_mono A) U) := by
    refine ⟨Uinv, ?_⟩
    show Uinv ≫ (U.arr ≫ diag A) = pair (Cat.id A) (Cat.id A)
    rw [← Cat.assoc, hUinv2, Cat.id_comp]
    exact (pair_uniq _ _ _ (fst_pair _ _) (snd_pair _ _)).symm
  have hsplit : (pushMono (diag A) (diag_mono A) U).le
      (HasSubobjectUnions.union (pushMono (diag A) (diag_mono A) A₁)
        (pushMono (diag A) (diag_mono A) A₂)) := pushMono_union_le (diag A) (diag_mono A) A₁ A₂
  have hpieces : (HasSubobjectUnions.union (pushMono (diag A) (diag_mono A) A₁)
        (pushMono (diag A) (diag_mono A) A₂)).le
      (HasSubobjectUnions.union (relSub R₁) (relSub R₂)) :=
    HasSubobjectUnions.union_min _ _ _
      (Subobject.le_trans (diagSub_le_relSub_xx A₁) (HasSubobjectUnions.union_left _ _))
      (Subobject.le_trans (diagSub_le_relSub_xx A₂) (HasSubobjectUnions.union_right _ _))
  exact Subobject.le_trans hΔ (Subobject.le_trans hsplit
    (Subobject.le_trans hpieces (relSub_union_ge R₁ R₂)))

/-- **Joint epi** (coproduct-free): when `A₁ ∪ A₂` is entire, the inclusions `A₁.arr, A₂.arr`
    are jointly epimorphic on `A`.  Mirrors `union_inclusions_cover`, replacing the generic monic
    by the equalizer of the two competing composites. -/
theorem jointly_epi {A : 𝒞} (A₁ A₂ : Subobject 𝒞 A)
    (hCover : (HasSubobjectUnions.union A₁ A₂).IsEntire)
    {Z : 𝒞} {p q : A ⟶ Z}
    (h1 : A₁.arr ≫ p = A₁.arr ≫ q) (h2 : A₂.arr ≫ p = A₂.arr ≫ q) : p = q := by
  let U := HasSubobjectUnions.union A₁ A₂
  obtain ⟨Uinv, hUinv1, hUinv2⟩ := hCover
  -- it suffices to show U.arr ≫ p = U.arr ≫ q  (cancel the iso U.arr on the left)
  suffices hUp : U.arr ≫ p = U.arr ≫ q by
    calc p = (Uinv ≫ U.arr) ≫ p := by rw [hUinv2, Cat.id_comp]
      _ = Uinv ≫ (U.arr ≫ p) := Cat.assoc _ _ _
      _ = Uinv ≫ (U.arr ≫ q) := by rw [hUp]
      _ = (Uinv ≫ U.arr) ≫ q := (Cat.assoc _ _ _).symm
      _ = q := by rw [hUinv2, Cat.id_comp]
  -- equalizer e of (U.arr ≫ p) and (U.arr ≫ q); show e is split epi hence iso, so equal holds
  letI : HasEqualizers 𝒞 := products_pullbacks_implies_equalizers
  let eq := HasEqualizers.eq U.dom Z (U.arr ≫ p) (U.arr ≫ q)
  let e : eq.cone.dom ⟶ U.dom := eq.cone.map
  have he_eq : e ≫ (U.arr ≫ p) = e ≫ (U.arr ≫ q) := eq.cone.eq
  -- get inclusions l₁, l₂ of A₁, A₂ into U.dom
  obtain ⟨l₁, hl₁⟩ := HasSubobjectUnions.union_left A₁ A₂
  obtain ⟨l₂, hl₂⟩ := HasSubobjectUnions.union_right A₁ A₂
  -- e is monic (equalizer leg), so M := ⟨eq.dom, e ≫ U.arr⟩ is a subobject of A
  have he_mono : Monic e := by
    intro W u v huv
    let ec : EqualizerCone (U.arr ≫ p) (U.arr ≫ q) := ⟨W, u ≫ e, by
      calc (u ≫ e) ≫ (U.arr ≫ p) = u ≫ (e ≫ (U.arr ≫ p)) := Cat.assoc _ _ _
        _ = u ≫ (e ≫ (U.arr ≫ q)) := by rw [he_eq]
        _ = (u ≫ e) ≫ (U.arr ≫ q) := (Cat.assoc _ _ _).symm⟩
    rw [eq.uniq ec u rfl, eq.uniq ec v (by dsimp only [ec]; rw [huv])]
  have heU_mono : Monic (e ≫ U.arr) := by
    intro W u v huv
    apply he_mono u v
    apply U.monic (u ≫ e) (v ≫ e)
    rw [Cat.assoc, Cat.assoc]; exact huv
  let M : Subobject 𝒞 A := ⟨eq.cone.dom, e ≫ U.arr, heU_mono⟩
  -- A₁ ≤ M and A₂ ≤ M:  Aᵢ.arr factors through e ≫ U.arr.  Need lᵢ to land in eq.dom.
  -- lᵢ ≫ U.arr = Aᵢ.arr, and lᵢ equalizes U.arr≫p, U.arr≫q (since Aᵢ.arr ≫ p = Aᵢ.arr ≫ q).
  have hl₁eq : l₁ ≫ (U.arr ≫ p) = l₁ ≫ (U.arr ≫ q) := by
    rw [← Cat.assoc, ← Cat.assoc, hl₁]; exact h1
  have hl₂eq : l₂ ≫ (U.arr ≫ p) = l₂ ≫ (U.arr ≫ q) := by
    rw [← Cat.assoc, ← Cat.assoc, hl₂]; exact h2
  let c₁ : EqualizerCone (U.arr ≫ p) (U.arr ≫ q) := ⟨A₁.dom, l₁, hl₁eq⟩
  let c₂ : EqualizerCone (U.arr ≫ p) (U.arr ≫ q) := ⟨A₂.dom, l₂, hl₂eq⟩
  have hj₁ : eq.lift c₁ ≫ e = l₁ := eq.fac c₁
  have hj₂ : eq.lift c₂ ≫ e = l₂ := eq.fac c₂
  have hA₁M : A₁.le M := ⟨eq.lift c₁, by
    show eq.lift c₁ ≫ (e ≫ U.arr) = A₁.arr
    rw [← Cat.assoc, hj₁, hl₁]⟩
  have hA₂M : A₂.le M := ⟨eq.lift c₂, by
    show eq.lift c₂ ≫ (e ≫ U.arr) = A₂.arr
    rw [← Cat.assoc, hj₂, hl₂]⟩
  -- so U ≤ M; the factorization j retracts e, making e a split epi (and monic) ⇒ iso.
  obtain ⟨j, hj⟩ := HasSubobjectUnions.union_min A₁ A₂ M hA₁M hA₂M
  have hje : j ≫ e = Cat.id U.dom := by
    apply U.monic
    rw [Cat.assoc]; show j ≫ (e ≫ U.arr) = Cat.id U.dom ≫ U.arr
    rw [hj, Cat.id_comp]
  -- finally:  U.arr ≫ p = (j ≫ e) ≫ U.arr ≫ p = j ≫ (e ≫ (U.arr ≫ p)) = … = U.arr ≫ q
  calc U.arr ≫ p = (Cat.id U.dom ≫ U.arr) ≫ p := by rw [Cat.id_comp]
    _ = ((j ≫ e) ≫ U.arr) ≫ p := by rw [hje]
    _ = j ≫ (e ≫ (U.arr ≫ p)) := by rw [Cat.assoc, Cat.assoc]
    _ = j ≫ (e ≫ (U.arr ≫ q)) := by rw [he_eq]
    _ = ((j ≫ e) ≫ U.arr) ≫ q := by rw [Cat.assoc, Cat.assoc]
    _ = (Cat.id U.dom ≫ U.arr) ≫ q := by rw [hje]
    _ = U.arr ≫ q := by rw [Cat.id_comp]

end DisjointGluing

open DisjointGluing

/-- **§1.621**: If A₁ ∩ A₂ = 0 and A₁ ∪ A₂ = A (as subobjects of A in a pre-logos)
    then A is the binary coproduct of A₁.dom and A₂.dom via the inclusions A₁.arr, A₂.arr.
    Here A₁ ∩ A₂ is the subobject represented by the pullback of A₁.arr along A₂.arr;
    A₁ ∩ A₂ = 0 means its domain is isomorphic to (PreLogos.bottom A).dom. -/
theorem disjoint_cover_is_coproduct [PreLogos 𝒞]
    {A : 𝒞} (A₁ A₂ : Subobject 𝒞 A)
    -- A₁ ∩ A₂ = 0: the pullback I of A₁.arr and A₂.arr has I.dom ≅ (⊥ A).dom
    (hDisjoint : Isomorphic (HasPullbacks.has A₁.arr A₂.arr).cone.pt (PreLogos.bottom A).dom)
    -- A₁ ∪ A₂ = A: the union is entire
    (hCover    : (HasSubobjectUnions.union A₁ A₂).IsEntire) :
    ∀ {X : 𝒞} (f₁ : A₁.dom ⟶ X) (f₂ : A₂.dom ⟶ X),
      ∃ h : A ⟶ X, A₁.arr ≫ h = f₁ ∧ A₂.arr ≫ h = f₂ ∧
        ∀ h' : A ⟶ X, A₁.arr ≫ h' = f₁ → A₂.arr ≫ h' = f₂ → h' = h := by
  -- §1.621 is the DISJOINT specialization of the §1.62 pasting lemma, done here COPRODUCT-FREE
  -- in a bare pre-logos via the `relUnionSub` bridge.  The descent relation is R = x°f₁ ∪ y°f₂
  -- (`relUnionSub`); we show R is a MAP (entire + simple), read off `h`, and use joint-epi for
  -- uniqueness.  hDisjoint is used ONLY to supply the cocone equation `π₁ ≫ f₁ = π₂ ≫ f₂`,
  -- which holds because the intersection apex is the coterminator (§1.61).
  classical
  intro X f₁ f₂
  let x := A₁.arr
  let y := A₂.arr
  let pb := HasPullbacks.has A₁.arr A₂.arr
  -- COCONE COMPATIBILITY: any two maps out of the (coterminator-like) intersection agree.
  have hmaps : ∀ (u v : pb.cone.pt ⟶ X), u = v := by
    let ct := minimal_subobject_of_one_is_coterminator (inferInstance : PreLogos 𝒞)
    -- pb.cone.pt ≅ (bottom A).dom ≅ ct.zero; assemble g : pb.cone.pt → ct.zero with inverse ginv.
    obtain ⟨e, einv, he1, _⟩ := hDisjoint
    obtain ⟨φ, φinv, hφ1, _⟩ :=
      PreLogos.bottom_dom_iso A (inferInstance : PreLogos 𝒞).toHasTerminal.one
    let g : pb.cone.pt ⟶ ct.zero := e ≫ φ
    let ginv : ct.zero ⟶ pb.cone.pt := φinv ≫ einv
    have hg_ginv : g ≫ ginv = Cat.id pb.cone.pt := by
      show (e ≫ φ) ≫ (φinv ≫ einv) = Cat.id pb.cone.pt
      rw [Cat.assoc e φ (φinv ≫ einv), ← Cat.assoc φ φinv einv, hφ1, Cat.id_comp, he1]
    intro u v
    calc u = (g ≫ ginv) ≫ u := by rw [hg_ginv, Cat.id_comp]
      _ = g ≫ (ginv ≫ u) := Cat.assoc _ _ _
      _ = g ≫ (ginv ≫ v) := by rw [ct.init_uniq (ginv ≫ u) (ginv ≫ v)]
      _ = (g ≫ ginv) ≫ v := (Cat.assoc _ _ _).symm
      _ = v := by rw [hg_ginv, Cat.id_comp]
  -- The cocone equation needed for `hxyg_lemma`.
  have hw : pb.cone.π₁ ≫ f₁ = pb.cone.π₂ ≫ f₂ := hmaps _ _
  -- Build the descent relation R = x°⊚f₁ ∪ y°⊚f₂ (coproduct-free union).
  let P : BinRel 𝒞 A X := (graph x)° ⊚ graph f₁
  let Q : BinRel 𝒞 A X := (graph y)° ⊚ graph f₂
  let R : BinRel 𝒞 A X := relUnionSub P Q
  have hxmono : Monic x := A₁.monic
  have hymono : Monic y := A₂.monic
  -- intersection relation + compatibility consequence
  have hinter : RelLe (graph x ⊚ (graph y)°)
      ((graph pb.cone.π₁)° ⊚ graph pb.cone.π₂) :=
    inter_lemma x y (Cat.id A) A₁.arr A₂.arr (Cat.comp_id _) (Cat.comp_id _)
  have hxyg : RelLe ((graph x ⊚ (graph y)°) ⊚ graph f₂) (graph f₁) :=
    hxyg_lemma f₁ f₂ pb.cone.π₁ pb.cone.π₂ (graph x ⊚ (graph y)°) hinter hw
  -- four atomic bounds for simplicity
  have hPP : RelLe (P° ⊚ P) (graph (Cat.id X)) := diag_le_one x f₁ hxmono
  have hQQ : RelLe (Q° ⊚ Q) (graph (Cat.id X)) := diag_le_one y f₂ hymono
  have hPQ : RelLe (P° ⊚ Q) (graph (Cat.id X)) := cross_le_one x y f₁ f₂ hxyg
  have hQP : RelLe (Q° ⊚ P) (graph (Cat.id X)) := by
    have hsub : RelLe (Q° ⊚ P) ((P° ⊚ Q)°) := by
      have h := (reciprocal_comp (P°) Q).2
      rw [reciprocal_invol] at h; exact h
    refine rel_le_trans hsub ?_
    have h := reciprocal_mono hPQ
    rwa [show (graph (Cat.id X))° = graph (Cat.id X) from rfl] at h
  have hSimple : Simple R := simple_relUnionSub P Q hPP hQQ hPQ hQP
  -- entirety from the joint cover (hCover) via xx_le_RRrecip
  have hEntire : Entire R := by
    have hjoint : RelLe (graph (Cat.id A))
        (relUnionSub ((graph x)° ⊚ graph x) ((graph y)° ⊚ graph y)) :=
      union_joint_cover_sub A₁ A₂ hCover
    refine rel_le_trans hjoint (le_relUnionSub ?_ ?_)
    · exact xx_le_RRrecip x f₁ R (relUnion_le_left P Q)
    · exact xx_le_RRrecip y f₂ R (relUnion_le_right P Q)
  -- extract the descent morphism h
  obtain ⟨h, hRh, _⟩ := map_to_graph R ⟨hEntire, hSimple⟩
  -- factorizations  x ≫ h = f₁  and  y ≫ h = f₂  (the hfac_gen pattern, coproduct-free)
  have hfac_gen : ∀ {C : 𝒞} (z : C ⟶ A) (k : C ⟶ X),
      RelLe ((graph z)° ⊚ graph k) R → z ≫ h = k := by
    intro C z k hpiece
    have step1 : RelLe (graph k) ((graph (Cat.id C)) ⊚ graph k) := comp_graph_id_left (graph k)
    have step2 : RelLe ((graph (Cat.id C)) ⊚ graph k) ((graph z ⊚ (graph z)°) ⊚ graph k) :=
      compose_le (graph_is_map z).1 (rel_le_refl _)
    have step3 : RelLe ((graph z ⊚ (graph z)°) ⊚ graph k) (graph z ⊚ ((graph z)° ⊚ graph k)) :=
      (compose_assoc_of_regular (graph z) ((graph z)°) (graph k)).1
    have step4 : RelLe (graph z ⊚ ((graph z)° ⊚ graph k)) (graph z ⊚ graph h) :=
      compose_le (rel_le_refl _) (rel_le_trans hpiece hRh)
    have step5 : RelLe (graph z ⊚ graph h) (graph (z ≫ h)) := comp_graph z h
    exact (graph_faithful (rel_le_trans step1 (rel_le_trans step2
      (rel_le_trans step3 (rel_le_trans step4 step5))))).symm
  have hfac1 : x ≫ h = f₁ := hfac_gen x f₁ (relUnion_le_left P Q)
  have hfac2 : y ≫ h = f₂ := hfac_gen y f₂ (relUnion_le_right P Q)
  refine ⟨h, hfac1, hfac2, ?_⟩
  -- uniqueness via joint epi (hCover)
  intro h' hh'1 hh'2
  exact jointly_epi A₁ A₂ hCover (by rw [hh'1, hfac1]) (by rw [hh'2, hfac2])

end Freyd
