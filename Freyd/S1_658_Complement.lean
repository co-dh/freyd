/-
  Freyd & Scedrov, *Categories and Allegories* §1.658  Complement infrastructure.

  This file builds the reusable §1.658 ("decidable object") infrastructure consumed
  by the boolean decidability theorems of `S1_64`, all stated over the CORRECT
  inter-based complement predicate `IsComplementedSub` (`S1_62`):

      A₁ ⊆ A is complemented  ⇔  ∃ A₂, A₁ ∩ A₂ ≤ ⊥  and  ⊤ ≤ A₁ ∪ A₂.

  Pieces:
  1. `invImage_complementedSub` — pullback stability: `f# K` is complemented when `K` is.
  2. `Subobject.Dom` — domain of a relation `R ⊆ A×B`, with monotonicity + graph lemma.
  3. `diagonal_classifies` — every subobject `S ⊆ B` is the inverse image of the diagonal
     `Δ : A ↣ A×A` along a classifying map, transferring decidability of `Δ` to `S`.
-/

module

public import Freyd.S1_62


open Freyd

universe v u

variable {𝒞 : Type u} [Cat.{v} 𝒞]

namespace Freyd

-- `PreLogos` already provides `HasTerminal`, `HasBinaryProducts`, `HasPullbacks`,
-- `HasImages` (via `RegularCategory`).  Declaring those separately would create an
-- instance diamond with the `PreLogos`-derived ones, so we take only `[PreLogos 𝒞]`.
variable [PreLogos 𝒞]

/-! ## §1.61 The bottom subobject is least *as a subobject* (not just up to domain iso)

  `PreLogos.bottom` records only that `f#(⊥)` has domain *isomorphic* to `⊥`, which is
  weaker than `f#(⊥) ≤ ⊥` as subobjects.  But §1.61 (`minimal_subobject_of_one_is_coterminator`)
  shows `⊥.dom` is the coterminator `0` — an *initial* object — so any subobject whose domain
  is isomorphic to `⊥.dom` has an **initial** domain, and maps out of an initial object are
  unique.  That upgrades the bare domain-iso into the genuine subobject inequality. -/

/-- A subobject of `B` whose domain is isomorphic to `(⊥ B).dom` is `≤ ⊥ B`.
    `⊥ B`'s domain is the coterminator `0` (§1.61), so `Z.dom ≅ 0` is initial; the map
    `Z.dom → (⊥ B).dom` it provides is the unique map out of an initial object, and
    composing with `(⊥ B).arr` necessarily lands back on `Z.arr` (also a map out of the
    same initial domain), giving the factorization `Z ≤ ⊥ B`. -/
public theorem le_bottom_of_dom_iso {B : 𝒞} (Z : Subobject 𝒞 B)
    (hiso : Isomorphic Z.dom (PreLogos.bottom B).dom) : Z.le (PreLogos.bottom B) := by
  letI hCot := minimal_subobject_of_one_is_coterminator (𝒞 := 𝒞) ‹PreLogos 𝒞›
  -- (⊥ B).dom ≅ zeroObj (initial); so Z.dom ≅ zeroObj.
  have hbot0 : Isomorphic (PreLogos.bottom B).dom hCot.zero :=
    PreLogos.bottom_dom_iso B (HasTerminal.one)
  have hZ0 : Isomorphic Z.dom hCot.zero := isomorphic_trans hiso hbot0
  -- Z.dom is initial: pick iso Z.dom ≅ zeroObj, transport uniqueness of maps out of zeroObj.
  obtain ⟨φ, φinv, hφφinv, hφinvφ⟩ := hZ0
  have hZinit_uniq : ∀ {X : 𝒞} (f g : Z.dom ⟶ X), f = g := by
    intro X f g
    have : φinv ≫ f = φinv ≫ g := hCot.init_uniq _ _
    calc f = (φ ≫ φinv) ≫ f := by rw [hφφinv, Cat.id_comp]
      _ = φ ≫ (φinv ≫ f) := Cat.assoc _ _ _
      _ = φ ≫ (φinv ≫ g) := by rw [this]
      _ = (φ ≫ φinv) ≫ g := (Cat.assoc _ _ _).symm
      _ = g := by rw [hφφinv, Cat.id_comp]
  -- the map Z.dom → (⊥ B).dom from the iso `hiso`.
  obtain ⟨g, _⟩ := hiso
  refine ⟨g, ?_⟩
  -- g ≫ (⊥ B).arr and Z.arr are both maps Z.dom → B out of the initial Z.dom, hence equal.
  exact hZinit_uniq (g ≫ (PreLogos.bottom B).arr) Z.arr

/-! ## §1.658 Subobject-meet lattice lemmas for `Subobject.inter`

  `Subobject.inter` (S1_62:75) is the pullback `π₁ ≫ S.arr`.  It is the greatest
  lower bound of `S` and `T` in `Sub(B)`.  The meet laws `Subobject.inter_le_left`,
  `Subobject.inter_le_right`, `Subobject.le_inter` are proved next to `Subobject.inter`
  in S1_62 (needed there for the §1.635 ultra-filter algebra); reused here. -/

/-! ## §1.452 Inverse image preserves intersection

  `f#` is a meet-homomorphism: `f#(S ∩ T) = f#S ∩ f#T`.  This is `S1_45`'s
  `invImg_preserves_inter` specialized to the canonical `HasPullbacks` pullbacks, so
  the `invImg`/`Sub.inter` of that lemma coincide *definitionally* with this file's
  `InverseImage`/`Subobject.inter` (same chosen pullback cones). -/

/-- Reverse inclusion of inverse-image / intersection interchange:
    `f#S ∩ f#T ≤ f#(S ∩ T)`.  This is the half used for the disjointness clause of a
    complement (the forward half follows from monotonicity, but only this half is needed). -/
public theorem inter_invImage_le {A B : 𝒞} (f : A ⟶ B) (S T : Subobject 𝒞 B) :
    (Subobject.inter (InverseImage f S) (InverseImage f T)).le
      (InverseImage f (Subobject.inter S T)) :=
  (invImg_preserves_inter f S T
    (HasPullbacks.has S.arr T.arr)
    (HasPullbacks.has f (Subobject.inter S T).arr)
    (HasPullbacks.has f S.arr)
    (HasPullbacks.has f T.arr)
    (HasPullbacks.has (InverseImage f S).arr (InverseImage f T).arr)).2

/-! ## §1.658 (1) Inverse images of complemented subobjects are complemented

  If `K ⊆ C` is complemented (`IsComplementedSub`) with complement `K₂`, then for any
  `f : B → C` the inverse image `f# K ⊆ B` is complemented, with complement `f# K₂`.

  * **disjointness** `f#K ∩ f#K₂ ≤ ⊥ B`:
      `f#K ∩ f#K₂ ≤ f#(K ∩ K₂)` (`inter_invImage_le`)
      `≤ f#(⊥ C)` (`inverseImage_mono`, since `K ∩ K₂ ≤ ⊥ C`)
      `≤ ⊥ B` (`le_bottom_of_dom_iso` + `invImage_preserves_bottom`);
  * **cover** `⊤ B ≤ f#K ∪ f#K₂`:
      `⊤ B ≤ f#(⊤ C)` (`entire_le_inverseImage_entire`)
      `≤ f#(K ∪ K₂)` (`inverseImage_mono`, since `⊤ C ≤ K ∪ K₂`)
      `≤ f#K ∪ f#K₂` (`PreLogos.invImage_preserves_union`, forward half). -/
public theorem invImage_complementedSub {B C : 𝒞} (f : B ⟶ C) {K : Subobject 𝒞 C}
    (hK : IsComplementedSub K) : IsComplementedSub (InverseImage f K) := by
  obtain ⟨K₂, hdisj, hcover⟩ := hK
  refine ⟨InverseImage f K₂, ?_, ?_⟩
  · -- disjointness
    have h1 : (Subobject.inter (InverseImage f K) (InverseImage f K₂)).le
        (InverseImage f (Subobject.inter K K₂)) := inter_invImage_le f K K₂
    have h2 : (InverseImage f (Subobject.inter K K₂)).le
        (InverseImage f (PreLogos.bottom C)) := inverseImage_mono f hdisj
    have h3 : (InverseImage f (PreLogos.bottom C)).le (PreLogos.bottom B) :=
      le_bottom_of_dom_iso _ (PreLogos.invImage_preserves_bottom f)
    exact Subobject.le_trans h1 (Subobject.le_trans h2 h3)
  · -- cover
    have h1 : (Subobject.entire B).le (InverseImage f (Subobject.entire C)) :=
      entire_le_inverseImage_entire f
    have h2 : (InverseImage f (Subobject.entire C)).le
        (InverseImage f (HasSubobjectUnions.union K K₂)) := inverseImage_mono f hcover
    have h3 : (InverseImage f (HasSubobjectUnions.union K K₂)).le
        (HasSubobjectUnions.union (InverseImage f K) (InverseImage f K₂)) :=
      (PreLogos.invImage_preserves_union f K K₂).1
    exact Subobject.le_trans h1 (Subobject.le_trans h2 h3)

/-! ## §1.658 (2) Domain of a relation

  For a relation `R ⊆ A×B` (a subobject of the product), its DOMAIN `Dom R ⊆ A` is the
  image of the composite `R.arr ≫ fst : R.dom → A` — the projection of `R` onto its first
  coordinate.  Used by `S1_6510` to carve out `Dom(S ∘ inl°)` when decomposing a map into a
  coproduct, and by the boolean-transfer construction. -/

/-- The domain of a relation `R ⊆ A×B`: the image of `R.arr ≫ fst`, a subobject of `A`. -/
def Subobject.Dom {A B : 𝒞} (R : Subobject 𝒞 (prod A B)) : Subobject 𝒞 A :=
  image (R.arr ≫ fst)

/-- `Dom` is monotone: `R ≤ R'` in `Sub(A×B)` gives `Dom R ≤ Dom R'` in `Sub(A)`.
    A factorization `h ≫ R'.arr = R.arr` makes `R.arr ≫ fst` factor through the image of
    `R'.arr ≫ fst`, so image-minimality gives the inclusion. -/
theorem Subobject.Dom_mono {A B : 𝒞} {R R' : Subobject 𝒞 (prod A B)} (hle : R.le R') :
    (Subobject.Dom R).le (Subobject.Dom R') := by
  obtain ⟨h, hh⟩ := hle
  -- R.arr ≫ fst = h ≫ (R'.arr ≫ fst), so image(R'.arr ≫ fst) allows R.arr ≫ fst.
  apply image_min (R.arr ≫ fst) (Subobject.Dom R')
  refine ⟨h ≫ image.lift (R'.arr ≫ fst), ?_⟩
  calc (h ≫ image.lift (R'.arr ≫ fst)) ≫ (Subobject.Dom R').arr
      = h ≫ (image.lift (R'.arr ≫ fst) ≫ (image (R'.arr ≫ fst)).arr) := by
        simp [Subobject.Dom, Cat.assoc]
    _ = h ≫ (R'.arr ≫ fst) := by rw [image.lift_fac]
    _ = (h ≫ R'.arr) ≫ fst := (Cat.assoc _ _ _).symm
    _ = R.arr ≫ fst := by rw [hh]

/-- The graph of `g : A → B`, as a subobject `⟨id_A, g⟩ : A ↣ A×B`.  Monic since `fst` is a
    retraction of `pair (id) g`. -/
def graphSub {A B : 𝒞} (g : A ⟶ B) : Subobject 𝒞 (prod A B) :=
  ⟨A, pair (Cat.id A) g, mono_of_retraction _ fst (fst_pair _ _)⟩

/-- **`Dom` of a graph is the whole domain**: `Dom (graphSub g) = ⊤ A`.
    `(graphSub g).arr ≫ fst = pair (id) g ≫ fst = id_A`, and the image of `id_A` is entire
    because `id_A` is a cover (it is iso). -/
theorem Subobject.Dom_graphSub {A B : 𝒞} (g : A ⟶ B) :
    (Subobject.Dom (graphSub g)).le (Subobject.entire A) ∧
    (Subobject.entire A).le (Subobject.Dom (graphSub g)) := by
  -- The defining map of Dom: c = (graphSub g).arr ≫ fst, which equals id_A.
  have harr : (graphSub g).arr ≫ fst = Cat.id A := by
    show pair (Cat.id A) g ≫ fst = Cat.id A; exact fst_pair _ _
  -- c is a cover (it equals id_A, which is a cover); so its image is entire.
  have hcover : Cover ((graphSub g).arr ≫ fst) := by
    rw [harr]
    intro C m gg hm hfac
    -- gg ≫ m = id_A makes m a split epi; with m monic, m is iso.
    refine ⟨gg, ?_, hfac⟩
    exact hm _ _ (by rw [Cat.assoc, hfac, Cat.id_comp, Cat.comp_id])
  -- Dom (graphSub g) = image ((graphSub g).arr ≫ fst), whose arr is iso.
  have hentire : Subobject.IsEntire (Subobject.Dom (graphSub g)) :=
    (cover_iff_image_entire ((graphSub g).arr ≫ fst)).1 hcover
  obtain ⟨inv, hinv1, hinv2⟩ := hentire
  -- hinv2 : inv ≫ (Dom (graphSub g)).arr = id_A.
  refine ⟨⟨(Subobject.Dom (graphSub g)).arr, Cat.comp_id _⟩, ⟨inv, hinv2⟩⟩

/-! ## §1.658 (3) Diagonal classifies — decidability transfers to inverse images

  The diagonal of `A`, viewed as the subobject `Δ A = ⟨diag A⟩ : A ↣ A×A`.  `A` is
  DECIDABLE when `Δ A` is complemented.  By pullback stability (`invImage_complementedSub`),
  the inverse image of `Δ A` along *any* classifying map `c : B → A×A` is then complemented.
  This is the engine of the (⇐) direction of `S1_64`'s `preTopos_boolean_iff_all_decidable`:
  every subobject `S ⊆ B` exhibited as such an inverse image `c# (Δ A)` is complemented. -/

/-- The diagonal subobject `Δ A = ⟨diag A⟩ : A ↣ A×A`. -/
@[expose] public def diagSub (A : 𝒞) : Subobject 𝒞 (prod A A) :=
  ⟨A, diag A, diag_mono A⟩

/-- `A` is decidable (inter-based form): its diagonal subobject is `IsComplementedSub`. -/
@[expose] public def DecidableObjectSub (A : 𝒞) : Prop := IsComplementedSub (diagSub A)

/-- **§1.658 diagonal-classifies**: if `A` is decidable and `c : B → A×A` is a classifying
    map, then the inverse image `c# (Δ A) ⊆ B` is complemented.  This transfers decidability
    of the diagonal to any subobject realized as an inverse image of it. -/
public theorem invImage_diagSub_complementedSub {A B : 𝒞} (hA : DecidableObjectSub A)
    (c : B ⟶ prod A A) : IsComplementedSub (InverseImage c (diagSub A)) :=
  invImage_complementedSub c hA

/-- **§1.658 diagonal-classifies (transfer form)**: any subobject `S ⊆ B` that *coincides*
    (mutual `≤`) with the inverse image of the decidable diagonal along some classifying map
    `c : B → A×A` is itself complemented.  This is the exact shape `S1_64`'s boolean (⇐)
    consumes: produce `c` with `S = c# (Δ A)`, then read off complementedness of `S`. -/
public theorem diagonal_classifies {A B : 𝒞} (hA : DecidableObjectSub A)
    {S : Subobject 𝒞 B} (c : B ⟶ prod A A)
    (hS₁ : S.le (InverseImage c (diagSub A)))
    (hS₂ : (InverseImage c (diagSub A)).le S) :
    IsComplementedSub S :=
  complementedSub_congr hS₁ hS₂ (invImage_diagSub_complementedSub hA c)

/-- The product map `φ × φ : X×X → Y×Y` for `φ : X → Y`, as `pair (fst≫φ) (snd≫φ)`. -/
@[expose] public def prodSelfMap {X Y : 𝒞} (φ : X ⟶ Y) : prod X X ⟶ prod Y Y := pair (fst ≫ φ) (snd ≫ φ)

/-- `diag X ≫ (φ × φ) = φ ≫ diag Y`: the diagonal is natural in `φ`. -/
public theorem diag_prodSelfMap {X Y : 𝒞} (φ : X ⟶ Y) :
    diag X ≫ prodSelfMap φ = φ ≫ diag Y := by
  apply fst_snd_jointly_monic
  · rw [Cat.assoc, show prodSelfMap φ ≫ fst = fst ≫ φ from fst_pair _ _, ← Cat.assoc,
        show diag X ≫ fst = Cat.id X from fst_pair _ _,
        Cat.id_comp, Cat.assoc, show diag Y ≫ fst = Cat.id Y from fst_pair _ _, Cat.comp_id]
  · rw [Cat.assoc, show prodSelfMap φ ≫ snd = snd ≫ φ from snd_pair _ _, ← Cat.assoc,
        show diag X ≫ snd = Cat.id X from snd_pair _ _,
        Cat.id_comp, Cat.assoc, show diag Y ≫ snd = Cat.id Y from snd_pair _ _, Cat.comp_id]

/-- **Decidability transports along isos**: if `X ≅ Y` (witnessed by a MONO `φ`, e.g. an iso)
    and `Y` is decidable, so is `X`.  The diagonal `Δ_X` coincides with `(φ×φ)# Δ_Y`
    (`φ` mono ⟹ `φ(x₁)=φ(x₂) ↔ x₁=x₂`), and inverse images of complemented subobjects are
    complemented (`diagonal_classifies`). -/
public theorem decidableSub_of_mono {X Y : 𝒞} (φ : X ⟶ Y) (hφ : Monic φ)
    (hY : DecidableObjectSub Y) : DecidableObjectSub X := by
  let pbeq := HasPullbacks.has (prodSelfMap φ) (diagSub Y).arr
  refine diagonal_classifies hY (prodSelfMap φ) ?_ ?_
  · -- diagSub X ≤ c#(diagSub Y) : the cone ⟨X, diag X, φ, diag_prodSelfMap⟩ lifts.
    have hw : diag X ≫ prodSelfMap φ = φ ≫ (diagSub Y).arr := diag_prodSelfMap φ
    exact ⟨pbeq.lift ⟨X, diag X, φ, hw⟩, pbeq.lift_fst ⟨X, diag X, φ, hw⟩⟩
  · -- c#(diagSub Y) ≤ diagSub X : π₁ factors through diag X since its two coords agree.
    have hw : pbeq.cone.π₁ ≫ prodSelfMap φ = pbeq.cone.π₂ ≫ diag Y := pbeq.cone.w
    have hcoord : pbeq.cone.π₁ ≫ fst = pbeq.cone.π₁ ≫ snd := by
      apply hφ
      -- (π₁≫fst)≫φ = (π₁≫c)≫fst = (π₂≫diagY)≫fst = (π₂≫diagY)≫snd = (π₁≫c)≫snd = (π₁≫snd)≫φ
      have hdd : diag Y ≫ fst = diag Y ≫ snd := by
        rw [show diag Y ≫ fst = Cat.id Y from fst_pair _ _,
          show diag Y ≫ snd = Cat.id Y from snd_pair _ _]
      calc (pbeq.cone.π₁ ≫ fst) ≫ φ
          = (pbeq.cone.π₁ ≫ prodSelfMap φ) ≫ fst := by
            rw [Cat.assoc, Cat.assoc, show prodSelfMap φ ≫ fst = fst ≫ φ from fst_pair _ _]
        _ = (pbeq.cone.π₂ ≫ diag Y) ≫ fst := by rw [hw]
        _ = pbeq.cone.π₂ ≫ (diag Y ≫ fst) := Cat.assoc _ _ _
        _ = pbeq.cone.π₂ ≫ (diag Y ≫ snd) := by rw [hdd]
        _ = (pbeq.cone.π₂ ≫ diag Y) ≫ snd := (Cat.assoc _ _ _).symm
        _ = (pbeq.cone.π₁ ≫ prodSelfMap φ) ≫ snd := by rw [hw]
        _ = (pbeq.cone.π₁ ≫ snd) ≫ φ := by
            rw [Cat.assoc, Cat.assoc, show prodSelfMap φ ≫ snd = snd ≫ φ from snd_pair _ _]
    -- π₁ = pair (π₁≫fst) (π₁≫snd) = (π₁≫fst) ≫ diag X.
    refine ⟨pbeq.cone.π₁ ≫ fst, ?_⟩
    show (pbeq.cone.π₁ ≫ fst) ≫ diag X = pbeq.cone.π₁
    apply fst_snd_jointly_monic
    · rw [Cat.assoc, show diag X ≫ fst = Cat.id X from fst_pair _ _, Cat.comp_id]
    · rw [Cat.assoc, show diag X ≫ snd = Cat.id X from snd_pair _ _, Cat.comp_id, hcoord]

/-- `DecidableObjectSub` transports across an isomorphism `X ≅ Y`. -/
theorem decidableSub_of_iso {X Y : 𝒞} (h : Isomorphic X Y) (hY : DecidableObjectSub Y) :
    DecidableObjectSub X := by
  obtain ⟨φ, φinv, hfg, _⟩ := h
  have hmono : Monic φ := by
    intro W u v huv
    have := congrArg (· ≫ φinv) huv
    simpa only [Cat.assoc, hfg, Cat.comp_id] using this
  exact decidableSub_of_mono φ hmono hY
