/-
  Freyd & Scedrov, *Categories and Allegories* §1.93  The slice lemma — step 1.

  The SLICE SUBOBJECT CLASSIFIER.  Given a base subobject classifier Ω on 𝒞
  (Cartesian, with pullbacks), the slice category `Over B` carries one too:

      Ω_{Over B}  :=  Δ(Ω)  =  ⟨Ω × B, snd⟩ : Over B
      true_B      :=  Δ(true)

  where `Δ : 𝒞 → Over B`, `Δ(A) = ⟨A × B, snd⟩`, is the base-change-into-the-slice
  functor.  The characteristic map of a slice mono is computed in the base along
  the FAITHFUL forgetful `Σ = SliceForget : Over B → 𝒞` and lifted back into the
  slice; the pullback fields are transported along Σ, using that Σ creates
  pullbacks (`overPullbackPt`, S1_44) and is faithful.

  Construction (subobject-classifier route, §1.93): `Sub_{E/B}(X) ≅ Sub_E(Σ X)`
  naturally, so the classifier of `Over B` is `Δ` of the base classifier.

  This is the self-contained foundation of the §1.93 slice-lemma route to full
  topos regularity (`PullbacksTransferCovers`).  ADDITIVE: a new file built only
  from the base classifier + slice transport; NO new axioms, NO allegory axioms.
-/

module

public import Freyd.S1_90
public import Freyd.S1_44
public import Freyd.S1_53_SliceRegular

universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

open HasSubobjectClassifier

/-! ## §1.93  The slice classifier object `Δ(Ω) = ⟨Ω × B, snd⟩`

  Everything below assumes a base subobject classifier (which packs `HasTerminal`
  and `HasPullbacks`) plus binary products, so that `Ω × B` exists. -/

variable [HasSubobjectClassifier 𝒞] [HasBinaryProducts 𝒞]

/-- The slice classifier object `Δ(Ω) = ⟨Ω × B, snd⟩ : Over B`. -/
@[expose] public def sliceOmega (B : 𝒞) : Over B := ⟨prod omega B, snd⟩

/-- The slice universal subobject `true_B = Δ(true) : 1_{Over B} ⟶ Δ(Ω)`.

  Underlying base arrow: `B = (overTerm B).dom ⟶ Ω × B` is `⟨B→1→Ω , id_B⟩`.
  It respects the slice structure because its second component is `id_B`. -/
@[expose] public def sliceTrue (B : 𝒞) : OverHom (overTerm B) (sliceOmega B) :=
  ⟨pair (term B ≫ HasSubobjectClassifier.true) (Cat.id B), by
    -- (overTerm B).hom = id B; need  pair (..) (id B) ≫ snd = id B
    simp [sliceOmega, overTerm, snd_pair]⟩

/-! ## Faithful-transport of pullbacks along `Σ = SliceForget`

  A slice cone over `(f, g)` is a pullback **iff** its underlying base cone
  (apply `.f` to point and projections) is a pullback in `𝒞`.  This is the only
  non-formal lemma: it rests on Σ being faithful and creating pullbacks
  (`overPullbackPt`, S1_44). -/

variable [HasPullbacks 𝒞]

/-- **Σ reflects pullbacks (general base `B`)**: if the `Σ`-image of a slice cone
    is a pullback in `𝒞`, the slice cone is a pullback in `Over B`.  The base lift
    `u` carries an over-hom triangle because `c.π₁` is itself an over-hom
    (`c.π₁.w`), so reflection holds over *any* base, not just the terminal.

    Companion to S1_53's `sliceForget_preserves_isPullback` (preservation) and
    strengthening of `sliceForget_reflects_isPullback_terminal` (which is restricted
    to `Over 1`).  This is the only new transport lemma the slice classifier needs. -/
public theorem sliceForget_reflects_isPullback {B : 𝒞} {X Y Z : Over B}
    {f : X ⟶ Z} {g : Y ⟶ Z} (c : Cone f g)
    (h : (sliceConeForget c).IsPullback) : c.IsPullback := by
  intro d
  -- forget the test cone d to the base, get the base lift, then re-lift to slice.
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := h (sliceConeForget d)
  have hu₁' : u ≫ c.π₁.f = d.π₁.f := hu₁
  have hu₂' : u ≫ c.π₂.f = d.π₂.f := hu₂
  -- u : d.pt.dom ⟶ c.pt.dom is the base lift; its over-hom triangle uses c.π₁.w.
  have uw : u ≫ c.pt.hom = d.pt.hom := by
    have h1 : u ≫ (c.π₁.f ≫ X.hom) = d.π₁.f ≫ X.hom := by rw [← Cat.assoc, hu₁']
    rwa [c.π₁.w, d.π₁.w] at h1
  refine ⟨⟨u, uw⟩, ⟨OverHom.ext hu₁', OverHom.ext hu₂'⟩, ?_⟩
  intro v hv₁ hv₂
  exact OverHom.ext (huniq v.f (congrArg OverHom.f hv₁) (congrArg OverHom.f hv₂))

/-! ## §1.93  The slice characteristic map and the classifier fields -/

/-- Base characteristic map of a slice mono `m`, viewing `m.f` as a base mono. -/
@[expose] public noncomputable def baseClassify {B : 𝒞} {A A' : Over B} (m : OverHom A' A) (hm : OverMono m) :
    A.dom ⟶ omega :=
  HasSubobjectClassifier.classify m.f (sigma_preserves_mono m hm)

/-- The slice characteristic map `χ_m : A ⟶ Δ(Ω)`, with underlying base arrow
    `⟨χ_base , A.hom⟩ : A.dom ⟶ Ω × B`. -/
@[expose] public noncomputable def sliceClassify {B : 𝒞} {A A' : Over B} (m : OverHom A' A) (hm : OverMono m) :
    OverHom A (sliceOmega B) :=
  ⟨pair (baseClassify m hm) A.hom, by simp [sliceOmega, snd_pair]⟩

/-- The slice classifying square commutes (Δ-level): `m ⊚ χ_m = term A' ⊚ true_B`. -/
public theorem sliceClassify_sq {B : 𝒞} {A A' : Over B} (m : OverHom A' A) (hm : OverMono m) :
    m ⊚ sliceClassify m hm = term A' ⊚ sliceTrue B := by
  apply OverHom.ext
  -- on base arrows: m.f ≫ pair χ A.hom = (term A').f ≫ pair (term B ≫ true) (id B)
  -- (term A').f = A'.hom.
  show m.f ≫ pair (baseClassify m hm) A.hom
      = (term A').f ≫ pair (term B ≫ HasSubobjectClassifier.true) (Cat.id B)
  have htermf : (term A' : OverHom A' (overTerm B)).f = A'.hom := rfl
  rw [htermf]
  -- base classify_sq + product structure.  Reduce both sides to `pair (m.f ≫ χ) A'.hom`.
  have hbase := HasSubobjectClassifier.classify_sq m.f (sigma_preserves_mono m hm)
  -- hbase : m.f ≫ classify m.f .. = term A'.dom ≫ true
  have hL : m.f ≫ pair (baseClassify m hm) A.hom
      = pair (m.f ≫ baseClassify m hm) A'.hom := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair]
    · rw [Cat.assoc, snd_pair]; exact m.w
  have hR : A'.hom ≫ pair (term B ≫ HasSubobjectClassifier.true) (Cat.id B)
      = pair (m.f ≫ baseClassify m hm) A'.hom := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, baseClassify, hbase, ← Cat.assoc]
      congr 1; exact term_uniq _ _
    · rw [Cat.assoc, snd_pair, Cat.comp_id]
  rw [hL, hR]

/-- **classify_pullback**: the slice classifying square is a pullback in `Over B`.
    Transported from the base pullback (`classify_pullback`) via Σ-reflection. -/
public theorem sliceClassify_pullback {B : 𝒞} {A A' : Over B} (m : OverHom A' A) (hm : OverMono m) :
    (⟨A', m, term A', sliceClassify_sq m hm⟩ :
        Cone (sliceClassify m hm) (sliceTrue B)).IsPullback := by
  apply sliceForget_reflects_isPullback
  -- Reduce to the BASE classifier pullback of `m.f` over `(χ, true)`.  The slice
  -- cospan into `Ω×B` decomposes via product projections: `fst` recovers the base
  -- classifier square, `snd` forces the B-leg `q = p ≫ A.hom`.  So a test cone over
  -- the `Ω×B`-cospan is exactly a test cone over `(χ, true)` (B-leg redundant).
  have hmf : Monic m.f := sigma_preserves_mono m hm
  let χ : A.dom ⟶ omega := baseClassify m hm
  have hbasePB := HasSubobjectClassifier.classify_pullback m.f hmf
  -- hbasePB : (⟨A'.dom, m.f, term A'.dom, classify_sq⟩ : Cone χ true).IsPullback
  intro d
  -- d : Cone (pair χ A.hom) (pair (term B ≫ true) (id B)); legs p := d.π₁, q := d.π₂.
  -- From the product square: q = p ≫ A.hom, and p ≫ χ = term d.pt ≫ true.
  have hdw : d.π₁ ≫ pair (baseClassify m hm) A.hom
      = d.π₂ ≫ pair (term B ≫ HasSubobjectClassifier.true) (Cat.id B) := d.w
  have hsnd : d.π₁ ≫ A.hom = d.π₂ := by
    have h := congrArg (· ≫ snd) hdw
    simp only [Cat.assoc, snd_pair] at h
    rw [← Cat.comp_id (d.π₂)]
    exact h
  have hfst : d.π₁ ≫ χ = term d.pt ≫ HasSubobjectClassifier.true := by
    have hw := congrArg (· ≫ fst) hdw
    -- (d.π₁ ≫ pair χ A.hom) ≫ fst = (d.π₂ ≫ pair (term B ≫ true) (id B)) ≫ fst
    simp only [Cat.assoc, fst_pair] at hw
    -- hw : d.π₁ ≫ χ = d.π₂ ≫ (term B ≫ true)
    rw [hw, ← hsnd, ← Cat.assoc]
    congr 1
    exact term_uniq _ _
  -- feed the base classifier pullback with the test cone (d.pt, d.π₁, term d.pt).
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hbasePB ⟨d.pt, d.π₁, term d.pt, hfst⟩
  -- hu₁ : u ≫ m.f = d.π₁;  base second leg auto by terminal uniqueness.
  refine ⟨u, ⟨hu₁, ?_⟩, ?_⟩
  · -- u ≫ (term A').f = d.π₂, i.e. u ≫ A'.hom = d.π₂.  Use m.w + hu₁ + hsnd.
    show u ≫ A'.hom = d.π₂
    rw [← m.w, ← Cat.assoc, hu₁, hsnd]
  · intro v hv₁ hv₂
    -- v ≫ m.f = d.π₁ and v ≫ A'.hom = d.π₂; base uniqueness needs v ≫ term A'.dom = term d.pt.
    exact huniq v hv₁ (term_uniq _ _)

/-- **classify_unique**: `χ_m` is the unique slice map making `m` a pullback of
    `true_B`. -/
public theorem sliceClassify_unique {B : 𝒞} {A A' : Over B} (m : OverHom A' A) (hm : OverMono m)
    (χ : OverHom A (sliceOmega B)) (hsq : m ⊚ χ = term A' ⊚ sliceTrue B)
    (hpb : (⟨A', m, term A', hsq⟩ : Cone χ (sliceTrue B)).IsPullback) :
    χ = sliceClassify m hm := by
  have hmf : Monic m.f := sigma_preserves_mono m hm
  -- χ is an over-hom into ⟨Ω×B, snd⟩, so χ.f ≫ snd = A.hom; set χ_base := χ.f ≫ fst.
  have hχsnd : χ.f ≫ snd = A.hom := χ.w
  let χb : A.dom ⟶ omega := χ.f ≫ fst
  have hχb : χb = χ.f ≫ fst := rfl
  have hχeta : χ.f = pair χb A.hom := by
    rw [hχb]; exact (pair_uniq _ _ χ.f rfl hχsnd)
  -- (1) base square commutes: m.f ≫ χb = term A'.dom ≫ true.
  have hsqf : m.f ≫ χ.f = A'.hom ≫ (sliceTrue B).f := congrArg OverHom.f hsq
  have hbsq : m.f ≫ χb = term A'.dom ≫ HasSubobjectClassifier.true := by
    have h := congrArg (· ≫ fst) hsqf
    simp only [Cat.assoc, sliceTrue, fst_pair] at h
    -- h : m.f ≫ χ.f ≫ fst = A'.hom ≫ (term B ≫ true)
    rw [hχb, h, ← Cat.assoc]
    congr 1; exact term_uniq _ _
  -- (2) base square is a pullback over (χb, true).  Reduce from the slice pullback:
  -- Σ preserves it (over Ω×B); a test cone over (χb, true) lifts to one over (χ.f, g0).
  have hbasePB : (⟨A'.dom, m.f, term A'.dom, hbsq⟩ :
      Cone χb HasSubobjectClassifier.true).IsPullback := by
    have hΩB := sliceForget_preserves_isPullback _ hpb
    -- hΩB : (sliceConeForget ⟨A',m,term A',hsq⟩).IsPullback, over (χ.f, (sliceTrue B).f).
    intro e
    -- e : Cone χb true (apex T, legs p:=e.π₁, q:=e.π₂, e.w : p ≫ χb = q ≫ true).
    -- lift e to a cone over (χ.f, g0): apex T, legs ⟨p, ⟨q≫? ⟩⟩ ... use
    -- A-leg p, B-leg = e.π₂... build the Ω×B-cone with legs (p, p ≫ A.hom).
    -- second leg into (overTerm B).dom = B is  p ≫ A.hom.
    have ewL : e.π₁ ≫ pair χb A.hom = pair (e.π₁ ≫ χb) (e.π₁ ≫ A.hom) := by
      apply pair_uniq
      · rw [Cat.assoc, fst_pair]
      · rw [Cat.assoc, snd_pair]
    have ewR : (e.π₁ ≫ A.hom) ≫ pair (term B ≫ HasSubobjectClassifier.true) (Cat.id B)
        = pair (e.π₁ ≫ χb) (e.π₁ ≫ A.hom) := by
      apply pair_uniq
      · -- (e.π₁ ≫ A.hom) ≫ (term B ≫ true) = e.π₁ ≫ χb.
        -- both sides equal `term e.pt ≫ true` (terminal uniqueness + e.w).
        rw [Cat.assoc, fst_pair, e.w]
        -- goal: (e.π₁ ≫ A.hom) ≫ (term B ≫ true) = e.π₂ ≫ true
        rw [← Cat.assoc]; congr 1; exact term_uniq _ _
      · rw [Cat.assoc, snd_pair, Cat.comp_id]
    have ew : e.π₁ ≫ pair χb A.hom
        = (e.π₁ ≫ A.hom) ≫ pair (term B ≫ HasSubobjectClassifier.true) (Cat.id B) := by
      rw [ewL, ewR]
    -- turn ew into a cone over (χ.f, (sliceTrue B).f) via hχeta and sliceTrue defn.
    have ew' : e.π₁ ≫ χ.f = (e.π₁ ≫ A.hom) ≫ (sliceTrue B).f := by
      rw [hχeta]; exact ew
    obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hΩB ⟨e.pt, e.π₁, e.π₁ ≫ A.hom, ew'⟩
    -- hu₁ : u ≫ m.f = e.π₁;  base second leg auto by terminal uniqueness.
    refine ⟨u, ⟨hu₁, term_uniq _ _⟩, ?_⟩
    intro v hv₁ _
    exact huniq v hv₁ (by
      -- v ≫ (term A').f = e.π₁ ≫ A.hom, i.e. v ≫ A'.hom = e.π₁ ≫ A.hom.
      show v ≫ A'.hom = e.π₁ ≫ A.hom
      rw [← m.w, ← Cat.assoc, hv₁])
  -- conclude via base classify_unique, then lift back to the slice.
  have hχbeq : χb = HasSubobjectClassifier.classify m.f hmf :=
    HasSubobjectClassifier.classify_unique m.f hmf χb hbsq hbasePB
  apply OverHom.ext
  show χ.f = (sliceClassify m hm).f
  rw [hχeta]
  show pair χb A.hom = pair (baseClassify m hm) A.hom
  rw [hχbeq]; rfl

@[expose] public noncomputable instance overHasSubobjectClassifier (B : 𝒞) :
    HasSubobjectClassifier (Over B) where
  toHasTerminal := overHasTerminal B
  toHasPullbacks := overHasPullbacks B
  omega := sliceOmega B
  true := sliceTrue B
  classify m hm := sliceClassify m hm
  classify_sq m hm := sliceClassify_sq m hm
  classify_pullback m hm := sliceClassify_pullback m hm
  classify_unique m hm χ hsq hpb := sliceClassify_unique m hm χ hsq hpb

end Freyd
