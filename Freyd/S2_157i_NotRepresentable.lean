/-
  Freyd & Scedrov, *Categories and Allegories* §2.157 — the p. 15 NON-REPRESENTABILITY payoff.

  §2.157h produced `VW_not_desarguesHorn`: the one-object allegory `LMonObj (PElem VW)` of
  the Veblen–Wedderburn plane violates the Desargues Horn sentence.  Since the Horn
  sentence "is easily verified for Rel(S)" and Horn sentences transfer backwards along
  faithful allegory representations, the VW allegory admits NO faithful representation in
  `Rel(Set)` — Horn sentences do not axiomatise the representable allegories.

  Formalised here:
  · monotonicity of an allegory functor (`AllegoryFunctor.mono`, §2.51: preserves `⊑`); a
    FAITHFUL one reflects it too (used inline in `desarguesHorn_reflect` via `map_inter` +
    faithfulness).
  · `desarguesHorn_reflect` — the Horn sentence transfers backwards along any faithful
    allegory functor: push the hypothesis inclusion forward, apply the Horn sentence in
    the target, reflect the conclusion inclusion back.
  · `setRel` and its `≫`/`°`/`∩`/`⊑` computation rules — the bridge from the honest
    quotient allegory `RelObj (Type u)` (§2.111) to concrete binary relations.
  · `desarguesHorn_relObj` — `Rel(Set)` satisfies the Horn sentence (the §2.157 element
    chase `desarguesHorn_binRel`, wired through the bridge).
  · `VW_not_representable` — THE HEADLINE: no faithful allegory representation
    `LMonObj (PElem VW) → RelObj (Type u)`.
  · `desarguesHorn_relObjPower` / `VW_not_representable_in_power` — the same for any
    power `Rel(Set^I)`, the target of the §2.218 representation theorems.
-/
import Freyd.S2_157h_VeblenWedderburn
import Freyd.S2_111_RelCat

universe v u u₁ u₂ v₁ v₂

namespace Freyd.Alg

/-! ## The Desargues Horn sentence transfers backwards along faithful representations

  Uses `AllegoryFunctor.mono` (§2.51): an allegory functor preserves the order `⊑`. -/

/-- **Horn reflection**: if `F : 𝒜 → ℬ` is a faithful allegory functor and `ℬ` satisfies
    the Desargues Horn sentence, so does `𝒜`.  Both sides of each inclusion are built from
    `≫`/`°`/`∩`, which `F` preserves on the nose; the hypothesis inclusion is pushed
    forward by monotonicity, the conclusion inclusion reflected back by faithfulness. -/
theorem desarguesHorn_reflect {𝒜 : Type u₁} {ℬ : Type u₂} [Allegory.{v₁} 𝒜] [Allegory.{v₂} ℬ]
    (F : AllegoryFunctor 𝒜 ℬ) (hF : F.Faithful) (horn : DesarguesHorn ℬ) :
    DesarguesHorn 𝒜 := by
  intro p q a b c A₁ A₂ B₁ B₂ C₁ C₂ hyp
  refine hF _ _ ?_
  rw [F.map_inter]
  have hpush : (F.map A₁ ≫ F.map A₂) ∩ (F.map B₁ ≫ F.map B₂) ⊑ F.map C₁ ≫ F.map C₂ := by
    have := F.mono hyp
    rwa [F.map_inter, F.map_comp, F.map_comp, F.map_comp] at this
  have hconc := horn (F.obj p) (F.obj q) (F.obj a) (F.obj b) (F.obj c)
    (F.map A₁) (F.map A₂) (F.map B₁) (F.map B₂) (F.map C₁) (F.map C₂) hpush
  -- rewrite both sides back into images of the 𝒜-composites
  simp only [F.map_inter, F.map_comp, F.map_recip]
  exact hconc

/-! ## The bridge: spans over `Set` and their concrete binary relations

  A morphism of `RelObj (Type u)` (§2.111) is a `RelLe`-class of jointly-monic spans
  `⟨T; colA : T → a, colB : T → b⟩`.  Each span induces the concrete relation
  "`x` and `y` have a common preimage"; under the §1.52 Set instances (product `×`,
  pullback = fibre subtype, image = image subtype) the span operations `⊚`/`°`/`⊓`/`⊂`
  compute to relational composition/transpose/pointwise-and/pointwise-implication. -/

section RelSetBridge

variable {a b c : Type u}

/-- The concrete binary relation of a span: `x` and `y` are related iff they are the
    two column values of a common row. -/
def setRel (R : BinRel (Type u) a b) : a → b → Prop :=
  fun x y => ∃ t : R.src, R.colA t = x ∧ R.colB t = y

/-- `°` computes to transposition. -/
theorem setRel_recip (R : BinRel (Type u) a b) (x : a) (y : b) :
    setRel R° y x ↔ setRel R x y :=
  ⟨fun ⟨t, h1, h2⟩ => ⟨t, h2, h1⟩, fun ⟨t, h1, h2⟩ => ⟨t, h2, h1⟩⟩

/-- `⊂` computes to pointwise implication.  (⇐) picks a row of `S` over each row of
    `R` (`Classical.choice`); joint monicity is not needed. -/
theorem relLe_iff_setRel {R S : BinRel (Type u) a b} :
    RelLe R S ↔ ∀ x y, setRel R x y → setRel S x y := by
  constructor
  · rintro ⟨⟨h, hA, hB⟩⟩ x y ⟨t, rfl, rfl⟩
    exact ⟨h t, congrFun hA t, congrFun hB t⟩
  · intro hsub
    have pick : ∀ t : R.src, ∃ s : S.src, S.colA s = R.colA t ∧ S.colB s = R.colB t :=
      fun t => hsub _ _ ⟨t, rfl, rfl⟩
    exact ⟨⟨fun t => (pick t).choose,
      funext fun t => (pick t).choose_spec.1,
      funext fun t => (pick t).choose_spec.2⟩⟩

/-- The ONE-ROW span `{(x, y)}`: source `PUnit` (trivially jointly monic). -/
def pointRel (x : a) (y : b) : BinRel (Type u) a b where
  src := PUnit
  colA := fun _ => x
  colB := fun _ => y
  isMonicPair := fun f g _ _ => funext fun w =>
    match f w, g w with | PUnit.unit, PUnit.unit => rfl

/-- `pointRel x y ⊂ R` as soon as `R` relates `x` to `y`. -/
theorem pointRel_le {R : BinRel (Type u) a b} {x : a} {y : b} (h : setRel R x y) :
    RelLe (pointRel x y) R :=
  relLe_iff_setRel.mpr fun _ _ ⟨_, h1, h2⟩ => h1 ▸ h2 ▸ h

/-- `⊓` computes to pointwise conjunction — abstractly, via the meet UMP
    (`intersect_le_*`, `le_intersect`) and the one-row span. -/
theorem setRel_inter (R S : BinRel (Type u) a b) (x : a) (y : b) :
    setRel (R ⊓ S) x y ↔ setRel R x y ∧ setRel S x y := by
  constructor
  · intro h
    exact ⟨relLe_iff_setRel.mp (intersect_le_left R S) x y h,
           relLe_iff_setRel.mp (intersect_le_right R S) x y h⟩
  · rintro ⟨hR, hS⟩
    exact relLe_iff_setRel.mp (le_intersect (pointRel_le hR) (pointRel_le hS))
      x y ⟨PUnit.unit, rfl, rfl⟩

/-- `⊚` computes to relational composition.  Forward: image minimality compares the
    §1.51 image with the concrete image subtype, lifting each row of `R ⊚ S` back to
    the §1.56 pullback; backward: the pullback UMP lifts the common value `y`, and the
    image's `Allows` pushes the resulting pullback row into `R ⊚ S`.  Only `pair`/`fst`/
    `snd`-level Set computation is used; the pullback and image are handled by UMPs. -/
theorem setRel_comp (R : BinRel (Type u) a b) (S : BinRel (Type u) b c) (x : a) (z : c) :
    setRel (R ⊚ S) x z ↔ ∃ y, setRel R x y ∧ setRel S y z := by
  -- the ingredients of `compose R S`, re-created definitionally
  let pb := HasPullbacks.has R.colB S.colA
  let h : pb.cone.pt ⟶ prod a c := pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ S.colB)
  constructor
  · rintro ⟨t, h1, h2⟩
    -- the concrete image subtype, as a §1.51 subobject
    let J : Subobject (Type u) (prod a c) :=
      ⟨{w : prod a c // ∃ q, h q = w}, Subtype.val,
        fun f g hfg => funext fun w => Subtype.ext (congrFun hfg w)⟩
    -- image minimality: the §1.51 image factors through `J`, so the row `t` lifts
    obtain ⟨k, hk⟩ := (HasImages.isImage h).2 J ⟨fun q => ⟨h q, q, rfl⟩, rfl⟩
    obtain ⟨q, hq⟩ := (k t).property
    have harr : h q = (image h).arr t := hq.trans (congrFun hk t)
    refine ⟨R.colB (pb.cone.π₁ q), ⟨pb.cone.π₁ q, ?_, rfl⟩, ⟨pb.cone.π₂ q, ?_, ?_⟩⟩
    · exact (congrArg Prod.fst harr).trans h1
    · exact (congrFun pb.cone.w q).symm
    · exact (congrArg Prod.snd harr).trans h2
  · rintro ⟨y, ⟨r, hr1, hr2⟩, ⟨s, hs1, hs2⟩⟩
    -- lift the matching rows `r`, `s` into the pullback
    let d : Cone R.colB S.colA :=
      { pt := PUnit, π₁ := fun _ => r, π₂ := fun _ => s,
        w := funext fun _ => hr2.trans hs1.symm }
    let q : pb.cone.pt := pb.lift d PUnit.unit
    have hq1 : pb.cone.π₁ q = r := congrFun (pb.lift_fst d) PUnit.unit
    have hq2 : pb.cone.π₂ q = s := congrFun (pb.lift_snd d) PUnit.unit
    -- push into the image
    obtain ⟨gI, hgI⟩ := (HasImages.isImage h).1
    have harr : (image h).arr (gI q) = h q := congrFun hgI q
    refine ⟨gI q, ?_, ?_⟩
    · calc ((image h).arr (gI q)).1 = (h q).1 := congrArg Prod.fst harr
        _ = R.colA (pb.cone.π₁ q) := rfl
        _ = R.colA r := congrArg R.colA hq1
        _ = x := hr1
    · calc ((image h).arr (gI q)).2 = (h q).2 := congrArg Prod.snd harr
        _ = S.colB (pb.cone.π₂ q) := rfl
        _ = S.colB s := congrArg S.colB hq2
        _ = z := hs2

/-! ## `Rel(Set)` satisfies the Desargues Horn sentence (§2.157: "easily verified") -/

/-- The Horn sentence at the SPAN level over `Set`: the §2.157 element chase
    `desarguesHorn_binRel`, transported through the `setRel` computation rules. -/
theorem desarguesHorn_span {p q a b c : Type u}
    (A₁ : BinRel (Type u) p a) (A₂ : BinRel (Type u) a q)
    (B₁ : BinRel (Type u) p b) (B₂ : BinRel (Type u) b q)
    (C₁ : BinRel (Type u) p c) (C₂ : BinRel (Type u) c q)
    (hyp : RelLe ((A₁ ⊚ A₂) ⊓ (B₁ ⊚ B₂)) (C₁ ⊚ C₂)) :
    RelLe ((A₁° ⊚ B₁) ⊓ (A₂ ⊚ B₂°))
      (((A₁° ⊚ C₁) ⊓ (A₂ ⊚ C₂°)) ⊚ ((C₁° ⊚ B₁) ⊓ (C₂ ⊚ B₂°))) := by
  -- the hypothesis, element-wise
  have hyp' : ∀ (u : p) (v : q),
      (∃ x, setRel A₁ u x ∧ setRel A₂ x v) ∧ (∃ y, setRel B₁ u y ∧ setRel B₂ y v) →
      ∃ z, setRel C₁ u z ∧ setRel C₂ z v := fun u v ⟨hA, hB⟩ =>
    (setRel_comp C₁ C₂ u v).mp (relLe_iff_setRel.mp hyp u v
      ((setRel_inter _ _ u v).mpr
        ⟨(setRel_comp A₁ A₂ u v).mpr hA, (setRel_comp B₁ B₂ u v).mpr hB⟩))
  refine relLe_iff_setRel.mpr fun x y hxy => ?_
  obtain ⟨h1, h2⟩ := (setRel_inter _ _ x y).mp hxy
  obtain ⟨u, hu1, hu2⟩ := (setRel_comp _ _ x y).mp h1
  obtain ⟨v, hv1, hv2⟩ := (setRel_comp _ _ x y).mp h2
  -- the §2.157 element chase
  obtain ⟨z, ⟨⟨u₁, hzu1, hzu2⟩, ⟨v₁, hzv1, hzv2⟩⟩, ⟨u₂, hzu3, hzu4⟩, v₂, hzv3, hzv4⟩ :=
    desarguesHorn_binRel (setRel A₁) (setRel A₂) (setRel B₁) (setRel B₂)
      (setRel C₁) (setRel C₂) hyp' x y
      ⟨⟨u, (setRel_recip A₁ u x).mp hu1, hu2⟩, ⟨v, hv1, (setRel_recip B₂ y v).mp hv2⟩⟩
  refine (setRel_comp _ _ x y).mpr ⟨z, (setRel_inter _ _ x z).mpr ⟨?_, ?_⟩,
    (setRel_inter _ _ z y).mpr ⟨?_, ?_⟩⟩
  · exact (setRel_comp _ _ x z).mpr ⟨u₁, (setRel_recip A₁ u₁ x).mpr hzu1, hzu2⟩
  · exact (setRel_comp _ _ x z).mpr ⟨v₁, hzv1, (setRel_recip C₂ z v₁).mpr hzv2⟩
  · exact (setRel_comp _ _ z y).mpr ⟨u₂, (setRel_recip C₁ u₂ z).mpr hzu3, hzu4⟩
  · exact (setRel_comp _ _ z y).mpr ⟨v₂, hzv3, (setRel_recip B₂ y v₂).mpr hzv4⟩

/-- **§2.157, "It is easily verified for Rel(S)"** — the Desargues Horn sentence holds
    in the honest §2.111 allegory of relations over `Set`. -/
theorem desarguesHorn_relObj : DesarguesHorn (RelObj (Type u)) := by
  intro P Q A B C A₁ A₂ B₁ B₂ C₁ C₂
  refine Quotient.inductionOn₃ A₁ A₂ B₁ (fun A₁ A₂ B₁ => ?_)
  refine Quotient.inductionOn₃ B₂ C₁ C₂ (fun B₂ C₁ C₂ => ?_)
  intro hyp
  rw [← quotLe_iff_algLe] at hyp ⊢
  exact desarguesHorn_span A₁ A₂ B₁ B₂ C₁ C₂ hyp

end RelSetBridge

/-! ## The power bridge: spans over `Set^I` fibrewise

  §2.218 represents allegories in POWERS `Rel(Set^I)`, so the non-representability
  headline should exclude those too.  The §1.521 power instances compute everything
  fibrewise, and the `setRel` bridge mirrors with an index `i` threaded through; the
  only new ingredient is the POINTED one-row span `pointRelPow` supported at a single
  fibre `i` (source `ULift (PLift (i = j))`, the empty-elsewhere family of
  `powerPullbacksTransferCovers` — no choice, no decidability on `I`). -/

section RelPowerBridge

variable {I : Type u} {a b c : I → Type u}

/-- The concrete binary relation of a power span at fibre `i`. -/
def powRel (R : BinRel (I → Type u) a b) (i : I) : a i → b i → Prop :=
  fun x y => ∃ t : R.src i, R.colA i t = x ∧ R.colB i t = y

/-- `°` computes to fibrewise transposition. -/
theorem powRel_recip (R : BinRel (I → Type u) a b) (i : I) (x : a i) (y : b i) :
    powRel R° i y x ↔ powRel R i x y :=
  ⟨fun ⟨t, h1, h2⟩ => ⟨t, h2, h1⟩, fun ⟨t, h1, h2⟩ => ⟨t, h2, h1⟩⟩

/-- `⊂` computes to fibrewise pointwise implication. -/
theorem relLe_iff_powRel {R S : BinRel (I → Type u) a b} :
    RelLe R S ↔ ∀ i x y, powRel R i x y → powRel S i x y := by
  constructor
  · rintro ⟨⟨h, hA, hB⟩⟩ i x y ⟨t, rfl, rfl⟩
    exact ⟨h i t, congrFun (congrFun hA i) t, congrFun (congrFun hB i) t⟩
  · intro hsub
    have pick : ∀ i (t : R.src i),
        ∃ s : S.src i, S.colA i s = R.colA i t ∧ S.colB i s = R.colB i t :=
      fun i t => hsub i _ _ ⟨t, rfl, rfl⟩
    exact ⟨⟨fun i t => (pick i t).choose,
      funext fun i => funext fun t => (pick i t).choose_spec.1,
      funext fun i => funext fun t => (pick i t).choose_spec.2⟩⟩

/-- The ONE-ROW span `{(x, y)}` supported at fibre `i`: the pointed family
    `ULift (PLift (i = j))`, inhabited only at `j = i`. -/
def pointRelPow (i : I) (x : a i) (y : b i) : BinRel (I → Type u) a b where
  src := fun j => ULift.{u} (PLift (i = j))
  colA := fun _ p => p.down.down ▸ x
  colB := fun _ p => p.down.down ▸ y
  isMonicPair := fun f g _ _ => funext fun j => funext fun w => by
    rcases hf : f j w with ⟨⟨e⟩⟩; rcases hg : g j w with ⟨⟨e'⟩⟩; rfl

theorem powRel_pointRelPow (i : I) (x : a i) (y : b i) :
    powRel (pointRelPow i x y) i x y :=
  ⟨ULift.up (PLift.up rfl), rfl, rfl⟩

/-- `pointRelPow i x y ⊂ R` as soon as `R` relates `x` to `y` at fibre `i`. -/
theorem pointRelPow_le {R : BinRel (I → Type u) a b} {i : I} {x : a i} {y : b i}
    (h : powRel R i x y) : RelLe (pointRelPow i x y) R :=
  relLe_iff_powRel.mpr fun j x' y' ⟨w, h1, h2⟩ => by
    obtain ⟨⟨e⟩⟩ := w; cases e; exact h1 ▸ h2 ▸ h

/-- `⊓` computes to fibrewise conjunction. -/
theorem powRel_inter (R S : BinRel (I → Type u) a b) (i : I) (x : a i) (y : b i) :
    powRel (R ⊓ S) i x y ↔ powRel R i x y ∧ powRel S i x y := by
  constructor
  · intro h
    exact ⟨relLe_iff_powRel.mp (intersect_le_left R S) i x y h,
           relLe_iff_powRel.mp (intersect_le_right R S) i x y h⟩
  · rintro ⟨hR, hS⟩
    exact relLe_iff_powRel.mp (le_intersect (pointRelPow_le hR) (pointRelPow_le hS))
      i x y (powRel_pointRelPow i x y)

/-- `⊚` computes to fibrewise relational composition (the `setRel_comp` argument with
    the fibre index threaded through; the pullback lift enters through the pointed
    family at `i`). -/
theorem powRel_comp (R : BinRel (I → Type u) a b) (S : BinRel (I → Type u) b c)
    (i : I) (x : a i) (z : c i) :
    powRel (R ⊚ S) i x z ↔ ∃ y, powRel R i x y ∧ powRel S i y z := by
  let pb := HasPullbacks.has R.colB S.colA
  let h : pb.cone.pt ⟶ prod a c := pair (pb.cone.π₁ ≫ R.colA) (pb.cone.π₂ ≫ S.colB)
  constructor
  · rintro ⟨t, h1, h2⟩
    -- the concrete fibrewise-image subobject
    let J : Subobject (I → Type u) (prod a c) :=
      ⟨fun j => {w : (prod a c) j // ∃ q, h j q = w}, fun _ p => p.val,
        fun f g hfg => funext fun j => funext fun w =>
          Subtype.ext (congrFun (congrFun hfg j) w)⟩
    obtain ⟨k, hk⟩ := (HasImages.isImage h).2 J ⟨fun j q => ⟨h j q, q, rfl⟩, rfl⟩
    obtain ⟨q, hq⟩ := (k i t).property
    have harr : h i q = (image h).arr i t := hq.trans (congrFun (congrFun hk i) t)
    refine ⟨R.colB i (pb.cone.π₁ i q), ⟨pb.cone.π₁ i q, ?_, rfl⟩,
      ⟨pb.cone.π₂ i q, ?_, ?_⟩⟩
    · exact (congrArg Prod.fst harr).trans h1
    · exact (congrFun (congrFun pb.cone.w i) q).symm
    · exact (congrArg Prod.snd harr).trans h2
  · rintro ⟨y, ⟨r, hr1, hr2⟩, ⟨s, hs1, hs2⟩⟩
    -- lift the matching rows into the pullback, through the pointed family at `i`
    let d : Cone R.colB S.colA :=
      { pt := fun j => ULift.{u} (PLift (i = j))
        π₁ := fun _ p => p.down.down ▸ r
        π₂ := fun _ p => p.down.down ▸ s
        w := funext fun j => funext fun p => by
          obtain ⟨⟨e⟩⟩ := p; cases e; exact hr2.trans hs1.symm }
    let q : pb.cone.pt i := pb.lift d i (ULift.up (PLift.up rfl))
    have hq1 : pb.cone.π₁ i q = r :=
      congrFun (congrFun (pb.lift_fst d) i) (ULift.up (PLift.up rfl))
    have hq2 : pb.cone.π₂ i q = s :=
      congrFun (congrFun (pb.lift_snd d) i) (ULift.up (PLift.up rfl))
    obtain ⟨gI, hgI⟩ := (HasImages.isImage h).1
    have harr : (image h).arr i (gI i q) = h i q := congrFun (congrFun hgI i) q
    refine ⟨gI i q, ?_, ?_⟩
    · calc ((image h).arr i (gI i q)).1 = (h i q).1 := congrArg Prod.fst harr
        _ = R.colA i (pb.cone.π₁ i q) := rfl
        _ = R.colA i r := congrArg (R.colA i) hq1
        _ = x := hr1
    · calc ((image h).arr i (gI i q)).2 = (h i q).2 := congrArg Prod.snd harr
        _ = S.colB i (pb.cone.π₂ i q) := rfl
        _ = S.colB i s := congrArg (S.colB i) hq2
        _ = z := hs2

/-- The Horn sentence at the SPAN level over `Set^I`: the §2.157 element chase runs
    entirely inside each single fibre. -/
theorem desarguesHorn_spanPow {p q a b c : I → Type u}
    (A₁ : BinRel (I → Type u) p a) (A₂ : BinRel (I → Type u) a q)
    (B₁ : BinRel (I → Type u) p b) (B₂ : BinRel (I → Type u) b q)
    (C₁ : BinRel (I → Type u) p c) (C₂ : BinRel (I → Type u) c q)
    (hyp : RelLe ((A₁ ⊚ A₂) ⊓ (B₁ ⊚ B₂)) (C₁ ⊚ C₂)) :
    RelLe ((A₁° ⊚ B₁) ⊓ (A₂ ⊚ B₂°))
      (((A₁° ⊚ C₁) ⊓ (A₂ ⊚ C₂°)) ⊚ ((C₁° ⊚ B₁) ⊓ (C₂ ⊚ B₂°))) := by
  have hyp' : ∀ i (u : p i) (v : q i),
      (∃ x, powRel A₁ i u x ∧ powRel A₂ i x v) ∧
        (∃ y, powRel B₁ i u y ∧ powRel B₂ i y v) →
      ∃ z, powRel C₁ i u z ∧ powRel C₂ i z v := fun i u v ⟨hA, hB⟩ =>
    (powRel_comp C₁ C₂ i u v).mp (relLe_iff_powRel.mp hyp i u v
      ((powRel_inter _ _ i u v).mpr
        ⟨(powRel_comp A₁ A₂ i u v).mpr hA, (powRel_comp B₁ B₂ i u v).mpr hB⟩))
  refine relLe_iff_powRel.mpr fun i x y hxy => ?_
  obtain ⟨h1, h2⟩ := (powRel_inter _ _ i x y).mp hxy
  obtain ⟨u, hu1, hu2⟩ := (powRel_comp _ _ i x y).mp h1
  obtain ⟨v, hv1, hv2⟩ := (powRel_comp _ _ i x y).mp h2
  obtain ⟨z, ⟨⟨u₁, hzu1, hzu2⟩, ⟨v₁, hzv1, hzv2⟩⟩, ⟨u₂, hzu3, hzu4⟩, v₂, hzv3, hzv4⟩ :=
    desarguesHorn_binRel (powRel A₁ i) (powRel A₂ i) (powRel B₁ i) (powRel B₂ i)
      (powRel C₁ i) (powRel C₂ i) (hyp' i) x y
      ⟨⟨u, (powRel_recip A₁ i u x).mp hu1, hu2⟩,
       ⟨v, hv1, (powRel_recip B₂ i y v).mp hv2⟩⟩
  refine (powRel_comp _ _ i x y).mpr ⟨z, (powRel_inter _ _ i x z).mpr ⟨?_, ?_⟩,
    (powRel_inter _ _ i z y).mpr ⟨?_, ?_⟩⟩
  · exact (powRel_comp _ _ i x z).mpr ⟨u₁, (powRel_recip A₁ i u₁ x).mpr hzu1, hzu2⟩
  · exact (powRel_comp _ _ i x z).mpr ⟨v₁, hzv1, (powRel_recip C₂ i z v₁).mpr hzv2⟩
  · exact (powRel_comp _ _ i z y).mpr ⟨u₂, (powRel_recip C₁ i u₂ z).mpr hzu3, hzu4⟩
  · exact (powRel_comp _ _ i z y).mpr ⟨v₂, hzv3, (powRel_recip B₂ i y v₂).mpr hzv4⟩

end RelPowerBridge

/-- **§2.157 for powers** — the Desargues Horn sentence holds in `Rel(Set^I)`
    (the §2.218 representation target) for every index type `I`. -/
theorem desarguesHorn_relObjPower (I : Type u) :
    DesarguesHorn (RelObj (I → Type u)) := by
  intro P Q A B C A₁ A₂ B₁ B₂ C₁ C₂
  refine Quotient.inductionOn₃ A₁ A₂ B₁ (fun A₁ A₂ B₁ => ?_)
  refine Quotient.inductionOn₃ B₂ C₁ C₂ (fun B₂ C₁ C₂ => ?_)
  intro hyp
  rw [← quotLe_iff_algLe] at hyp ⊢
  exact desarguesHorn_spanPow A₁ A₂ B₁ B₂ C₁ C₂ hyp

/-! ## THE HEADLINE (p. 15): the Veblen–Wedderburn allegory is NOT representable

  "the theory of allegories in which Desargues's theorem is false" is consistent —
  and its witness `LMonObj (PElem VW)` cannot be faithfully represented in `Rel(S)`:
  the Horn sentence holds there (`desarguesHorn_relObj`) and would reflect back
  (`desarguesHorn_reflect`), contradicting `VW_not_desarguesHorn`. -/

/-- **§2.157 (p. 15): non-representability.**  There is NO faithful allegory
    representation of the Veblen–Wedderburn allegory in the allegory of relations
    over `Set`.  Horn sentences do not axiomatise the representable allegories. -/
theorem VW_not_representable :
    ¬ ∃ F : AllegoryFunctor (LMonObj (PElem VW)) (RelObj (Type u)), F.Faithful :=
  fun ⟨F, hF⟩ => VW_not_desarguesHorn (desarguesHorn_reflect F hF desarguesHorn_relObj)

/-- **§2.157 (p. 15), power form**: the Veblen–Wedderburn allegory is not faithfully
    representable in ANY power `Rel(Set^I)` — the targets of the §2.218 representation
    theorems (`tabular_repr_in_power_of_sets`).  A REPRESENTATION of an allegory is a
    faithful embedding in a power of `Rel(S)`; `LMonObj (PElem VW)` has none. -/
theorem VW_not_representable_in_power :
    ¬ ∃ (I : Type u) (F : AllegoryFunctor (LMonObj (PElem VW)) (RelObj (I → Type u))),
        F.Faithful :=
  fun ⟨I, F, hF⟩ =>
    VW_not_desarguesHorn (desarguesHorn_reflect F hF (desarguesHorn_relObjPower I))

end Freyd.Alg
