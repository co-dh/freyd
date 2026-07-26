/-
  Freyd & Scedrov, *Categories and Allegories* §1.95–§1.96  Topos theorems.

  §1.951  A topos is EFFECTIVE (every equivalence relation is effective).
  §1.952  A topos is POSITIVE.
  §1.954  A topos has coequalizers.
  §1.955  A topos is bicartesian.
  §1.961  INJECTIVE object; INTERNALLY INJECTIVE; Ω is internally injective.
  §1.962  Ω^A is injective; every object embeds in an injective.
  §1.964  VALUE-BASED category/topos; Ω cogenerates in a value-based topos.
  §1.965  INTERNALLY COGENERATES.
  §1.966  PROGENITOR.
  §1.967  Arbitrary powers ↔ arbitrary copowers ↔ arbitrary copowers of 1 (locally small topos).
  §1.968  Locally small topos: complete ↔ cocomplete.
  §1.969  Lawvere and Tierney definitions of Grothendieck topos.
-/

import Freyd.S1_10
import Freyd.S1_90
import Freyd.S1_51
import Freyd.S1_52
import Freyd.S1_56
import Freyd.S1_58
import Freyd.S1_59
import Freyd.S1_60
import Freyd.S1_62
import Freyd.S1_64
import Freyd.S1_77
import Freyd.S1_82
import Freyd.S1_84
import Freyd.S1_85
import Freyd.S1_91
import Freyd.S1_92
import Freyd.S1_94
import Freyd.S1_967_ToposExists
import Freyd.S1_75
import Freyd.S1_97_ToposDistributive
import Freyd.S1_943_ToposRTC


universe v u

namespace Freyd

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-! ## §1.951  A topos is effective -/

section Effective
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

/-- **§1.951, recovery half (fully proved)**: in a Cartesian category with images,
    if an equivalence relation `E` is the level (kernel pair) of a cover
    `x : A → Q` — i.e. `E ⊂ level x` and `level x ⊂ E` — then `E` is EFFECTIVE.

    This is the *substantive content* of §1.568/§1.951 once the quotient cover is
    available: it packages `E ≅ level x ≅ (graph x) ⊚ (graph x)°` using the two
    bridges above, producing the `IsEffective` data (`Q`, `x`, `Cover x`, and the
    mutual relational containments with `(graph x) ⊚ (graph x)°`).  No `Sorry`. -/
theorem effective_of_quotient_cover {A Q : 𝒞} (E : BinRel 𝒞 A A)
    (hE : EquivalenceRelation E) (x : A ⟶ Q) (hx : Cover x)
    (hElx : RelLe E (kernelPairRel x)) (hlxE : RelLe (kernelPairRel x) E) :
    IsEffective E :=
  ⟨hE, Q, x, hx,
    rel_le_trans hElx (kernelPairRel_le_level x),
    rel_le_trans (graphComp_le_kernelPairRel x) hlxE⟩

/-- **Kernel pair is invariant under post-composition with a monic.**  If `m` is
    monic then `q` and `q ≫ m` have isomorphic kernel pairs as relations: the
    defining equation `a ≫ q = a' ≫ q` is equivalent to `a ≫ (q ≫ m) = a' ≫ (q ≫ m)`
    (monic `m` cancels), so the two kernel-pair lifts are mutually-inverse `RelHom`s.
    This is the bridge from `kernelPairRel (image.lift Λ)` (the quotient cover) to
    `kernelPairRel Λ` (the classifying map), since `Λ = image.lift Λ ≫ (image Λ).arr`
    with `(image Λ).arr` monic. -/
theorem kernelPairRel_postmono {A C D : 𝒞} (q : A ⟶ C) (m : C ⟶ D) (hm : Monic m) :
    RelLe (kernelPairRel q) (kernelPairRel (q ≫ m)) ∧
    RelLe (kernelPairRel (q ≫ m)) (kernelPairRel q) := by
  -- `kp₁(q) ≫ q = kp₂(q) ≫ q` ⟹ `kp₁(q) ≫ (q≫m) = kp₂(q) ≫ (q≫m)`.
  have hfwd : kp₁ (f := q) ≫ (q ≫ m) = kp₂ (f := q) ≫ (q ≫ m) := by
    rw [← Cat.assoc, ← Cat.assoc, kp_sq]
  -- Conversely, `kp₁(q≫m) ≫ q = kp₂(q≫m) ≫ q` via `m` monic.
  have hbwd : kp₁ (f := q ≫ m) ≫ q = kp₂ (f := q ≫ m) ≫ q :=
    hm _ _ (by rw [Cat.assoc, Cat.assoc]; exact kp_sq)
  constructor
  · -- E := kernelPairRel q ⊑ kernelPairRel (q≫m): lift `(kp₁ q, kp₂ q)` into kernelPair (q≫m).
    refine ⟨⟨(HasPullbacks.has (q ≫ m) (q ≫ m)).lift ⟨_, kp₁ (f := q), kp₂ (f := q), hfwd⟩, ?_, ?_⟩⟩
    · exact kp_lift_p₁ _ _ hfwd
    · exact kp_lift_p₂ _ _ hfwd
  · refine ⟨⟨(HasPullbacks.has q q).lift ⟨_, kp₁ (f := q ≫ m), kp₂ (f := q ≫ m), hbwd⟩, ?_, ?_⟩⟩
    · exact kp_lift_p₁ _ _ hbwd
    · exact kp_lift_p₂ _ _ hbwd

end Effective

/-- **§1.951 core (the tabulation identity)**: the classifying map `Λ = powerClassify E`
    of an equivalence relation `E ⊆ A×A` against the universal membership `∈_A` has
    KERNEL PAIR exactly `E`.

    `Λ a = Λ a' ⟺ {x | a E x} = {x | a' E x} ⟺ a E a'` (the last `⟺` uses E's
    reflexivity for `⟸`-class-membership and symmetry+transitivity for the `⟹` collapse).
    Relationally: `E ≅ relPullback Λ ∈_A` (`powerClassify_pullback_iso`), and equality of
    classifying maps is governed by `powerClassify_unique`.

    The proof factors through four steps (below): `classify_eq_of_relPullback_iso`
    (`relPullback a E ≅ relPullback a' E ⟹ a≫Λ = a'≫Λ`, via `powerClassify_natural`
    + `classify_unique`), `composePoint` (a point of `E⊚E` from two consecutive E-points),
    `relPullback_relHom_of_rel` (`a E a' ⟹ {x|aEx} ⊆ {x|a'Ex}` using symmetry+transitivity),
    and `relPullback_iso_of_classify_eq` (the converse bridge).  Direction `E ⊑ level Λ`
    shows `E.colA≫Λ = E.colB≫Λ` then lifts; direction `level Λ ⊑ E` transports the
    reflexivity point `(kp₂,kp₂)` across the `relPullback` iso to `(kp₁,kp₂)`. -/
private theorem classify_eq_of_relPullback_iso [Topos 𝒞] [HasPullbacks 𝒞]
    [∀ C : 𝒞, HasPowerObject C]
    {A W : 𝒞} (E : BinRel 𝒞 A A) {a a' : W ⟶ A}
    (h₁ : RelHom (relPullback a E) (relPullback a' E))
    (h₂ : RelHom (relPullback a' E) (relPullback a E)) :
    a ≫ powerClassify E = a' ≫ powerClassify E := by
  rw [← powerClassify_natural E a, ← powerClassify_natural E a']
  exact HasPowerObject.is_universal.classify_unique W (relPullback a E) _ _
    (HasPowerObject.is_universal.classify_exists W (relPullback a E)).choose_spec
    ⟨relHom_trans h₁
        (HasPowerObject.is_universal.classify_exists W (relPullback a' E)).choose_spec.1,
     relHom_trans (HasPowerObject.is_universal.classify_exists W (relPullback a' E)).choose_spec.2
        h₂⟩

/-- A point of `E ⊚ E` over `(x, z)` from witnesses `x E y` and `y E z`. -/
private theorem composePoint [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {A W : 𝒞} {E : BinRel 𝒞 A A} {x y z : W ⟶ A}
    (u : W ⟶ E.src) (huA : u ≫ E.colA = x) (huB : u ≫ E.colB = y)
    (v : W ⟶ E.src) (hvA : v ≫ E.colA = y) (hvB : v ≫ E.colB = z) :
    ∃ p : W ⟶ (E ⊚ E).src, p ≫ (E ⊚ E).colA = x ∧ p ≫ (E ⊚ E).colB = z := by
  let pb := HasPullbacks.has E.colB E.colA
  have hmid : u ≫ E.colB = v ≫ E.colA := by rw [huB, hvA]
  let q : W ⟶ pb.cone.pt := pb.lift ⟨W, u, v, hmid⟩
  have hq1 : q ≫ pb.cone.π₁ = u := pb.lift_fst _
  have hq2 : q ≫ pb.cone.π₂ = v := pb.lift_snd _
  let sp := pair (pb.cone.π₁ ≫ E.colA) (pb.cone.π₂ ≫ E.colB)
  refine ⟨q ≫ image.lift sp, ?_, ?_⟩
  · show (q ≫ image.lift sp) ≫ ((image sp).arr ≫ fst) = x
    rw [Cat.assoc, ← Cat.assoc (image.lift sp), image.lift_fac]
    show q ≫ pair (pb.cone.π₁ ≫ E.colA) (pb.cone.π₂ ≫ E.colB) ≫ fst = x
    rw [fst_pair, ← Cat.assoc, hq1, huA]
  · show (q ≫ image.lift sp) ≫ ((image sp).arr ≫ snd) = z
    rw [Cat.assoc, ← Cat.assoc (image.lift sp), image.lift_fac]
    show q ≫ pair (pb.cone.π₁ ≫ E.colA) (pb.cone.π₂ ≫ E.colB) ≫ snd = z
    rw [snd_pair, ← Cat.assoc, hq2, hvB]

/-- From `a E a'` and symmetry + transitivity of `E`, `{x | a E x} ⊆ {x | a' E x}`
    (`a' E a E x ⟹ a' E x`). -/
private theorem relPullback_relHom_of_rel [HasBinaryProducts 𝒞] [HasPullbacks 𝒞]
    [HasImages 𝒞] {A W : 𝒞} {E : BinRel 𝒞 A A}
    (hsym : RelHom E (reciprocal E)) (htrans : RelHom (E ⊚ E) E)
    {a a' : W ⟶ A} (t : W ⟶ E.src) (htA : t ≫ E.colA = a) (htB : t ≫ E.colB = a') :
    RelHom (relPullback a E) (relPullback a' E) := by
  obtain ⟨s, hsA, hsB⟩ := hsym
  simp only [reciprocal] at hsA hsB
  obtain ⟨τ, hτA, hτB⟩ := htrans
  let P := HasPullbacks.has a E.colA
  let P' := HasPullbacks.has a' E.colA
  let u : P.cone.pt ⟶ E.src := P.cone.π₁ ≫ t ≫ s
  have huA : u ≫ E.colA = P.cone.π₁ ≫ a' := by
    show (P.cone.π₁ ≫ t ≫ s) ≫ E.colA = P.cone.π₁ ≫ a'
    rw [Cat.assoc, Cat.assoc, hsB, htB]
  have huB : u ≫ E.colB = P.cone.π₁ ≫ a := by
    show (P.cone.π₁ ≫ t ≫ s) ≫ E.colB = P.cone.π₁ ≫ a
    rw [Cat.assoc, Cat.assoc, hsA, htA]
  have hvA : P.cone.π₂ ≫ E.colA = P.cone.π₁ ≫ a := P.cone.w.symm
  obtain ⟨p, hpA, hpB⟩ := composePoint (E := E)
    u huA huB P.cone.π₂ hvA rfl
  let e' : P.cone.pt ⟶ E.src := p ≫ τ
  have he'A : e' ≫ E.colA = P.cone.π₁ ≫ a' := by
    show (p ≫ τ) ≫ E.colA = P.cone.π₁ ≫ a'
    rw [Cat.assoc, hτA, hpA]
  have he'B : e' ≫ E.colB = P.cone.π₂ ≫ E.colB := by
    show (p ≫ τ) ≫ E.colB = P.cone.π₂ ≫ E.colB
    rw [Cat.assoc, hτB, hpB]
  have hsq : P.cone.π₁ ≫ a' = e' ≫ E.colA := he'A.symm
  refine ⟨P'.lift ⟨P.cone.pt, P.cone.π₁, e', hsq⟩, P'.lift_fst _, ?_⟩
  have : P'.lift ⟨P.cone.pt, P.cone.π₁, e', hsq⟩ ≫ P'.cone.π₂ = e' := P'.lift_snd _
  calc P'.lift ⟨P.cone.pt, P.cone.π₁, e', hsq⟩ ≫ (P'.cone.π₂ ≫ E.colB)
      = (P'.lift ⟨P.cone.pt, P.cone.π₁, e', hsq⟩ ≫ P'.cone.π₂) ≫ E.colB := (Cat.assoc _ _ _).symm
    _ = e' ≫ E.colB := by rw [this]
    _ = P.cone.π₂ ≫ E.colB := he'B

/-- Converse bridge: `a ≫ Λ(E) = a' ≫ Λ(E) ⟹ relPullback a E ≅ relPullback a' E`. -/
private theorem relPullback_iso_of_classify_eq [Topos 𝒞] [HasPullbacks 𝒞]
    [∀ C : 𝒞, HasPowerObject C]
    {A W : 𝒞} (E : BinRel 𝒞 A A) {a a' : W ⟶ A}
    (heq : a ≫ powerClassify E = a' ≫ powerClassify E) :
    RelHom (relPullback a E) (relPullback a' E) := by
  have ea : powerClassify (relPullback a E) = a ≫ powerClassify E := powerClassify_natural E a
  have ea' : powerClassify (relPullback a' E) = a' ≫ powerClassify E := powerClassify_natural E a'
  have h1 : RelHom (relPullback a E)
      (relPullback (powerClassify (relPullback a E)) HasPowerObject.mem) :=
    (HasPowerObject.is_universal.classify_exists W (relPullback a E)).choose_spec.1
  have h2 : RelHom (relPullback (powerClassify (relPullback a' E)) HasPowerObject.mem)
      (relPullback a' E) :=
    (HasPowerObject.is_universal.classify_exists W (relPullback a' E)).choose_spec.2
  rw [ea] at h1; rw [ea', ← heq] at h2
  exact relHom_trans h1 h2

theorem kernelPairRel_powerClassify_iso [Topos 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    [∀ C : 𝒞, HasPowerObject C]
    {A : 𝒞} (E : BinRel 𝒞 A A) (hE : EquivalenceRelation E) :
    RelLe E (kernelPairRel (powerClassify E)) ∧
    RelLe (kernelPairRel (powerClassify E)) E := by
  obtain ⟨⟨r, hrA, hrB⟩, ⟨hsym⟩, ⟨htrans⟩⟩ := hE
  let Λ := powerClassify E
  obtain ⟨s, hsA0, hsB0⟩ := id hsym
  simp only [reciprocal] at hsA0 hsB0
  refine ⟨?_, ?_⟩
  · have hfwd : RelHom (relPullback E.colA E) (relPullback E.colB E) :=
      relPullback_relHom_of_rel hsym htrans (Cat.id E.src)
        (by rw [Cat.id_comp]) (by rw [Cat.id_comp])
    have hbwd : RelHom (relPullback E.colB E) (relPullback E.colA E) :=
      relPullback_relHom_of_rel hsym htrans s hsB0 hsA0
    have hΛeq : E.colA ≫ Λ = E.colB ≫ Λ :=
      classify_eq_of_relPullback_iso E hfwd hbwd
    refine ⟨⟨(HasPullbacks.has Λ Λ).lift ⟨E.src, E.colA, E.colB, hΛeq⟩, ?_, ?_⟩⟩
    · exact (HasPullbacks.has Λ Λ).lift_fst _
    · exact (HasPullbacks.has Λ Λ).lift_snd _
  · have hkp : kp₁ (f := Λ) ≫ Λ = kp₂ (f := Λ) ≫ Λ := kp_sq
    have hiso : RelHom (relPullback (kp₂ (f := Λ)) E) (relPullback (kp₁ (f := Λ)) E) :=
      relPullback_iso_of_classify_eq E hkp.symm
    obtain ⟨φ, hφA, hφB⟩ := hiso
    let P₂ := HasPullbacks.has (kp₂ (f := Λ)) E.colA
    let P₁ := HasPullbacks.has (kp₁ (f := Λ)) E.colA
    have hd_sq : Cat.id (kernelPair Λ) ≫ kp₂ (f := Λ) = (kp₂ (f := Λ) ≫ r) ≫ E.colA := by
      rw [Cat.id_comp, Cat.assoc, hrA, Cat.comp_id]
    let d : kernelPair Λ ⟶ P₂.cone.pt :=
      P₂.lift ⟨kernelPair Λ, Cat.id (kernelPair Λ), kp₂ (f := Λ) ≫ r, hd_sq⟩
    have hd1 : d ≫ P₂.cone.π₁ = Cat.id (kernelPair Λ) := P₂.lift_fst _
    have hd2 : d ≫ P₂.cone.π₂ = kp₂ (f := Λ) ≫ r := P₂.lift_snd _
    let g : kernelPair Λ ⟶ P₁.cone.pt := d ≫ φ
    have hg1 : g ≫ P₁.cone.π₁ = Cat.id (kernelPair Λ) := by
      show (d ≫ φ) ≫ P₁.cone.π₁ = Cat.id (kernelPair Λ)
      rw [Cat.assoc]; rw [show φ ≫ P₁.cone.π₁ = P₂.cone.π₁ from hφA, hd1]
    have hgB : g ≫ (P₁.cone.π₂ ≫ E.colB) = kp₂ (f := Λ) := by
      show (d ≫ φ) ≫ (P₁.cone.π₂ ≫ E.colB) = kp₂ (f := Λ)
      rw [Cat.assoc, show φ ≫ (P₁.cone.π₂ ≫ E.colB) = P₂.cone.π₂ ≫ E.colB from hφB,
          ← Cat.assoc, hd2, Cat.assoc, hrB, Cat.comp_id]
    refine ⟨⟨g ≫ P₁.cone.π₂, ?_, ?_⟩⟩
    · show (g ≫ P₁.cone.π₂) ≫ E.colA = kp₁ (f := Λ)
      calc (g ≫ P₁.cone.π₂) ≫ E.colA = g ≫ (P₁.cone.π₂ ≫ E.colA) := Cat.assoc _ _ _
        _ = g ≫ (P₁.cone.π₁ ≫ kp₁ (f := Λ)) := by rw [P₁.cone.w]
        _ = (g ≫ P₁.cone.π₁) ≫ kp₁ (f := Λ) := (Cat.assoc _ _ _).symm
        _ = kp₁ (f := Λ) := by rw [hg1, Cat.id_comp]
    · show (g ≫ P₁.cone.π₂) ≫ E.colB = kp₂ (f := Λ)
      rw [Cat.assoc]; exact hgB

/-- **§1.951**: A topos is effective: every equivalence relation on any object is
    the level of some cover (i.e., is effective in the sense of §1.568).

    Freyd's route (the power-object construction): an equivalence relation
    `E ⊆ A×A` is tabulated; the quotient `A/E` is obtained as the image of the
    classifying / characteristic map `A → Ω^A` (singleton `Δ₁` composed with the
    quotient that names `E`-classes), and `q : A ↠ A/E` is a cover whose level
    (kernel pair) is exactly `E`.  Granting that quotient cover,
    `effective_of_quotient_cover` discharges effectiveness completely.

    **Sharpened blocker (faithful Sorry — (1)+(2) now CLOSED, (3) remains).**
    Building the `EffectiveRegular` instance from bare `[Topos 𝒞]` needs THREE
    ingredients.  As of the regularity-refactor, the regular core (1)+(2) is DONE; the
    irreducible residual is the per-relation quotient cover (3):

      (1) `HasImages 𝒞` — NOW AVAILABLE (`InternalForallTopos.toposHasImages`):
          `image f = ⋂{B' ↣ B | f factors through B'}` built via the internal-∀
          family-glb `bigInter`, bypassing the §1.54 capitalization route entirely.

      (2) `PullbacksTransferCovers 𝒞` — NOW AVAILABLE
          (`SlicePi.toposPullbacksTransferCovers`, from the §1.931 dependent-product
          right adjoint).  With (1)+(2), `RegularCategory 𝒞` assembles
          (`topos_is_regular`, S1_94, now Sorry-free).

      (3) THE QUOTIENT COVER — for each equivalence relation `E`, a cover
          `q : A ↠ A/E` with `level q ≅ E`.  This is Freyd's power-object construction
          `A → [A]`: `q` is the IMAGE of the classifying map and one must prove its
          level (kernel pair) is exactly `E`.  Power objects are bundled in `Topos`
          and `HasImages` is now present, so `q` can be FORMED — but proving
          `level q ≅ E` (the `(hElx, hlxE)` containments) is a SEPARATE relation-algebra
          construction (the tabulation/quotient argument of §1.951), NOT supplied by
          regularity.  No such per-relation witness exists in the repo yet.

    `EffectiveRegular extends RegularCategory`; that super-field is now discharged, but
    the `effective` field still needs (3) for every `E`.  Once (3) is built, this is
    `⟨…, fun E hE => effective_of_quotient_cover E hE q hq hElq hlqE⟩` with
    `(q, hq, hElq, hlqE)` the quotient cover.  The recovery half (the relation-algebra
    identity `E ≅ level q ≅ (graph q)⊚(graph q)°`) is PROVED above
    (`effective_of_quotient_cover`); the residual gap is exactly the quotient-cover
    existence (3), now the SOLE blocker (the §1.54-blocked (1)–(2) are gone).  Out of
    scope for the regularity wiring.

    **(3) NOW CONSTRUCTED.**  The quotient cover is
    `q := image.lift (powerClassify E) : A ↠ (image (powerClassify E)).dom = A/E`,
    a cover by `image_lift_cover`.  Its level is `E` because
    `kernelPairRel q ≅ kernelPairRel (powerClassify E)` (`kernelPairRel_postmono`,
    `(image Λ).arr` monic) and `kernelPairRel (powerClassify E) ≅ E`
    (`kernelPairRel_powerClassify_iso`: classifying map of an equivalence relation has
    kernel pair = the relation, via reflexivity for one direction and
    symmetry+transitivity for the other).  Then `effective_of_quotient_cover` finishes. -/
noncomputable instance topos_is_effective [Topos 𝒞] : EffectiveRegular 𝒞 := by
  classical
  -- Build `RegularCategory` directly from the ambient topos instances (`toposHasImages`,
  -- `SlicePi.toposPullbacksTransferCovers`, …) rather than `Classical.choice (topos_is_regular)`,
  -- so its product/pullback/image fields stay SYNTACTICALLY the topos instances — otherwise the
  -- `effective` field's `EquivalenceRelation E` (stated via `toRegularCategory`) and the topos
  -- `powerClassify`/`kernelPairRel` below resolve different-but-defeq instances (a diamond).
  refine { (inferInstance : RegularCategory 𝒞) with effective := ?_ }
  intro A E hE
  -- The quotient cover: image factorization of the classifying map `Λ = powerClassify E`.
  let Λ := powerClassify E
  let q := image.lift Λ
  have hqcov : Cover q := image_lift_cover Λ
  have hpm := kernelPairRel_postmono q (image Λ).arr (image Λ).monic
  have hfac : q ≫ (image Λ).arr = Λ := image.lift_fac Λ
  rw [hfac] at hpm
  obtain ⟨hΛE_le, hEΛ_le⟩ := kernelPairRel_powerClassify_iso (𝒞 := 𝒞) E hE
  exact effective_of_quotient_cover E hE q hqcov
    (rel_le_trans hΛE_le hpm.2) (rel_le_trans hpm.1 hEΛ_le)

/-! ## §1.952  A topos is positive -/

/-- **§1.952**: A topos is positive: it has binary coproducts A + B.
    `A + B` is the subobject `union (image inlRaw)(image inrRaw) ⊆ [A] × [B]`, with
    `inlRaw a = ({a},∅)`, `inrRaw b = (∅,{b})`.

    Most of the construction is now DELIVERED Sorry-free in `Freyd/ToposExists.lean`
    (GOAL 3), the frame law `invImage_preserves_union` having unblocked the union layer:
      * CARRIER + EMBEDDING       — `coprodSub`, `coprodObj`, `coprodArr` (monic).
      * INJECTIONS                — `coprodInl`, `coprodInr`, with `coprodInl_arr`/
                                    `coprodInr_arr` and `coprodInl_monic`/`coprodInr_monic`.
      * `case_uniq` (jointly epi) — `coprod_jointly_epi` (equalizer + `union_min`, FULL).
      * PARTIAL-MAP DATA          — `casePMf`/`casePMg` + their classify β-squares, via the
                                    lawful PMC `partialMapClassifier_exists`
                                    (`Freyd/PartialMapClassifier.lean`, Sorry-free).

    The SINGLE remaining piece is the copairing existence

        case_morphism_exists {A B X} (f : A ⟶ X) (g : B ⟶ X) :
          ∃ c, coprodInl A B ≫ c = f ∧ coprodInr A B ≫ c = g

    — Freyd's §1.935 amalgamation: GLUE `f,g` into one map out of `A+B`.  This is NOT
    reducible to the join-lattice/PMC data already present, because a subobject JOIN
    (`union`) carries only a map-IN universal property (`union_left/right/min`), never a
    map-OUT (colimit) one, and the PMC only certifies TOTALITY of a candidate `χ : A+B→X̃`,
    not its existence.  Producing `χ = χf ∨ χg` as a single total map needs the
    DISJOINTNESS `image inl ⊓ image inr = ⊥` (a singleton is not the empty subobject — a
    non-degeneracy fact) plus the union-cover, i.e. the value-object amalgamation.  See the
    RESIDUAL note in `Freyd/ToposExists.lean` for the exact stuck step.

    Because `HasBinaryCoproducts` is all-or-nothing (carrier + lawful `case`/`case_uniq`),
    no honest partial instance can be supplied without faking `case`.  Once
    `case_morphism_exists` lands, `case := …choose`, the β-laws are `…choose_spec`,
    `case_uniq := coprod_jointly_epi`, assembling
    `toposHasBinaryCoproducts : HasBinaryCoproducts 𝒞`, after which this becomes
    `exact toposHasBinaryCoproducts`. -/
noncomputable instance topos_is_positive [Topos 𝒞] : HasBinaryCoproducts 𝒞 :=
  toposHasBinaryCoproducts

/-! ## §1.954  A topos has coequalizers -/

section Coequalizers
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]

/-! The §1.77↔§1.56 equivalence-relation bridge `equivalenceRelation_of_isEquivRel`
    and the §1.954 core reduction `minEquiv_of_rtc` (every endo-relation has a minimal
    equivalence relation containing it, via the closure `(R ∪ R° ∪ 1)*`) live canonically
    in `Freyd.S1_64` (lower in the import hierarchy); reused here via import (DRY). -/

end Coequalizers

/-- **§1.954, substantive reduction (no `Sorry`)**: a PRE-TOPOS that has
    reflexive-transitive closures has coequalizers.

    Construction: from `[HasReflTransClosure 𝒞]`, `minEquiv_of_rtc` gives
    `HasMinEquivContaining` (the equivalence closure `(R ∪ R° ∪ 1)*` is the minimal
    equivalence containing `R`); then `preTopos_minEquiv_to_cocartesian` (§1.657)
    builds coequalizers via the *effective-regular* route — the minimal equivalence
    `S` containing `R = «f,g»` is the level of a cover `q : B ↠ C` (effectiveness,
    §1.951), and `q` is the coequalizer of `f, g`.  No `Sorry`. -/
noncomputable def preTopos_rtc_has_coequalizers [inst : PreTopos 𝒞]
    [hRtc : @HasReflTransClosure 𝒞 _ PreTopos.toPositivePreLogos.toHasBinaryProducts
      PreTopos.toPositivePreLogos.toHasPullbacks PreTopos.toPositivePreLogos.toHasImages] :
    HasCoequalizers 𝒞 :=
  -- The `HasReflTransClosure` hypothesis is stated over the *canonical*
  -- `PreTopos → PositivePreLogos` products, the same instance
  -- `preTopos_minEquiv_to_cocartesian` resolves with.  (Pinned to avoid the
  -- `topos_has_exponentials` products instance that `[PreTopos]` also makes
  -- available — defeq, but not syntactically equal, which derails instance-implicit
  -- unification.)
  Classical.choice (preTopos_minEquiv_to_cocartesian
    (@minEquiv_of_rtc 𝒞 _
      PreTopos.toPositivePreLogos.toHasBinaryProducts
      PreTopos.toPositivePreLogos.toHasPullbacks PreTopos.toPositivePreLogos.toHasImages
      PreTopos.toPositivePreLogos.toPreLogos.toHasSubobjectUnions hRtc))

/-- **§1.954**: A topos has coequalizers.
    Given f, g : A → B, let R = f"g, S = (R ∪ R")* (the equivalence closure).
    A topos is effective [1.951], so S is the level of some B → C.
    This B → C is the coequalizer of f and g.

    The *substantive content* is fully discharged in `preTopos_rtc_has_coequalizers`
    (no `Sorry`): once `[PreTopos 𝒞]` (= effective-regular + positive pre-logos) and
    `[HasReflTransClosure 𝒞]` are available, the equivalence-closure construction
    `(R ∪ R° ∪ 1)*` (now constructive via `rtc`) plus §1.657/§1.951 yield
    coequalizers.

    **Sharpened blocker (faithful Sorry — effectiveness now CLOSED).**  Of the two
    ingredients `preTopos_rtc_has_coequalizers` needs, (1) is now DONE and only (2) remains:

      (1) `PreTopos 𝒞` = `EffectiveRegular 𝒞` + `PositivePreLogos 𝒞` — NOW ASSEMBLABLE.
          `topos_is_effective` (above) is SORRY-FREE (axioms `[propext, Classical.choice]`);
          its `EffectiveRegular 𝒞` resolves by `inferInstance`.  `PositivePreLogos` =
          `PreLogos` (`toposPreLogos`) + `HasBinaryCoproducts` (`topos_is_positive`,
          Sorry-free), both in scope.  (Not registered as a global `PreTopos 𝒞` instance
          here to avoid the documented `PreLogos`/`PreTopos` instance diamond, S1_64.)

      (2) `HasReflTransClosure 𝒞` — STILL the sole blocker.  There is no `topos_has_rtc`
          instance: a topos's reflexive-transitive closures `R*` are the §1.943 family-glb
          `⋂{S | S reflexive-transitive, R ⊑ S}` over a subobject family of `[B×B]`, whose
          EXISTENCE rests on §1.54's `capitalization_lemma` glb-construction (the genuine
          §1.543 residual; see `topos_has_rtc` in S1_94 which carries it as a hypothesis).
          The closure-ASSEMBLY (`rtc`/reflexivity/`rtc_transitive`/`rtc_minimal`) is
          Sorry-free; only the glb *instance* for a bare topos is missing.

    With a `HasReflTransClosure 𝒞` instance, this is literally
    `preTopos_rtc_has_coequalizers`.  The effectiveness half of the §1.951↔§1.954 bridge
    is no longer the gap. -/
noncomputable instance topos_has_coequalizers [Topos 𝒞] : HasCoequalizers 𝒞 := by
  -- Assemble `PreTopos 𝒞` from the (now all Sorry-free) topos exactness instances, then
  -- apply `preTopos_rtc_has_coequalizers` with the `toposHasReflTransClosure` instance
  -- (Freyd.ToposRTC) supplying the reflexive-transitive closures.
  letI hER : EffectiveRegular 𝒞 := topos_is_effective
  letI hPL : PreLogos 𝒞 := toposPreLogos
  letI hBC : HasBinaryCoproducts 𝒞 := topos_is_positive
  letI hPPL : PositivePreLogos 𝒞 := { }
  letI hPT : PreTopos 𝒞 := { }
  exact preTopos_rtc_has_coequalizers

/-! ## §1.955  A topos is bicartesian -/

/-- **§1.955**: A topos is bicartesian: `CartesianCategory` + `HasCoterminator` +
    `HasBinaryCoproducts` + `HasCoequalizers`.

    Three of the four parents are Sorry-free under `[Topos 𝒞]`: Cartesian (terminal +
    products, native), `HasCoterminator` (`topos_has_strict_coterminator`, §1.944), and
    `HasBinaryCoproducts` (`topos_is_positive`, §1.952).  The SOLE residual is
    `HasCoequalizers 𝒞` (`topos_has_coequalizers` above), itself blocked only on the
    `HasReflTransClosure 𝒞` glb-existence instance (§1.54).  Once that lands, this is
    `{ (inferInstance : CartesianCategory 𝒞), … with }`. -/
noncomputable instance topos_is_bicartesian [Topos 𝒞] : BicartesianCategory 𝒞 := by
  letI hCot : HasCoterminator 𝒞 := Classical.choice topos_has_coterminator
  letI hEq : HasEqualizers 𝒞 := products_pullbacks_implies_equalizers
  letI hCart : CartesianCategory 𝒞 := { }
  exact { hCart, hCot,
          (topos_is_positive : HasBinaryCoproducts 𝒞),
          (topos_has_coequalizers : HasCoequalizers 𝒞) with }

/-! ## §1.961  Injective objects -/

/-- **§1.961**: An object E is INJECTIVE if the functor (-, E) carries monics to epics.
    Elementary version (in a pre-topos, pushouts of monics are monic):
    E is injective iff every monic E ↣ A has a right-inverse. -/
def IsInjective [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞] (E : 𝒞) : Prop :=
  ∀ {A B : 𝒞} (f : A ⟶ B), Monic f →
    ∀ (g : A ⟶ E), ∃ (h : B ⟶ E), f ≫ h = g

/-- The composite of two monics is monic (§1.41). -/
private theorem mono_comp {X Y Z : 𝒞} {m : X ⟶ Y} {n : Y ⟶ Z}
    (hm : Monic m) (hn : Monic n) : Monic (m ≫ n) := by
  intro W u v huv
  exact hm _ _ (hn _ _ (by simpa [Cat.assoc] using huv))

/-- **§1.961**: Ω is INJECTIVE in a topos.  Given a monic `f : A ↣ B` and any
    `g : A → Ω`, classify the subobject `m : S ↣ A` that `g` names, then classify
    its composite `m ≫ f : S ↣ B` to obtain `h : B → Ω`.  Because `f` is monic the
    pullback of the subobject `m ≫ f` along `f` is `m` itself, so `f ≫ h` classifies
    `m`; by uniqueness of characteristic maps `f ≫ h = g`.  (This is the elementary
    form of "Ω is injective": maps into Ω extend along monics via `classify`.) -/
theorem omega_is_injective [Topos 𝒞] :
    IsInjective (𝒞 := 𝒞) (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := by
  intro A B f hf g
  -- m : S ↣ A is the subobject named by g (pullback of `true` along g).
  let cone := (HasPullbacks.has g (HasSubobjectClassifier.true (𝒞 := 𝒞))).cone
  let m : cone.pt ⟶ A := cone.π₁
  have hm : Monic m := by
    -- m is monic: it is the pullback of the monic `true` along g.  The other leg
    -- `cone.π₂` lands in the terminal `one`, so cones over (g, true) are determined
    -- by their first leg; joint pullback uniqueness then forces u = v.
    intro W u v huv
    have hpb := (HasPullbacks.has g (HasSubobjectClassifier.true (𝒞 := 𝒞))).cone_isPullback
    have hwu : (u ≫ m) ≫ g = (u ≫ cone.π₂) ≫ HasSubobjectClassifier.true := by
      rw [Cat.assoc, Cat.assoc, cone.w]
    obtain ⟨_, _, huniq⟩ := hpb ⟨W, u ≫ m, u ≫ cone.π₂, hwu⟩
    rw [huniq u rfl rfl, huniq v huv.symm (term_uniq _ _)]
  -- g classifies m.
  have hsq_m : m ≫ g = term cone.pt ≫ HasSubobjectClassifier.true :=
    cone.w.trans (congrArg (· ≫ HasSubobjectClassifier.true) (term_uniq cone.π₂ (term cone.pt)))
  have hg : g = HasSubobjectClassifier.classify m hm :=
    HasSubobjectClassifier.classify_unique m hm g hsq_m (by
      -- the chosen cone is a pullback; replace its π₂ by `term` (terminal uniqueness)
      have hpb := (HasPullbacks.has g (HasSubobjectClassifier.true (𝒞 := 𝒞))).cone_isPullback
      intro d
      obtain ⟨u, ⟨hu₁, _⟩, huniq⟩ := hpb d
      exact ⟨u, ⟨hu₁, term_uniq _ _⟩, fun w hw₁ _ => huniq w hw₁ (term_uniq _ _)⟩)
  -- h = classify(m ≫ f).
  refine ⟨HasSubobjectClassifier.classify (m ≫ f) (mono_comp hm hf), ?_⟩
  -- f ≫ h classifies m, hence f ≫ h = classify m = g.
  refine Eq.trans ?_ hg.symm
  -- m ≫ (f ≫ classify(m≫f)) = term ≫ true
  have hsq_fh : m ≫ (f ≫ HasSubobjectClassifier.classify (m ≫ f) (mono_comp hm hf))
      = term cone.pt ≫ HasSubobjectClassifier.true := by
    rw [← Cat.assoc, HasSubobjectClassifier.classify_sq (m ≫ f) (mono_comp hm hf)]
  refine HasSubobjectClassifier.classify_unique m hm _ hsq_fh ?_
  -- (S, m, term) is a pullback of (f ≫ classify(m≫f), true)
  · intro d
    -- d.π₁ : d.pt → A with d.π₁ ≫ (f ≫ classify(m≫f)) = d.π₂ ≫ true
    have hsq : (d.π₁ ≫ f) ≫ HasSubobjectClassifier.classify (m ≫ f) (mono_comp hm hf)
        = d.π₂ ≫ HasSubobjectClassifier.true := by rw [Cat.assoc]; exact d.w
    have hpb := HasSubobjectClassifier.classify_pullback (m ≫ f) (mono_comp hm hf)
    obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := hpb ⟨d.pt, d.π₁ ≫ f, d.π₂, hsq⟩
    -- u ≫ (m≫f) = d.π₁ ≫ f.  f monic ⟹ u ≫ m = d.π₁.
    have hum : u ≫ m = d.π₁ := hf _ _ (by rw [Cat.assoc]; exact hu₁)
    refine ⟨u, ⟨hum, term_uniq _ _⟩, ?_⟩
    intro v hv₁ _
    exact huniq v (by rw [← Cat.assoc, hv₁]) (term_uniq _ _)

/-- The map f × 1_Z : A × Z → B × Z for f : A → B (mapping the left factor). -/
def prodMapLeft [HasBinaryProducts 𝒞] {A B : 𝒞} (Z : 𝒞) (f : A ⟶ B) : prod A Z ⟶ prod B Z :=
  pair (fst ≫ f) snd

/-- The contravariant exponential map E^f : E^^B → E^^A induced by f : A → B
    (§1.853).  Defined by curry(e_B ∘ (f × 1_{E^^B})), where
    e_B : B × E^^B → E is evaluation and (f × 1) : A × E^^B → B × E^^B. -/
def expMap [HasExponentials 𝒞] {A B : 𝒞} (E : 𝒞) (f : A ⟶ B) : E ^^ B ⟶ E ^^ A :=
  -- (f × 1_{E^^B}) : prod A (E^^B) → prod B (E^^B)  (left-factor map)
  -- eval_exp B E   : prod B (E^^B) → E
  curry (prodMapLeft (E ^^ B) f ≫ eval_exp B E)

/-- **§1.961**: An object E in an exponential category is INTERNALLY INJECTIVE if
    E^(−) carries monics to epics: for every monic f : A ↣ B,
    the induced map E^f : E^^B → E^^A is a cover (= epic in a regular category). -/
def IsInternallyInjective [HasExponentials 𝒞] (E : 𝒞) : Prop :=
  ∀ {A B : 𝒞} (f : A ⟶ B), Monic f → Cover (expMap E f)


/-- **DRY bridge (§1.92 ↔ §1.961)**: the §1.961 contravariant exponential action
    `expMap Ω f` on the classifier coincides with the §1.922 power-functor map
    `omegaPowContra.map f = Ω^f`.  Both are `curry (pair (fst ≫ f) snd ≫ eval)`,
    so the equality is definitional (`rfl`).  Lets §1.961 reuse the proved
    contravariant-functoriality (`map_id`, `map_comp`) of `omegaPowContra`. -/
theorem expMap_omega_eq_omegaPow [Topos 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    expMap (𝒞 := 𝒞) (HasSubobjectClassifier.omega (𝒞 := 𝒞)) f
      = (omegaPowContra (𝒞 := 𝒞)).map f := rfl

/-- **Pullback is monotone under relation-iso.**  Pulling two `RelHom`-isomorphic
    relations `R ≅ S : BinRel P C` back along a common `g : X → P` gives isomorphic
    pullbacks: `relPullback g R ≅ relPullback g S` (both directions).  This is the
    reusable form of the inline span-lift that appears in `univClassify_natural`
    (S1_92): a witness `w : R.src → S.src` lifts the pullback cone `(π₁, π₂ ≫ w)`. -/
theorem relPullback_relHom [HasPullbacks 𝒞] {P C X : 𝒞} (g : X ⟶ P)
    {R S : BinRel 𝒞 P C} (h : RelHom R S ∧ RelHom S R) :
    RelHom (relPullback g R) (relPullback g S) ∧
    RelHom (relPullback g S) (relPullback g R) := by
  constructor
  · obtain ⟨w, hwA, hwB⟩ := h.1
    let P₀ := HasPullbacks.has g R.colA
    let P₁ := HasPullbacks.has g S.colA
    refine ⟨P₁.lift ⟨P₀.cone.pt, P₀.cone.π₁, P₀.cone.π₂ ≫ w, ?_⟩, ?_, ?_⟩
    · show P₀.cone.π₁ ≫ g = (P₀.cone.π₂ ≫ w) ≫ S.colA
      rw [Cat.assoc, hwA]; exact P₀.cone.w
    · show _ ≫ (relPullback g S).colA = (relPullback g R).colA
      exact P₁.lift_fst _
    · show _ ≫ (P₁.cone.π₂ ≫ S.colB) = P₀.cone.π₂ ≫ R.colB
      rw [← Cat.assoc, P₁.lift_snd, Cat.assoc, hwB]
  · obtain ⟨w, hwA, hwB⟩ := h.2
    let P₀ := HasPullbacks.has g R.colA
    let P₁ := HasPullbacks.has g S.colA
    refine ⟨P₀.lift ⟨P₁.cone.pt, P₁.cone.π₁, P₁.cone.π₂ ≫ w, ?_⟩, ?_, ?_⟩
    · show P₁.cone.π₁ ≫ g = (P₁.cone.π₂ ≫ w) ≫ R.colA
      rw [Cat.assoc, hwA]; exact P₁.cone.w
    · exact P₀.lift_fst _
    · show _ ≫ (P₀.cone.π₂ ≫ R.colB) = P₁.cone.π₂ ≫ S.colB
      rw [← Cat.assoc, P₀.lift_snd, Cat.assoc, hwB]

section OmegaInjective
variable [Topos 𝒞]

/-- **Monic kernel-pair collapse:** `graph x ⊚ (graph x)° ⊆ 1_A` for monic `x`.
    (Local copy of `S1_62.graph_comp_recip_le_one_of_mono`, whose only obstacle is the
    stale file-level `variable [PreLogos 𝒞]`; the proof needs only `Simple` of `(graph x)°`,
    i.e. `tabulated_is_simple_iff_left_monic`, and a topos has `[HasImages]`.) -/
theorem graph_recip_collapse_mono {A B : 𝒞} (x : A ⟶ B) (hx : Monic x) :
    RelLe (graph x ⊚ (graph x)°) (graph (Cat.id A)) := by
  have hp : MonicPair (x : A ⟶ B) (Cat.id A) := by
    intro W u v _ hid; simpa [Cat.comp_id] using hid
  have hsimp : Simple (BinRel.mk A x (Cat.id A) hp) :=
    (tabulated_is_simple_iff_left_monic x (Cat.id A) hp).mpr hx
  have heq : BinRel.mk A x (Cat.id A) hp = (graph x)° := rfl
  rw [heq] at hsimp
  unfold Simple at hsimp
  rw [reciprocal_invol] at hsimp
  exact hsimp

/-- The DIRECT IMAGE `f" : Ω^A → Ω^B` for `f : A → B`, defined at the exponential level
    `Ω^A = exp A Ω` directly (NOT transported from power objects).  It is the universal
    classifier of the composite membership relation `evalRel A ⊚ graph f : BinRel (Ω^A) B`
    (= `{(T, b) | ∃ a ∈ T, f a = b}`) against the universal `evalRel B` on `Ω^B`. -/
noncomputable def directImageOmega {A B : 𝒞} (f : A ⟶ B) :
    exp A (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ⟶
    exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞)) :=
  univClassify (evalRel_universal B) (evalRel A ⊚ graph f)

/-- The inverse-image relation cut out by `expMap Ω f` is the reciprocal-graph composite:
    `classRel(prodMapLeft f ≫ eval_B) ≅ evalRel B ⊚ (graph f)°`, i.e. `{(S,a) | f a ∈ S}`.

    Both directions of `RelHom`.  Membership: `classRel χ = {(S,a) | eval(f a, S) = ⊤}`
    and `evalRel B ⊚ (graph f)° = {(S,a) | ∃ b, b ∈ S ∧ f a = b}`; the existential over `b`
    is forced to `b = f a`, so the two relations coincide. -/
theorem classRel_eq_recip_graph {A B : 𝒞} (f : A ⟶ B) :
    RelHom (classRel (prodMapLeft (exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞))) f
              ≫ eval_exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞))))
           (evalRel B ⊚ (graph f)°) ∧
    RelHom (evalRel B ⊚ (graph f)°)
           (classRel (prodMapLeft (exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞))) f
              ≫ eval_exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞)))) := by
  let Ω := HasSubobjectClassifier.omega (𝒞 := 𝒞)
  let χ : prod A (exp B Ω) ⟶ Ω := prodMapLeft (exp B Ω) f ≫ eval_exp B Ω
  -- pullbacks underlying the two sides
  let pbχ := HasPullbacks.has χ HasSubobjectClassifier.true              -- src of `classRel χ`
  let pbE := HasPullbacks.has (eval_exp B Ω) HasSubobjectClassifier.true -- src of `evalRel B`
  -- composite `evalRel B ⊚ (graph f)°`: image of `span` over `pb = pullback(evalRel.colB, f)`.
  let pb := HasPullbacks.has (evalRel B).colB ((graph f)°).colA
  let span : pb.cone.pt ⟶ prod (exp B Ω) A :=
    pair (pb.cone.π₁ ≫ (evalRel B).colA) (pb.cone.π₂ ≫ ((graph f)°).colB)
  -- `prodMapLeft` factor laws (`pair (fst≫f) snd`).
  have hpmf : prodMapLeft (exp B Ω) f ≫ fst = fst ≫ f := fst_pair _ _
  have hpms : prodMapLeft (exp B Ω) f ≫ snd = snd := snd_pair _ _
  -- column unfoldings (definitional).
  have hcaA : (classRel χ).colA = pbχ.cone.π₁ ≫ snd := rfl
  have hcaB : (classRel χ).colB = pbχ.cone.π₁ ≫ fst := rfl
  have heA  : (evalRel B).colA = pbE.cone.π₁ ≫ snd := rfl
  have heB  : (evalRel B).colB = pbE.cone.π₁ ≫ fst := rfl
  have hgA  : ((graph f)°).colA = f := rfl
  have hgB  : ((graph f)°).colB = Cat.id A := rfl
  constructor
  · -- FORWARD: build a witness `pbχ.pt → (image span).dom` directly.
    -- `m = pbχ.π₁ ≫ (f×1) : pbχ.pt → prod B (exp B Ω)` lands on the eval-`true` square.
    let m : pbχ.cone.pt ⟶ prod B (exp B Ω) := pbχ.cone.π₁ ≫ prodMapLeft (exp B Ω) f
    have hmev : m ≫ eval_exp B Ω = term pbχ.cone.pt ≫ HasSubobjectClassifier.true := by
      show (pbχ.cone.π₁ ≫ prodMapLeft (exp B Ω) f) ≫ eval_exp B Ω = _
      rw [Cat.assoc]
      show pbχ.cone.π₁ ≫ χ = _
      rw [pbχ.cone.w, term_uniq pbχ.cone.π₂ (term pbχ.cone.pt)]
    let e : pbχ.cone.pt ⟶ pbE.cone.pt := pbE.lift ⟨pbχ.cone.pt, m, term pbχ.cone.pt, hmev⟩
    have he₁ : e ≫ pbE.cone.π₁ = m := pbE.lift_fst _
    -- `e ≫ evalRel.colB = (classRel χ.colB) ≫ f`, lifting into `pb`.
    have hePbB : e ≫ (evalRel B).colB = (classRel χ).colB ≫ ((graph f)°).colA := by
      rw [heB, hgA, hcaB, ← Cat.assoc, he₁]
      show (pbχ.cone.π₁ ≫ prodMapLeft (exp B Ω) f) ≫ fst = _
      rw [Cat.assoc, hpmf, ← Cat.assoc]
    let t : pbχ.cone.pt ⟶ pb.cone.pt :=
      pb.lift ⟨pbχ.cone.pt, e, (classRel χ).colB, hePbB⟩
    have ht₁ : t ≫ pb.cone.π₁ = e := pb.lift_fst _
    have ht₂ : t ≫ pb.cone.π₂ = (classRel χ).colB := pb.lift_snd _
    refine ⟨t ≫ image.lift span, ?_, ?_⟩
    · -- colA: `e ≫ evalRel.colA = pbχ.π₁ ≫ snd`.
      show (t ≫ image.lift span) ≫ ((image span).arr ≫ fst) = (classRel χ).colA
      rw [← Cat.assoc, Cat.assoc t, image.lift_fac]
      show (t ≫ span) ≫ fst = _
      rw [Cat.assoc]
      show t ≫ pair (pb.cone.π₁ ≫ (evalRel B).colA) (pb.cone.π₂ ≫ ((graph f)°).colB) ≫ fst = _
      rw [fst_pair, ← Cat.assoc, ht₁, heA, ← Cat.assoc, he₁, hcaA]
      show (pbχ.cone.π₁ ≫ prodMapLeft (exp B Ω) f) ≫ snd = _
      rw [Cat.assoc, hpms]
    · -- colB: `t ≫ pb.π₂ = pbχ.π₁ ≫ fst`.
      show (t ≫ image.lift span) ≫ ((image span).arr ≫ snd) = (classRel χ).colB
      rw [← Cat.assoc, Cat.assoc t, image.lift_fac]
      show (t ≫ span) ≫ snd = _
      rw [Cat.assoc]
      show t ≫ pair (pb.cone.π₁ ≫ (evalRel B).colA) (pb.cone.π₂ ≫ ((graph f)°).colB) ≫ snd = _
      rw [snd_pair, ← Cat.assoc, ht₂]
      show (classRel χ).colB ≫ ((graph f)°).colB = _
      rw [hgB, Cat.comp_id]
  · -- BACKWARD: descend through the image-cover `image.lift span`.
    -- `n = ⟨a, S⟩ : pb.pt → prod A (exp B Ω)` from `pb.π₂ = a` and `pb.π₁ ≫ pbE.π₁ ≫ snd = S`.
    let n : pb.cone.pt ⟶ prod A (exp B Ω) :=
      pair (pb.cone.π₂) (pb.cone.π₁ ≫ pbE.cone.π₁ ≫ snd)
    have hnf : n ≫ fst = pb.cone.π₂ := fst_pair _ _
    have hns : n ≫ snd = pb.cone.π₁ ≫ pbE.cone.π₁ ≫ snd := snd_pair _ _
    -- `pb`-square: `pb.π₁ ≫ evalRel.colB = pb.π₂ ≫ f`, i.e. `pb.π₁ ≫ pbE.π₁ ≫ fst = pb.π₂ ≫ f`.
    have hpbw : pb.cone.π₁ ≫ pbE.cone.π₁ ≫ fst = pb.cone.π₂ ≫ f := pb.cone.w
    -- `n ≫ (f×1) = pb.π₁ ≫ pbE.π₁`, so `n ≫ χ = pb.π₁ ≫ pbE.π₁ ≫ eval = term ≫ true`.
    have hnpm : n ≫ prodMapLeft (exp B Ω) f = pb.cone.π₁ ≫ pbE.cone.π₁ := by
      have e1 : (n ≫ prodMapLeft (exp B Ω) f) ≫ fst = (pb.cone.π₁ ≫ pbE.cone.π₁) ≫ fst := by
        rw [Cat.assoc, hpmf, ← Cat.assoc, hnf, Cat.assoc, ← hpbw]
      have e2 : (n ≫ prodMapLeft (exp B Ω) f) ≫ snd = (pb.cone.π₁ ≫ pbE.cone.π₁) ≫ snd := by
        rw [Cat.assoc, hpms, hns, Cat.assoc]
      exact (pair_uniq _ _ _ e1 e2).trans (pair_uniq _ _ _ rfl rfl).symm
    have hnχ : n ≫ χ = term pb.cone.pt ≫ HasSubobjectClassifier.true := by
      show n ≫ (prodMapLeft (exp B Ω) f ≫ eval_exp B Ω) = _
      rw [← Cat.assoc, hnpm, Cat.assoc, pbE.cone.w, term_uniq pbE.cone.π₂ (term pbE.cone.pt),
        ← Cat.assoc, term_uniq (pb.cone.π₁ ≫ term pbE.cone.pt) (term pb.cone.pt)]
    let φ : pb.cone.pt ⟶ pbχ.cone.pt := pbχ.lift ⟨pb.cone.pt, n, term pb.cone.pt, hnχ⟩
    have hφ₁ : φ ≫ pbχ.cone.π₁ = n := pbχ.lift_fst _
    refine relLe_of_cover_factor (image.lift span) (image_lift_cover span) φ ?_ ?_ |>.elim id
    · -- `φ ≫ classRel.colA = image.lift span ≫ (evalRel B ⊚ (graph f)°).colA`.
      have hrhs : image.lift span ≫ (evalRel B ⊚ (graph f)°).colA
          = pb.cone.π₁ ≫ (evalRel B).colA := by
        show image.lift span ≫ ((image span).arr ≫ fst) = _
        rw [← Cat.assoc, image.lift_fac]
        show pair (pb.cone.π₁ ≫ (evalRel B).colA) (pb.cone.π₂ ≫ ((graph f)°).colB) ≫ fst = _
        exact fst_pair _ _
      rw [hrhs, heA, hcaA, ← Cat.assoc, hφ₁, hns]
    · -- `φ ≫ classRel.colB = image.lift span ≫ (evalRel B ⊚ (graph f)°).colB`.
      have hrhs : image.lift span ≫ (evalRel B ⊚ (graph f)°).colB
          = pb.cone.π₂ ≫ ((graph f)°).colB := by
        show image.lift span ≫ ((image span).arr ≫ snd) = _
        rw [← Cat.assoc, image.lift_fac]
        show pair (pb.cone.π₁ ≫ (evalRel B).colA) (pb.cone.π₂ ≫ ((graph f)°).colB) ≫ snd = _
        exact snd_pair _ _
      rw [hcaB, ← Cat.assoc, hφ₁, hnf, hrhs]
      show _ = pb.cone.π₂ ≫ ((graph f)°).colB
      rw [hgB]; exact (Cat.comp_id _).symm

/-- **The monic direct-image unit `f" ≫ f* = 1`** (Freyd §1.961).  For monic `f`, the
    direct image `directImageOmega f` is a section of the inverse-image power map
    `expMap Ω f`.  The relational chain (all `RelHom`-iso, justified inline) is:
    `relPullback (f" ≫ f*) (evalRel A) ≅ relPullback f" (classRel χ)`
      `≅ relPullback f" (evalRel B ⊚ (graph f)°)`
      `≅ (relPullback f" (evalRel B)) ⊚ (graph f)°`   (`relPullback_compose_dist`)
      `≅ (evalRel A ⊚ graph f) ⊚ (graph f)°`           (`univClassify_spec`)
      `≅ evalRel A ⊚ (graph f ⊚ (graph f)°)`           (`compose_assoc`)
      `≅ evalRel A ⊚ graph 1_A ≅ evalRel A`.            (`f` monic ⟹ kernel pair collapses)
    By `evalRel`-universality (`classify_unique`), `f" ≫ f* = 1`. -/
theorem directImageOmega_unit {A B : 𝒞} (f : A ⟶ B) (hf : Monic f) :
    directImageOmega f ≫ expMap _ f = Cat.id _ := by
  classical
  letI : RegularCategory 𝒞 := Classical.choice (topos_is_regular_real (𝒞 := 𝒞))
  let Ω := HasSubobjectClassifier.omega (𝒞 := 𝒞)
  let s := directImageOmega f
  -- `χ`: the inverse-image classifier; `expMap Ω f = curry χ` definitionally.
  let χ : prod A (exp B Ω) ⟶ Ω := prodMapLeft (exp B Ω) f ≫ eval_exp B Ω
  have hexp : expMap Ω f = curry χ := rfl
  -- Universality of `evalRel A`: it suffices to show both `s ≫ expMap Ω f` and `1`
  -- classify `evalRel A` against `evalRel A`.
  refine (evalRel_universal A).classify_unique (exp A Ω) (evalRel A) (s ≫ expMap Ω f)
    (Cat.id _) ?_ ?_
  · -- `relPullback (s ≫ expMap Ω f) (evalRel A) ≅ evalRel A`.
    -- (1) relPullback_comp: split the composite pullback.
    have h1 : RelHom (relPullback (s ≫ expMap Ω f) (evalRel A))
                (relPullback s (relPullback (expMap Ω f) (evalRel A))) ∧
              RelHom (relPullback s (relPullback (expMap Ω f) (evalRel A)))
                (relPullback (s ≫ expMap Ω f) (evalRel A)) :=
      ⟨(relPullback_comp s (expMap Ω f) (evalRel A)).2,
       (relPullback_comp s (expMap Ω f) (evalRel A)).1⟩
    -- (2) relPullback (expMap Ω f) (evalRel A) ≅ classRel χ  (β-law bridge).
    have h2 : RelHom (relPullback (expMap Ω f) (evalRel A)) (classRel χ) ∧
              RelHom (classRel χ) (relPullback (expMap Ω f) (evalRel A)) := by
      rw [hexp]; exact ⟨evalRel_pull_bwd χ, evalRel_pull_fwd χ⟩
    -- (3) classRel χ ≅ evalRel B ⊚ (graph f)°.
    have h3 := classRel_eq_recip_graph f
    -- (4) pull (2)∘(3) back along s.
    have h23 : RelHom (relPullback (expMap Ω f) (evalRel A)) (evalRel B ⊚ (graph f)°) ∧
               RelHom (evalRel B ⊚ (graph f)°) (relPullback (expMap Ω f) (evalRel A)) :=
      ⟨RelHom_trans h2.1 h3.1, RelHom_trans h3.2 h2.2⟩
    have h4 := relPullback_relHom s h23
    -- (5) relPullback_compose_dist: relPullback s (evalRel B ⊚ (graph f)°)
    --       ≅ (relPullback s (evalRel B)) ⊚ (graph f)°.
    have h5 := relPullback_compose_dist s (evalRel B) ((graph f)°)
    -- (6) univClassify_spec: relPullback s (evalRel B) ≅ evalRel A ⊚ graph f.
    have h6 : RelHom (relPullback s (evalRel B)) (evalRel A ⊚ graph f) ∧
              RelHom (evalRel A ⊚ graph f) (relPullback s (evalRel B)) :=
      ⟨(univClassify_spec (evalRel_universal B) (evalRel A ⊚ graph f)).2,
       (univClassify_spec (evalRel_universal B) (evalRel A ⊚ graph f)).1⟩
    -- (7) ⊚-monotone in left arg: (relPullback s (evalRel B)) ⊚ (graph f)°
    --       ≅ (evalRel A ⊚ graph f) ⊚ (graph f)°.
    have h7 : RelHom ((relPullback s (evalRel B)) ⊚ ((graph f)°))
                ((evalRel A ⊚ graph f) ⊚ ((graph f)°)) ∧
              RelHom ((evalRel A ⊚ graph f) ⊚ ((graph f)°))
                ((relPullback s (evalRel B)) ⊚ ((graph f)°)) :=
      ⟨(compose_le ⟨h6.1⟩ (rel_le_refl _)).elim id,
       (compose_le ⟨h6.2⟩ (rel_le_refl _)).elim id⟩
    -- (8) associativity: (evalRel A ⊚ graph f) ⊚ (graph f)° ≅ evalRel A ⊚ (graph f ⊚ (graph f)°).
    have h8 : RelHom ((evalRel A ⊚ graph f) ⊚ ((graph f)°))
                (evalRel A ⊚ (graph f ⊚ ((graph f)°))) ∧
              RelHom (evalRel A ⊚ (graph f ⊚ ((graph f)°)))
                ((evalRel A ⊚ graph f) ⊚ ((graph f)°)) :=
      ⟨(compose_assoc_of_regular (evalRel A) (graph f) ((graph f)°)).1.elim id,
       (compose_assoc_of_regular (evalRel A) (graph f) ((graph f)°)).2.elim id⟩
    -- (9) f monic ⟹ graph f ⊚ (graph f)° ≅ graph 1_A (kernel-pair collapse + entirety).
    have h9 : RelHom (graph f ⊚ ((graph f)°)) (graph (Cat.id A)) ∧
              RelHom (graph (Cat.id A)) (graph f ⊚ ((graph f)°)) :=
      ⟨(graph_recip_collapse_mono f hf).elim id, (graph_is_map f).1.elim id⟩
    have h9' : RelHom (evalRel A ⊚ (graph f ⊚ ((graph f)°))) (evalRel A ⊚ graph (Cat.id A)) ∧
               RelHom (evalRel A ⊚ graph (Cat.id A)) (evalRel A ⊚ (graph f ⊚ ((graph f)°))) :=
      ⟨(compose_le (rel_le_refl _) ⟨h9.1⟩).elim id, (compose_le (rel_le_refl _) ⟨h9.2⟩).elim id⟩
    -- (10) R ⊚ graph 1 ≅ R.
    have h10 : RelHom (evalRel A ⊚ graph (Cat.id A)) (evalRel A) ∧
               RelHom (evalRel A) (evalRel A ⊚ graph (Cat.id A)) :=
      ⟨(comp_graph_id (evalRel A)).elim id, (comp_graph_id_right (evalRel A)).elim id⟩
    -- `classify_unique` wants `(RelHom R (relPullback _ U) ∧ RelHom (relPullback _ U) R)`,
    -- i.e. first BACKWARD (evalRel A → relPullback), then FORWARD.
    refine ⟨?_, ?_⟩
    · exact RelHom_trans h10.2 (RelHom_trans h9'.2 (RelHom_trans h8.2 (RelHom_trans h7.2
        (RelHom_trans h5.2 (RelHom_trans h4.2 h1.2)))))
    · exact RelHom_trans h1.1 (RelHom_trans h4.1 (RelHom_trans h5.1 (RelHom_trans h7.1
        (RelHom_trans h8.1 (RelHom_trans h9'.1 h10.1)))))
  · -- `relPullback (1) (evalRel A) ≅ evalRel A`.
    exact ⟨(relPullback_id (evalRel A)).2, (relPullback_id (evalRel A)).1⟩

end OmegaInjective

/-- **§1.961**: In a topos, Ω is internally injective.  CLOSED, Sorry-free
    ([propext, Classical.choice]).

    Freyd's proof: for monic `f : A ↣ B`, the contravariant action `Ω^f = expMap Ω f`
    is the inverse-image `f*`, and it has a LEFT INVERSE — the covariant direct image
    `f"` — because `f` monic gives the unit identity `f" ≫ f* = 1` (`f"` is a section of
    `f*`).  A split epi is a cover (`cover_of_section`), so `Ω^f` is a cover.

    **Proof (load-bearing).**  `cover_of_section (expMap Ω f) s hs` reduces the goal to a
    section `s : Ω^A → Ω^B` of `expMap Ω f` with `s ≫ Ω^f = 1`.  We build `s` and the unit
    DIRECTLY at the exponential level, NOT transported from power objects:

    * `directImageOmega f := univClassify (evalRel_universal B) (evalRel A ⊚ graph f)` — the
      direct image, classifying the composite membership relation `{(T,b) | ∃ a∈T, f a = b}`
      against the universal `evalRel B` on `Ω^B`.  (`evalRel A` is the universal membership
      `BinRel (Ω^A) A`, Sorry-free; `exp A Ω ≅ [A]` is no longer needed.)

    * `directImageOmega_unit` proves `f" ≫ f* = 1` for monic `f` by `evalRel A`-universality
      (`classify_unique`): it suffices that `relPullback (f" ≫ f*) (evalRel A) ≅ evalRel A`.
      The relational chain (each step a `RelHom`-iso) is
        `relPullback (f"≫f*) (evalRel A)`
          `≅ relPullback f" (relPullback f* (evalRel A))`        (`relPullback_comp`)
          `≅ relPullback f" (classRel χ)`                        (`evalRel_pull`, `f* = curry χ`)
          `≅ relPullback f" (evalRel B ⊚ (graph f)°)`            (`classRel_eq_recip_graph`)
          `≅ (relPullback f" (evalRel B)) ⊚ (graph f)°`          (`relPullback_compose_dist`)
          `≅ (evalRel A ⊚ graph f) ⊚ (graph f)°`                 (`univClassify_spec`)
          `≅ evalRel A ⊚ (graph f ⊚ (graph f)°)`                 (`compose_assoc_of_regular`)
          `≅ evalRel A ⊚ graph 1_A ≅ evalRel A`.                 (`graph_recip_collapse_mono`,
                                                                   `graph_is_map`, `comp_graph_id`)
      Monicity of `f` enters at the single step `graph f ⊚ (graph f)° ≅ graph 1_A` (kernel
      pair of a monic collapses; `graph_recip_collapse_mono` ⊆ and entirety `graph_is_map` ⊇).
      Everything rests on `relPullback_compose_dist` (S1_92), proven Sorry-free on master. -/
theorem omega_is_internally_injective [Topos 𝒞] :
    IsInternallyInjective (𝒞 := 𝒞) (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := by
  intro A B f hf
  classical
  letI : RegularCategory 𝒞 := Classical.choice (topos_is_regular_real (𝒞 := 𝒞))
  -- Reduce to the genuine residual: a section `s : Ω^A → Ω^B` of the inverse-image map
  -- `Ω^f = expMap Ω f`.  The section is Freyd's direct image `f"`; the cover step then
  -- follows from `cover_of_section`.
  obtain ⟨s, hs⟩ :
      ∃ s : (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ^^ A
              ⟶ (HasSubobjectClassifier.omega (𝒞 := 𝒞)) ^^ B,
        s ≫ expMap _ f = Cat.id _ := by
    exact ⟨directImageOmega f, directImageOmega_unit f hf⟩
  intro C m g hm hgm
  exact cover_of_section (expMap _ f) s hs m g hm hgm

/-! ## §1.962  Ω^A is injective; every object embeds in an injective -/

/-- The right-factor product map `A × f : A × X → A × Y` is monic when `f` is.
    (Joint cancellation on `fst`/`snd`; `f` monic kills the `snd` component.) -/
private theorem prodMap_mono [HasBinaryProducts 𝒞] (A : 𝒞) {X Y : 𝒞} {f : X ⟶ Y}
    (hf : Monic f) : Monic (prodMap A X Y f) := by
  intro W u v huv
  -- u ≫ fst = v ≫ fst (from prodMap_fst) and u ≫ snd = v ≫ snd (f monic via prodMap_snd).
  have hfst : u ≫ fst = v ≫ fst := by
    have := congrArg (· ≫ fst (A := A) (B := Y)) huv
    simpa [Cat.assoc, prodMap_fst] using this
  have hsnd : u ≫ snd = v ≫ snd := by
    apply hf
    have := congrArg (· ≫ snd (A := A) (B := Y)) huv
    simpa [Cat.assoc, prodMap_snd] using this
  -- Both agree on fst and snd ⟹ equal (product extensionality).
  calc u = pair (u ≫ fst) (u ≫ snd) := pair_uniq _ _ u rfl rfl
    _ = pair (v ≫ fst) (v ≫ snd) := by rw [hfst, hsnd]
    _ = v := (pair_uniq _ _ v rfl rfl).symm

/-- **§1.962**: If E is injective in an exponential category, then E^A is injective
    for any A.  Proof: (−, E^A) ≅ (− × A, E) and − × A preserves monics in any category.
    Concretely: given a monic `f : X ↣ Y` and `g : X → E^A`, transp `g` to
    `ĝ : A×X → E`; the map `A×f : A×X ↣ A×Y` is monic, so by injectivity of E it
    extends to `k : A×Y → E` with `(A×f) ≫ k = ĝ`; then `h = curry k` satisfies
    `f ≫ h = g` by transpose naturality. -/
theorem exp_of_injective_is_injective [HasExponentials 𝒞] [HasPullbacks 𝒞] [HasImages 𝒞]
    {E : 𝒞} (hE : IsInjective E) (A : 𝒞) : IsInjective (E ^^ A) := by
  intro X Y f hf g
  -- ĝ : A × X → E is the uncurried g; by construction g = curry ĝ.
  let ghat : prod A X ⟶ E := prodMap A X (E ^^ A) g ≫ eval_exp A E
  have hg : g = curry ghat := curry_unique_eq rfl
  -- Extend ĝ along the monic A × f using injectivity of E.
  obtain ⟨k, hk⟩ := hE (prodMap A X Y f) (prodMap_mono A hf) ghat
  -- h = curry k.  Then f ≫ h = curry (A×f ≫ k) = curry ĝ = g.
  refine ⟨curry k, ?_⟩
  rw [curry_precomp, hk, ← hg]

/-- **§1.962**: Consequently, in a topos, Ω^A is injective for all A.
    Since the singleton map embeds A into Ω^A, every object appears as a subobject
    of an injective. -/
theorem topos_every_object_embeds_in_injective [Topos 𝒞] (A : 𝒞) :
    ∃ (I : 𝒞) (m : A ⟶ I), Monic m ∧ IsInjective (𝒞 := 𝒞) I :=
  -- I = Ω^A = [A]; the singleton map Δ₁ : A ↣ [A] is monic (§1.92); [A] is injective
  -- because Ω is injective (`omega_is_injective`) and exponentials of injectives are
  -- injective (`exp_of_injective_is_injective`).
  ⟨HasSubobjectClassifier.omega (𝒞 := 𝒞) ^^ A, singletonMapCat A,
    singletonMapCat_monic A,
    exp_of_injective_is_injective omega_is_injective A⟩

/-! ## §1.964  Value-based categories -/

/-- **§1.964**: A category is VALUE-BASED if its values (= morphisms from subterminators)
    form a basis (§1.632): the class of objects of the form U (for U ≤ 1) generates
    in the sense that the representable functors {(U, −)} for subterminators U are
    collectively faithful. -/
def IsValueBased [HasTerminal 𝒞] : Prop :=
  IsGeneratingSet (𝒞 := 𝒞) (fun G => ∃ (m : G ⟶ one), Monic m)

/-- **§1.964**: In a value-based topos, Ω is a cogenerator: for any f ≠ g : A → B,
    there exists h : B → Ω such that f ≫ h ≠ g ≫ h.

    Freyd's route is `(−, Ω) = χ?(−)` plus `B' = Im(xf)` for a subterminator value
    `x : U → A` with `xf ≠ xg`.  Under this repo's *bare* `[Topos 𝒞]` that route is
    not directly available (it needs `HasImages` / image-of-`xf`, both blocked on the
    §1.54 capitalization lemma; cf. `topos_is_effective`).  We give an equivalent
    proof needing only the classifier:

    A value `x : U → A` out of a subterminator `U` (`Monic (term U)`) makes ANY map out
    of `U` monic — any two maps INTO `U` agree (`term`-uniqueness + `term U` monic).  So
    `x ≫ f : U ↣ B` is itself monic; take `h := χ(x ≫ f)`.  Then `(x≫f)≫h = term≫true`,
    and the no-separation hypothesis forces `(x≫g)≫h = term≫true` too.  `monic_is_equalizer`
    (§1.913) factors `x≫g = k ≫ (x≫f)` with `k : U → U`; subterminal collapse gives `k = id`,
    so `x≫g = x≫f`.  This holds for every subterminator value, so `IsValueBased` forces
    `f = g`, contradicting `f ≠ g`.  (Sorry-free; axioms: propext, choice, Quot.sound.) -/
theorem omega_cogenerates_in_value_based_topos [Topos 𝒞] (hVB : IsValueBased (𝒞 := 𝒞)) :
    ∀ {A B : 𝒞} (f g : A ⟶ B), f ≠ g →
      ∃ (h : B ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞)), f ≫ h ≠ g ≫ h := by
  intro A B f g hfg
  -- Contrapositive: if NO `h` separates, then `f = g`, contradicting `f ≠ g`.
  apply Classical.byContradiction; intro hcon'
  -- `hcon' : ¬ ∃ h, f ≫ h ≠ g ≫ h`, i.e. every `h` fails to separate.
  have hcon : ∀ h : B ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞), f ≫ h = g ≫ h := fun h =>
    Classical.byContradiction (fun hne => hcon' ⟨h, hne⟩)
  apply hfg
  -- `hVB` reduces `f = g` to: every value `x : U → A` from a subterminator `U`
  -- has `x ≫ f = x ≫ g`.
  refine hVB f g (fun U hU x => ?_)
  obtain ⟨mU, hmU⟩ := hU
  -- A map OUT of a subterminator is monic: any two maps into `U` already agree
  -- (their composites with `term U` agree by terminal uniqueness, and `term U` is
  -- monic), so `x ≫ f` is monic with subterminal domain.
  have hsub : ∀ {Z : 𝒞} (a b : Z ⟶ U), a = b := fun a b => hmU a b (term_uniq _ _)
  have hm : Monic (x ≫ f) := fun a b _ => hsub a b
  -- Take `h := χ(x ≫ f)` (the classifier of the monic `x ≫ f : U ↣ B`).
  let h : B ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) := HasSubobjectClassifier.classify (x ≫ f) hm
  -- `x ≫ f` factors through itself, so `(x ≫ f) ≫ h = term U ≫ true`.
  have hf_sq : (x ≫ f) ≫ h = term U ≫ HasSubobjectClassifier.true :=
    HasSubobjectClassifier.classify_sq (x ≫ f) hm
  -- From the contradiction hypothesis `f ≫ h = g ≫ h`, also `(x ≫ g) ≫ h = term U ≫ true`.
  have hg_sq : (x ≫ g) ≫ h = term U ≫ HasSubobjectClassifier.true := by
    calc (x ≫ g) ≫ h = x ≫ (g ≫ h) := Cat.assoc _ _ _
      _ = x ≫ (f ≫ h) := by rw [hcon h]
      _ = (x ≫ f) ≫ h := (Cat.assoc _ _ _).symm
      _ = term U ≫ HasSubobjectClassifier.true := hf_sq
  -- `monic_is_equalizer` turns `(x ≫ g) ≫ χ = (x ≫ g) ≫ (term ≫ true)` into a
  -- factorization `k ≫ (x ≫ f) = x ≫ g`.
  obtain ⟨_, huniv⟩ := monic_is_equalizer (x ≫ f) hm
  obtain ⟨k, hk, _⟩ := huniv (x ≫ g) (by
    rw [hg_sq, ← Cat.assoc]
    exact congrArg (· ≫ HasSubobjectClassifier.true) (term_uniq (term U) ((x ≫ g) ≫ term B)))
  -- `k : U → U` equals `id U` (subterminal), hence `x ≫ g = x ≫ f`.
  calc x ≫ f = Cat.id U ≫ (x ≫ f) := (Cat.id_comp _).symm
    _ = k ≫ (x ≫ f) := by rw [hsub (Cat.id U) k]
    _ = x ≫ g := hk

/-! ## §1.965  Internally cogenerates -/

/-- **§1.965**: An object C in an exponential category INTERNALLY COGENERATES if
    the functor C^(−) is a contravariant embedding: the maps C^f for varying f
    together distinguish morphisms.  Formally: for f ≠ g : A → B, C^f ≠ C^g. -/
def InternallyCogenerates [HasExponentials 𝒞] (C : 𝒞) : Prop :=
  ∀ {A B : 𝒞} (f g : A ⟶ B), expMap C f = expMap C g → f = g

/-- **§1.965**: A cogenerator internally cogenerates.
    If C cogenerates (i.e., (−, C) is an embedding) then C^(−) is also an embedding:
    for f ≠ g, T(C^f) ≠ T(C^g), hence C^f ≠ C^g. -/
theorem cogenerator_internally_cogenerates [HasExponentials 𝒞] [HasTerminal 𝒞]
    (C : 𝒞)
    (hcog : ∀ {A B : 𝒞} (f g : A ⟶ B), f ≠ g →
      ∃ (h : B ⟶ C), f ≫ h ≠ g ≫ h) :
    InternallyCogenerates C := by
  intro A B f g heq
  apply Classical.byContradiction; intro hne
  obtain ⟨h, hh⟩ := hcog f g hne
  -- expMap C f = expMap C g; curry_inj gives the uncurried identity.
  have hunc : prodMapLeft (C ^^ B) f ≫ eval_exp B C =
              prodMapLeft (C ^^ B) g ≫ eval_exp B C := curry_inj heq
  -- Let s := pair fstA (sndA ≫ curry(fstB ≫ h)) : prod A one → prod A (C^^B).
  -- Key: s ≫ prodMapLeft(k) ≫ eval_exp B C = fstA ≫ k ≫ h for any k : A → B.
  have heval_A : ∀ (k : A ⟶ B),
      pair (fst (A := A) (B := one)) (snd (A := A) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) ≫
        prodMapLeft (C ^^ B) k ≫ eval_exp B C =
      fst (A := A) (B := one) ≫ k ≫ h := by
    intro k
    -- s ≫ prodMapLeft(k) = pair(fstA≫k)(sndA≫curry(fstB≫h))
    have step1 : pair (fst (A := A) (B := one)) (snd (A := A) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) ≫
        prodMapLeft (C ^^ B) k =
      pair (fst (A := A) (B := one) ≫ k) (snd (A := A) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) :=
      pair_uniq _ _ _
        (by rw [Cat.assoc, prodMapLeft, fst_pair, ← Cat.assoc, fst_pair])
        (by rw [Cat.assoc, prodMapLeft, snd_pair, snd_pair])
    -- pair(fstA≫k)(sndA≫t) = pair(fstA≫k) sndAone ≫ pair fstBone (sndBone≫t), via prod B one
    have hfactor : pair (fst (A := A) (B := one) ≫ k) (snd (A := A) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) =
        (pair (fst (A := A) (B := one) ≫ k) (snd (A := A) (B := one)) : prod A one ⟶ prod B one) ≫
        pair (fst (A := B) (B := one)) (snd (A := B) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) :=
      (pair_uniq _ _ _
        (by rw [Cat.assoc, fst_pair, fst_pair])
        (by rw [Cat.assoc, snd_pair, ← Cat.assoc, snd_pair])).symm
    calc pair (fst (A := A) (B := one)) (snd (A := A) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) ≫
            prodMapLeft (C ^^ B) k ≫ eval_exp B C
        = pair (fst (A := A) (B := one) ≫ k) (snd (A := A) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) ≫
            eval_exp B C := by rw [← Cat.assoc, step1]
      _ = (pair (fst (A := A) (B := one) ≫ k) (snd (A := A) (B := one)) : prod A one ⟶ prod B one) ≫
            pair (fst (A := B) (B := one)) (snd (A := B) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) ≫
            eval_exp B C := by rw [hfactor, Cat.assoc]
      _ = (pair (fst (A := A) (B := one) ≫ k) (snd (A := A) (B := one)) : prod A one ⟶ prod B one) ≫
            (fst (A := B) (B := one) ≫ h) := by congr 1; exact curry_eval_eq _
      _ = fst (A := A) (B := one) ≫ k ≫ h := by rw [← Cat.assoc, fst_pair, Cat.assoc]
  -- Precompose hunc with s to get fstA ≫ f ≫ h = fstA ≫ g ≫ h.
  have heqh : fst (A := A) (B := one) ≫ f ≫ h = fst (A := A) (B := one) ≫ g ≫ h := by
    rw [← heval_A f, ← heval_A g]
    exact congrArg (pair (fst (A := A) (B := one)) (snd (A := A) (B := one) ≫ curry (fst (A := B) (B := one) ≫ h)) ≫ ·) hunc
  -- Cancel fstA via its right-inverse prodOneRightInv A, concluding f ≫ h = g ≫ h.
  exact hh (by
    have := congrArg (prodOneRightInv A ≫ ·) heqh
    simp only [← Cat.assoc, show prodOneRightInv A ≫ fst = Cat.id A from fst_pair _ _,
      Cat.id_comp] at this
    exact this)

/-- **The inverse-image relation `expMap Ω f` cuts out is `evalRel B ⊚ (graph f)°`.**
    Pulling the universal membership `evalRel A` (on `Ω^A`) back along the contravariant
    `expMap Ω f = curry χ` (`χ = (f×1) ≫ eval_B`) gives `classRel χ ≅ evalRel B ⊚ (graph f)°`
    (`evalRel_pull_*` + `classRel_eq_recip_graph`).  This is the `exp`-level "inverse image
    detects membership of `f a`" identity, both `RelHom` directions. -/
theorem relPullback_expMap_eq_recip_graph [Topos 𝒞] {A B : 𝒞} (f : A ⟶ B) :
    RelHom (relPullback (expMap (HasSubobjectClassifier.omega (𝒞 := 𝒞)) f) (evalRel A))
           (evalRel B ⊚ (graph f)°) ∧
    RelHom (evalRel B ⊚ (graph f)°)
           (relPullback (expMap (HasSubobjectClassifier.omega (𝒞 := 𝒞)) f) (evalRel A)) := by
  let Ω := HasSubobjectClassifier.omega (𝒞 := 𝒞)
  let χ : prod A (exp B Ω) ⟶ Ω := prodMapLeft (exp B Ω) f ≫ eval_exp B Ω
  have hexp : expMap Ω f = curry χ := rfl
  -- `relPullback (curry χ) (evalRel A) ≅ classRel χ ≅ evalRel B ⊚ (graph f)°`.
  have h2 : RelHom (relPullback (expMap Ω f) (evalRel A)) (classRel χ) ∧
            RelHom (classRel χ) (relPullback (expMap Ω f) (evalRel A)) := by
    rw [hexp]; exact ⟨evalRel_pull_bwd χ, evalRel_pull_fwd χ⟩
  have h3 := classRel_eq_recip_graph f
  exact ⟨RelHom_trans h2.1 h3.1, RelHom_trans h3.2 h2.2⟩

/-- **Membership pulled back along the singleton is the diagonal.**  Pulling the
    universal membership `evalRel B` (on `Ω^B`) back along the singleton `Δ₁ = singletonMapCat B`
    gives the diagonal `graph(1_B)`: `{(b,b') | b' ∈ {b}} = {(b,b') | b' = b}`.  This is the
    `hLHS` content of `singletonMapCat_eq_powExp`, isolated as a reusable lemma. -/
theorem relPullback_singleton_evalRel [Topos 𝒞] (B : 𝒞) :
    RelHom (graph (Cat.id B)) (relPullback (singletonMapCat B) (evalRel B)) ∧
    RelHom (relPullback (singletonMapCat B) (evalRel B)) (graph (Cat.id B)) := by
  let χΔ := HasSubobjectClassifier.classify (diag B) (diag_mono B)
  -- `relMonic (graph 1_B) = diag B` defeq, so `classRel (classify (relMonic (graph 1_B))) = classRel χΔ`.
  have hcr : RelHom (graph (Cat.id B)) (classRel χΔ) ∧ RelHom (classRel χΔ) (graph (Cat.id B)) :=
    classRel_roundtrip (graph (Cat.id B))
  -- `singletonMapCat B = curry χΔ` defeq, so `relPullback (singletonMapCat B) (evalRel B)
  --   = relPullback (curry χΔ) (evalRel B) ≅ classRel χΔ`.
  exact ⟨RelHom_trans hcr.1 (evalRel_pull_fwd χΔ),
         RelHom_trans (evalRel_pull_bwd χΔ) hcr.2⟩

/-- **§1.965**: In a topos, Ω internally cogenerates — `Ω^(−)` is a FAITHFUL contravariant
    functor.  (NOTE: Ω is *not* a cogenerator in a general topos; internal cogeneration is
    strictly weaker and holds directly, with no §1.543 capitalization.)

    Proof (membership calculus, Sorry-free on master infra).  Set `φ_f := Δ₁ ≫ Ω^f : B → Ω^A`
    (`Δ₁ = singletonMapCat B`).  We compute `relPullback φ_f (evalRel A) ≅ (graph f)°`, naming
    `(graph f)°` against the universal `evalRel A`:
      `relPullback φ_f (evalRel A)`
        `≅ relPullback Δ₁ (relPullback (Ω^f) (evalRel A))`   (`relPullback_comp`)
        `≅ relPullback Δ₁ (evalRel B ⊚ (graph f)°)`          (`relPullback_expMap_eq_recip_graph`)
        `≅ (relPullback Δ₁ (evalRel B)) ⊚ (graph f)°`        (`relPullback_compose_dist`)
        `≅ graph(1_B) ⊚ (graph f)°`                          (`relPullback_singleton_evalRel`)
        `≅ (graph f)°`.                                       (`graph_id_comp`/`comp_graph_id_left`)
    Now `Ω^f = Ω^g ⟹ φ_f = φ_g ⟹ relPullback φ_f (evalRel A) = relPullback φ_g (evalRel A)`
    (`congrArg`), so `(graph f)° ≅ (graph g)°`; a `RelHom (graph f)° → (graph g)°` gives a
    witness `w` with `w ≫ id = id` and `w ≫ g = f`, hence `w = id` and `f = g`. -/
theorem omega_internally_cogenerates [Topos 𝒞] : InternallyCogenerates (𝒞 := 𝒞) (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := by
  classical
  letI : RegularCategory 𝒞 := Classical.choice (topos_is_regular_real (𝒞 := 𝒞))
  intro A B f g heq
  let Ω := HasSubobjectClassifier.omega (𝒞 := 𝒞)
  -- `φ_h := Δ₁(B) ≫ Ω^h : B → Ω^A`, and the relation it names is `(graph h)°`.
  have hnames : ∀ h : A ⟶ B,
      RelHom (relPullback (singletonMapCat B ≫ expMap Ω h) (evalRel A)) ((graph h)°) ∧
      RelHom ((graph h)°) (relPullback (singletonMapCat B ≫ expMap Ω h) (evalRel A)) := by
    intro h
    -- (1) split `relPullback (Δ₁ ≫ Ω^h) (evalRel A)`.
    obtain ⟨hc1, hc2⟩ := relPullback_comp (singletonMapCat B) (expMap Ω h) (evalRel A)
    -- (2) `relPullback (Ω^h) (evalRel A) ≅ evalRel B ⊚ (graph h)°`, pulled back along Δ₁.
    have h23 := relPullback_relHom (singletonMapCat B) (relPullback_expMap_eq_recip_graph h)
    -- (3) distribute the pullback over the composite.
    have hdist := relPullback_compose_dist (singletonMapCat B) (evalRel B) ((graph h)°)
    -- (4) `relPullback Δ₁ (evalRel B) ≅ graph(1_B)`, monotone in the left ⊚-arg.
    have hsing := relPullback_singleton_evalRel B
    have h4 : RelHom ((relPullback (singletonMapCat B) (evalRel B)) ⊚ ((graph h)°))
                (graph (Cat.id B) ⊚ ((graph h)°)) ∧
              RelHom (graph (Cat.id B) ⊚ ((graph h)°))
                ((relPullback (singletonMapCat B) (evalRel B)) ⊚ ((graph h)°)) :=
      ⟨(compose_le ⟨hsing.2⟩ (rel_le_refl _)).elim id,
       (compose_le ⟨hsing.1⟩ (rel_le_refl _)).elim id⟩
    -- (5) `graph(1_B) ⊚ (graph h)° ≅ (graph h)°`.
    have h5 : RelHom (graph (Cat.id B) ⊚ ((graph h)°)) ((graph h)°) ∧
              RelHom ((graph h)°) (graph (Cat.id B) ⊚ ((graph h)°)) :=
      ⟨(graph_id_comp ((graph h)°)).elim id, (comp_graph_id_left ((graph h)°)).elim id⟩
    refine ⟨?_, ?_⟩
    · exact RelHom_trans hc2 (RelHom_trans h23.1 (RelHom_trans hdist.1
        (RelHom_trans h4.1 h5.1)))
    · exact RelHom_trans h5.2 (RelHom_trans h4.2 (RelHom_trans hdist.2
        (RelHom_trans h23.2 hc1)))
  -- `Ω^f = Ω^g ⟹ φ f = φ g ⟹ relPullback (φ f) = relPullback (φ g)` (congrArg).
  have hφ : singletonMapCat B ≫ expMap Ω f = singletonMapCat B ≫ expMap Ω g :=
    congrArg (singletonMapCat B ≫ ·) heq
  -- `(graph f)° ≅ relPullback (φ f) = relPullback (φ g) ≅ (graph g)°`.
  have hrel : RelHom ((graph f)°) ((graph g)°) :=
    RelHom_trans (hnames f).2 (hφ.symm ▸ (hnames g).1)
  -- A `RelHom (graph f)° → (graph g)°` gives `w` with `w ≫ g = f` and `w ≫ id = id`, so `f = g`.
  obtain ⟨w, hwA, hwB⟩ := hrel
  -- `(graph f)°.colA = f`, `.colB = id`; `(graph g)°.colA = g`, `.colB = id`.
  simp only [reciprocal, graph] at hwA hwB
  -- hwA : w ≫ g = f ; hwB : w ≫ id = id ⟹ w = id ⟹ f = g.
  have hw : w = Cat.id _ := by rw [← Cat.comp_id w]; exact hwB
  rw [← hwA, hw]; exact Cat.id_comp g

/-! ## §1.966  Progenitor -/

/-- **§1.966**: An object G is a PROGENITOR if its subobjects form a generating set:
    for any monic m : A' ↣ A that is not an iso, there exists a subobject G' ≤ G
    and a map G' → A that does not factor through A'. -/
def IsProgenitor (G : 𝒞) : Prop :=
  IsGeneratingSet (𝒞 := 𝒞) (fun X => ∃ (m : X ⟶ G), Monic m)

/-- **§1.966**: A topos is value-based iff its terminator 1 is a progenitor.
    Any Grothendieck topos has a progenitor (disjoint union of a generating set). -/
theorem topos_value_based_iff_terminal_progenitor [Topos 𝒞] :
    IsValueBased (𝒞 := 𝒞) ↔ IsProgenitor (𝒞 := 𝒞) one :=
  -- both sides unfold to `IsGeneratingSet (fun X => ∃ m : X ⟶ one, Monic m)`
  Iff.rfl

/-- The swap-transpose `Φ : (G ⟶ Ω^B) → (B ⟶ Ω^G)`: transp `k` (exponent base `B`),
    swap the product factors, then curry (exponent base `G`).  This realises the natural
    bijection `Hom(G, Ω^B) ≅ Hom(prod B G, Ω) ≅ Hom(prod G B, Ω) ≅ Hom(B, Ω^G)`. -/
private noncomputable def swapTranspose [Topos 𝒞] {G B : 𝒞}
    (k : G ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) ^^ B) :
    B ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) ^^ G :=
  curry (prodSwap G B ≫ prodMap B G (HasSubobjectClassifier.omega ^^ B) k ≫
    eval_exp B (HasSubobjectClassifier.omega (𝒞 := 𝒞)))

/-- **`swapTranspose` is injective.**  It is a curry of a precomposition by the iso
    `prodSwap`, so injective. -/
private theorem swapTranspose_inj [Topos 𝒞] {G B : 𝒞}
    {k k' : G ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) ^^ B}
    (h : swapTranspose k = swapTranspose k') : k = k' := by
  let Ω := HasSubobjectClassifier.omega (𝒞 := 𝒞)
  -- curry_inj then strip the prodSwap iso, then curry-cancel the transp.
  have h1 : prodSwap G B ≫ prodMap B G (Ω ^^ B) k ≫ eval_exp B Ω =
            prodSwap G B ≫ prodMap B G (Ω ^^ B) k' ≫ eval_exp B Ω := curry_inj h
  have h2 : prodMap B G (Ω ^^ B) k ≫ eval_exp B Ω =
            prodMap B G (Ω ^^ B) k' ≫ eval_exp B Ω := by
    have := congrArg (prodSwap B G ≫ ·) h1
    simpa only [← Cat.assoc, prodSwap_prodSwap, Cat.id_comp] using this
  -- k = curry (transp k) = curry (transp k') = k'
  have hk : k = curry (prodMap B G (Ω ^^ B) k ≫ eval_exp B Ω) := curry_unique_eq rfl
  have hk' : k' = curry (prodMap B G (Ω ^^ B) k' ≫ eval_exp B Ω) := curry_unique_eq rfl
  rw [hk, hk', h2]

/-- **Naturality of `swapTranspose` in the contravariant slot.**
    `f ≫ swapTranspose k = swapTranspose (k ≫ expMap Ω f)`.  This is the exponential
    bifunctor naturality square that turns "`Ω^f` is distinguished by `k`" into
    "`f` is distinguished by `swapTranspose k`". -/
private theorem swapTranspose_natural [Topos 𝒞] {G A B : 𝒞}
    (f : A ⟶ B) (k : G ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) ^^ B) :
    f ≫ swapTranspose k = swapTranspose (k ≫ expMap (HasSubobjectClassifier.omega (𝒞 := 𝒞)) f) := by
  let Ω := HasSubobjectClassifier.omega (𝒞 := 𝒞)
  -- LHS = curry (prodMap G A B f ≫ swapBody k)   (curry_precomp)
  -- RHS = curry (swapBody (k ≫ Ω^f))
  -- suffices: the two uncurried bodies agree on prod G A.
  rw [swapTranspose, swapTranspose, curry_precomp]
  congr 1
  -- prodMap G A B f ≫ prodSwap G B ≫ prodMap B G (Ω^B) k ≫ eval_B
  --   = prodSwap G A ≫ prodMap A G (Ω^A) (k ≫ Ω^f) ≫ eval_A
  -- Expand (k ≫ Ω^f) via prodMap_comp; β-law of Ω^f = curry(prodMapLeft f ≫ eval_B).
  have hβ : prodMap A (Ω ^^ B) (Ω ^^ A) (expMap Ω f) ≫ eval_exp A Ω =
            prodMapLeft (Ω ^^ B) f ≫ eval_exp B Ω := by
    rw [expMap]; exact curry_eval_eq _
  -- RHS rewrite: prodMap A G (Ω^A) (k ≫ Ω^f) = prodMap A G (Ω^B) k ≫ prodMap A (Ω^B) (Ω^A) (Ω^f)
  rw [prodMap_comp, Cat.assoc, hβ]
  -- Both sides are `front ≫ eval_exp B Ω`; the two fronts (`prod G A ⟶ prod B (Ω^B)`)
  -- collapse to the same normal form `nf := pair (snd≫f) (fst≫k)`.
  simp only [prodMap, prodMapLeft, prodSwap]
  have hL : (pair (fst : prod G A ⟶ G) (snd ≫ f) ≫ pair snd fst ≫ pair fst (snd ≫ k) :
        prod G A ⟶ prod B (Ω ^^ B)) = pair (snd ≫ f) (fst ≫ k) :=
    pair_uniq _ _ _
      (by rw [Cat.assoc, Cat.assoc, fst_pair, fst_pair, snd_pair])
      (by rw [Cat.assoc, Cat.assoc, snd_pair, ← Cat.assoc (pair snd fst), snd_pair,
              ← Cat.assoc, fst_pair])
  have hR : (pair (snd : prod G A ⟶ A) fst ≫ pair fst (snd ≫ k) ≫ pair (fst ≫ f) snd :
        prod G A ⟶ prod B (Ω ^^ B)) = pair (snd ≫ f) (fst ≫ k) :=
    pair_uniq _ _ _
      (by rw [Cat.assoc, Cat.assoc, fst_pair, ← Cat.assoc (pair fst (snd ≫ k)), fst_pair,
              ← Cat.assoc, fst_pair])
      (by rw [Cat.assoc, Cat.assoc, snd_pair, snd_pair, ← Cat.assoc, snd_pair])
  -- Group off the common `eval_exp B Ω` tail, rewrite both fronts to `nf`, regroup.
  calc pair (fst : prod G A ⟶ G) (snd ≫ f) ≫ pair snd fst ≫ pair fst (snd ≫ k) ≫ eval_exp B Ω
      = (pair (fst : prod G A ⟶ G) (snd ≫ f) ≫ pair snd fst ≫ pair fst (snd ≫ k)) ≫ eval_exp B Ω :=
        by rw [Cat.assoc, Cat.assoc]
    _ = pair (snd ≫ f) (fst ≫ k) ≫ eval_exp B Ω := by rw [hL]
    _ = (pair (snd : prod G A ⟶ A) fst ≫ pair fst (snd ≫ k) ≫ pair (fst ≫ f) snd) ≫ eval_exp B Ω :=
        by rw [hR]
    _ = pair (snd : prod G A ⟶ A) fst ≫ pair fst (snd ≫ k) ≫ pair (fst ≫ f) snd ≫ eval_exp B Ω :=
        by rw [Cat.assoc, Cat.assoc]

/-- **§1.966**: If G is a progenitor for a topos, then Ω^G is a cogenerator:
    given f ≠ g : A → B there exists h : B → Ω^G with f ≫ h ≠ g ≫ h.

    Proof.  `Ω` internally cogenerates (§1.965), so `f ≠ g ⟹ Ω^f ≠ Ω^g : Ω^B → Ω^A`.
    `G` is a progenitor, so its subobjects generate: there is a subobject `m : G' ↣ G`
    and `k : G' → Ω^B` with `k ≫ Ω^f ≠ k ≫ Ω^g`.  `Ω^B` is injective (`exp` of the
    injective `Ω`), so `k` extends along `m` to `k̄ : G → Ω^B` with `m ≫ k̄ = k`; then
    `k̄ ≫ Ω^f ≠ k̄ ≫ Ω^g` (precomposition by `m` can't equalise them).  Finally
    `h := swapTranspose k̄ : B → Ω^G`; naturality `f ≫ h = swapTranspose (k̄ ≫ Ω^f)`
    and injectivity of `swapTranspose` give `f ≫ h ≠ g ≫ h`. -/
theorem progenitor_omega_exp_cogenerates [Topos 𝒞] (G : 𝒞) (hG : IsProgenitor G) :
    ∀ {A B : 𝒞} (f g : A ⟶ B), f ≠ g →
      ∃ (h : B ⟶ HasSubobjectClassifier.omega (𝒞 := 𝒞) ^^ G), f ≫ h ≠ g ≫ h := by
  intro A B f g hfg
  let Ω := HasSubobjectClassifier.omega (𝒞 := 𝒞)
  -- (1) Ω internally cogenerates ⟹ Ω^f ≠ Ω^g.
  have hexp : expMap Ω f ≠ expMap Ω g := fun h => hfg (omega_internally_cogenerates f g h)
  -- (2) G is a progenitor: subobjects of G generate.  Contrapositive of IsGeneratingSet
  -- applied to the distinct maps Ω^f, Ω^g : Ω^B → Ω^A.
  have hgen := hG (expMap Ω f) (expMap Ω g)
  obtain ⟨G', ⟨m, hm⟩, k, hk⟩ : ∃ G' : 𝒞, (∃ m : G' ⟶ G, Monic m) ∧
      ∃ k : G' ⟶ Ω ^^ B, k ≫ expMap Ω f ≠ k ≫ expMap Ω g :=
    -- Contrapositive of `IsGeneratingSet`: ¬(Ω^f = Ω^g) gives a distinguishing subobject map.
    Classical.byContradiction fun hcon => hexp <| hgen fun G' hG' k =>
      Classical.byContradiction fun hne => hcon ⟨G', hG', k, hne⟩
  -- (3) Ω^B is injective; extend k along the mono m to k̄ : G → Ω^B with m ≫ k̄ = k.
  have hinj : IsInjective (Ω ^^ B) := exp_of_injective_is_injective omega_is_injective B
  obtain ⟨kbar, hkbar⟩ := hinj m hm k
  -- (4) k̄ ≫ Ω^f ≠ k̄ ≫ Ω^g (precompose with m can't equalise; m ≫ k̄ = k).
  have hkbar_ne : kbar ≫ expMap Ω f ≠ kbar ≫ expMap Ω g := by
    intro hbad
    exact hk (by rw [← hkbar, Cat.assoc, Cat.assoc, hbad])
  -- (5) h := swapTranspose k̄; naturality + injectivity give f ≫ h ≠ g ≫ h.
  refine ⟨swapTranspose kbar, ?_⟩
  rw [swapTranspose_natural f kbar, swapTranspose_natural g kbar]
  exact fun heq => hkbar_ne (swapTranspose_inj heq)

/-! ## §1.967  Arbitrary powers ↔ arbitrary copowers ↔ arbitrary copowers of 1 -/

/-- **§1.967**: A category has arbitrary POWERS if for every object A and index set I,
    the I-fold product of A with itself exists (i.e., A^I in the exponential sense).
    In a topos this is A^(Ω^I) but here we mean the indexed product ∏_{i:I} A.
    Formally: for every type I : Type v and object A, an indexed product of the
    constant family (fun _ : I => A) exists. -/
class HasArbitraryPowers (𝒞 : Type u) [Cat.{v} 𝒞] [HasBinaryProducts 𝒞] where
  /-- For each index type I and object A, the I-fold power of A. -/
  pow : (I : Type v) → 𝒞 → 𝒞
  /-- Projection from the power to A. -/
  proj : {I : Type v} → {A : 𝒞} → I → pow I A ⟶ A
  /-- Universal property: maps into the power correspond to I-indexed families of maps into A. -/
  tupling : {I : Type v} → {A X : 𝒞} → (I → X ⟶ A) → X ⟶ pow I A
  tupling_proj : ∀ {I : Type v} {A X : 𝒞} (f : I → X ⟶ A) (i : I),
    tupling f ≫ proj i = f i
  tupling_uniq : ∀ {I : Type v} {A X : 𝒞} (f : I → X ⟶ A) (h : X ⟶ pow I A),
    (∀ i, h ≫ proj i = f i) → h = tupling f

/-! ## §1.967 — the indexed-joins engine (arbitrary powers + well-poweredness ⟹ joins)

    This is the machinery that turns `HasArbitraryPowers` into arbitrary meets/joins of
    subobjects.  It is hosted HERE (rather than in the downstream `ToposIndexedJoins`, which
    re-exports it) so that `LocallySmallTopos` can carry the `WellPoweredSub` datum as a field
    and the §1.967/§1.968 completeness theorems below can feed it into
    `locallyComplete_of_powers_wellPowered`.  All defs/proofs are Sorry-free
    (axioms: `propext, Classical.choice, Quot.sound`). -/
section IndexedJoinsEngine
variable [Topos 𝒞]

section FamilyMeet
variable (hpow : HasArbitraryPowers (𝒞 := 𝒞))

/-- **§1.967 — arbitrary MEET of a `Type v`-indexed family of subobjects.**

    `⋂ᵢ Bᵢ` is the equalizer of the two tuples `A → ∏ᵢ Ω`: the tuple `⟨χ(Bᵢ)⟩ᵢ` of the
    members' characteristic maps, and the constant `⟨⊤⟩ᵢ`.  A point `a : A` factors through
    the equalizer exactly when, in every coordinate `i`, `χ(Bᵢ)(a) = ⊤`, i.e. `a ∈ Bᵢ` for all
    `i`.  Needs `HasArbitraryPowers` (for `∏ᵢ Ω`) plus the topos's own equalizers. -/
noncomputable def familyMeet {A : 𝒞} {I : Type v} (B : I → Subobject 𝒞 A) :
    Subobject 𝒞 A :=
  let chi  : A ⟶ hpow.pow I (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := hpow.tupling (fun i => subChar (B i))
  let chiT : A ⟶ hpow.pow I (HasSubobjectClassifier.omega (𝒞 := 𝒞)) :=
    hpow.tupling (fun _ => term A ≫ HasSubobjectClassifier.true (𝒞 := 𝒞))
  ⟨eqObj chi chiT, eqMap chi chiT, eqMap_monic chi chiT⟩

/-- **LOWER bound** — `⋂ᵢ Bᵢ ≤ Bⱼ` for every `j`.  The equalizer arrow equalises the two
    tuples; projecting at `j` gives `(⋂B).arr ≫ χ(Bⱼ) = (⋂B).arr ≫ ⊤ = term ≫ true`, i.e. the
    inclusion lands in `Bⱼ` (`le_iff_classify`). -/
theorem familyMeet_le {A : 𝒞} {I : Type v} (B : I → Subobject 𝒞 A) (i : I) :
    (familyMeet hpow B).le (B i) := by
  rw [familyMeet, le_iff_classify]
  show eqMap _ _ ≫ subChar (B i) = _
  have hi := congrArg (· ≫ hpow.proj i)
    (eqMap_eq (hpow.tupling (fun i => subChar (B i)))
              (hpow.tupling (fun _ => term A ≫ HasSubobjectClassifier.true (𝒞 := 𝒞))))
  simp only [Cat.assoc] at hi
  rw [hpow.tupling_proj, hpow.tupling_proj] at hi
  rw [hi, ← Cat.assoc]
  congr 1
  exact term_uniq _ _

/-- **GREATEST lower bound** — if `U ≤ Bᵢ` for every `i`, then `U ≤ ⋂ᵢ Bᵢ`.  `U.arr` equalises
    the two tuples (componentwise: `U ≤ Bᵢ` gives `U.arr ≫ χ(Bᵢ) = term ≫ true = U.arr ≫ ⊤`),
    so it factors through the equalizer by the equalizer UMP. -/
theorem familyMeet_greatest {A : 𝒞} {I : Type v} (B : I → Subobject 𝒞 A) (U : Subobject 𝒞 A)
    (hU : ∀ i, U.le (B i)) : U.le (familyMeet hpow B) := by
  rw [familyMeet]
  let chi  : A ⟶ hpow.pow I (HasSubobjectClassifier.omega (𝒞 := 𝒞)) := hpow.tupling (fun i => subChar (B i))
  let chiT : A ⟶ hpow.pow I (HasSubobjectClassifier.omega (𝒞 := 𝒞)) :=
    hpow.tupling (fun _ => term A ≫ HasSubobjectClassifier.true (𝒞 := 𝒞))
  have heq : U.arr ≫ chi = U.arr ≫ chiT := by
    rw [hpow.tupling_uniq (fun i => U.arr ≫ subChar (B i)) (U.arr ≫ chi)
          (fun i => by rw [Cat.assoc]; show U.arr ≫ hpow.tupling _ ≫ hpow.proj i = _;
                       rw [hpow.tupling_proj])]
    rw [hpow.tupling_uniq (fun i => U.arr ≫ subChar (B i)) (U.arr ≫ chiT)
          (fun i => by
            rw [Cat.assoc]
            show U.arr ≫ hpow.tupling (fun _ => term A ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)) ≫ hpow.proj i = _
            rw [hpow.tupling_proj]
            show U.arr ≫ term A ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) = U.arr ≫ subChar (B i)
            rw [(le_iff_classify U (B i)).mp (hU i), ← Cat.assoc,
                term_uniq (U.arr ≫ term A) (term U.dom)])]
  exact ⟨eqLift chi chiT U.arr heq, eqLift_fac chi chiT U.arr heq⟩

/-- **POINT/MAP into the meet (§1.968).**  An arbitrary map `t : X ⟶ A` that factors through
    *every* member `B i` factors through `⋂ᵢ Bᵢ`.  (`familyMeet_greatest` is the SUBOBJECT
    version; this is the map version needed to build the product universal property in §1.968:
    the candidate map into the ambient power, factoring through each pullback `Pᵢ`, descends to
    the intersection.)  `familyMeet` is the equalizer of `⟨χ(Bᵢ)⟩ᵢ` and `⟨⊤⟩ᵢ`; `t` factors
    through each `Bᵢ.arr`, so in every coordinate `t ≫ χ(Bᵢ) = term ≫ true` (`allows_iff_classify`),
    i.e. `t` equalises the two tuples and `eqLift` produces the factorization. -/
theorem familyMeet_lift {A X : 𝒞} {I : Type v} (B : I → Subobject 𝒞 A)
    (t : X ⟶ A) (ht : ∀ i, ∃ l, l ≫ (B i).arr = t) :
    ∃ tup : X ⟶ (familyMeet hpow B).dom, tup ≫ (familyMeet hpow B).arr = t := by
  let chi  : A ⟶ hpow.pow I (HasSubobjectClassifier.omega (𝒞 := 𝒞)) :=
    hpow.tupling (fun i => subChar (B i))
  let chiT : A ⟶ hpow.pow I (HasSubobjectClassifier.omega (𝒞 := 𝒞)) :=
    hpow.tupling (fun _ => term A ≫ HasSubobjectClassifier.true (𝒞 := 𝒞))
  -- `t` equalises the two tuples: componentwise `t ≫ χ(Bᵢ) = term ≫ true = t ≫ (term ≫ true)`.
  have heq : t ≫ chi = t ≫ chiT := by
    rw [hpow.tupling_uniq (fun i => t ≫ subChar (B i)) (t ≫ chi)
          (fun i => by rw [Cat.assoc]; show t ≫ hpow.tupling _ ≫ hpow.proj i = _;
                       rw [hpow.tupling_proj])]
    refine (hpow.tupling_uniq (fun i => t ≫ subChar (B i)) (t ≫ chiT) (fun i => ?_)).symm
    rw [Cat.assoc]
    show t ≫ hpow.tupling (fun _ => term A ≫ HasSubobjectClassifier.true (𝒞 := 𝒞)) ≫ hpow.proj i = _
    rw [hpow.tupling_proj]
    show t ≫ term A ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) = t ≫ subChar (B i)
    rw [← Cat.assoc, term_uniq (t ≫ term A) (term X),
        (allows_iff_classify (B i) t).mp (ht i)]
  exact ⟨eqLift chi chiT t heq, eqLift_fac chi chiT t heq⟩

end FamilyMeet

/-- **`Type v` well-poweredness of `Sub(A)` (§1.967).**  A small index `idx A : Type v` with an
    enumeration `enum : idx A → Sub A` that hits every subobject up to `≤` in both directions.
    This is the one primitive an elementary topos does NOT supply; in a *locally small* topos
    (`|Hom(A,Ω)| = |Sub A|` is a set, §1.967) it holds.  Given it, all arbitrary joins exist. -/
structure WellPoweredSub (𝒞 : Type u) [Cat.{v} 𝒞] where
  idx  : (A : 𝒞) → Type v
  enum : {A : 𝒞} → idx A → Subobject 𝒞 A
  surj : ∀ {A : 𝒞} (S : Subobject 𝒞 A), ∃ j : idx A, S.le (enum j) ∧ (enum j).le S

section ExtJoin
variable (hpow : HasArbitraryPowers (𝒞 := 𝒞)) (wp : WellPoweredSub.{v} 𝒞)

/-- **§1.967 — arbitrary JOIN over an external predicate.**  `sup S = ⋂ { common upper bounds
    of S }`, with the upper bounds taken among the enumerated subobjects (`wp`).  The meet is
    the `familyMeet` over the `Type v` subtype of indices whose enumerated subobject is an
    upper bound of every member of `S`. -/
noncomputable def extJoin {A : 𝒞} (S : Subobject 𝒞 A → Prop) : Subobject 𝒞 A :=
  familyMeet hpow (I := {j : wp.idx A // ∀ s, S s → s.le (wp.enum j)})
    (fun j => wp.enum j.val)

/-- `s ≤ sup S` for every member `S s`: `s` is below every common upper bound (definitionally),
    so below their meet (`familyMeet_greatest`). -/
theorem extJoin_upper {A : 𝒞} (S : Subobject 𝒞 A → Prop) (s : Subobject 𝒞 A) (hs : S s) :
    s.le (extJoin hpow wp S) := by
  rw [extJoin]
  apply familyMeet_greatest
  rintro ⟨j, hj⟩
  exact hj s hs

/-- `sup S ≤ U` whenever `U` bounds every member: enumerate `U` as `enum j` (`wp.surj`); then
    `j` indexes a common upper bound, so `familyMeet_le` gives `⋂ ≤ enum j ≤ U`. -/
theorem extJoin_least {A : 𝒞} (S : Subobject 𝒞 A → Prop) (U : Subobject 𝒞 A)
    (hU : ∀ s, S s → s.le U) : (extJoin hpow wp S).le U := by
  rw [extJoin]
  obtain ⟨j, hUj, hjU⟩ := wp.surj U
  have hjmem : ∀ s, S s → s.le (wp.enum j) := fun s hs =>
    let ⟨a, ha⟩ := hU s hs; let ⟨b, hb⟩ := hUj; ⟨a ≫ b, by rw [Cat.assoc, hb, ha]⟩
  have hle := familyMeet_le hpow
    (I := {j : wp.idx A // ∀ s, S s → s.le (wp.enum j)})
    (fun j => wp.enum j.val) ⟨j, hjmem⟩
  exact ⟨hle.choose ≫ hjU.choose, by rw [Cat.assoc, hjU.choose_spec, hle.choose_spec]⟩

/-- **§1.967 — a topos with arbitrary powers and well-powered subobjects is LOCALLY COMPLETE.**
    The `sup` is `extJoin`; the two lattice laws are `extJoin_upper` / `extJoin_least`.  This is
    the genuine `LocallyComplete` of S1_70 (the conclusion of §1.967 "powers ⟹ locally
    complete"), conditional on the well-poweredness witness `wp` that the bare topos lacks. -/
noncomputable def locallyComplete_of_powers_wellPowered : LocallyComplete 𝒞 where
  toHasImages := inferInstance
  sup S := extJoin hpow wp S
  sup_isSup := fun S => ⟨extJoin_upper hpow wp S, extJoin_least hpow wp S⟩

/-- **§1.84 FRAME LAW** — inverse image preserves arbitrary joins:
    `f#(⊔ S) ≤ ⊔ { f# B' | B' ∈ S }`.

    Holds in a topos because `f#` (inverse image) is a LEFT-adjoint-having functor on
    subobjects: `f# ⊣ ∀_f` (`ForallAlong.forallAlong_adjunction`). -/
theorem extJoin_invImage_le {A B : 𝒞} (f : A ⟶ B) (S : Subobject 𝒞 B → Prop) :
    (InverseImage f (extJoin hpow wp S)).le
      (extJoin hpow wp (fun A' => ∃ B', S B' ∧ A' = InverseImage f B')) := by
  rw [show InverseImage f (extJoin hpow wp S)
        = invImg f (extJoin hpow wp S) (HasPullbacks.has f (extJoin hpow wp S).arr) from rfl]
  rw [forallAlong_adjunction f (extJoin hpow wp (fun A' => ∃ B', S B' ∧ A' = InverseImage f B'))
        (extJoin hpow wp S) (HasPullbacks.has f (extJoin hpow wp S).arr)]
  apply extJoin_least
  intro s hs
  rw [← forallAlong_adjunction f
        (extJoin hpow wp (fun A' => ∃ B', S B' ∧ A' = InverseImage f B')) s
        (HasPullbacks.has f s.arr)]
  show (invImg f s _).le _
  rw [show invImg f s (HasPullbacks.has f s.arr) = InverseImage f s from rfl]
  exact extJoin_upper hpow wp _ (InverseImage f s) ⟨s, hs, rfl⟩

/-- **`HasIndexedSubobjectJoins 𝒞` (S1_75)** from arbitrary powers + `Type v` well-poweredness:
    `sup` is the meet of (enumerated) common upper bounds (`extJoin`); `sup_upper`/`sup_least`
    are the join UMP; `invImage_preserves_sup` is the §1.84 frame law via `f# ⊣ ∀_f`. -/
noncomputable def hasIndexedSubobjectJoins_of_powers_wellPowered :
    HasIndexedSubobjectJoins 𝒞 where
  sup S := extJoin hpow wp S
  sup_upper := extJoin_upper hpow wp
  sup_least := extJoin_least hpow wp
  invImage_preserves_sup := extJoin_invImage_le hpow wp

end ExtJoin
end IndexedJoinsEngine

/-- **§1.967**: A category has arbitrary COPOWERS if for every object A and index set I,
    the I-fold coproduct of A with itself exists (the copower I ⊗ A = ∐_{i:I} A). -/
class HasArbitraryCopowers (𝒞 : Type u) [Cat.{v} 𝒞] [HasBinaryCoproducts 𝒞] where
  /-- For each index type I and object A, the I-fold copower of A. -/
  copow : (I : Type v) → 𝒞 → 𝒞
  /-- Injection into the copower. -/
  inj : {I : Type v} → {A : 𝒞} → I → A ⟶ copow I A
  /-- Universal property: maps out of the copower correspond to I-indexed families of maps from A. -/
  cotupling : {I : Type v} → {A X : 𝒞} → (I → A ⟶ X) → copow I A ⟶ X
  inj_cotupling : ∀ {I : Type v} {A X : 𝒞} (f : I → A ⟶ X) (i : I),
    inj i ≫ cotupling f = f i
  cotupling_uniq : ∀ {I : Type v} {A X : 𝒞} (f : I → A ⟶ X) (h : copow I A ⟶ X),
    (∀ i, inj i ≫ h = f i) → h = cotupling f

/-- A LOCALLY SMALL TOPOS is a topos that is WELL-POWERED: for every object `A`, the
    collection `Sub(A)` of subobjects is small — it admits a `Type v` enumeration hitting
    every subobject up to `≤`.  This is Freyd's §1.96 "locally small" (`|Hom(A,Ω)| = |Sub A|`
    is a set); his §1.967 proof "arbitrary powers ⟹ locally complete" uses it explicitly.

    The witness is packaged as the `WellPoweredSub 𝒞` datum (a `Type v`-indexed enumeration of
    `Sub A`).  A bare elementary topos does NOT supply this `Type v` enumeration (`Subobject 𝒞 A`
    lives in `Type (max u v)`), so it is GENUINE extra structure — exactly the datum that turns
    `HasArbitraryPowers` into arbitrary subobject joins (`familyMeet`/`extJoin` above) and hence
    local completeness.  This faithful enrichment is parallel to bundling power objects into
    `Topos` and is what closes `topos_powers_implies_locally_complete`. -/
class LocallySmallTopos (𝒞 : Type u) [Cat.{v} 𝒞] extends Topos 𝒞 where
  /-- Well-poweredness: a `Type v` enumeration of `Sub(A)` for every `A` (§1.96). -/
  wellPowered : WellPoweredSub.{v} 𝒞

/-! ### §1.967 (c)→(a): arbitrary copowers-of-1 build arbitrary powers via exponentials

    Given a copower-of-1 `cI = ∐_I 1` for every index `I`, set `pow I A := A ^^ cI`.  The
    power universal property is the exponential law "exp of a coproduct is a product of
    exps": `Hom(X, A^cI) ≅ Hom(cI × X, A) ≅ ∏_I Hom(X, A)`, where the middle iso is the
    copower UP of `cI` distributed across `X × −` (`prod_distrib_copow`).  Concretely the
    `I`-fold copower of `X` is `prod X cI` (object of `prod_distrib_copow P X`), and a map
    `prod cI X ⟶ A` curries to `X ⟶ A^cI`. -/
section PowersOfCopowersOfOne
variable [Topos 𝒞]

/-- `proj i : A^cI ⟶ A` — evaluate the exponential at the `i`-th injection `inj i : 1 → cI`:
    `pair (term ≫ inj i) id ≫ eval`. -/
private noncomputable def powProj {I : Type v} (P : CopowerOfOne I 𝒞) (A : 𝒞) (i : I) :
    (A ^^ P.obj) ⟶ A :=
  pair (term (A ^^ P.obj) ≫ P.inj i) (Cat.id (A ^^ P.obj)) ≫ eval_exp P.obj A

/-- `tupling f : X ⟶ A^cI` — cotuple `f` over the copower `prod X cI`, swap to `prod cI X`,
    then curry. -/
private noncomputable def powTup {I : Type v} (P : CopowerOfOne I 𝒞) {A X : 𝒞}
    (f : I → X ⟶ A) : X ⟶ (A ^^ P.obj) :=
  curry (prodSwap P.obj X ≫ (prod_distrib_copow P X).cotup f)

/-- Key reduction: precomposing `proj i` by any `k : X ⟶ A^cI` plugs `k` into evaluation at
    coordinate `i`, i.e. `k ≫ proj i = copInj P X i ≫ prodSwap X cI ≫ transp k`.
    (`copInj P X i = pair id (term ≫ inj i)`, the `i`-th copower injection of `X`.) -/
private theorem powProj_precomp {I : Type v} (P : CopowerOfOne I 𝒞) {A X : 𝒞}
    (k : X ⟶ (A ^^ P.obj)) (i : I) :
    k ≫ powProj P A i = copInj P X i ≫ prodSwap X P.obj ≫ transp k := by
  unfold powProj transp copInj
  -- LHS: k ≫ (pair (term ≫ inj i) id ≫ eval) = pair (term X ≫ inj i) k ≫ eval
  have hL : k ≫ pair (term (A ^^ P.obj) ≫ P.inj i) (Cat.id (A ^^ P.obj)) =
      pair (term X ≫ P.inj i) k := by
    apply pair_uniq
    · rw [Cat.assoc, fst_pair, ← Cat.assoc, term_uniq (k ≫ term (A ^^ P.obj)) (term X)]
    · rw [Cat.assoc, snd_pair, Cat.comp_id]
  -- RHS: (pair id (term≫inj i) ≫ prodSwap) ≫ (X×k) = pair (term X≫inj i) k
  have hR : (pair (Cat.id X) (term X ≫ P.inj i) ≫ prodSwap X P.obj) ≫
      prodMap P.obj X (A ^^ P.obj) k = pair (term X ≫ P.inj i) k := by
    apply pair_uniq
    · rw [Cat.assoc, prodMap_fst, Cat.assoc,
        show prodSwap X P.obj ≫ fst = snd (A := X) (B := P.obj) from fst_pair _ _, snd_pair]
    · rw [Cat.assoc, prodMap_snd, Cat.assoc, ← Cat.assoc (prodSwap X P.obj),
          show prodSwap X P.obj ≫ snd = fst (A := X) (B := P.obj) from snd_pair _ _,
          ← Cat.assoc, fst_pair, Cat.id_comp]
  rw [← Cat.assoc, hL]
  simp only [← Cat.assoc]
  rw [hR]

/-- **§1.967 (c)→(a)**: a `Type v`-indexed family of copowers-of-1 yields arbitrary powers
    (built over the topos's own products; transported to a caller's products instance below). -/
noncomputable def powersOfCopowersOfOne
    (P : (I : Type v) → CopowerOfOne I 𝒞) : HasArbitraryPowers (𝒞 := 𝒞) where
  pow I A := A ^^ (P I).obj
  proj {I A} i := powProj (P I) A i
  tupling {I A X} f := powTup (P I) f
  tupling_proj {I A X} f i := by
    rw [powTup, powProj_precomp]
    -- copInj ≫ prodSwap ≫ transp (curry g) = copInj ≫ prodSwap ≫ g  with g = swap ≫ cotup f
    rw [uncurry_curry, ← Cat.assoc (prodSwap X (P I).obj), prodSwap_prodSwap, Cat.id_comp]
    -- copInj P X i = (prod_distrib_copow P X).inj i ; inj_cotup
    show (prod_distrib_copow (P I) X).inj i ≫ (prod_distrib_copow (P I) X).cotup f = f i
    rw [(prod_distrib_copow (P I) X).inj_cotup]
  tupling_uniq {I A X} f h hh := by
    -- show h = curry (prodSwap ≫ cotup f); use transp injectivity then cotup_uniq.
    rw [powTup, ← curry_uncurry h]
    apply congrArg curry
    -- goal: transp h = prodSwap P.obj X ≫ cotup f
    -- precompose by prodSwap X P.obj (iso) and use cotup_uniq
    have hswap : prodSwap X (P I).obj ≫ transp h = (prod_distrib_copow (P I) X).cotup f := by
      apply (prod_distrib_copow (P I) X).cotup_uniq
      intro i
      -- inj i ≫ prodSwap ≫ transp h = f i, via powProj_precomp on h
      show copInj (P I) X i ≫ prodSwap X (P I).obj ≫ transp h = f i
      rw [← powProj_precomp]
      exact hh i
    calc transp h = Cat.id _ ≫ transp h := (Cat.id_comp _).symm
      _ = (prodSwap (P I).obj X ≫ prodSwap X (P I).obj) ≫ transp h := by
            rw [prodSwap_prodSwap]
      _ = prodSwap (P I).obj X ≫ (prodSwap X (P I).obj ≫ transp h) := by rw [Cat.assoc]
      _ = prodSwap (P I).obj X ≫ (prod_distrib_copow (P I) X).cotup f := by rw [hswap]

end PowersOfCopowersOfOne

/-- **§1.967**: Arbitrary copowers of objects exist iff arbitrary copowers of 1 exist.
    (b)→(c) is trivial (specialise `A := 1`).  (c)→(b) is `∐ᵢ A ≅ (∐ᵢ 1) × A` via the
    distributive-law engine `prod_distrib_copow` (`Freyd/ToposDistributive.lean`, Sorry-free).

    STATEMENT FIX (faithful to §1.967, NOT a weakening).  The `(c)` side was previously a bare
    EXISTENTIAL `∃ h, ∀ i, inj i ≫ h = f i` with NO uniqueness clause.  A *copower* is a COLIMIT,
    so its cotupling `h` is part of a UNIVERSAL property and is therefore UNIQUE; dropping
    uniqueness encodes a strictly weaker statement (a "weakly initial" cocone), which is not what
    Freyd asserts.  Concretely, without uniqueness one cannot even define the `cotupling` *function*
    of `HasArbitraryCopowers` (choice over the family is not canonical) and certainly cannot
    discharge `cotupling_uniq`, so the reverse direction is genuinely unprovable from the bare
    existential.  The RHS is therefore restated as a genuine `CopowerOfOne I 𝒞` datum
    (`Freyd/ToposDistributive.lean`), which bundles `cotup` together with its uniqueness field
    `cotup_uniq` — exactly the colimit universal property.

    Both directions now CLOSE, Sorry-free:
    * `(b)→(c)`: specialise the copower of `A := 1`; `cotup`/`inj_cotup`/`cotup_uniq` come straight
      from `HasArbitraryCopowers.{cotupling, inj_cotupling, cotupling_uniq}`.
    * `(c)→(b)`: `prod_distrib_copow` turns each `CopowerOfOne I 𝒞` into a `CopowerOf I A` on
      `A × cI`, transferring cotupling AND uniqueness across the distributivity iso. -/
theorem topos_copowers_equiv_copowers_of_one [LocallySmallTopos 𝒞]
    [HasBinaryProducts 𝒞] [HasBinaryCoproducts 𝒞] :
    (Nonempty (HasArbitraryCopowers (𝒞 := 𝒞))) ↔
    (∀ (I : Type v), Nonempty (CopowerOfOne I 𝒞)) := by
  constructor
  · -- (b)→(c): the copower of `A := 1` IS a copower of 1, with full universal property.
    rintro ⟨C⟩ I
    exact ⟨{ obj := C.copow I one
             inj := fun i => C.inj i
             cotup := fun f => C.cotupling f
             inj_cotup := fun f i => C.inj_cotupling f i
             cotup_uniq := fun f h hh => C.cotupling_uniq f h hh }⟩
  · -- (c)→(b): assemble `HasArbitraryCopowers` from the per-index `CopowerOf I A` built by
    -- `prod_distrib_copow` from the chosen `CopowerOfOne`.  `Classical.choice` picks the datum.
    intro hc
    exact ⟨{
      copow := fun I A => (prod_distrib_copow (Classical.choice (hc I)) A).obj
      inj := fun {I A} i => (prod_distrib_copow (Classical.choice (hc I)) A).inj i
      cotupling := fun {I A X} f => (prod_distrib_copow (Classical.choice (hc I)) A).cotup f
      inj_cotupling := fun {I A X} f i =>
        (prod_distrib_copow (Classical.choice (hc I)) A).inj_cotup f i
      cotupling_uniq := fun {I A X} f h hh =>
        (prod_distrib_copow (Classical.choice (hc I)) A).cotup_uniq f h hh }⟩

-- **§1.967 powers↔copowers** (`topos_powers_copowers_equiv`) is now CLOSED Sorry-free in
-- `Freyd/ToposCopowers.lean`: its only residual was the (a)→(b) carving `∐ᵢ1 ⊂ ∏ᵢ(1+1)`
-- (`toposCopowerOfOne`), whose map-OUT universal property needs the infinitary disjoint
-- gluing built there (composition-over-arbitrary-join distributivity).  Relocated downstream
-- because `ToposCopowers` imports this file (it needs `HasArbitraryPowers`/`LocallySmallTopos`).

/-- **§1.967**: Arbitrary powers imply local completeness in a locally small topos.
    Proof: let {Bᵢ ↣ B} be a family of subobjects.  Since the topos is locally small,
    (B, Ω) is a set, so the power ∏ᵢ Ω exists.  The maps χ(Bᵢ) and χ(B) : B → ∏ᵢ Ω
    have an equalizer that is ⋂ᵢ Bᵢ.  Arbitrary intersections + well-poweredness
    give arbitrary unions via the Ω-internal complement structure. -/
noncomputable def topos_powers_implies_locally_complete [LocallySmallTopos 𝒞]
    (hpow : HasArbitraryPowers (𝒞 := 𝒞)) :
    LocallyComplete 𝒞 :=
  -- `LocallySmallTopos` carries the well-poweredness witness (§1.96); feed it together with
  -- the arbitrary powers into the §1.967 join engine (`extJoin` = ⋂ of common upper bounds).
  -- (Binary products / equalizers come from the topos itself, so no explicit instance args —
  -- this avoids a `HasBinaryProducts` diamond between the explicit arg and `Topos`'s own.)
  locallyComplete_of_powers_wellPowered hpow (LocallySmallTopos.wellPowered (𝒞 := 𝒞))

-- **§1.968 complete↔cocomplete** (`topos_complete_iff_cocomplete`) and **§1.969 Lawvere↔Tierney**
-- (`lawvere_eq_tierney`, with the `LawvereGrothendieckTopos`/`TierneyGrothendieckTopos` classes)
-- are relocated to `Freyd/ToposCopowers.lean`.  Both are now CLOSED (sorry-free,
-- axioms `[propext, Classical.choice, Quot.sound]`).  Hosting them next to the
-- `toposCopowerOfOne` keeps the powers↔copowers cascade in one place.

end Freyd
