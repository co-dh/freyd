import Freyd.S1_92

/-! # §1.934  Lawful per-codomain Partial Map Classifier (PMC)

  This file builds the **lawful per-codomain partial-map classifier** that the
  §1.97 W-type / recursor cluster (`Freyd/S1_97.lean :: nno_of_bicartesian_data`,
  §1.98(11)/§1.98(13)) needs but the bare law-free single-object
  `HasPartialMapClassifier` (in `Freyd/S1_92.lean`, around `:740-758`) cannot supply.

  ## What a partial map is
  A PARTIAL MAP `A ⇀ B` is a span `A ←m— D —f→ B` whose left leg `m : D ↪ A` is
  monic (the DOMAIN of definition).  Two partial maps are "the same" when their
  domains are isomorphic subobjects compatibly with `f`.  We package one as
  `PartialMap A B`.

  ## What a lawful PMC is (Freyd §1.934)
  A per-codomain classifier for `B` is an object `B̃` with a generic mono
  `η_B : B ↪ B̃` such that **every** partial map `(D ↪ A, f : D → B)` corresponds to
  a UNIQUE total map `χ : A → B̃` for which the square

  ```
        D ──f──▶ B
        │        │
       m│        │η_B
        ▼        ▼
        A ──χ──▶ B̃
  ```

  is a PULLBACK.  Being a pullback simultaneously encodes the two laws the
  recursor needs:
  *  RESTRICTION — `χ` restricted to the domain recovers `f` (`m ≫ χ = f ≫ η_B`,
     i.e. the square commutes), and the domain `D` is recovered as the pullback
     `χ⁻¹(η_B)`;
  *  UNIQUENESS — `χ` is the only total map with this property.

  The single-object structure in S1_92 is structurally only the `B = 1` instance
  `1̃ = Ω₊`; here the carrier is the genuine functor `B ↦ B̃` and the universal
  property is carried as a field (no vacuity).

  ## Status of this file
  *  `PartialMap`, `LawfulPMC`, and the pullback-square law are DEFINED in full,
     at the general per-codomain altitude (no special-casing).
  *  The `B = 1` instance `pmcAtTerminal : LawfulPMC (one)` is proved **fully and
     non-vacuously**: `1̃ = Ω`, `η_1 = true`, and the universal property is
     *exactly* the subobject-classifier universal property
     (`classify_pullback` / `classify_unique`).  This is the genuine content that
     a lawful PMC must contain, instantiated where it is provable elementarily.
  *  The general construction `∀ B, LawfulPMC B` in a topos is reduced to ONE
     precisely-named sub-lemma (`partialClassifierObject_exists`), which is the
     §1.935 "value-object" carrier `B̃` — the only piece that is genuinely
     §1.935/§1.963-gated (see the integrity note in S1_92).  Everything *around*
     that carrier (the bijection laws, packaged from a hypothetical carrier) is
     proven here.
-/

namespace Freyd

open Cat HasTerminal HasBinaryProducts HasSubobjectClassifier

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-! ## §1.934(a)  Partial maps -/

/-- A PARTIAL MAP `A ⇀ B`: a span `A ←m— D —f→ B` with monic left leg `m`
    (the domain of definition).  `dom = D`, `incl = m : D ↪ A`, `val = f : D → B`. -/
structure PartialMap (𝒞 : Type u) [Cat.{v} 𝒞] (A B : 𝒞) where
  /-- Domain of definition `D`. -/
  dom    : 𝒞
  /-- The monic inclusion `m : D ↪ A` carving out where the map is defined. -/
  incl   : dom ⟶ A
  /-- `incl` is monic (a genuine subobject of `A`). -/
  monic  : Monic incl
  /-- The value `f : D → B` on the domain of definition. -/
  val    : dom ⟶ B

/-- A total map `g : A → B` as a partial map (domain all of `A`). -/
def PartialMap.ofTotal {A B : 𝒞} (g : A ⟶ B) : PartialMap 𝒞 A B :=
  ⟨A, Cat.id A, by
    intro W u w h
    rw [Cat.comp_id, Cat.comp_id] at h; exact h, g⟩

/-! ## §1.934(b)  Lawful per-codomain classifier

  We phrase the classifying square as a `Cone` over the cospan `(χ, η)` and
  require it to be a pullback, reusing the repo's `Cone.IsPullback` (the exact
  idiom of `classify_pullback`). -/

/-- `IsPullback` depends only on the cone, so it transports across cone equality.
    (Used to identify the PMC-cone of a partial map `A ⇀ 1` with the
    subobject-classifier cone of its domain inclusion, whose `π₂` is the forced
    `D → 1`.) -/
theorem isPullback_congr {A B C : 𝒞} {f : A ⟶ C} {g : B ⟶ C}
    {c d : Cone f g} (h : c = d) (hc : c.IsPullback) : d.IsPullback := h ▸ hc

/-- The classifying cone of a partial map `P` against a candidate
    `(carrier, η)` and total map `χ : A ⟶ carrier`, *given* the commuting square
    `P.incl ≫ χ = P.val ≫ η`.  Apex `D`, legs `incl : D → A`, `val : D → B`. -/
def pmcCone {A B carrier : 𝒞} (P : PartialMap 𝒞 A B)
    (η : B ⟶ carrier) (χ : A ⟶ carrier)
    (hsq : P.incl ≫ χ = P.val ≫ η) :
    Cone χ η :=
  ⟨P.dom, P.incl, P.val, hsq⟩

/-- A LAWFUL per-codomain partial-map classifier for the codomain `B` (Freyd
    §1.934).  Carries the value object `B̃ = carrier`, the generic mono
    `η : B ↪ B̃`, and the full universal property: every partial map `A ⇀ B`
    has a unique classifying `χ : A → B̃` whose square is a pullback. -/
structure LawfulPMC (𝒞 : Type u) [Cat.{v} 𝒞] (B : 𝒞) where
  /-- The value object `B̃`. -/
  carrier      : 𝒞
  /-- The generic mono `η_B : B ↪ B̃` ("defined" point). -/
  eta          : B ⟶ carrier
  /-- `η_B` is monic. -/
  eta_monic    : Monic eta
  /-- CLASSIFY: every partial map `A ⇀ B` gets a total `χ : A → B̃`. -/
  classify     : ∀ {A : 𝒞} (_ : PartialMap 𝒞 A B), A ⟶ carrier
  /-- RESTRICTION (square commutes): `m ≫ χ = f ≫ η`. -/
  classify_sq  : ∀ {A : 𝒞} (P : PartialMap 𝒞 A B),
                   P.incl ≫ classify P = P.val ≫ eta
  /-- DOMAIN-RECOVERY: the classifying square is a pullback, so the domain `D`
      is recovered as `χ⁻¹(η_B)`. -/
  classify_pb  : ∀ {A : 𝒞} (P : PartialMap 𝒞 A B),
                   (pmcCone P eta (classify P) (classify_sq P)).IsPullback
  /-- UNIQUENESS: any `χ` whose square is a pullback equals `classify P`. -/
  classify_uniq : ∀ {A : 𝒞} (P : PartialMap 𝒞 A B) (χ : A ⟶ carrier)
                   (hsq : P.incl ≫ χ = P.val ≫ eta),
                   (pmcCone P eta χ hsq).IsPullback → χ = classify P

/-! ## §1.934(c)  The terminal instance `1̃ = Ω` (genuine, non-vacuous)

  When `B = 1` a partial map `A ⇀ 1` is just a subobject `D ↪ A` (the value
  `D → 1` is forced).  Its classifier is exactly the subobject classifier:
  `1̃ = Ω`, `η_1 = true : 1 ↪ Ω`, and the classifying map is the characteristic
  map.  The universal property is *literally* `classify_pullback` /
  `classify_unique`.  This proves the laws are inhabited and non-vacuous. -/

section Terminal
variable [HasSubobjectClassifier 𝒞]

/-- **The subobject classifier IS the lawful PMC for `B = 1`.**
    `1̃ = Ω`, `η_1 = true`, `classify P = χ_{P.incl}`. -/
noncomputable def pmcAtTerminal : LawfulPMC 𝒞 (one (𝒞 := 𝒞)) where
  carrier   := omega
  eta       := HasSubobjectClassifier.true
  eta_monic := HasSubobjectClassifier.true_monic
  classify  := fun {A} P => HasSubobjectClassifier.classify P.incl P.monic
  classify_sq := fun {A} P => by
    -- `m ≫ χ_m = (D→1) ≫ true` is `classify_sq`; and `P.val = D→1` since `B = 1`.
    rw [show P.val = term P.dom from term_uniq _ _]
    exact HasSubobjectClassifier.classify_sq P.incl P.monic
  classify_pb := fun {A} P => by
    -- The PMC-cone for `P` equals the subobject-classifier cone of `P.incl`:
    -- same apex/π₁; π₂ agree by `P.val = term P.dom`; the `w` field is
    -- proof-irrelevant.  So transport `classify_pullback` across that equality.
    have hval : P.val = term P.dom := term_uniq _ _
    have hpb := HasSubobjectClassifier.classify_pullback P.incl P.monic
    refine isPullback_congr ?_ hpb
    -- Goal: classifier-cone = pmcCone P true (classify P.incl) _.
    cases P with
    | mk dom incl monic val =>
      simp only [pmcCone] at *
      cases hval; rfl
  classify_uniq := fun {A} P χ hsq hpb => by
    have hval : P.val = term P.dom := term_uniq _ _
    -- Rewrite the square into the `term P.dom` form, then apply `classify_unique`.
    have hsq' : P.incl ≫ χ = term P.dom ≫ HasSubobjectClassifier.true := by
      rw [← hval]; exact hsq
    refine HasSubobjectClassifier.classify_unique P.incl P.monic χ hsq' ?_
    -- The classifier cone `⟨P.dom, P.incl, term P.dom, hsq'⟩` equals `pmcCone P true χ hsq`.
    refine isPullback_congr ?_ hpb
    cases P with
    | mk dom incl monic val =>
      simp only [pmcCone] at *
      cases hval; rfl

end Terminal

/-! ## §1.934(d)  The general per-codomain construction in a topos

  For a general codomain `B` the value object `B̃` is Freyd's §1.935 "value
  object": classically `B̃ ≅ B ⊔ {undefined}`, internally the object representing
  partial (deterministic) maps into `B`.  Constructing the carrier `B̃` is the
  one genuinely §1.935/§1.963-gated step (see the integrity note in
  `Freyd/S1_92.lean :: HasPartialMapClassifier`).  We isolate it as a SINGLE,
  precisely-named obligation; everything else (`PartialMap`, the laws as fields,
  the `B = 1` instance) is proved Sorry-free above.

  Standard construction (the proof obligation below).
  *  Carrier.  In a topos, `B̃` is the subobject of the power object `[B]` (or
     `Ω^B`) of those relations `S ⊆ B` that are SUBSINGLETONS ("at most one
     element").  Equivalently it is the equalizer carving out the "deterministic"
     part of `[B]`.  The repo has `singletonMap923 : B → [B]` (the diagonal
     relation `{b}`) and `singletonMapMonic923`; `η_B` is `singletonMap923 B`
     factored through the subsingleton subobject, and `topos_has_equalizers`
     supplies the carving equalizer.
  *  Generic mono `η_B : B ↪ B̃`.  The "total values": each `b ↦ {b}`, monic by
     `singletonMapMonic923`.
  *  CLASSIFY.  A partial map `(m : D ↪ A, f : D → B)` is the relation
     `R ⊆ A × B` with `R = graph` of `f` along `m`; its name `Λ(R) : A → [B]`
     lands in the subsingleton subobject (because `m` is monic ⇒ `R` is
     functional ⇒ each fibre is a subsingleton), giving `χ : A → B̃`.
  *  RESTRICTION + DOMAIN-RECOVERY (pullback).  The fibre of `η_B` over `χ(a)` is
     non-empty exactly when `a ∈ dom`, and there equals `f(a)`; this is the
     universality of `∈_B` (`is_universal`) transported through the
     subsingleton equalizer — i.e. `D = χ⁻¹(η_B)` and `m ≫ χ = f ≫ η_B`.
  *  UNIQUENESS.  `χ` is the unique name of `R` by `IsUniversalRel.classify_unique`
     for `∈_B`, restricted along the (monic) subsingleton inclusion. -/

section General
variable [Topos 𝒞]

/-! ### §1.935 construction infrastructure

  We build the per-codomain classifier `B̃` exactly as `Freyd/SlicePower.lean`
  builds the genuine slice power object: the idempotent-split subobject of `[B]`
  cut out by a "functionalize" idempotent `e : [B] → [B]`.  The base-case
  analogue of SlicePower's fibre machinery is the SUBSINGLETON restriction:
  `e(S) = {b : S = {b}}` (the singleton if `S` is a singleton, else `∅`), whose
  fixed points are exactly the subsingleton relations `B̃`.  Concretely
  `e := Λ(funcMem)` where `funcMem ⊆ [B] × B` is `{({b}, b)}` (the reciprocal
  graph of the singleton map), and a name `Λ(R)` is `e`-fixed iff `R` is
  functional (left leg monic). -/

/-- The PMC cone relation `⟨D; m, f⟩ : BinRel A B` of a span `A ←m— D —f→ B`. -/
def coneRel {A B D : 𝒞} (m : D ⟶ A) (f : D ⟶ B) (hmono : MonicPair m f) :
    BinRel 𝒞 A B := ⟨D, m, f, hmono⟩

/-- **Bridge (existence direction).**  A PMC cone `(D, m, f)` over the cospan
    `(χ, η)` is a pullback as soon as the relation `⟨D; m, f⟩` is two-sided
    `RelHom` with `relPullback χ ((graph η)°)` (the canonical pullback relation of
    `χ` against `η`).  The witnesses give mutually inverse comparison maps between
    `D` and the chosen pullback `A ×_K B`, hence the universal property. -/
theorem coneIsPullback_of_relIso {A B B' : 𝒞} {χ : A ⟶ B'} {η : B ⟶ B'}
    {D : 𝒞} {m : D ⟶ A} {f : D ⟶ B} (hmono : MonicPair m f) (hsq : m ≫ χ = f ≫ η)
    (hiso : RelHom (coneRel m f hmono) (relPullback χ ((graph η)°)) ∧
            RelHom (relPullback χ ((graph η)°)) (coneRel m f hmono)) :
    (⟨D, m, f, hsq⟩ : Cone χ η).IsPullback := by
  obtain ⟨⟨_, _, _⟩, ⟨ψ, hψA, hψB⟩⟩ := hiso
  let P := HasPullbacks.has χ η
  have hψA' : ψ ≫ m = P.cone.π₁ := hψA
  have hψB' : ψ ≫ f = P.cone.π₂ ≫ Cat.id B := hψB
  rw [Cat.comp_id] at hψB'
  intro d
  let e := P.lift d
  refine ⟨e ≫ ψ, ⟨?_, ?_⟩, ?_⟩
  · rw [Cat.assoc, hψA']; exact P.lift_fst d
  · rw [Cat.assoc, hψB']; exact P.lift_snd d
  · intro v hv1 hv2
    apply hmono
    · rw [hv1, Cat.assoc, hψA']; exact (P.lift_fst d).symm
    · rw [hv2, Cat.assoc, hψB']; exact (P.lift_snd d).symm

/-- **Bridge (uniqueness direction).**  A PMC cone that IS a pullback gives the
    two-sided `RelHom` between `⟨D; m, f⟩` and `relPullback χ ((graph η)°)`. -/
theorem coneIsPullback_to_relIso {A B B' : 𝒞} {χ : A ⟶ B'} {η : B ⟶ B'}
    {D : 𝒞} {m : D ⟶ A} {f : D ⟶ B} (hmono : MonicPair m f) (hsq : m ≫ χ = f ≫ η)
    (hpb : (⟨D, m, f, hsq⟩ : Cone χ η).IsPullback) :
    RelHom (coneRel m f hmono) (relPullback χ ((graph η)°)) ∧
    RelHom (relPullback χ ((graph η)°)) (coneRel m f hmono) := by
  let P := HasPullbacks.has χ η
  refine ⟨⟨P.lift ⟨D, m, f, hsq⟩, ?_, ?_⟩, ?_⟩
  · show P.lift ⟨D, m, f, hsq⟩ ≫ P.cone.π₁ = m; exact P.lift_fst _
  · show P.lift ⟨D, m, f, hsq⟩ ≫ (P.cone.π₂ ≫ Cat.id B) = f
    rw [Cat.comp_id]; exact P.lift_snd _
  · obtain ⟨u, ⟨hu1, hu2⟩, _⟩ := hpb ⟨P.cone.pt, P.cone.π₁, P.cone.π₂, P.cone.w⟩
    refine ⟨u, ?_, ?_⟩
    · show u ≫ m = P.cone.π₁; exact hu1
    · show u ≫ f = P.cone.π₂ ≫ Cat.id B; rw [Cat.comp_id]; exact hu2

/-- The functionalized membership relation `funcMem ⊆ [B] × B`, tabulated by
    `({·}, id) : B → [B] × B`, i.e. `{({b}, b) : b : B}`.  Equal on the nose to
    `(graph {·})°`. -/
noncomputable def funcMem (B : 𝒞) :
    BinRel 𝒞 (HasPowerObject.powerObj (C := B)) B where
  src  := B
  colA := singletonMap923 B
  colB := Cat.id B
  isMonicPair := by intro W u v _ hB; rw [Cat.comp_id, Cat.comp_id] at hB; exact hB

/-- `funcMem ⊂ ∈_B`: `{b} ∋ b`, so the functionalized membership is a sub-relation
    of true membership.  (Witness: `b ↦ (b ∈ {b})` from `relPullback {·} ∈ ≅ Δ`.) -/
theorem funcMem_le_mem (B : 𝒞) : RelHom (funcMem B) (HasPowerObject.mem (C := B)) := by
  obtain ⟨w, hwA, hwB⟩ := (powerClassify_pullback_iso (graph (Cat.id B))).1
  let P := HasPullbacks.has (singletonMap923 B) (HasPowerObject.mem (C := B)).colA
  refine ⟨w ≫ P.cone.π₂, ?_, ?_⟩
  · show (w ≫ P.cone.π₂) ≫ (HasPowerObject.mem (C := B)).colA = singletonMap923 B
    rw [Cat.assoc, ← P.cone.w, ← Cat.assoc]
    have hh : w ≫ P.cone.π₁ = Cat.id B := hwA
    rw [hh]; exact Cat.id_comp _
  · show (w ≫ P.cone.π₂) ≫ (HasPowerObject.mem (C := B)).colB = Cat.id B
    have hh : w ≫ (P.cone.π₂ ≫ (HasPowerObject.mem (C := B)).colB) = Cat.id B := hwB
    rw [Cat.assoc]; exact hh

/-- Pulling a relation `R` back along its own monic left leg yields `graph R.colB`:
    the kernel pair of a mono is the diagonal, so `relPullback R.colA R ≅ graph R.colB`.
    This is the functional content `b ∈ R(a) ⟹ R(a) = {b}`. -/
theorem relPullback_selfLeg_monic {A B : 𝒞} (R : BinRel 𝒞 A B) (hmono : Monic R.colA) :
    RelHom (relPullback R.colA R) (graph R.colB) ∧
    RelHom (graph R.colB) (relPullback R.colA R) := by
  let P := HasPullbacks.has R.colA R.colA
  have hππ : P.cone.π₁ = P.cone.π₂ := hmono _ _ P.cone.w
  refine ⟨⟨P.cone.π₁, by show P.cone.π₁ ≫ Cat.id R.src = P.cone.π₁; rw [Cat.comp_id],
      by show P.cone.π₁ ≫ R.colB = P.cone.π₂ ≫ R.colB; rw [hππ]⟩, ?_⟩
  let dcone : Cone R.colA R.colA := ⟨R.src, Cat.id R.src, Cat.id R.src, rfl⟩
  refine ⟨P.lift dcone, by show P.lift dcone ≫ P.cone.π₁ = Cat.id R.src; rw [P.lift_fst], ?_⟩
  show P.lift dcone ≫ (P.cone.π₂ ≫ R.colB) = R.colB
  rw [← Cat.assoc, P.lift_snd]; show Cat.id R.src ≫ R.colB = R.colB; rw [Cat.id_comp]

/-- **Naming identity** for a functional relation: `R.colA ≫ Λ(R) = R.colB ≫ {·}`,
    i.e. each point `(a,b)` of `R` has `R(a) = {b}` (so `Λ(R)(a)` is the singleton
    `{R(a)}`).  Proven from `relPullback_selfLeg_monic` via `classify_unique`. -/
theorem naming_eq {A B : 𝒞} (R : BinRel 𝒞 A B) (hmono : Monic R.colA) :
    R.colA ≫ powerClassify R = R.colB ≫ singletonMap923 B := by
  rw [← powerClassify_natural923 R R.colA, singletonMapNaming923]
  obtain ⟨hf, hg⟩ := relPullback_selfLeg_monic R hmono
  apply HasPowerObject.is_universal.classify_unique R.src (relPullback R.colA R)
  · exact powerClassify_pullback_iso _
  · exact ⟨relHom_trans923 hf (powerClassify_pullback_iso (graph R.colB)).1,
           relHom_trans923 (powerClassify_pullback_iso (graph R.colB)).2 hg⟩

/-- **Subsingleton/functional iso.**  For a functional `R` (left leg monic),
    `relPullback (Λ R) funcMem ≅ R`: the functionalized membership and true
    membership agree at the name of a functional relation.  This is the §1.935
    heart (`B̃ = subsingletons`). -/
theorem funcMem_pullback_iso {A B : 𝒞} (R : BinRel 𝒞 A B) (hmono : Monic R.colA) :
    RelHom (relPullback (powerClassify R) (funcMem B)) R ∧
    RelHom R (relPullback (powerClassify R) (funcMem B)) := by
  refine ⟨relHom_trans923 (relHom_pullback923 (powerClassify R) (funcMem_le_mem B))
      (powerClassify_pullback_iso R).2, ?_⟩
  let P := HasPullbacks.has (powerClassify R) (funcMem B).colA
  have hsq : R.colA ≫ powerClassify R = R.colB ≫ (funcMem B).colA := naming_eq R hmono
  let c : Cone (powerClassify R) (funcMem B).colA := ⟨R.src, R.colA, R.colB, hsq⟩
  refine ⟨P.lift c, ?_, ?_⟩
  · show P.lift c ≫ P.cone.π₁ = R.colA; exact P.lift_fst c
  · show P.lift c ≫ (P.cone.π₂ ≫ (funcMem B).colB) = R.colB
    rw [← Cat.assoc, P.lift_snd]; show R.colB ≫ Cat.id B = R.colB; rw [Cat.comp_id]

/-- The functionalize idempotent `e := Λ(funcMem) : [B] → [B]`. -/
noncomputable def funcIdem (B : 𝒞) :
    HasPowerObject.powerObj (C := B) ⟶ HasPowerObject.powerObj (C := B) :=
  powerClassify (funcMem B)

/-- **`e`-fixedness of functional names**: `Λ(R) ≫ e = Λ(R)` for functional `R`.
    `Λ(R) ≫ e = Λ(relPullback (Λ R) funcMem) = Λ(R)` since `relPullback (Λ R) funcMem ≅ R`. -/
theorem efixed_of_functional {A B : 𝒞} (R : BinRel 𝒞 A B) (hmono : Monic R.colA) :
    powerClassify R ≫ funcIdem B = powerClassify R := by
  rw [funcIdem, ← powerClassify_natural923 (funcMem B) (powerClassify R)]
  obtain ⟨h1, h2⟩ := funcMem_pullback_iso R hmono
  apply HasPowerObject.is_universal.classify_unique A (relPullback (powerClassify R) (funcMem B))
  · exact powerClassify_pullback_iso _
  · exact ⟨relHom_trans923 h1 (powerClassify_pullback_iso R).1,
           relHom_trans923 (powerClassify_pullback_iso R).2 h2⟩

/-- **e-fixed names re-present membership**: if `g ≫ e = g` then
    `relPullback g funcMem ≅ relPullback g ∈_B`.  (An e-fixed name is the name of
    its own functionalized membership: `g = Λ(relPullback g funcMem)`.) -/
theorem efixed_funcMem_iso_mem {A B : 𝒞} (g : A ⟶ HasPowerObject.powerObj (C := B))
    (hg : g ≫ funcIdem B = g) :
    RelHom (relPullback g (funcMem B)) (relPullback g (HasPowerObject.mem (C := B))) ∧
    RelHom (relPullback g (HasPowerObject.mem (C := B))) (relPullback g (funcMem B)) := by
  have hnat : g ≫ funcIdem B = powerClassify (relPullback g (funcMem B)) := by
    rw [funcIdem, powerClassify_natural923 (funcMem B) g]
  rw [hg] at hnat
  -- g = Λ(relPullback g funcMem); so relPullback g mem ≅ relPullback g funcMem via the spec.
  have hspec := powerClassify_pullback_iso (relPullback g (funcMem B))
  rw [← hnat] at hspec
  exact ⟨hspec.1, hspec.2⟩

/-- `e ≫ e = e`: idempotence (the special case `R = funcMem`, whose left leg `{·}`
    is monic by `singletonMapMonic923`). -/
theorem funcIdem_idem (B : 𝒞) : funcIdem B ≫ funcIdem B = funcIdem B :=
  efixed_of_functional (funcMem B) (singletonMapMonic923 B)

/-- The identity is monic. -/
theorem id_mono (X : 𝒞) : Monic (Cat.id X) := fun u v h => by
  rw [Cat.comp_id u, Cat.comp_id v] at h; exact h

/-- `{·}` is `e`-fixed: `{·} ≫ e = {·}`.  (`{·} = Λ(graph id)`, and `graph id` is
    functional since `id` is monic.) -/
theorem singleton_efixed (B : 𝒞) :
    singletonMap923 B ≫ funcIdem B = singletonMap923 B :=
  efixed_of_functional (graph (Cat.id B)) (id_mono B)

/-- **The value object `B̃`**: the idempotent-split subobject of `[B]` cut out by
    `e` (the equalizer of `e` and `id`), i.e. the subsingleton relations. -/
noncomputable def pmcObj (B : 𝒞) : 𝒞 :=
  eqObj (funcIdem B) (Cat.id (HasPowerObject.powerObj (C := B)))

/-- The mono `ι : B̃ ↪ [B]` (the equalizer map / idempotent section). -/
noncomputable def pmcIota (B : 𝒞) : pmcObj B ⟶ HasPowerObject.powerObj (C := B) :=
  eqMap (funcIdem B) (Cat.id _)

/-- The retraction `r : [B] ↠ B̃` (the idempotent factorization). -/
noncomputable def pmcRetr (B : 𝒞) : HasPowerObject.powerObj (C := B) ⟶ pmcObj B :=
  eqLift (funcIdem B) (Cat.id _) (funcIdem B) (by rw [Cat.comp_id]; exact funcIdem_idem B)

theorem pmcIota_idem (B : 𝒞) : pmcIota B ≫ funcIdem B = pmcIota B := by
  have h : pmcIota B ≫ funcIdem B = pmcIota B ≫ Cat.id _ := eqMap_eq (funcIdem B) (Cat.id _)
  rw [h, Cat.comp_id]

theorem pmcRetr_iota (B : 𝒞) : pmcRetr B ≫ pmcIota B = funcIdem B :=
  eqLift_fac (funcIdem B) (Cat.id _) (funcIdem B) (by rw [Cat.comp_id]; exact funcIdem_idem B)

theorem pmcIota_retr (B : 𝒞) : pmcIota B ≫ pmcRetr B = Cat.id (pmcObj B) := by
  have hy : pmcIota B ≫ funcIdem B = pmcIota B ≫ Cat.id _ := eqMap_eq (funcIdem B) (Cat.id _)
  have hfac : (pmcIota B ≫ pmcRetr B) ≫ pmcIota B = pmcIota B := by
    rw [Cat.assoc, pmcRetr_iota, pmcIota_idem]
  have hid : Cat.id (pmcObj B) ≫ pmcIota B = pmcIota B := Cat.id_comp _
  rw [eqLift_uniq _ _ _ hy _ hfac, ← eqLift_uniq _ _ _ hy _ hid]

/-- **Post-compose-mono pullback equivalence.**  For a mono `ι : K ↪ L`,
    `relPullback χ ((graph η)°) ≅ relPullback (χ ≫ ι) ((graph (η ≫ ι))°)`:
    cones over `(χ, η)` are exactly cones over `(χ≫ι, η≫ι)` since `ι` is monic. -/
theorem pullback_postcomp_mono {A B K L : 𝒞} (ι : K ⟶ L) (hι : Monic ι)
    (χ : A ⟶ K) (η : B ⟶ K) :
    RelHom (relPullback χ ((graph η)°)) (relPullback (χ ≫ ι) ((graph (η ≫ ι))°)) ∧
    RelHom (relPullback (χ ≫ ι) ((graph (η ≫ ι))°)) (relPullback χ ((graph η)°)) := by
  let P := HasPullbacks.has χ η
  let Q := HasPullbacks.has (χ ≫ ι) (η ≫ ι)
  constructor
  · have hPQ : P.cone.π₁ ≫ (χ ≫ ι) = P.cone.π₂ ≫ (η ≫ ι) := by
      rw [← Cat.assoc, ← Cat.assoc, P.cone.w]
    let c : Cone (χ ≫ ι) (η ≫ ι) := ⟨P.cone.pt, P.cone.π₁, P.cone.π₂, hPQ⟩
    refine ⟨Q.lift c, ?_, ?_⟩
    · show Q.lift c ≫ Q.cone.π₁ = P.cone.π₁; exact Q.lift_fst c
    · show Q.lift c ≫ (Q.cone.π₂ ≫ Cat.id B) = P.cone.π₂ ≫ Cat.id B
      rw [Cat.comp_id, Cat.comp_id, Q.lift_snd]
  · have hQι : (Q.cone.π₁ ≫ χ) ≫ ι = (Q.cone.π₂ ≫ η) ≫ ι := by
      rw [Cat.assoc, Cat.assoc]; exact Q.cone.w
    have hQP : Q.cone.π₁ ≫ χ = Q.cone.π₂ ≫ η := hι _ _ hQι
    let c : Cone χ η := ⟨Q.cone.pt, Q.cone.π₁, Q.cone.π₂, hQP⟩
    refine ⟨P.lift c, ?_, ?_⟩
    · show P.lift c ≫ P.cone.π₁ = Q.cone.π₁; exact P.lift_fst c
    · show P.lift c ≫ (P.cone.π₂ ≫ Cat.id B) = Q.cone.π₂ ≫ Cat.id B
      rw [Cat.comp_id, Cat.comp_id, P.lift_snd]

/-- The partial-map graph relation `⟨P.dom; P.incl, P.val⟩ : BinRel A B` (jointly
    monic because `P.incl` is monic). -/
noncomputable def pmRel {A B : 𝒞} (P : PartialMap 𝒞 A B) : BinRel 𝒞 A B :=
  ⟨P.dom, P.incl, P.val, by intro W u v hA _; exact P.monic u v (by simpa using hA)⟩

@[simp] theorem pmRel_colA {A B : 𝒞} (P : PartialMap 𝒞 A B) : (pmRel P).colA = P.incl := rfl
@[simp] theorem pmRel_colB {A B : 𝒞} (P : PartialMap 𝒞 A B) : (pmRel P).colB = P.val := rfl

/-- **§1.935 value-object obligation** (the single residual).  In a topos every
    codomain `B` has a lawful per-codomain partial-map classifier `B̃`.

    This is THE one §1.935/§1.963-gated step: it asserts the existence of the
    value object `B̃ = B ⊔ {undefined}` together with its universal property.
    All the *interface* (the `LawfulPMC` laws as a package, the `B = 1` instance
    `pmcAtTerminal` which is the `Ω`-case, and `PartialMap`) is built and verified
    Sorry-free above; only the carrier construction — Freyd's "value object",
    the subsingleton-subobject of `[B]` — remains.

    PROOF OBLIGATION (how to discharge, no axiom beyond the topos data):
      `carrier := equalizer carving the subsingleton relations out of [B]`;
      `eta := singletonMap923 B` factored through it (monic by
      `singletonMapMonic923`); `classify P := Λ(graph (P.incl, P.val))` factored
      through the subsingleton equalizer; the pullback/uniqueness laws are
      `IsUniversalRel.classify_exists`/`classify_unique` of `∈_B` transported
      across the equalizer.  See §1.934(d) above. -/
theorem partialMapClassifier_exists (B : 𝒞) : Nonempty (LawfulPMC 𝒞 B) := by
  -- `B̃ = pmcObj B` (subsingleton-subobject of `[B]`), `η = {·} ≫ r`,
  -- `classify P = Λ(pmRel P) ≫ r`.  The four laws come from the relation universal
  -- property of `∈_B` bridged to the PMC pullback square, using e-fixedness of
  -- functional names through the idempotent split `ι ⊣ r`.
  have hιmono : Monic (pmcIota B) := by
    -- ι split mono (ι ≫ r = id).
    intro W u v h
    have : (u ≫ pmcIota B) ≫ pmcRetr B = (v ≫ pmcIota B) ≫ pmcRetr B := by rw [h]
    rwa [Cat.assoc, Cat.assoc, pmcIota_retr, Cat.comp_id, Cat.comp_id] at this
  -- The monic-pair structure of a partial-map graph.
  have hpmMono : ∀ {A : 𝒞} (P : PartialMap 𝒞 A B), MonicPair P.incl P.val :=
    fun {A} P => (pmRel P).isMonicPair
  refine ⟨{
    carrier   := pmcObj B
    eta       := singletonMap923 B ≫ pmcRetr B
    eta_monic := ?_
    classify  := fun {A} P => powerClassify (pmRel P) ≫ pmcRetr B
    classify_sq := ?_
    classify_pb := ?_
    classify_uniq := ?_ }⟩
  · -- eta_monic: postcompose ι, use {·}-e-fixed and singletonMapMonic923.
    intro W u v h
    have hsη : singletonMap923 B ≫ pmcRetr B ≫ pmcIota B = singletonMap923 B := by
      rw [pmcRetr_iota, singleton_efixed]
    have hι : u ≫ singletonMap923 B = v ≫ singletonMap923 B := by
      have h2 := congrArg (· ≫ pmcIota B) h
      simp only [Cat.assoc] at h2
      rw [hsη] at h2
      exact h2
    exact singletonMapMonic923 B u v hι
  · -- classify_sq: P.incl ≫ (Λ ≫ r) = P.val ≫ ({·} ≫ r); from naming_eq ≫ r.
    intro A P
    show P.incl ≫ (powerClassify (pmRel P) ≫ pmcRetr B)
       = P.val ≫ (singletonMap923 B ≫ pmcRetr B)
    have hnm : P.incl ≫ powerClassify (pmRel P) = P.val ≫ singletonMap923 B :=
      naming_eq (pmRel P) P.monic
    rw [← Cat.assoc, ← Cat.assoc, hnm]
  · -- classify_pb.
    intro A P
    refine coneIsPullback_of_relIso (hpmMono P) _ ?_
    -- iso: coneRel P.incl P.val ≅ relPullback χ ((graph eta)°), χ = Λ ≫ r, eta = {·} ≫ r.
    -- Step χ ≫ ι = Λ, eta ≫ ι = {·}.
    have hχι : (powerClassify (pmRel P) ≫ pmcRetr B) ≫ pmcIota B = powerClassify (pmRel P) := by
      rw [Cat.assoc, pmcRetr_iota]
      exact efixed_of_functional (pmRel P) P.monic
    have hηι : (singletonMap923 B ≫ pmcRetr B) ≫ pmcIota B = singletonMap923 B := by
      rw [Cat.assoc, pmcRetr_iota, singleton_efixed]
    obtain ⟨hpc1, hpc2⟩ := pullback_postcomp_mono (pmcIota B) hιmono
      (powerClassify (pmRel P) ≫ pmcRetr B) (singletonMap923 B ≫ pmcRetr B)
    rw [hχι, hηι] at hpc1 hpc2
    -- relPullback Λ ((graph {·})°) = relPullback Λ funcMem (defeq);  coneRel = pmRel P (defeq).
    obtain ⟨hf1, hf2⟩ := funcMem_pullback_iso (pmRel P) P.monic
    exact ⟨relHom_trans923 hf2 hpc2, relHom_trans923 hpc1 hf1⟩
  · -- classify_uniq.
    intro A P χ hsq hpb
    -- get relation iso from the pullback.
    obtain ⟨hr1, hr2⟩ := coneIsPullback_to_relIso (hpmMono P) hsq hpb
    -- χ ≫ ι is e-fixed; classifies pmRel P against mem ⟹ χ ≫ ι = Λ(pmRel P).
    have hχι_efix : (χ ≫ pmcIota B) ≫ funcIdem B = χ ≫ pmcIota B := by
      -- ι ≫ e = ι ≫ (r ≫ ι) = (ι ≫ r) ≫ ι = ι.
      rw [Cat.assoc, pmcIota_idem B]
    -- relPullback (χ≫ι) mem ≅ pmRel P : via postcomp_mono + funcMem→mem (e-fixed) + hr.
    obtain ⟨hpc1, hpc2⟩ := pullback_postcomp_mono (pmcIota B) hιmono χ (singletonMap923 B ≫ pmcRetr B)
    -- (singletonMap923 B ≫ pmcRetr B) ≫ ι = {·}.
    have hηι : (singletonMap923 B ≫ pmcRetr B) ≫ pmcIota B = singletonMap923 B := by
      rw [Cat.assoc, pmcRetr_iota, singleton_efixed]
    rw [hηι] at hpc1 hpc2
    -- relPullback (χ≫ι) ((graph {·})°) = relPullback (χ≫ι) funcMem.
    obtain ⟨hfm1, hfm2⟩ := efixed_funcMem_iso_mem (χ ≫ pmcIota B) hχι_efix
    -- Chain: relPullback (χ≫ι) mem ⊂ relPullback (χ≫ι) funcMem ⊂ relPullback χ (graph η)° ≅ coneRel = pmRel.
    have hχι_eq : χ ≫ pmcIota B = powerClassify (pmRel P) := by
      apply HasPowerObject.is_universal.classify_unique A (pmRel P) (χ ≫ pmcIota B)
        (powerClassify (pmRel P))
      · -- pmRel P ≅ relPullback (χ≫ι) mem.
        refine ⟨relHom_trans923 hr1 (relHom_trans923 hpc1 hfm1),
                relHom_trans923 hfm2 (relHom_trans923 hpc2 hr2)⟩
      · exact powerClassify_pullback_iso (pmRel P)
    -- (classify P) ≫ ι = Λ(pmRel P) too; ι mono cancels.
    have hcl_ι : (powerClassify (pmRel P) ≫ pmcRetr B) ≫ pmcIota B = powerClassify (pmRel P) := by
      rw [Cat.assoc, pmcRetr_iota]
      exact efixed_of_functional (pmRel P) P.monic
    apply hιmono
    rw [hcl_ι, hχι_eq]

end General

end Freyd
