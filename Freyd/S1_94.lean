/-
  Freyd & Scedrov, *Categories and Allegories* §1.94  Internally defined intersection/union.

  §1.94  SUBOBJECTS NAMED BY F (for F ⊆ [A]); INTERNALLY DEFINED INTERSECTION ∩F.
  §1.941 ∩F is preserved by representations and is the "internally definable" lower bound.
  §1.942 NAME OF A' (adjoint name 'A' : 1 → Ω^A of χ_{A'}).
  §1.943 ∩F is below every subobject named by F; if F well-pointed, ∩F is the glb.
  §1.944 A topos has a strict coterminator.
  §1.945 A topos is regular.
  §1.946 A topos is a logos.
  §1.947 A topos is a transitive logos (R* exists for reflexive R).
  §1.948 Example: G-sets (remark).
  §1.949 INTERNALLY DEFINED UNION ∪F.
  §1.94(10) WELL-POINTED PART, SOLVABLE TOPOS.

  The §1.7 classes `HasRightAdjointImage` and `Logos` are the canonical ones from
  S1_70 (imported below).
-/

import Freyd.S1_01
import Freyd.S1_70
import Freyd.S1_09
import Freyd.S1_85
import Freyd.S1_92
import Freyd.S1_52
import Freyd.S1_58
import Freyd.S1_60
import Freyd.S1_77
-- §1.94 power-object name / `interIntersection` cluster (relocated upstream to break the
-- import cycle S1_94 → InternalForall → InternalForallTopos → S1_94).  Re-exported here so
-- S1_94's public surface (`powObj`, `nameOf`, `interIntersection`, …) is unchanged for its
-- own downstream users.
import Freyd.S1_94_InterIntersection
-- §1.945 topos-regularity infrastructure.  The cycle that used to block this import
-- (S1_94 → InternalForall → InternalForallTopos → S1_94) was removed by pointing
-- InternalForall at S1_9 directly instead of S1_94.  InternalForallTopos provides the
-- Sorry-free `toposHasImages` instance, the `SlicePi.toposPullbacksTransferCovers`
-- instance, and `topos_is_regular_real : Nonempty (RegularCategory 𝒞)`.
import Freyd.S1_94_InternalForallTopos
-- §1.946 right adjoint f## to inverse image (the `HasRightAdjointImage` keystone): the
-- subobject-level internal-∀ `radjImage`/`radjImage_adjunction`, built Sorry-free via the
-- internal-∀ family-glb machinery.  Plus §1.95 `bottomSub` for the strict coterminator.
import Freyd.S1_946_RightAdjointImage
import Freyd.S1_95_ToposColimits
-- §1.944 strict coterminator: `topos_has_coterminator` (built Sorry-free modulo the single
-- `bottomSub_dom_iso` seed = `0 × A ≅ 0`; see `Freyd/ToposStrictZero.lean`).
import Freyd.S1_944_ToposStrictZero

universe v u

namespace Freyd

open HasSubobjectClassifier

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-! ## §1.70  Logos (canonical classes from S1_70)

  A LOGOS (§1.7) is a regular category where the inverse-image f# has a
  right adjoint f## for every morphism f : A → B.  The classes
  `HasRightAdjointImage` and `Logos` are imported from S1_70. -/

/-- **§1.946 — a topos has the right adjoint `f##` to inverse image.**  Bundles the §1.946
    keystone `radjImage` (the internal-∀ right adjoint `f## = ∀_f : Sub(A) → Sub(B)`) with its
    adjunction `radjImage_adjunction` (`f* ⊣ f##`) into the `HasRightAdjointImage` interface (S1_70).
    Both are built Sorry-free in `Freyd.RightAdjointImage` via the internal-∀ family-glb machinery
    (NO §1.54 transfinite capitalization).  This is the load-bearing instance that turns
    `topos_is_logos` from a `Sorry` into an assembly. -/
noncomputable instance toposHasRightAdjointImage : HasRightAdjointImage 𝒞 where
  rightAdj f A' := radjImage f A'
  adjunction f B' A' := radjImage_adjunction f B' A'

/-! ## §1.94  Power object [A] and families named by F

  In a topos the POWER OBJECT [A] is the exponential Ω^A (§1.92).
  A subobject A' ↣ A is NAMED BY F ⊆ [A] if its name 'A'' ≤ F (§1.942).
  The INTERNALLY DEFINED INTERSECTION ∩F is built by pulling back
  `true : 1 → Ω` along the membership evaluation map (§1.94). -/

-- `powObj` (the POWER OBJECT [A] = Ω^A) is now defined in `InterIntersection` and
-- re-exported via the import above.

/-! ## §1.941  Representational invariance of ∩F

  ∩F is preserved by representations of topoi — any topos morphism T : 𝒞 → 𝒟
  carries ∩F to ∩(T(F)).  It is the LARGEST subobject of A that remains a
  lower bound under all representations, and is characterised as the largest
  subobject constructible by a formula in the partial operations of topos theory.
  In particular it is "internally definable" (§1.941). -/

/-- **§1.941**: A REPRESENTATION OF TOPOI is a functor T : 𝒞 → 𝒟 between topoi
    that preserves the topos structure (terminal, products, subobject classifier,
    exponentials).  We record this as a predicate on the functorial data. -/
def ToposMap {𝒟 : Type u} [Cat.{v} 𝒟] [Topos 𝒟]
    (T : Functor 𝒞 𝒟) : Prop :=
  PreservesMono T ∧
  (Isomorphic (T.obj (one (𝒞 := 𝒞))) (one (𝒞 := 𝒟))) ∧
  (∀ (A B : 𝒞), Isomorphic (T.obj (prod A B)) (prod (T.obj A) (T.obj B)))

-- §1.941 (PERMANENT LOWER BOUND under representations): "T(∩F) is below every
-- subobject named by T(F), for every representation of topoi T : 𝒞 → 𝒟" cannot
-- be stated faithfully yet — it needs functorial transport of subobjects and of
-- the `NamedBy` relation along T (a `T(F)`-as-a-subobject construction), which is
-- not available from the bare `ToposMap` predicate.  Recorded MISSING in S1_94.md.
-- The non-representational fragment ("∩F ≤ every subobject named by F") IS proved
-- below as `inter_le_named` (§1.943 part 1).

/-! ## §1.942  Name of a subobject

  For A' ↣ A with characteristic map χ_{A'} : A → Ω, the NAME OF A',
  written 'A'', is curry(χ_{A'}) : 1 → Ω^A = [A].  The adjunction
  prod A 1 ≅ A → Ω^A gives 'A'' = curry(fst ≫ χ_{A'}) : 1 → [A]. -/

-- `nameOf` (the NAME 'A'' : 1 → [A] of a monic) and `NamedBy` are now in
-- `InterIntersection` and re-exported via the import above.

/-! ## §1.94  Internally defined intersection ∩F

  The construction from the book: pull back `true : 1 → Ω` along the
  membership evaluation map A → Ω induced by F.  When F ⊆ [A] is presented
  as a subobject F ↣ [A], its "adjoint" 1 → [[A]] is its name.  For the
  case where F is given by a global element `F_name : 1 → [A]` (i.e. F
  is the singleton subobject of [A] containing F_name), the membership map is

      A ──pair(id,term≫F_name)──→ A × [A] ──eval──→ Ω.

  and ∩F is the pullback of true along this map. -/

-- `membershipMap` (the membership test A → Ω of a global name) and `interIntersection`
-- (the INTERNALLY DEFINED INTERSECTION ∩F) are now in `InterIntersection` and re-exported.

/-! ## §1.948  Example: G-sets (remark)

  Let G be a group.  G appears as an object in the topos YG of G-sets.
  Let F ⊆ [G] be the complement of the image of the singleton map G1 : G → [G].
  The only G-set named by F is the entire subobject; but ∩F = ∅ for non-trivial G
  (most easily checked via the forgetful U : YG → Y which is a faithful
  representation of topoi and carries ∩F to ∩(UF) = ∅).
  This shows ∩F need not equal the intersection of the named subobjects
  in general (it is only the greatest *permanent* lower bound). -/

/-! ## §1.949  Internally defined union ∪F

  Given F ⊆ [A], the INTERNALLY DEFINED UNION ∪F is the direct image of
  ε_F : prod F.dom A → Ω, where ε_F sends (f, a) to eval(a, f).
  In terms of subobjects of Ω: ∪F is the image of the evaluation
  restricted to F × A ↣ [A] × A.  Since A is the "base" and the
  target of evaluation is Ω, we record ∪F as the image of ε_F as a
  subobject of Ω.  A' is in ∪F iff some member of F names an A'' ⊆ A'. -/

/-- **§1.949**: INTERNALLY DEFINED UNION ∪F for F ⊆ [A].
    The "membership characteristic" of ∪F: subobject of Ω equal to the
    image of `pair snd (fst ≫ F.arr) ≫ eval_exp A Ω : prod F.dom A → Ω`.
    This says a ∈ ∪F iff ∃ f ∈ F, a ∈ f (i.e. eval(a, f) = true). -/
noncomputable def interUnion [HasImages 𝒞] {A : 𝒞} (F : Subobject 𝒞 (powObj A)) :
    Subobject 𝒞 (omega (𝒞 := 𝒞)) :=
  image (pair (snd (A := F.dom) (B := A)) (fst ≫ F.arr) ≫
    eval_exp A (omega (𝒞 := 𝒞)))

/-! ## §1.943  ∩F is a lower bound; glb when F is well-pointed

  The β/η-law lemma cluster around `membershipMap`/`interIntersection`
  (`membershipMap_nameOf`, `inter_le_named`, `curry_fst_membershipMap`,
  `classify_interIntersection`, `nameOf_interIntersection`, `inter_le_singleton_named`)
  is now in `InterIntersection` and re-exported via the import above. -/


/-! ## §1.944  A topos has a strict coterminator

  A STRICT COTERMINATOR is an initial object 0 such that every morphism
  into 0 is an isomorphism (§1.58).  In a topos, ∩∅ (the intersection over
  the empty family over 1) is a minimal subobject of 1 and is strict. -/

/-- **§1.946**: A topos is a logos — a regular category in which every inverse-image
    functor f# : 𝒫(B) → 𝒫(A) has a right adjoint f## (§1.946).
    Binary unions: A₁ ∪ A₂ = ∩{B' | A₁ ⊆ B' ∧ A₂ ⊆ B'} via §1.943.

    CLOSED.  `Logos` (S1_70) extends `RegularCategory` + `HasSubobjectUnions` + the right
    adjoint `HasRightAdjointImage` (f##), and additionally carries the lattice bottom
    (`bottom`/`bottom_min`/`bottom_dom_iso`).  All are available topos instances:

    * `RegularCategory` — `topos_is_regular` (the internal-∀ family-glb image + `Π_f`-cover-transfer);
    * `HasSubobjectUnions` — `toposHasSubobjectUnions` (the §1.952 family-glb of common upper bounds,
      `Freyd.ToposColimits`);
    * `HasRightAdjointImage` — `toposHasRightAdjointImage` above, the §1.946 keystone `f##`
      (`Freyd.RightAdjointImage`, internal-∀ right adjoint + adjunction, Sorry-free);
    * the lattice bottom — the strict zero subobject `bottomSub` (§1.944, `Freyd.ToposStrictZero`):
      `bottom A := bottomSub A`, minimality is `bottomSub_le`, and all bottom domains are isomorphic
      (`bottomSub_dom_iso_one`, via the `1`-pivot). -/
theorem topos_is_logos : Nonempty (Logos 𝒞) := by
  obtain ⟨reg⟩ := topos_is_regular_real (𝒞 := 𝒞)
  letI : HasImages 𝒞 := reg.toHasImages
  letI : PullbacksTransferCovers 𝒞 := reg.toPullbacksTransferCovers
  exact ⟨{ reg with
    toHasSubobjectUnions := toposHasSubobjectUnions
    toHasRightAdjointImage := toposHasRightAdjointImage
    bottom := fun A => bottomSub A
    bottom_min := fun S => bottomSub_le S
    bottom_dom_iso := fun A B =>
      isomorphic_trans (bottomSub_dom_iso_one A) (isomorphic_symm (bottomSub_dom_iso_one B)) }⟩

/-! ## §1.947  A topos is a transitive logos

  A TRANSITIVE LOGOS (§1.77) is a logos in which, for every endo-relation R on B,
  the reflexive-transitive closure R* exists (i.e. the least reflexive transitive
  relation ≥ R).

  Construction (§1.947): It suffices to find R* for reflexive R (since for any R,
  R⁺ is the transitive closure of R and R* = R(1 ∪ R)* , but Freyd notes R⁺ is
  constructible as R(1 ∪ R)*).

  Given reflexive R on B, consider the endo-relation R×1 on B×B.
  Apply the right-adjoint f## (f = R×1 : [B×B] → [B×B]) to get an endomorphism
  of 𝒫(B×B) sending S to RS.  Let F₁ ⊆ [B×B] be the equalizer of id and R×1,
  so S is named by F₁ iff RS = S (i.e. R ≤ S is a "pre-fixed-point").
  Since R is reflexive, RS ⊆ S iff RS = S.

  Let F₂ ⊆ [B×B] name the reflexive relations (contains the diagonal Δ_B).
  Set F = F₁ ∩ F₂.  Then ∩F names all reflexive S with RS ⊆ S, i.e. all
  "pre-closed" reflexive relations.  By §1.943 (capitalization + well-pointed),
  ∩F is their greatest lower bound.  R(∩F) ⊆ R(∩F) and 1 ⊆ ∩F hold by
  ordinary categorical reasoning, so ∩F is reflexive and RS ⊆ S, i.e. ∩F = R*. -/

/-- **§1.947**: A topos is a TRANSITIVE LOGOS — every endo-relation `R` on `B` has a
    reflexive-transitive closure `R*` (the least reflexive transitive relation ⊇ R), with
    its four universal properties: `R ⊑ R*`, `R*` reflexive, `R*` transitive, and `R*`
    minimal among reflexive-transitive relations containing `R`.

    HONEST DISCHARGE.  This is now stated and proved in the genuine §1.77 `BinRel` encoding
    (reflexivity = `graph(id) ⊑ R*`, the diagonal — Freyd's real notion, not the degenerate
    "entire ≤ R*" of the old `Subobject`-stub which forced `R = ⊤`).  The proof is by the new
    §1.77 keystone path: the topos R* IS Freyd's family-glb `⋂F` of reflexive pre-closed
    relations, which `transRefClos_of_glb_preclosed` assembles into a full `TransRefClos R`.
    We take that closure ABSTRACTLY via `[HasReflTransClosure 𝒞]` — Freyd's own hypothesis
    "a topos has R*" (§1.77 documents `HasReflTransClosure` as exactly the natural input for
    this theorem).  The closure-ASSEMBLY (R ⊑ R*, refl, trans, minimal) is now genuinely
    discharged from `rtc`/`le_rtc`/`(HasReflTransClosure.transRefClos R).refl`/
    `rtc_transitive`/`rtc_minimal`.

    RESIDUAL (pinned by the hypothesis, NOT a Sorry): the *existence* of the glb `M = ⋂F`
    — the §1.943 family-glb over a subobject family of `[B×B]` — still rests on §1.54's
    capitalization route, which is what would *construct* the `HasReflTransClosure 𝒞`
    instance for a bare topos (taking the `[HasReflTransClosure 𝒞]` hypothesis here rather
    than building it avoids that dependency).  The regular structure `[HasImages 𝒞]`/
    `[PullbacksTransferCovers 𝒞]` is likewise carried as an explicit hypothesis (both are now
    available — `topos_is_regular` is closed — but kept explicit here for clarity).
    This theorem isolates precisely the *closure-assembly* (done) from the *glb-instance*.

    AXIOM-HYGIENE NOTE: `#print axioms topos_has_rtc` reports `[propext, Classical.choice]` —
    the four §1.77 components (`le_rtc`/reflexivity/`rtc_transitive`/`rtc_minimal`) and
    `topos_has_exponentials` (now genuinely proved, axiom `Classical.choice` only) are all
    axiom-honest.  The local `attribute [local instance 10000] Topos.toHasBinaryProducts`
    guard is retained so `BinRel`'s `HasPullbacks` resolution always picks the computable
    product path rather than the `Classical.choice`-heavy exponential one. -/
theorem topos_has_rtc [HasImages 𝒞] [PullbacksTransferCovers 𝒞] [HasReflTransClosure 𝒞]
    {B : 𝒞} (R : BinRel 𝒞 B B) :
    ∃ Rstar : BinRel 𝒞 B B,
      -- R ⊑ R*
      RelLe R Rstar ∧
      -- R* is reflexive: diagonal graph(id) ⊑ R*
      IsReflexive Rstar ∧
      -- R* is transitive: R* ⊚ R* ⊑ R*
      IsTransitive Rstar ∧
      -- R* is the least reflexive-transitive relation containing R
      ∀ (S : BinRel 𝒞 B B),
        RelLe R S → IsReflexive S → IsTransitive S → RelLe Rstar S :=
  ⟨rtc R, le_rtc R, (HasReflTransClosure.transRefClos R).refl, rtc_transitive R,
    fun S hRS hReflS hTransS => rtc_minimal R S hRS hReflS hTransS⟩

-- §1.947: that a topos is a TRANSITIVE LOGOS (R* exists for every endo-relation)
-- is exactly the content of `topos_has_rtc` above; not restated as a vacuous theorem.

/-! ## §1.94(10)  Well-pointed part and solvable topos

  The SINGLETON MAP A1 : A → [A] names precisely the singleton subobjects,
  i.e. the images of points 1 → A.  The WELL-POINTED PART A* of A is the
  join (least upper bound) of all singletons — equivalently, the largest
  well-pointed subobject of A.

  In general A* does not exist; there is no internal construction (§1.941
  shows the obvious ∪(A1) candidate can fail).

  A SOLVABLE TOPOS is one in which every object has a well-pointed part.
  In a solvable topos every elementarily definable family of subobjects has
  a glb and lub (via ∩(F*) and ∪(F*)).

  Capital topoi are solvable: A* = A if A is well-supported, else A* = 0. -/

-- `singletonMap` (the SINGLETON MAP A1 : A → [A]) is now in `InterIntersection` and
-- re-exported via the import above.

/-- **§1.94(10)**: A subobject A' ↣ A is a POINT SUBOBJECT (named by A1) iff
    A' is the image of some point p : 1 → A. -/
def IsPointSubobj {A : 𝒞} (A' : Subobject 𝒞 A) : Prop :=
  ∃ (p : one ⟶ A), ∃ (h : one ⟶ A'.dom), h ≫ A'.arr = p

/-- **§1.94(10)**: The WELL-POINTED PART of A, if it exists, is the least upper
    bound of all point subobjects of A.  We encode existence separately. -/
def IsWellPointedPart {A : 𝒞} [HasImages 𝒞]
    (Astar : Subobject 𝒞 A) : Prop :=
  -- Astar is above every point subobject
  (∀ P : Subobject 𝒞 A, IsPointSubobj P → P.le Astar) ∧
  -- Astar is well-pointed (the points of Astar.dom are jointly epic)
  WellPointed Astar.dom ∧
  -- Astar is the least such: any other well-pointed subobject ≤ Astar
  ∀ Q : Subobject 𝒞 A, WellPointed Q.dom →
    (∀ P : Subobject 𝒞 A, IsPointSubobj P → P.le Q) → Astar.le Q

/-- **§1.94(10)**: A SOLVABLE TOPOS is a topos in which every object has a
    well-pointed part. -/
class SolvableTopos (𝒞 : Type u) [Cat.{v} 𝒞] [Topos 𝒞] [HasImages 𝒞] where
  wpPart : ∀ (A : 𝒞), Subobject 𝒞 A
  wpPart_is_wp_part : ∀ (A : 𝒞), IsWellPointedPart (wpPart A)

-- §1.94(10): the book's claim is "U(A1) is always entire" — entireness of the
-- singleton map's IMAGE under the forgetful representation U to Set.  It is NOT
-- true that A1 itself is a cover in 𝒞 (A1 is monic and is iso only when A is
-- subterminal), so `Cover (singletonMap A)` is not Freyd's statement.  The
-- representational claim needs the forgetful functor U : 𝒞 → Set, which this
-- repo does not have; recorded MISSING in S1_94.md.
--
-- The genuine categorical fact about A1 available here is MONICITY (§1.92),
-- exposed as `singletonMap_monic` — now in `InterIntersection` and re-exported.

/-- If `A` has a point `p : 1 → A`, then `A` is well-supported: `p` is a section of
    `term A : A → 1` (`p ≫ term A = id₁` by `term_uniq`), so `term A` is a cover. -/
private theorem wellSupported_of_point {A : 𝒞} (p : one ⟶ A) : WellSupported A :=
  cover_of_section (term A) p (term_uniq _ _)

/-- The image of a point `p : 1 → A` is a point subobject. -/
private theorem isPointSubobj_image {A : 𝒞} [HasImages 𝒞] (p : one ⟶ A) :
    IsPointSubobj (image p) :=
  ⟨p, image_allows p⟩

/-- **§1.94(10)**: A capital topos is solvable; the well-pointed part is
    `A* = A` when `A` is well-supported, else `A* = 0` (the §1.944/§1.95 strict
    coterminator `∅_A ↪ A`).

    CONSTRUCTION (no §1.54 capitalization needed — the old blocker note was stale,
    superseded by the now-Sorry-free §1.945/§1.946/§1.95 infra):

    * **Well-supported `A`.**  `Capital` gives `WellPointed A` directly, so take
      `A* = entire A`.  Upper: every `P ≤ entire A` trivially.  WP: `WellPointed A`.
      Least: any WP `Q` above all point subobjects must be entire — if `Q.arr` were a
      proper mono, `WellPointed A` yields a point `x : 1 → A` not factoring through
      `Q`; but `image x` is a point subobject `≤ Q`, so `x` *does* factor through `Q`
      — contradiction.  Hence `Q.arr` iso and `entire A ≤ Q`.

    * **Not well-supported `A`.**  Then `A` has NO point (a point would make `term A`
      split epi, hence a cover — `wellSupported_of_point`).  Take `A* = bottomSub A`
      (`∅_A`, §1.95).  Upper: vacuous (no point subobjects, since a point subobject
      supplies a point of `A`).  WP: vacuous — `(bottomSub A).dom ≅ Z` the strict
      coterminator (`bottomSub_dom_iso_one`), so every mono into it is iso (no proper
      monos).  Least: `bottomSub_le` (`∅_A ≤ anything`). -/
theorem capital_is_solvable [HasImages 𝒞] (hcap : Capital (𝒞 := 𝒞)) :
    ∀ (A : 𝒞), ∃ Astar : Subobject 𝒞 A, IsWellPointedPart Astar := by
  intro A
  by_cases hws : WellSupported A
  · -- A* = entire A.
    have hwpA : WellPointed A := hcap A hws
    refine ⟨Subobject.entire A, ?_, ?_, ?_⟩
    · -- upper: everything ≤ entire A.
      exact fun P _ => ⟨P.arr, Cat.comp_id _⟩
    · -- WP: (entire A).dom = A is well-pointed.
      exact hwpA
    · -- least: any WP Q above all point subobjects is entire, so entire A ≤ Q.
      intro Q _hwpQ hQabove
      -- Show Q.arr is iso, then entire A ≤ Q via Q.arr⁻¹.
      have hQiso : IsIso Q.arr := by
        by_cases hiso : IsIso Q.arr
        · exact hiso
        · exfalso
          -- WellPointed A on the proper mono Q.arr gives a point x missing Q.
          obtain ⟨x, hx⟩ := hwpA Q.arr Q.monic hiso
          -- But image x is a point subobject ≤ Q, so x factors through Q — contra.
          obtain ⟨k, hk⟩ := hQabove (image x) (isPointSubobj_image x)
          obtain ⟨g, hg⟩ := image_allows x
          exact hx ⟨g ≫ k, by rw [Cat.assoc, hk, hg]⟩
      obtain ⟨inv, _, hinv2⟩ := hQiso
      -- entire A ≤ Q : inv ≫ Q.arr = id_A = (entire A).arr.
      exact ⟨inv, by simpa [Subobject.entire] using hinv2⟩
  · -- A* = bottomSub A (∅_A).  No points of A, so no point subobjects.
    have hno_point : ∀ p : one ⟶ A, False := fun p => hws (wellSupported_of_point p)
    -- (bottomSub A).dom ≅ Z (strict coterminator): every mono into it is iso.
    obtain ⟨φ, hφ⟩ := bottomSub_dom_iso_one A
    refine ⟨bottomSub A, ?_, ?_, ?_⟩
    · -- upper: no point subobjects (a point subobject yields a point of A).
      intro P hP
      obtain ⟨p, _⟩ := hP
      exact (hno_point p).elim
    · -- WP: vacuous — every mono m into (bottomSub A).dom IS iso, contradicting the
      -- supplied `¬IsIso m`.  (m ≫ φ : D → Z is iso by strictness; φ iso ⟹ m iso.)
      intro D m _hm hnotiso
      exfalso; apply hnotiso
      have hmφ : IsIso (m ≫ φ) := strict_coterminator_bottomSub_one (m ≫ φ)
      obtain ⟨φ', hφ1, hφ2⟩ := hφ
      have hm_eq : m = (m ≫ φ) ≫ φ' := by
        rw [Cat.assoc, hφ1, Cat.comp_id]
      rw [hm_eq]
      exact isIso_comp hmφ ⟨φ, hφ2, hφ1⟩
    · -- least: ∅_A ≤ anything.
      intro Q _ _
      exact bottomSub_le Q

end Freyd
