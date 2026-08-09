/-
  Freyd & Scedrov, *Categories and Allegories* §1.637 (base case of §1.646).

  §1.637 (and the parallel reduction §1.472) say that to prove a small special
  Cartesian category / special positive pre-logos is faithfully representable in
  the category of sets, IT SUFFICES to construct, for every finite set `S` of
  proper subobjects `{A'ᵢ ⊂ Aᵢ}`, a representation `T_S : 𝒞 → 𝒮` that is faithful
  and under which each `A'ᵢ ⊂ Aᵢ` STAYS PROPER (maps to a proper, i.e. non-iso,
  monic subset).  The §1.646 assembly then forms `T : 𝒞 → 𝒮^I` over the index set
  `I` of all finite sets and collapses the power to a single `Set` with an
  ULTRAFILTER on `I` (the principal-co-ideal pre-filter extended to an ultra-filter).

  THIS FILE builds the §1.637 BASE CASE, constructively (`Classical.choice` only via
  `funext`/`Quot.sound`), with NO new axioms:

    The **Henkin–Lubkin representation** `homRep 𝒞 : 𝒞 → 𝒮^|𝒞|` (covariant hom
    family `i ↦ Hom(i,-)`, §1.55) is FAITHFUL (`homRep_separates`) and PRESERVES
    THE PROPERNESS of *every* mono — a proper (monic, non-iso) subobject maps to a
    proper monic in `𝒮^|𝒞|` (`homRep_preserves_properMono`).  In particular it
    preserves the properness of every member of any given finite set `S`
    (`finite_separation`).

  WHY DIRECT (not via §1.453 `pullback_faithful_iff_preserves_properness`):
  that lemma is stated for functors whose source and target share one object
  universe (`𝒜 ℬ : Type u`).  `homRep` lands in the power `(𝒞 → Type u) : Type (u+1)`,
  one universe up from `𝒞 : Type u`, so the §1.453 iff does not type-check on it.
  We instead reprove the properness-preservation it abstracts, directly by Yoneda:
  `homRep` PRESERVES monos (`homRep_preserves_mono`, §1.55) and REFLECTS isos
  (`homRep_reflects_iso`, below — the Yoneda right/left-inverse argument), so a
  proper mono cannot become an iso.

  HAND-OFF TO THE ULTRAFILTER (Phase A `Ultrafilter.lean`, the §1.646 INFINITE
  assembly): see `finite_separation` in this file.  The faithful
  *single-`Set`* representation of §1.646 is NOT built here: over an infinite small
  `𝒞`, a single `Set`-valued functor cannot be faithful (Cayley needs the index
  `i = A` for *every* `A`), which is precisely why §1.646 needs the ultra-product
  `𝒮^I → 𝒮`.  This file stops, as instructed, at the finite case.
-/

module

public import Freyd.S1_55
public import Freyd.S1_47


open Freyd

universe u

namespace Freyd

/-! ## §1.637  Henkin–Lubkin reflects isomorphisms (Yoneda) -/

/-- The Henkin–Lubkin representation `homRep 𝒞 : 𝒞 → 𝒮^|𝒞|` REFLECTS ISOMORPHISMS.

    If every component `Hom(i, m) : Hom(i, A') → Hom(i, A)` is a bijection then `m`
    is an iso.  This is the Yoneda argument: surjectivity at `i = A` produces a
    right inverse `r := m⁻¹(id_A)` (`r ≫ m = id_A`); injectivity of `Hom(A', m)`
    (which is just `(· ≫ m)`) upgrades it to a left inverse (`m ≫ r = id_{A'}`,
    since `(m ≫ r) ≫ m = m = id_{A'} ≫ m`).  Constructive — the inverse data is the
    given power-category inverse, no choice. -/
public theorem homRep_reflects_iso (𝒞 : Type u) [Cat.{u} 𝒞]
    {A' A : 𝒞} (m : A' ⟶ A) (hiso : IsIso ((homRepFunctor 𝒞).map m)) : IsIso m := by
  obtain ⟨ginv, h1, h2⟩ := hiso
  -- `r := ginv A (id_A)` is a right inverse of `m`.
  let r : A ⟶ A' := ginv A (Cat.id A)
  have hrm : r ≫ m = Cat.id A := by
    have := congrFun (congrFun h2 A) (Cat.id A)
    simpa [r, powerCat, homRep, homRepFunctor, familyFunctor, familyFunctorFunctor,
      homFunctor] using this
  -- `(· ≫ m)` is injective (it is `Hom(i, m)`, a component of the iso), upgrading `r`
  -- to a left inverse.
  have hmr : m ≫ r = Cat.id A' := by
    have hinj : ∀ {i : 𝒞} (g h : i ⟶ A'), g ≫ m = h ≫ m → g = h := by
      intro i g h hgh
      have hg := congrFun (congrFun h1 i) g
      have hh := congrFun (congrFun h1 i) h
      simp only [powerCat, homRepFunctor, familyFunctor, familyFunctorFunctor, homFunctor] at hg hh
      rw [← hg, ← hh, hgh]
    apply hinj (m ≫ r) (Cat.id A')
    rw [Cat.assoc, hrm, Cat.comp_id, Cat.id_comp]
  exact ⟨r, hmr, hrm⟩

/-! ## §1.637  Henkin–Lubkin preserves the properness of every mono -/

/-- **§1.637 (properness preservation).**  The Henkin–Lubkin representation
    `homRep 𝒞` carries a PROPER mono `m` (monic, non-iso) to a PROPER monic in
    `𝒮^|𝒞|`: its image is monic (`homRep_preserves_mono`, §1.55) and non-iso —
    were it iso, `homRep_reflects_iso` would force `m` iso, contradicting
    properness.  This is the §1.453 conclusion (`PreservesProperness`) for the
    Henkin–Lubkin functor, proved directly because §1.453's iff is single-universe
    and `homRep` is cross-universe (see file header). -/
theorem homRep_preserves_properMono (𝒞 : Type u) [Cat.{u} 𝒞]
    {A' A : 𝒞} {m : A' ⟶ A} (hm : ProperMono m) :
    Monic ((homRepFunctor 𝒞).map m) ∧ ¬ IsIso ((homRepFunctor 𝒞).map m) := by
  obtain ⟨hmono, hniso⟩ := hm
  exact ⟨homRep_preserves_mono 𝒞 hmono, fun hiso => hniso (homRep_reflects_iso 𝒞 m hiso)⟩

/-! ## §1.637  Finite separation: the base case of the §1.646 representation -/

/-- A PROPER SUBOBJECT datum `A' ⊂ A`: a proper mono together with its endpoints.
    A finite set `S` of proper subobjects (as in §1.637/§1.472) is a `List` of these. -/
structure ProperSub (𝒞 : Type u) [Cat.{u} 𝒞] where
  /-- the subobject `A'`. -/
  dom : 𝒞
  /-- the ambient object `A`. -/
  cod : 𝒞
  /-- the inclusion `A' ↪ A`. -/
  mono : dom ⟶ cod
  /-- it is a proper mono (monic, non-iso). -/
  proper : ProperMono mono

/-- **§1.637 BASE CASE / §1.472 reduction (finite separation).**

    For ANY finite set `S` of proper subobjects of a small category `𝒞`
    (`PreRegularCategory` covers the special-Cartesian and positive-pre-logos cases
    of §1.646), there is a representation `T_S := homRep 𝒞 : 𝒞 → 𝒮^|𝒞|` that is
    - FAITHFUL (`SeparatesMaps`, §1.55 Henkin–Lubkin), and
    - SEPARATES the properness in `S`: every member `A'ᵢ ⊂ Aᵢ ∈ S` maps to a PROPER
      monic `T_S(A'ᵢ) ⊂ T_S(Aᵢ)` (monic and non-iso).

    This is exactly the statement §1.637/§1.472 says "suffices" for §1.646.  It is
    proved Sorry-free and choice-free (`homRep_separates` + `homRep_preserves_properMono`).

    The finite set `S` plays no role in the *construction* — the single faithful
    `homRep` already preserves the properness of *every* mono — but the statement is
    phrased over a given finite `S` because that is the unit the §1.646 ultra-product
    consumes (one principal co-ideal per `S`).  -/
theorem finite_separation (𝒞 : Type u) [Cat.{u} 𝒞] [PreRegularCategory 𝒞]
    (S : List (ProperSub 𝒞)) :
    ∃ T : Functor 𝒞 (𝒞 → Type u),
      SeparatesMaps T ∧
      ∀ s ∈ S, Monic (T.map s.mono) ∧ ¬ IsIso (T.map s.mono) := by
  refine ⟨homRepFunctor 𝒞, homRep_separates 𝒞, ?_⟩
  intro s _
  exact homRep_preserves_properMono 𝒞 s.proper

/-! ## §1.646  Hand-off to the ultra-filter (Phase A `Ultrafilter.lean`)

  `finite_separation` is the §1.637 BASE CASE.  The §1.646 INFINITE assembly,
  which produces the faithful *single-`Set`* representation, is NOT done here; it
  is the job of the ultra-filter file.  The precise hand-off:

  * `I := { S : List (ProperSub 𝒞) }` is the index set of finite sets of proper
    subobjects.  `finite_separation` supplies, for every `S ∈ I`, a representation
    `T_S = homRep 𝒞 : 𝒞 → 𝒮^|𝒞|` and, for each `s ∈ S`, the witness
    `Monic (T_S s.mono) ∧ ¬ IsIso (T_S s.mono)` (properness survives).

  * Collapse `𝒮^|𝒞|` to `𝒮` per `S`: choosing a coordinate (or, faithfully,
    keeping the power) gives Freyd's `T_S : A → 𝒮` with `(T_S A'ᵢ ⊂ T_S Aᵢ) = 1`
    for `(A'ᵢ ⊂ Aᵢ) ∈ S`.  Assemble `T : 𝒞 → 𝒮^I`, `T A = (S ↦ T_S A)`.

  * `F` := the pre-filter of principal co-ideals on `I`
    (`I' ∈ F ⟺ ∃ S, I' = { S' | S ⊆ S' }`).  Extend `F` to an ULTRA-FILTER `𝓤 ⊇ F`
    (`Ultrafilter.lean` / `WellOrdering.lean` Zermelo, the only choice-heavy step).

  * The ultra-product functor `𝒮^I →[𝓤] 𝒮` post-composed with `T` is the faithful
    §1.646 representation: for `A' ⊂ A` proper, the support `‖T A' ⊂ T A‖` ⊆ `I`
    contains the principal co-ideal of `S = {A' ⊂ A}` (every richer `S'` still
    separates it, by `finite_separation`), hence lies in `F ⊆ 𝓤`, hence is not
    killed — faithfulness (`%e(𝓤) = ∅`, §1.645).

  The single residual for the full §1.646 theorem is therefore the ultra-filter
  existence/non-killing argument, which lives in Phase A's `Ultrafilter.lean`; this
  file discharges everything up to (and not including) that ultra-product step. -/
end Freyd
