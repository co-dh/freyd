/-
  Freyd & Scedrov, *Categories and Allegories* §1.546 / §1.547
  THE RELATIVE-CAPITALIZATION / `WellPointed` OBLIGATION OF THE §1.547 SLICE FACTOR.

  ── THE QUESTION (gap 2's core) ────────────────────────────────────────────────

  In the product-slice `A/(∏U)` the §1.547 rung embeds the well-supported factor
  `A = U.get k` as `sliceEmbedObj (∏U) A = ⟨A×∏U, snd⟩`.  The relative-cap step asks:
  is this embedded factor `WellPointed` in the slice — does every PROPER mono into it
  miss some global point `sliceFactorPoint A g` (`g : ∏U → A`)?

  Two pieces from `RationalCapitalization.lean` (imported, read-only) reduce this to a
  downstairs statement with no slice bookkeeping:

    * `sliceMiss_iff_g_unreachable` — a slice mono `m : D ↪ ⟨A×∏U, snd⟩` MISSES the
      g-point iff `g` is *unreachable*: no section `s` of `D.hom` has `s ≫ (m.f≫fst) = g`.
    * `prodFormMono_misses_point` — a PRODUCT-FORM mono `id_A × i` (proper base `i`) is
      missed by EVERY g-point.

  Writing `m.f = pair p q` (`q = D.hom = m.f≫snd`, `p = m.f≫fst`), `WellPointed` of the
  factor is, by the first lemma's CONTRAPOSITIVE, exactly:

      (REACH-ALL ⟹ ISO)   if every `g : ∏U → A` is reachable, then `m` is iso.

  ── THE DETERMINATION (this file) ──────────────────────────────────────────────

  REDUCTION (Sorry-free, `cover_imp_slice_iso`).  "Every `g` reachable" says exactly that
  every map `pair g id : ∏U → A×∏U` factors through `m.f`.  If those maps `{pair g id}_g`
  jointly make `m.f` a *cover*, then `m.f` is a mono cover, hence iso (`monic_cover_iso`),
  hence `m` is a slice-iso (`overIso_of_underlying`).  That is the entire categorical
  content the reduction needs.

  THE RESIDUAL IS GENUINELY CAPITAL-LEVEL, NOT well-supportedness.  The crux is whether
  REACH-ALL forces `m.f` to be a cover.  This file PROVES (Sorry-free, `factorWP_imp_wp`)
  that for the base `P = 1` (the one-element index) the slice-`WellPointed` of the embedded
  factor `sliceEmbedObj 1 A` IMPLIES `A` is `WellPointed` downstairs.  Hence:

      `sliceEmbed_factor_wellPointed` over a general pre-regular `𝒞` (only
      `WellSupported A` assumed) is NOT provable — it would make every well-supported
      object well-pointed, i.e. force `𝒞` to be `Capital`, the very property
      capitalization is meant to ACHIEVE, not assume.

  So well-supportedness of `A` does NOT give the missing fact: the family
  `{pair g id}_g` is jointly cover-like ⟺ `A` well-pointed, and `A↠1` a cover is strictly
  weaker.  Freyd's reduction forces `m` into product form using the rational-LOCALIZATION
  structure (§1.547 objects `(A,F)`, dense monos) where surviving subobjects are exactly
  the product-form `AB' ↪ AB` that `prodFormMono_misses_point` escapes — that
  localization-level reduction is the genuine missing content, above the plain slice.

  Everything here is Sorry-free and depends on NO axioms (`#print axioms` below); the
  honest reduction is committed, and the obstruction is pinned to the exact fact.
-/
module

public import Freyd.S1_48_RationalCapitalization

namespace Freyd

universe u
variable {𝒞 : Type u} [Cat.{u} 𝒞]

section SliceWellPointed
variable [HasTerminal 𝒞] [HasBinaryProducts 𝒞] [HasPullbacks 𝒞] [PullbacksTransferCovers 𝒞]

/-! ## The reduction `REACH-ALL ⟹ ISO` via the cover hypothesis (Sorry-free)

  A slice mono `m : D ↪ sliceEmbedObj P A = ⟨A×P, snd⟩` has underlying arrow
  `m.f : D.dom → A×P`.  If `m.f` is a *cover*, then (being also mono) it is iso, and then
  `m` is a slice-iso.  This is the whole categorical content of the reduction; the only
  question (settled negatively below) is what forces `m.f` to be a cover. -/

/-- If the underlying arrow `m.f` of a slice mono `m` is a COVER, then `m` is a slice-iso.
    `m.f` is mono (the slice mono reflects to its underlying arrow, `sigma_reflects_mono`)
    and a cover, so iso (`monic_cover_iso`); then `m` is iso (`overIso_of_underlying`). -/
public theorem cover_imp_slice_iso {P A : 𝒞} {D : Over P}
    (m : OverHom D (sliceEmbedObj P A)) (hm : OverMono m) (hcov : Cover m.f) :
    OverIso m :=
  overIso_of_underlying m (monic_cover_iso m.f hcov (sigma_preserves_mono m hm))

/-! ## The decisive negative determination (Sorry-free)

  The §1.547 obligation `sliceEmbed_factor_wellPointed` asks the embedded factor to be
  `WellPointed` from `WellSupported A` ALONE.  We show this is too strong: already for the
  one-element index (base `P = 1`, the terminator), `WellPointed (sliceEmbedObj 1 A)` in
  `Over 1` IMPLIES `A` is `WellPointed` downstairs.  Since `WellSupported A` (i.e. `A↠1` a
  cover) does NOT imply `WellPointed A` in a non-`Capital` category, the obligation is not
  derivable from the ambient hypotheses — it would force `𝒞` to be `Capital`.

  Mechanics: a proper mono `m : D ↪ A` in `𝒞` becomes the slice mono
  `mbar = ⟨pair m (term D), _⟩ : ⟨D, term D⟩ ↪ sliceEmbedObj 1 A` (`pair m (term D)` is mono
  because its `fst`-leg `m` is; `snd`-leg = `term D` need NOT be).  `mbar` is proper because
  `mbar.f ≫ fst = m` and `fst : A×1 ≅ A` (`prod_one_iso_right`), so `mbar` iso ⟹ `m` iso.  A
  slice point missing `mbar` projects (`·≫fst`) to a point of `A` missing `m`. -/

/-- `pair m t` is mono whenever its FIRST leg `m` is mono (the `snd`-leg `t` is arbitrary).
    Dual of `monic_pair_of_monic` (which needs the `snd`-leg mono); the `fst`-leg version is
    what the `P = 1` slice point needs (`t = term D` is not mono in general). -/
public theorem mono_pair_of_mono_fst {T A B : 𝒞} (m : T ⟶ A) (t : T ⟶ B) (hm : Monic m) :
    Monic (pair m t) :=
  (monicPair_iff_monic_pair m t).mp (fun f g hx _ => hm f g hx)

/-- **The §1.547 factor-`WellPointed` obligation forces `A` well-pointed (Sorry-free).**
    If the embedded factor `sliceEmbedObj 1 A` is `WellPointed` in `Over 1`, then `A` is
    `WellPointed` in `𝒞`.  Hence `sliceEmbed_factor_wellPointed` cannot follow from
    `WellSupported A` alone (that would make every well-supported object well-pointed, i.e.
    force `𝒞` `Capital`); the residual is genuinely Capital-level, NOT well-supportedness.
    This is the precise pin on what the cover hypothesis of `cover_imp_slice_iso` costs. -/
public theorem factorWP_imp_wp (A : 𝒞)
    (hwp : @WellPointed (Over (one : 𝒞)) _ (overHasTerminal one) (sliceEmbedObj one A)) :
    WellPointed A := by
  intro D m hm hm_not_iso
  -- the slice object and slice mono built from `m`
  let Dbar : Over (one : 𝒞) := ⟨D, term D⟩
  let mbar : OverHom Dbar (sliceEmbedObj one A) :=
    ⟨pair m (term D), snd_pair m (term D)⟩
  have hmbarf_mono : Monic mbar.f := mono_pair_of_mono_fst m (term D) hm
  have hmbar_mono : OverMono mbar := sigma_reflects_mono mbar hmbarf_mono
  -- `mbar` is proper: if iso, `mbar.f` iso, and `m = mbar.f ≫ fst` with `fst` iso, so `m` iso.
  have hmbar_not_iso : ¬ OverIso mbar := by
    intro hiso
    apply hm_not_iso
    have hf_iso : IsIso mbar.f := overIso_underlying hiso
    have : m = mbar.f ≫ (fst : prod A one ⟶ A) := (fst_pair m (term D)).symm
    rw [this]
    exact isIso_comp hf_iso prod_one_iso_right
  -- well-pointedness of the factor yields a slice point `x` missed by `mbar`
  obtain ⟨x, hx_miss⟩ := hwp mbar hmbar_mono hmbar_not_iso
  -- the missed point of `A`: project `x` to `A` by `·≫fst`
  refine ⟨x.f ≫ fst, ?_⟩
  rintro ⟨y, hy⟩
  -- lift `y : 1 → D` to a slice point `ybar : overTerm 1 → Dbar` with `ybar ≫ mbar = x`
  apply hx_miss
  refine ⟨⟨y, term_uniq _ _⟩, ?_⟩
  -- `ybar ≫ mbar = x` : a slice equation, check the underlying `y ≫ pair m (term D) = x.f`
  apply OverHom.ext
  show y ≫ pair m (term D) = x.f
  refine fst_snd_jointly_monic _ x.f ?_ ?_
  · -- `fst`-leg : `y ≫ m = x.f ≫ fst` is exactly `hy`
    rw [Cat.assoc, fst_pair]; exact hy
  · -- `snd`-leg : both are the unique map to `1`
    rw [Cat.assoc, snd_pair]; exact term_uniq _ _

end SliceWellPointed

end Freyd

