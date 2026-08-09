/-
  Freyd & Scedrov, *Categories and Allegories* — §2.331 (Moerdijk representation).

  §2.331 (i)   A countable tabular unitary division allegory is faithfully represented in a
               countable power of the allegory of `O(X)`-valued sets, for `X` metrizable without
               isolated points and `O(X)` its locale of opens.
  §2.331 (ii)  Same conclusion stated abstractly (no metric space): a power of the allegory of
               `O`-valued sets.
  §2.331 (iii) A countable logos is faithfully represented in a power of `H(X)`.
  §2.331 (iv)  A countable logos with a coprime terminator is faithfully represented in `H(X)`.

  WHAT THIS FILE PROVES (faithful conditional form).  The repo has NO metric-space / point-set
  topology type, and one must not be fabricated.  Freyd's metric space `X` enters §2.331 ONLY
  through two pieces of data, which we take as EXPLICIT hypotheses:

    • the locale `O` (an abstract `Frame`, standing for `O(X)`), and
    • Moerdijk's embedding, supplied as a FAITHFUL `AllegoryFunctor` from the §2.218 target
      allegory `Rel(Set^|Ā|)` into (a power of) `OValuedSet O`.  Concretely, a `FrameHom
      O(2^ω) ⟶ O` induces an `AllegoryFunctor (OValuedSet O(2^ω)) (OValuedSet O)`
      (`OSetFrameHom.functor`, built below from `Freyd.Locale`); the topological theorem that the
      composite `Rel(Set^|Ā|) ⟶ OValuedSet O` is faithful is the genuinely space-specific input.

  The ALGEBRAIC reduction is then PROVED here, using:
    • `Freyd.instOSetAllegory` — `OValuedSet O` is a full `Allegory` (§2.227, this session, in
      `Freyd/Locale.lean`);
    • `Freyd.repr_in_power_of_sets_of_tabular` (§2.218) — a tabular unitary distributive allegory
      is faithfully represented in `Rel(Set^|Ā|)` given the §1.543 capital data `Ā`/`hproj`/`cap`;
    • `AllegoryFunctor.comp` + `AllegoryFunctor.Faithful.comp` — faithful functors compose.

  So §2.331 is reduced, faithfully, to ONE named topological hypothesis (`moerdijk` below): the
  faithfulness of the Moerdijk embedding into `OValuedSet O`.  Everything else is proved.

  Parts (iii)/(iv) name a `logos` and a `coprime terminator`; the repo has no `Logos` class.
  The honest carrier of (iii)/(iv) is the SAME reduction with `𝒜 := Rel(Map(logos))` — see the
  marker at the end of the file.
-/

module

public import Freyd.S1_723_Locale
public import Freyd.S2_21
public import Freyd.S2_147_MapCat
public import Freyd.S2_111_RelCat

universe u

namespace Freyd

open Freyd.Alg

/-! ## §2.227/§2.331  The frame-reindexing allegory functor `OSet(F) ⟶ OSet(G)`

  `Freyd.Locale` builds `OSetFrameHom.{obj, map, map_comp, map_id, map_recip, map_inter}` from a
  `FrameHom f : F ⟶ G`.  We bundle them into the `AllegoryFunctor` here, where `AllegoryFunctor`
  (from `MapCat`) is in scope.  This is the concrete vehicle for Moerdijk's `FrameHom O(2^ω) ⟶ O`. -/

/-- **OSet is functorial in the frame** (§2.227): a `FrameHom f : F ⟶ G` induces a covariant
    `AllegoryFunctor (OValuedSet F) (OValuedSet G)` by relabelling every truth value by `f`. -/
def OSetFrameHom.functor {F G : Frame.{u}} (f : FrameHom F G) :
    AllegoryFunctor (OValuedSet F) (OValuedSet G) where
  obj       := OSetFrameHom.obj f
  map       := OSetFrameHom.map f
  map_id    := OSetFrameHom.map_id f
  map_comp  := OSetFrameHom.map_comp f
  map_recip := OSetFrameHom.map_recip f
  map_inter := OSetFrameHom.map_inter f

/-! ## §2.331 — the conditional representation theorem

  We give the abstract (part (ii)) form, from which part (i) follows by instantiating `O := O(X)`
  and `moerdijk` by Moerdijk's classical embedding; the metric space `X` itself never appears. -/

/-- **§2.331 (ii), faithful conditional form.**  Let `𝒜` be a tabular unitary distributive
    allegory (the abstract stand-in for *countable tabular unitary division allegory* — division
    ⟹ distributive, and the abstract reduction does not see countability).  Given:

      • the §1.543 CAPITAL data `Ā`/`hproj`/`cap`/`hcap` (the precisely-isolated R3 residual of the
        §2.218 representation), and
      • a FRAME `O` together with `moerdijk`, a FAITHFUL allegory functor
        `Rel(Set^|Ā|) ⟶ OValuedSet O` — Moerdijk's embedding of relations-in-a-power-of-sets into
        the allegory of `O`-valued sets —

    THEN `𝒜` is FAITHFULLY represented in the allegory `OValuedSet O` of `O`-valued sets, via
    `repr_in_power_of_sets_of_tabular ⋙ moerdijk`.

    The full topological theorem (parts (i)/(iv)) is exactly the statement that, for `O := O(X)`
    with `X` metrizable without isolated points, such a faithful `moerdijk` EXISTS; that existence
    is the only remaining non-algebraic input. -/
theorem repr_in_oset_of_tabular
    {𝒜 : Type u} [TabularUnitaryDistributiveAllegory 𝒜]
    {Ā : Type u} [Cat.{u} Ā] [RegularCategory Ā]
    (hproj : ∀ C : Ā, ∀ {P : Ā} (e : P ⟶ C), Cover e → ∃ s : C ⟶ P, s ≫ e = Cat.id C)
    (cap : @AllegoryFunctor (RelObj (MapObj 𝒜)) (RelObj Ā)
        (@relAllegory (MapObj 𝒜) Alg.mapCat Alg.mapRegularCategory) (relAllegory))
    (hcap : cap.Faithful)
    (O : Frame.{u})
    (moerdijk : AllegoryFunctor (RelObj (Ā → Type u)) (OValuedSet O))
    (hmoerdijk : moerdijk.Faithful) :
    ∃ rep : AllegoryFunctor 𝒜 (OValuedSet O), rep.Faithful := by
  obtain ⟨rep, hrep⟩ := repr_in_power_of_sets_of_tabular (𝒜 := 𝒜) hproj cap hcap
  exact ⟨rep.comp moerdijk, AllegoryFunctor.Faithful.comp hrep hmoerdijk⟩

/-- **§2.331 (i) reduced to part (ii).**  Moerdijk's data is most naturally a `FrameHom O(2^ω) ⟶ O`
    plus a faithful embedding of `Rel(Set^|Ā|)` into `OValuedSet O(2^ω)`.  This packaging shows the
    `FrameHom` entering through `OSetFrameHom.functor`: given a faithful `embed : Rel(Set^|Ā|) ⟶
    OValuedSet B` and a `FrameHom h : B ⟶ O` whose induced functor is faithful, their composite is
    a faithful `moerdijk` and part (ii) applies.  (`B` plays the role of `O(2^ω)`.) -/
theorem repr_in_oset_via_frameHom
    {𝒜 : Type u} [TabularUnitaryDistributiveAllegory 𝒜]
    {Ā : Type u} [Cat.{u} Ā] [RegularCategory Ā]
    (hproj : ∀ C : Ā, ∀ {P : Ā} (e : P ⟶ C), Cover e → ∃ s : C ⟶ P, s ≫ e = Cat.id C)
    (cap : @AllegoryFunctor (RelObj (MapObj 𝒜)) (RelObj Ā)
        (@relAllegory (MapObj 𝒜) Alg.mapCat Alg.mapRegularCategory) (relAllegory))
    (hcap : cap.Faithful)
    (B O : Frame.{u})
    (embed : AllegoryFunctor (RelObj (Ā → Type u)) (OValuedSet B)) (hembed : embed.Faithful)
    (h : FrameHom B O) (hh : (OSetFrameHom.functor h).Faithful) :
    ∃ rep : AllegoryFunctor 𝒜 (OValuedSet O), rep.Faithful :=
  repr_in_oset_of_tabular hproj cap hcap O
    (embed.comp (OSetFrameHom.functor h))
    (AllegoryFunctor.Faithful.comp hembed hh)

/-! ## §2.331 (iii)/(iv) — logos and coprime terminator

  The repo has no standalone `Logos` class; the honest carrier of a *countable logos* in this
  development is its allegory of relations `𝒜 := Rel(Map 𝒜₀)` (a tabular unitary distributive
  allegory), to which `repr_in_oset_of_tabular` already applies.  Part (iii) (representation in a
  power of `H(X)`) is then the SAME statement with the OSet target read through the §2.227
  identification `Map(OValuedSet O) ≃ H(·)` (the `opredFrame`/`H(Y)` ingredient already in
  `Freyd/Locale.lean`).  Part (iv) ADDS a *coprime terminator* hypothesis (a focal/atomic point of
  the frame) collapsing the countable power to a single `H(X)`; that focality datum is the §1.74
  focal-representation input and would be threaded as a further explicit hypothesis exactly as
  `moerdijk` is here.  No new wall: both are instances of `repr_in_oset_of_tabular` with the
  topological faithfulness supplied as a named hypothesis. -/

end Freyd
