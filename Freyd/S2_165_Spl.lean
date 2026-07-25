/-
  Freyd & Scedrov, *Categories and Allegories* — Splitting-completion §2.165–§2.169,
  §2.16(10), §2.42, §2.433–§2.435.

  Builds the pre-tabular / tabular / effective / semi-simple theory for the splitting
  completion `Spl 𝒜 = SplObj 𝒜` (constructed in `S2_21.lean`):

    §2.165   PreTabularAllegory (SplCorObj 𝒜) when 𝒜 is pre-tabular.   [PROVED]
    §2.166   TabularAllegory (SplCorObj 𝒜) when 𝒜 is pre-tabular.      [PROVED]
             (the COREFLEXIVE sub-completion = Freyd's tabular reflection §2.167)
    §2.167   The embedding 𝒜 ↪ SplObj 𝒜 is faithful.                [PROVED]
    §2.169   SplObj 𝒜 is effective.                                  [PROVED; re-export]
    §2.16(10) SplObj 𝒜 (FULL split) is tabular ↔ 𝒜 is semi-simple.
              Backward (𝒜 semi-simple → tabular): [PROVED]
                `splObj_tabular_of_semiSimple`, axiom-clean ([propext]).
              Forward (tabular → 𝒜 semi-simple): [PROVED]
                `semiSimpleAllegory_of_splObj_tabular` ([propext]).  The old "apex-vs-carrier"
                worry dissolves: the legs of a tabulation of `embHom R` are simple in `𝒜`
                because the EMBEDDED codomains carry the identity idempotent, so leg-simplicity
                in `SplObj` IS carrier-level simplicity in `𝒜` (`splLe_iff`).

  IMPORTANT SCOPE CORRECTION.  The full `SplObj 𝒜` (split ALL symmetric idempotents)
  is NOT tabular merely because `𝒜` is tabular — Freyd §2.16(10) shows it is tabular
  *iff* `𝒜` is SEMI-SIMPLE, and a general tabular allegory need not be semi-simple.
  "Spl of a tabular allegory is tabular" holds only for the COREFLEXIVE sub-completion
  `SplCorObj 𝒜` (the genuine tabular reflection, §2.167), proved below.  The full
  case needs the stronger hypothesis `[SemiSimpleAllegory 𝒜]`, under which we DO get
  `TabularAllegory (SplObj 𝒜)` (`splObj_tabular_of_semiSimple`).
    §2.42    For a power allegory 𝒜, SplObj 𝒜 is an effective power allegory.
             [TODO: needs UnionAllegory/DistributiveAllegory for SplObj 𝒜]
    §2.433–§2.435  [TODO: infra missing]

  ---

  TWO COMPLETIONS — §2.165/§2.166 vs §2.16(10):

  `SplObj 𝒜` splits ALL symmetric idempotents `e : a → a` (SymIdem: `e° = e`, `ee = e`),
  combining Freyd's two steps:
    §2.167  PM(Corefl 𝒜): split coreflexive SymIdem only (`e ⊑ id_a`).
    §2.169  PM(ER 𝒜):     split equivalence-relation SymIdem only (`id_a ⊑ e`).

  • §2.165/§2.166 (`SplCorObj 𝒜`, below): the COREFLEXIVE sub-completion is the tabular
    reflection of a pre-tabular `𝒜` — PROVED (`SplCorObj.tabular_of_preTabular`).  The
    coreflexive apex `A = 1 ∩ f≫Ψ.R≫g°` and leg-absorption (`coref_inter_comp_le`)
    handle general object idempotents; the source-apex Simple-leg obstruction
    "`P° E.e P ⊑ id_t` fails for ER E.e" is dissolved by measuring simplicity against the
    OBJECT identity `E.e` (= `id_E` in SplObj), not `id_a`.

  • §2.16(10) (FULL `SplObj 𝒜`): tabular IFF `𝒜` semi-simple.  Backward PROVED
    (`splObj_tabular_of_semiSimple`):  every `Ψ : E ⟶ F` is semi-simple in `SplObj 𝒜`
    via the TRIVIAL apex `C = ⟨c₀, 1_{c₀}⟩`, legs `F₀≫E.e`, `G₀≫F.e` — SIMPLE because
    `(F₀ E.e)°(F₀ E.e) = E.e F₀° F₀ E.e ⊑ E.e = id_E`; and `SplObj 𝒜` splits its own
    symmetric idempotents (`splObj_splitsSymmIdem`, WEAK leg — not entire, since a
    general/coreflexive object idempotent is not reflexive).  Then §2.16(10)'s
    source-apex assembly (`srcTabulation_of_semiSimple_split`, S2_22) tabulates every
    morphism.  No `UnionAllegory (SplObj 𝒜)` needed.

  §2.16(10) FORWARD (tabular `SplObj 𝒜` → `𝒜` semi-simple): PROVED
  (`semiSimpleAllegory_of_splObj_tabular`).  Tabulate `embHom R` (source-apex convention):
  apex `C` and MAPS `P : C ⟶ embObj a`, `Q : C ⟶ embObj b` with `embHom R = P° ≫ Q`,
  `P≫P° ∩ Q≫Q° = id_C`.  Underlying `R = P.R° ≫ Q.R`.  The legs ARE simple in `𝒜` at the
  carrier: `Simple P` in `SplObj` is `P° ≫ P ⊑ id_{embObj a}`, and the EMBEDDED codomain
  `embObj a` has the IDENTITY idempotent (`1_a`), so via `splLe_iff` this is exactly
  `P.R° ≫ P.R ⊑ 1_a` = `Simple P.R` in `𝒜`.  The old "apex-vs-carrier" worry was a false
  alarm: `SemiSimple` tests simplicity at the leg CODOMAIN (`1_a`, `1_b`), not at the apex
  `C.idem.e`, so no carrier-vs-apex bridge is needed — the apex idempotent only constrains
  the (untested) source.

  Conventions: diagram-order `R ≫ S`, reciprocation `R°`, `R ⊑ S`, `R ∩ S`.
  Mathlib-free.
-/

import Freyd.S2_16
import Freyd.S2_16b
import Freyd.S2_04

universe v u

namespace Freyd.Alg

open Cat

/-! ## §2.165 / §2.166  Pre-tabular and tabular completion

  §2.165/§2.166 (`SplCorObj 𝒜`, the COREFLEXIVE sub-completion = Freyd's tabular
  reflection of a pre-tabular `𝒜`): PROVED below, `SplCorObj.tabular_of_preTabular`.
  §2.16(10) (FULL `SplObj 𝒜`, tabular from `[SemiSimpleAllegory 𝒜]`): PROVED below,
  `splObj_tabular_of_semiSimple`.  See file header for the scope correction. -/

/-! ## §2.167  The embedding `𝒜 ↪ SplObj 𝒜` and the tabular reflection
  Faithfulness: use `embHom_injective` from `S2_21`. -/

/-! ## §2.169 (re-export)  Every equivalence relation of `SplObj 𝒜` splits as a map -/

/-- **§2.169** (re-export): every reflexive symmetric idempotent of `SplObj 𝒜` splits
    as a map (= every equivalence relation splits). Re-export from `S2_16b`. -/
theorem spl_effective {𝒜 : Type u} [Allegory 𝒜] {E : SplObj 𝒜} (Φ : E ⟶ E)
    (hrefl : E.idem.e ⊑ Φ.R) (hsym : Φ.R° = Φ.R) (hidem : Φ.R ≫ Φ.R = Φ.R) :
    ∃ (G : SplObj 𝒜) (f : E ⟶ G), Map f ∧ f ≫ f° = Φ ∧ f° ≫ f = Cat.id G :=
  spl_equivalence_splits_map Φ hrefl hsym hidem

/-! ## §2.16(10)  `SplObj 𝒜` is tabular when `𝒜` is semi-simple

  Freyd §2.16(10): `PM(RI 𝒜)` — the completion that splits *all* symmetric idempotents,
  our `SplObj 𝒜` — is tabular **iff** `𝒜` is semi-simple.  (It is NOT tabular merely
  because `𝒜` is tabular: a general tabular allegory need not be semi-simple, so the
  "Spl of a tabular allegory is tabular" reading holds only for the COREFLEXIVE
  sub-completion `SplCorObj 𝒜` below, the genuine tabular reflection §2.167.)

  BACKWARD (the keystone, proven here): `[SemiSimpleAllegory 𝒜] → TabularAllegory (SplObj 𝒜)`.
  Freyd's "routine" argument, made constructive:
    • `SplObj 𝒜` is itself semi-simple (`splObj_semiSimple`): a factorisation
      `Ψ.R = F₀° G₀` in `𝒜` (`F₀, G₀` simple) lifts to SIMPLE split-homs `F = F₀ E.e`,
      `G = G₀ F.e` out of the apex `C = ⟨c₀, F F° ∩ G G°⟩` — using `Ψ.R` fixed
      (`Ψ.R = (F₀ E.e)°(G₀ F.e)`).
    • `SplObj 𝒜` splits all its own symmetric idempotents (`splObj_splitsSymmIdem`,
      from `spl_equivalence_splits`); the split leg need not be entire (the object
      idempotent need not be reflexive), which is exactly why the WEAKENED
      `SplitsSymmIdem` predicate (no `Map f`) is the right hypothesis.
    • §2.16(10) source-apex assembly (`srcTabulation_of_semiSimple_split`, S2_22) then
      tabulates every morphism: split `F F° ∩ G G°` of a semi-simple factorisation, and
      `(f° F, f° G)` is a jointly-monic map span.  `tabular_of_semiSimple_splits`
      packages this into `Tabular` for any allegory with both properties. -/

/-- An allegory in which every morphism is semi-simple **and** every symmetric idempotent
    splits (the weak idempotent-split, no entireness) is tabular.  Freyd §2.16(10):
    `srcTabulation_of_semiSimple_split` yields a source-apex jointly-monic *map* span
    `(f° F₀, f° G₀)` of any morphism, which is exactly a `Tabulates`. -/
theorem tabular_of_semiSimple_splits {ℬ : Type u} [Allegory ℬ]
    (hss : ∀ {a b : ℬ} (R : a ⟶ b), SemiSimple R) (hsplit : SplitsSymmIdem ℬ)
    {a b : ℬ} (R : a ⟶ b) : Tabular R :=
  let ⟨c, F, G, hF, hG, hU, hm⟩ := srcTabulation_of_semiSimple_split hsplit R (hss R)
  ⟨c, F, G, hF, hG, hU, hm⟩

/-! ### §2.16(10) ingredient 1 — `SplObj 𝒜` splits its own symmetric idempotents. -/

/-- In `SplObj 𝒜`, the allegory order, reciprocation and composition are read off the
    underlying `𝒜`-morphisms (`splInter`/`splRecip`/`splComp` are `𝒜`-fixed). -/
theorem splLe_iff {𝒜 : Type u} [Allegory 𝒜] {E F : SplObj 𝒜} (Φ Ψ : E ⟶ F) :
    Φ ⊑ Ψ ↔ Φ.R ⊑ Ψ.R := by
  -- `Φ ⊑ Ψ` is `Φ ∩ Ψ = Φ`, i.e. `splInter Φ Ψ = Φ`; underlying `(splInter Φ Ψ).R = Φ.R ∩ Ψ.R`.
  show splInter Φ Ψ = Φ ↔ Φ.R ∩ Ψ.R = Φ.R
  constructor
  · intro h; exact congrArg SplHom.R h
  · intro h; exact SplHom.ext h

/-- **§2.16(10) ingredient 1**: `SplObj 𝒜` splits every symmetric idempotent (no
    entireness on the leg — a general object idempotent is not reflexive).  This is
    exactly `spl_equivalence_splits` repackaged into the weak `SplitsSymmIdem` form. -/
theorem splObj_splitsSymmIdem {𝒜 : Type u} [Allegory 𝒜] : SplitsSymmIdem (SplObj 𝒜) := by
  intro E Φ hΦsym hΦidem
  -- Φ.R is a symmetric idempotent of 𝒜 (the SplObj symmetry/idempotency descend).
  have hRsym : Φ.R° = Φ.R := by
    have := (splLe_iff (splRecip Φ) Φ).mp hΦsym
    exact symmetric_eq this
  have hRidem : Φ.R ≫ Φ.R = Φ.R := by
    have h := congrArg SplHom.R hΦidem
    exact h
  obtain ⟨G, leg, hleg1, hleg2⟩ := spl_equivalence_splits Φ hRsym hRidem
  exact ⟨G, leg, hleg1, hleg2⟩

/-! ### §2.16(10) ingredient 2 — `SplObj 𝒜` is semi-simple when `𝒜` is. -/

/-- **§2.16(10) ingredient 2**: if `𝒜` is semi-simple then so is `SplObj 𝒜`.

    A factorisation `Ψ.R = F₀° G₀` (`F₀ : c₀ ⟶ a`, `G₀ : c₀ ⟶ b` simple in `𝒜`) lifts
    to the TRIVIAL-apex span `C = ⟨c₀, 1_{c₀}⟩`, `legF.R = F₀ ≫ E.e : C ⟶ E`,
    `legG.R = G₀ ≫ F.e : C ⟶ F`.

    • `Ψ = legF° ≫ legG`: underlying `E.e F₀° G₀ F.e = E.e Ψ.R F.e = Ψ.R` (`Ψ.R` fixed).
    • `legF` SIMPLE in `SplObj` — `legF° ≫ legF ⊑ id_E = E.e` — because the codomain
      identity *is* `E.e`: `(F₀ E.e)° (F₀ E.e) = E.e F₀° F₀ E.e ⊑ E.e 1 E.e = E.e`
      (`F₀` simple).  This is exactly why the trivial apex suffices: simplicity is
      measured against the codomain idempotent `E.e`, not against `1_a`. -/
theorem splObj_semiSimple {𝒜 : Type u} [SemiSimpleAllegory 𝒜] {E F : SplObj 𝒜}
    (Ψ : E ⟶ F) : SemiSimple Ψ := by
  obtain ⟨c0, F0, G0, hF0, hG0, hUfac⟩ := SemiSimpleAllegory.semi_simple Ψ.R
  have hEsym : E.idem.e° = E.idem.e := E.idem.sym
  have hFsym : F.idem.e° = F.idem.e := F.idem.sym
  have hEidem : E.idem.e ≫ E.idem.e = E.idem.e := E.idem.idem
  have hFidem : F.idem.e ≫ F.idem.e = F.idem.e := F.idem.idem
  -- Trivial apex C = ⟨c0, 1_{c0}⟩.
  let C : SplObj 𝒜 := ⟨c0, ⟨Cat.id c0, recip_id, Cat.id_comp _⟩⟩
  -- Legs, with the right SplHom fixedness (id on the left, E.e/F.e on the right).
  let legF : C ⟶ E := ⟨F0 ≫ E.idem.e, by
        show Cat.id c0 ≫ (F0 ≫ E.idem.e) ≫ E.idem.e = F0 ≫ E.idem.e
        rw [Cat.id_comp, Cat.assoc, hEidem]⟩
  let legG : C ⟶ F := ⟨G0 ≫ F.idem.e, by
        show Cat.id c0 ≫ (G0 ≫ F.idem.e) ≫ F.idem.e = G0 ≫ F.idem.e
        rw [Cat.id_comp, Cat.assoc, hFidem]⟩
  refine ⟨C, legF, legG, ?_, ?_, ?_⟩
  · -- Simple legF:  legF° ≫ legF ⊑ id_E.
    unfold Simple; rw [splLe_iff]
    show (F0 ≫ E.idem.e)° ≫ (F0 ≫ E.idem.e) ⊑ E.idem.e
    rw [Allegory.recip_comp, hEsym]
    calc (E.idem.e ≫ F0°) ≫ F0 ≫ E.idem.e
        = E.idem.e ≫ (F0° ≫ F0) ≫ E.idem.e := by simp only [Cat.assoc]
      _ ⊑ E.idem.e ≫ Cat.id E.carrier ≫ E.idem.e := comp_mono_left _ (comp_mono_right hF0 _)
      _ = E.idem.e := by rw [Cat.id_comp, hEidem]
  · -- Simple legG.
    unfold Simple; rw [splLe_iff]
    show (G0 ≫ F.idem.e)° ≫ (G0 ≫ F.idem.e) ⊑ F.idem.e
    rw [Allegory.recip_comp, hFsym]
    calc (F.idem.e ≫ G0°) ≫ G0 ≫ F.idem.e
        = F.idem.e ≫ (G0° ≫ G0) ≫ F.idem.e := by simp only [Cat.assoc]
      _ ⊑ F.idem.e ≫ Cat.id F.carrier ≫ F.idem.e := comp_mono_left _ (comp_mono_right hG0 _)
      _ = F.idem.e := by rw [Cat.id_comp, hFidem]
  · -- Ψ = legF° ≫ legG.
    apply SplHom.ext
    show Ψ.R = ((splRecip legF) ≫ legG).R
    show Ψ.R = (F0 ≫ E.idem.e)° ≫ (G0 ≫ F.idem.e)
    rw [Allegory.recip_comp, hEsym]
    have hfix : E.idem.e ≫ Ψ.R ≫ F.idem.e = Ψ.R := Ψ.fixed
    calc Ψ.R = E.idem.e ≫ Ψ.R ≫ F.idem.e := hfix.symm
      _ = E.idem.e ≫ (F0° ≫ G0) ≫ F.idem.e := by rw [hUfac]
      _ = (E.idem.e ≫ F0°) ≫ (G0 ≫ F.idem.e) := by simp only [Cat.assoc]

/-! ### §2.16(10) assembly — `TabularAllegory (SplObj 𝒜)` for semi-simple `𝒜`. -/

/-- **§2.16(10) (the keystone)**: if `𝒜` is a SEMI-SIMPLE allegory then the full
    splitting completion `SplObj 𝒜` — which splits *all* symmetric idempotents — is a
    TABULAR allegory.  (Freyd §2.16(10): `PM(RI)` is tabular iff `𝒜` is semi-simple;
    this is the substantive "if".  A merely tabular `𝒜` does NOT suffice — that gives
    only the coreflexive reflection `SplCorObj 𝒜` below.)

    Assembled from the two ingredients via `tabular_of_semiSimple_splits`:
    `splObj_semiSimple` (every morphism semi-simple) and `splObj_splitsSymmIdem`
    (every symmetric idempotent splits, weak leg). -/
instance splObj_tabular_of_semiSimple {𝒜 : Type u} [SemiSimpleAllegory 𝒜] :
    TabularAllegory (SplObj 𝒜) :=
  { instAllegorySpl with
    tabular := fun {_E _F} Ψ =>
      tabular_of_semiSimple_splits (fun R => splObj_semiSimple R) splObj_splitsSymmIdem Ψ }

/-- **§2.16(10) corollary**: `SplObj 𝒜` is tabular whenever `𝒜` is TABULAR — since every
    tabular allegory is semi-simple (`tabular_is_semiSimple`), the keystone applies.  Combined
    with `§2.169` (every equivalence relation of `SplObj 𝒜` splits), `SplObj 𝒜` is the
    *effective tabular* completion of a tabular allegory — the allegory side of the effective
    reflection of a regular category. -/
def splObj_tabular_of_tabular {𝒜 : Type u} [TabularAllegory 𝒜] :
    TabularAllegory (SplObj 𝒜) :=
  letI := semiSimpleAllegory_of_tabular (ℬ := 𝒜)
  splObj_tabular_of_semiSimple

/-! ### §2.16(10) FORWARD — `TabularAllegory (SplObj 𝒜) → SemiSimpleAllegory 𝒜`

  Freyd §2.16(10), the other implication: if the full splitting completion `SplObj 𝒜`
  (split ALL symmetric idempotents) is tabular, then `𝒜` is semi-simple.

  Given `R : a ⟶ b` in `𝒜`, embed it as `embHom R : embObj a ⟶ embObj b` and TABULATE it
  in `SplObj 𝒜`: an apex `C` and MAPS `P : C ⟶ embObj a`, `Q : C ⟶ embObj b` with
  `embHom R = P° ≫ Q` and `P≫P° ∩ Q≫Q° = id_C`.  Underlying, `R = P.R° ≫ Q.R` with
  `P.R, Q.R : C.carrier ⟶ a, b`.

  The apex/carrier reconciliation (the old marker's worry): simplicity of the legs is read
  off the CODOMAIN object, and the codomains `embObj a`, `embObj b` carry the IDENTITY
  idempotent (`1_a`, `1_b`).  So `Simple P` in `SplObj` — `P° ≫ P ⊑ id_{embObj a}` — descends
  via `splLe_iff` to `P.R° ≫ P.R ⊑ 1_a`, i.e. `Simple P.R` in `𝒜` AT THE CARRIER LEVEL (no
  apex idempotent intrudes, because `Simple F := F°≫F ⊑ id_{cod}` and the cod identity is
  `1_a`).  Hence `F = P.R`, `G = Q.R` are simple in `𝒜` with `R = F°≫G` — exactly `SemiSimple R`.
  (The apex `C.idem.e` only constrains the SOURCE, which `SemiSimple` does not test.) -/

/-- **§2.16(10) forward (per morphism)**: if every morphism of `SplObj 𝒜` is tabular
    (the `Tabular` predicate over the canonical `instAllegorySpl`) then every `R : a ⟶ b`
    of `𝒜` is semi-simple.  Tabulate `embHom R`; the legs' underlying morphisms are simple
    in `𝒜` because the embedded codomains carry the identity idempotent (`splLe_iff`).

    Stated against the `Tabular` predicate rather than `[TabularAllegory (SplObj 𝒜)]` so it
    is independent of which `Cat (SplObj 𝒜)` an ambient instance carries — the canonical
    `splObj_tabular_of_semiSimple` supplies `htab` via `TabularAllegory.tabular`. -/
theorem semiSimple_of_splObj_tabular {𝒜 : Type u} [Allegory 𝒜]
    (htab : ∀ {E F : SplObj 𝒜} (Ψ : E ⟶ F), Tabular Ψ)
    {a b : 𝒜} (R : a ⟶ b) : SemiSimple R := by
  obtain ⟨C, P, Q, hPmap, hQmap, hRfac, _hjoint⟩ := htab (embHom R)
  -- Legs simple in `𝒜`: `Simple P` in `SplObj` is `P° ≫ P ⊑ id_{embObj a}`; via `splLe_iff`
  -- the underlying is `P.R° ≫ P.R ⊑ (Cat.id (embObj a)).R = Cat.id a` — `Simple P.R` in `𝒜`.
  have hFsimple : Simple P.R := (splLe_iff (P° ≫ P) (Cat.id (embObj a))).mp hPmap.2
  have hGsimple : Simple Q.R := (splLe_iff (Q° ≫ Q) (Cat.id (embObj b))).mp hQmap.2
  -- `R = P.R° ≫ Q.R`:  `embHom R = P° ≫ Q` underlies as `R = P.R° ≫ Q.R` (`(embHom R).R = R`).
  have hR : R = P.R° ≫ Q.R := congrArg SplHom.R hRfac
  exact ⟨C.carrier, P.R, Q.R, hFsimple, hGsimple, hR⟩

/-- **§2.16(10) forward**: if the full splitting completion `SplObj 𝒜` is tabular (canonical
    instance) then `𝒜` is a SEMI-SIMPLE allegory.  Combined with `splObj_tabular_of_semiSimple`
    (backward), this is Freyd's biconditional `SplObj 𝒜` tabular ↔ `𝒜` semi-simple. -/
def semiSimpleAllegory_of_splObj_tabular {𝒜 : Type u} [Allegory 𝒜]
    (htab : ∀ {E F : SplObj 𝒜} (Ψ : E ⟶ F), Tabular Ψ) : SemiSimpleAllegory 𝒜 where
  semi_simple R := semiSimple_of_splObj_tabular htab R

/-! ## §2.21  `SplObj 𝒜` is a DISTRIBUTIVE allegory (pointwise union/zero)

  Freyd §2.21: union and zero of `SplObj 𝒜` are read off the underlying `𝒜`-morphisms.
  For parallel `Φ Ψ : E ⟶ F` the union is `Φ.R ∪ Ψ.R` (fixed since `E.e ≫ (Φ.R∪Ψ.R) ≫ F.e
  = (E.e≫Φ.R≫F.e) ∪ (E.e≫Ψ.R≫F.e) = Φ.R ∪ Ψ.R` by `union_comp_distrib`/`comp_union_distrib`,
  each leg fixed); zero is `𝟘` (fixed since `E.e≫𝟘≫F.e = 𝟘`).  All distributive-allegory
  laws descend pointwise from `[DistributiveAllegory 𝒜]` via `SplHom.ext`. -/

/-- Pointwise union of two parallel split-homs: underlying `Φ.R ∪ Ψ.R`, fixed because
    `E.e ≫ (Φ.R∪Ψ.R) ≫ F.e` distributes into `(E.e≫Φ.R≫F.e) ∪ (E.e≫Ψ.R≫F.e) = Φ.R ∪ Ψ.R`. -/
def splUnion {𝒜 : Type u} [DistributiveAllegory 𝒜] {E F : SplObj 𝒜} (Φ Ψ : E ⟶ F) : E ⟶ F :=
  ⟨Φ.R ∪ Ψ.R, by
    rw [union_comp_distrib, DistributiveAllegory.comp_union_distrib, Φ.fixed, Ψ.fixed]⟩

/-- The zero split-hom `E ⟶ F`: underlying `𝟘`, fixed because `E.e ≫ 𝟘 ≫ F.e = 𝟘`. -/
def splZero {𝒜 : Type u} [DistributiveAllegory 𝒜] {E F : SplObj 𝒜} : E ⟶ F :=
  ⟨𝟘, by rw [DistributiveAllegory.zero_comp, DistributiveAllegory.comp_zero]⟩

/-- **§2.21**: if `𝒜` is a DISTRIBUTIVE allegory then so is `SplObj 𝒜`, with union and
    zero taken pointwise on the underlying `𝒜`-morphisms (`splUnion`, `splZero`).  Every
    distributive law reduces to the base `[DistributiveAllegory 𝒜]` law via `SplHom.ext`. -/
instance instDistributiveSpl {𝒜 : Type u} [DistributiveAllegory 𝒜] :
    DistributiveAllegory (SplObj 𝒜) :=
  { instAllegorySpl with
    zero := splZero
    union := splUnion
    zero_comp := fun R => by
      apply SplHom.ext; show (𝟘 : _ ⟶ _) ≫ R.R = 𝟘; exact DistributiveAllegory.zero_comp _
    comp_zero := fun R => by
      apply SplHom.ext; show R.R ≫ (𝟘 : _ ⟶ _) = 𝟘; exact DistributiveAllegory.comp_zero _
    union_idem := fun R => by
      apply SplHom.ext; show R.R ∪ R.R = R.R; exact DistributiveAllegory.union_idem _
    union_comm := fun R S => by
      apply SplHom.ext; show R.R ∪ S.R = S.R ∪ R.R; exact DistributiveAllegory.union_comm _ _
    union_assoc := fun R S T => by
      apply SplHom.ext; show R.R ∪ (S.R ∪ T.R) = (R.R ∪ S.R) ∪ T.R
      exact DistributiveAllegory.union_assoc _ _ _
    union_inter_absorb := fun R S => by
      apply SplHom.ext; show R.R ∪ (S.R ∩ R.R) = R.R; exact DistributiveAllegory.union_inter_absorb _ _
    inter_union_absorb := fun R S => by
      apply SplHom.ext; show (R.R ∪ S.R) ∩ R.R = R.R; exact DistributiveAllegory.inter_union_absorb _ _
    comp_union_distrib := fun R S T => by
      apply SplHom.ext; show R.R ≫ (S.R ∪ T.R) = (R.R ≫ S.R) ∪ (R.R ≫ T.R)
      exact DistributiveAllegory.comp_union_distrib _ _ _
    inter_union_distrib := fun R S T => by
      apply SplHom.ext; show R.R ∩ (S.R ∪ T.R) = (R.R ∩ S.R) ∪ (R.R ∩ T.R)
      exact DistributiveAllegory.inter_union_distrib _ _ _
    zero_union := fun R => by
      apply SplHom.ext; show (𝟘 : _ ⟶ _) ∪ R.R = R.R; exact DistributiveAllegory.zero_union _ }

/-! ## §2.15  `SplObj 𝒜` is a UNITARY allegory

  Freyd §2.15: the unit object of `SplObj 𝒜` is the embedded base unit `⟨λ, 1_λ⟩` (the
  unit `λ` with its identity idempotent — `1_λ` is coreflexive, so this IS a SplObj).

    • PartialUnit `⟨λ,1⟩`: any `Φ : ⟨λ,1⟩ ⟶ ⟨λ,1⟩` has underlying `Φ.R : λ⟶λ ⊑ 1_λ`
      (base `PartialUnit λ`), and `Φ ⊑ id` in `SplObj` is exactly `Φ.R ⊑ 1_λ` (`splLe_iff`,
      with `id_{⟨λ,1⟩}.R = 1_λ`).
    • Entire-to-unit: for any `E = ⟨a,e⟩`, the base entire `p : a ⟶ λ` gives the SplHom
      `legP = ⟨e ≫ p, …⟩ : E ⟶ ⟨λ,1⟩` (fixed: `e≫(e≫p)≫1 = e≫p`).  It is `Entire` AGAINST
      the OBJECT idempotent `e = id_E`: `dom legP = id_E`, i.e. `e ∩ (e≫p)≫(e≫p)° = e`,
      which holds because base-entire `p` gives `1_a ⊑ p≫p°`, hence `e ⊑ e≫(p≫p°)≫e`. -/

/-- The unit object of `SplObj 𝒜`: the embedded base unit `⟨λ, 1_λ⟩`. -/
def splUnitObj (𝒜 : Type u) [UnitaryAllegory 𝒜] : SplObj 𝒜 :=
  embObj (UnitaryAllegory.unit_obj (𝒜 := 𝒜))

/-- `⟨λ,1⟩` is a partial unit of `SplObj 𝒜`: every endomorphism is `⊑ id`, because its
    underlying `λ⟶λ` morphism is `⊑ 1_λ` by the base `PartialUnit λ`. -/
theorem splUnit_partialUnit {𝒜 : Type u} [UnitaryAllegory 𝒜] :
    PartialUnit (splUnitObj 𝒜) := by
  intro Φ
  have hPU : PartialUnit (UnitaryAllegory.unit_obj (𝒜 := 𝒜)) := UnitaryAllegory.unit_prop.1
  -- `Φ ⊑ id_{⟨λ,1⟩}` is `Φ.R ⊑ (splId _).R = 1_λ`; base PartialUnit gives `Φ.R ⊑ 1_λ`.
  rw [splLe_iff]; exact hPU Φ.R

/-- Every object `E = ⟨a,e⟩` of `SplObj 𝒜` is the source of an ENTIRE split-hom to the
    unit `⟨λ,1⟩` (entire against the OBJECT idempotent `e = id_E`, not `1_a`).
    Take the base entire `p : a ⟶ λ` and absorb the object idempotent: `legP = e ≫ p`. -/
theorem splUnit_entire {𝒜 : Type u} [UnitaryAllegory 𝒜] (E : SplObj 𝒜) :
    ∃ (P : E ⟶ splUnitObj 𝒜), Entire P := by
  obtain ⟨p, hpEntire⟩ :=
    UnitaryAllegory.unit_prop.2 E.carrier
  have hesym : E.idem.e° = E.idem.e := E.idem.sym
  have heidem : E.idem.e ≫ E.idem.e = E.idem.e := E.idem.idem
  -- Base entire `p`: `1_a ⊑ p ≫ p°`.
  have hpp : Cat.id E.carrier ⊑ p ≫ p° := by
    have := hpEntire; unfold Entire dom at this; exact this ▸ inter_lb_right _ _
  -- SplHom `legP = ⟨e ≫ p, …⟩ : E ⟶ ⟨λ,1⟩` (right idempotent `1_λ` absorbs trivially).
  let legP : E ⟶ splUnitObj 𝒜 := ⟨E.idem.e ≫ p, by
        show E.idem.e ≫ (E.idem.e ≫ p) ≫ Cat.id (UnitaryAllegory.unit_obj) = E.idem.e ≫ p
        rw [Cat.comp_id, ← Cat.assoc, heidem]⟩
  refine ⟨legP, ?_⟩
  -- Entire legP in SplObj: `dom legP = id_E`, i.e. `e ∩ (e≫p)≫(e≫p)° = e`.
  unfold Entire dom; apply SplHom.ext
  show E.idem.e ∩ (E.idem.e ≫ p) ≫ (E.idem.e ≫ p)° = E.idem.e
  -- (e≫p)≫(e≫p)° = e≫(p≫p°)≫e  (e symmetric);  e ⊑ e≫(p≫p°)≫e  (1 ⊑ p≫p°).
  have hPP : (E.idem.e ≫ p) ≫ (E.idem.e ≫ p)° = E.idem.e ≫ (p ≫ p°) ≫ E.idem.e := by
    rw [Allegory.recip_comp, hesym]; simp only [Cat.assoc]
  have hEnt : E.idem.e ⊑ (E.idem.e ≫ p) ≫ (E.idem.e ≫ p)° := by
    rw [hPP]
    calc E.idem.e = E.idem.e ≫ Cat.id E.carrier ≫ E.idem.e := by rw [Cat.id_comp, heidem]
      _ ⊑ E.idem.e ≫ (p ≫ p°) ≫ E.idem.e := comp_mono_left _ (comp_mono_right hpp _)
  exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hEnt)

/-- **§2.15**: if `𝒜` is a UNITARY allegory then so is `SplObj 𝒜`, with unit object the
    embedded base unit `⟨λ, 1_λ⟩` (`splUnitObj`). -/
noncomputable instance instUnitarySpl {𝒜 : Type u} [UnitaryAllegory 𝒜] :
    UnitaryAllegory (SplObj 𝒜) :=
  { instAllegorySpl with
    unit_obj := splUnitObj 𝒜
    unit_prop := ⟨splUnit_partialUnit, splUnit_entire⟩ }

/-! ## §2.215  `SplObj 𝒜` is a POSITIVE allegory (block-diagonal coproduct)

  Freyd §2.215: the coproduct of `E = ⟨a,e⟩, F = ⟨b,f⟩` in `SplObj 𝒜` is built on the base
  coproduct `coprod a b` (injections `u₁ : a ⟶ coprod a b`, `u₂ : b ⟶ coprod a b`).  The
  apex object carries the BLOCK-DIAGONAL symmetric idempotent

      D = u₁°≫e≫u₁ ∪ u₂°≫f≫u₂   on   coprod a b,

  with SplObj injections `U₁ = e≫u₁ : E ⟶ ⟨coprod a b, D⟩`, `U₂ = f≫u₂ : F ⟶ …`.
  The base coproduct equations (`u₁u₁°=1`, `u₁u₂°=0`, `u₂u₁°=0`, `u₂u₂°=1`, `e,f` sym+idem)
  make the five §2.214 `Coproduct` equations lift verbatim:
    `U₁U₁° = e(u₁u₁°)e = e = id_E`,  `U₁U₂° = e(u₁u₂°)f = 0`,  `U₂U₁° = 0`,
    `U₂U₂° = f = id_F`,  `U₁°U₁ ∪ U₂°U₂ = u₁°eu₁ ∪ u₂°fu₂ = D = id_C`. -/

/-- The block-diagonal symmetric idempotent `D = u₁°eu₁ ∪ u₂°fu₂` on `coprod a b`, the
    apex carrier of the `SplObj 𝒜` coproduct of `E = ⟨a,e⟩` and `F = ⟨b,f⟩`. -/
def splCoprodIdem {𝒜 : Type u} [PositiveAllegory 𝒜] (E F : SplObj 𝒜) :
    SymIdem (PositiveAllegory.coprod E.carrier F.carrier) :=
  let cp := PositiveAllegory.has_coproduct E.carrier F.carrier
  { e := (cp.u₁° ≫ E.idem.e ≫ cp.u₁) ∪ (cp.u₂° ≫ F.idem.e ≫ cp.u₂)
    sym := by
      -- D° = (u₁°eu₁)° ∪ (u₂°fu₂)°  (recip_union flips, then ∪-comm);  e,f symmetric.
      show ((cp.u₁° ≫ E.idem.e ≫ cp.u₁) ∪ (cp.u₂° ≫ F.idem.e ≫ cp.u₂))° = _
      rw [recip_union]
      simp only [Allegory.recip_comp, Allegory.recip_recip, E.idem.sym, F.idem.sym, Cat.assoc,
        DistributiveAllegory.union_comm]
    idem := by
      -- D≫D: diagonal terms reproduce, cross terms vanish (u₁u₂°=0, u₂u₁°=0).
      show ((cp.u₁° ≫ E.idem.e ≫ cp.u₁) ∪ (cp.u₂° ≫ F.idem.e ≫ cp.u₂)) ≫
           ((cp.u₁° ≫ E.idem.e ≫ cp.u₁) ∪ (cp.u₂° ≫ F.idem.e ≫ cp.u₂))
        = (cp.u₁° ≫ E.idem.e ≫ cp.u₁) ∪ (cp.u₂° ≫ F.idem.e ≫ cp.u₂)
      rw [union_comp_distrib, DistributiveAllegory.comp_union_distrib,
          DistributiveAllegory.comp_union_distrib]
      -- four terms; rewrite each via the coproduct equations.
      have t11 : (cp.u₁° ≫ E.idem.e ≫ cp.u₁) ≫ (cp.u₁° ≫ E.idem.e ≫ cp.u₁)
          = cp.u₁° ≫ E.idem.e ≫ cp.u₁ := by
        calc (cp.u₁° ≫ E.idem.e ≫ cp.u₁) ≫ (cp.u₁° ≫ E.idem.e ≫ cp.u₁)
            = cp.u₁° ≫ E.idem.e ≫ (cp.u₁ ≫ cp.u₁°) ≫ E.idem.e ≫ cp.u₁ := by
                simp only [Cat.assoc]
          _ = cp.u₁° ≫ E.idem.e ≫ E.idem.e ≫ cp.u₁ := by rw [cp.u₁_self_comp_recip, Cat.id_comp]
          _ = cp.u₁° ≫ E.idem.e ≫ cp.u₁ := by rw [← Cat.assoc E.idem.e E.idem.e cp.u₁, E.idem.idem]
      have t12 : (cp.u₁° ≫ E.idem.e ≫ cp.u₁) ≫ (cp.u₂° ≫ F.idem.e ≫ cp.u₂) = 𝟘 := by
        calc (cp.u₁° ≫ E.idem.e ≫ cp.u₁) ≫ (cp.u₂° ≫ F.idem.e ≫ cp.u₂)
            = cp.u₁° ≫ E.idem.e ≫ (cp.u₁ ≫ cp.u₂°) ≫ F.idem.e ≫ cp.u₂ := by simp only [Cat.assoc]
          _ = cp.u₁° ≫ E.idem.e ≫ 𝟘 ≫ F.idem.e ≫ cp.u₂ := by rw [cp.u₁_u₂_recip]
          _ = 𝟘 := by rw [DistributiveAllegory.zero_comp, DistributiveAllegory.comp_zero,
                          DistributiveAllegory.comp_zero]
      have t21 : (cp.u₂° ≫ F.idem.e ≫ cp.u₂) ≫ (cp.u₁° ≫ E.idem.e ≫ cp.u₁) = 𝟘 := by
        calc (cp.u₂° ≫ F.idem.e ≫ cp.u₂) ≫ (cp.u₁° ≫ E.idem.e ≫ cp.u₁)
            = cp.u₂° ≫ F.idem.e ≫ (cp.u₂ ≫ cp.u₁°) ≫ E.idem.e ≫ cp.u₁ := by simp only [Cat.assoc]
          _ = cp.u₂° ≫ F.idem.e ≫ 𝟘 ≫ E.idem.e ≫ cp.u₁ := by rw [cp.u₂_u₁_recip]
          _ = 𝟘 := by rw [DistributiveAllegory.zero_comp, DistributiveAllegory.comp_zero,
                          DistributiveAllegory.comp_zero]
      have t22 : (cp.u₂° ≫ F.idem.e ≫ cp.u₂) ≫ (cp.u₂° ≫ F.idem.e ≫ cp.u₂)
          = cp.u₂° ≫ F.idem.e ≫ cp.u₂ := by
        calc (cp.u₂° ≫ F.idem.e ≫ cp.u₂) ≫ (cp.u₂° ≫ F.idem.e ≫ cp.u₂)
            = cp.u₂° ≫ F.idem.e ≫ (cp.u₂ ≫ cp.u₂°) ≫ F.idem.e ≫ cp.u₂ := by simp only [Cat.assoc]
          _ = cp.u₂° ≫ F.idem.e ≫ F.idem.e ≫ cp.u₂ := by rw [cp.u₂_self_comp_recip, Cat.id_comp]
          _ = cp.u₂° ≫ F.idem.e ≫ cp.u₂ := by rw [← Cat.assoc F.idem.e F.idem.e cp.u₂, F.idem.idem]
      show ((cp.u₁° ≫ E.idem.e ≫ cp.u₁) ≫ (cp.u₁° ≫ E.idem.e ≫ cp.u₁) ∪
            (cp.u₁° ≫ E.idem.e ≫ cp.u₁) ≫ (cp.u₂° ≫ F.idem.e ≫ cp.u₂)) ∪
           ((cp.u₂° ≫ F.idem.e ≫ cp.u₂) ≫ (cp.u₁° ≫ E.idem.e ≫ cp.u₁) ∪
            (cp.u₂° ≫ F.idem.e ≫ cp.u₂) ≫ (cp.u₂° ≫ F.idem.e ≫ cp.u₂)) = _
      rw [t11, t12, t21, t22, union_zero, DistributiveAllegory.zero_union] }

/-- The `SplObj 𝒜` coproduct diagram of `E, F`: apex `⟨coprod a b, D⟩` with the block-diagonal
    idempotent `D`, injections `U₁ = e≫u₁`, `U₂ = f≫u₂`.  The five §2.214 equations lift from
    the base coproduct equations. -/
def splCoproduct {𝒜 : Type u} [PositiveAllegory 𝒜] (E F : SplObj 𝒜) :
    Coproduct (𝒜 := SplObj 𝒜) ⟨PositiveAllegory.coprod E.carrier F.carrier, splCoprodIdem E F⟩ E F :=
  let cp := PositiveAllegory.has_coproduct E.carrier F.carrier
  let C : SplObj 𝒜 := ⟨PositiveAllegory.coprod E.carrier F.carrier, splCoprodIdem E F⟩
  -- U₁ : E ⟶ C with underlying `e ≫ u₁` (fixed: e≫(e≫u₁)≫D = e≫u₁ since u₁≫D = e≫u₁).
  let U₁ : E ⟶ C := ⟨E.idem.e ≫ cp.u₁, by
        show E.idem.e ≫ (E.idem.e ≫ cp.u₁) ≫ (splCoprodIdem E F).e = E.idem.e ≫ cp.u₁
        show E.idem.e ≫ (E.idem.e ≫ cp.u₁) ≫
              ((cp.u₁° ≫ E.idem.e ≫ cp.u₁) ∪ (cp.u₂° ≫ F.idem.e ≫ cp.u₂)) = E.idem.e ≫ cp.u₁
        rw [DistributiveAllegory.comp_union_distrib]
        have h1 : (E.idem.e ≫ cp.u₁) ≫ (cp.u₁° ≫ E.idem.e ≫ cp.u₁)
            = E.idem.e ≫ cp.u₁ := by
          calc (E.idem.e ≫ cp.u₁) ≫ (cp.u₁° ≫ E.idem.e ≫ cp.u₁)
              = E.idem.e ≫ (cp.u₁ ≫ cp.u₁°) ≫ E.idem.e ≫ cp.u₁ := by simp only [Cat.assoc]
            _ = E.idem.e ≫ E.idem.e ≫ cp.u₁ := by rw [cp.u₁_self_comp_recip, Cat.id_comp]
            _ = E.idem.e ≫ cp.u₁ := by rw [← Cat.assoc E.idem.e E.idem.e cp.u₁, E.idem.idem]
        have h2 : (E.idem.e ≫ cp.u₁) ≫ (cp.u₂° ≫ F.idem.e ≫ cp.u₂) = 𝟘 := by
          calc (E.idem.e ≫ cp.u₁) ≫ (cp.u₂° ≫ F.idem.e ≫ cp.u₂)
              = E.idem.e ≫ (cp.u₁ ≫ cp.u₂°) ≫ F.idem.e ≫ cp.u₂ := by simp only [Cat.assoc]
            _ = E.idem.e ≫ 𝟘 ≫ F.idem.e ≫ cp.u₂ := by rw [cp.u₁_u₂_recip]
            _ = 𝟘 := by rw [DistributiveAllegory.zero_comp, DistributiveAllegory.comp_zero]
        rw [h1, h2, union_zero, ← Cat.assoc, E.idem.idem]⟩
  let U₂ : F ⟶ C := ⟨F.idem.e ≫ cp.u₂, by
        show F.idem.e ≫ (F.idem.e ≫ cp.u₂) ≫
              ((cp.u₁° ≫ E.idem.e ≫ cp.u₁) ∪ (cp.u₂° ≫ F.idem.e ≫ cp.u₂)) = F.idem.e ≫ cp.u₂
        rw [DistributiveAllegory.comp_union_distrib]
        have h1 : (F.idem.e ≫ cp.u₂) ≫ (cp.u₁° ≫ E.idem.e ≫ cp.u₁) = 𝟘 := by
          calc (F.idem.e ≫ cp.u₂) ≫ (cp.u₁° ≫ E.idem.e ≫ cp.u₁)
              = F.idem.e ≫ (cp.u₂ ≫ cp.u₁°) ≫ E.idem.e ≫ cp.u₁ := by simp only [Cat.assoc]
            _ = F.idem.e ≫ 𝟘 ≫ E.idem.e ≫ cp.u₁ := by rw [cp.u₂_u₁_recip]
            _ = 𝟘 := by rw [DistributiveAllegory.zero_comp, DistributiveAllegory.comp_zero]
        have h2 : (F.idem.e ≫ cp.u₂) ≫ (cp.u₂° ≫ F.idem.e ≫ cp.u₂) = F.idem.e ≫ cp.u₂ := by
          calc (F.idem.e ≫ cp.u₂) ≫ (cp.u₂° ≫ F.idem.e ≫ cp.u₂)
              = F.idem.e ≫ (cp.u₂ ≫ cp.u₂°) ≫ F.idem.e ≫ cp.u₂ := by simp only [Cat.assoc]
            _ = F.idem.e ≫ F.idem.e ≫ cp.u₂ := by rw [cp.u₂_self_comp_recip, Cat.id_comp]
            _ = F.idem.e ≫ cp.u₂ := by rw [← Cat.assoc F.idem.e F.idem.e cp.u₂, F.idem.idem]
        rw [h1, h2, DistributiveAllegory.zero_union, ← Cat.assoc, F.idem.idem]⟩
  { u₁ := U₁
    u₂ := U₂
    -- U₁≫U₁° = id_E:  underlying  (e≫u₁)(u₁°≫e) = e(u₁u₁°)e = e·1·e = e.
    u₁_self_comp_recip := by
      apply SplHom.ext
      show (E.idem.e ≫ cp.u₁) ≫ (E.idem.e ≫ cp.u₁)° = E.idem.e
      rw [Allegory.recip_comp, E.idem.sym]; simp only [Cat.assoc]
      rw [← Cat.assoc cp.u₁ cp.u₁° E.idem.e, cp.u₁_self_comp_recip, Cat.id_comp, E.idem.idem]
    -- U₁≫U₂° = 0:  (e≫u₁)(u₂°≫f) = e(u₁u₂°)f = e·0·f = 0.
    u₁_u₂_recip := by
      apply SplHom.ext
      show (E.idem.e ≫ cp.u₁) ≫ (F.idem.e ≫ cp.u₂)° = 𝟘
      rw [Allegory.recip_comp, F.idem.sym]; simp only [Cat.assoc]
      rw [← Cat.assoc cp.u₁ cp.u₂° F.idem.e, cp.u₁_u₂_recip, DistributiveAllegory.zero_comp,
          DistributiveAllegory.comp_zero]
    -- U₂≫U₁° = 0.
    u₂_u₁_recip := by
      apply SplHom.ext
      show (F.idem.e ≫ cp.u₂) ≫ (E.idem.e ≫ cp.u₁)° = 𝟘
      rw [Allegory.recip_comp, E.idem.sym]; simp only [Cat.assoc]
      rw [← Cat.assoc cp.u₂ cp.u₁° E.idem.e, cp.u₂_u₁_recip, DistributiveAllegory.zero_comp,
          DistributiveAllegory.comp_zero]
    -- U₂≫U₂° = id_F = f.
    u₂_self_comp_recip := by
      apply SplHom.ext
      show (F.idem.e ≫ cp.u₂) ≫ (F.idem.e ≫ cp.u₂)° = F.idem.e
      rw [Allegory.recip_comp, F.idem.sym]; simp only [Cat.assoc]
      rw [← Cat.assoc cp.u₂ cp.u₂° F.idem.e, cp.u₂_self_comp_recip, Cat.id_comp, F.idem.idem]
    -- (U₁°≫U₁) ∪ (U₂°≫U₂) = id_C = D.
    recip_union_eq_id := by
      apply SplHom.ext
      show ((E.idem.e ≫ cp.u₁)° ≫ (E.idem.e ≫ cp.u₁)) ∪ ((F.idem.e ≫ cp.u₂)° ≫ (F.idem.e ≫ cp.u₂))
        = (cp.u₁° ≫ E.idem.e ≫ cp.u₁) ∪ (cp.u₂° ≫ F.idem.e ≫ cp.u₂)
      rw [Allegory.recip_comp, Allegory.recip_comp, E.idem.sym, F.idem.sym]
      simp only [Cat.assoc]
      rw [← Cat.assoc E.idem.e E.idem.e cp.u₁, E.idem.idem,
          ← Cat.assoc F.idem.e F.idem.e cp.u₂, F.idem.idem] }

/-- **§2.215**: if `𝒜` is a POSITIVE allegory then so is `SplObj 𝒜`.  The coproduct of
    `E = ⟨a,e⟩, F = ⟨b,f⟩` is the apex `⟨coprod a b, D⟩` with the block-diagonal symmetric
    idempotent `D = u₁°eu₁ ∪ u₂°fu₂` and injections `U₁ = e≫u₁`, `U₂ = f≫u₂` (`splCoproduct`).
    The coterminal object is the embedded base `coterm`. -/
noncomputable instance instPositiveSpl {𝒜 : Type u} [PositiveAllegory 𝒜] :
    PositiveAllegory (SplObj 𝒜) :=
  { instDistributiveSpl with
    coterm := embObj PositiveAllegory.coterm
    coprod := fun E F => ⟨PositiveAllegory.coprod E.carrier F.carrier, splCoprodIdem E F⟩
    has_coproduct := fun E F => splCoproduct E F }

/-! ## §2.169  `SplObj 𝒜` is an EFFECTIVE allegory

  Freyd §2.169: an effective allegory is one in which every EQUIVALENCE RELATION splits.
  `SplObj 𝒜` splits all symmetric idempotents (`spl_equivalence_splits_map`); for a
  REFLEXIVE one (an equivalence relation) the splitting leg is a MAP — exactly the
  `EffectiveAllegory.split_symmetric_idempotent` shape.  Combined with
  `splObj_tabular_of_semiSimple` (tabular for semi-simple `𝒜`), this packages
  `EffectiveAllegory (SplObj 𝒜)`. -/

/-- **§2.169 (effective-shape lemma)**: a reflexive symmetric idempotent `Φ : E ⟶ E` of
    `SplObj 𝒜` — i.e. an equivalence relation — splits with a MAP leg.  Translates the
    category-level `Reflexive Φ` (`id_E ⊑ Φ`, where `id_E` underlies as `E.idem.e`),
    `Symmetric Φ` (`Φ° ⊑ Φ`, giving `Φ.R° = Φ.R`) and idempotency `Φ≫Φ=Φ` (giving
    `Φ.R≫Φ.R=Φ.R`) into the hypotheses of `spl_effective`. -/
theorem splObj_split_equivalence {𝒜 : Type u} [Allegory 𝒜] {E : SplObj 𝒜} (Φ : E ⟶ E)
    (hrefl : Reflexive Φ) (hsym : Symmetric Φ) (hidem : Φ ≫ Φ = Φ) :
    ∃ (G : SplObj 𝒜) (f : E ⟶ G), Map f ∧ f ≫ f° = Φ ∧ f° ≫ f = Cat.id G := by
  -- Reflexive Φ : id_E ⊑ Φ, i.e. (splId E) ⊑ Φ; via splLe_iff this is E.idem.e ⊑ Φ.R.
  have hreflR : E.idem.e ⊑ Φ.R := (splLe_iff (splId E) Φ).mp hrefl
  -- Symmetric Φ : Φ° ⊑ Φ, i.e. Φ.R° ⊑ Φ.R; reciprocating gives Φ.R ⊑ Φ.R°, hence equality.
  have hsymR : Φ.R° = Φ.R := by
    have h1 : Φ.R° ⊑ Φ.R := (splLe_iff (Φ°) Φ).mp hsym
    have h2 : Φ.R ⊑ Φ.R° := by
      have := recip_mono h1; rwa [Allegory.recip_recip] at this
    exact le_antisymm h1 h2
  -- Idempotency: Φ ≫ Φ = Φ underlies as Φ.R ≫ Φ.R = Φ.R.
  have hidemR : Φ.R ≫ Φ.R = Φ.R := congrArg SplHom.R hidem
  exact spl_effective Φ hreflR hsymR hidemR

/-- **§2.169**: `SplObj 𝒜` is an EFFECTIVE allegory whenever `𝒜` is SEMI-SIMPLE — it is
    tabular (`splObj_tabular_of_semiSimple`) and every equivalence relation splits as a map
    (`splObj_split_equivalence`).  This is the §2.217(2) ingredient for the pre-topos target. -/
instance instEffectiveSpl {𝒜 : Type u} [SemiSimpleAllegory 𝒜] :
    EffectiveAllegory (SplObj 𝒜) :=
  { splObj_tabular_of_semiSimple with
    split_symmetric_idempotent := fun E hrefl hsym hidem =>
      splObj_split_equivalence E hrefl hsym hidem }

/-- **§2.169 (corollary)**: `SplObj 𝒜` is an EFFECTIVE allegory whenever `𝒜` is TABULAR
    (a tabular allegory is semi-simple, `semiSimpleAllegory_of_tabular`). -/
def splObj_effective_of_tabular {𝒜 : Type u} [TabularAllegory 𝒜] :
    EffectiveAllegory (SplObj 𝒜) :=
  letI := semiSimpleAllegory_of_tabular (ℬ := 𝒜)
  instEffectiveSpl

/-! ## §2.31  `SplObj 𝒜` is a DIVISION allegory (pointwise division)

  Freyd §2.31: right division descends to `SplObj 𝒜` pointwise.  For `Φ : E ⟶ G`,
  `Ψ : F ⟶ G` the quotient `Φ / Ψ : E ⟶ F` has underlying `E.e ≫ (Φ.R / Ψ.R) ≫ F.e`
  (the base division `Φ.R / Ψ.R`, re-fixed by the source/target idempotents `E.e, F.e`).
  The two §2.31 laws lift to the base laws:
    • `(Φ/Ψ)≫Ψ ⊑ Φ`:  underlying `E.e≫(Φ.R/Ψ.R)≫F.e≫Ψ.R = E.e≫(Φ.R/Ψ.R)≫Ψ.R`
      (`F.e≫Ψ.R = Ψ.R`, `Ψ.fixed_left`) `⊑ E.e≫Φ.R = Φ.R` (`div_comp_le`, `Φ.fixed_left`).
    • `T≫Ψ ⊑ Φ ⟹ T ⊑ Φ/Ψ`:  base `le_div` gives `T.R ⊑ Φ.R/Ψ.R`, then
      `T.R = E.e≫T.R≫F.e ⊑ E.e≫(Φ.R/Ψ.R)≫F.e` (`T.fixed`, monotone). -/

/-- Pointwise right division of split-homs: underlying `E.e ≫ (Φ.R / Ψ.R) ≫ F.e`, the base
    quotient re-fixed by the source/target idempotents (so the result is a genuine split-hom). -/
def splDiv {𝒜 : Type u} [DivisionAllegory 𝒜] {E F G : SplObj 𝒜} (Φ : E ⟶ G) (Ψ : F ⟶ G) :
    E ⟶ F :=
  ⟨E.idem.e ≫ (Φ.R / Ψ.R) ≫ F.idem.e, by
    show E.idem.e ≫ (E.idem.e ≫ (Φ.R / Ψ.R) ≫ F.idem.e) ≫ F.idem.e
        = E.idem.e ≫ (Φ.R / Ψ.R) ≫ F.idem.e
    simp only [Cat.assoc]
    rw [← Cat.assoc E.idem.e E.idem.e, E.idem.idem, F.idem.idem]⟩

/-- **§2.31**: if `𝒜` is a DIVISION allegory then so is `SplObj 𝒜`, with right division taken
    pointwise (`splDiv`).  Both §2.31 laws reduce to the base `div_comp_le` / `le_div`. -/
noncomputable instance instDivisionSpl {𝒜 : Type u} [DivisionAllegory 𝒜] :
    DivisionAllegory (SplObj 𝒜) :=
  { instDistributiveSpl with
    div := splDiv
    div_comp_le := fun {E F G} Φ Ψ => by
      rw [splLe_iff]
      show (E.idem.e ≫ (Φ.R / Ψ.R) ≫ F.idem.e) ≫ Ψ.R ⊑ Φ.R
      -- F.e ≫ Ψ.R = Ψ.R (Ψ.fixed_left), then div_comp_le, then E.e ≫ Φ.R = Φ.R (Φ.fixed_left).
      calc (E.idem.e ≫ (Φ.R / Ψ.R) ≫ F.idem.e) ≫ Ψ.R
          = E.idem.e ≫ (Φ.R / Ψ.R) ≫ (F.idem.e ≫ Ψ.R) := by simp only [Cat.assoc]
        _ = E.idem.e ≫ (Φ.R / Ψ.R) ≫ Ψ.R := by rw [Ψ.fixed_left]
        _ ⊑ E.idem.e ≫ Φ.R := comp_mono_left _ (DivisionAllegory.div_comp_le _ _)
        _ = Φ.R := Φ.fixed_left
    le_div := fun {E F G} T Φ Ψ h => by
      rw [splLe_iff] at h ⊢
      show T.R ⊑ E.idem.e ≫ (Φ.R / Ψ.R) ≫ F.idem.e
      have hbase : T.R ⊑ Φ.R / Ψ.R := DivisionAllegory.le_div T.R Φ.R Ψ.R h
      calc T.R = E.idem.e ≫ T.R ≫ F.idem.e := T.fixed.symm
        _ ⊑ E.idem.e ≫ (Φ.R / Ψ.R) ≫ F.idem.e :=
            comp_mono_left _ (comp_mono_right hbase _) }

/-- **§2.34**: the faithful embedding `A → PRel(E)` (`embHom`) PRESERVES DIVISION —
    `embHom (R/S) = splDiv (embHom R) (embHom S)` — so it is a faithful representation OF DIVISION
    ALLEGORIES (it already preserves `≫`/`°`/`∩`/`∪`).  On `embObj a` the idempotent is the identity
    (`idSymIdem`, `.e = 1`), so `splDiv`'s `E.e ≫ (R/S) ≫ F.e` collapses to `R/S`. -/
theorem embHom_div {𝒜 : Type u} [DivisionAllegory 𝒜] {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) :
    (embHom (R / S) : embObj a ⟶ embObj b) = splDiv (embHom R) (embHom S) := by
  apply SplHom.ext
  show R / S = (embObj a).idem.e ≫ ((embHom R).R / (embHom S).R) ≫ (embObj b).idem.e
  simp only [embObj, idSymIdem, embHom_R, Cat.id_comp, Cat.comp_id]

/-! ## Goal A — `EffectiveDivisionAllegory (SplObj 𝒜)` for a semi-simple division allegory

  Packages `instDivisionSpl` + `instEffectiveSpl` into the combined class.  The hypothesis
  uses `SemiSimpleDivisionAllegory 𝒜` (defined in S2_4.lean, extending BOTH `DivisionAllegory`
  and `SemiSimpleAllegory` from ONE shared `Allegory` base) to avoid the Lean 4 instance diamond
  that arises when `[DivisionAllegory 𝒜]` and `[SemiSimpleAllegory 𝒜]` are carried separately:
  the two `extends Allegory 𝒜` chains give distinct `Cat.Hom` types on `𝒜`, making `SplObj 𝒜`
  via each path a DIFFERENT TYPE.  The combined class eliminates this by construction. -/

/-- **Goal A** (§2.42 packaging): if `𝒜` is a SEMI-SIMPLE DIVISION ALLEGORY (the combined
    `SemiSimpleDivisionAllegory`, which unifies the `Allegory` base) then `SplObj 𝒜` is an
    EFFECTIVE DIVISION ALLEGORY.  The proof inlines `instDivisionSpl` for the division structure
    and rebuilds the `EffectiveAllegory` side from `SemiSimpleDivisionAllegory.semi_simple` (which
    operates on the SAME `Allegory` as the division side), avoiding any instance diamond. -/
private theorem splObj_semiSimple_of_ssd {𝒜 : Type u} [SemiSimpleDivisionAllegory 𝒜]
    {E F : SplObj 𝒜} (Ψ : E ⟶ F) : SemiSimple Ψ := by
  obtain ⟨c0, F0, G0, hF0, hG0, hUfac⟩ := SemiSimpleDivisionAllegory.semi_simple Ψ.R
  have hEsym : E.idem.e° = E.idem.e := E.idem.sym
  have hFsym : F.idem.e° = F.idem.e := F.idem.sym
  have hEidem : E.idem.e ≫ E.idem.e = E.idem.e := E.idem.idem
  have hFidem : F.idem.e ≫ F.idem.e = F.idem.e := F.idem.idem
  let C : SplObj 𝒜 := ⟨c0, ⟨Cat.id c0, recip_id, Cat.id_comp _⟩⟩
  let legF : C ⟶ E := ⟨F0 ≫ E.idem.e, by
        show Cat.id c0 ≫ (F0 ≫ E.idem.e) ≫ E.idem.e = F0 ≫ E.idem.e
        rw [Cat.id_comp, Cat.assoc, hEidem]⟩
  let legG : C ⟶ F := ⟨G0 ≫ F.idem.e, by
        show Cat.id c0 ≫ (G0 ≫ F.idem.e) ≫ F.idem.e = G0 ≫ F.idem.e
        rw [Cat.id_comp, Cat.assoc, hFidem]⟩
  refine ⟨C, legF, legG, ?_, ?_, ?_⟩
  · unfold Simple; rw [splLe_iff]
    show (F0 ≫ E.idem.e)° ≫ (F0 ≫ E.idem.e) ⊑ E.idem.e
    rw [Allegory.recip_comp, hEsym]
    calc (E.idem.e ≫ F0°) ≫ F0 ≫ E.idem.e
        = E.idem.e ≫ (F0° ≫ F0) ≫ E.idem.e := by simp only [Cat.assoc]
      _ ⊑ E.idem.e ≫ Cat.id E.carrier ≫ E.idem.e := comp_mono_left _ (comp_mono_right hF0 _)
      _ = E.idem.e := by rw [Cat.id_comp, hEidem]
  · unfold Simple; rw [splLe_iff]
    show (G0 ≫ F.idem.e)° ≫ (G0 ≫ F.idem.e) ⊑ F.idem.e
    rw [Allegory.recip_comp, hFsym]
    calc (F.idem.e ≫ G0°) ≫ G0 ≫ F.idem.e
        = F.idem.e ≫ (G0° ≫ G0) ≫ F.idem.e := by simp only [Cat.assoc]
      _ ⊑ F.idem.e ≫ Cat.id F.carrier ≫ F.idem.e := comp_mono_left _ (comp_mono_right hG0 _)
      _ = F.idem.e := by rw [Cat.id_comp, hFidem]
  · apply SplHom.ext
    show Ψ.R = ((splRecip legF) ≫ legG).R
    show Ψ.R = (F0 ≫ E.idem.e)° ≫ (G0 ≫ F.idem.e)
    rw [Allegory.recip_comp, hEsym]
    have hfix : E.idem.e ≫ Ψ.R ≫ F.idem.e = Ψ.R := Ψ.fixed
    calc Ψ.R = E.idem.e ≫ Ψ.R ≫ F.idem.e := hfix.symm
      _ = E.idem.e ≫ (F0° ≫ G0) ≫ F.idem.e := by rw [hUfac]
      _ = (E.idem.e ≫ F0°) ≫ (G0 ≫ F.idem.e) := by simp only [Cat.assoc]

noncomputable instance instEffectiveDivisionSpl {𝒜 : Type u}
    [SemiSimpleDivisionAllegory 𝒜] :
    EffectiveDivisionAllegory (SplObj 𝒜) :=
  { instDivisionSpl,
    (show EffectiveAllegory (SplObj 𝒜) from
      { instAllegorySpl with
        tabular := fun Ψ => tabular_of_semiSimple_splits
          (fun S => splObj_semiSimple_of_ssd S) splObj_splitsSymmIdem Ψ
        split_symmetric_idempotent := fun Φ hrefl hsym hidem =>
          splObj_split_equivalence Φ hrefl hsym hidem })
    with }

/-! ## §2.42  `SplObj 𝒜` is an effective power allegory for a power allegory `𝒜`

  Freyd §2.42 (book, §2.422 corollary): *Let A be a power allegory.  Then `Spl(Corefl A)`
  is an effective power allegory.*  The completion is the COREFLEXIVE one `SplCorObj 𝒜`
  (split only coreflexives), reached because §2.421/§2.422 give `E = E/E = A(E)A°(E) = ff°`
  for every equivalence relation `E`, so splitting coreflexives makes every equivalence
  relation effective.  Crucially the book does NOT make the power allegory semi-simple —
  "free power allegories are not semi-simple" (book §2.42, near §2.441) — so the full
  `SplObj`/`instEffectiveSpl` route (which DEMANDS `[SemiSimpleAllegory 𝒜]`) does NOT apply
  to a general power allegory.

  WHAT LANDS HERE (the genuinely transportable structure, all sorry-free):
    • `instDivisionSpl` — `DivisionAllegory (SplObj 𝒜)` (pointwise division, above). This was
      the PRIMARY blocker flagged by the old TODO; it is now closed for the FULL `SplObj 𝒜`
      (hence a fortiori usable for `SplCorObj 𝒜`).  Together with `instDistributiveSpl`
      (§2.21) and `instUnitarySpl`/`instPositiveSpl`, `SplObj 𝒜` now has the full
      distributive/division tower.
    • For a SEMI-SIMPLE power allegory the assembly completes through the existing pieces:
      `instEffectiveSpl` + `instDivisionSpl` give `EffectiveDivisionAllegory (SplObj 𝒜)`,
      `splObj_effectivePrePower_of_semiSimple` adds the thick targets, and
      `effective_pre_power_is_power` yields `PowerAllegory (SplObj 𝒜)`.

  GOAL B STATUS (precise marker):

  Goal B is `EffectiveAllegory (SplCorObj 𝒜)` for `[PowerAllegory 𝒜]`.  The Lean class
  `EffectiveAllegory` extends `TabularAllegory`, but the existing `SplCorObj.instTabularAllegorySplCor`
  requires `[TabularAllegory 𝒜]`, which `PowerAllegory` alone does not provide.  Hence the
  instance cannot be assembled as is.

  The *mathematical* content — that every equivalence relation in `SplCorObj 𝒜` splits —
  relies on `equivRel_eq_map_comp_recip` (§2.422), which requires the side-condition
  `hbox : codBox E = codBox (∋ a)`.  For a reflexive E, `codBox E = 1`; but `codBox (∋ a) = 1`
  iff `∋ a` is entire, which is NOT a consequence of the current `PowerAllegory` axioms
  (the `eps_thick` field is box-guarded, not the unguarded `1 ⊑ ∋/∋`).

  TWO-PART BLOCKER for Goal B:
    (B1) `TabularAllegory (SplCorObj 𝒜)` under `[PowerAllegory 𝒜]` — needs either
         `PowerAllegory → TabularAllegory` (not in repo; not trivially true) or the
         effective part decoupled from `TabularAllegory`.
    (B2) `hbox` for reflexive `E` — needs `dom((∋ a)°) = 1`, i.e., `∋ a` entire, which
         requires adding `eps_entire : Entire (∋ b)` or `eps_codBox_one : codBox (∋ b) = 1`
         to `PowerAllegory` (currently absent).

  REMAINING GAP (precise, NOT a repo lemma).  The conclusion `(effective) PowerAllegory`
  needs a THICK target for every object, which §2.43/§2.432 supply via the membership `eps`
  (`Thick (eps b)`).  An `EffectivePrePowerAllegory.thick_target` therefore requires a
  GENUINELY thick morphism on `SplObj 𝒜` — and the only source of one is a TRANSPORTED `eps`.
  Identities are NOT thick (`Thick (id_b)` would force every box-matched `R` to be entire), so
  no thick target can be fabricated from the distributive/division tower alone.

  Hence the two missing primitives (book-routine, neither reducible to an existing repo lemma):
    (1) the TRANSPORTED `eps_{SplObj}`/`powerObj_{SplObj}` (the §2.421 identity
        `R/S = A(R)A°(S)`, carried across the splitting), giving `Thick (eps_{SplObj} b)`;
    (2) for a GENERAL power allegory, effectiveness of the COREFLEXIVE completion
        `SplCorObj 𝒜` via §2.422 (`E = E/E = A(E)A°(E) = ff°` + coreflexive split), since a
        general power allegory is NOT semi-simple so `instEffectiveSpl` does not fire;
        BLOCKED by (B1)+(B2) above.

  With those, `effective_pre_power_is_power` (S2_4) closes the conclusion.  The
  distributive/division tower (`instDistributiveSpl`, `instDivisionSpl`, `instUnitarySpl`,
  `instPositiveSpl`) and — in the semi-simple case — `instEffectiveSpl` are all in place;
  the strict residue is the transported membership `eps`. -/

/-! ## §2.433 / §2.434 / §2.435  Power allegory completions

  §2.433: If `𝒜` is a pre-power allegory, `Spl(Eq 𝒜)` is a power allegory.
          MISSING: `Spl(Eq 𝒜)` category construction.

  §2.434: The systemic completion of a small locally complete distributive allegory is a
          power allegory.  MISSING: systemic completion type.

  §2.435: A connected division allegory with a thick endomorphism is trivial.
          MISSING: `ConnectedAllegory` class.  The one-object §2.436 is in `S2_43.lean`. -/

-- §2.433: TODO — needs Spl(Eq 𝒜) construction.
-- §2.434: TODO — needs systemic completion (out of scope).
-- §2.435: TODO — needs ConnectedAllegory; see S2_43 for §2.436.

/-! ## §2.165 / §2.166 for `SplCorObj 𝒜`  (coreflexive splitting completion)

  `SplObj 𝒜` splits ALL symmetric idempotents. Freyd's §2.165/§2.166 apply only to the
  COREFLEXIVE sub-completion `SplCorObj 𝒜 = { E : SplObj 𝒜 // E.idem.e ⊑ 1_{E.carrier} }`,
  which splits only the coreflexive symmetric idempotents (`e° = e, ee = e, e ⊑ 1`).

  This section:
    §2.165  `Allegory (SplCorObj 𝒜)`          [PROVED: Cat + Allegory instances]
            `PreTabularAllegory (SplCorObj 𝒜)` [PROVED via §2.166]
    §2.166  `TabularAllegory (SplCorObj 𝒜)`    [PROVED]

  Construction (source-apex convention `Tabulates p q R := R = p°≫q ∧ p≫p° ∩ q≫q° = id`):
  given a tabulation `(f, g)` of `Ψ.R` in `𝒜` (`Ψ.R = f°≫g`, `f≫f° ∩ g≫g° = id_c`), the
  object idempotents `E.e`, `F.e` (coreflexive) are absorbed into the legs `p = f≫E.e`,
  `q = g≫F.e`.  These only PRE-tabulate `Ψ.R`, so the apex is the coreflexive
  `D = 1 ∩ p≫p° ∩ q≫q° = 1 ∩ f≫E.e≫f° ∩ g≫F.e≫g°` on `c`, split in `SplCorObj 𝒜` as
  `C = ⟨c, D⟩`.  The source-apex legs are `legA = D≫p : C ⟶ E`, `legB = D≫q : C ⟶ F`.
  Map/joint laws follow from `D ⊑ id`, `D ⊑ p≫p°`, `D ⊑ q≫q°`, and `f≫f° ∩ g≫g° = id`;
  the relation law `Ψ = legA°≫legB` is the factoring `p°≫q ⊑ p°≫D≫q` (`splCor_factor`). -/

/-- The COREFLEXIVE splitting completion of `𝒜`: restrict `SplObj 𝒜` to objects whose
    symmetric idempotent `E.idem.e` is coreflexive (`E.idem.e ⊑ Cat.id E.carrier`).
    This is Freyd's `ℬℳ(𝒞𝑜𝓇ℯ𝒻𝓁 𝒜)` (§2.167): split only the coreflexive SymIdem. -/
def SplCorObj (𝒜 : Type u) [Allegory 𝒜] : Type u :=
  { E : SplObj 𝒜 // Coreflexive E.idem.e }

namespace SplCorObj

variable {𝒜 : Type u} [Allegory 𝒜]

/-- Category structure on `SplCorObj 𝒜`: homs and composition inherited from `SplObj 𝒜`. -/
instance instCatSplCor : Cat (SplCorObj 𝒜) where
  Hom E F     := SplHom E.1 F.1
  id E        := splId E.1
  comp R S    := splComp R S
  id_comp R   := SplHom.ext R.fixed_left
  comp_id R   := SplHom.ext R.fixed_right
  assoc _R _S _T := SplHom.ext (Cat.assoc _ _ _)

/-- Allegory structure on `SplCorObj 𝒜`: reciprocation and intersection inherited
    from `SplObj 𝒜`; all axioms reduce to the underlying `𝒜` axioms via `SplHom.ext`. -/
instance instAllegorySplCor : Allegory (SplCorObj 𝒜) where
  recip R             := splRecip R
  inter R S           := splInter R S
  recip_recip _R       := SplHom.ext (Allegory.recip_recip _)
  recip_comp _R _S      := SplHom.ext (Allegory.recip_comp _ _)
  recip_inter _R _S     := SplHom.ext (Allegory.recip_inter _ _)
  inter_idem _R        := SplHom.ext (Allegory.inter_idem _)
  inter_comm _R _S      := SplHom.ext (Allegory.inter_comm _ _)
  inter_assoc _R _S _T   := SplHom.ext (Allegory.inter_assoc _ _ _)
  semidistrib _R _S _T   := SplHom.ext (Allegory.semidistrib _ _ _)
  modular _R _S _T       := SplHom.ext (Allegory.modular _ _ _)

end SplCorObj

/-! ## §2.165 / §2.166 for `SplCorObj 𝒜` under `[TabularAllegory 𝒜]`

  With a full tabular allegory we can build tabulations directly, bypassing the source-apex
  issue that blocks the pre-tabular version. -/

-- §2.136 dual: for a SYMMETRIC SIMPLE `A`, `(R ∩ S) ≫ A = R≫A ∩ S≫A`.
-- (Reciprocate `simple_dist_inter` applied to `A°` and use `A° = A`.)
private theorem splCor_dist_inter_right {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} {A : b ⟶ b}
    (hAsym : A° = A) (hsimpleA : Simple A) (R S : a ⟶ b) :
    (R ∩ S) ≫ A = (R ≫ A) ∩ (S ≫ A) := by
  -- ((R∩S)≫A)° = A≫(R∩S)° = A≫(R°∩S°) = A≫R° ∩ A≫S° = (R≫A)° ∩ (S≫A)°
  have key : ((R ∩ S) ≫ A)° = ((R ≫ A) ∩ (S ≫ A))° := by
    rw [Allegory.recip_comp, Allegory.recip_inter, hAsym, simple_dist_inter hsimpleA R° S°,
        Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_comp, hAsym]
  have := congrArg (·°) key
  simpa only [Allegory.recip_recip] using this

private theorem splCor_entire_to_le {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} {f : a ⟶ b}
    (h : Entire f) : Cat.id a ⊑ f ≫ f° := by
  unfold Entire dom at h; exact h ▸ inter_lb_right _ _

-- `R ⊑ dom R ≫ R` (= `R ⊑ (1 ∩ R≫R°) ≫ R`); §2.122 helper (re-derived; the S2_1 one is private).
private theorem le_dom_comp' {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} (R : a ⟶ b) :
    R ⊑ (Cat.id a ∩ R ≫ R°) ≫ R := by
  have h := modular_le (Cat.id a) R R
  simp only [Cat.id_comp, Allegory.inter_idem] at h
  exact h

-- `cod` factoring (dual): `R ⊑ R ≫ (1 ∩ R°≫R)`.
private theorem le_comp_cod {𝒜 : Type u} [Allegory 𝒜] {a b : 𝒜} (R : a ⟶ b) :
    R ⊑ R ≫ (Cat.id b ∩ R° ≫ R) := by
  have h := recip_mono (le_dom_comp' R°)
  -- le_dom_comp' R° : R° ⊑ (1 ∩ R°≫R°°)≫R°;  reciprocate.
  rw [Allegory.recip_comp, Allegory.recip_inter, recip_id, Allegory.recip_comp,
      Allegory.recip_recip] at h
  exact h

-- §2.166 factoring: `p°≫q` factors through the coreflexive `1 ∩ p≫p° ∩ q≫q°`.
-- (Insert `cod p° = 1∩p≫p°` after `p°`, then `dom q = 1∩q≫q°` before `q`; the two coreflexives
--  compose to their intersection by `coreflexive_comp_eq_inter`.)
private theorem splCor_factor {𝒜 : Type u} [Allegory 𝒜] {c x y : 𝒜} (p : c ⟶ x) (q : c ⟶ y) :
    p° ≫ q ⊑ p° ≫ (Cat.id c ∩ p ≫ p° ∩ q ≫ q°) ≫ q := by
  have hcodp : p° ⊑ p° ≫ (Cat.id c ∩ p ≫ p°) := by
    have := le_comp_cod p°
    rwa [Allegory.recip_recip] at this
  have hdomq : q ⊑ (Cat.id c ∩ q ≫ q°) ≫ q := le_dom_comp' q
  have hcorL : Coreflexive (Cat.id c ∩ p ≫ p°) := inter_lb_left _ _
  have hcorR : Coreflexive (Cat.id c ∩ q ≫ q°) := inter_lb_left _ _
  -- p°≫q ⊑ (p°≫(1∩pp°))≫q ⊑ (p°≫(1∩pp°))≫((1∩qq°)≫q)
  have h1 : p° ≫ q ⊑ p° ≫ (Cat.id c ∩ p ≫ p°) ≫ q := by
    rw [← Cat.assoc]; exact comp_mono_right hcodp q
  have h2 : p° ≫ (Cat.id c ∩ p ≫ p°) ≫ q
      ⊑ p° ≫ (Cat.id c ∩ p ≫ p°) ≫ (Cat.id c ∩ q ≫ q°) ≫ q :=
    comp_mono_left p° (comp_mono_left _ hdomq)
  refine le_trans h1 (le_trans h2 ?_)
  -- merge the two coreflexives:  (1∩pp°)≫(1∩qq°) = (1∩pp°) ∩ (1∩qq°) = 1∩pp°∩qq°.
  rw [← Cat.assoc (Cat.id c ∩ p ≫ p°) (Cat.id c ∩ q ≫ q°) q,
      coreflexive_comp_eq_inter hcorL hcorR]
  refine comp_mono_left p° (comp_mono_right ?_ q)
  -- (1∩pp°) ∩ (1∩qq°) = 1∩pp°∩qq°  (drop the redundant second `1`); show ⊑.
  refine le_inter (le_inter ?_ ?_) ?_
  · exact le_trans (inter_lb_left _ _) (inter_lb_left _ _)
  · exact le_trans (inter_lb_left _ _) (inter_lb_right _ _)
  · exact le_trans (inter_lb_right _ _) (inter_lb_right _ _)

-- For a symmetric idempotent coreflexive `Ee` and any `X`, `1 ∩ Ee≫X ⊑ Ee`
-- (in Rel: the diagonal restricted to `{s ∈ Ee : (s,s) ∈ X}` lies inside `Ee`).
-- Used in §2.166 (pre-tabular) to show the source-apex leg `A≫f` already absorbs `E.e`
-- on the right (`A≫f≫E.e = A≫f`), so the absorbed legs reduce to Freyd's bare legs.
private theorem coref_inter_comp_le {𝒜 : Type u} [Allegory 𝒜] {a : 𝒜}
    {Ee : a ⟶ a} (hsym : Ee° = Ee) (hidem : Ee ≫ Ee = Ee) (X : a ⟶ a) :
    Cat.id a ∩ Ee ≫ X ⊑ Ee := by
  have hDcor : Coreflexive (Cat.id a ∩ Ee ≫ X) := inter_lb_left _ _
  have hDsym : (Cat.id a ∩ Ee ≫ X)° = Cat.id a ∩ Ee ≫ X :=
    symmetric_eq (coreflexive_symmetric_idempotent hDcor).1
  -- D = D° = 1 ∩ X°≫Ee  ⊑ X°≫Ee
  have hDle : Cat.id a ∩ Ee ≫ X ⊑ X° ≫ Ee := by
    have hrw : Cat.id a ∩ Ee ≫ X = Cat.id a ∩ X° ≫ Ee := by
      have h := hDsym
      rw [Allegory.recip_inter, recip_id, Allegory.recip_comp, hsym] at h
      exact h.symm
    rw [hrw]; exact inter_lb_right _ _
  -- D = D ∩ 1 ⊑ (X°≫Ee)∩1 ⊑ (X°∩Ee)≫Ee ⊑ Ee≫Ee = Ee
  refine le_trans (le_inter hDle (inter_lb_left _ _)) ?_
  have hmod := modular_le X° Ee (Cat.id a)
  rw [Cat.id_comp, hsym] at hmod
  refine le_trans hmod ?_
  calc (X° ∩ Ee) ≫ Ee ⊑ Ee ≫ Ee := comp_mono_right (inter_lb_right _ _) Ee
    _ = Ee := hidem

-- Dual modular law (reciprocal of `modular_le`):  `(R≫S) ∩ T ⊑ R ≫ (S ∩ R°≫T)`.
private theorem dual_modular_le {𝒜 : Type u} [Allegory 𝒜] {a b c : 𝒜}
    (R : a ⟶ b) (S : b ⟶ c) (T : a ⟶ c) : (R ≫ S) ∩ T ⊑ R ≫ (S ∩ R° ≫ T) := by
  have hr := recip_mono (modular_le S° R° T°)
  rw [Allegory.recip_comp, Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_recip,
      Allegory.recip_recip] at hr
  rw [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_recip, Allegory.recip_recip] at hr
  exact hr

/-- **§2.166**: If `𝒜` is a tabular allegory then `SplCorObj 𝒜` is a tabular allegory.

    Source-apex convention (`Tabulates p q R := … ∧ R = p°≫q ∧ p≫p° ∩ q≫q° = id`).
    Given `Ψ : E ⟶ F` in `SplCorObj 𝒜`, extract a tabulation `(f, g)` of `Ψ.R` in `𝒜`
    (`Ψ.R = f°≫g`, `f≫f° ∩ g≫g° = id_c`).  Freyd §2.166: the coreflexive
    `A = 1 ∩ f≫Ψ.R≫g°` on `c` is a symmetric idempotent; in `SplCorObj 𝒜` it splits as
    the apex object `C = ⟨c, A⟩`.  The source-apex legs are `legA = A≫f : C ⟶ E` and
    `legB = A≫g : C ⟶ F` (each `A`-fixed on the left and `E.e/F.e`-fixed on the right).
    The three tabulation laws are Freyd's two displayed computations:
    `f°≫A≫g = Ψ.R` (sandwich, since `Ψ.R = f°≫g`) and
    `legA≫legA° ∩ legB≫legB° = A≫(f≫f° ∩ g≫g°)≫A = A≫A = A = id_C`. -/
instance SplCorObj.instTabularAllegorySplCor {𝒜 : Type u} [TabularAllegory 𝒜] :
    TabularAllegory (SplCorObj 𝒜) :=
  { SplCorObj.instAllegorySplCor with
    tabular := fun {E F} Ψ => by
      obtain ⟨c, f, g, hMapf, hMapg, hRfg, htab⟩ := TabularAllegory.tabular Ψ.R
      -- Entireness of the two legs, read off the joint-monicity `htab`.
      have hfent : Cat.id c ⊑ f ≫ f° := htab ▸ inter_lb_left (f ≫ f°) (g ≫ g°)
      have hgent : Cat.id c ⊑ g ≫ g° := htab ▸ inter_lb_right (f ≫ f°) (g ≫ g°)
      -- Object idempotents (E.e on E.carrier, F.e on F.carrier), symmetric idempotent + coreflexive.
      have hEcor : E.1.idem.e ⊑ Cat.id E.1.carrier := E.2
      have hFcor : F.1.idem.e ⊑ Cat.id F.1.carrier := F.2
      have hEsym : E.1.idem.e° = E.1.idem.e := E.1.idem.sym
      have hFsym : F.1.idem.e° = F.1.idem.e := F.1.idem.sym
      have hEidem : E.1.idem.e ≫ E.1.idem.e = E.1.idem.e := E.1.idem.idem
      have hFidem : F.1.idem.e ≫ F.1.idem.e = F.1.idem.e := F.1.idem.idem
      -- The two *absorbed* legs `f≫E.e`, `g≫F.e` only pre-tabulate Ψ.R; the apex idempotent is
      -- the coreflexive `D = 1 ∩ (f≫E.e≫f° ∩ g≫F.e≫g°)` on c (the domain of the absorbed pair).
      -- `legX≫legX° = (·≫E.e)≫(·≫E.e)° = ·≫E.e≫·°` (E.e sym+idem).
      let M : c ⟶ c := f ≫ E.1.idem.e ≫ f° ∩ g ≫ F.1.idem.e ≫ g°
      let D : c ⟶ c := Cat.id c ∩ M
      have hDcor : Coreflexive D := inter_lb_left _ _
      have hDsym : D° = D := symmetric_eq (coreflexive_symmetric_idempotent hDcor).1
      have hDidem : D ≫ D = D := (coreflexive_symmetric_idempotent hDcor).2
      have hDsimple : Simple D := by dsimp [Simple]; rw [hDsym, hDidem]; exact hDcor
      have hDle : D ⊑ Cat.id c := hDcor
      have hDM1 : D ⊑ f ≫ E.1.idem.e ≫ f° :=
        le_trans (inter_lb_right (Cat.id c) M) (inter_lb_left _ _)
      have hDM2 : D ⊑ g ≫ F.1.idem.e ≫ g° :=
        le_trans (inter_lb_right (Cat.id c) M) (inter_lb_right _ _)
      -- `legA≫legA° = D≫(f≫E.e≫f°)≫D`  (E.e sym+idem, D sym).
      have hLA : (D ≫ f ≫ E.1.idem.e) ≫ (D ≫ f ≫ E.1.idem.e)° = D ≫ (f ≫ E.1.idem.e ≫ f°) ≫ D := by
        simp only [Allegory.recip_comp, hDsym, hEsym, Cat.assoc]
        rw [← Cat.assoc E.1.idem.e E.1.idem.e (f° ≫ D), hEidem]
      have hLB : (D ≫ g ≫ F.1.idem.e) ≫ (D ≫ g ≫ F.1.idem.e)° = D ≫ (g ≫ F.1.idem.e ≫ g°) ≫ D := by
        simp only [Allegory.recip_comp, hDsym, hFsym, Cat.assoc]
        rw [← Cat.assoc F.1.idem.e F.1.idem.e (g° ≫ D), hFidem]
      -- `D ⊑ legA≫legA°`  (and `D ⊑ legB≫legB°`):  D = D≫D≫D ⊑ D≫(f≫E.e≫f°)≫D.
      have hEntA : D ⊑ (D ≫ f ≫ E.1.idem.e) ≫ (D ≫ f ≫ E.1.idem.e)° := by
        rw [hLA]
        calc D = D ≫ D ≫ D := by rw [hDidem, hDidem]
          _ ⊑ D ≫ (f ≫ E.1.idem.e ≫ f°) ≫ D := comp_mono_left D (comp_mono_right hDM1 D)
      have hEntB : D ⊑ (D ≫ g ≫ F.1.idem.e) ≫ (D ≫ g ≫ F.1.idem.e)° := by
        rw [hLB]
        calc D = D ≫ D ≫ D := by rw [hDidem, hDidem]
          _ ⊑ D ≫ (g ≫ F.1.idem.e ≫ g°) ≫ D := comp_mono_left D (comp_mono_right hDM2 D)
      -- `legA≫legA° ⊑ f≫f°`  (D ⊑ id both ends, E.e ⊑ id):  for joint `⊑ id_c`.
      -- `D≫X≫D ⊑ X` (both ends D ⊑ id):
      have hsandwich : ∀ {X : c ⟶ c}, D ≫ X ≫ D ⊑ X := by
        intro X
        have h1 : D ≫ X ≫ D ⊑ Cat.id c ≫ X ≫ Cat.id c := by
          refine le_trans (comp_mono_right hDle (X ≫ D)) ?_
          rw [Cat.id_comp, Cat.id_comp]
          exact comp_mono_left X hDle
        rwa [Cat.id_comp, Cat.comp_id] at h1
      have hLAf : (D ≫ f ≫ E.1.idem.e) ≫ (D ≫ f ≫ E.1.idem.e)° ⊑ f ≫ f° := by
        rw [hLA]
        refine le_trans hsandwich ?_
        calc f ≫ E.1.idem.e ≫ f° ⊑ f ≫ Cat.id E.1.carrier ≫ f° :=
              comp_mono_left f (comp_mono_right hEcor f°)
          _ = f ≫ f° := by rw [Cat.id_comp]
      have hLBg : (D ≫ g ≫ F.1.idem.e) ≫ (D ≫ g ≫ F.1.idem.e)° ⊑ g ≫ g° := by
        rw [hLB]
        refine le_trans hsandwich ?_
        calc g ≫ F.1.idem.e ≫ g° ⊑ g ≫ Cat.id F.1.carrier ≫ g° :=
              comp_mono_left g (comp_mono_right hFcor g°)
          _ = g ≫ g° := by rw [Cat.id_comp]
      -- Apex object `C = ⟨c, D⟩` in SplCorObj (D is its identity, splitting the coreflexive D).
      let C : SplCorObj 𝒜 := ⟨⟨c, ⟨D, hDsym, hDidem⟩⟩, hDcor⟩
      -- Legs `D≫f≫E.e : C ⟶ E`, `D≫g≫F.e : C ⟶ F` (D-fixed left, E.e/F.e-fixed right).
      let legA : C ⟶ E := ⟨D ≫ f ≫ E.1.idem.e, by
            show D ≫ (D ≫ f ≫ E.1.idem.e) ≫ E.1.idem.e = D ≫ f ≫ E.1.idem.e
            simp only [Cat.assoc]; rw [hEidem, ← Cat.assoc D D (f ≫ E.1.idem.e), hDidem]⟩
      let legB : C ⟶ F := ⟨D ≫ g ≫ F.1.idem.e, by
            show D ≫ (D ≫ g ≫ F.1.idem.e) ≫ F.1.idem.e = D ≫ g ≫ F.1.idem.e
            simp only [Cat.assoc]; rw [hFidem, ← Cat.assoc D D (g ≫ F.1.idem.e), hDidem]⟩
      -- `legA≫legA° ⊑ f≫E.e≫f°` and `legB≫legB° ⊑ g≫F.e≫g°` (both ends D ⊑ id):
      have hLAM : (D ≫ f ≫ E.1.idem.e) ≫ (D ≫ f ≫ E.1.idem.e)° ⊑ f ≫ E.1.idem.e ≫ f° := by
        rw [hLA]; exact hsandwich
      have hLBM : (D ≫ g ≫ F.1.idem.e) ≫ (D ≫ g ≫ F.1.idem.e)° ⊑ g ≫ F.1.idem.e ≫ g° := by
        rw [hLB]; exact hsandwich
      refine ⟨C, legA, legB, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      -- Map legA: Entire — id_C = D ⊑ legA≫legA° = D≫(f≫E.e≫f°)≫D.
      · unfold Entire dom; apply SplHom.ext
        show D ∩ (D ≫ f ≫ E.1.idem.e) ≫ (D ≫ f ≫ E.1.idem.e)° = D
        exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hEntA)
      -- Map legA: Simple — legA°≫legA = E.e≫f°≫D≫f≫E.e ⊑ id_E = E.e.
      · unfold Simple; apply SplHom.ext
        show (D ≫ f ≫ E.1.idem.e)° ≫ (D ≫ f ≫ E.1.idem.e) ⊑ E.1.idem.e
        -- normalise to `E.e≫f°≫D≫D≫f≫E.e`, collapse `D≫D=D`, bound `f°≫D≫f ⊑ f°≫f ⊑ id`.
        rw [Allegory.recip_comp, Allegory.recip_comp, hDsym, hEsym]
        simp only [Cat.assoc]
        rw [← Cat.assoc D D (f ≫ E.1.idem.e), hDidem]
        -- goal: E.e≫f°≫D≫f≫E.e ⊑ E.e
        have key : E.1.idem.e ≫ f° ≫ D ≫ f ≫ E.1.idem.e ⊑ E.1.idem.e ≫ (f° ≫ f) ≫ E.1.idem.e := by
          have hDf : f° ≫ D ≫ f ⊑ f° ≫ f := by
            refine comp_mono_left f° ?_
            have h := comp_mono_right hDle f; rwa [Cat.id_comp] at h
          have := comp_mono_left E.1.idem.e (comp_mono_right hDf E.1.idem.e)
          simpa only [Cat.assoc] using this
        refine le_trans key ?_
        have hsf : f° ≫ f ⊑ Cat.id E.1.carrier := hMapf.2
        calc E.1.idem.e ≫ (f° ≫ f) ≫ E.1.idem.e
            ⊑ E.1.idem.e ≫ Cat.id E.1.carrier ≫ E.1.idem.e :=
              comp_mono_left _ (comp_mono_right hsf _)
          _ = E.1.idem.e := by rw [Cat.id_comp, hEidem]
      -- Map legB: Entire.
      · unfold Entire dom; apply SplHom.ext
        show D ∩ (D ≫ g ≫ F.1.idem.e) ≫ (D ≫ g ≫ F.1.idem.e)° = D
        exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hEntB)
      -- Map legB: Simple.
      · unfold Simple; apply SplHom.ext
        show (D ≫ g ≫ F.1.idem.e)° ≫ (D ≫ g ≫ F.1.idem.e) ⊑ F.1.idem.e
        rw [Allegory.recip_comp, Allegory.recip_comp, hDsym, hFsym]
        simp only [Cat.assoc]
        rw [← Cat.assoc D D (g ≫ F.1.idem.e), hDidem]
        have key : F.1.idem.e ≫ g° ≫ D ≫ g ≫ F.1.idem.e ⊑ F.1.idem.e ≫ (g° ≫ g) ≫ F.1.idem.e := by
          have hDg : g° ≫ D ≫ g ⊑ g° ≫ g := by
            refine comp_mono_left g° ?_
            have h := comp_mono_right hDle g; rwa [Cat.id_comp] at h
          have := comp_mono_left F.1.idem.e (comp_mono_right hDg F.1.idem.e)
          simpa only [Cat.assoc] using this
        refine le_trans key ?_
        have hsg : g° ≫ g ⊑ Cat.id F.1.carrier := hMapg.2
        calc F.1.idem.e ≫ (g° ≫ g) ≫ F.1.idem.e
            ⊑ F.1.idem.e ≫ Cat.id F.1.carrier ≫ F.1.idem.e :=
              comp_mono_left _ (comp_mono_right hsg _)
          _ = F.1.idem.e := by rw [Cat.id_comp, hFidem]
      -- Ψ = legA° ≫ legB:  Ψ.R = E.e≫f°≫D≫g≫F.e.  The `⊒` step is the §2.166 factoring
      -- `(f≫E.e)°≫(g≫F.e) ⊑ (f≫E.e)°≫D≫(g≫F.e)`; `⊑` is `D ⊑ id`.
      · apply SplHom.ext
        show Ψ.R = (D ≫ f ≫ E.1.idem.e)° ≫ (D ≫ g ≫ F.1.idem.e)
        -- abbreviations p = f≫E.e, q = g≫F.e
        have hpp : (f ≫ E.1.idem.e) ≫ (f ≫ E.1.idem.e)° = f ≫ E.1.idem.e ≫ f° := by
          rw [Allegory.recip_comp, hEsym]; simp only [Cat.assoc]
          rw [← Cat.assoc E.1.idem.e E.1.idem.e f°, hEidem]
        have hqq : (g ≫ F.1.idem.e) ≫ (g ≫ F.1.idem.e)° = g ≫ F.1.idem.e ≫ g° := by
          rw [Allegory.recip_comp, hFsym]; simp only [Cat.assoc]
          rw [← Cat.assoc F.1.idem.e F.1.idem.e g°, hFidem]
        -- D' (the factoring's coreflexive) equals D.
        have hD' : Cat.id c ∩ (f ≫ E.1.idem.e) ≫ (f ≫ E.1.idem.e)°
                       ∩ (g ≫ F.1.idem.e) ≫ (g ≫ F.1.idem.e)° = D := by
          show Cat.id c ∩ (f ≫ E.1.idem.e) ≫ (f ≫ E.1.idem.e)°
                 ∩ (g ≫ F.1.idem.e) ≫ (g ≫ F.1.idem.e)° = Cat.id c ∩ M
          rw [hpp, hqq, Allegory.inter_assoc]
        -- the factoring, with D' rewritten to D.
        have hfac : (f ≫ E.1.idem.e)° ≫ (g ≫ F.1.idem.e)
            ⊑ (f ≫ E.1.idem.e)° ≫ D ≫ (g ≫ F.1.idem.e) := by
          have := splCor_factor (f ≫ E.1.idem.e) (g ≫ F.1.idem.e)
          rwa [hD'] at this
        -- expand both sides to E.e≫f°≫…  and prove equality by `le_antisymm`.
        have hL : (f ≫ E.1.idem.e)° ≫ (g ≫ F.1.idem.e) = E.1.idem.e ≫ f° ≫ g ≫ F.1.idem.e := by
          rw [Allegory.recip_comp, hEsym]; simp only [Cat.assoc]
        have hR : (D ≫ f ≫ E.1.idem.e)° ≫ (D ≫ g ≫ F.1.idem.e)
            = E.1.idem.e ≫ f° ≫ D ≫ g ≫ F.1.idem.e := by
          rw [Allegory.recip_comp, Allegory.recip_comp, hDsym, hEsym]; simp only [Cat.assoc]
          rw [← Cat.assoc D D (g ≫ F.1.idem.e), hDidem]
        rw [hR]
        -- Ψ.R = E.e≫f°≫g≫F.e (Ψ.R = f°≫g, Ψ E.e/F.e-fixed);  then sandwich-insert D.
        have hΨ : Ψ.R = E.1.idem.e ≫ f° ≫ g ≫ F.1.idem.e := by
          have hfix : E.1.idem.e ≫ Ψ.R ≫ F.1.idem.e = Ψ.R := Ψ.fixed
          rw [hRfg] at hfix ⊢; rw [← hfix]; simp only [Cat.assoc]
        rw [hΨ]
        apply le_antisymm
        · -- E.e≫f°≫g≫F.e ⊑ E.e≫f°≫D≫g≫F.e  (factoring; via hL, hfac)
          have := hfac; rw [hL] at this
          -- this : E.e≫f°≫g≫F.e ⊑ (f≫E.e)°≫D≫(g≫F.e); rewrite RHS
          have hRHS : (f ≫ E.1.idem.e)° ≫ D ≫ (g ≫ F.1.idem.e)
              = E.1.idem.e ≫ f° ≫ D ≫ g ≫ F.1.idem.e := by
            rw [Allegory.recip_comp, hEsym]; simp only [Cat.assoc]
          rwa [hRHS] at this
        · -- E.e≫f°≫D≫g≫F.e ⊑ E.e≫f°≫g≫F.e  (D ⊑ id)
          refine comp_mono_left E.1.idem.e (comp_mono_left f° ?_)
          have hDg : D ≫ g ≫ F.1.idem.e ⊑ g ≫ F.1.idem.e := by
            have h := comp_mono_right hDle (g ≫ F.1.idem.e); rwa [Cat.id_comp] at h
          simpa only [Cat.assoc] using hDg
      -- Joint: legA≫legA° ∩ legB≫legB° = D = id_C.
      · apply SplHom.ext
        show (D ≫ f ≫ E.1.idem.e) ≫ (D ≫ f ≫ E.1.idem.e)° ∩
             (D ≫ g ≫ F.1.idem.e) ≫ (D ≫ g ≫ F.1.idem.e)° = D
        apply le_antisymm
        · -- joint ⊑ D = id_c ∩ M
          apply le_inter
          · -- ⊑ id_c : joint ⊑ f≫f° ∩ g≫g° = id_c
            refine le_trans (le_inter (le_trans (inter_lb_left _ _) hLAf)
              (le_trans (inter_lb_right _ _) hLBg)) ?_
            rw [htab]; exact le_refl _
          · -- ⊑ M : joint ⊑ f≫E.e≫f° ∩ g≫F.e≫g°
            exact le_inter (le_trans (inter_lb_left _ _) hLAM)
              (le_trans (inter_lb_right _ _) hLBM)
        · exact le_inter hEntA hEntB
  }

/-- **§2.166 / §2.167** (the real content): if `𝒜` is a *pre-tabular* allegory then
    `SplCorObj 𝒜` is a *tabular* allegory — `PM(Corefl 𝒜)` is the tabular reflection of a
    pre-tabular `𝒜`.

    Given `Ψ : E ⟶ F`, `pre_tabular Ψ.R` yields a tabular `S` with `Ψ.R ⊑ S = f°≫g`,
    `f≫f° ∩ g≫g° = id_c` (f, g maps).  Freyd §2.166 tabulates `Ψ.R` itself (not `S`) via the
    coreflexive apex `A = 1 ∩ f≫Ψ.R≫g°` (depending on `Ψ.R`), split in `SplCorObj 𝒜` as
    `C = ⟨c, A⟩`.  Legs `legA = A≫f≫E.e : C ⟶ E`, `legB = A≫g≫F.e : C ⟶ F`.  Because `Ψ.R`
    is `E.e/F.e`-fixed, the apex absorbs the object idempotents: `A≫f≫E.e = A≫f` and
    `A≫g≫F.e = A≫g` (via `coref_inter_comp_le`), so the legs reduce to Freyd's bare `A≫f`,
    `A≫g`.  The tabulation law `legA°≫legB = Ψ.R` is Freyd's two displays
    (`(hf)°(hg) ⊑ f°fΨg°g ⊑ Ψ`  and  `Ψ ⊑ f°g∩Ψ ⊑ f°(1∩fΨg°)g = (hf)°(hg)`), both using
    only `Ψ.R ⊑ f°≫g` and the modular law; the joint law is
    `A≫(f≫f° ∩ g≫g°)≫A = A≫A = A = id_C`. -/
instance SplCorObj.tabular_of_preTabular {𝒜 : Type u} [PreTabularAllegory 𝒜] :
    TabularAllegory (SplCorObj 𝒜) :=
  { SplCorObj.instAllegorySplCor with
    tabular := fun {E F} Ψ => by
      obtain ⟨S, hΨS, c, f, g, hMapf, hMapg, hSfg, htab⟩ := PreTabularAllegory.pre_tabular Ψ.R
      -- `Ψ.R ⊑ f°≫g`.
      have hRle : Ψ.R ⊑ f° ≫ g := hSfg ▸ hΨS
      -- f, g entire (1 ⊑ ff°, gg°) and simple (f°f ⊑ 1, g°g ⊑ 1).
      have hfent : Cat.id c ⊑ f ≫ f° := htab ▸ inter_lb_left (f ≫ f°) (g ≫ g°)
      have hgent : Cat.id c ⊑ g ≫ g° := htab ▸ inter_lb_right (f ≫ f°) (g ≫ g°)
      have hfsim : f° ≫ f ⊑ Cat.id E.1.carrier := hMapf.2
      have hgsim : g° ≫ g ⊑ Cat.id F.1.carrier := hMapg.2
      -- Object idempotents.
      have hEsym : E.1.idem.e° = E.1.idem.e := E.1.idem.sym
      have hFsym : F.1.idem.e° = F.1.idem.e := F.1.idem.sym
      have hEidem : E.1.idem.e ≫ E.1.idem.e = E.1.idem.e := E.1.idem.idem
      have hFidem : F.1.idem.e ≫ F.1.idem.e = F.1.idem.e := F.1.idem.idem
      -- Ψ.R is E.e/F.e-fixed.
      have hΨL : E.1.idem.e ≫ Ψ.R = Ψ.R := Ψ.fixed_left
      have hΨR : Ψ.R ≫ F.1.idem.e = Ψ.R := Ψ.fixed_right
      -- Freyd's apex `A = 1 ∩ f≫Ψ.R≫g°` on c (depends on Ψ.R).
      let A : c ⟶ c := Cat.id c ∩ f ≫ Ψ.R ≫ g°
      have hAcor : Coreflexive A := inter_lb_left _ _
      have hAsym : A° = A := symmetric_eq (coreflexive_symmetric_idempotent hAcor).1
      have hAidem : A ≫ A = A := (coreflexive_symmetric_idempotent hAcor).2
      have hAle : A ⊑ Cat.id c := hAcor
      have hAfΨg : A ⊑ f ≫ Ψ.R ≫ g° := inter_lb_right _ _
      have hAsimple : Simple A := by dsimp [Simple]; rw [hAsym, hAidem]; exact hAcor
      -- Leg-absorption: `A≫f≫E.e = A≫f` and `A≫g≫F.e = A≫g`.  Because `Ψ.R` is E.e/F.e-fixed,
      -- the apex `A = 1∩f≫Ψ.R≫g°` forces `1 ∩ f°≫A≫f ⊑ E.e` (`coref_inter_comp_le`),
      -- so `A≫f` already lands inside `E.e` on the right.
      have hAf : A ≫ f = A ≫ f ≫ E.1.idem.e := by
        have hAfEe : A ⊑ f ≫ E.1.idem.e ≫ Ψ.R ≫ g° := by
          have heq : f ≫ E.1.idem.e ≫ Ψ.R ≫ g° = f ≫ Ψ.R ≫ g° := by
            rw [← Cat.assoc E.1.idem.e Ψ.R g°, hΨL]
          rw [heq]; exact hAfΨg
        have hfA : f° ≫ A ⊑ E.1.idem.e ≫ Ψ.R ≫ g° := by
          refine le_trans (comp_mono_left f° hAfEe) ?_
          have h := comp_mono_right hfsim (E.1.idem.e ≫ Ψ.R ≫ g°)
          rw [Cat.id_comp] at h
          refine le_trans ?_ h
          rw [← Cat.assoc f° f]; exact le_refl _
        have hfAfE : Cat.id E.1.carrier ∩ f° ≫ A ≫ f ⊑ E.1.idem.e := by
          refine le_trans (le_inter (inter_lb_left _ _) ?_)
            (coref_inter_comp_le hEsym hEidem (Ψ.R ≫ g° ≫ f))
          refine le_trans (inter_lb_right _ _) ?_
          have h := comp_mono_right hfA f
          simp only [Cat.assoc] at h ⊢; exact h
        apply le_antisymm
        · refine le_trans (le_comp_cod (A ≫ f)) ?_
          have hgoal : (A ≫ f) ≫ (Cat.id E.1.carrier ∩ (A ≫ f)° ≫ (A ≫ f)) ⊑ (A ≫ f) ≫ E.1.idem.e := by
            refine comp_mono_left (A ≫ f) ?_
            rw [Allegory.recip_comp, hAsym]
            have hrw : f° ≫ A ≫ A ≫ f = f° ≫ A ≫ f := by rw [← Cat.assoc A A f, hAidem]
            simp only [Cat.assoc] at hfAfE ⊢; rw [hrw]; exact hfAfE
          simpa only [Cat.assoc] using hgoal
        · have h := comp_mono_left (A ≫ f) E.2
          simp only [Cat.assoc, Cat.comp_id] at h ⊢; exact h
      have hAg : A ≫ g = A ≫ g ≫ F.1.idem.e := by
        have hAgFe : A ⊑ g ≫ F.1.idem.e ≫ Ψ.R° ≫ f° := by
          -- A = A° ⊑ (f≫Ψ.R≫g°)° = g≫Ψ.R°≫f°, then F.e-fix on the left of Ψ.R°.
          have hArec : A ⊑ g ≫ Ψ.R° ≫ f° := by
            have := recip_mono hAfΨg
            rw [hAsym, Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip] at this
            simpa only [Cat.assoc] using this
          have hFΨ : F.1.idem.e ≫ Ψ.R° = Ψ.R° := by
            have := congrArg (·°) hΨR
            simpa only [Allegory.recip_comp, hFsym] using this
          have heq : g ≫ F.1.idem.e ≫ Ψ.R° ≫ f° = g ≫ Ψ.R° ≫ f° := by
            rw [← Cat.assoc F.1.idem.e Ψ.R° f°, hFΨ]
          rw [heq]; exact hArec
        have hgA : g° ≫ A ⊑ F.1.idem.e ≫ Ψ.R° ≫ f° := by
          refine le_trans (comp_mono_left g° hAgFe) ?_
          have h := comp_mono_right hgsim (F.1.idem.e ≫ Ψ.R° ≫ f°)
          rw [Cat.id_comp] at h
          refine le_trans ?_ h
          rw [← Cat.assoc g° g]; exact le_refl _
        have hgAgF : Cat.id F.1.carrier ∩ g° ≫ A ≫ g ⊑ F.1.idem.e := by
          refine le_trans (le_inter (inter_lb_left _ _) ?_)
            (coref_inter_comp_le hFsym hFidem (Ψ.R° ≫ f° ≫ g))
          refine le_trans (inter_lb_right _ _) ?_
          have h := comp_mono_right hgA g
          simp only [Cat.assoc] at h ⊢; exact h
        apply le_antisymm
        · refine le_trans (le_comp_cod (A ≫ g)) ?_
          have hgoal : (A ≫ g) ≫ (Cat.id F.1.carrier ∩ (A ≫ g)° ≫ (A ≫ g)) ⊑ (A ≫ g) ≫ F.1.idem.e := by
            refine comp_mono_left (A ≫ g) ?_
            rw [Allegory.recip_comp, hAsym]
            have hrw : g° ≫ A ≫ A ≫ g = g° ≫ A ≫ g := by rw [← Cat.assoc A A g, hAidem]
            simp only [Cat.assoc] at hgAgF ⊢; rw [hrw]; exact hgAgF
          simpa only [Cat.assoc] using hgoal
        · have h := comp_mono_left (A ≫ g) F.2
          simp only [Cat.assoc, Cat.comp_id] at h ⊢; exact h
      -- `legA≫legA° = A≫f≫f°≫A` (absorbing E.e via `hAf`), likewise legB.
      have hAf' : A ≫ f ≫ E.1.idem.e = A ≫ f := hAf.symm
      have hAg' : A ≫ g ≫ F.1.idem.e = A ≫ g := hAg.symm
      have hLA : (A ≫ f ≫ E.1.idem.e) ≫ (A ≫ f ≫ E.1.idem.e)° = A ≫ (f ≫ f°) ≫ A := by
        rw [hAf', Allegory.recip_comp, hAsym]; simp only [Cat.assoc]
      have hLB : (A ≫ g ≫ F.1.idem.e) ≫ (A ≫ g ≫ F.1.idem.e)° = A ≫ (g ≫ g°) ≫ A := by
        rw [hAg', Allegory.recip_comp, hAsym]; simp only [Cat.assoc]
      -- Entire: `A ⊑ A≫(f≫f°)≫A`  (f entire: 1 ⊑ ff°).  Likewise g.
      have hEntA : A ⊑ (A ≫ f ≫ E.1.idem.e) ≫ (A ≫ f ≫ E.1.idem.e)° := by
        rw [hLA]
        calc A = A ≫ Cat.id c ≫ A := by rw [Cat.id_comp, hAidem]
          _ ⊑ A ≫ (f ≫ f°) ≫ A := comp_mono_left A (comp_mono_right hfent A)
      have hEntB : A ⊑ (A ≫ g ≫ F.1.idem.e) ≫ (A ≫ g ≫ F.1.idem.e)° := by
        rw [hLB]
        calc A = A ≫ Cat.id c ≫ A := by rw [Cat.id_comp, hAidem]
          _ ⊑ A ≫ (g ≫ g°) ≫ A := comp_mono_left A (comp_mono_right hgent A)
      -- Apex object `C = ⟨c, A⟩`, legs `A≫f≫E.e : C ⟶ E`, `A≫g≫F.e : C ⟶ F`.
      let C : SplCorObj 𝒜 := ⟨⟨c, ⟨A, hAsym, hAidem⟩⟩, hAcor⟩
      let legA : C ⟶ E := ⟨A ≫ f ≫ E.1.idem.e, by
            show A ≫ (A ≫ f ≫ E.1.idem.e) ≫ E.1.idem.e = A ≫ f ≫ E.1.idem.e
            simp only [Cat.assoc]; rw [hEidem, ← Cat.assoc A A (f ≫ E.1.idem.e), hAidem]⟩
      let legB : C ⟶ F := ⟨A ≫ g ≫ F.1.idem.e, by
            show A ≫ (A ≫ g ≫ F.1.idem.e) ≫ F.1.idem.e = A ≫ g ≫ F.1.idem.e
            simp only [Cat.assoc]; rw [hFidem, ← Cat.assoc A A (g ≫ F.1.idem.e), hAidem]⟩
      refine ⟨C, legA, legB, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      -- Map legA: Entire.
      · unfold Entire dom; apply SplHom.ext
        show A ∩ (A ≫ f ≫ E.1.idem.e) ≫ (A ≫ f ≫ E.1.idem.e)° = A
        exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hEntA)
      -- Map legA: Simple — E.e≫f°≫A≫f≫E.e ⊑ E.e.
      · unfold Simple; apply SplHom.ext
        show (A ≫ f ≫ E.1.idem.e)° ≫ (A ≫ f ≫ E.1.idem.e) ⊑ E.1.idem.e
        rw [Allegory.recip_comp, Allegory.recip_comp, hAsym, hEsym]
        simp only [Cat.assoc]
        rw [← Cat.assoc A A (f ≫ E.1.idem.e), hAidem]
        have key : E.1.idem.e ≫ f° ≫ A ≫ f ≫ E.1.idem.e ⊑ E.1.idem.e ≫ (f° ≫ f) ≫ E.1.idem.e := by
          have hAf' : f° ≫ A ≫ f ⊑ f° ≫ f :=
            comp_mono_left f° (by have h := comp_mono_right hAle f; rwa [Cat.id_comp] at h)
          have := comp_mono_left E.1.idem.e (comp_mono_right hAf' E.1.idem.e)
          simpa only [Cat.assoc] using this
        refine le_trans key ?_
        calc E.1.idem.e ≫ (f° ≫ f) ≫ E.1.idem.e
            ⊑ E.1.idem.e ≫ Cat.id E.1.carrier ≫ E.1.idem.e :=
              comp_mono_left _ (comp_mono_right hfsim _)
          _ = E.1.idem.e := by rw [Cat.id_comp, hEidem]
      -- Map legB: Entire.
      · unfold Entire dom; apply SplHom.ext
        show A ∩ (A ≫ g ≫ F.1.idem.e) ≫ (A ≫ g ≫ F.1.idem.e)° = A
        exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hEntB)
      -- Map legB: Simple.
      · unfold Simple; apply SplHom.ext
        show (A ≫ g ≫ F.1.idem.e)° ≫ (A ≫ g ≫ F.1.idem.e) ⊑ F.1.idem.e
        rw [Allegory.recip_comp, Allegory.recip_comp, hAsym, hFsym]
        simp only [Cat.assoc]
        rw [← Cat.assoc A A (g ≫ F.1.idem.e), hAidem]
        have key : F.1.idem.e ≫ g° ≫ A ≫ g ≫ F.1.idem.e ⊑ F.1.idem.e ≫ (g° ≫ g) ≫ F.1.idem.e := by
          have hAg' : g° ≫ A ≫ g ⊑ g° ≫ g :=
            comp_mono_left g° (by have h := comp_mono_right hAle g; rwa [Cat.id_comp] at h)
          have := comp_mono_left F.1.idem.e (comp_mono_right hAg' F.1.idem.e)
          simpa only [Cat.assoc] using this
        refine le_trans key ?_
        calc F.1.idem.e ≫ (g° ≫ g) ≫ F.1.idem.e
            ⊑ F.1.idem.e ≫ Cat.id F.1.carrier ≫ F.1.idem.e :=
              comp_mono_left _ (comp_mono_right hgsim _)
          _ = F.1.idem.e := by rw [Cat.id_comp, hFidem]
      -- Ψ = legA° ≫ legB:  Ψ.R = E.e≫f°≫A≫g≫F.e.  Freyd §2.166 two displays.
      · apply SplHom.ext
        show Ψ.R = (A ≫ f ≫ E.1.idem.e)° ≫ (A ≫ g ≫ F.1.idem.e)
        have hRleg : (A ≫ f ≫ E.1.idem.e)° ≫ (A ≫ g ≫ F.1.idem.e)
            = E.1.idem.e ≫ f° ≫ A ≫ g ≫ F.1.idem.e := by
          rw [Allegory.recip_comp, Allegory.recip_comp, hAsym, hEsym]; simp only [Cat.assoc]
          rw [← Cat.assoc A A (g ≫ F.1.idem.e), hAidem]
        rw [hRleg]
        apply le_antisymm
        · -- Display 2:  Ψ.R = Ψ.R ∩ f°g ⊑ f°(1∩fΨg°)g = f°Ag,  then E.e/F.e-wrap.
          -- `f° ∩ Ψ.R≫g° ⊑ f°≫A`  is `dual_modular_le f° (id c) (Ψ.R≫g°)` (since `f°≫id = f°`,
          --  `f°° = f`, so `(f°≫id)∩Z ⊑ f°≫(id ∩ f≫Z) = f°≫A`).
          have hfA : f° ∩ Ψ.R ≫ g° ⊑ f° ≫ A := by
            have h := dual_modular_le f° (Cat.id c) (Ψ.R ≫ g°)
            rw [Cat.comp_id, Allegory.recip_recip] at h
            simpa only [Cat.assoc] using h
          -- (f°≫g) ∩ Ψ.R ⊑ f°≫A≫g  (modular + hfA).
          have hfAg : (f° ≫ g) ∩ Ψ.R ⊑ f° ≫ A ≫ g :=
            le_trans (modular_le f° g Ψ.R)
              (by have := comp_mono_right hfA g; simpa only [Cat.assoc] using this)
          -- Ψ.R = Ψ.R ∩ f°g ⊑ f°Ag ⊑ E.e≫f°Ag≫F.e.
          have hΨfix : Ψ.R = E.1.idem.e ≫ Ψ.R ≫ F.1.idem.e := by rw [← Cat.assoc, hΨL, hΨR]
          calc Ψ.R = E.1.idem.e ≫ Ψ.R ≫ F.1.idem.e := hΨfix
            _ ⊑ E.1.idem.e ≫ (f° ≫ A ≫ g) ≫ F.1.idem.e := by
                  refine comp_mono_left _ (comp_mono_right ?_ _)
                  have hAbs : Ψ.R = (f° ≫ g) ∩ Ψ.R :=
                    le_antisymm (le_inter hRle (le_refl _)) (inter_lb_right _ _)
                  rw [hAbs]; exact hfAg
            _ = E.1.idem.e ≫ f° ≫ A ≫ g ≫ F.1.idem.e := by simp only [Cat.assoc]
        · -- Display 1: E.e≫f°≫A≫g≫F.e ⊑ E.e≫(f°≫f)≫Ψ.R≫(g°≫g)≫F.e ⊑ E.e≫Ψ.R≫F.e = Ψ.R.
          have hbound : E.1.idem.e ≫ (f° ≫ f) ≫ Ψ.R ≫ (g° ≫ g) ≫ F.1.idem.e
              ⊑ E.1.idem.e ≫ Cat.id E.1.carrier ≫ Ψ.R ≫ Cat.id F.1.carrier ≫ F.1.idem.e := by
            refine comp_mono_left _ (le_trans (comp_mono_right hfsim _) ?_)
            refine comp_mono_left _ (comp_mono_left _ ?_)
            exact comp_mono_right hgsim _
          have hstep1 : E.1.idem.e ≫ f° ≫ A ≫ g ≫ F.1.idem.e
              ⊑ E.1.idem.e ≫ (f° ≫ f) ≫ Ψ.R ≫ (g° ≫ g) ≫ F.1.idem.e := by
            refine le_trans (comp_mono_left _ (comp_mono_left _ (comp_mono_right hAfΨg _))) ?_
            simp only [Cat.assoc]; exact le_refl _
          have hend : E.1.idem.e ≫ Cat.id E.1.carrier ≫ Ψ.R ≫ Cat.id F.1.carrier ≫ F.1.idem.e = Ψ.R := by
            rw [Cat.id_comp, Cat.id_comp, ← Cat.assoc E.1.idem.e Ψ.R F.1.idem.e, hΨL, hΨR]
          exact hend ▸ le_trans hstep1 hbound
      -- Joint: legA≫legA° ∩ legB≫legB° = A≫(f≫f°∩g≫g°)≫A = A≫A = A = id_C.
      · apply SplHom.ext
        show (A ≫ f ≫ E.1.idem.e) ≫ (A ≫ f ≫ E.1.idem.e)° ∩
             (A ≫ g ≫ F.1.idem.e) ≫ (A ≫ g ≫ F.1.idem.e)° = A
        rw [hLA, hLB]
        -- A≫(f≫f°)≫A ∩ A≫(g≫g°)≫A = A≫(f≫f° ∩ g≫g°)≫A  (A symmetric simple).
        have hdistL : A ≫ (f ≫ f°) ≫ A ∩ A ≫ (g ≫ g°) ≫ A
            = A ≫ ((f ≫ f°) ≫ A ∩ (g ≫ g°) ≫ A) :=
          (simple_dist_inter hAsimple ((f ≫ f°) ≫ A) ((g ≫ g°) ≫ A)).symm
        have hdistR : (f ≫ f°) ≫ A ∩ (g ≫ g°) ≫ A = (f ≫ f° ∩ g ≫ g°) ≫ A :=
          (splCor_dist_inter_right hAsym hAsimple (f ≫ f°) (g ≫ g°)).symm
        rw [hdistL, hdistR, htab, Cat.id_comp, hAidem]
  }

/-- **§2.165**: If `𝒜` is a tabular allegory then `SplCorObj 𝒜` is pre-tabular.
    (Every morphism is already tabular, witnessed by `instTabularAllegorySplCor`.) -/
instance SplCorObj.instPreTabularAllegorySplCor {𝒜 : Type u} [TabularAllegory 𝒜] :
    PreTabularAllegory (SplCorObj 𝒜) :=
  { SplCorObj.instAllegorySplCor with
    pre_tabular := fun {E F} R =>
      ⟨R, le_refl _,
        @TabularAllegory.tabular (SplCorObj 𝒜) SplCorObj.instTabularAllegorySplCor E F R⟩ }

end Freyd.Alg
