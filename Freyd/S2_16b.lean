/-
  Freyd & Scedrov, *Categories and Allegories* — §2.165–§2.169: tabular and
  effective universal properties of the split-idempotent completion `Spl 𝒜`.

  This continues `Freyd/S2_21.lean` (§2.164, the construction of `Spl 𝒜`).  Here we
  prove the *structural* results of §2.165–§2.169 about `Spl 𝒜`:

  §2.163  A coreflexive splits iff it is tabular; an equivalence relation splits iff
          it is effective.  In `Spl 𝒜` *every* symmetric idempotent splits, so in
          particular every coreflexive and every equivalence relation split.
  §2.165  If `𝒜` is pre-tabular then `Spl 𝒜` remains pre-tabular.
  §2.166  An allegory is tabular iff it is pre-tabular and all coreflexives split.
          The constructive core is `tabulation_of_pre_tabular`: from a containment
          `R ⊑ f°g` with `ff° ∩ gg° = 1` and a splitting of the coreflexive
          `A = 1 ∩ fRg°` one builds a tabulation `(hf, hg)` of `R`.
  §2.167  `Spl 𝒜` is tabular when `𝒜` is pre-tabular (pre-tabular + coreflexives
          split ⟹ tabular).  This is the tabular reflection.
  §2.169  An EFFECTIVE allegory is one in which all equivalence relations split.
          `Spl 𝒜` is effective.

  Conventions: diagram-order composition `R ≫ S`, reciprocation `R°`, intersection
  `R ∩ S`, order `R ⊑ S`.  Mathlib-free.
-/

import Freyd.S2_02
import Freyd.S2_16
import Freyd.S2_22  -- le_comp_recip_comp (A4_1, via S2_22), symmetric_transitive_idempotent (§2.12)

universe v u

namespace Freyd.Alg

open Cat

variable {𝒜 : Type u} [Allegory 𝒜]

/-! ## §2.163  Splitting a symmetric idempotent *as a map*

  The book's notion of "split" for an EQUIVALENCE relation `E` (§2.163, §2.169) is:
  there is a map `f` with `f f° = E` and `f° f = 1`.  This is the "effective" form of
  splitting (legs are maps, not just morphisms).  We package it. -/

/-- `f : a ⟶ c` splits the endomorphism `E : a ⟶ a` *as a map* (§2.163): `f` is a map,
    `f ≫ f° = E`, and `f° ≫ f = 1_c`.  For a coreflexive this is §2.145 tabularity; for
    an equivalence relation this is §2.169 effectiveness. -/
def SplitsAsMap {a c : 𝒜} (f : a ⟶ c) (E : a ⟶ a) : Prop :=
  Map f ∧ f ≫ f° = E ∧ f° ≫ f = Cat.id c

/-- A symmetric idempotent `E` of `𝒜` that splits as a map is symmetric and idempotent —
    so the notion is only ever applied to symmetric idempotents. -/
theorem SplitsAsMap.symm {a c : 𝒜} {f : a ⟶ c} {E : a ⟶ a} (h : SplitsAsMap f E) :
    E° = E := by
  obtain ⟨_, hff, _⟩ := h
  rw [← hff, Allegory.recip_comp, Allegory.recip_recip]

/-! ## §2.163 / §2.169  Every symmetric idempotent splits *as a map* in `Spl 𝒜`

  An endomorphism of `Spl 𝒜` is a `SplHom E E` for an object `E = (a, e)`; its
  underlying morphism `R : a ⟶ a` satisfies `e ≫ R ≫ e = R`.  If moreover `R` is a
  symmetric idempotent of `Spl 𝒜` — i.e. `R° = R` and `R ≫ R = R` *as split-homs*,
  equivalently as morphisms of `𝒜` (recip and composition are inherited) — then `R`
  is itself a symmetric idempotent of `𝒜`, and the new object `(a, R)` together with
  the leg `R : E ⟶ (a,R)` exhibits a *map* splitting of `R` in `Spl 𝒜`.

  This is the central effectiveness fact: relevant idempotents (coreflexives §2.163,
  equivalence relations §2.169) all split this way. -/

/-- Given a symmetric idempotent `Φ : E ⟶ E` of `Spl 𝒜` (so `Φ.R° = Φ.R`,
    `Φ.R ≫ Φ.R = Φ.R`), its underlying morphism is a symmetric idempotent of `𝒜`. -/
def SplHom.toSymIdem {E : SplObj 𝒜} (Φ : SplHom E E)
    (hsym : Φ.R° = Φ.R) (hidem : Φ.R ≫ Φ.R = Φ.R) : SymIdem E.carrier :=
  ⟨Φ.R, hsym, hidem⟩

/-- The splitting object `(a, Φ)` for a symmetric idempotent `Φ : E ⟶ E` of `Spl 𝒜`. -/
def SplHom.splitObj {E : SplObj 𝒜} (Φ : SplHom E E)
    (hsym : Φ.R° = Φ.R) (hidem : Φ.R ≫ Φ.R = Φ.R) : SplObj 𝒜 :=
  ⟨E.carrier, Φ.toSymIdem hsym hidem⟩

/-- The splitting leg `E ⟶ (a, Φ)` of a symmetric idempotent `Φ : E ⟶ E`: underlying
    morphism `Φ.R`.  Fixed condition `e ≫ Φ.R ≫ Φ.R = Φ.R`. -/
def SplHom.splitLeg {E : SplObj 𝒜} (Φ : SplHom E E)
    (hsym : Φ.R° = Φ.R) (hidem : Φ.R ≫ Φ.R = Φ.R) :
    SplHom E (Φ.splitObj hsym hidem) :=
  ⟨Φ.R, by
    show E.idem.e ≫ Φ.R ≫ Φ.R = Φ.R
    rw [hidem]; exact Φ.fixed_left⟩

/-- The reverse leg `(a, Φ) ⟶ E`: also underlying `Φ.R`. -/
def SplHom.splitLeg' {E : SplObj 𝒜} (Φ : SplHom E E)
    (hsym : Φ.R° = Φ.R) (hidem : Φ.R ≫ Φ.R = Φ.R) :
    SplHom (Φ.splitObj hsym hidem) E :=
  ⟨Φ.R, by
    show Φ.R ≫ Φ.R ≫ E.idem.e = Φ.R
    rw [← Cat.assoc, hidem]; exact Φ.fixed_right⟩

/-- **§2.164 / §2.169**: every symmetric idempotent `Φ` of `Spl 𝒜` SPLITS — the leg
    `splitLeg` is a map (entire + simple) of `Spl 𝒜` with `leg ≫ leg° = Φ` and
    `leg° ≫ leg = 1_{(a,Φ)}`.  Compare `EffectiveAllegory.split_symmetric_idempotent`:
    here the split leg is `Φ.R` regarded as a map `E ⟶ (a, Φ)`. -/
theorem SplHom.split_symmetric_idempotent {E : SplObj 𝒜} (Φ : SplHom E E)
    (hsym : Φ.R° = Φ.R) (hidem : Φ.R ≫ Φ.R = Φ.R) :
    let leg := Φ.splitLeg hsym hidem
    splComp leg (splRecip leg) = Φ ∧
    splComp (splRecip leg) leg = splId (Φ.splitObj hsym hidem) := by
  refine ⟨?_, ?_⟩
  · -- leg ≫ leg° = Φ.   underlying: Φ.R ≫ Φ.R° = Φ.R ≫ Φ.R = Φ.R.
    apply SplHom.ext
    show Φ.R ≫ Φ.R° = Φ.R
    rw [hsym, hidem]
  · -- leg° ≫ leg = 1_{(a,Φ)}.   underlying: Φ.R° ≫ Φ.R = Φ.R = id of (a,Φ).
    apply SplHom.ext
    show Φ.R° ≫ Φ.R = Φ.R
    rw [hsym, hidem]

-- §2.13: composition of maps is a map — now `Freyd.Alg.map_comp` in `S2_1.lean`.


/-! ## §2.166  Tabulation by splitting the apex coreflexive

  An allegory is TABULAR iff it is pre-tabular and all coreflexive morphisms split
  (§2.166).  The forward direction is immediate; the converse is the construction
  below.  Given a (source-apex) tabulation `(f, g)` of `U = f° ≫ g` (maps `f : c→a`,
  `g : c→b`) and a containment `R ⊑ U`, the coreflexive `A := 1_c ∩ f ≫ R ≫ g°` on
  the apex `c` carries the "image of `R` on the apex".  Splitting `A` by a map
  `h : d ⟶ c` (`h° ≫ h = A`, `h ≫ h° = 1_d`) yields refined legs `(h ≫ f, h ≫ g)`, and

      `(h ≫ f)° ≫ (h ≫ g) = f° ≫ (h° ≫ h) ≫ g = f° ≫ A ≫ g`.

  So `(h ≫ f, h ≫ g)` tabulates `R` IFF `R = f° ≫ A ≫ g` — the APEX-SATURATION of `R`.
  This is genuinely necessary, *not* automatic: it fails for a non-difunctional
  `R ⊑ U`.  We record the honest content: for an apex-saturated `R`, splitting the apex
  coreflexive tabulates `R`.  (`R = U` and every difunctional `R ⊑ U` are saturated.)

  Conventions: repo `Tabulates f g R := Map f ∧ Map g ∧ R = f° ≫ g ∧ ff° ∩ gg° = 1`. -/

/-- The **apex coreflexive** `A = 1_c ∩ f ≫ R ≫ g°` of `R` relative to the tabulation
    `(f,g)` of `U = f° ≫ g` (§2.166): the image of `R` pushed onto the apex `c`. -/
def tabApex {a b c : 𝒜} (f : c ⟶ a) (g : c ⟶ b) (R : a ⟶ b) : c ⟶ c :=
  Cat.id c ∩ f ≫ R ≫ g°

/-- The apex coreflexive sits below each of `f ≫ f°` and `g ≫ g°`.  Trivially, since
    `tabApex ⊑ 1_c` (coreflexive) and `1_c ⊑ f ≫ f°`, `1_c ⊑ g ≫ g°` (f, g entire). -/
theorem tabApex_le_legs {a b c : 𝒜} {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b}
    (hf : Map f) (hg : Map g) (_hRS : R ⊑ f° ≫ g) :
    tabApex f g R ⊑ f ≫ f° ∧ tabApex f g R ⊑ g ≫ g° := by
  have hfe : Cat.id c ⊑ f ≫ f° := by
    have := hf.1; dsimp [Entire, dom] at this; rw [← this]; exact inter_lb_right _ _
  have hge : Cat.id c ⊑ g ≫ g° := by
    have := hg.1; dsimp [Entire, dom] at this; rw [← this]; exact inter_lb_right _ _
  exact ⟨le_trans (inter_lb_left _ _) hfe, le_trans (inter_lb_left _ _) hge⟩


/-- If a map `h : d ⟶ c` splits a coreflexive `A` (`h° ≫ h = A`, `h ≫ h° = 1_d`) and
    `A ⊑ M`, then `1_d ⊑ h ≫ M ≫ h°`.  Proof:
    `1_d = hh° = h(h°h)h° ⊑ h M h°`, using `h(h°h) = (hh°)h = h`. -/
theorem id_le_split_conj {c d : 𝒜} {h : d ⟶ c} {A M : c ⟶ c}
    (hhA : h° ≫ h = A) (hh1 : h ≫ h° = Cat.id d) (hAM : A ⊑ M) :
    Cat.id d ⊑ h ≫ M ≫ h° := by
  have hmid : h ≫ (h° ≫ h) ≫ h° = h ≫ h° := by
    have e : (h° ≫ h) ≫ h° = h° := by rw [Cat.assoc, hh1, Cat.comp_id]
    rw [e]
  calc Cat.id d = h ≫ h° := hh1.symm
    _ = h ≫ (h° ≫ h) ≫ h° := hmid.symm
    _ ⊑ h ≫ M ≫ h° := by rw [hhA]; exact comp_mono_left h (comp_mono_right hAM h°)

/-- **§2.166 (apex-split tabulation).**  Let `(f,g)` tabulate `U = f° ≫ g` and let
    `R ⊑ U` be APEX-SATURATED (`R = f° ≫ tabApex f g R ≫ g`).  If a map `h : d ⟶ c`
    SPLITS the apex coreflexive — `h° ≫ h = tabApex f g R`, `h ≫ h° = 1_d` — then the
    refined legs `(h ≫ f, h ≫ g)` form a genuine tabulation of `R`. -/
theorem tabulation_of_split_apex {a b c d : 𝒜}
    {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b} {h : d ⟶ c}
    (hf : Map f) (hg : Map g) (hRS : R ⊑ f° ≫ g)
    (htab : f ≫ f° ∩ g ≫ g° = Cat.id c)
    (hh : Map h) (hhA : h° ≫ h = tabApex f g R) (hh1 : h ≫ h° = Cat.id d)
    (hsat : R = f° ≫ (tabApex f g R) ≫ g) :
    Tabulates (h ≫ f) (h ≫ g) R := by
  have hFmap : Map (h ≫ f) := map_comp hh hf
  have hGmap : Map (h ≫ g) := map_comp hh hg
  obtain ⟨hAf, hAg⟩ := tabApex_le_legs hf hg hRS
  have hhcoref : h° ≫ h ⊑ Cat.id c := hhA ▸ inter_lb_left _ _
  have hReq : R = (h ≫ f)° ≫ (h ≫ g) := by
    rw [Allegory.recip_comp]
    calc R = f° ≫ (tabApex f g R) ≫ g := hsat
      _ = f° ≫ (h° ≫ h) ≫ g := by rw [hhA]
      _ = (f° ≫ h°) ≫ h ≫ g := by simp [Cat.assoc]
  have hFF : (h ≫ f) ≫ (h ≫ f)° = h ≫ (f ≫ f°) ≫ h° := by
    rw [Allegory.recip_comp]; simp [Cat.assoc]
  have hGG : (h ≫ g) ≫ (h ≫ g)° = h ≫ (g ≫ g°) ≫ h° := by
    rw [Allegory.recip_comp]; simp [Cat.assoc]
  have hApex : (h ≫ f) ≫ (h ≫ f)° ∩ (h ≫ g) ≫ (h ≫ g)° = Cat.id d := by
    refine le_antisymm ?_ ?_
    · -- M ⊑ id_d:  M = h(h° M h)h°,  and  h° M h ⊑ ff° ∩ gg° = id_c.
      -- For any leg L: h°(hLh°)h = (h°h)L(h°h) ⊑ L.
      have hsqueeze : ∀ L : c ⟶ c, h° ≫ (h ≫ L ≫ h°) ≫ h ⊑ L := by
        intro L
        have e : h° ≫ (h ≫ L ≫ h°) ≫ h = (h° ≫ h) ≫ L ≫ (h° ≫ h) := by simp [Cat.assoc]
        rw [e]
        have s1 : (h° ≫ h) ≫ L ≫ (h° ≫ h) ⊑ Cat.id c ≫ L ≫ (h° ≫ h) :=
          comp_mono_right hhcoref _
        have s2 : Cat.id c ≫ L ≫ (h° ≫ h) ⊑ Cat.id c ≫ L ≫ Cat.id c :=
          comp_mono_left _ (comp_mono_left _ hhcoref)
        have s3 : Cat.id c ≫ L ≫ Cat.id c = L := by rw [Cat.id_comp, Cat.comp_id]
        have := le_trans s1 s2; rw [s3] at this; exact this
      have hMconj : h° ≫ ((h ≫ f) ≫ (h ≫ f)° ∩ (h ≫ g) ≫ (h ≫ g)°) ≫ h ⊑ Cat.id c := by
        rw [← htab]
        refine le_inter ?_ ?_
        · refine le_trans (comp_mono_left h° (comp_mono_right (inter_lb_left _ _) h)) ?_
          rw [hFF]; exact hsqueeze (f ≫ f°)
        · refine le_trans (comp_mono_left h° (comp_mono_right (inter_lb_right _ _) h)) ?_
          rw [hGG]; exact hsqueeze (g ≫ g°)
      -- M = (h h°) M (h h°) = h (h° M h) h° ⊑ h id_c h° = id_d.
      have hMeq : ((h ≫ f) ≫ (h ≫ f)° ∩ (h ≫ g) ≫ (h ≫ g)°) =
          (h ≫ h°) ≫ ((h ≫ f) ≫ (h ≫ f)° ∩ (h ≫ g) ≫ (h ≫ g)°) ≫ (h ≫ h°) := by
        rw [hh1, Cat.id_comp, Cat.comp_id]
      rw [hMeq]
      have hstep1 : (h ≫ h°) ≫ ((h ≫ f) ≫ (h ≫ f)° ∩ (h ≫ g) ≫ (h ≫ g)°) ≫ (h ≫ h°) =
          h ≫ (h° ≫ ((h ≫ f) ≫ (h ≫ f)° ∩ (h ≫ g) ≫ (h ≫ g)°) ≫ h) ≫ h° := by
        simp [Cat.assoc]
      rw [hstep1]
      have hstep2 : h ≫ (h° ≫ ((h ≫ f) ≫ (h ≫ f)° ∩ (h ≫ g) ≫ (h ≫ g)°) ≫ h) ≫ h° ⊑
          h ≫ Cat.id c ≫ h° := comp_mono_left h (comp_mono_right hMconj h°)
      have hstep3 : h ≫ Cat.id c ≫ h° = Cat.id d := by rw [Cat.id_comp, hh1]
      exact hstep3 ▸ hstep2
    · refine le_inter ?_ ?_
      · rw [hFF]; exact id_le_split_conj hhA hh1 hAf
      · rw [hGG]; exact id_le_split_conj hhA hh1 hAg
  exact ⟨hFmap, hGmap, hReq, hApex⟩

/-! ## §2.166  Tabular ⟺ pre-tabular and coreflexives split

  • FORWARD (tabular ⟹ coreflexives split): in a `TabularAllegory` every coreflexive
    splits — `S2_2.coreflexive_splits` (the splitting map `g : c → a` points from the apex).
  • CONVERSE: given a pre-tabular containment and a splitting of the apex coreflexive
    of an apex-saturated `R`, `R` is tabular (`tabulation_of_split_apex`). -/

/-- **§2.166 (converse, apex-saturated form)**: a containment `R ⊑ U` whose apex
    coreflexive splits, and which is apex-saturated, is tabular. -/
theorem tabular_of_split_apex {a b c d : 𝒜}
    {f : c ⟶ a} {g : c ⟶ b} {R : a ⟶ b} {h : d ⟶ c}
    (hf : Map f) (hg : Map g) (hRS : R ⊑ f° ≫ g)
    (htab : f ≫ f° ∩ g ≫ g° = Cat.id c)
    (hh : Map h) (hhA : h° ≫ h = tabApex f g R) (hh1 : h ≫ h° = Cat.id d)
    (hsat : R = f° ≫ (tabApex f g R) ≫ g) :
    Tabular R :=
  ⟨d, h ≫ f, h ≫ g, tabulation_of_split_apex hf hg hRS htab hh hhA hh1 hsat⟩

/-! ## §2.169  Effective reflection: equivalence relations split in `Spl 𝒜`

  An EFFECTIVE allegory is one in which all equivalence relations split (§2.169); by
  §2.163 this is equivalent to effectiveness of its category of maps.  Since `Spl 𝒜`
  splits *every* symmetric idempotent (`SplHom.split_symmetric_idempotent`), and every
  equivalence relation is a symmetric idempotent, `Spl 𝒜` is effective. -/

/-- An EQUIVALENCE relation `E : a ⟶ a` (§2.12): reflexive, symmetric, transitive. -/
structure EquivRel (a : 𝒜) where
  /-- The underlying endomorphism. -/
  E : a ⟶ a
  /-- REFLEXIVE: `1_a ⊑ E`. -/
  refl : Reflexive E
  /-- SYMMETRIC: `E° ⊑ E`. -/
  sym : Symmetric E
  /-- TRANSITIVE: `E ≫ E ⊑ E`. -/
  trans : Transitive E

namespace EquivRel

variable {a : 𝒜}

/-- An equivalence relation is symmetric in the strong sense `E° = E`. -/
theorem recip_eq (E : EquivRel a) : E.E° = E.E :=
  le_antisymm E.sym (by have := recip_mono E.sym; rwa [Allegory.recip_recip] at this)

/-- An equivalence relation is idempotent `E ≫ E = E`: `⊑` by transitivity, `⊒` since
    `E = 1 ≫ E ⊑ E ≫ E` using reflexivity. -/
theorem idem (E : EquivRel a) : E.E ≫ E.E = E.E := by
  refine le_antisymm E.trans ?_
  calc E.E = Cat.id a ≫ E.E := by rw [Cat.id_comp]
    _ ⊑ E.E ≫ E.E := comp_mono_right E.refl E.E

/-- An equivalence relation is a symmetric idempotent (§2.12, §2.163). -/
def toSymIdem (E : EquivRel a) : SymIdem a :=
  ⟨E.E, E.recip_eq, E.idem⟩

end EquivRel

/-- **§2.169**: every equivalence relation of `Spl 𝒜` splits.  An equivalence relation
    on an object `E = (a,e)` of `Spl 𝒜` is a split-hom `Φ : E ⟶ E` that is reflexive
    (`1_{E} ⊑ Φ`), symmetric (`Φ.R° = Φ.R`) and transitive (`Φ.R ≫ Φ.R ⊑ Φ.R`); being
    symmetric + transitive over a reflexive carrier it is a symmetric idempotent, hence
    splits by `SplHom.split_symmetric_idempotent`.

    We state it for any `Φ` already known to be a symmetric idempotent (`hsym`,
    `hidem`) — which equivalence relations are — giving the splitting legs explicitly. -/
theorem spl_equivalence_splits {E : SplObj 𝒜} (Φ : SplHom E E)
    (hsym : Φ.R° = Φ.R) (hidem : Φ.R ≫ Φ.R = Φ.R) :
    ∃ (G : SplObj 𝒜) (leg : SplHom E G),
      splComp leg (splRecip leg) = Φ ∧ splComp (splRecip leg) leg = splId G :=
  ⟨Φ.splitObj hsym hidem, Φ.splitLeg hsym hidem, Φ.split_symmetric_idempotent hsym hidem⟩

/-! ## §2.169  `Spl 𝒜` is effective in the `EffectiveAllegory` shape

  `EffectiveAllegory.split_symmetric_idempotent` asks: a symmetric idempotent `E`
  splits as `E = f ≫ f°` with `f` a MAP and `f° ≫ f = 1`.  For a general symmetric
  idempotent the leg is simple but not entire (entireness `1 ⊑ E` requires `E`
  REFLEXIVE).  Exactly the REFLEXIVE symmetric idempotents — the EQUIVALENCE relations
  — split with a *map* leg, which is the §2.169 effectiveness condition (equivalence
  relations split, the leg being a map).  We prove this map-shaped splitting in
  `Spl 𝒜`. -/

/-- **§2.169 (effective shape)**: a REFLEXIVE symmetric idempotent `Φ` of `Spl 𝒜` (an
    equivalence relation: `E.idem.e ⊑ Φ.R`, `Φ.R° = Φ.R`, `Φ.R ≫ Φ.R = Φ.R`) splits
    with a MAP leg, matching `EffectiveAllegory.split_symmetric_idempotent`:
    there is `G` and a `Map`-leg `f : E ⟶ G` with `f ≫ f° = Φ` and `f° ≫ f = 1_G`. -/
theorem spl_equivalence_splits_map {E : SplObj 𝒜} (Φ : SplHom E E)
    (hrefl : E.idem.e ⊑ Φ.R) (hsym : Φ.R° = Φ.R) (hidem : Φ.R ≫ Φ.R = Φ.R) :
    ∃ (G : SplObj 𝒜) (f : E ⟶ G),
      Map f ∧ f ≫ f° = Φ ∧ f° ≫ f = Cat.id G := by
  refine ⟨Φ.splitObj hsym hidem, Φ.splitLeg hsym hidem, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- Entire in `Spl 𝒜`: `dom f = id E`, i.e. `id E ∩ f ≫ f° = id E`.  Underlying:
    -- `e ∩ Φ.R ≫ Φ.R° = e`; with `Φ.R° = Φ.R`, `Φ.R ≫ Φ.R = Φ.R` this is `e ∩ Φ.R = e`,
    -- true since `e ⊑ Φ.R` (reflexivity).
    show dom (Φ.splitLeg hsym hidem) = Cat.id E
    apply SplHom.ext
    show E.idem.e ∩ Φ.R ≫ Φ.R° = E.idem.e
    rw [hsym, hidem]
    exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hrefl)
  · -- Simple in `Spl 𝒜`: `f° ≫ f ⊑ id G`.  Underlying `Φ.R° ≫ Φ.R = Φ.R = id G`.
    dsimp only [Simple]
    have he : (Φ.splitLeg hsym hidem)° ≫ (Φ.splitLeg hsym hidem) = Cat.id (Φ.splitObj hsym hidem) := by
      apply SplHom.ext; show Φ.R° ≫ Φ.R = Φ.R; rw [hsym, hidem]
    rw [he]; exact le_refl _
  · -- f ≫ f° = Φ.
    apply SplHom.ext; show Φ.R ≫ Φ.R° = Φ.R; rw [hsym, hidem]
  · -- f° ≫ f = id G.
    apply SplHom.ext; show Φ.R° ≫ Φ.R = Φ.R; rw [hsym, hidem]

/-! ## §2.16(11)  Neighboring idempotents

  "We say that a pair of idempotents in a category are neighbors if `ee'e = e`,
  `e'ee' = e'`."  If either of a neighboring pair of idempotents splits, then so does
  the other.  For an idempotent `A` in an allegory, `A ∩ A°` is symmetric and
  transitive, hence a symmetric idempotent; the containments
  `(A∩A°)A(A∩A°) ⊑ A∩A°` and `A ⊑ A(A∩A°)A` are the necessary and sufficient
  conditions for the existence of an extension of `A`'s allegory in which `A` splits —
  the converse containments are automatic, so they make `A` and `A ∩ A°` neighbors.
  `A ∩ A°` splits in `Spl 𝒜` (which splits all symmetric idempotents, §2.164), hence
  so does `A`: "when we have split all the symmetric idempotents we have automatically
  split all idempotents that can ever be split in an allegory." -/

section NeighborsInCategory

variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-- Two idempotents `e, e'` in a category are NEIGHBORS (§2.16(11)):
    `e ≫ e' ≫ e = e` and `e' ≫ e ≫ e' = e'`.  (The book assumes both endomorphisms
    idempotent wherever the notion is used; the definition itself does not need it.) -/
def Neighbors {a : 𝒞} (e e' : a ⟶ a) : Prop :=
  e ≫ e' ≫ e = e ∧ e' ≫ e ≫ e' = e'

/-- Neighborliness is symmetric. -/
theorem Neighbors.symm {a : 𝒞} {e e' : a ⟶ a} (h : Neighbors e e') : Neighbors e' e :=
  ⟨h.2, h.1⟩

/-- `⟨x, y⟩` SPLITS the endomorphism `e` in a category (§1.281, §2.164): `x ≫ y = e`
    and `y ≫ x = 1`.  Any such `e` is automatically idempotent:
    `e ≫ e = x ≫ (y ≫ x) ≫ y = x ≫ y = e`. -/
def CatSplits {a : 𝒞} (e : a ⟶ a) : Prop :=
  ∃ (c : 𝒞) (x : a ⟶ c) (y : c ⟶ a), x ≫ y = e ∧ y ≫ x = Cat.id c

/-- **§2.16(11)**: "if either of a neighboring pair of idempotents splits, then so
    does the other."  If `⟨x, y⟩` splits `e` then `⟨e' ≫ x, y ≫ e'⟩` splits its
    neighbor `e'`.  Book computation: `(e'x)(ye') = e'ee' = e'` and
    `(ye')(e'x) = ye'x = y(xy)e'(xy)x = yee'ex = yex = y(xy)x = (yx)(yx) = 1`.
    (Only `e'`'s idempotency is needed; `e`'s follows from the splitting.) -/
theorem neighbors_split_transfer {a : 𝒞} {e e' : a ⟶ a}
    (he' : e' ≫ e' = e') (hn : Neighbors e e') (hs : CatSplits e) : CatSplits e' := by
  obtain ⟨c, x, y, hxy, hyx⟩ := hs
  -- The key collapse: `y ≫ e' ≫ x = 1`, by inserting `1 = y ≫ x` on both ends.
  have key : y ≫ e' ≫ x = Cat.id c := by
    calc y ≫ e' ≫ x
        = (y ≫ x) ≫ (y ≫ e' ≫ x) ≫ y ≫ x := by rw [hyx, Cat.id_comp, Cat.comp_id]
      _ = y ≫ (x ≫ y) ≫ e' ≫ (x ≫ y) ≫ x := by simp [Cat.assoc]
      _ = y ≫ e ≫ e' ≫ e ≫ x := by rw [hxy]
      _ = y ≫ (e ≫ e' ≫ e) ≫ x := by simp [Cat.assoc]
      _ = y ≫ e ≫ x := by rw [hn.1]
      _ = (y ≫ x) ≫ y ≫ x := by rw [← hxy]; simp [Cat.assoc]
      _ = Cat.id c := by rw [hyx, Cat.id_comp]
  refine ⟨c, e' ≫ x, y ≫ e', ?_, ?_⟩
  · -- `(e'x)(ye') = e'ee' = e'`.
    calc (e' ≫ x) ≫ y ≫ e' = e' ≫ (x ≫ y) ≫ e' := by simp [Cat.assoc]
      _ = e' ≫ e ≫ e' := by rw [hxy]
      _ = e' := hn.2
  · -- `(ye')(e'x) = ye'x = 1` (`e'` idempotent, then `key`).
    calc (y ≫ e') ≫ e' ≫ x = y ≫ (e' ≫ e') ≫ x := by simp [Cat.assoc]
      _ = y ≫ e' ≫ x := by rw [he']
      _ = Cat.id c := key

end NeighborsInCategory

/-! ### §2.16(11)  `A ∩ A°` is a symmetric idempotent; the neighbor containments -/

/-- **§2.16(11)**: for an idempotent `A` in an allegory, "`A ∩ A°` is symmetric and
    transitive, hence an idempotent" — a SYMMETRIC idempotent.  Symmetry needs no
    hypothesis; transitivity and idempotency use `A ≫ A = A`
    (via `symmetric_transitive_idempotent`, §2.12). -/
theorem inter_recip_symm_trans_idem {a : 𝒜} (A : a ⟶ a) (hA : A ≫ A = A) :
    (A ∩ A°)° = A ∩ A° ∧ (A ∩ A°) ≫ (A ∩ A°) ⊑ A ∩ A° ∧
      (A ∩ A°) ≫ (A ∩ A°) = A ∩ A° := by
  have hsym : (A ∩ A°)° = A ∩ A° := by
    rw [Allegory.recip_inter, Allegory.recip_recip, Allegory.inter_comm]
  have htrans : (A ∩ A°) ≫ (A ∩ A°) ⊑ A ∩ A° := by
    refine le_inter ?_ ?_
    · -- `(A∩A°)(A∩A°) ⊑ A ≫ A = A`.
      have h := le_trans (comp_mono_right (inter_lb_left A A°) (A ∩ A°))
                         (comp_mono_left A (inter_lb_left A A°))
      rwa [hA] at h
    · -- `(A∩A°)(A∩A°) ⊑ A° ≫ A° = (A ≫ A)° = A°`.
      have h := le_trans (comp_mono_right (inter_lb_right A A°) (A ∩ A°))
                         (comp_mono_left A° (inter_lb_right A A°))
      have hAr : A° ≫ A° = A° := by rw [← Allegory.recip_comp, hA]
      rwa [hAr] at h
  exact ⟨hsym, htrans, symmetric_transitive_idempotent ((symmetric_iff _).mpr hsym) htrans⟩

/-- The symmetric idempotent `A ∩ A°` of an idempotent `A` (§2.16(11)), packaged as a
    `SymIdem` — the shape `Spl 𝒜` splits (§2.164). -/
def interRecipSymIdem {a : 𝒜} (A : a ⟶ a) (hA : A ≫ A = A) : SymIdem a :=
  ⟨A ∩ A°, (inter_recip_symm_trans_idem A hA).1, (inter_recip_symm_trans_idem A hA).2.2⟩

/-- **§2.16(11)**: the containments `(A∩A°)A(A∩A°) ⊑ A∩A°` and `A ⊑ A(A∩A°)A` make the
    idempotent `A` and the symmetric idempotent `A ∩ A°` NEIGHBORS — "the converse
    containments are automatic":
    `A∩A° ⊑ (A∩A°)³ ⊑ (A∩A°)A(A∩A°)` (by `X ⊑ XX°X` and `A∩A° ⊑ A`), and
    `A(A∩A°)A ⊑ A³ ⊑ A`. -/
theorem neighbors_of_containments {a : 𝒜} (A : a ⟶ a) (hA : A ≫ A = A)
    (h1 : (A ∩ A°) ≫ A ≫ (A ∩ A°) ⊑ A ∩ A°)
    (h2 : A ⊑ A ≫ (A ∩ A°) ≫ A) : Neighbors A (A ∩ A°) := by
  obtain ⟨hsym, -, -⟩ := inter_recip_symm_trans_idem A hA
  constructor
  · -- `A ≫ (A∩A°) ≫ A = A`: `⊑` via `A∩A° ⊑ A` and `A³ = A`; `⊒` is `h2`.
    refine le_antisymm ?_ h2
    have hstep : A ≫ (A ∩ A°) ≫ A ⊑ A ≫ A ≫ A :=
      comp_mono_left A (comp_mono_right (inter_lb_left A A°) A)
    have hAAA : A ≫ A ≫ A = A := by rw [hA, hA]
    rwa [hAAA] at hstep
  · -- `(A∩A°) ≫ A ≫ (A∩A°) = A∩A°`: `⊑` is `h1`; `⊒` via `A∩A° ⊑ (A∩A°)³ ⊑ (A∩A°)A(A∩A°)`.
    refine le_antisymm h1 ?_
    have h3 := le_comp_recip_comp (A ∩ A°)
    rw [hsym, Cat.assoc] at h3
    -- h3 : `A∩A° ⊑ (A∩A°) ≫ (A∩A°) ≫ (A∩A°)`
    refine le_trans h3 ?_
    exact comp_mono_left (A ∩ A°) (comp_mono_right (inter_lb_left A A°) (A ∩ A°))

/-! ### §2.16(11)  A splitting of `A` forces the neighbor containments

  "If `⟨R,S⟩` splits `A` then `A` and `A ∩ A°` are neighbors."  The book's chain,
  with `A = RS`, `SR = 1`:

    `(A∩A°)A(A∩A°) ⊑ (RS ∩ S°R°)RS(RS ∩ S°R°) ⊑ S°(SRS ∩ R°)RS(RSR ∩ S°)R°`
                  `⊑ S°(SRS)RS(RSR)R° ⊑ S°R° ⊑ A°`,
    `(A∩A°)A(A∩A°) ⊑ A³ ⊑ A`,
    `A ⊑ R(SRSR ∩ 1)S ⊑ RS(RS ∩ S°R°)RS ⊑ A(A∩A°)A`.

  With the splitting available, `SRS = S(RS)` collapses through `SR = 1`, so the
  modular-law bounds simplify to `A∩A° ⊑ S°S` and `A∩A° ⊑ RR°` before composing. -/

/-- **§2.16(11)**: if `⟨R, S⟩` splits the idempotent `A`, then `A` and `A ∩ A°` are
    neighbors. -/
theorem neighbors_of_catSplits {a : 𝒜} (A : a ⟶ a) (hA : A ≫ A = A)
    (h : CatSplits A) : Neighbors A (A ∩ A°) := by
  obtain ⟨c, R, S, hRS, hSR⟩ := h
  have hNeq : A ∩ A° = (S° ≫ R°) ∩ (R ≫ S) := by
    rw [← hRS, Allegory.recip_comp, Allegory.inter_comm]
  -- `A∩A° = S°R° ∩ RS ⊑ S°(R° ∩ SRS) = S°(R° ∩ S) ⊑ S°S`  (left modular + `SR = 1`).
  have hN1 : A ∩ A° ⊑ S° ≫ S := by
    have h := modular_le_left S° R° (R ≫ S)
    rw [Allegory.recip_recip, ← Cat.assoc, hSR, Cat.id_comp] at h
    rw [hNeq]
    exact le_trans h (comp_mono_left S° (inter_lb_right R° S))
  -- `A∩A° = S°R° ∩ RS ⊑ (S° ∩ RSR)R° = (S° ∩ R)R° ⊑ RR°`  (right modular + `SR = 1`).
  have hN2 : A ∩ A° ⊑ R ≫ R° := by
    have h := modular_le S° R° (R ≫ S)
    rw [Allegory.recip_recip, Cat.assoc, hSR, Cat.comp_id] at h
    rw [hNeq]
    exact le_trans h (comp_mono_right (inter_lb_right S° R) R°)
  -- First containment, `A°` half: `(A∩A°)A(A∩A°) ⊑ (S°S)(RS)(RR°) = S°(SR)(SR)R° = A°`.
  have hb : (A ∩ A°) ≫ A ≫ (A ∩ A°) ⊑ A° := by
    have hmono : (A ∩ A°) ≫ A ≫ (A ∩ A°) ⊑ (S° ≫ S) ≫ A ≫ (R ≫ R°) :=
      le_trans (comp_mono_right hN1 (A ≫ (A ∩ A°)))
               (comp_mono_left (S° ≫ S) (comp_mono_left A hN2))
    have hcollapse : (S° ≫ S) ≫ A ≫ (R ≫ R°) = A° := by
      rw [← hRS, Allegory.recip_comp]
      calc (S° ≫ S) ≫ (R ≫ S) ≫ R ≫ R°
          = S° ≫ (S ≫ R) ≫ (S ≫ R) ≫ R° := by simp [Cat.assoc]
        _ = S° ≫ R° := by rw [hSR, Cat.id_comp, Cat.id_comp]
    exact hcollapse ▸ hmono
  -- First containment, `A` half: `(A∩A°)A(A∩A°) ⊑ A³ = A`.
  have ha : (A ∩ A°) ≫ A ≫ (A ∩ A°) ⊑ A := by
    have hstep : (A ∩ A°) ≫ A ≫ (A ∩ A°) ⊑ A ≫ A ≫ A :=
      le_trans (comp_mono_right (inter_lb_left A A°) (A ≫ (A ∩ A°)))
               (comp_mono_left A (comp_mono_left A (inter_lb_left A A°)))
    have hAAA : A ≫ A ≫ A = A := by rw [hA, hA]
    rwa [hAAA] at hstep
  -- Second containment: `A = R(SRSR ∩ 1)S ⊑ RS(RS ∩ S°R°)RS = A(A∩A°)A`.
  have h2 : A ⊑ A ≫ (A ∩ A°) ≫ A := by
    have hm1 := modular_le_left S (R ≫ S ≫ R) (Cat.id c)
    rw [Cat.comp_id] at hm1
    -- hm1 : `(SRSR) ∩ 1 ⊑ S(RSR ∩ S°)`  (left modular)
    have hm2 := modular_le (R ≫ S) R S°
    rw [Cat.assoc] at hm2
    -- hm2 : `RSR ∩ S° ⊑ (RS ∩ S°R°)R`  (right modular)
    have hSRSR : S ≫ R ≫ S ≫ R = Cat.id c := by rw [hSR, Cat.comp_id, hSR]
    have hid : Cat.id c ⊑ (S ≫ R ≫ S ≫ R) ∩ Cat.id c := by
      rw [hSRSR, Allegory.inter_idem]; exact le_refl _
    have hchain : Cat.id c ⊑ S ≫ ((R ≫ S) ∩ S° ≫ R°) ≫ R :=
      le_trans hid (le_trans hm1 (comp_mono_left S hm2))
    have hmono := comp_mono_left R (comp_mono_right hchain S)
    -- hmono : `R ≫ 1 ≫ S ⊑ R(S(RS ∩ S°R°)R)S`
    have hL : R ≫ Cat.id c ≫ S = A := by rw [Cat.id_comp, hRS]
    have hR2 : R ≫ (S ≫ ((R ≫ S) ∩ S° ≫ R°) ≫ R) ≫ S = A ≫ (A ∩ A°) ≫ A := by
      rw [← hRS, Allegory.recip_comp]
      simp [Cat.assoc]
    rw [hL, hR2] at hmono
    exact hmono
  exact neighbors_of_containments A hA (le_inter ha hb) h2

/-! ### §2.16(11)  HEADLINE: the two containments make `A` split in `Spl 𝒜`

  "These last two containments are the necessary and sufficient conditions for the
  existence of an extension of `A` in which `A` splits: the converse containments are
  automatic, hence `A` and `A∩A°` are neighbors; if `𝒮ℐ𝒹` is the class of all
  symmetric idempotents then `A∩A°` splits in `Spl(𝒮ℐ𝒹)`, hence `A` splits in
  `Spl(𝒮ℐ𝒹`).  That is, when we have split all the symmetric idempotents we have
  automatically split all idempotents that can ever be split in an allegory."

  Our `SplObj 𝒜` is exactly `Spl(𝒮ℐ𝒹)`: it splits every symmetric idempotent of `𝒜`
  (§2.164, `embHom_idem_splits`).  Sufficiency is assembled below; necessity (a
  faithful representation into an allegory where `TA` splits forces the containments)
  is the §2.154-representation direction, not formalised here. -/

/-- **§2.16(11) (headline)**: an idempotent `A` of `𝒜` satisfying the two containments
    `(A∩A°)A(A∩A°) ⊑ A∩A°` and `A ⊑ A(A∩A°)A` SPLITS in `Spl 𝒜`.  Route: `A ∩ A°` is a
    symmetric idempotent, so its image splits in `Spl 𝒜` through the object
    `(a, A∩A°)` (§2.164); the containments make `A` and `A ∩ A°` neighbors, the
    embedding transports neighborliness, and a split transfers across neighbors. -/
theorem idempotent_splits_in_spl {a : 𝒜} (A : a ⟶ a) (hA : A ≫ A = A)
    (h1 : (A ∩ A°) ≫ A ≫ (A ∩ A°) ⊑ A ∩ A°)
    (h2 : A ⊑ A ≫ (A ∩ A°) ≫ A) :
    CatSplits (𝒞 := SplObj 𝒜) (a := embObj a) (embHom A) := by
  -- `embHom (A∩A°)` splits through the new object `(a, A∩A°)` (§2.164).
  have hsplitN : CatSplits (𝒞 := SplObj 𝒜) (a := embObj a) (embHom (A ∩ A°)) :=
    ⟨⟨a, interRecipSymIdem A hA⟩, splDown (interRecipSymIdem A hA),
     splUp (interRecipSymIdem A hA),
     splDown_up (interRecipSymIdem A hA), splUp_down (interRecipSymIdem A hA)⟩
  -- The embedding transports `Neighbors A (A∩A°)` (composition is inherited).
  have hnb : Neighbors A (A ∩ A°) := neighbors_of_containments A hA h1 h2
  have hnbSpl : Neighbors (𝒞 := SplObj 𝒜) (embHom (A ∩ A°)) (embHom A) := by
    constructor
    · apply SplHom.ext
      show (A ∩ A°) ≫ A ≫ (A ∩ A°) = A ∩ A°
      exact hnb.2
    · apply SplHom.ext
      show A ≫ (A ∩ A°) ≫ A = A
      exact hnb.1
  have hAidem : splComp (embHom A) (embHom A) = embHom A := by
    rw [← embHom_comp, hA]
  exact neighbors_split_transfer hAidem hnbSpl hsplitN

/-! ### §2.16(11)  Orderings cannot split

  The two containments now yield the book's closing observations: for a PARTIAL
  ORDERING (`T² ⊑ T`, `T ∩ T° = 1`) the first containment forces `T = 1`; for a
  STRICT DENSE partial ordering (`T² = T`, `T ∩ T° = 0`) the second forces `T = 0`. -/

/-- **§2.16(11)**: "If `T` is a partial ordering, that is, if `T² ⊑ T` and
    `T ∩ T° = 1`, then the first of the above containments `(T∩T°)T(T∩T°) ⊑ T∩T°`
    forces `T` to be the identity.  Non-trivial partial orderings cannot split in an
    allegory."  (Transitivity is part of the book's definition of a partial ordering;
    the containment `h1` alone does the forcing.) -/
theorem partialOrder_no_split {a : 𝒜} (T : a ⟶ a) (_htrans : T ≫ T ⊑ T)
    (hanti : T ∩ T° = Cat.id a)
    (h1 : (T ∩ T°) ≫ T ≫ (T ∩ T°) ⊑ T ∩ T°) : T = Cat.id a := by
  rw [hanti, Cat.id_comp, Cat.comp_id] at h1
  -- h1 : `T ⊑ 1`; and `1 = T ∩ T° ⊑ T`.
  have h2 : Cat.id a ⊑ T := by rw [← hanti]; exact inter_lb_left T T°
  exact le_antisymm h1 h2

section StrictDense

variable {ℬ : Type u} [DistributiveAllegory ℬ]

/-- **§2.16(11)**: "If `T` is a strict dense partial ordering, that is, if `T² = T`
    and `T ∩ T° = 0` (for example, the strict order on the rational numbers) then the
    second of the above containments forces `T` to be empty.  Non-trivial strict dense
    partial orderings cannot split in an allegory."

    NOTE: the book misprints the second containment here as `T ⊆ (T∩T°)T(T∩T°)`; "the
    second of the above containments" is `A ⊆ A(A∩A°)A`, i.e. `T ⊑ T(T∩T°)T`, which is
    what forces `T ⊑ T ≫ 0 ≫ T = 0` — the form used below.  (Idempotency is part of
    the book's definition of strict dense; the containment `h2` alone does the
    forcing.)  Stated over a distributive allegory, which supplies the zero morphism
    `𝟘` with its absorption laws (§2.21). -/
theorem strictDense_no_split {a : ℬ} (T : a ⟶ a) (_hidem : T ≫ T = T)
    (hdisj : T ∩ T° = (𝟘 : a ⟶ a))
    (h2 : T ⊑ T ≫ (T ∩ T°) ≫ T) : T = (𝟘 : a ⟶ a) := by
  rw [hdisj, DistributiveAllegory.zero_comp, DistributiveAllegory.comp_zero] at h2
  -- h2 : `T ⊑ 𝟘`; and `𝟘` is the minimum (§2.211).
  exact le_antisymm h2 (zero_le T)

end StrictDense

end Freyd.Alg
