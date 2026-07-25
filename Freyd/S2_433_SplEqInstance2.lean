/-
  Freyd & Scedrov, *Categories and Allegories* — §2.433: the REFLEXIVE splitting
  completion `Spl(Eq 𝒜)`.

  `SplEqObj 𝒜 = { E : SplObj 𝒜 // Cat.id E.carrier ⊑ E.idem.e }` restricts `SplObj 𝒜`
  to the objects whose symmetric idempotent is REFLEXIVE — i.e. the EQUIVALENCE
  RELATIONS of `𝒜`.  This is the reflexive analogue of the COREFLEXIVE sub-completion
  `SplCorObj 𝒜` (§2.34 / S2_165_Spl); homs are again the underlying `SplObj`-homs
  `SplHom E.1 F.1`, so `Cat`/`Allegory`/`Distributive`/`Division` all descend pointwise
  via `SplHom.ext`, byte-for-byte as for `SplCorObj`.

  Conventions: diagram-order composition `R ≫ S`, reciprocation `R°`, intersection
  `R ∩ S`, order `R ⊑ S`.  Mathlib-free.
-/
import Freyd.S2_43
import Freyd.S2_40

universe v u

namespace Freyd.Alg

open Cat

/-- The REFLEXIVE splitting completion of `𝒜`: restrict `SplObj 𝒜` to objects whose
    symmetric idempotent `E.idem.e` is REFLEXIVE (`Cat.id E.carrier ⊑ E.idem.e`), i.e.
    the EQUIVALENCE RELATIONS of `𝒜`.  This is Freyd's `Spl(Eq 𝒜)` (§2.433): split only
    the reflexive symmetric idempotents (equivalence relations).  The reflexive dual of
    `SplCorObj 𝒜` (§2.34), which splits only the coreflexives. -/
def SplEqObj (𝒜 : Type u) [Allegory 𝒜] : Type u :=
  { E : SplObj 𝒜 // Cat.id E.carrier ⊑ E.idem.e }

namespace SplEqObj

variable {𝒜 : Type u} [Allegory 𝒜]

/-- Category structure on `SplEqObj 𝒜`: homs and composition inherited from `SplObj 𝒜`. -/
instance instCatSplEq : Cat (SplEqObj 𝒜) where
  Hom E F     := SplHom E.1 F.1
  id E        := splId E.1
  comp R S    := splComp R S
  id_comp R   := SplHom.ext R.fixed_left
  comp_id R   := SplHom.ext R.fixed_right
  assoc _R _S _T := SplHom.ext (Cat.assoc _ _ _)

/-- Allegory structure on `SplEqObj 𝒜`: reciprocation and intersection inherited
    from `SplObj 𝒜`; all axioms reduce to the underlying `𝒜` axioms via `SplHom.ext`. -/
instance instAllegorySplEq : Allegory (SplEqObj 𝒜) where
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

end SplEqObj

/-- Order on `SplEqObj 𝒜` is read off the underlying `𝒜`-morphisms (the reflexive analogue
    of `splCorLe_iff`): `Φ ⊑ Ψ ↔ Φ.R ⊑ Ψ.R`. -/
theorem splEqLe_iff {𝒜 : Type u} [Allegory 𝒜] {E F : SplEqObj 𝒜} (Φ Ψ : E ⟶ F) :
    Φ ⊑ Ψ ↔ Φ.R ⊑ Ψ.R := by
  show splInter Φ Ψ = Φ ↔ Φ.R ∩ Ψ.R = Φ.R
  exact ⟨fun h => congrArg SplHom.R h, fun h => SplHom.ext h⟩

/-- **§2.21 (reflexive)**: if `𝒜` is distributive then so is `Spl(Eq 𝒜)`, with union and
    zero taken pointwise (`splUnion`, `splZero`).  Each law descends via `SplHom.ext`. -/
instance instDistributiveSplEq {𝒜 : Type u} [DistributiveAllegory 𝒜] :
    DistributiveAllegory (SplEqObj 𝒜) :=
  { SplEqObj.instAllegorySplEq with
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
      apply SplHom.ext; show R.R ∪ (S.R ∩ R.R) = R.R
      exact DistributiveAllegory.union_inter_absorb _ _
    inter_union_absorb := fun R S => by
      apply SplHom.ext; show (R.R ∪ S.R) ∩ R.R = R.R
      exact DistributiveAllegory.inter_union_absorb _ _
    comp_union_distrib := fun R S T => by
      apply SplHom.ext; show R.R ≫ (S.R ∪ T.R) = (R.R ≫ S.R) ∪ (R.R ≫ T.R)
      exact DistributiveAllegory.comp_union_distrib _ _ _
    inter_union_distrib := fun R S T => by
      apply SplHom.ext; show R.R ∩ (S.R ∪ T.R) = (R.R ∩ S.R) ∪ (R.R ∩ T.R)
      exact DistributiveAllegory.inter_union_distrib _ _ _
    zero_union := fun R => by
      apply SplHom.ext; show (𝟘 : _ ⟶ _) ∪ R.R = R.R; exact DistributiveAllegory.zero_union _ }

/-- **§2.34 (reflexive)**: if `𝒜` is a DIVISION allegory then so is `Spl(Eq 𝒜)`, with right
    division taken pointwise (`splDiv`).  Both §2.31 laws reduce to the base `div_comp_le` /
    `le_div`, exactly as for the full `SplObj 𝒜` (`instDivisionSpl`). -/
noncomputable instance instDivisionSplEq {𝒜 : Type u} [DivisionAllegory 𝒜] :
    DivisionAllegory (SplEqObj 𝒜) :=
  { instDistributiveSplEq with
    div := fun Φ Ψ => splDiv Φ Ψ
    div_comp_le := fun {E F G} Φ Ψ => by
      rw [splEqLe_iff]
      show (E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ F.1.idem.e) ≫ Ψ.R ⊑ Φ.R
      calc (E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ F.1.idem.e) ≫ Ψ.R
          = E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ (F.1.idem.e ≫ Ψ.R) := by simp only [Cat.assoc]
        _ = E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ Ψ.R := by rw [Ψ.fixed_left]
        _ ⊑ E.1.idem.e ≫ Φ.R := comp_mono_left _ (DivisionAllegory.div_comp_le _ _)
        _ = Φ.R := Φ.fixed_left
    le_div := fun {E F G} T Φ Ψ h => by
      rw [splEqLe_iff] at h ⊢
      show T.R ⊑ E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ F.1.idem.e
      have hbase : T.R ⊑ Φ.R / Ψ.R := DivisionAllegory.le_div T.R Φ.R Ψ.R h
      calc T.R = E.1.idem.e ≫ T.R ≫ F.1.idem.e := T.fixed.symm
        _ ⊑ E.1.idem.e ≫ (Φ.R / Ψ.R) ≫ F.1.idem.e :=
            comp_mono_left _ (comp_mono_right hbase _) }

/-! ## §2.433  Assembling `PowerAllegory (SplEqObj 𝒜)`

  `SplEqObj 𝒜` is a FULL subcategory of `SplObj 𝒜` (homs are the identical `SplHom`s), so
  every allegory operation — `≫`/`°`/`∩`/`/ₛ`/`dom`/`Entire`/`codBox` — is the SAME underlying
  `splComp`/`splRecip`/`splInter`/`splDiv` on both.  We assemble the two hypotheses of
  `power_of_split_thick` (no tabularity): equivalence relations split with a map leg
  (`splEq_hsplit`), and every object is the target of a thick morphism (`splEq_hthick`). -/

section Assembly
variable {𝒜 : Type u}

/-- **Thick transfer** `Spl(𝒜) → Spl(Eq 𝒜)`.  `SplEqObj 𝒜` is a FULL subcategory of
    `SplObj 𝒜`, so `Thick` in `Spl(Eq)` quantifies over FEWER test morphisms (only those
    with reflexive source) than `Thick` in `Spl`.  Hence `SplObj`-thickness (stronger) implies
    `SplEqObj`-thickness (weaker): feed the `SplEqObj` test `R : Q ⟶ E` to the `SplObj`
    thickness at `Q.1`, and `codBox`/`/ₛ`/`Entire` transfer definitionally (same `splComp`/
    `splDiv`). -/
theorem thick_splObj_to_splEq [DivisionAllegory 𝒜] {P E : SplEqObj 𝒜} (S : P ⟶ E)
    (h : Thick (𝒜 := SplObj 𝒜) S) : Thick (𝒜 := SplEqObj 𝒜) S := by
  intro Q R hbox
  exact h Q.1 R hbox

/-- **§2.433 (equivalence relations split).**  Every equivalence relation `Φ : E ⟶ E` of
    `Spl(Eq 𝒜)` splits with a MAP leg.  `Φ` reflexive/symmetric/idempotent translates to the
    underlying `𝒜`-facts `E.1.idem.e ⊑ Φ.R`, `Φ.R° = Φ.R`, `Φ.R ≫ Φ.R = Φ.R`; the split object
    is `Φ.splitObj` (idempotent `Φ.R`), REFLEXIVE because `1 ⊑ E.1.idem.e ⊑ Φ.R`, so it lands
    in `Spl(Eq)`.  The three conclusions are the `SplObj`-splitting of `Φ` (`splitLeg` a map,
    `f ≫ f° = Φ`, `f° ≫ f = 1`), transferred to `Spl(Eq)` definitionally. -/
theorem splEq_hsplit [Allegory 𝒜] : EqSplits (SplEqObj 𝒜) := by
  intro E Φ hrefl hsym hidem
  -- Translate the `Spl(Eq)` hypotheses to the underlying `SplObj`/`𝒜` facts.
  have hrefl2 : E.1.idem.e ⊑ Φ.R := (splEqLe_iff (Cat.id E) Φ).mp hrefl
  have hs1 : Φ.R° ⊑ Φ.R := (splEqLe_iff (Φ°) Φ).mp hsym
  have hsym2 : Φ.R° = Φ.R := by
    refine le_antisymm hs1 ?_
    have := recip_mono hs1; rwa [Allegory.recip_recip] at this
  have hidem2 : Φ.R ≫ Φ.R = Φ.R := congrArg SplHom.R hidem
  -- The split object `(carrier, Φ.R)` is REFLEXIVE, hence an object of `Spl(Eq)`.
  let G₀ : SplObj 𝒜 := Φ.splitObj hsym2 hidem2
  have hGrefl : Cat.id G₀.carrier ⊑ G₀.idem.e := le_trans E.2 hrefl2
  -- The map leg `f = Φ.R`, with the three splitting facts read off `SplObj`.
  have hMap : Map (𝒜 := SplObj 𝒜) (Φ.splitLeg hsym2 hidem2) := by
    refine ⟨?_, ?_⟩
    · show dom (Φ.splitLeg hsym2 hidem2) = Cat.id E.1
      apply SplHom.ext
      show E.1.idem.e ∩ Φ.R ≫ Φ.R° = E.1.idem.e
      rw [hsym2, hidem2]
      exact le_antisymm (inter_lb_left _ _) (le_inter (le_refl _) hrefl2)
    · dsimp only [Simple]
      have he : (Φ.splitLeg hsym2 hidem2)° ≫ (Φ.splitLeg hsym2 hidem2) = Cat.id G₀ := by
        apply SplHom.ext; show Φ.R° ≫ Φ.R = Φ.R; rw [hsym2, hidem2]
      rw [he]; exact le_refl _
  refine ⟨⟨G₀, hGrefl⟩, Φ.splitLeg hsym2 hidem2, hMap, ?_, ?_⟩
  · exact (Φ.split_symmetric_idempotent hsym2 hidem2).1
  · exact (Φ.split_symmetric_idempotent hsym2 hidem2).2

/-- **§2.433 (thick targets).**  Every object `E` of `Spl(Eq 𝒜)` is the target of a THICK
    morphism.  A thick `T : x → E.1.carrier` of `𝒜` (from `PrePowerAllegory.thick_target`)
    yields the `SplObj`-thick `splEqTarget E.1 T : embObj x ⟶ E.1` (`splEqTarget_thick`, using
    `E`'s reflexivity `E.2` and the §2.41 box-naming `hbox E`); the embedded witness object
    `embObj x` (identity idempotent, hence reflexive) is an object of `Spl(Eq)`, and the
    thickness transfers to `Spl(Eq)` via `thick_splObj_to_splEq`. -/
theorem splEq_hthick [PrePowerAllegory 𝒜] (hbox : ∀ (E : SplEqObj 𝒜), SplEqBoxNaming E.1)
    (E : SplEqObj 𝒜) : ∃ (x : SplEqObj 𝒜) (S : x ⟶ E), Thick S := by
  obtain ⟨x, T, hThickT⟩ := PrePowerAllegory.thick_target E.1.carrier
  have hThickSpl : Thick (𝒜 := SplObj 𝒜) (splEqTarget E.1 T) :=
    splEqTarget_thick E.1 E.2 T hThickT (hbox E)
  exact ⟨⟨embObj x, le_refl _⟩, splEqTarget E.1 T,
    thick_splObj_to_splEq (P := ⟨embObj x, le_refl _⟩) (splEqTarget E.1 T) hThickSpl⟩

/-- **§2.433 (HEADLINE).**  `Spl(Eq 𝒜)`, the REFLEXIVE splitting completion of a pre-power
    allegory `𝒜`, is a POWER ALLEGORY.  Route (tabular-free, `power_of_split_thick`): equivalence
    relations split with a map leg (`splEq_hsplit`), and every object is the target of a thick
    morphism (`splEq_hthick`, given the §2.41 box-naming `hbox`).  Only `[PrePowerAllegory 𝒜]`
    is needed — no tabularity, no semi-simplicity (splitting equivalence relations in `Spl(Eq)`
    is structural, `[Allegory 𝒜]`-only), which also avoids the `DivisionAllegory 𝒜` instance
    diamond that carrying a second Division-extending class would reintroduce. -/
noncomputable def splEqPowerAllegory [PrePowerAllegory 𝒜]
    (hbox : ∀ (E : SplEqObj 𝒜), SplEqBoxNaming E.1) : PowerAllegory (SplEqObj 𝒜) :=
  power_of_split_thick splEq_hsplit (splEq_hthick hbox)

end Assembly

end Freyd.Alg
