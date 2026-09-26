/-
  Bird & de Moor §5.7, settled in the set model: which of the POWER-ALLEGORY beads are natural.

  `∋` is lax and no better; `∈ ≜ ∋°` is not even lax; the singleton `𝟙%∋` is lax (and no more:
  its strict square holds only for a map); `⋃` — lax abstractly (`bigUnion_lax_natural`,
  AOP.A5_4) — is STRICT over `Rel(Set)`.

  Both refutations run on one witness: `boolTip = {(true,true)} : Bool ⟶ Bool`, which has no
  image at `false`, together with the full set `{true,false} : [Bool]`.  Composition is diagram
  order (`≫`) throughout.
-/
module

public import AOP.A5_7
public import AOP.A8_2

universe u

namespace Freyd.Alg

/-! ## `∋` is lax natural, bundled -/

section EpsLax

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerAllegory 𝒜]

/-- **B&dM p.133**, bundled: `∋` is a lax natural transformation from the power relator to the
    identity relator.  The inequality is `powerRel_eps_lax` (`AOP.A5_4`) — term₂ of the
    Egli–Milner definition — read at `LaxNatural`'s definition; `AOP.A5_7`'s `eps_lax_natural`
    is the same fact before the power relator is bundled. -/
public theorem eps_laxNatural :
    LaxNatural (Relator.idRelator 𝒜) (powerRelator (𝒜 := 𝒜)) (fun A => ∋ A) :=
  fun R => powerRel_eps_lax R

/-- The identity relator preserves converse: its action on arrows is the identity. -/
public theorem idRelator_preservesRecip : (Relator.idRelator 𝒜).PreservesRecip :=
  fun _ => rfl

/-- **`∈ ≜ ∋°` is OP-lax**, the converse verdict `recip_oplax` turns `eps_laxNatural` into; lax it
    is not (`mem_not_laxNatural`), so op-lax is the strongest reading its bead may carry. -/
public theorem mem_oplaxNatural :
    OpLaxNatural (powerRelator (𝒜 := 𝒜)) (Relator.idRelator 𝒜) (fun A => (∋ A)°) :=
  recip_oplax idRelator_preservesRecip powerRelator_preservesRecip eps_laxNatural

/-- **`⊆ ≜ subset°` is OP-lax** along the power relator: `⊆ ≫ P(R) ⊑ P(R) ≫ ⊆`.  Both sides lie
    in term₁ `∈\(R∈)` of `P(R)`, and term₁ lies under the right side: for `xs term₁ zs` the set
    `ys = {z ∈ zs | ∃x∈xs. xRz}` has `xs P(R) ys ⊆ zs`; `ys` is `Λ W` over a tabulation `f°g` of
    term₁.  Lax it is not: an element of `zs` outside `R`'s image stops `P(R) ≫ ⊆`. -/
public theorem subset_recip_oplaxNatural :
    OpLaxNatural (powerRelator (𝒜 := 𝒜)) powerRelator (fun A => (subset (a := A))°) := by
  intro A B R
  show (subset (a := A))° ≫ powerRel R ⊑ powerRel R ≫ (subset (a := B))°
  have hT : (∋ A)° ≫ ((∋ A)° \ (R ≫ (∋ B)°)) ⊑ R ≫ (∋ B)° := leftDiv_comp_le _ _
  refine le_trans (?_ : _ ⊑ (∋ A)° \ (R ≫ (∋ B)°)) ?_
  · apply (le_leftDiv_iff _ _ _).mpr
    have hs : (∋ A)° ≫ (subset (a := A))° ⊑ (∋ A)° := by
      rw [← Allegory.recip_comp]; exact recip_mono (DivisionAllegory.div_comp_le _ _)
    rw [← Cat.assoc]
    exact le_trans (comp_mono_right hs _) (le_trans (comp_mono_left _ (inter_lb_left _ _)) hT)
  obtain ⟨C, f, g, hf, hg, hfg, -⟩ := TabularAllegory.tabular ((∋ A)° \ (R ≫ (∋ B)°))
  rw [hfg] at hT ⊢
  have hW : Λ ((g ≫ ∋ B) ∩ (f ≫ ∋ A ≫ R)) ≫ ∋ B = (g ≫ ∋ B) ∩ (f ≫ ∋ A ≫ R) := Λ_eps_eq' _
  have hh : Map (Λ ((g ≫ ∋ B) ∩ (f ≫ ∋ A ≫ R))) := Λ_is_map' _
  generalize Λ ((g ≫ ∋ B) ∩ (f ≫ ∋ A ≫ R)) = h at hW hh
  -- `g ⊑ h ≫ ⊆`: every output member of the pair survives into `ys = h`.
  have ha : g ⊑ h ≫ (subset (a := B))° := by
    have hs : h° ≫ g ⊑ (subset (a := B))° := by
      have hd : g° ≫ h ⊑ subset (a := B) := by
        apply (le_div_iff _ _ _).mpr
        rw [Cat.assoc, hW]
        refine le_trans (comp_mono_left _ (inter_lb_left _ _)) ?_
        rw [← Cat.assoc]
        exact le_trans (comp_mono_right hg.2 _) (le_of_eq (Cat.id_comp _))
      have := recip_mono hd
      rwa [Allegory.recip_comp, Allegory.recip_recip] at this
    calc g = 𝟙 C ≫ g := (Cat.id_comp _).symm
      _ ⊑ (h ≫ h°) ≫ g := comp_mono_right (map_entire_le hh) _
      _ = h ≫ h° ≫ g := Cat.assoc _ _ _
      _ ⊑ h ≫ (subset (a := B))° := comp_mono_left _ hs
  -- `f° ≫ h ⊑ P(R)`: term₂ because `ys ⊆ R(xs)`, term₁ by the modular law.
  have hb2 : f° ≫ h ⊑ (∋ A ≫ R) / ∋ B := by
    apply (le_div_iff _ _ _).mpr
    rw [Cat.assoc, hW]
    refine le_trans (comp_mono_left _ (inter_lb_right _ _)) ?_
    rw [← Cat.assoc]
    exact le_trans (comp_mono_right hf.2 _) (le_of_eq (Cat.id_comp _))
  have hb1 : f° ≫ h ⊑ (∋ A)° \ (R ≫ (∋ B)°) := by
    apply (le_leftDiv_iff _ _ _).mpr
    have h1 : (∋ A)° ≫ f° ⊑ R ≫ (∋ B)° ≫ g° := by
      calc (∋ A)° ≫ f° = ((∋ A)° ≫ f°) ≫ 𝟙 C := (Cat.comp_id _).symm
        _ ⊑ ((∋ A)° ≫ f°) ≫ g ≫ g° := comp_mono_left _ (map_entire_le hg)
        _ = ((∋ A)° ≫ f° ≫ g) ≫ g° := by simp only [Cat.assoc]
        _ ⊑ (R ≫ (∋ B)°) ≫ g° := comp_mono_right hT _
        _ = R ≫ (∋ B)° ≫ g° := Cat.assoc _ _ _
    have h2 : (∋ A)° ≫ f° ⊑ R ≫ (∋ B)° ≫ h° := by
      have hm := modular_le_left R ((∋ B)° ≫ g°) ((∋ A)° ≫ f°)
      have hWr : ((∋ B)° ≫ g°) ∩ R° ≫ (∋ A)° ≫ f° = (∋ B)° ≫ h° := by
        rw [← Allegory.recip_comp h, hW]
        simp only [Allegory.recip_inter, Allegory.recip_comp, Cat.assoc]
      rw [hWr] at hm
      exact le_trans (le_inter h1 (le_refl _)) hm
    calc (∋ A)° ≫ f° ≫ h = ((∋ A)° ≫ f°) ≫ h := (Cat.assoc _ _ _).symm
      _ ⊑ (R ≫ (∋ B)° ≫ h°) ≫ h := comp_mono_right h2 _
      _ = (R ≫ (∋ B)°) ≫ h° ≫ h := by simp only [Cat.assoc]
      _ ⊑ (R ≫ (∋ B)°) ≫ 𝟙 _ := comp_mono_left _ hh.2
      _ = R ≫ (∋ B)° := Cat.comp_id _
  calc f° ≫ g ⊑ f° ≫ h ≫ (subset (a := B))° := comp_mono_left _ ha
    _ = (f° ≫ h) ≫ (subset (a := B))° := (Cat.assoc _ _ _).symm
    _ ⊑ powerRel R ≫ (subset (a := B))° := comp_mono_right (le_inter hb1 hb2) _

end EpsLax

/-! ## `cp` is lax natural -/

section CpLax

-- `cpMap` lives over `TabularUnitaryUnguardedDivisionPowerAllegory` and `powerRelator` over
-- `TabularUnitaryUnguardedPowerAllegory`; only the class BELOW both carries one `Allegory` path
-- for the two, and it is the one §7.4's cylinder is stated over.
variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜]

/-- **B&dM p.126, `cp ≜ Λ(F(∋))` is LAX natural** `F∘P ⟶ P∘F`: distributing `F` over a tuple of
    sets and then taking one element out of each beats taking the elements out first and then
    collecting the results, because the collected sets need not be a `F`-shape of sets.

    STRICT it is not: at `F = Δ` (`A ↦ A×A`) `cp` is the cross product `(X,Y) ↦ X×Y`, and over
    the full relation on a two-element set the Egli–Milner right-hand side admits the diagonal
    `{(1,1),(2,2)}`, which is no rectangle `X'×Y'`, so nothing on the left reaches it.

    Theorem 5.2 (`laxNatural_iff_strict_on_maps`) carries it: on a map `f` the power relator IS
    the existential image (`powerRel_map`), and there the square is the transpose's own
    absorption/fusion pair. -/
public theorem cpMap_laxNatural (F : Relator 𝒜 𝒜) :
    LaxNatural (Relator.comp F powerRelator) (Relator.comp powerRelator F)
      (fun A => cpMap F A) :=
  (laxNatural_iff_strict_on_maps (Relator.comp F powerRelator) (Relator.comp powerRelator F)
      (fun A => cpMap F A)).mpr fun f hf => by
    show F.map (powerRel f) ≫ cpMap F _ = cpMap F _ ≫ powerRel (F.map f)
    rw [powerRel_map hf, powerRel_map (F.map_is_map hf)]
    show F.map (existsImage f) ≫ Λ (F.map (∋ _)) = Λ (F.map (∋ _)) ≫ existsImage (F.map f)
    have hE : Map (F.map (existsImage f)) := F.map_is_map (Λ_is_map' _)
    rw [← Λ_fusion hE, Λ_absorption, ← F.map_comp, ← F.map_comp, existsImage_eps]

end CpLax

/-! ## The singleton's two spellings -/

section SingletonSpelling

variable {𝒜 : Type u} [UnguardedPowerAllegory 𝒜]

/-- `𝟙%∋` IS `singletonMap`.  §2.415 defines the singleton as `Λ 𝟙`, and that is the spelling a
    picture is drawn in — `Λ W = 𝟙%∋ E(W)` splits the transpose and leaves `Λ 𝟙` standing — while
    every theorem about it is written with the name.  The bridge is what makes the two ONE
    statement to `diag-export`'s naturality search, which filters candidates by the constants the
    bead is built from and so never reached `singletonMap_natural` from a panel drawn as `Λ 𝟙`. -/
@[diag_bridge] public theorem Λ_id_eq_singletonMap (a : 𝒜) : Λ (𝟙 a) = singletonMap := rfl

end SingletonSpelling

/-! ## `𝟙%∋` is lax natural, bundled -/

section SingletonLax

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜]

/-- **B&dM p.106**, bundled: the singleton `𝟙%∋` IS a lax natural transformation from the
    identity relator to the power relator — `R ≫ 𝟙%∋ ⊑ 𝟙%∋ ≫ P R` for EVERY relation `R`, not
    only for a map.  The inequality is `singletonMap_powerRel_lax` (`AOP.A8_1`), read at
    `LaxNatural`'s definition.

    What fails off the maps is the STRICT square `f ≫ 𝟙%∋ = 𝟙%∋ ≫ E f` of `singletonMap_natural`
    (`AOP.A4_6`), whose right-hand side is the map `Λ R` onto the WHOLE `R`-image of a point; the
    power relator is the Egli–Milner relation instead, which relates `{x}` to every non-empty
    subset of that image, and each singleton `{y}` the left-hand side produces is one of them. -/
public theorem singleton_laxNatural :
    LaxNatural (powerRelator (𝒜 := 𝒜)) (Relator.idRelator 𝒜) (fun _ => singletonMap) :=
  fun R => singletonMap_powerRel_lax R

/-- `F(∋,∋)` IS LAX NATURAL in the first argument, for EVERY binary relator and every second
    argument: `F.map_comp` collapses the two composites to `F` of one relation, and what is left
    is `E(R)∋⊑∋R` under `F`.  The exporter needs a verdict for the family it cannot split, and
    `laxNatural_outside` only covers the one-argument steps `F(∋,𝟙)`, `F(𝟙,∋)`. -/
public theorem laxNatural_birel_eps_eps (F : BiRelator 𝒜) (B : 𝒜) :
    LaxNatural (Relator.comp (Relator.idRelator 𝒜) (F.appr B))
      (Relator.comp (Relator.comp (Relator.idRelator 𝒜) powerRelator)
        (F.appr (PowerAllegory.powerObj B)))
      (fun a => F.map (∋ a) (∋ B)) := by
  intro a b R
  show F.map (powerRel R) (𝟙 (PowerAllegory.powerObj B)) ≫ F.map (∋ b) (∋ B)
      ⊑ F.map (∋ a) (∋ B) ≫ F.map R (𝟙 B)
  rw [← F.map_comp, ← F.map_comp, Cat.id_comp, Cat.comp_id]
  exact F.map_mono (powerRel_eps_lax R) (le_refl _)

/-- `F(𝟙,H)` IS STRICTLY NATURAL in the first argument, for every binary relator and every `H`:
    both squares are `F(R,H)` by interchange.  The verdict Proposition 9.4's bead `G(𝟙,H)` needs. -/
public theorem strictNatural_birel_id {𝒜 : Type u} [Allegory 𝒜] (F : BiRelator 𝒜) {w A : 𝒜}
    (H : w ⟶ A) :
    StrictNatural (Relator.comp (Relator.idRelator 𝒜) (F.appr A))
      (Relator.comp (Relator.idRelator 𝒜) (F.appr w)) (fun a => F.map (𝟙 a) H) := by
  intro a b R
  show F.map R (𝟙 w) ≫ F.map (𝟙 b) H = F.map (𝟙 a) H ≫ F.map R (𝟙 A)
  rw [F.interchange, F.interchange']

end SingletonLax

/-! ## The set model read pointwise, and the witness

  `powerRel` and `bigUnion` are defined by universal properties (`\`, `/`, `Λ`); over `Rel(Set)`
  the first unfolds to the Egli–Milner conjunction on the nose, and the second is pinned by
  being a map whose composite with `∋` is `∋∋`. -/

/-- `powerRel` in `Rel(Set)`, pointwise: `X (P R) Y` iff every element of `X` `R`-reaches into
    `Y` (term₁) and every element of `Y` is `R`-reachable from `X` (term₂). -/
public theorem powerRel_apply {A B : RelSet.{u}} (R : A ⟶ B)
    (X : (PowerAllegory.powerObj A).carrier) (Y : (PowerAllegory.powerObj B).carrier) :
    powerRel R X Y ↔ (∀ x, X x → ∃ y, R x y ∧ Y y) ∧ (∀ y, Y y → ∃ x, X x ∧ R x y) :=
  Iff.rfl

/-- `bigUnion` in `Rel(Set)`, pointwise: `⋃` relates the family `F` to exactly one set, the set
    of the elements of the members of `F`.  `⋃` is a map (`Λ_is_map'`) with `⋃ ≫ ∋ = ∋∋`
    (`Λ_eps_eq'`); simplicity pins the set, entireness produces it. -/
public theorem bigUnion_apply {A : RelSet.{u}}
    (F : (PowerAllegory.powerObj (PowerAllegory.powerObj A)).carrier)
    (U : (PowerAllegory.powerObj A).carrier) :
    bigUnion (a := A) F U ↔ ∀ x, (U x ↔ ∃ X, F X ∧ X x) := by
  have hmap : Map (bigUnion (a := A)) := by
    show Map (Λ (∋ (PowerAllegory.powerObj A) ≫ ∋ A)); exact Λ_is_map' _
  have heq : bigUnion (a := A) ≫ ∋ A = ∋ (PowerAllegory.powerObj A) ≫ ∋ A := Λ_eps_eq' _
  have fwd : ∀ V : (PowerAllegory.powerObj A).carrier, bigUnion (a := A) F V →
      ∀ x, (V x ↔ ∃ X, F X ∧ X x) := by
    intro V hFV x
    constructor
    · intro hVx
      have h1 : (bigUnion (a := A) ≫ ∋ A) F x := ⟨V, hFV, hVx⟩
      rw [heq] at h1
      exact h1
    · intro hx
      have h2 : (bigUnion (a := A) ≫ ∋ A) F x := by rw [heq]; exact hx
      obtain ⟨V', hFV', hV'x⟩ := h2
      exact RelSet.simple_uniq hmap.2 hFV' hFV ▸ hV'x
  refine ⟨fwd U, fun hdesc => ?_⟩
  obtain ⟨U', hFU'⟩ := RelSet.entire_total hmap.1 F
  exact funext (fun x => propext ((fwd U' hFU' x).trans (hdesc x).symm)) ▸ hFU'

/-- `R = {(true,true)} : Bool ⟶ Bool`.  `false` has no `R`-image at all, and that single gap is
    what both refutations exploit: `powerRel R` is empty at every set containing `false`
    (term₁ has nowhere to send it) and at every target set containing `false` (term₂ has
    nowhere to fetch it from). -/
@[expose] public def boolTip : (⟨Bool⟩ : RelSet.{0}) ⟶ ⟨Bool⟩ := fun x y => x = true ∧ y = true

/-! ## `∋` is lax and no more -/

/-- `∋` is NOT strictly natural: `∋ ≫ R ⊑ P R ≫ ∋` fails.  At the full set `{true,false}` the
    left side reaches `true` — the member `true` `R`-reaches `true` — while `powerRel R` is
    empty at `{true,false}`, because term₁ demands that EVERY member `R`-reach into the output
    and the member `false` reaches nothing. -/
public theorem eps_not_strict :
    ∃ (A : RelSet.{0}) (R : A ⟶ A), ¬ (∋ A ≫ R ⊑ powerRel R ≫ ∋ A) := by
  refine ⟨⟨Bool⟩, boolTip, fun h => ?_⟩
  obtain ⟨T, hT, -⟩ := RelSet.le_iff.mp h (fun _ => True) true ⟨true, trivial, rfl, rfl⟩
  obtain ⟨y, hy, -⟩ :=
    RelSet.le_iff.mp (powerRel_term1_cancel boolTip) false T ⟨fun _ => True, trivial, hT⟩
  exact Bool.noConfusion hy.1

/-! ## `∈` is not lax at all -/

/-- `∈ ≜ ∋°` is NOT lax natural from the identity relator to the power relator: `R ≫ ∈ ⊑ ∈ ≫ P R`
    fails.  The left side relates `true` to `{true,false}` (`true R true` and `true ∈ {true,false}`),
    but the right side needs a `T` with `T (P R) {true,false}`, and term₂ demands that every
    element of `{true,false}` be `R`-reachable from `T` — nothing `R`-reaches `false`.

    `recip_oplax` (`AOP.A5_7`) does not rescue `∈`: it turns a lax `φ` into an OPLAX `φ°` only
    when BOTH relators preserve `°` (`Relator.PreservesRecip`), and the power relator does not.

    `∈` has no declaration of its own — the note's convention reads it as `∋` backwards. -/
public theorem mem_not_laxNatural :
    ¬ LaxNatural (powerRelator (𝒜 := RelSet.{0})) (Relator.idRelator RelSet.{0})
        (fun A => (∋ A)°) := by
  intro h
  have hsq : boolTip ≫ (∋ (⟨Bool⟩ : RelSet.{0}))°
      ⊑ (∋ (⟨Bool⟩ : RelSet.{0}))° ≫ powerRel boolTip := h boolTip
  obtain ⟨T, -, hTS⟩ :=
    RelSet.le_iff.mp hsq true (fun _ => True) ⟨true, ⟨rfl, rfl⟩, trivial⟩
  obtain ⟨x, -, hx⟩ :=
    RelSet.le_iff.mp (powerRel_eps_lax boolTip) T false ⟨fun _ => True, hTS, trivial⟩
  exact Bool.noConfusion hx.2

/-! ## `⋃` is lax abstractly and STRICT over `Rel(Set)` -/

/-- `⋃` is not merely lax over the set model: `P(P R) ≫ ⋃ = ⋃ ≫ P R`.  The lax half is
    `bigUnion_lax_natural` (`AOP.A5_4`).  For the other half, given `⋃F = U` and `U (P R) Y`,
    the family `G = {Yₓ | X ∈ F}` with `Y_X = {y ∈ Y | y is R-reachable from X}` satisfies
    `F (P(P R)) G` — term₁ because each `X ⊆ U` inherits `U`'s reaching, term₂ by construction —
    and `⋃G = Y` because term₂ of `U (P R) Y` says every `y ∈ Y` comes from some `x ∈ U`, hence
    from some member of `F`.

    The abstract statement stays lax: `powerRel_est_lt_bigUnion` (`AOP.A6_1_OrdRelSet`) is the
    neighbouring square that genuinely fails. -/
public theorem bigUnion_strict_relSet {A B : RelSet.{u}} (R : A ⟶ B) :
    powerRel (powerRel R) ≫ bigUnion = bigUnion ≫ powerRel R := by
  have hlax : powerRel (powerRel R) ≫ bigUnion (a := B) ⊑ bigUnion (a := A) ≫ powerRel R :=
    bigUnion_lax_natural R
  refine le_antisymm hlax (RelSet.le_iff.mpr fun F Y hFY => ?_)
  obtain ⟨U, hFU, hUY⟩ := hFY
  have hU := (bigUnion_apply F U).mp hFU
  have hEM := (powerRel_apply R U Y).mp hUY
  -- Each member `X` of `F` is `P R`-related to the part of `Y` it reaches.
  have hkey : ∀ X : (PowerAllegory.powerObj A).carrier, F X →
      powerRel R X (fun y => Y y ∧ ∃ x, X x ∧ R x y) := by
    intro X hFX
    refine (powerRel_apply R X _).mpr ⟨fun x hXx => ?_, ?_⟩
    · obtain ⟨y, hRxy, hYy⟩ := hEM.1 x ((hU x).mpr ⟨X, hFX, hXx⟩)
      exact ⟨y, hRxy, hYy, x, hXx, hRxy⟩
    · rintro y ⟨-, x, hXx, hRxy⟩
      exact ⟨x, hXx, hRxy⟩
  refine ⟨fun Z => ∃ X, F X ∧ Z = (fun y => Y y ∧ ∃ x, X x ∧ R x y), ?_, ?_⟩
  · refine (powerRel_apply (powerRel R) F _).mpr ⟨fun X hFX => ⟨_, hkey X hFX, X, hFX, rfl⟩, ?_⟩
    rintro Z ⟨X, hFX, rfl⟩
    exact ⟨X, hFX, hkey X hFX⟩
  · refine (bigUnion_apply _ Y).mpr fun y => ⟨fun hYy => ?_, ?_⟩
    · obtain ⟨x, hUx, hRxy⟩ := hEM.2 y hYy
      obtain ⟨X, hFX, hXx⟩ := (hU x).mp hUx
      exact ⟨_, ⟨X, hFX, rfl⟩, hYy, x, hXx, hRxy⟩
    · rintro ⟨Z, ⟨X, hFX, rfl⟩, hZy⟩
      exact hZy.1

end Freyd.Alg
