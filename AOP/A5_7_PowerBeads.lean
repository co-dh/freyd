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
    LaxNatural (Relator.idRelator 𝒜) (powerRelator (𝒜 := 𝒜)) (fun a => ∋ a) :=
  fun R => powerRel_eps_lax R

end EpsLax

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

end SingletonLax

/-! ## The set model read pointwise, and the witness

  `powerRel` and `bigUnion` are defined by universal properties (`\`, `/`, `Λ`); over `Rel(Set)`
  the first unfolds to the Egli–Milner conjunction on the nose, and the second is pinned by
  being a map whose composite with `∋` is `∋∋`. -/

/-- `powerRel` in `Rel(Set)`, pointwise: `X (P R) Y` iff every element of `X` `R`-reaches into
    `Y` (term₁) and every element of `Y` is `R`-reachable from `X` (term₂). -/
public theorem powerRel_apply {a b : RelSet.{u}} (R : a ⟶ b)
    (X : (PowerAllegory.powerObj a).carrier) (Y : (PowerAllegory.powerObj b).carrier) :
    powerRel R X Y ↔ (∀ x, X x → ∃ y, R x y ∧ Y y) ∧ (∀ y, Y y → ∃ x, X x ∧ R x y) :=
  Iff.rfl

/-- `bigUnion` in `Rel(Set)`, pointwise: `⋃` relates the family `F` to exactly one set, the set
    of the elements of the members of `F`.  `⋃` is a map (`Λ_is_map'`) with `⋃ ≫ ∋ = ∋∋`
    (`Λ_eps_eq'`); simplicity pins the set, entireness produces it. -/
public theorem bigUnion_apply {a : RelSet.{u}}
    (F : (PowerAllegory.powerObj (PowerAllegory.powerObj a)).carrier)
    (U : (PowerAllegory.powerObj a).carrier) :
    bigUnion (a := a) F U ↔ ∀ x, (U x ↔ ∃ X, F X ∧ X x) := by
  have hmap : Map (bigUnion (a := a)) := by
    show Map (Λ (∋ (PowerAllegory.powerObj a) ≫ ∋ a)); exact Λ_is_map' _
  have heq : bigUnion (a := a) ≫ ∋ a = ∋ (PowerAllegory.powerObj a) ≫ ∋ a := Λ_eps_eq' _
  have fwd : ∀ V : (PowerAllegory.powerObj a).carrier, bigUnion (a := a) F V →
      ∀ x, (V x ↔ ∃ X, F X ∧ X x) := by
    intro V hFV x
    constructor
    · intro hVx
      have h1 : (bigUnion (a := a) ≫ ∋ a) F x := ⟨V, hFV, hVx⟩
      rw [heq] at h1
      exact h1
    · intro hx
      have h2 : (bigUnion (a := a) ≫ ∋ a) F x := by rw [heq]; exact hx
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
    ∃ (a : RelSet.{0}) (R : a ⟶ a), ¬ (∋ a ≫ R ⊑ powerRel R ≫ ∋ a) := by
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
        (fun a => (∋ a)°) := by
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
public theorem bigUnion_strict_relSet {a b : RelSet.{u}} (R : a ⟶ b) :
    powerRel (powerRel R) ≫ bigUnion = bigUnion ≫ powerRel R := by
  have hlax : powerRel (powerRel R) ≫ bigUnion (a := b) ⊑ bigUnion (a := a) ≫ powerRel R :=
    bigUnion_lax_natural R
  refine le_antisymm hlax (RelSet.le_iff.mpr fun F Y hFY => ?_)
  obtain ⟨U, hFU, hUY⟩ := hFY
  have hU := (bigUnion_apply F U).mp hFU
  have hEM := (powerRel_apply R U Y).mp hUY
  -- Each member `X` of `F` is `P R`-related to the part of `Y` it reaches.
  have hkey : ∀ X : (PowerAllegory.powerObj a).carrier, F X →
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
