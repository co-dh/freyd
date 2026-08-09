/-
  Freyd & Scedrov, *Categories, Allegories* §2.153 — the COMPOSE-CAUCUS lemma
  (the reusable heart of the concrete non-effectiveness), and the §2.153 witness.

  `Freyd/S2_153c_ConcreteNonEffective.lean` reduces the §2.153 headline
  `¬ CoversSplit (AsmEffReflection Krec)` to ONE construction:

      ∃ (A : Assembly Krec) (E : BinRel (Assembly Krec) A A),
        EquivalenceRelation E ∧ ¬ IsEffective E

  via `asm_not_effective_of_binRel`.  `Freyd/S2_153d_NonEffWitness.lean`
  supplies the forward level bridge (`level_forward`, `effective_xIdentifies`).

  ## Layer 1 (this file) — the compose-caucus characterization

  For ANY morphism `x : A → Q` of assemblies, the LEVEL relation `graph x ⊚ (graph x)°`
  has a caucus structure computed ENTIRELY from `A` (independent of `Q`): a point `y`
  of the level's source (a pair `(a,a') = (colA y, colB y)` with `x a = x a'`) lies in
  caucus `n` exactly when `A|_{ℓn}` contains `a` and `A|_{ϰn}` contains `a'`, i.e. when
  `n = code r_a r_a'` for `A`-caucus indices `r_a` of `a`, `r_{a'}` of `a'`.

  This is the point-level unfolding of `compose`/`imgAsm`/`products_equalizers_implies_pullbacks`
  (§1.56/§1.432/§2.153).  Two Sorry-free corollaries package it as the effectiveness bridge:
  `level_caucus_of_indices` (the level caucus over any point is inhabited by the cheap coded
  index `code r r'`) and `level_fill_realizer` (a modulus `σ` tracking a `RelHom (level x) E`
  produces, from that cheap index, an `E.src`-realizer of the glued point).

  ## Why Layers 2–4 (the concrete witness + `¬ IsEffective E`) are not closed HERE
     (they are CLOSED in `S2_153f` — see the correction at the end of this note)

  With `level_fill_realizer` the effectiveness bridge is exact, and it makes precise why the
  halting-encoding witness CANNOT be completed from Layer 1 alone (the wall the prior agents
  hit).  `IsEffective E` gives a cover `x` with `RelLe E (level x)` AND `RelLe (level x) E`;
  the two witnessing `RelHom`s are mutually inverse (joint monicity), so `E.src ≅ (level x).src`
  as ASSEMBLIES — and by Layer 1 the right side has the CHEAP caucus (`code r r'`).  So
  effectiveness is exactly: a `Krec`-tracked "fill" `τ` recovering an `E.src`-realizer of every
  point from its cheap index.

  To make `τ` DECIDE `Kc` one needs the level's caucus over each glued pair `(2e, 2e+1)`
  inhabited for EVERY `e` (so `τ` is total on a `Kc`-indexed family) WHILE the matching
  `E.src`-realizer carries a `Kc`-halting datum.  But:
  * inhabited-for-every-`e` forces `x(2e) = x(2e+1)` for every `e` (`effective_xIdentifies`,
    `S2_153d`), i.e. `E` glues `2e ~ 2e+1` for ALL `e`;
  * `E.src` a legitimate assembly forces (`carrier_mem`) the glued point over `(2e, 2e+1)` to
    lie in SOME caucus for every `e` — so its caucus CANNOT require a `Kc`-witness on the
    non-halting `e`; and any always-present caucus index that is a recursive function of the
    cheap `code r r'` lets `τ := that function` split the fill, making `E` EFFECTIVE.
  Thus a single equivalence relation whose only computational content is a halting encoding is
  either not a valid assembly (witness-caucus) or effective (fallback-caucus): the
  "`Tracks` constrains only inhabited caucus indices" barrier (documented in `S2_153c/d`) is
  intrinsic and Layer 1 does not break it.

  CORRECTION (`S2_153f`): the last step of the old analysis — "any always-present caucus
  index that is a recursive function of the cheap index splits the fill" — silently assumed
  the cheap index DETERMINES the pair.  Over `A = ∇ℕ` it does not (every index names every
  point), so an always-present caucus family can still defeat every fill: the parity witness
  (caucus at `m` = diagonal ∪ classes ≤ m) makes the single tracked index `φ(0)` claim the
  whole kernel, contradiction.  No halting encoding is needed; `¬ IsEffective` holds over
  `Krec` AND `allPartial` — Freyd's §2.153 uniformly in K, via THIS file's `level_caucus_iff`.

  MATHLIB-FREE.  Composition in DIAGRAM ORDER.
-/
module

public import Freyd.S2_153d_NonEffWitness

open Freyd Freyd.Alg

namespace Freyd.Alg

variable {K : ModulusSystem}

/-! ## Layer 1: the caucus of the level of `x`

  Unfold `graph x ⊚ (graph x)°`.  Its source is `imgAsm h` where
  `h = pair (π₁ ≫ 1_A) (π₂ ≫ 1_A) : PB → A×A` and `PB` is the §1.432 pullback of
  `x` against `x` (the kernel-pair assembly).  A caucus index `n` of a point `y`
  is a `pb`-caucus index of some pullback point mapping to `y.val`; those are exactly
  the `ℓ/ϰ`-coded caucus indices of the two components. -/

/-- **Compose-caucus lemma (Layer 1).**  For a point `y` of the level `graph x ⊚ (graph x)°`,
    membership in caucus `n` is exactly: `A|_{ℓn}` contains the first column `colA y` and
    `A|_{ϰn}` contains the second column `colB y`.  INDEPENDENT of the codomain `Q`. -/
public theorem level_caucus_iff {A Q : Assembly.{u} K} (x : A ⟶ Q) (n : Nat)
    (y : (graph x ⊚ (graph x)°).src.X) :
    (graph x ⊚ (graph x)°).src.caucus n y ↔
      A.caucus (K.proj₁ n) ((graph x ⊚ (graph x)°).colA.toFun y) ∧
      A.caucus (K.proj₂ n) ((graph x ⊚ (graph x)°).colB.toFun y) := by
  constructor
  · rintro ⟨w, ⟨hc1, hc2⟩, hwy⟩
    -- `hwy : (w.val.1, w.val.2) = y.val`, so the columns agree componentwise
    have h1 : w.val.1 = (graph x ⊚ (graph x)°).colA.toFun y := congrArg Prod.fst hwy
    have h2 : w.val.2 = (graph x ⊚ (graph x)°).colB.toFun y := congrArg Prod.snd hwy
    exact ⟨h1 ▸ hc1, h2 ▸ hc2⟩
  · rintro ⟨h1, h2⟩
    -- the image point `y` carries a pullback preimage `w` with `h.toFun w = y.val`
    refine ⟨y.property.choose, ⟨?_, ?_⟩, y.property.choose_spec⟩
    · have : y.property.choose.val.1 = (graph x ⊚ (graph x)°).colA.toFun y :=
        congrArg Prod.fst y.property.choose_spec
      exact this ▸ h1
    · have : y.property.choose.val.2 = (graph x ⊚ (graph x)°).colB.toFun y :=
        congrArg Prod.snd y.property.choose_spec
      exact this ▸ h2

/-- **Level caucus is CHEAP (Layer 1 corollary).**  Given any `A`-caucus index `r` of the
    first column `colA y` and `r'` of the second column `colB y`, the coded index
    `code r r'` is a caucus index of `y` in the level of `x`.  In particular the level's
    caucus over any point is always inhabited (feed `A.carrier_mem` on the two columns).
    This is the source-side realizer the fill must be recovered from. -/
theorem level_caucus_of_indices {A Q : Assembly.{u} K} (x : A ⟶ Q)
    (y : (graph x ⊚ (graph x)°).src.X) {r r' : Nat}
    (hr : A.caucus r ((graph x ⊚ (graph x)°).colA.toFun y))
    (hr' : A.caucus r' ((graph x ⊚ (graph x)°).colB.toFun y)) :
    (graph x ⊚ (graph x)°).src.caucus (K.code r r') y := by
  refine (level_caucus_iff x (K.code r r') y).mpr ?_
  rw [K.code_proj₁, K.code_proj₂]
  exact ⟨hr, hr'⟩

/-- **The fill realizer (Layer 1 → the effectiveness bridge).**  Suppose the level of `x`
    is contained in a relation `E` via a morphism `g` (`g ≫ E.colA = colA`,
    `g ≫ E.colB = colB`) — this is the reverse half `RelLe (level x) E` of `IsEffective E`.
    If `g` is tracked by a modulus `σ`, then from ANY pair of `A`-caucus indices `r, r'`
    of a point `y`'s two columns, `σ (code r r')` is DEFINED and is an `E.src`-caucus index
    of `g y` (a point of `E.src` over `(colA y, colB y)`).

    This is the exact obligation the §2.153 witness must contradict: `σ` is a total function
    on the always-inhabited cheap index `code r r'`, so if `E.src`'s caucus over the glued
    pair `(2e, 2e+1)` could only be witnessed by a `Kc`-halting datum, `σ (code r r')`
    would compute one for every `e`, deciding `Kc`. -/
theorem level_fill_realizer {A Q : Assembly.{u} K} (x : A ⟶ Q)
    {E : BinRel (Assembly.{u} K) A A}
    (g : (graph x ⊚ (graph x)°).src ⟶ E.src)
    {σ : ModFun} (hσ : Tracks σ (graph x ⊚ (graph x)°).src E.src g.toFun)
    (y : (graph x ⊚ (graph x)°).src.X) {r r' : Nat}
    (hr : A.caucus r ((graph x ⊚ (graph x)°).colA.toFun y))
    (hr' : A.caucus r' ((graph x ⊚ (graph x)°).colB.toFun y)) :
    ∃ m, σ.graph (K.code r r') m ∧ E.src.caucus m (g.toFun y) :=
  hσ (K.code r r') y (level_caucus_of_indices x y hr hr')

end Freyd.Alg
