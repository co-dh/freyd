/-
  Freyd & Scedrov, *Categories, Allegories* §2.153 — "The category of assemblies is
  not effective."  CLOSED OUTRIGHT: the PARITY WITNESS.

  ## The witness

  * Assembly `A = ∇ℕ` (`nablaNat`): carrier ℕ, every caucus full.
  * Equivalence relation `E = parityRel`: it glues each pair `2k ~ 2k+1` (the parity
    classes `{2k, 2k+1}`).  Its table `paritySrc` has carrier
    `{(x,y) : x/2 = y/2}` and caucus at `m` = the diagonal together with the pairs of
    class `≤ m`:  `E|ₘ = {(x,y) : x = y ∨ x/2 ≤ m}`.

  ## The obstruction: UNIFORMITY OF NAMING (no recursion theory!)

  Freyd's §2.153 claim carries no side condition: it is stated for EVERY modulus
  system `K` satisfying (i) identity, (ii) composition, (iii) pairing.  The
  obstruction is NOT the halting problem (representative choice); it is that a
  splitting forces a SINGLE caucus index of the relation to contain the ENTIRE
  kernel:

  Suppose `E` were the level `q ⊚ q°` of a morphism `q : ∇ℕ → D` (in the containment
  order — `SplitsAsMap` gives exactly this via §2.148-dual fullness, and the second
  splitting equation `q° ≫ q = 1` is never needed).  Over `∇ℕ` the level's caucuses
  are FULL — every index names every point (`level_caucus_iff`, §2.153e), because the
  level's realizers come from `A×A`, never from `D`.  So a tracked containment
  `level ⊑ E` (modulus `φ`) must send the single index `0` to a single caucus index
  `m₀ = φ(0)` of `E` containing EVERY glued pair.  But `E|ₘ₀` omits the pair
  `(2(m₀+1), 2(m₀+1)+1)` of class `m₀+1`.  Contradiction — with NO hypothesis on `D`
  or its caucuses, and no computability argument.

  Consequently non-effectiveness holds over `Krec` (the book's "K may be the
  collection of all partial recursive functions") AND over `ModulusSystem.allPartial`
  — refuting the previously recorded expectation that the reflection over
  `allPartial` is AC.  The only extra ingredient beyond the `ModulusSystem` fields is
  a total member of K dominating both projections (`ProjBounded`, e.g.
  `n ↦ max (nℓ) (nϰ)`), used ONLY for `E`'s transitivity modulus.

  ## What this file proves (Sorry-free)

  * `parityRel_equivalence` — `E` is a §1.567 equivalence relation (BinRel level);
    reflexivity/symmetry are tracked by the identity modulus, transitivity by the
    dominating bound.
  * `parityRel_not_level` / `parityRel_not_effective` — the core: `E` is not the
    level of ANY morphism out of `∇ℕ` (a fortiori of any cover): `¬ IsEffective E`.
  * `asm_not_effective_of_projBounded` — the §2.153 headline hypothesis, generic in
    `K`: an equivalence relation `I` of `Rel(Assembly K)` with NO map-splitting
    (`∀ d f, ¬ SplitsAsMap f I`).
  * `asm_not_effective` / `asm_not_effective_allPartial` — at `Krec` / `allPartial`.
  * `asmReflection_not_ac` / `asmReflection_not_ac_allPartial` — **§2.153/§2.16(13)**:
    `¬ CoversSplit (AsmEffReflection K)` for `K = Krec` and `K = allPartial`, by
    feeding the witness to `asmReflection_not_ac_of_notEffective` (§2.153).

  Conventions: diagram-order composition `R ≫ S`, reciprocation `R°`, containment
  `⊂` (BinRel) / `⊑` (allegory).  Mathlib-free.
-/
module

public import Freyd.S2_153e_ComposeCaucus

universe u

namespace Freyd.Alg

open Rcat

variable {K : ModulusSystem}

/-! ## The dominating-bound hypothesis

  The single closure fact beyond the `ModulusSystem` fields that the witness uses:
  a TOTAL member of K dominating both projections.  It tracks the transitivity
  `E ⊚ E ⊂ E` (a composite index `n` certifies the two halves at `nℓ` and `nϰ`; the
  glued class is bounded by one of them, hence by the dominator).  Any reasonable K
  has one (`max (nℓ) (nϰ)` is recursive in the projections); an abstract
  `ModulusSystem` need not, so it is a hypothesis, discharged below for `Krec` and
  `allPartial`. -/

/-- K has a total member dominating both projections ℓ and ϰ. -/
def ProjBounded (K : ModulusSystem) : Prop :=
  ∃ g : Nat → Nat, K.mem (ModFun.ofFun g) ∧ ∀ n, K.proj₁ n ≤ g n ∧ K.proj₂ n ≤ g n

/-- `Krec` is projection-bounded: `n ↦ cfst n + (csnd n - cfst n)` (= `max`) is total
    recursive. -/
theorem krec_projBounded : ProjBounded Krec := by
  refine ⟨fun n => cfst n + (csnd n - cfst n), partRec_ofFun ?_, fun n => ?_⟩
  · exact Recursive1.comp2 Recursive2.add Recursive1.cfst
      (Recursive1.comp2 Recursive2.sub Recursive1.csnd Recursive1.cfst)
  · show cfst n ≤ cfst n + (csnd n - cfst n) ∧ csnd n ≤ cfst n + (csnd n - cfst n)
    omega

/-- `allPartial` is projection-bounded (its `mem` is `True`). -/
theorem allPartial_projBounded : ProjBounded ModulusSystem.allPartial := by
  refine ⟨fun n => ModulusSystem.allPartial.proj₁ n +
    (ModulusSystem.allPartial.proj₂ n - ModulusSystem.allPartial.proj₁ n),
    trivial, fun n => ?_⟩
  show ModulusSystem.allPartial.proj₁ n ≤ ModulusSystem.allPartial.proj₁ n +
      (ModulusSystem.allPartial.proj₂ n - ModulusSystem.allPartial.proj₁ n)
    ∧ ModulusSystem.allPartial.proj₂ n ≤ ModulusSystem.allPartial.proj₁ n +
      (ModulusSystem.allPartial.proj₂ n - ModulusSystem.allPartial.proj₁ n)
  omega

/-! ## The witness: `A = ∇ℕ`, `E` = the parity-pair relation -/

/-- The assembly `∇ℕ`: carrier ℕ (`ULift`ed for universe polymorphism), every caucus
    full.  Over `∇ℕ` an index carries NO information about the element it names —
    the uniformity that powers the non-splitting argument. -/
abbrev nablaNat : Assembly.{u} K := nablaAsm (ULift.{u} Nat)

/-- The TABLE of the parity relation: carrier = the same-class pairs
    `{(x,y) : x/2 = y/2}` (classes `{2k, 2k+1}`); the caucus at `m` is the diagonal
    together with the pairs of class `≤ m`.  The diagonal disjunct is what lets the
    identity modulus track reflexivity off `∇ℕ`'s full caucuses; the class bound is
    what no single index can exhaust. -/
def paritySrc : Assembly.{u} K where
  X := {p : ULift.{u} Nat × ULift.{u} Nat // p.1.down / 2 = p.2.down / 2}
  caucus m p := p.val.1.down = p.val.2.down ∨ p.val.1.down / 2 ≤ m
  carrier_mem p := ⟨p.val.1.down / 2, Or.inr (Nat.le_refl _)⟩

/-- First column of the parity relation (tracked by the identity modulus — the
    codomain `∇ℕ` has full caucuses). -/
def parityColA : paritySrc (K := K) ⟶ nablaNat :=
  ⟨fun p => p.val.1, ModFun.ident, K.id_mem, fun n _ _ => ⟨n, rfl, trivial⟩⟩

/-- Second column of the parity relation. -/
def parityColB : paritySrc (K := K) ⟶ nablaNat :=
  ⟨fun p => p.val.2, ModFun.ident, K.id_mem, fun n _ _ => ⟨n, rfl, trivial⟩⟩

/-- **The §2.153 witness relation** `E : ∇ℕ → ∇ℕ` in `Rel(Assembly K)`: the parity
    equivalence relation `x ~ y ⟺ x/2 = y/2`, with class-bounded caucuses. -/
def parityRel : BinRel (Assembly.{u} K) nablaNat nablaNat where
  src := paritySrc
  colA := parityColA
  colB := parityColB
  isMonicPair := fun {_W} _ _ hA hB => AsmHom.ext (funext fun w => Subtype.ext (Prod.ext
    (congrArg (fun m => AsmHom.toFun m w) hA)
    (congrArg (fun m => AsmHom.toFun m w) hB)))

/-! ### `E` is an equivalence relation (BinRel level, §1.567) -/

/-- Reflexivity witness `∇ℕ → E`: the diagonal, tracked by the identity modulus
    (diagonal pairs lie in EVERY caucus of `paritySrc`). -/
def parityDiag : nablaNat (K := K) ⟶ paritySrc :=
  ⟨fun x => ⟨(x, x), rfl⟩, ModFun.ident, K.id_mem, fun n _ _ => ⟨n, rfl, Or.inl rfl⟩⟩

/-- Symmetry witness `E → E°`: the swap, tracked by the identity modulus — the caucus
    bound `x/2 ≤ m` is symmetric on the carrier since `x/2 = y/2` there. -/
def paritySwap : paritySrc (K := K) ⟶ paritySrc :=
  ⟨fun p => ⟨(p.val.2, p.val.1), p.property.symm⟩, ModFun.ident, K.id_mem,
    fun n p hp => ⟨n, rfl, by
      show p.val.2.down = p.val.1.down ∨ p.val.2.down / 2 ≤ n
      rcases hp with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by have := p.property; omega)⟩⟩

/-- Carrier containment for transitivity: a point of `E ⊚ E` is a same-class pair
    (the matched middle chains the two class equalities). -/
theorem parityCompose_carrier (y : (parityRel (K := K) ⊚ parityRel).src.X) :
    y.val.1.down / 2 = y.val.2.down / 2 := by
  obtain ⟨x, hx⟩ := y.property
  have d1 : x.val.1.val.1.down = y.val.1.down := congrArg (fun p => (Prod.fst p).down) hx
  have d2 : x.val.2.val.2.down = y.val.2.down := congrArg (fun p => (Prod.snd p).down) hx
  have dmid : x.val.1.val.2.down = x.val.2.val.1.down := congrArg ULift.down x.property
  have hp1 : x.val.1.val.1.down / 2 = x.val.1.val.2.down / 2 := x.val.1.property
  have hp2 : x.val.2.val.1.down / 2 = x.val.2.val.2.down / 2 := x.val.2.property
  omega

/-- Transitivity witness `(E ⊚ E).src → E.src`, tracked by the dominating bound `g`:
    a composite index `n` certifies the two halves at `nℓ` and `nϰ`; in every case the
    glued pair is diagonal or its class is `≤ nℓ` or `≤ nϰ`, hence `≤ g n`. -/
def parityTransHom (g : Nat → Nat) (hg : K.mem (ModFun.ofFun g))
    (hg₁ : ∀ n, K.proj₁ n ≤ g n) (hg₂ : ∀ n, K.proj₂ n ≤ g n) :
    (parityRel (K := K) ⊚ parityRel).src ⟶ paritySrc :=
  ⟨fun y => ⟨y.val, parityCompose_carrier y⟩, ModFun.ofFun g, hg, fun n y hy => by
    refine ⟨g n, rfl, ?_⟩
    obtain ⟨x, ⟨hc1, hc2⟩, hxy⟩ := hy
    have d1 : x.val.1.val.1.down = y.val.1.down := congrArg (fun p => (Prod.fst p).down) hxy
    have d2 : x.val.2.val.2.down = y.val.2.down := congrArg (fun p => (Prod.snd p).down) hxy
    have dmid : x.val.1.val.2.down = x.val.2.val.1.down := congrArg ULift.down x.property
    have hp1 : x.val.1.val.1.down / 2 = x.val.1.val.2.down / 2 := x.val.1.property
    have e1 : x.val.1.val.1.down = x.val.1.val.2.down
        ∨ x.val.1.val.1.down / 2 ≤ K.proj₁ n := hc1
    have e2 : x.val.2.val.1.down = x.val.2.val.2.down
        ∨ x.val.2.val.1.down / 2 ≤ K.proj₂ n := hc2
    have hb1 := hg₁ n
    have hb2 := hg₂ n
    show y.val.1.down = y.val.2.down ∨ y.val.1.down / 2 ≤ g n
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)⟩

/-- **`E` is an equivalence relation** (§1.567 BinRel form): reflexive, symmetric,
    transitive.  Only transitivity needs the dominating bound. -/
theorem parityRel_equivalence (hb : ProjBounded K) :
    EquivalenceRelation (parityRel (K := K)) := by
  obtain ⟨g, hg, hgb⟩ := hb
  exact ⟨⟨parityDiag, AsmHom.ext rfl, AsmHom.ext rfl⟩,
    ⟨⟨paritySwap, AsmHom.ext rfl, AsmHom.ext rfl⟩⟩,
    ⟨⟨parityTransHom g hg (fun n => (hgb n).1) (fun n => (hgb n).2),
      AsmHom.ext rfl, AsmHom.ext rfl⟩⟩⟩

/-! ## The core: `E` is not the level of ANY morphism out of `∇ℕ`

  The uniformity argument.  Note that no hypothesis is placed on the codomain `Q`
  or its caucuses, and cover-ness of `x` is never used — a fortiori `E` is not the
  level of a cover (`¬ IsEffective`). -/

/-- The point of the parity table over the class-`k` pair `(2k, 2k+1)`. -/
def parityPair (k : Nat) : (paritySrc (K := K)).X :=
  ⟨(ULift.up (2 * k), ULift.up (2 * k + 1)), show 2 * k / 2 = (2 * k + 1) / 2 by omega⟩

/-- **The §2.153 non-effectiveness core.**  `E` is not mutually contained with the
    level `x ⊚ x°` of any morphism `x : ∇ℕ → Q`.  Proof (uniformity of naming): the
    level's caucuses over `∇ℕ` are full (`level_caucus_iff`), so the modulus `φ` of a
    containment `level ⊂ E` is defined at the single index `0` with a single value
    `m₀` that must be an `E`-caucus index of EVERY glued pair — but the class-`(m₀+1)`
    pair (in the level via `E ⊂ level`) is off-diagonal and of class `> m₀`. -/
theorem parityRel_not_level {Q : Assembly.{u} K} (x : nablaNat ⟶ Q)
    (hEle : RelLe (parityRel (K := K)) (graph x ⊚ (graph x)°))
    (hlevelE : RelLe (graph x ⊚ (graph x)°) (parityRel (K := K))) : False := by
  obtain ⟨⟨h, hhA, hhB⟩⟩ := hEle
  obtain ⟨⟨g, hgA, hgB⟩⟩ := hlevelE
  obtain ⟨φ, hφmem, hφtr⟩ := g.tracked
  -- over ∇ℕ the level's caucuses are FULL: every index names every point
  have hfull : ∀ n (yy : (graph x ⊚ (graph x)°).src.X),
      (graph x ⊚ (graph x)°).src.caucus n yy :=
    fun n yy => (level_caucus_iff x n yy).mpr ⟨trivial, trivial⟩
  -- the two columns of `g (h (parityPair k))` are `2k` and `2k+1`
  have eA : ∀ k, (g.toFun (h.toFun (parityPair k))).val.1 = ULift.up (2 * k) := fun k =>
    (congrArg (fun m => AsmHom.toFun m (h.toFun (parityPair k))) hgA).trans
      (congrArg (fun m => AsmHom.toFun m (parityPair k)) hhA)
  have eB : ∀ k, (g.toFun (h.toFun (parityPair k))).val.2 = ULift.up (2 * k + 1) := fun k =>
    (congrArg (fun m => AsmHom.toFun m (h.toFun (parityPair k))) hgB).trans
      (congrArg (fun m => AsmHom.toFun m (parityPair k)) hhB)
  -- the single value `m₀ = φ(0)` of the tracking modulus at index 0
  obtain ⟨m₀, hm₀, _⟩ := hφtr 0 (h.toFun (parityPair 0)) (hfull 0 _)
  -- track the SAME index 0 at the class-(m₀+1) point
  obtain ⟨m₁, hm₁, hc⟩ := hφtr 0 (h.toFun (parityPair (m₀ + 1))) (hfull 0 _)
  obtain rfl : m₀ = m₁ := φ.functional hm₀ hm₁
  -- `E`'s caucus at m₀ must contain the class-(m₀+1) pair: contradiction
  have hc' : (g.toFun (h.toFun (parityPair (K := K) (m₀ + 1)))).val.1.down
        = (g.toFun (h.toFun (parityPair (K := K) (m₀ + 1)))).val.2.down
      ∨ (g.toFun (h.toFun (parityPair (K := K) (m₀ + 1)))).val.1.down / 2 ≤ m₀ := hc
  have dA : (g.toFun (h.toFun (parityPair (K := K) (m₀ + 1)))).val.1.down = 2 * (m₀ + 1) :=
    congrArg ULift.down (eA (m₀ + 1))
  have dB : (g.toFun (h.toFun (parityPair (K := K) (m₀ + 1)))).val.2.down
      = 2 * (m₀ + 1) + 1 := congrArg ULift.down (eB (m₀ + 1))
  rcases hc' with heq | hle
  · omega
  · omega

/-- **§2.153, category form**: the parity relation is NOT effective — it is not the
    level of any cover (§1.568). -/
theorem parityRel_not_effective : ¬ IsEffective (parityRel (K := K)) := by
  rintro ⟨-, Q, x, -, hEle, hlevelE⟩
  exact parityRel_not_level x hEle hlevelE

/-! ## The headline: `Rel(Assembly K)` has a non-splitting equivalence relation

  Quotient-level packaging is `asm_not_effective_of_binRel` (S2_153c): `I := [E]` is a
  §2.12 equivalence relation of the allegory `Rel(Assembly K)`, and no map splits it — a
  splitting `f` is, by §2.148-dual fullness, the graph-class of an assembly morphism `q`,
  and `f ≫ f° = I` says exactly that `E` is mutually contained with the level of `q`,
  killed here by `parityRel_not_effective`. -/

/-- **§2.153 for any projection-bounded modulus system**: some assembly over `K`
    carries an equivalence relation of `Rel(Assembly K)` that does not split as a
    map — for ANY choice of codomain `d` and map `f`, with no hypothesis on `d`. -/
theorem asm_not_effective_of_projBounded (hb : ProjBounded K) :
    ∃ (A : Assembly.{u} K) (I : (⟨A⟩ : AsmRel K) ⟶ ⟨A⟩),
      Reflexive I ∧ Symmetric I ∧ Transitive I ∧
      ∀ (d : AsmRel K) (f : (⟨A⟩ : AsmRel K) ⟶ d), ¬ SplitsAsMap f I :=
  asm_not_effective_of_binRel parityRel (parityRel_equivalence hb) parityRel_not_effective

/-- Generic headline: over any projection-bounded `K`, the effective reflection of
    `Rel(Assembly K)` (§2.16(14)) is not an allegory of choice. -/
theorem asmReflection_not_ac_of_projBounded (hb : ProjBounded K) :
    ¬ CoversSplit (AsmEffReflection.{u} K) :=
  asmReflection_not_ac_of_notEffective (asm_not_effective_of_projBounded hb)

/-- **§2.153 (headline 1), over `Krec`**: `Rel(Assembly Krec)` is not effective — the
    parity relation on `∇ℕ` is an equivalence relation with no map-splitting. -/
theorem asm_not_effective :
    ∃ (A : Assembly.{u} Krec) (I : (⟨A⟩ : AsmRel Krec) ⟶ ⟨A⟩),
      Reflexive I ∧ Symmetric I ∧ Transitive I ∧
      ∀ (d : AsmRel Krec) (f : (⟨A⟩ : AsmRel Krec) ⟶ d), ¬ SplitsAsMap f I :=
  asm_not_effective_of_projBounded krec_projBounded

/-- **§2.153 / §2.16(13) (headline 2), over `Krec`**: the effective reflection of the
    category of assemblies over the partial-recursive modulus system is NOT an
    allegory of choice — covers do not all split there. -/
theorem asmReflection_not_ac : ¬ CoversSplit (AsmEffReflection.{u} Krec) :=
  asmReflection_not_ac_of_projBounded krec_projBounded

/-- **§2.153 over `allPartial`**: the witness is uniform — even the modulus system of
    ALL partial endofunctions yields a non-effective category of assemblies.  This
    refutes the old "over `allPartial` the obstruction vanishes / expected FALSE"
    analysis (the obstruction is uniformity of naming, not representative choice). -/
theorem asm_not_effective_allPartial :
    ∃ (A : Assembly.{u} ModulusSystem.allPartial)
      (I : (⟨A⟩ : AsmRel ModulusSystem.allPartial) ⟶ ⟨A⟩),
      Reflexive I ∧ Symmetric I ∧ Transitive I ∧
      ∀ (d : AsmRel ModulusSystem.allPartial)
        (f : (⟨A⟩ : AsmRel ModulusSystem.allPartial) ⟶ d), ¬ SplitsAsMap f I :=
  asm_not_effective_of_projBounded allPartial_projBounded

/-- **§2.153 / §2.16(13) over `allPartial`**: the effective reflection fails AC there
    too. -/
theorem asmReflection_not_ac_allPartial :
    ¬ CoversSplit (AsmEffReflection.{u} ModulusSystem.allPartial) :=
  asmReflection_not_ac_of_projBounded allPartial_projBounded

end Freyd.Alg
