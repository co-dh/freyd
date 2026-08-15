/-
  Freyd & Scedrov, *Categories and Allegories* §2.417 — Target 3.
  "A generator (as opposed to a progenitor) is not good enough."

  §2.417 concludes: `Rel(C)` HAS a generator (§2.417 target 2, `S2_417_Generator.lean`)
  but is NOT a power allegory, because — "just as in [1.96(10)]" — the ONLY object of `C`
  with a power-object is the COTERMINATOR (the initial object `O`).  By §2.414, `Rel(C)`
  is a power allegory iff `Map(Rel C) = C` is a topos iff EVERY object of `C` has a
  power-object; so a non-coterminator lacking a power-object refutes the power allegory.

  This file supplies the reachable, hole-free core of that conclusion:

    (1)  A faithful CONCRETE power-object condition in `Rel(C)` (`IsPowerObj`), phrased with
         the file's own equivariant relations `CRel` (§2.41/§1.9 universal property): `mem`
         is a power-object of `X` iff every equivariant relation `R : A → X` factors as
         `Λ(R) ⊚ mem` for a UNIQUE `C`-map `Λ(R) : A → P`.  `HasPowerObj X` bundles ∃P,mem.

    (2)  `RelCIsPowerAllegory := ∀ X, HasPowerObj X` — the concrete §2.414 content of
         "`Rel(C)` is a power allegory".  Target 3 is `¬ RelCIsPowerAllegory`.

    (3)  `singleton_of_power` — §2.415: a power-object yields the SINGLETON MAP `{·}:X → [X]`
         with `x ∈ {y} ⟺ x = y` (the classifier of the diagonal).  A genuine necessary
         consequence of `IsPowerObj`, true independent of any topos structure.

    (4)  `coterminator_hasPowerObject` — the POSITIVE half of §2.417's dichotomy: the
         coterminator `O` (empty carrier) DOES have a power-object, namely the terminator
         with the empty membership relation.  (Every relation into `O` is empty, so `Rel(-,O)`
         is represented by the terminator.)

  REACHABILITY VERDICT on the NEGATIVE half `¬ RelCIsPowerAllegory` (see trailing comment):
  it is NOT faithfully reachable over a FIXED label type `L`.  Freyd's §1.96(10) collapse is
  driven by "for all `s` in the universe" — the label universe is a PROPER CLASS; the map
  condition ranging over it is what kills power-objects of non-initial objects.  The
  `variable {L : Type}` encoding replaces that proper class by a SET, and over a set the
  collapse mechanism disappears (for `|L| ≤ 1`, `C` is literally the presheaf topos of a
  single endofunction, which HAS all power-objects and IS a power allegory).  Reaching
  target 3 needs a re-encoding of `C` with an unbounded label universe — a different file.

  MATHLIB-FREE.  Axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/

module

public import Freyd.S2_417_Generator

namespace Freyd.S2_417
open Freyd

variable {L : Type}

/-! ## §2.41  A concrete power-object in `Rel(C)`

  A morphism of `Rel(C)` is an equivariant relation (`CRel`, `S2_417_Generator.lean`).
  A MAP of `Rel(C)` (an entire single-valued relation) is the graph of a `C`-morphism
  `CHom`.  Precomposing the graph of `g : A → P` into `mem : P → X` gives the relation
  `(graph g ⊚ mem).rel a x = mem.rel (g a) x`.  Freyd's §2.41 universal property for the
  power-object `[X] = P` with membership `∋_X = mem` reads: every equivariant relation
  `R : A → X` equals `Λ(R) ⊚ mem` for a UNIQUE `C`-map `Λ(R) = g`. -/

/-- **§2.41 concrete power-object.**  `mem : P → X` is a power-object of `X` in `Rel(C)`:
    for every object `A` and every equivariant relation `R : A → X` there is a unique
    `C`-map `g : A → P` with `R = graph g ⊚ mem`, i.e. `R.rel a x ↔ mem.rel (g x) x`. -/
@[expose] public def IsPowerObj (X P : Obj L) (mem : CRel P X) : Prop :=
  ∀ (A : Obj L) (R : CRel A X),
    ∃ g : CHom A P, (∀ (a : A.S) (x : X.S), R.rel a x ↔ mem.rel (g.g a) x) ∧
      ∀ g' : CHom A P, (∀ (a : A.S) (x : X.S), R.rel a x ↔ mem.rel (g'.g a) x) → g' = g

/-- `X` has a power-object in `Rel(C)` (§2.414: needed of EVERY object for a power allegory). -/
@[expose] public def HasPowerObj (X : Obj L) : Prop := ∃ (P : Obj L) (mem : CRel P X), IsPowerObj X P mem

/-- **§2.414 concrete.**  "`Rel(C)` is a power allegory" — every object of `C` has a
    power-object.  §2.417 target 3 is the negation of this. -/
@[expose] public def RelCIsPowerAllegory (L : Type) : Prop := ∀ X : Obj L, HasPowerObj X

/-! ## §2.415  The singleton map — a necessary consequence of a power-object -/

/-- The diagonal / identity relation `1_X : X → X`, `x (1_X) y ⟺ x = y`; equivariant. -/
def idRel (X : Obj L) : CRel X X where
  rel x y := x = y
  equiv _ _ _ h := by cases h; rfl

/-- **§2.415.**  A power-object `mem` of `X` yields the SINGLETON MAP `{·} : X → [X]`, the
    (equivariant) classifier of the diagonal, with membership `y ∈ {x} ⟺ x = y`. -/
theorem singleton_of_power {X P : Obj L} {mem : CRel P X} (h : IsPowerObj X P mem) :
    ∃ sing : CHom X P, ∀ x y, mem.rel (sing.g x) y ↔ x = y := by
  obtain ⟨g, hg, _⟩ := h X (idRel X)
  exact ⟨g, fun x y => (hg x y).symm⟩

/-! ## §2.417  The coterminator has a power-object (positive half of the dichotomy) -/

/-- Auxiliary: the terminator carrier is a subsingleton. -/
public theorem unit_eq (a b : Unit) : a = b := by cases a; cases b; rfl

/-- The COTERMINATOR `O` of `C`: empty carrier (the initial object). -/
def zeroObj (L : Type) : Obj L where
  S := Empty
  s := fun x => x
  A := fun _ => False
  f := fun _ x => x

/-- The TERMINATOR `1` of `C`: one point, fixed by every action. -/
@[expose] public def oneObj (L : Type) : Obj L where
  S := Unit
  s := fun _ => ()
  A := fun _ => False
  f := fun _ x => x

/-- The unique `C`-map `A → 1` into the terminator. -/
def toOne (A : Obj L) : CHom A (oneObj L) := ⟨fun _ => (), fun _ _ => unit_eq _ _⟩

theorem toOne_unique (A : Obj L) (g : CHom A (oneObj L)) : g = toOne A := by
  apply CHom.ext; funext x; exact unit_eq _ _

/-- The empty membership relation `∅ : 1 → O` (there are no elements of `O` to be in). -/
def emptyMem (L : Type) : CRel (oneObj L) (zeroObj L) where
  rel _ x := x.elim
  equiv _ _ x := by exact x.elim

/-- **§2.417 (positive half).**  The coterminator `O` has a power-object: `[O] = 1` with the
    empty membership relation.  Every relation into `O` is empty, so `Rel(-,O)` is represented
    by the terminator, and the classifier of any `R : A → O` is the unique map `A → 1`. -/
theorem coterminator_isPowerObj : IsPowerObj (zeroObj L) (oneObj L) (emptyMem L) := by
  intro A R
  refine ⟨toOne A, ?_, ?_⟩
  · intro _ x; exact x.elim
  · intro g _; exact toOne_unique A g

/-- **§2.417.**  The coterminator has a power-object (`HasPowerObj` form). -/
theorem coterminator_hasPowerObject : HasPowerObj (zeroObj L) :=
  ⟨oneObj L, emptyMem L, coterminator_isPowerObj⟩

/-
  ## Target 3 — the negative half `¬ RelCIsPowerAllegory` — REACHABILITY GAP.

  Freyd's §1.96(10)/§2.417 collapse ("only the coterminator has a power-object") is powered
  by the map condition quantifying over ALL labels `a` "in the universe" — a PROPER CLASS.
  The `variable {L : Type}` encoding fixes `L` as a SET.  Over a set the collapse fails:

    * `|L| ≤ 1`: `C` is the category of a single endofunction (`x ↦ x^a`) with equivariant
      maps = the presheaf topos `[Bℕ, Set]`, which HAS all power-objects — so `RelCIsPowerAllegory`
      HOLDS and `¬ RelCIsPowerAllegory` is FALSE there.
    * general fixed `L`: the per-object active set `A ⊆ L` adds cross-label constraints, so `C`
      is not simply a presheaf topos, but there is no size/universe obstruction of the §1.96(10)
      kind, so a general refutation is not available (and would be UNSOUND for small `L`).

  A faithful `¬ RelCIsPowerAllegory` therefore requires re-encoding `C` with an unbounded /
  proper-class label universe (matching "for all `s` in the universe").  That is a separate
  formalization; asserting the negation here for fixed `L` would be false-with-a-hole, which
  this file deliberately avoids.  What IS proved: the concrete power-object universal property,
  the §2.415 singleton map it forces, and the positive half (coterminator has a power-object).
-/

end Freyd.S2_417
