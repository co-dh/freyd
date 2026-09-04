/-
  Bird & de Moor, *Algebra of Programming* §7.4 (book pp. 180-181) — the four cylinder beads as
  CONCRETE relations on `n`-tuples in `Rel(Set)`, and their lax naturality PROVED.

  The book says of these four only "to define `generate` we will need a number of other LAX
  NATURAL TRANSFORMATIONS of different types" and then cites "naturality of `trans`" and
  "naturality of `moves`" in the p.183 derivation.  `AOP.A7_4_Cylinder` keeps them as bare
  object-indexed parameters, so nothing there can be computed with; here they get the book's own
  definitions and the squares are proved.  Same split as `AOP.A5_6_ListCombinators` /
  `AOP.A5_7_ListBeads` for the list combinators, and the same shape: `N` is a plain function on
  relations rather than a bundled `Relator`, so each square is stated as the raw inequality.

  `N A = Aⁿ` — B&dM's `n`-tuple, one component per ROW of the cylinder — is `Fin n → A`, not a
  list: `trans` transposes a SET of tuples into a TUPLE of sets, which is a total function only
  because every tuple has the same length `n`.

  All four are graphs of polymorphic FUNCTIONS, so the free theorem gives the square on maps and
  `laxNatural_iff_strict_on_maps` (`AOP.A5_7`, B&dM Theorem 5.2) would carry it to every
  relation.  The squares below are proved DIRECTLY at an arbitrary relation instead — the
  pointwise Egli-Milner reading (`powerRel_apply`) makes that no longer than the map case, and it
  says at which relations the inclusion is strict without a second theorem.

  Composition is diagram order (`≫`) throughout: B&dM `X·Y` = Freyd `Y ≫ X`.
-/
module

public import AOP.A5_7_PowerBeads
public import AOP.A6_ConsList

namespace Freyd.Alg.RelSet.Tuple

open Freyd

-- Everything is indexed by RelSet OBJECTS, not by the carrier types: `powerObj a` is an object,
-- and a `dE`-shaped index would leave the elaborator to solve `dE ?A =?= powerObj a` at every
-- `N(P(R))`.
variable {a b : RelSet.{0}} {n : Nat}

/-! ## The `n`-tuple relator `N` -/

/-- `N A = Aⁿ`, B&dM's `n`-tuple: one component per row of the cylinder (book p.180). -/
@[expose] public abbrev dTuple (n : Nat) (a : RelSet.{0}) : RelSet.{0} := ⟨Fin n → a.carrier⟩

/-- The tuple relator's action `N(R)`: one `R` per component, the length untouched.  The
    elementwise shape `listP` has for lists, with the shape fixed by `n`. -/
@[expose] public def tupleP (n : Nat) (R : a ⟶ b) : dTuple n a ⟶ dTuple n b :=
  fun t u => ∀ k, R (t k) (u k)

/-! ## The four beads (book pp. 180-181) -/

/-- `rot j t` is `t` rotated up by `j` rows, the top row glued to the bottom (`+` on `Fin n` is
    already mod `n`). -/
@[expose] public def rot {A : Type} (j : Fin n) (t : Fin n → A) : Fin n → A := fun k => t (k + j)

/-- **`moves(t) = {t, rot(t), rot²(t), …}`** (book p.180): the tuple rotated up, unrotated and
    down — every rotation of it, since a path may step up, straight or down. -/
@[expose] public def moves : dTuple n a ⟶ PowerAllegory.powerObj (dTuple n a) :=
  graph fun t => fun u => ∃ j, rot j t = u

/-- **`trans{(a,b,c),(x,y,z)} = ({a,x},{b,y},{c,z})`** (book p.180): component `k` of the result
    is the set of the `k`-th components. -/
@[expose] public def transT :
    PowerAllegory.powerObj (dTuple n a) ⟶ dTuple n (PowerAllegory.powerObj a) :=
  graph fun S => fun k => fun x => ∃ t, S t ∧ t k = x

/-- **`setify(1,2,3,4) = {1,2,3,4}`** (book p.181): the components of a tuple as a set — which
    row a component came from is forgotten. -/
@[expose] public def setify : dTuple n a ⟶ PowerAllegory.powerObj a :=
  graph fun t => fun x => ∃ k, t k = x

/-- **`zip((a₁,…,aₙ),(x₁,…,xₙ)) = ((a₁,x₁),…,(aₙ,xₙ))`** (book p.181): the product half of the
    book's `zip = 𝟙 + zip'`, which is the only half `cyl-step` names (`AOP.A7_4_Cylinder`'s
    `cyl_step` hypothesis `hzip`); on the `𝟙` summand `zip` is `N(inl)` and carries no content. -/
@[expose] public def zipT :
    (⟨(Fin n → a.carrier) × (Fin n → b.carrier)⟩ : RelSet.{0})
      ⟶ dTuple n ⟨a.carrier × b.carrier⟩ :=
  graph fun p => fun k => (p.1 k, p.2 k)

/-! ## Lax naturality -/

/-- **`setify` is lax natural**: `N(R) setify ⊑ setify P(R)`.  The components of an `N(R)`-image
    of `t` are an Egli-Milner `R`-image of the components of `t`: term₁ sends the component `t k`
    to `u k`, term₂ fetches `u k` back from `t k`.

    Not an equality: at `n = 1` the right side relates `(a)` to any `{b,c}` with `R a b`,
    `R a c`, while `setify` of a one-tuple is always a singleton. -/
public theorem setify_lax_natural (R : a ⟶ b) :
    tupleP n R ≫ setify ⊑ setify ≫ powerRel R := by
  refine le_iff.mpr fun t S h => ?_
  obtain ⟨u, hRu, hS⟩ := h
  -- `setify u S` IS `S = {u k}`, but only definitionally: name the equation before rewriting.
  have hSeq : S = fun x => ∃ k, u k = x := hS
  subst hSeq
  refine ⟨fun x => ∃ k, t k = x, rfl, ?_, ?_⟩
  · rintro x ⟨k, rfl⟩
    exact ⟨u k, hRu k, ⟨k, rfl⟩⟩
  · rintro y ⟨k, rfl⟩
    exact ⟨t k, ⟨k, rfl⟩, hRu k⟩

/-- **`moves` is lax natural**: `N(R) moves ⊑ moves P(N(R))`.  Rotating commutes with acting on
    every component — `rot j` of an `N(R)`-image is the `N(R)`-image of `rot j` — so the two sets
    of rotations correspond rotation by rotation, which is both Egli-Milner halves at once. -/
public theorem moves_lax_natural (R : a ⟶ b) :
    tupleP n R ≫ moves ⊑ moves ≫ powerRel (tupleP n R) := by
  refine le_iff.mpr fun t S h => ?_
  obtain ⟨u, hRu, hS⟩ := h
  have hSeq : S = fun v => ∃ j, rot j u = v := hS
  subst hSeq
  refine ⟨fun v => ∃ j, rot j t = v, rfl, ?_, ?_⟩
  · rintro v ⟨j, rfl⟩
    exact ⟨rot j u, fun k => hRu (k + j), ⟨j, rfl⟩⟩
  · rintro w ⟨j, rfl⟩
    exact ⟨rot j t, ⟨j, rfl⟩, fun k => hRu (k + j)⟩

/-- **`trans` is lax natural**: `P(N(R)) trans ⊑ trans N(P(R))`.  Transposing and then relating
    componentwise is beaten by relating the sets of tuples first: each of the two Egli-Milner
    halves at component `k` is the corresponding half of `P(N(R))` read at `k`. -/
public theorem trans_lax_natural (R : a ⟶ b) :
    powerRel (tupleP n R) ≫ transT ⊑ transT ≫ tupleP n (powerRel R) := by
  refine le_iff.mpr fun S q h => ?_
  obtain ⟨S', ⟨h1, h2⟩, hq⟩ := h
  have hqeq : q = fun k => fun x => ∃ u, S' u ∧ u k = x := hq
  subst hqeq
  refine ⟨fun k => fun x => ∃ t, S t ∧ t k = x, rfl, fun k => ⟨?_, ?_⟩⟩
  · rintro x ⟨t, hSt, rfl⟩
    obtain ⟨u, hRu, hS'u⟩ := h1 t hSt
    exact ⟨u k, hRu k, ⟨u, hS'u, rfl⟩⟩
  · rintro y ⟨u, hS'u, rfl⟩
    obtain ⟨t, hSt, hRt⟩ := h2 u hS'u
    exact ⟨t k, ⟨t, hSt, rfl⟩, hRt k⟩

/-- **The free theorem of `zip`, and it is STRICT**: `(N(R)×N(S)) zip = zip N(R×S)`.  Both sides
    relate `(t,v)` to `w` exactly when `R (t k) (w k).1` and `S (v k) (w k).2` at every `k`;
    `zip` is a bijection, so the tuple of pairs the right side names is the pair of tuples the
    left side names.  Compare `cons_natural` (`AOP.A5_6_ListCombinators`), the same verdict for
    the same reason. -/
public theorem zip_natural (R : a ⟶ b) {c d : RelSet.{0}} (S : c ⟶ d) :
    rprodMap (tupleP n R) (tupleP n S) ≫ zipT = zipT ≫ tupleP n (rprodMap R S) := by
  apply hom_ext; intro p w
  constructor
  · rintro ⟨⟨u, x⟩, ⟨hRu, hSx⟩, rfl⟩
    exact ⟨fun k => (p.1 k, p.2 k), rfl, fun k => ⟨hRu k, hSx k⟩⟩
  · rintro ⟨_, rfl, hw⟩
    refine ⟨(fun k => (w k).1, fun k => (w k).2), ⟨fun k => (hw k).1, fun k => (hw k).2⟩, ?_⟩
    exact funext fun k => rfl

/-- **`zip` is lax natural** — the lax half of the STRICT `zip_natural`. -/
public theorem zip_lax_natural (R : a ⟶ b) {c d : RelSet.{0}} (S : c ⟶ d) :
    rprodMap (tupleP n R) (tupleP n S) ≫ zipT ⊑ zipT ≫ tupleP n (rprodMap R S) :=
  le_of_eq (zip_natural R S)

end Freyd.Alg.RelSet.Tuple
