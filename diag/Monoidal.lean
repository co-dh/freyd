/-
  `diag.Monoidal` — the poset-enriched symmetric monoidal category underlying every layer.

  functorialSemanticsForRelationalTheories.pdf Def. 4.1 opens "A cartesian bicategory of
  relations is a poset enriched category
  that is symmetric monoidal and additionally …".  This file supplies exactly that opening clause;
  `diag.CB` adds the "additionally".

  STRICT, deliberately — this branch is the strict variant, kept for comparison against the
  non-strict tower.  The papers state their syntax over props (Def. 2.2: objects are `ℕ` and
  `m ⊕ n = m + n`), where the monoidal product is strict, and this file follows them: there is no
  associator, there are no unitors, and there is no pentagon or triangle, because `(a ⊗ b) ⊗ c` IS
  `a ⊗ (b ⊗ c)` and `𝕀 ⊗ a` IS `a`, as Lean types.  Only the symmetry survives as a real arrow — a
  symmetric monoidal category is never strict in its symmetry.

  HOW STRICTNESS IS OBTAINED.  Objects are `Word O`, the words in the generators `O`, presented in
  Cayley form as `List O → List O` with `⊗` function composition and `𝕀` the identity function.
  Composition of functions is associative by `rfl` and unital by `rfl`-plus-eta, so the object
  equations are DEFINITIONAL and every law below states without a single transport.  The two
  cheaper-looking routes both fail:
    * `List O` with `++` — `(as ++ bs) ++ cs = as ++ (bs ++ cs)` is `List.append_assoc`, a theorem
      proved by induction, and `rfl` is rejected with "Type mismatch: rfl has type `?m = ?m` but is
      expected to have type `as ++ bs ++ cs = as ++ (bs ++ cs)`";
    * strictness as PROPOSITIONAL class fields (`tens_assoc : tens (tens a b) c = tens a (tens b c)`,
      `runit_eq : tens a tunit = a`) with `▸` in the laws — the laws can be stated, at the price of a
      transport in each, but the first proof that has to move an arrow along one dies with
      "Tactic `rewrite` failed: motive is not type correct".

  THE PRICE, in two parts, both real.
    1. `Word O` is EVERY endofunction of `List O`, not only the concatenations, so a model must
       supply arrows at objects that no word names.  And `Rel(Set)` (`AOP/A6_1_RelSet.lean`), whose
       tensor is the carrier product, is not a model at all: `(a × b) × c` is not `a × (b × c)` as a
       Lean type.  The `diag/RelSet*.lean` soundness files are absent from this branch.
    2. With the objects strict, an object no longer records its own bracketing, so the elaborator
       can no longer recover the split from a type: `Word.tens ?x ?y =?= n ⊗ (n ⊗ n)` has several
       solutions and Lean's first-order heuristic takes the outermost one, which in `frob_left` and
       in the hexagon is the wrong one.  The fix is the ascription in the `⊗ₕ` notation below, which
       stops the expected type from being propagated into `tensHom`'s implicit objects before its
       explicit arrow arguments have determined them.  It is load-bearing everywhere in `diag/`.

  SYMBOL CHOICE.  functorialSemanticsForRelationalTheories.pdf writes its single monoidal
  product `⊕`.  We write `⊗` and keep `⊕`
  free for the biproduct that `diag.Tape` adds (TapeDiagrams.pdf Def. 7.1), so the two products never
  collide once both layers exist.
-/
import diag.Basic

universe v u

namespace Freyd.Diag

open Freyd

/-- The objects of a strict monoidal category: WORDS in the generators `O`, in Cayley form —
    a word is represented by the function that prefixes it.  Concatenation then becomes function
    composition, which Lean's definitional equality already knows to be associative and unital. -/
def Word (O : Type u) : Type u := List O → List O

namespace Word

variable {O : Type u}

/-- The monoidal product on objects: concatenation of words, i.e. composition of the functions
    that represent them. -/
def tens (a b : Word O) : Word O := fun w => a (b w)

/-- The monoidal unit `I`: the empty word, i.e. the identity function. -/
def unit : Word O := fun w => w

/-- The one-letter word on a generator — what makes `Word O` the words over `O` rather than an
    anonymous monoid of endofunctions. -/
def gen (x : O) : Word O := fun w => x :: w

scoped infixr:70 " ⊗ " => Word.tens
scoped notation:max "𝕀" => Word.unit

end Word

open scoped Word

/-- A poset-enriched STRICT symmetric monoidal category: `OrderedCat` on the word objects, plus a
    tensor whose action on arrows is functorial, monotone, strictly associative and strictly
    unital, with the symmetry as an honest iso. -/
class SymMonCat (O : Type u) extends OrderedCat.{v} (Word O) where
  /-- The action of the product on arrows. -/
  tensHom {a a' b b' : Word O} (R : a ⟶ a') (S : b ⟶ b') : a ⊗ b ⟶ a' ⊗ b'

  /-- The product is a functor: it preserves identities. -/
  tensHom_id (a b : Word O) : tensHom (𝟙 a) (𝟙 b) = 𝟙 (a ⊗ b)
  /-- The product is a functor: interchange with composition. -/
  tensHom_comp {a a' a'' b b' b'' : Word O}
      (R : a ⟶ a') (R' : a' ⟶ a'') (S : b ⟶ b') (S' : b' ⟶ b'') :
    tensHom (R ≫ R') (S ≫ S') = tensHom R S ≫ tensHom R' S'
  /-- Poset enrichment of `⊗`, the counterpart of `comp_mono`. -/
  tensHom_mono {a a' b b' : Word O} {R R' : a ⟶ a'} {S S' : b ⟶ b'} :
    R ≤ R' → S ≤ S' → (tensHom R S) ≤ (tensHom R' S')

  /-- STRICT ASSOCIATIVITY.  The two bracketings are already the same OBJECT; this says they are
      the same ARROW, which is what `α = 𝟙` amounts to and is not implied by the object equation. -/
  tensHom_assoc {a a' b b' c c' : Word O} (R : a ⟶ a') (S : b ⟶ b') (T : c ⟶ c') :
    tensHom (tensHom R S) T = (tensHom R (tensHom S T) : _)
  /-- STRICT LEFT UNIT, what is left of `λ = 𝟙`. -/
  tensHom_lunit {a b : Word O} (R : a ⟶ b) : tensHom (𝟙 𝕀) R = R
  /-- STRICT RIGHT UNIT, what is left of `ρ = 𝟙`. -/
  tensHom_runit {a b : Word O} (R : a ⟶ b) : tensHom R (𝟙 𝕀) = R

  /-- Symmetry `a ⊗ b ⟶ b ⊗ a`. -/
  swap (a b : Word O) : a ⊗ b ⟶ b ⊗ a
  swap_swap (a b : Word O) : swap a b ≫ swap b a = 𝟙 (a ⊗ b)
  swap_nat {a a' b b' : Word O} (R : a ⟶ a') (S : b ⟶ b') :
    tensHom R S ≫ swap a' b' = swap a b ≫ tensHom S R
  /-- Hexagon, read with `α = 𝟙`: a symmetry past a product is the two symmetries in turn.  The
      three associators of the non-strict statement have all become identities. -/
  hexagon (a b c : Word O) :
    swap a (b ⊗ c) = (tensHom (swap a b) (𝟙 c) : _) ≫ (tensHom (𝟙 b) (swap a c) : _)

namespace SymMonCat

/-- `⊗` on arrows.  THE ASCRIPTION IS LOAD-BEARING, not decoration: without it Lean propagates the
    expected type into `tensHom`'s implicit objects before the explicit arrows have determined
    them, and since a strict object does not record its own bracketing, `Word.tens ?x ?y` against a
    three-letter word is solved the wrong way — `frob_left` then reports "`∇ n` has type
    `n ⊗ n ⟶ n` but is expected to have type `n ⟶ …`".  With the ascription the arrows are
    elaborated first and the objects come out of them. -/
scoped notation:70 R:71 " ⊗ₕ " S:70 => ((SymMonCat.tensHom R S : _))

end SymMonCat

open SymMonCat

variable {O : Type u} [SymMonCat.{v} O]

/-- `R ⊗ₕ 𝟙` then `𝟙 ⊗ₕ S` is `R ⊗ₕ S`: the two ways of building a product arrow agree.
    Used constantly to split a `⊗` of composites into stages. -/
theorem tensHom_split {a a' b b' : Word O} (R : a ⟶ a') (S : b ⟶ b') :
    (R ⊗ₕ 𝟙 b) ≫ (𝟙 a' ⊗ₕ S) = R ⊗ₕ S := by
  rw [← tensHom_comp, Cat.comp_id, Cat.id_comp]

/-- The other splitting order. -/
theorem tensHom_split' {a a' b b' : Word O} (R : a ⟶ a') (S : b ⟶ b') :
    (𝟙 a ⊗ₕ S) ≫ (R ⊗ₕ 𝟙 b') = R ⊗ₕ S := by
  rw [← tensHom_comp, Cat.comp_id, Cat.id_comp]

/-- `γ_{a,I} = 𝟙_a`.  Mac Lane lists `γ;λ = ρ` among the axioms of a symmetric monoidal category and
    it is a `SymMonCat` field in the non-strict tower; here the unitors are identities, so what it
    says is that the symmetry against the unit is the identity — and THAT is a theorem.  The hexagon
    at `b := I` gives `(γ_{a,I} ⊗ 𝟙_c);γ_{a,c} = γ_{a,c}`; cancel `γ` and take `c := I`. -/
theorem swap_unit_right (a : Word O) : swap a (𝕀 : Word O) = 𝟙 a := by
  have key : ∀ c : Word O, (swap a (𝕀 : Word O) ⊗ₕ 𝟙 c) = 𝟙 (a ⊗ c) := by
    intro c
    -- `hx` is the hexagon at `b := I`, restated at the reduced objects: `𝕀 ⊗ c` and `c` are the
    -- same object but not the same TERM, so the restatement is an `exact`, not a rewrite.
    have hx : (swap a (𝕀 : Word O) ⊗ₕ 𝟙 c) ≫ swap a c = swap a c := by
      have h := hexagon a (𝕀 : Word O) c
      rw [tensHom_lunit] at h
      exact h.symm
    have hid : ((swap a (𝕀 : Word O) ⊗ₕ 𝟙 c) ≫ (swap a c ≫ swap c a))
        = (swap a (𝕀 : Word O) ⊗ₕ 𝟙 c) := by
      rw [swap_swap a c]; exact Cat.comp_id _
    calc (swap a (𝕀 : Word O) ⊗ₕ 𝟙 c)
        = (swap a (𝕀 : Word O) ⊗ₕ 𝟙 c) ≫ (swap a c ≫ swap c a) := hid.symm
      _ = ((swap a (𝕀 : Word O) ⊗ₕ 𝟙 c) ≫ swap a c) ≫ swap c a := (Cat.assoc _ _ _).symm
      _ = swap a c ≫ swap c a := by rw [hx]
      _ = 𝟙 (a ⊗ c) := swap_swap a c
  have h := key (𝕀 : Word O)
  rw [tensHom_runit] at h
  exact h

/-- `γ_{I,a} = 𝟙_a`, the mirror of `swap_unit_right` through `swap_swap`. -/
theorem swap_unit_left (a : Word O) : swap (𝕀 : Word O) a = 𝟙 a := by
  calc swap (𝕀 : Word O) a
      = swap (𝕀 : Word O) a ≫ 𝟙 a := (Cat.comp_id _).symm
    _ = swap (𝕀 : Word O) a ≫ swap a (𝕀 : Word O) := by rw [swap_unit_right]
    _ = 𝟙 a := swap_swap _ _

end Freyd.Diag
