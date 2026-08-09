/-
  Freyd & Scedrov, *Categories and Allegories* §1.395–§1.397
  The genuine Q-SEQUENCE and its SATISFACTION RELATION (with ∀/∃ steps).

  A Q-sequence here is a finite telescope of arrows rooted at A₀, together with a
  sequence of quantifiers Q₀, Q₁, …, Qₙ ∈ {∀, ∃} (book §1.395):

      A₀ --α₁--> A₁ --α₂--> ... --αₙ--> Aₙ        (Q₁, …, Qₙ) and a trailing Q₀

  A morphism f : A₀ ⟶ B SATISFIES the Q-sequence by recursion on the telescope
  (`Satisfies` below).  The COMPLEMENTARY Q-SEQUENCE (`QSeq.complement`) transposes
  every quantifier ∀↔∃ keeping the arrows; the book DEFINES satisfaction of the
  complement to be the negation of satisfaction of the original — that identity is
  our Thm 2.

  Boundary (§1.395): the book's sequence carries a trailing quantifier Q₀, and
  "if n = 0 then A₀→B satisfies iff Q₀ = ∀".  So the empty telescope is NOT
  quantifier-free: it is `nil A q`, satisfied exactly when `q = .all` (the book's
  ∀, "customarily omitted when at the end").  Folding Q₀ away (`Satisfies nil = True`
  unconditionally) would BREAK Thm 2 at n=0 — `nil`'s complement would be itself,
  so `True ↔ ¬True` would be demanded — hence we keep Q₀.

  This is NOT §1.392 (finite presentation by a graph + path equations): that lives
  in `S1_38.lean` and has no quantifiers.

  Composition is DIAGRAM ORDER `≫` (Freyd's juxtaposition: `α ≫ g` = first α, then g).
  Hand-built category theory only (no `Mathlib.CategoryTheory.*`).
-/

module

public import Freyd.S1_31

open Freyd

universe v u

variable {𝒟 : Type u} [Cat.{v} 𝒟]

namespace Freyd

/-! ## §1.395 Quantifiers and Q-sequences -/

/-- A quantifier attached to a Q-sequence step: `all` = ∀, `ex` = ∃. -/
public inductive Quant | all | ex
deriving DecidableEq

/-- Transpose a quantifier (∀↔∃); the engine of the complementary Q-sequence. -/
@[expose] public def Quant.flip : Quant → Quant
  | .all => .ex
  | .ex  => .all

@[simp] theorem Quant.flip_flip : ∀ q : Quant, q.flip.flip = q
  | .all => rfl
  | .ex  => rfl

/-- A Q-SEQUENCE rooted at `A` in the ambient category `𝒟`: a finite telescope of
    quantifier-tagged arrows.  `nil A q` is the empty telescope carrying the trailing
    quantifier `q = Q₀` (book §1.395: ∀ is customarily omitted at the end). -/
public inductive QSeq (𝒟 : Type u) [Cat.{v} 𝒟] : 𝒟 → Type (max u v)
  | nil  (A : 𝒟) (q : Quant) : QSeq 𝒟 A
  | cons {A A' : 𝒟} (q : Quant) (α : A ⟶ A') (rest : QSeq 𝒟 A') : QSeq 𝒟 A

/-- SATISFACTION of a Q-sequence `s` rooted at `A` by a morphism `f : A ⟶ B`.

    Empty telescope (§1.395 boundary): `nil A q` is satisfied iff `q = .all` ("A₀→B
    satisfies iff Q₀ = ∀").  Each step extends the witness over the next arrow `α`,
    the triangle `α ≫ g = f` asserting that `g : A' ⟶ B` agrees with `f` over `A`. -/
@[expose] public def Satisfies : {A : 𝒟} → QSeq 𝒟 A → {B : 𝒟} → (A ⟶ B) → Prop
  | _, .nil _ q,          _, _ => q = .all
  | _, .cons .all α rest, _, f => ∀ g, α ≫ g = f → Satisfies rest g
  | _, .cons .ex  α rest, _, f => ∃ g, α ≫ g = f ∧ Satisfies rest g

@[simp] public theorem satisfies_nil_all {A B : 𝒟} (f : A ⟶ B) : Satisfies (.nil A .all) f :=
  rfl

@[simp] public theorem not_satisfies_nil_ex {A B : 𝒟} (f : A ⟶ B) : ¬ Satisfies (.nil A .ex) f := by
  intro h; exact Quant.noConfusion h

@[simp] public theorem satisfies_cons_all {A A' B : 𝒟} (α : A ⟶ A') (rest : QSeq 𝒟 A')
    (f : A ⟶ B) : Satisfies (.cons .all α rest) f ↔ ∀ g, α ≫ g = f → Satisfies rest g :=
  Iff.rfl

@[simp] public theorem satisfies_cons_ex {A A' B : 𝒟} (α : A ⟶ A') (rest : QSeq 𝒟 A')
    (f : A ⟶ B) : Satisfies (.cons .ex α rest) f ↔ ∃ g, α ≫ g = f ∧ Satisfies rest g :=
  Iff.rfl

/-- The COMPLEMENTARY Q-SEQUENCE (§1.395): transpose every quantifier ∀↔∃ (including
    the trailing Q₀), keeping the arrows.  (Contrast §1.392's op-dual presentation,
    which reverses arrows instead.) -/
@[expose] public def QSeq.complement : {A : 𝒟} → QSeq 𝒟 A → QSeq 𝒟 A
  | _, .nil A q       => .nil A q.flip
  | _, .cons q α rest => .cons q.flip α rest.complement

@[simp] theorem QSeq.complement_complement :
    ∀ {A : 𝒟} (s : QSeq 𝒟 A), s.complement.complement = s
  | _, .nil _ q       => by simp [QSeq.complement, Quant.flip_flip]
  | _, .cons _ _ rest => by simp [QSeq.complement, Quant.flip_flip, complement_complement rest]

/-! ## Theorem 1 (§1.395, last para): satisfaction is invariant under post-composing an iso

  If `e : B ⟶ B'` is an isomorphism then `f` satisfies `s` iff `f ≫ e` does.  Both
  directions are constructive (induction on `s`): an extension downstairs is built
  by post-composing with `e`, upstairs by post-composing with `e⁻¹`.  Sorry-free,
  axiom-free. -/

/-- Forward half of Thm 1, stated with an explicit two-sided inverse `e'` so we can
    apply it in both directions of the `↔`.  Each extension `g` post-composes by `e`;
    the ∀-step recovers a downstairs extension `g' ≫ e'` and cancels with `e'≫e = id`. -/
private theorem satisfies_postcomp
    {B B' : 𝒟} (e : B ⟶ B') (e' : B' ⟶ B)
    (hee : e ≫ e' = Cat.id B) (hee2 : e' ≫ e = Cat.id B') :
    ∀ {A : 𝒟} (s : QSeq 𝒟 A) (f : A ⟶ B), Satisfies s f → Satisfies s (f ≫ e)
  | _, .nil _ _,          _, h => h
  | _, .cons .all α rest, f, h => by
      intro g' htri
      -- recover the downstairs extension g := g' ≫ e' and feed it to `h`
      have hg : α ≫ (g' ≫ e') = f := by
        rw [← Cat.assoc, htri, Cat.assoc, hee, Cat.comp_id]
      have hr := satisfies_postcomp e e' hee hee2 rest _ (h (g' ≫ e') hg)
      -- (g'≫e')≫e = g'≫(e'≫e) = g' since e'≫e = id
      rwa [Cat.assoc, hee2, Cat.comp_id] at hr
  | _, .cons .ex  α rest, f, h => by
      obtain ⟨g, htri, hrest⟩ := h
      exact ⟨g ≫ e, by rw [← Cat.assoc, htri], satisfies_postcomp e e' hee hee2 rest g hrest⟩

/-- THEOREM 1 (§1.395). Post-composing by an isomorphism `e : B ⟶ B'` preserves
    satisfaction: `Satisfies s f ↔ Satisfies s (f ≫ e)`.  Constructive, axiom-free. -/
public theorem satisfies_iff_postcomp_iso {A B B' : 𝒟} (s : QSeq 𝒟 A) (f : A ⟶ B)
    {e : B ⟶ B'} (he : IsIso e) : Satisfies s f ↔ Satisfies s (f ≫ e) := by
  obtain ⟨e', h1, h2⟩ := he
  refine ⟨satisfies_postcomp e e' h1 h2 s f, fun h => ?_⟩
  -- reverse direction = forward one with the inverse e', then rewrite (f≫e)≫e' = f
  have hr := satisfies_postcomp e' e h2 h1 s (f ≫ e) h
  rwa [Cat.assoc, h1, Cat.comp_id] at hr

/-! ## Theorem 2 (§1.395): complement = negation of satisfaction

  `Satisfies s.complement f ↔ ¬ Satisfies s f`.  This is the book's DEFINING identity
  for the complementary Q-sequence ("A₀→B satisfies a Q-sequence iff it does not
  satisfy the complementary Q-sequence").  It is quantifier De Morgan, so the full
  `↔` needs `Classical` (¬∀ ↔ ∃¬).  The CONSTRUCTIVE HALF
  (`Satisfies s.complement f → ¬ Satisfies s f`) is axiom-free; the converse uses
  `Classical` (via `not_forall`).

  Axiom split (verified by `#print axioms`):
    * `satisfies_complement_imp_not`  — no axioms.
    * `satisfies_complement_iff_not`  — `Classical.choice` (+ `propext`/`Quot`). -/

/-- CONSTRUCTIVE HALF of Thm 2: satisfying the complement entails NOT satisfying the
    original.  Axiom-free.  Induction on `s`; each quantifier becomes the De Morgan
    "easy" direction. -/
public theorem satisfies_complement_imp_not :
    ∀ {A : 𝒟} (s : QSeq 𝒟 A) {B : 𝒟} (f : A ⟶ B),
      Satisfies s.complement f → ¬ Satisfies s f
  | _, .nil _ q,          _, f, hcomp, hsat => by
      -- complement flips Q₀: hcomp : q.flip = .all, hsat : q = .all → contradiction
      cases q <;> simp_all [QSeq.complement, Quant.flip]
  | _, .cons .all α rest, _, f, hcomp, hsat => by
      -- complement step is ∃: ⟨g, α≫g=f, Sat rest.complement g⟩; original ∀ gives
      -- Sat rest g; recurse to a contradiction.
      obtain ⟨g, htri, hc⟩ := hcomp
      exact satisfies_complement_imp_not rest g hc (hsat g htri)
  | _, .cons .ex  α rest, _, f, hcomp, hsat => by
      -- complement step is ∀; original ∃ gives a witness g; instantiate and recurse.
      obtain ⟨g, htri, hs⟩ := hsat
      exact satisfies_complement_imp_not rest g (hcomp g htri) hs

/-- THEOREM 2 (§1.395), full `↔`. The complementary Q-sequence is satisfied exactly
    when the original is not.  Uses `Classical` for the De Morgan converse (¬∀ ⇒ ∃¬).
    The forward implication is the axiom-free `satisfies_complement_imp_not`. -/
public theorem satisfies_complement_iff_not :
    ∀ {A : 𝒟} (s : QSeq 𝒟 A) {B : 𝒟} (f : A ⟶ B),
      Satisfies s.complement f ↔ ¬ Satisfies s f
  | _, .nil _ q,          _, f =>
      ⟨satisfies_complement_imp_not (.nil _ q) f, by cases q <;> simp [QSeq.complement, Quant.flip]⟩
  | _, .cons .all α rest, _, f => by
      -- original ∀; complement ∃.  ¬∀g(α≫g=f→Sat rest g) ⇔ ∃g, α≫g=f ∧ ¬Sat rest g
      -- ⇔ ∃g, α≫g=f ∧ Sat rest.complement g  (IH).
      constructor
      · exact satisfies_complement_imp_not (.cons .all α rest) f
      · -- ¬∀g(α≫g=f→Sat rest g): find a witness `g` violating the implication by a
        -- second contradiction, then use IH to turn ¬Sat rest g into Sat rest.complement g.
        intro h
        apply Classical.byContradiction
        intro hne
        -- hne : ¬∃g, α≫g=f ∧ Sat rest.complement g  ⇒  Sat (cons all) f, contradicting h
        apply h
        intro g htri
        apply Classical.byContradiction
        intro hns
        exact hne ⟨g, htri, (satisfies_complement_iff_not rest g).2 hns⟩
  | _, .cons .ex  α rest, _, f => by
      -- original ∃; complement ∀.  ¬∃g(α≫g=f ∧ Sat rest g) ⇔ ∀g, α≫g=f → ¬Sat rest g
      -- ⇔ ∀g, α≫g=f → Sat rest.complement g  (IH).
      constructor
      · exact satisfies_complement_imp_not (.cons .ex α rest) f
      · intro h g htri
        rw [satisfies_complement_iff_not rest g]
        intro hs
        exact h ⟨g, htri, hs⟩

/-! ## §1.396 A class with diagonal fills preserves (and reflects) satisfaction

  Book §1.396: given classes 𝔅, 𝒜 of morphisms such that every square with top in 𝔅
  and right in 𝒜 has a "back-diagonal" fill, the morphisms of 𝒜 preserve and reflect
  satisfaction of any Q-sequence whose steps lie in 𝔅.

  We abstract the geometric hypothesis as an HONEST named predicate `DiagonalFill t`
  on a single right-edge morphism `t : B ⟶ B'`: every Q-sequence step `α` and witness
  `f` over `B`, together with an extension `g'` over `B'` closing the outer square
  (`α ≫ g' = f ≫ t`), admits a back-diagonal `g` over `B` with `α ≫ g = f` and
  `g ≫ t = g'`.  This is exactly the §1.396 lifting obligation (NOT a `True` stub).

  Preservation is by induction (∃ needs nothing; ∀ uses `DiagonalFill`).  Reflection
  is preservation of the COMPLEMENT (Thm 1 + Thm 2), exactly as the book reduces it. -/

/-- §1.396 diagonal-fill (back-diagonal) condition for a right-edge morphism
    `t : B ⟶ B'`.  Honest existence-of-lift predicate; no placeholder. -/
def DiagonalFill {B B' : 𝒟} (t : B ⟶ B') : Prop :=
  ∀ {A A' : 𝒟} (α : A ⟶ A') (f : A ⟶ B) (g' : A' ⟶ B'),
    α ≫ g' = f ≫ t → ∃ g : A' ⟶ B, α ≫ g = f ∧ g ≫ t = g'

/-- §1.396 PRESERVATION. If `t : B ⟶ B'` has the diagonal-fill property then it
    preserves satisfaction: `Satisfies s f → Satisfies s (f ≫ t)`.  Constructive,
    axiom-free.  Induction on `s`: the ∀-step consumes one `DiagonalFill` lift. -/
theorem diagFill_preserves_satisfies {B B' : 𝒟} {t : B ⟶ B'} (ht : DiagonalFill t) :
    ∀ {A : 𝒟} (s : QSeq 𝒟 A) (f : A ⟶ B), Satisfies s f → Satisfies s (f ≫ t)
  | _, .nil _ _,          _, h => h
  | _, .cons .all α rest, f, h => by
      intro g' htri
      -- outer square α ≫ g' = f ≫ t ; lift to back-diagonal g over B
      obtain ⟨g, hg, hgt⟩ := ht α f g' htri
      -- upstairs hypothesis on g, pushed down by t, equals the goal at g'
      have hr := diagFill_preserves_satisfies ht rest g (h g hg)
      rwa [hgt] at hr
  | _, .cons .ex  α rest, f, h => by
      obtain ⟨g, htri, hrest⟩ := h
      exact ⟨g ≫ t, by rw [← Cat.assoc, htri], diagFill_preserves_satisfies ht rest g hrest⟩

/-- §1.396 REFLECTION (book's reduction: reflect = preserve-the-COMPLEMENT).
    `DiagonalFill t` quantifies over every step, so the same hypothesis preserves
    satisfaction of `s.complement`; reflection for `s` then follows from Thm 2.
    `Satisfies s (f ≫ t) → Satisfies s f`.  Uses `Classical` (only via Thm 2's converse). -/
theorem diagFill_reflects_satisfies {B B' : 𝒟} {t : B ⟶ B'} (ht : DiagonalFill t)
    {A : 𝒟} (s : QSeq 𝒟 A) (f : A ⟶ B) :
    Satisfies s (f ≫ t) → Satisfies s f := by
  intro h
  apply Classical.byContradiction
  intro hsf
  -- ¬Sat s f ⇒ Sat s.complement f ⇒ (preserve) Sat s.complement (f≫t) ⇒ ¬Sat s (f≫t)
  have hc  : Satisfies s.complement f := (satisfies_complement_iff_not s f).2 hsf
  have hct : Satisfies s.complement (f ≫ t) := diagFill_preserves_satisfies ht s.complement f hc
  exact (satisfies_complement_imp_not s (f ≫ t) hct) h

/-! ## §1.397 Equivalence functors preserve and reflect satisfaction

  Book §1.397: inflation cross-sections preserve/reflect Q-sequences whose steps
  separate objects; compositions of such morphisms do too; by §1.361 every
  equivalence functor factors through inflations, so it preserves and reflects.

  Here `Satisfies` lives WITHIN one category `𝒟`, so "the right-edge `t`" is an
  isomorphism (the §1.395 iso case) — Thm 1 already gives preserve AND reflect for an
  iso `t`, with NO axioms.  That is the honest minimum the in-category statement
  supports; we record it as `iso_preserves`/`iso_reflects`.

  The genuine §1.397 statement (an EQUIVALENCE FUNCTOR `T : 𝒞 → 𝒟` between DIFFERENT
  categories preserves/reflects via the §1.361 inflation-class factorization) is
  cross-category: it re-indexes the whole telescope along `T`.  The §1.361 inflation
  machinery is NOT needed: full + faithful already give the cross-category transport
  directly (induction on the telescope, per step: ∃-step pushes witness forward;
  ∀-step pulls back via fullness + reflects via faithfulness).
  `equiv_preserves_satisfies` is proved axiom-free (axioms: propext). -/

/-- §1.397 (iso case, axiom-free): an isomorphism `e : B ⟶ B'` preserves satisfaction.
    Direct corollary of Thm 1. -/
theorem iso_preserves_satisfies {A B B' : 𝒟} (s : QSeq 𝒟 A) (f : A ⟶ B)
    {e : B ⟶ B'} (he : IsIso e) : Satisfies s f → Satisfies s (f ≫ e) :=
  (satisfies_iff_postcomp_iso s f he).1

/-- §1.397 (iso case, axiom-free): an isomorphism `e : B ⟶ B'` reflects satisfaction.
    Direct corollary of Thm 1. -/
theorem iso_reflects_satisfies {A B B' : 𝒟} (s : QSeq 𝒟 A) (f : A ⟶ B)
    {e : B ⟶ B'} (he : IsIso e) : Satisfies s (f ≫ e) → Satisfies s f :=
  (satisfies_iff_postcomp_iso s f he).2

/-- Re-index a Q-sequence along a functor `T : 𝒞 → 𝒟`: push every object and arrow of
    the telescope through `T`, keeping the quantifiers.  This is the cross-category
    transport that lets §1.397 STATE "T preserves satisfaction". -/
@[expose] public def QSeq.map {𝒞 : Type u} [Cat.{v} 𝒞] (T : Functor 𝒞 𝒟) :
    {A : 𝒞} → QSeq 𝒞 A → QSeq 𝒟 (T.obj A)
  | _, .nil _ q       => .nil (T.obj _) q
  | _, .cons q α rest => .cons q (T.map α) (rest.map T)

/-- §1.397 hypothesis "a Q-sequence all of whose functors separate objects": each step
    arrow `α` (a functor, since the ambient `𝒟` is the category of small categories)
    is an `Embedding` in the ambient sense.  We carry it as a per-step predicate
    `Sep` supplied by the caller, so §1.397 quantifies over it honestly (the general
    proof inspects each step).  Non-vacuous: a `nil` carries no obligation, a `cons`
    demands `Sep` of its arrow and recurses. -/
def StepsSeparate {𝒞 : Type u} [Cat.{v} 𝒞] (Sep : ∀ {A A' : 𝒞}, (A ⟶ A') → Prop) :
    {A : 𝒞} → QSeq 𝒞 A → Prop
  | _, .nil _ _       => True
  | _, .cons _ α rest => Sep α ∧ StepsSeparate Sep rest

/-- §1.397 (GENERAL inflation-class case), axiom-free.

    The book's statement: an equivalence functor `T : 𝒞 → 𝒟` preserves satisfaction.
    Re-indexing the telescope along `T` (`s.map T`) and pushing the witness `f`
    through `T` (`hT.map f`), satisfaction transports: `Satisfies s f → Satisfies
    (s.map T) (T.map f)`.

    PROOF: by induction on the telescope `s`.  An equivalence functor is full and
    faithful (`EquivalenceFunctor T = Embedding T ∧ Full T ∧ HasRepresentativeImage T`),
    so each quantifier transports along `T`:

    * `∃`-step: push the chosen witness `g'` forward to `hT.map g'`; the factoring
      equation transports by `map_comp`.
    * `∀`-step: any `g : T A' ⟶ T B` over `T.map f` is `hT.map g'` by FULLNESS, and
      `T.map α ≫ T.map g' = T.map f` reflects to `α ≫ g' = f` by FAITHFULNESS
      (`Embedding`), so the universally-quantified premise of `Satisfies s f` applies.

    The §1.361 inflation-class factorization is NOT needed: full + faithful already
    give the cross-category transport directly.  `_hsep` (`StepsSeparate`) is the
    book's hypothesis on the telescope but is subsumed by faithfulness of `T`, hence
    unused. -/
theorem equiv_preserves_satisfies {𝒞 : Type u} [Cat.{v} 𝒞] (T : Functor 𝒞 𝒟)
    (hT' : EquivalenceFunctor T) {A B : 𝒞} (s : QSeq 𝒞 A) (f : A ⟶ B)
    {Sep : ∀ {X Y : 𝒞}, (X ⟶ Y) → Prop} (_hsep : StepsSeparate Sep s)
    (hsat : Satisfies s f) : Satisfies (s.map T) (T.map f) := by
  obtain ⟨hfaith, hfull, _⟩ := hT'
  clear _hsep
  induction s generalizing B with
  | nil A q =>
    cases q with
    | all => exact (satisfies_nil_all _)
    | ex  => exact (not_satisfies_nil_ex f hsat).elim
  | cons q α rest ih =>
    cases q with
    | all =>
      -- goal: ∀ g, T.map α ≫ g = T.map f → Satisfies (rest.map T) g
      rw [QSeq.map, satisfies_cons_all]
      intro g hg
      obtain ⟨g', rfl⟩ := hfull g                    -- g = T.map g' by fullness
      have hαg : α ≫ g' = f := by                     -- reflect the factoring
        apply hfaith
        rw [T.map_comp]; exact hg
      have := (satisfies_cons_all α rest f).1 hsat g' hαg
      exact ih g' this
    | ex =>
      rw [QSeq.map, satisfies_cons_ex]
      obtain ⟨g', hαg, hrest⟩ := (satisfies_cons_ex α rest f).1 hsat
      exact ⟨T.map g', by rw [← T.map_comp, hαg], ih g' hrest⟩

/-- §1.397 REFLECTION (cross-category): an equivalence functor `T : 𝒞 → 𝒟` reflects
    satisfaction.  If `Satisfies (s.map T) (hT.map f)` holds in `𝒟` then `Satisfies s f`
    holds in `𝒞`.  Symmetric to `equiv_preserves_satisfies`: fullness lifts the witness
    back, faithfulness reflects the factoring equation.  Uses `Classical` (via Thm 2). -/
theorem equiv_reflects_satisfies {𝒞 : Type u} [Cat.{v} 𝒞] (T : Functor 𝒞 𝒟)
    (hT' : EquivalenceFunctor T) {A B : 𝒞} (s : QSeq 𝒞 A) (f : A ⟶ B)
    {Sep : ∀ {X Y : 𝒞}, (X ⟶ Y) → Prop} (_hsep : StepsSeparate Sep s)
    (hsat : Satisfies (s.map T) (T.map f)) : Satisfies s f := by
  obtain ⟨hfaith, hfull, _⟩ := hT'
  clear _hsep
  induction s generalizing B with
  | nil A q =>
    cases q with
    | all => exact satisfies_nil_all f
    | ex  =>
      -- s.map T = nil _ .ex; hsat : ¬Satisfies (nil .ex) (hT.map f), contradiction
      simp [QSeq.map] at hsat
  | cons q α rest ih =>
    cases q with
    | all =>
      rw [satisfies_cons_all]
      intro g' hαg'
      -- need Satisfies rest g'
      -- push g' through T; have T.map α ≫ T.map g' = T.map f
      have hT_step : T.map α ≫ T.map g' = T.map f := by
        rw [← T.map_comp, hαg']
      -- hsat : ∀ g, T.map α ≫ g = T.map f → Satisfies (rest.map T) g
      rw [QSeq.map, satisfies_cons_all] at hsat
      have hD : Satisfies (rest.map T) (T.map g') := hsat _ hT_step
      exact ih g' hD
    | ex =>
      rw [satisfies_cons_ex]
      rw [QSeq.map, satisfies_cons_ex] at hsat
      obtain ⟨g, htri, hrest⟩ := hsat
      -- g : T A' ⟶ T B in 𝒟; lift to g' : A' ⟶ B by fullness
      obtain ⟨g', rfl⟩ := hfull g
      refine ⟨g', ?_, ih g' hrest⟩
      -- α ≫ g' = f; have T.map α ≫ T.map g' = T.map f (from htri); reflect by faith
      apply hfaith
      rw [T.map_comp]; exact htri

/-! ## §1.398 Q-trees and their satisfaction (TODO)

  Book §1.398: a Q-TREE is a rooted finite-length poset tree T with:
  - a collection of objects {Aᵢ}_{i∈T} and morphisms Aᵢ* → Aᵢ for i ≠ root,
  - a collection of quantifiers {Qᵢ} (∀ or ∃) for each node.
  A₀ → B satisfies the Q-tree iff (Q₀ = ∀ and for every child i of 0 and A₀→Aᵢ,
  Aᵢ→B satisfies the subtree at Aᵢ) or (Q₀ = ∃ and some such exists and satisfies).
  The book proves R-morphisms preserve and reflect satisfaction of Q-trees in C
  (same argument as §1.396, by induction on the tree).
  Corollary: equivalence functors preserve and reflect Q-trees all of whose
  morphisms separate objects.

  BOOK §1.398: R-morphisms preserve and reflect satisfaction of Q-trees in C.
  TODO: define `QTree` (branching generalization of `QSeq`) and prove the analogue
  of `diagFill_preserves_satisfies` for Q-trees. -/

/-! ## Examples (§1.39 sanity checks): unfold `Satisfies` to recognisable ∀/∃ statements -/

section Examples

variable {A B : 𝒟}

/-- A length-1 ∃ Q-sequence `(∃, α)` then trailing ∀: `f` satisfies it iff there is a
    factorization `g` of `f` through `α`.  This is the "α left-divides f" property. -/
example (α : A ⟶ B) (f : A ⟶ B) :
    Satisfies (.cons .ex α (.nil B .all)) f ↔ ∃ g : B ⟶ B, α ≫ g = f := by
  simp [Satisfies]

/-- A length-1 ∀ Q-sequence `(∀, α)` then trailing ∀: `f` satisfies it iff EVERY
    `g` with `α ≫ g = f` exists trivially — i.e. the obligation is the bare triangle
    universally, vacuously true here since the tail (trailing ∀) always holds. -/
example (α : A ⟶ B) (f : A ⟶ B) :
    Satisfies (.cons .all α (.nil B .all)) f := by
  intro g _; exact satisfies_nil_all g

/-- The empty telescope with trailing ∃ is NEVER satisfied (the "there exists a
    trailing object" obligation with no arrow), confirming `nil`'s quantifier matters. -/
example (f : A ⟶ B) : ¬ Satisfies (.nil A .ex) f := not_satisfies_nil_ex f

/-- Complement of the ∃-factorization sequence is the ∀-sequence, and (Thm 2) it is
    satisfied exactly when `f` does NOT factor through `α`. -/
example (α : A ⟶ B) (f : A ⟶ B) :
    Satisfies (QSeq.complement (.cons .ex α (.nil B .all))) f
      ↔ ¬ ∃ g : B ⟶ B, α ≫ g = f := by
  rw [satisfies_complement_iff_not]; simp [Satisfies]

end Examples

end Freyd
