/-
  Bird & de Moor, *Algebra of Programming* §6.1  Digits of a number (book pp. 137-140)
  — the first WORKED PROGRAM, derived in the concrete allegory `Rel(Set)` (`AOP.A6_1_RelSet`).

  A decimal representation is a non-empty sequence of digits starting with a nonzero digit:
    `Decimal ::= wrap Digit⁺ | snoc (Decimal, Digit)`,
  the INITIAL ALGEBRA of the functor `F A = Digit⁺ + (A × Digit)` (book p.138).  `val` reads a
  decimal as a number — the catamorphism `⦇⁅embed, op⁆⦈` — and the program `digits` is a
  functional refinement of `val°` (spec (6.1): `digits ⊆ val°`).

  This file builds the reusable DATATYPE-AS-INITIAL-ALGEBRA core (the `Relator` `F` and the
  `InitialAlgebra` instance for `Decimal`, the first in the repo), then derives §6.1's headline:
  the recursive equation the converse of a catamorphism satisfies (mirrored to diagram order),
    `⦇⁅g, h⁆⦈° = (g° ≫ wrap) ∪ (h° ≫ (⦇⁅g, h⁆⦈° × id) ≫ snoc)`   (`⁅g, h⁆` = the book's `[g, h]`),
  which is exactly `val° = (wrap·embed°) ∪ (snoc·(val°×id)·op°)` of book p.138 at `φ = [embed, op]`.
  The headline is proved BY THE BOOK'S OWN EQUATIONAL DERIVATION (p.138): a six-step calc —
  {catamorphisms}, {converse}, {definition of F}, {α = [wrap,snoc]}, {coproduct fusion},
  {coproduct (5.11)} — over the `junc`/`sumMap` calculus of `AOP.A5_3`, not by pointwise cases.
  Everything is constructive (the fold is defined FROM the algebra-relation, no choice).
-/
module

public import AOP.A6_1_RelSet
public import AOP.A5_3

namespace Freyd.Alg.RelSet.Digits

open Freyd

/- Bird and de Moor's product-bifunctor notation.  Lean can overload the same `×` token used for
   products of types because here the operands elaborate as relations. -/
local infixr:70 " × " => rprodMap

/-- The canonical coproduct action of two relations in `Rel(Set)`.  It hides the chosen
    `Sum` coproducts so calculations can use Bird and de Moor's `R + S` notation. -/
@[expose] public def rsumMap {a a' b b' : RelSet.{0}} (R : a ⟶ a') (S : b ⟶ b') :
    (⟨a.carrier ⊕ b.carrier⟩ : RelSet.{0}) ⟶ ⟨a'.carrier ⊕ b'.carrier⟩ :=
  sumMap (sumCop a b) (sumCop a' b') R S

/-- Bird and de Moor's coproduct-bifunctor `+` on relations. -/
@[expose] public instance {a a' b b' : RelSet.{0}} :
    HAdd (a ⟶ a') (b ⟶ b')
      ((⟨a.carrier ⊕ b.carrier⟩ : RelSet.{0}) ⟶ ⟨a'.carrier ⊕ b'.carrier⟩) where
  hAdd := rsumMap

/-! ## Datatypes and their objects in `Rel(Set)` (universe 0) -/

/-- The ten decimal digits `{0,…,9}`. -/
@[expose] public def Digit : Type := Fin 10
/-- The nine nonzero digits `{1,…,9}`. -/
@[expose] public def DigitP : Type := { d : Fin 10 // d.val ≠ 0 }

/-- Decimal representations: `wrap` a leading nonzero digit, then `snoc` further digits. -/
public inductive Decimal where
  | wrap : DigitP → Decimal
  | snoc : Decimal → Digit → Decimal

/-- Object of `Rel(Set)` carrying `Digit`.  `abbrev` so `.carrier` reduces to `Digit`. -/
abbrev dDigit : RelSet.{0} := ⟨Digit⟩
/-- Object of `Rel(Set)` carrying `Digit⁺`. -/
@[expose] public abbrev dDigitP : RelSet.{0} := ⟨DigitP⟩
/-- Object of `Rel(Set)` carrying `Decimal`. -/
@[expose] public abbrev dDec : RelSet.{0} := ⟨Decimal⟩

/-! ## The functor `F A = Digit⁺ + (A × Digit)` -/

/-- Carrier of `F A`.  The first summand is spelled `dDigitP.carrier` (not `DigitP`) so that
    unifying an `⁅g, h⁆`-hole against `Fobj c` solves the coproduct object to the CONSTANT
    `dDigitP` — the same spelling standalone `⁅g, h⁆` gets — keeping `rw` steps syntactic. -/
@[expose] public def Fobj (c : RelSet.{0}) : RelSet.{0} := ⟨dDigitP.carrier ⊕ (c.carrier × Digit)⟩

/-- Action of `F` on a relation: identity on the `Digit⁺` summand, `R × id` on `A × Digit`. -/
@[expose] public def Fmap {c c' : RelSet.{0}} (R : c ⟶ c') : Fobj c ⟶ Fobj c' :=
  fun u v => match u, v with
    | Sum.inl d, Sum.inl d' => d = d'
    | Sum.inr p, Sum.inr q => R p.1 q.1 ∧ p.2 = q.2
    | _, _ => False

@[simp] theorem Fmap_ll {c c' : RelSet.{0}} (R : c ⟶ c') (d d' : DigitP) :
    Fmap R (Sum.inl d) (Sum.inl d') = (d = d') := rfl
@[simp] theorem Fmap_rr {c c' : RelSet.{0}} (R : c ⟶ c') (p : c.carrier × Digit)
    (q : c'.carrier × Digit) :
    Fmap R (Sum.inr p) (Sum.inr q) = (R p.1 q.1 ∧ p.2 = q.2) := rfl
@[simp] theorem Fmap_lr {c c' : RelSet.{0}} (R : c ⟶ c') (d : DigitP) (q : c'.carrier × Digit) :
    Fmap R (Sum.inl d) (Sum.inr q) = False := rfl
@[simp] theorem Fmap_rl {c c' : RelSet.{0}} (R : c ⟶ c') (p : c.carrier × Digit) (d : DigitP) :
    Fmap R (Sum.inr p) (Sum.inl d) = False := rfl

/-- `F` is a relator (monotone functor) on `Rel(Set)`. -/
@[expose] public def F : Relator RelSet.{0} RelSet.{0} where
  obj := Fobj
  map := Fmap
  -- constructive case split (no `grind` — it is classical and would put `Classical.choice`
  -- into every theorem whose statement mentions `F`, including the §6.1 headline)
  map_id c := hom_ext fun u v => by
    cases u with
    | inl d => cases v with
      | inl d' => exact ⟨congrArg Sum.inl, Sum.inl.inj⟩
      | inr q => exact ⟨False.elim, fun h => nomatch h⟩
    | inr p => cases v with
      | inl d' => exact ⟨False.elim, fun h => nomatch h⟩
      | inr q => exact ⟨fun h => congrArg Sum.inr (Prod.ext_iff.mpr h),
          fun h => Prod.ext_iff.mp (Sum.inr.inj h)⟩
  map_comp R S := hom_ext fun u v => by
    cases u with
    | inl d => cases v with
      | inl d' => exact ⟨fun h => ⟨Sum.inl d, rfl, h⟩,
          fun ⟨w, hw1, hw2⟩ => by cases w with
            | inl e => exact hw1.trans hw2
            | inr q => exact hw1.elim⟩
      | inr q => exact ⟨fun h => h.elim,
          fun ⟨w, hw1, hw2⟩ => by cases w with
            | inl e => exact hw2.elim
            | inr q' => exact hw1.elim⟩
    | inr p => cases v with
      | inl d' => exact ⟨fun h => h.elim,
          fun ⟨w, hw1, hw2⟩ => by cases w with
            | inl e => exact hw1.elim
            | inr q' => exact hw2.elim⟩
      | inr q =>
        obtain ⟨pa, pd⟩ := p; obtain ⟨qa, qd⟩ := q
        exact ⟨fun ⟨⟨m, hRm, hSm⟩, hpd⟩ => ⟨Sum.inr (m, pd), ⟨hRm, rfl⟩, ⟨hSm, hpd⟩⟩,
          fun ⟨w, hw1, hw2⟩ => by cases w with
            | inl e => exact hw1.elim
            | inr md => exact ⟨⟨md.1, hw1.1, hw2.1⟩, hw1.2.trans hw2.2⟩⟩
  map_mono {c c' R S} h := le_iff.mpr fun u v => by
    cases u <;> cases v <;>
      first | exact id | exact fun hh => ⟨le_iff.mp h _ _ hh.1, hh.2⟩ | exact False.elim

/-! ## `Decimal` is the initial algebra of `F` -/

/-- The constructor map `⁅wrap, snoc⁆ : F Decimal → Decimal`. -/
def con : (Fobj dDec).carrier → Decimal
  | Sum.inl d => Decimal.wrap d
  | Sum.inr p => Decimal.snoc p.1 p.2

/-- The structural fold of a decimal through an algebra `f`, defined DIRECTLY from the
    algebra-RELATION `f` (so no choice is needed to turn `f` into a function). -/
@[expose] public def cataFold {c : RelSet.{0}} (f : Fobj c ⟶ c) : Decimal → c.carrier → Prop
  | Decimal.wrap d => fun r => f (Sum.inl d) r
  | Decimal.snoc dec dig => fun r => ∃ r', cataFold f dec r' ∧ f (Sum.inr (r', dig)) r

@[simp] theorem cataFold_wrap {c : RelSet.{0}} (f : Fobj c ⟶ c) (d : DigitP) (r : c.carrier) :
    cataFold f (Decimal.wrap d) r = f (Sum.inl d) r := rfl
@[simp] theorem cataFold_snoc {c : RelSet.{0}} (f : Fobj c ⟶ c) (dec : Decimal) (dig : Digit)
    (r : c.carrier) :
    cataFold f (Decimal.snoc dec dig) r = ∃ r', cataFold f dec r' ∧ f (Sum.inr (r', dig)) r := rfl

/-- Every decimal folds to at least one value: the fold is entire when `f` is. -/
theorem cataFold_total {c : RelSet.{0}} (f : Fobj c ⟶ c) (hf : Map f) :
    ∀ dec : Decimal, ∃ r, cataFold f dec r
  | Decimal.wrap d => entire_total hf.1 (Sum.inl d)
  | Decimal.snoc dec dig => by
    obtain ⟨r', hr'⟩ := cataFold_total f hf dec
    obtain ⟨r, hr⟩ := entire_total hf.1 (Sum.inr (r', dig))
    exact ⟨r, r', hr', hr⟩

/-- The fold is single-valued: it is simple when `f` is. -/
theorem cataFold_functional {c : RelSet.{0}} (f : Fobj c ⟶ c) (hf : Map f) :
    ∀ (dec : Decimal) (r r' : c.carrier), cataFold f dec r → cataFold f dec r' → r = r'
  | Decimal.wrap d, r, r', h1, h2 => simple_uniq hf.2 h1 h2
  | Decimal.snoc dec dig, r, r', h1, h2 => by
    obtain ⟨s, hs, hfs⟩ := h1
    obtain ⟨s', hs', hfs'⟩ := h2
    have hss : s = s' := cataFold_functional f hf dec s s' hs hs'
    subst hss
    exact simple_uniq hf.2 hfs hfs'

theorem cataFold_map {c : RelSet.{0}} (f : Fobj c ⟶ c) (hf : Map f) :
    Map (a := dDec) (b := c) (cataFold f) := by
  refine ⟨?_, ?_⟩
  · show dom (cataFold f) = 𝟙 dDec
    apply hom_ext; intro dec dec'
    refine ⟨fun h => h.1, fun (h : dec = dec') => ⟨h, ?_⟩⟩
    subst h
    obtain ⟨r, hr⟩ := cataFold_total f hf dec
    exact ⟨r, hr, hr⟩
  · refine le_iff.mpr fun r r' h => ?_
    obtain ⟨dec, h1, h2⟩ := h
    exact cataFold_functional f hf dec r r' h1 h2

/-- The catamorphism (fold) of `φ` as a genuine morphism `dDec ⟶ c`. -/
@[expose] public def cataR {c : RelSet.{0}} (φ : Fobj c ⟶ c) : dDec ⟶ c := cataFold φ

/-- The book's banana brackets for the catamorphism.  Global (not scoped): each datatype engine
    declares the same notation for its own `cataR`; Lean overload resolution picks the one whose
    algebra type fits. -/
notation:max "⦇" φ "⦈" => cataR φ

/-- The fold square `α ≫ ⦇φ⦈ = F⦇φ⦈ ≫ φ` for EVERY algebra `φ` (not only maps) — the
    homomorphism equation, hoisted out of `decInitial` so the §6.1 derivation can cite it. -/
theorem cata_square {c : RelSet.{0}} (φ : Fobj c ⟶ c) :
    graph con ≫ ⦇φ⦈ = F.map ⦇φ⦈ ≫ φ := by
  apply hom_ext; intro u r
  cases u with
  | inl d =>
    constructor
    · intro h; obtain ⟨dec, hdec, hfold⟩ := h
      have hd : dec = Decimal.wrap d := hdec; subst hd
      exact ⟨Sum.inl d, rfl, hfold⟩
    · intro h; obtain ⟨v, hv, hfv⟩ := h
      cases v with
      | inl d' => have hdd : d = d' := hv; subst hdd; exact ⟨Decimal.wrap d, rfl, hfv⟩
      | inr q => exact hv.elim
  | inr p =>
    obtain ⟨pa, pd⟩ := p
    constructor
    · intro h; obtain ⟨dec, hdec, hfold⟩ := h
      have hd : dec = Decimal.snoc pa pd := hdec; subst hd
      obtain ⟨r', hr', hfr'⟩ := hfold
      exact ⟨Sum.inr (r', pd), ⟨hr', rfl⟩, hfr'⟩
    · intro h; obtain ⟨v, hv, hfv⟩ := h
      cases v with
      | inl d' => exact hv.elim
      | inr q =>
        obtain ⟨qa, qd⟩ := q
        obtain ⟨hq1, hq2⟩ := hv
        have hpq : pd = qd := hq2
        refine ⟨Decimal.snoc pa pd, rfl, qa, hq1, ?_⟩
        rw [hpq]; exact hfv

/-- The initial `F`-algebra: `Decimal` with the constructor `⁅wrap, snoc⁆`, folds as
    catamorphisms.  This is the first concrete `InitialAlgebra` instance in the repo. -/
def decInitial : InitialAlgebra F where
  t := dDec
  α := graph con
  α_map := graph_map con
  cata f _ := cataFold f
  cata_map f hf := cataFold_map f hf
  cata_comm f _ := cata_square f
  cata_unique f hf h hmap hcomm := by
    apply hom_ext; intro dec
    induction dec with
    | wrap d =>
      intro r
      have key := congrFun (congrFun hcomm (Sum.inl d)) r
      constructor
      · intro hh
        have hlhs : (graph con ≫ h) (Sum.inl d) r := ⟨Decimal.wrap d, rfl, hh⟩
        rw [key] at hlhs
        obtain ⟨v, hv, hfv⟩ := hlhs
        cases v with
        | inl d' => have hdd : d = d' := hv; subst hdd; exact hfv
        | inr q => exact hv.elim
      · intro hc
        have hrhs : (F.map h ≫ f) (Sum.inl d) r := ⟨Sum.inl d, rfl, hc⟩
        rw [← key] at hrhs
        obtain ⟨dec, hdec, hh⟩ := hrhs
        have hd : dec = Decimal.wrap d := hdec; subst hd; exact hh
    | snoc dec dig ih =>
      intro r
      have key := congrFun (congrFun hcomm (Sum.inr (dec, dig))) r
      constructor
      · intro hh
        have hlhs : (graph con ≫ h) (Sum.inr (dec, dig)) r := ⟨Decimal.snoc dec dig, rfl, hh⟩
        rw [key] at hlhs
        obtain ⟨v, hv, hfv⟩ := hlhs
        cases v with
        | inl d' => exact hv.elim
        | inr q =>
          obtain ⟨qa, qd⟩ := q
          obtain ⟨hq1, hq2⟩ := hv
          have hpq : dig = qd := hq2
          refine ⟨qa, (ih qa).mp hq1, ?_⟩
          rw [hpq]; exact hfv
      · intro hc
        obtain ⟨r', hr', hfr'⟩ := hc
        have hrhs : (F.map h ≫ f) (Sum.inr (dec, dig)) r :=
          ⟨Sum.inr (r', dig), ⟨(ih r').mpr hr', rfl⟩, hfr'⟩
        rw [← key] at hrhs
        obtain ⟨d', hd', hh⟩ := hrhs
        have hd : d' = Decimal.snoc dec dig := hd'; subst hd; exact hh

/-! ## §6.1 headline: the recursive equation for the converse of a catamorphism

  Book p.138 derives, for `val = ⦇⁅embed, op⁆⦈`,
    `val° = (wrap·embed°) ∪ (snoc·(val°×id)·op°)`.
  Following the book, the algebra is presented as a junc `⁅g, h⁆` of its two components (the
  book's `[g, h]`; `alg_eq_junc` shows every algebra has this form, so nothing is lost).
  Mirrored to diagram order, `wrap·embed°` becomes `embed° ≫ wrap` and `snoc·(val°×id)·op°`
  becomes `op° ≫ (val° ×× id) ≫ snoc`.  The proof is the book's own point-free chain:
  expand the catamorphism, converse it, split the coproduct. -/

/-- The book's junc `[g, h]` over the canonical sum coproduct of `Rel(Set)` (Lean reserves
    `[ ]` for lists, so the closest available glyphs are `⁅ ⁆`).  The coproduct is inferred
    from the component types, so the notation works for every datatype engine. -/
notation:max "⁅" g ", " h "⁆" => junc (sumCop _ _) g h

/-- The constructor `wrap` as a relation (the book's `wrap : Digit⁺ → Decimal`). -/
def wrap : dDigitP ⟶ dDec := graph Decimal.wrap
/-- The constructor `snoc` as a relation (the book's `snoc : Decimal × Digit → Decimal`). -/
def snoc : (⟨Decimal × Digit⟩ : RelSet.{0}) ⟶ dDec := graph (fun p => Decimal.snoc p.1 p.2)

/-! Supporting laws for the derivation, each a single ingredient of one p.138 step. -/

/-- `α` is a cover: `α° ≫ α = 1` (`con` is surjective — every decimal is a `wrap` or a `snoc`).
    Cancels the constructor in the fold square, giving the fixed-point form below. -/
theorem con_recip_con : (graph con)° ≫ graph con = 𝟙 dDec := by
  apply hom_ext; intro dec dec'
  constructor
  · intro h; obtain ⟨u, h1, h2⟩ := h; exact h1.trans h2.symm
  · intro h
    have h' : dec = dec' := h
    subst h'
    cases dec with
    | wrap d => exact ⟨Sum.inl d, rfl, rfl⟩
    | snoc a b => exact ⟨Sum.inr (a, b), rfl, rfl⟩

/-- The fold's fixed-point form `⦇φ⦈ = α° ≫ F⦇φ⦈ ≫ φ` — the book's "{catamorphisms}" step. -/
theorem cata_fix {c : RelSet.{0}} (φ : Fobj c ⟶ c) :
    ⦇φ⦈ = (graph con)° ≫ (F.map ⦇φ⦈ ≫ φ) :=
  calc ⦇φ⦈
      = 𝟙 dDec ≫ ⦇φ⦈ := (Cat.id_comp _).symm
    _ = ((graph con)° ≫ graph con) ≫ ⦇φ⦈ := by rw [con_recip_con]
    _ = (graph con)° ≫ (graph con ≫ ⦇φ⦈) := Cat.assoc _ _ _
    _ = (graph con)° ≫ (F.map ⦇φ⦈ ≫ φ) := by rw [cata_square]

/-- `F`'s action in the coproduct calculus: `F R = id + (R × id)` as a `sumMap` over the
    concrete coproducts `sumCop` — the raw material of the "{definition of F}" step. -/
theorem Fmap_eq_sumMap {c c' : RelSet.{0}} (R : c ⟶ c') :
    F.map R = sumMap (sumCop dDigitP ⟨c.carrier × Digit⟩) (sumCop dDigitP ⟨c'.carrier × Digit⟩)
      (𝟙 dDigitP) (R × 𝟙 dDigit) := by
  apply hom_ext; intro u v
  constructor
  · intro h
    cases u with
    | inl d => cases v with
      | inl d' => exact Or.inl ⟨d, rfl, d', h, rfl⟩
      | inr q => exact h.elim
    | inr p => cases v with
      | inl d' => exact h.elim
      | inr q => exact Or.inr ⟨p, rfl, q, h, rfl⟩
  · intro h
    cases h with
    | inl h => obtain ⟨d, h1, e, h2, h3⟩ := h; subst h1; subst h3; exact h2
    | inr h => obtain ⟨p, h1, q, h2, h3⟩ := h; subst h1; subst h3; exact h2

/-- Converse of `F`'s action: `(F R)° = id + (R° × id)` — the "{definition of F}" step
    as used on p.138 (the functor applied to the conversed fold). -/
theorem Fmap_recip {c c' : RelSet.{0}} (R : c ⟶ c') :
    (F.map R)° = sumMap (sumCop dDigitP ⟨c'.carrier × Digit⟩) (sumCop dDigitP ⟨c.carrier × Digit⟩)
      (𝟙 dDigitP) (R° × 𝟙 dDigit) := by
  rw [Fmap_eq_sumMap, sumMap_recip, recip_id, rprodMap_recip]
  -- `rw [recip_id]` cannot key-match this last `(Cat.id dDigit)°`: its `Cat` instance sits
  -- behind `Allegory.toCat`, so apply the same law by congruence instead.
  exact congrArg (sumMap _ _ _) (congrArg (rprodMap _) recip_id)

/-- The constructor map as a junc: `α = ⁅wrap, snoc⁆` — the book's presentation of `α`. -/
theorem con_eq_junc : graph con = ⁅wrap, snoc⁆ := by
  apply hom_ext; intro u dec
  constructor
  · intro h
    cases u with
    | inl d => exact Or.inl ⟨d, rfl, h⟩
    | inr p => exact Or.inr ⟨p, rfl, h⟩
  · intro h
    cases h with
    | inl h => obtain ⟨d, h1, h2⟩ := h; subst h1; exact h2
    | inr h => obtain ⟨p, h1, h2⟩ := h; subst h1; exact h2

/-- Every algebra on `F` is a junc `⁅g, h⁆` of its two restrictions — so stating the
    derivation below for `⦇⁅g, h⁆⦈` loses no generality. -/
theorem alg_eq_junc {c : RelSet.{0}} (φ : Fobj c ⟶ c) :
    ∃ (g : dDigitP ⟶ c) (h : (⟨c.carrier × Digit⟩ : RelSet.{0}) ⟶ c), φ = ⁅g, h⁆ := by
  refine ⟨fun d r => φ (Sum.inl d) r, fun p r => φ (Sum.inr p) r, ?_⟩
  apply hom_ext; intro u r
  constructor
  · intro h
    cases u with
    | inl d => exact Or.inl ⟨d, rfl, h⟩
    | inr p => exact Or.inr ⟨p, rfl, h⟩
  · intro h
    cases h with
    | inl h => obtain ⟨d, h1, h2⟩ := h; subst h1; exact h2
    | inr h => obtain ⟨p, h1, h2⟩ := h; subst h1; exact h2

/-- **§6.1 (B&dM p.138)**: the converse of a catamorphism satisfies the recursive equation
    `val° = (wrap·embed°) ∪ (snoc·(val°×id)·op°)` (mirrored), for any algebra `⁅g, h⁆`.
    Instantiating `g := embed`, `h := op` gives the book's `val°` recursion verbatim.

    The proof is the book's derivation, step for step (brace-hints as on p.138). -/
theorem cata_converse_eq {c : RelSet.{0}} (g : dDigitP ⟶ c)
    (h : (⟨c.carrier × Digit⟩ : RelSet.{0}) ⟶ c) :
    ⦇⁅g, h⁆⦈° = g° ≫ wrap
      ∪ h° ≫ (⦇⁅g, h⁆⦈° × 𝟙 dDigit) ≫ snoc :=
  calc ⦇⁅g, h⁆⦈°
      -- {catamorphisms}: `⦇φ⦈ = α° ≫ F⦇φ⦈ ≫ φ`
    _ = ((graph con)° ≫ (F.map ⦇⁅g, h⁆⦈ ≫ ⁅g, h⁆))° := by rw [← cata_fix]
      -- {converse}: `(R ≫ S)° = S° ≫ R°`, `R°° = R`
    _ = ⁅g, h⁆° ≫ ((F.map ⦇⁅g, h⁆⦈)° ≫ graph con) := by
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, Cat.assoc]
      -- {definition of F}: `(F⦇φ⦈)° = id + (⦇φ⦈° × id)`
    _ = ⁅g, h⁆° ≫ (((𝟙 dDigitP) + (⦇⁅g, h⁆⦈° × 𝟙 dDigit)) ≫ graph con) := by
        dsimp only [HAdd.hAdd, rsumMap]
        rw [Fmap_recip]
      -- {α = ⁅wrap, snoc⁆}
    _ = ⁅g, h⁆° ≫ (((𝟙 dDigitP) +
          (⦇⁅g, h⁆⦈° × 𝟙 dDigit)) ≫ ⁅wrap, snoc⁆) := by
        rw [con_eq_junc]
      -- {coproduct fusion}: `(R + S) ≫ [P, Q] = [R ≫ P, S ≫ Q]`
    _ = ⁅g, h⁆° ≫ ⁅wrap, (⦇⁅g, h⁆⦈° × 𝟙 dDigit) ≫ snoc⁆ := by
        dsimp only [HAdd.hAdd, rsumMap]
        rw [sumMap_junc, Cat.id_comp]
      -- {coproduct (5.11)}: `⁅g, h⁆° ≫ ⁅P, Q⁆ = (g° ≫ P) ∪ (h° ≫ Q)`
    _ = g° ≫ wrap ∪ h° ≫ (⦇⁅g, h⁆⦈° × 𝟙 dDigit) ≫ snoc :=
        junc_recip_junc (sumCop dDigitP ⟨c.carrier × Digit⟩)

/-! ## The `val`uation catamorphism and its recursion (book p.138)

  `embed d = d` includes a nonzero digit as a number; `op (n, d) = 10·n + d`.  `val = ⦇⁅embed,
  op⁆⦈ : Decimal → ℕ` reads a decimal representation as a number.  (The book works in `ℕ⁺`; the
  positivity of the result is a side condition irrelevant to the recursion, so we land in `ℕ`.) -/

/-- The codomain object: the natural numbers. -/
@[expose] public abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-- The book's `embed : Digit⁺ → ℕ` — include a nonzero digit as a number. -/
def embed : dDigitP ⟶ dNat := graph fun d => d.1.val
/-- The book's `op (n, d) = 10·n + d` — append a digit to a number. -/
def op : (⟨Nat × Digit⟩ : RelSet.{0}) ⟶ dNat := graph fun p => 10 * p.1 + p.2.val

/-- `val = ⦇⁅embed, op⁆⦈ : Decimal → ℕ`, the reading catamorphism. -/
def val : dDec ⟶ dNat := ⦇⁅embed, op⁆⦈

/-- **§6.1 (B&dM p.138)** for the actual valuation: `val°` satisfies the recursive equation
    `val° = (wrap·embed°) ∪ (snoc·(val°×id)·op°)` — a direct instance of `cata_converse_eq`. -/
theorem val_converse_eq :
    val° = embed° ≫ wrap ∪ op° ≫ (val° × 𝟙 dDigit) ≫ snoc :=
  cata_converse_eq embed op

end Freyd.Alg.RelSet.Digits
