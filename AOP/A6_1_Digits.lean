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
  The headline is proved BY THE BOOK'S OWN EQUATIONAL DERIVATION (p.138): a four-step calc —
  {catamorphisms, α = [wrap,snoc]}, {coproduct}, {converse of a composite}, {converse of a
  product} — over the `junc`/`sumMap` calculus of `AOP.A5_3`, not by pointwise cases.
  Everything is constructive (the fold is defined FROM the algebra-relation, no choice).
-/
module

public import AOP.A6_1_RelSet
public import AOP.A5_3
import AOP.CalcSteps

namespace Freyd.Alg.RelSet.Digits

open Freyd

/- Bird and de Moor's product-bifunctor notation.  Lean can overload the same `×` token used for
   products of types because here the operands elaborate as relations. -/
local infixr:70 " × " => rprodMap

/-- The canonical coproduct action of two relations in `Rel(Set)`.  It hides the chosen
    `Sum` coproducts so calculations can use Bird and de Moor's `R + S` notation. -/
@[expose] public def rsumMap {A a' B b' : RelSet.{0}} (R : A ⟶ a') (S : B ⟶ b') :
    (⟨A.carrier ⊕ B.carrier⟩ : RelSet.{0}) ⟶ ⟨a'.carrier ⊕ b'.carrier⟩ :=
  sumMap (sumCop A B) (sumCop a' b') R S

/-- Bird and de Moor's coproduct-bifunctor `+` on relations. -/
@[expose] public instance {A a' B b' : RelSet.{0}} :
    HAdd (A ⟶ a') (B ⟶ b')
      ((⟨A.carrier ⊕ B.carrier⟩ : RelSet.{0}) ⟶ ⟨a'.carrier ⊕ b'.carrier⟩) where
  hAdd := rsumMap

/-! ## Datatypes and their objects in `Rel(Set)` (universe 0) -/

/-- The ten decimal digits `{0,…,9}`. -/
@[expose] public def Digit : Type := Fin 10
/-- The nine nonzero digits `{1,…,9}`. -/
@[expose] public def DigitP : Type := { d : Fin 10 // d.val ≠ 0 }
-- B&dM's name has a superscript, which no Lean identifier can carry; a notation can.
notation "Digit⁺" => Freyd.Alg.RelSet.Digits.DigitP

/-- Decimal representations: `wrap` a leading nonzero digit, then `snoc` further digits. -/
public inductive Decimal where
  | wrap : DigitP → Decimal
  | snoc : Decimal → Digit → Decimal

/-- Object of `Rel(Set)` carrying `Digit`.  `abbrev` so `.carrier` reduces to `Digit`. -/
@[expose] public abbrev dDigit : RelSet.{0} := ⟨Digit⟩
/-- Object of `Rel(Set)` carrying `Digit⁺`. -/
@[expose] public abbrev dDigitP : RelSet.{0} := ⟨DigitP⟩
/-- Object of `Rel(Set)` carrying `Decimal`. -/
@[expose] public abbrev dDec : RelSet.{0} := ⟨Decimal⟩

/-! ## The functor `F A = Digit⁺ + (A × Digit)`, the composite of `−×Digit` and `Digit⁺+−`

  Book p.138's `F` is two unary relators applied in turn: first `−×Digit`, then `Digit⁺+−`.  Stated
  as their `Relator.comp`, so the string diagram draws `F` as the two wires it is. -/

/-- Carrier of `F A`.  The first summand is spelled `dDigitP.carrier` (not `DigitP`) so that
    unifying an `⁅g, h⁆`-hole against `Fobj c` solves the coproduct object to the CONSTANT
    `dDigitP` — the same spelling standalone `⁅g, h⁆` gets — keeping `rw` steps syntactic. -/
@[expose] public def Fobj (C : RelSet.{0}) : RelSet.{0} := ⟨dDigitP.carrier ⊕ (C.carrier × Digit)⟩

/-- The relator `−×Digit`: `C ↦ C×Digit`, `R ↦ R×𝟙`. -/
@[expose] public def timesDigit : Relator RelSet.{0} RelSet.{0} where
  obj C := ⟨C.carrier × Digit⟩
  map R := R × 𝟙 dDigit
  map_id C := rprodMap_id C dDigit
  map_comp R S := by rw [rprodMap_comp]; exact congrArg (rprodMap (R ≫ S)) (Cat.id_comp (𝟙 dDigit)).symm
  map_mono h := rprodMap_mono h (le_iff.mpr fun _ _ e => e)
notation "−×Digit" => Freyd.Alg.RelSet.Digits.timesDigit

/-- The relator `Digit⁺+−`: `C ↦ Digit⁺+C`, `R ↦ 𝟙+R`. -/
@[expose] public def plusDigitP : Relator RelSet.{0} RelSet.{0} where
  obj C := ⟨dDigitP.carrier ⊕ C.carrier⟩
  map R := 𝟙 dDigitP + R
  map_id C := sumMap_id (sumCop dDigitP C)
  map_comp R S := by dsimp only [HAdd.hAdd, rsumMap]; rw [sumMap_comp, Cat.id_comp]
  map_mono h := sumMap_mono _ _ (le_iff.mpr fun _ _ e => e) h
notation "Digit⁺+−" => Freyd.Alg.RelSet.Digits.plusDigitP

/-- `F = (−×Digit)(Digit⁺+−)` in diagram order, so `F(R)` is `𝟙+(R×𝟙)`.  A notation, not a
    constant, so every statement carries the `Relator.comp` the exporter splits into two lanes. -/
local notation:max "F(" R ")" => Freyd.Functor.map (Relator.toFunctor (Relator.comp timesDigit plusDigitP)) R

/-- Pointwise action of `F` on a relation: identity on `Digit⁺`, `R × id` on `A × Digit`. -/
@[expose] public def Fmap {C c' : RelSet.{0}} (R : C ⟶ c') : Fobj C ⟶ Fobj c' :=
  fun u v => match u, v with
    | Sum.inl d, Sum.inl d' => d = d'
    | Sum.inr p, Sum.inr q => R p.1 q.1 ∧ p.2 = q.2
    | _, _ => False

@[simp] theorem Fmap_ll {C c' : RelSet.{0}} (R : C ⟶ c') (d d' : DigitP) :
    Fmap R (Sum.inl d) (Sum.inl d') = (d = d') := rfl
@[simp] theorem Fmap_rr {C c' : RelSet.{0}} (R : C ⟶ c') (p : C.carrier × Digit)
    (q : c'.carrier × Digit) :
    Fmap R (Sum.inr p) (Sum.inr q) = (R p.1 q.1 ∧ p.2 = q.2) := rfl
@[simp] theorem Fmap_lr {C c' : RelSet.{0}} (R : C ⟶ c') (d : DigitP) (q : c'.carrier × Digit) :
    Fmap R (Sum.inl d) (Sum.inr q) = False := rfl
@[simp] theorem Fmap_rl {C c' : RelSet.{0}} (R : C ⟶ c') (p : C.carrier × Digit) (d : DigitP) :
    Fmap R (Sum.inr p) (Sum.inl d) = False := rfl

/-- `F`'s action in the coproduct calculus: `F(R) = 𝟙 + (R × 𝟙)` as a `sumMap` over the
    concrete coproducts `sumCop` — the raw material of the "{definition of F}" step. -/
public theorem Fmap_eq_sumMap {C c' : RelSet.{0}} (R : C ⟶ c') :
    F(R) = sumMap (sumCop dDigitP ⟨C.carrier × Digit⟩) (sumCop dDigitP ⟨c'.carrier × Digit⟩)
      (𝟙 dDigitP) (R × 𝟙 dDigit) := rfl

/-- The composite's action is the pointwise `Fmap` the initial-algebra proofs case-split on. -/
public theorem Fmap_eq {C c' : RelSet.{0}} (R : C ⟶ c') : F(R) = Fmap R := by
  rw [Fmap_eq_sumMap]
  apply hom_ext; intro u v
  constructor
  · intro h
    cases h with
    | inl h => obtain ⟨d, h1, e, h2, h3⟩ := h; subst h1; subst h3; exact h2
    | inr h => obtain ⟨p, h1, q, h2, h3⟩ := h; subst h1; subst h3; exact h2
  · intro h
    cases u with
    | inl d => cases v with
      | inl d' => exact Or.inl ⟨d, rfl, d', h, rfl⟩
      | inr q => exact h.elim
    | inr p => cases v with
      | inl d' => exact h.elim
      | inr q => exact Or.inr ⟨p, rfl, q, h, rfl⟩

/-! ## `Decimal` is the initial algebra of `F` -/

/-- The constructor map `⁅wrap, snoc⁆ : F Decimal → Decimal`. -/
public def con : ((Relator.comp timesDigit plusDigitP).obj dDec).carrier → Decimal
  | Sum.inl d => Decimal.wrap d
  | Sum.inr p => Decimal.snoc p.1 p.2

/-- The structural fold of a decimal through an algebra `f`, defined DIRECTLY from the
    algebra-RELATION `f` (so no choice is needed to turn `f` into a function). -/
@[expose] public def cataFold {C : RelSet.{0}} (f : Fobj C ⟶ C) : Decimal → C.carrier → Prop
  | Decimal.wrap d => fun r => f (Sum.inl d) r
  | Decimal.snoc dec dig => fun r => ∃ r', cataFold f dec r' ∧ f (Sum.inr (r', dig)) r

@[simp] theorem cataFold_wrap {C : RelSet.{0}} (f : Fobj C ⟶ C) (d : DigitP) (r : C.carrier) :
    cataFold f (Decimal.wrap d) r = f (Sum.inl d) r := rfl
@[simp] theorem cataFold_snoc {C : RelSet.{0}} (f : Fobj C ⟶ C) (dec : Decimal) (dig : Digit)
    (r : C.carrier) :
    cataFold f (Decimal.snoc dec dig) r = ∃ r', cataFold f dec r' ∧ f (Sum.inr (r', dig)) r := rfl

/-- Every decimal folds to at least one value: the fold is entire when `f` is. -/
theorem cataFold_total {C : RelSet.{0}} (f : Fobj C ⟶ C) (hf : Map f) :
    ∀ dec : Decimal, ∃ r, cataFold f dec r
  | Decimal.wrap d => entire_total hf.1 (Sum.inl d)
  | Decimal.snoc dec dig => by
    obtain ⟨r', hr'⟩ := cataFold_total f hf dec
    obtain ⟨r, hr⟩ := entire_total hf.1 (Sum.inr (r', dig))
    exact ⟨r, r', hr', hr⟩

/-- The fold is single-valued: it is simple when `f` is. -/
theorem cataFold_functional {C : RelSet.{0}} (f : Fobj C ⟶ C) (hf : Map f) :
    ∀ (dec : Decimal) (r r' : C.carrier), cataFold f dec r → cataFold f dec r' → r = r'
  | Decimal.wrap d, r, r', h1, h2 => simple_uniq hf.2 h1 h2
  | Decimal.snoc dec dig, r, r', h1, h2 => by
    obtain ⟨s, hs, hfs⟩ := h1
    obtain ⟨s', hs', hfs'⟩ := h2
    have hss : s = s' := cataFold_functional f hf dec s s' hs hs'
    subst hss
    exact simple_uniq hf.2 hfs hfs'

theorem cataFold_map {C : RelSet.{0}} (f : Fobj C ⟶ C) (hf : Map f) :
    Map (a := dDec) (b := C) (cataFold f) := by
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
@[expose] public def cataR {C : RelSet.{0}} (φ : Fobj C ⟶ C) : dDec ⟶ C := cataFold φ

/-- The fold square `α ≫ ⦇φ⦈ = F⦇φ⦈ ≫ φ` for EVERY algebra `φ` (not only maps) — the
    homomorphism equation, hoisted out of `decInitial` so the §6.1 derivation can cite it. -/
public theorem cata_square {C : RelSet.{0}} (φ : Fobj C ⟶ C) :
    graph con ≫ cataR φ = F(cataR φ) ≫ φ := by
  rw [Fmap_eq]
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
def decInitial : InitialAlgebra (Relator.comp timesDigit plusDigitP) where
  t := dDec
  α := graph con
  α_map := graph_map con
  cata f _ := cataFold f
  cata_map f hf := cataFold_map f hf
  cata_comm f _ := cata_square f
  cata_unique f hf h hmap hcomm := by
    rw [Fmap_eq] at hcomm
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
        have hrhs : (Fmap h ≫ f) (Sum.inl d) r := ⟨Sum.inl d, rfl, hc⟩
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
        have hrhs : (Fmap h ≫ f) (Sum.inr (dec, dig)) r :=
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
public def wrap : dDigitP ⟶ dDec := graph Decimal.wrap
/-- The constructor `snoc` as a relation (the book's `snoc : Decimal × Digit → Decimal`). -/
public def snoc : timesDigit.obj dDec ⟶ dDec := graph (fun p => Decimal.snoc p.1 p.2)

/-! Supporting laws for the derivation, each a single ingredient of one p.138 step. -/

/-- `α` is a cover: `α° ≫ α = 1` (`con` is surjective — every decimal is a `wrap` or a `snoc`).
    Cancels the constructor in the fold square, giving the fixed-point form below. -/
public theorem con_recip_con : (graph con)° ≫ graph con = 𝟙 dDec := by
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
public theorem cata_fix {C : RelSet.{0}} (φ : Fobj C ⟶ C) :
    cataR φ = (graph con)° ≫ (F(cataR φ) ≫ φ) :=
  calc cataR φ
      = 𝟙 dDec ≫ cataR φ := (Cat.id_comp _).symm
    _ = ((graph con)° ≫ graph con) ≫ cataR φ := by rw [con_recip_con]
    _ = (graph con)° ≫ (graph con ≫ cataR φ) := Cat.assoc _ _ _
    _ = (graph con)° ≫ (F(cataR φ) ≫ φ) := by rw [cata_square]

/-- The constructor map as a junc: `α = ⁅wrap, snoc⁆` — the book's presentation of `α`. -/
public theorem con_eq_junc : graph con = ⁅wrap, snoc⁆ := by
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
theorem alg_eq_junc {C : RelSet.{0}} (φ : Fobj C ⟶ C) :
    ∃ (g : dDigitP ⟶ C) (h : timesDigit.obj C ⟶ C), φ = ⁅g, h⁆ := by
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

/-- The book's {catamorphisms} step with `α = [wrap,snoc]`: `⦇φ⦈ = [wrap,snoc]°F(⦇φ⦈)φ`. -/
public theorem cata_fix_junc {C : RelSet.{0}} (φ : Fobj C ⟶ C) :
    cataR φ = ⁅wrap, snoc⁆° ≫ (F(cataR φ) ≫ φ) :=
  (cata_fix φ).trans (by rw [con_eq_junc])

/-- The relator `−×Digit` preserves converse: `(R×𝟙)° = R°×𝟙`. -/
public theorem timesDigit_recip {C c' : RelSet.{0}} (R : C ⟶ c') :
    (timesDigit.map R)° = timesDigit.map R° :=
  (rprodMap_recip R (𝟙 dDigit)).trans (congrArg (rprodMap _) recip_id)

/-- **§6.1 (B&dM p.138)**: the converse of a catamorphism satisfies the recursive equation
    `val° = (wrap·embed°) ∪ (snoc·(val°×id)·op°)` (mirrored), for any algebra `⁅g, h⁆`.
    Instantiating `g := embed`, `h := op` gives the book's `val°` recursion verbatim.

    The proof is the book's derivation, one law per step. -/
public theorem cata_converse_eq {C : RelSet.{0}} (g : dDigitP ⟶ C)
    (h : timesDigit.obj C ⟶ C) :
    (cataR ⁅g, h⁆)° = g° ≫ wrap
      ∪ h° ≫ timesDigit.map (cataR ⁅g, h⁆)° ≫ snoc :=
  calc (cataR ⁅g, h⁆)°
        = (⁅wrap, snoc⁆° ≫ (F(cataR ⁅g, h⁆) ≫ ⁅g, h⁆))° := congrArg _ (cata_fix_junc _)
    -- `F(R)` is `𝟙+(R×𝟙)` by definition, so the `show` spells it as the `sumMap` the law reads.
    _ = (⁅wrap, snoc⁆° ≫ ⁅g, timesDigit.map (cataR ⁅g, h⁆) ≫ h⁆)° := by
        show (⁅wrap, snoc⁆° ≫ (sumMap (sumCop dDigitP (timesDigit.obj dDec))
          (sumCop dDigitP (timesDigit.obj C)) (𝟙 dDigitP) (timesDigit.map (cataR ⁅g, h⁆))
          ≫ ⁅g, h⁆))° = _
        rw [sumMap_junc, Cat.id_comp]
    _ = ((wrap° ≫ g) ∪ (snoc° ≫ (timesDigit.map (cataR ⁅g, h⁆) ≫ h)))° := by
        rw [junc_recip_junc]
    _ = (snoc° ≫ (timesDigit.map (cataR ⁅g, h⁆) ≫ h))° ∪ (wrap° ≫ g)° := by rw [recip_union]
    _ = (wrap° ≫ g)° ∪ (snoc° ≫ (timesDigit.map (cataR ⁅g, h⁆) ≫ h))° :=
        DistributiveAllegory.union_comm _ _
    _ = g° ≫ wrap ∪ (timesDigit.map (cataR ⁅g, h⁆) ≫ h)° ≫ snoc := by
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, Allegory.recip_recip]
    _ = g° ≫ wrap ∪ h° ≫ (timesDigit.map (cataR ⁅g, h⁆))° ≫ snoc := by
        rw [Allegory.recip_comp, Cat.assoc]
    _ = g° ≫ wrap ∪ h° ≫ timesDigit.map (cataR ⁅g, h⁆)° ≫ snoc := by rw [timesDigit_recip]

calc_steps cata_converse_eq

/-! ## The `val`uation catamorphism and its recursion (book p.138)

  `embed d = d` includes a nonzero digit as a number; `op (n, d) = 10·n + d`.  `val = ⦇⁅embed,
  op⁆⦈ : Decimal → ℕ` reads a decimal representation as a number.  (The book works in `ℕ⁺`; the
  positivity of the result is a side condition irrelevant to the recursion, so we land in `ℕ`.) -/

/-- The codomain object: the natural numbers. -/
@[expose] public abbrev dNat : RelSet.{0} := ⟨Nat⟩

/-- The book's `embed : Digit⁺ → ℕ` — include a nonzero digit as a number. -/
public def embed : dDigitP ⟶ dNat := graph fun d => d.1.val
/-- The book's `op (n, d) = 10·n + d` — append a digit to a number. -/
public def op : timesDigit.obj dNat ⟶ dNat := graph fun p => 10 * p.1 + p.2.val

/-- `val = ⦇⁅embed, op⁆⦈ : Decimal → ℕ`, the reading catamorphism. -/
public def val : dDec ⟶ dNat := cataR ⁅embed, op⁆

/-- **§6.1 (B&dM p.138)** for the actual valuation: `val°` satisfies the recursive equation
    `val° = (wrap·embed°) ∪ (snoc·(val°×id)·op°)` — a direct instance of `cata_converse_eq`. -/
public theorem val_converse_eq :
    val° = embed° ≫ wrap ∪ op° ≫ timesDigit.map val° ≫ snoc :=
  cata_converse_eq embed op

/-! ## B&dM p.139: the two converses in `val°`'s recursion

  `op(n,d)=m ≡ n=m div 10 ∧ d=m mod 10`; with the book's `n ∈ ℕ⁺`, `op°` is defined exactly on
  `m ≥ 10`, and `embed°` exactly on `0 < m < 10` — the two ranges are disjoint, so the join in
  `val°`'s recursion is a conditional. -/

/-- **B&dM p.139**: `op(n,d)=m ≡ n=m div 10 ∧ d=m mod 10`. -/
public theorem op_recip_iff (m : Nat) (p : Nat × Digit) :
    (op°) m p ↔ p.1 = m / 10 ∧ p.2.val = m % 10 := by
  rw [recip_apply, op]
  show m = 10 * p.1 + p.2.val ↔ _
  have := p.2.isLt
  omega

/-- **B&dM p.139**: `op°` at a positive quotient is defined iff `m ≥ 10`. -/
public theorem op_recip_defined (m : Nat) : (∃ p : Nat × Digit, 0 < p.1 ∧ (op°) m p) ↔ 10 ≤ m := by
  constructor
  · rintro ⟨p, hp, h⟩
    have := (op_recip_iff m p).mp h
    omega
  · intro h
    exact ⟨(m / 10, ⟨m % 10, Nat.mod_lt m (by decide)⟩), by omega,
      (op_recip_iff m _).mpr ⟨rfl, rfl⟩⟩

/-- **B&dM p.139**: `embed°` is defined iff `0 < m < 10`. -/
public theorem embed_recip_defined (m : Nat) : (∃ d : DigitP, (embed°) m d) ↔ 0 < m ∧ m < 10 := by
  constructor
  · rintro ⟨d, h⟩
    have h' : m = d.1.val := by rw [recip_apply, embed] at h; exact h
    have := d.1.isLt
    have := d.2
    omega
  · intro h
    exact ⟨⟨⟨m, h.2⟩, by show m ≠ 0; omega⟩, by rw [recip_apply, embed]; show m = m; rfl⟩

end Freyd.Alg.RelSet.Digits
