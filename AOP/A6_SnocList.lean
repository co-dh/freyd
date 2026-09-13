/-
  Generic SNOC-LIST datatype as an initial algebra in `Rel(Set)` — the reusable engine behind the
  Bird & de Moor concrete case studies (§6.1 digits, §6.4 fast exponentiation, …).

  `SnocList L E` (leaf type `L`, element type `E`) is `wrap L | snoc (SnocList L E, E)`, the
  initial algebra of the polynomial functor `F X = L + (X × E)`.  §6.1's `Decimal` is
  `SnocList Digit⁺ Digit`; §6.4's `Bin` is `SnocList Unit Bit`.  We build the functor as a
  `Relator` (with `PreservesRecip`), the `InitialAlgebra` instance (catamorphism = a structural
  fold defined DIRECTLY from the algebra-relation, no choice), and the §6-style recursive
  equation for the converse of a catamorphism.  Mirrors the ad-hoc §6.1 construction
  (`AOP.A6_1_Digits`), parameterised over `L`, `E`.
-/
module

public import AOP.A6_1_RelSet

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.SL

open Freyd

variable {L E : Type}

/-- The snoc-list datatype: a leaf `wrap l`, extended by `snoc`-ing elements. -/
public inductive SnocList (L E : Type) where
  | wrap : L → SnocList L E
  | snoc : SnocList L E → E → SnocList L E

/-- The object carrying `SnocList L E`. -/
@[expose] public abbrev dSL (L E : Type) : RelSet.{0} := ⟨SnocList L E⟩
/-- The object carrying the leaf type `L`. -/
@[expose] public abbrev dL (L : Type) : RelSet.{0} := ⟨L⟩
/-- The object carrying the element type `E`. -/
public abbrev dE (E : Type) : RelSet.{0} := ⟨E⟩

/-! ## The functor `F X = L + (X × E)` -/

/-- Carrier of `F X`. -/
@[expose] public def Fobj (L E : Type) (C : RelSet.{0}) : RelSet.{0} := ⟨L ⊕ (C.carrier × E)⟩

/-- Action of `F` on a relation: identity on the `L` summand, `R × id` on `X × E`. -/
@[expose] public def Fmap (L E : Type) {C c' : RelSet.{0}} (R : C ⟶ c') : Fobj L E C ⟶ Fobj L E c' :=
  fun u v => match u, v with
    | Sum.inl d, Sum.inl d' => d = d'
    | Sum.inr p, Sum.inr q => R p.1 q.1 ∧ p.2 = q.2
    | _, _ => False

@[simp] theorem Fmap_ll (L E : Type) {C c' : RelSet.{0}} (R : C ⟶ c') (d d' : L) :
    Fmap L E R (Sum.inl d) (Sum.inl d') = (d = d') := rfl
@[simp] theorem Fmap_rr (L E : Type) {C c' : RelSet.{0}} (R : C ⟶ c') (p : C.carrier × E)
    (q : c'.carrier × E) : Fmap L E R (Sum.inr p) (Sum.inr q) = (R p.1 q.1 ∧ p.2 = q.2) := rfl
@[simp] theorem Fmap_lr (L E : Type) {C c' : RelSet.{0}} (R : C ⟶ c') (d : L) (q : c'.carrier × E) :
    Fmap L E R (Sum.inl d) (Sum.inr q) = False := rfl
@[simp] theorem Fmap_rl (L E : Type) {C c' : RelSet.{0}} (R : C ⟶ c') (p : C.carrier × E) (d : L) :
    Fmap L E R (Sum.inr p) (Sum.inl d) = False := rfl

/-- `F` is a relator (monotone functor) on `Rel(Set)`. -/
@[expose] public def F (L E : Type) : Relator RelSet.{0} RelSet.{0} where
  obj := Fobj L E
  map R := Fmap L E R
  map_id C := hom_ext fun u v => by
    cases u <;> cases v <;> simp only [Fmap_ll, Fmap_rr, Fmap_lr, Fmap_rl, id_apply] <;> grind
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
  map_mono {C c' R S} h := le_iff.mpr fun u v => by
    cases u <;> cases v <;> simp only [Fmap_ll, Fmap_rr, Fmap_lr, Fmap_rl] <;>
      first | exact id | exact fun hh => ⟨le_iff.mp h _ _ hh.1, hh.2⟩ | exact False.elim

/-- `F` preserves converse. -/
public theorem F_preservesRecip (L E : Type) : (F L E).PreservesRecip := by
  intro C c' R
  apply hom_ext; intro u v
  cases u <;> cases v <;> simp only [F, Fmap_ll, Fmap_rr, Fmap_lr, Fmap_rl] <;>
    first
      | exact ⟨fun h => h.symm, fun h => h.symm⟩
      | exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩
      | exact Iff.rfl

/-! ## `SnocList L E` is the initial algebra of `F` -/

/-- The constructor map `[wrap, snoc] : F (SnocList L E) → SnocList L E`. -/
@[expose] public def con : (Fobj L E (dSL L E)).carrier → SnocList L E
  | Sum.inl d => SnocList.wrap d
  | Sum.inr p => SnocList.snoc p.1 p.2

/-- The structural fold, defined DIRECTLY from the algebra-relation `f` (no choice). -/
@[expose] public def cataFold {C : RelSet.{0}} (f : Fobj L E C ⟶ C) : SnocList L E → C.carrier → Prop
  | SnocList.wrap d => fun r => f (Sum.inl d) r
  | SnocList.snoc dec dig => fun r => ∃ r', cataFold f dec r' ∧ f (Sum.inr (r', dig)) r

@[simp] public theorem cataFold_wrap {C : RelSet.{0}} (f : Fobj L E C ⟶ C) (d : L)
    (r : C.carrier) : cataFold f (SnocList.wrap d) r = f (Sum.inl d) r := rfl
@[simp] public theorem cataFold_snoc {C : RelSet.{0}} (f : Fobj L E C ⟶ C)
    (dec : SnocList L E) (dig : E) (r : C.carrier) :
    cataFold f (SnocList.snoc dec dig) r = ∃ r', cataFold f dec r' ∧ f (Sum.inr (r', dig)) r := rfl

public theorem cataFold_total {C : RelSet.{0}} (f : Fobj L E C ⟶ C) (hf : Map f) :
    ∀ dec : SnocList L E, ∃ r, cataFold f dec r
  | SnocList.wrap d => entire_total hf.1 (Sum.inl d)
  | SnocList.snoc dec dig => by
    obtain ⟨r', hr'⟩ := cataFold_total f hf dec
    obtain ⟨r, hr⟩ := entire_total hf.1 (Sum.inr (r', dig))
    exact ⟨r, r', hr', hr⟩

public theorem cataFold_functional {C : RelSet.{0}} (f : Fobj L E C ⟶ C) (hf : Map f) :
    ∀ (dec : SnocList L E) (r r' : C.carrier), cataFold f dec r → cataFold f dec r' → r = r'
  | SnocList.wrap d, r, r', h1, h2 => simple_uniq hf.2 h1 h2
  | SnocList.snoc dec dig, r, r', h1, h2 => by
    obtain ⟨s, hs, hfs⟩ := h1
    obtain ⟨s', hs', hfs'⟩ := h2
    have hss : s = s' := cataFold_functional f hf dec s s' hs hs'
    subst hss
    exact simple_uniq hf.2 hfs hfs'

public theorem cataFold_map {C : RelSet.{0}} (f : Fobj L E C ⟶ C) (hf : Map f) :
    Map (a := dSL L E) (b := C) (cataFold f) := by
  refine ⟨?_, ?_⟩
  · show dom (cataFold f) = Cat.id (dSL L E)
    apply hom_ext; intro dec dec'
    refine ⟨fun h => h.1, fun (h : dec = dec') => ⟨h, ?_⟩⟩
    subst h
    obtain ⟨r, hr⟩ := cataFold_total f hf dec
    exact ⟨r, hr, hr⟩
  · refine le_iff.mpr fun r r' h => ?_
    obtain ⟨dec, h1, h2⟩ := h
    exact cataFold_functional f hf dec r r' h1 h2

/-- The initial `F`-algebra structure on `SnocList L E`. -/
@[expose, instance] public def initial (L E : Type) : InitialAlgebra (F L E) where
  t := dSL L E
  α := graph con
  α_map := graph_map con
  cata f _ := cataFold f
  cata_map f hf := cataFold_map f hf
  cata_comm f hf := by
    apply hom_ext; intro u r
    cases u with
    | inl d =>
      constructor
      · intro h; obtain ⟨dec, hdec, hfold⟩ := h
        have hd : dec = SnocList.wrap d := hdec; subst hd
        exact ⟨Sum.inl d, rfl, hfold⟩
      · intro h; obtain ⟨v, hv, hfv⟩ := h
        cases v with
        | inl d' => have hdd : d = d' := hv; subst hdd; exact ⟨SnocList.wrap d, rfl, hfv⟩
        | inr q => exact hv.elim
    | inr p =>
      obtain ⟨pa, pd⟩ := p
      constructor
      · intro h; obtain ⟨dec, hdec, hfold⟩ := h
        have hd : dec = SnocList.snoc pa pd := hdec; subst hd
        obtain ⟨r', hr', hfr'⟩ := hfold
        exact ⟨Sum.inr (r', pd), ⟨hr', rfl⟩, hfr'⟩
      · intro h; obtain ⟨v, hv, hfv⟩ := h
        cases v with
        | inl d' => exact hv.elim
        | inr q =>
          obtain ⟨qa, qd⟩ := q
          obtain ⟨hq1, hq2⟩ := hv
          have hpq : pd = qd := hq2
          refine ⟨SnocList.snoc pa pd, rfl, qa, hq1, ?_⟩
          rw [hpq]; exact hfv
  cata_unique f hf h hmap hcomm := by
    apply hom_ext; intro dec
    induction dec with
    | wrap d =>
      intro r
      have key := congrFun (congrFun hcomm (Sum.inl d)) r
      constructor
      · intro hh
        have hlhs : (graph con ≫ h) (Sum.inl d) r := ⟨SnocList.wrap d, rfl, hh⟩
        rw [key] at hlhs
        obtain ⟨v, hv, hfv⟩ := hlhs
        cases v with
        | inl d' => have hdd : d = d' := hv; subst hdd; exact hfv
        | inr q => exact hv.elim
      · intro hc
        have hrhs : ((F L E).map h ≫ f) (Sum.inl d) r := ⟨Sum.inl d, rfl, hc⟩
        rw [← key] at hrhs
        obtain ⟨dec, hdec, hh⟩ := hrhs
        have hd : dec = SnocList.wrap d := hdec; subst hd; exact hh
    | snoc dec dig ih =>
      intro r
      have key := congrFun (congrFun hcomm (Sum.inr (dec, dig))) r
      constructor
      · intro hh
        have hlhs : (graph con ≫ h) (Sum.inr (dec, dig)) r := ⟨SnocList.snoc dec dig, rfl, hh⟩
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
        have hrhs : ((F L E).map h ≫ f) (Sum.inr (dec, dig)) r :=
          ⟨Sum.inr (r', dig), ⟨(ih r').mpr hr', rfl⟩, hfr'⟩
        rw [← key] at hrhs
        obtain ⟨d', hd', hh⟩ := hrhs
        have hd : d' = SnocList.snoc dec dig := hd'; subst hd; exact hh

/-! ## The recursive equation for the converse of a catamorphism (the §6.1/§6.4 derivation) -/

/-- The catamorphism (fold) of `φ` as a genuine morphism `dSL L E ⟶ c`. -/
@[expose] public def cataR {C : RelSet.{0}} (φ : Fobj L E C ⟶ C) : dSL L E ⟶ C := cataFold φ

/-- The catamorphism computation rule holds for ANY algebra-relation `φ` (not just maps):
    `α ≫ cataFold φ = F(cataFold φ) ≫ φ`.  (The structural proof never uses `Map φ` — it is the
    `Map`-free form of `initial`'s own `cata_comm` field.) -/
public theorem cataFold_comm {C : RelSet.{0}} (φ : Fobj L E C ⟶ C) :
    graph con ≫ cataFold φ = (F L E).map (cataFold φ) ≫ φ := by
  apply hom_ext; intro u r
  cases u with
  | inl d =>
    constructor
    · intro h; obtain ⟨dec, hdec, hfold⟩ := h
      have hd : dec = SnocList.wrap d := hdec; subst hd
      exact ⟨Sum.inl d, rfl, hfold⟩
    · intro h; obtain ⟨v, hv, hfv⟩ := h
      cases v with
      | inl d' => have hdd : d = d' := hv; subst hdd; exact ⟨SnocList.wrap d, rfl, hfv⟩
      | inr q => exact hv.elim
  | inr p =>
    obtain ⟨pa, pd⟩ := p
    constructor
    · intro h; obtain ⟨dec, hdec, hfold⟩ := h
      have hd : dec = SnocList.snoc pa pd := hdec; subst hd
      obtain ⟨r', hr', hfr'⟩ := hfold
      exact ⟨Sum.inr (r', pd), ⟨hr', rfl⟩, hfr'⟩
    · intro h; obtain ⟨v, hv, hfv⟩ := h
      cases v with
      | inl d' => exact hv.elim
      | inr q =>
        obtain ⟨qa, qd⟩ := q
        obtain ⟨hq1, hq2⟩ := hv
        have hpq : pd = qd := hq2
        refine ⟨SnocList.snoc pa pd, rfl, qa, hq1, ?_⟩
        rw [hpq]; exact hfv

/-- The structural fold IS the relational catamorphism `relCata I φ` (Eilenberg–Wright, via
    `cataFold_comm` and the universal property `relCata_UP`).  Lets the abstract catamorphism laws
    (fusion, greedy, …) apply to `cataR` over snoc-lists.  ConsList has the same bridge
    (`A6_ConsList.cataR_eq_relCata`); this is the missing SnocList counterpart. -/
public theorem cataR_eq_relCata {C : RelSet.{0}} (φ : (F L E).obj C ⟶ C) :
    cataR φ = relCata φ :=
  (relCata_UP (initial L E) φ (cataR φ)).mp (cataFold_comm φ)

/-- **Reflection**: the fold of the constructor algebra is the identity, `⦇[nil,snoc]⦈ = 𝟙`.
    What collapses `H = ⦇h⦈·⦇T⦈°` to `⦇T⦈°` whenever the refolding algebra is `α` itself. -/
public theorem cataR_con : cataR (graph (con (L := L) (E := E))) = 𝟙 (dSL L E) := by
  apply hom_ext; intro dec
  induction dec with
  | wrap d => exact fun r => ⟨Eq.symm, Eq.symm⟩
  | snoc x a ih =>
    intro r
    constructor
    · rintro ⟨r', hr', hcon⟩
      obtain rfl : x = r' := (ih r').mp hr'
      exact (hcon : r = SnocList.snoc x a).symm
    · intro (h : SnocList.snoc x a = r)
      exact ⟨x, (ih x).mpr rfl, h.symm⟩

/-- The `wrap`-component of an algebra `φ = [g, h]`. -/
def algWrap {C : RelSet.{0}} (φ : Fobj L E C ⟶ C) : dL L ⟶ C :=
  fun d r => φ (Sum.inl d) r
/-- The `snoc`-component of an algebra `φ = [g, h]`. -/
def algSnoc {C : RelSet.{0}} (φ : Fobj L E C ⟶ C) :
    (⟨C.carrier × E⟩ : RelSet.{0}) ⟶ C := fun p r => φ (Sum.inr p) r

/-- The constructor `wrap` as a relation. -/
def wrapR : dL L ⟶ dSL L E := graph SnocList.wrap
/-- The constructor `snoc` as a relation. -/
@[expose] public def snocR : (⟨SnocList L E × E⟩ : RelSet.{0}) ⟶ dSL L E :=
  graph (fun p => SnocList.snoc p.1 p.2)

/-- The empty list `nil : 𝟏⟼[E]` — `wrap` at the ONE label, written as the constant map it is
    there, because that is what the picture draws: a box with no input port. -/
@[expose] public def nilR : dL Unit ⟶ dSL Unit E := graph fun _ => SnocList.wrap ()

/-- **The §6.1/§6.4 recursive equation** (B&dM p.138/145): the converse of a catamorphism over a
    snoc-list datatype satisfies `val° = (wrap·g°) ∪ (snoc·(val°×id)·h°)` (mirrored to diagram
    order), for any algebra `φ = [g, h]`. -/
theorem cata_converse_eq {C : RelSet.{0}} (φ : Fobj L E C ⟶ C) :
    (cataR φ)° = (algWrap φ)° ≫ wrapR
      ∪ (algSnoc φ)° ≫ rprodMap (cataR φ)° (Cat.id (dE E)) ≫ snocR := by
  apply hom_ext; intro r dec
  cases dec with
  | wrap d =>
    constructor
    · intro h
      exact Or.inl ⟨d, h, rfl⟩
    · intro h
      cases h with
      | inl h =>
        obtain ⟨e, he, hde⟩ := h
        have hd : d = e := SnocList.wrap.inj hde
        rw [hd]; exact he
      | inr h =>
        obtain ⟨p, hp, q, hq, hsnoc⟩ := h
        obtain ⟨qa, qd⟩ := q
        have hc : SnocList.wrap d = SnocList.snoc qa qd := hsnoc
        nomatch hc
  | snoc dec dig =>
    constructor
    · intro h
      obtain ⟨r', hr', hφ⟩ := h
      exact Or.inr ⟨(r', dig), hφ, (dec, dig), ⟨hr', rfl⟩, rfl⟩
    · intro h
      cases h with
      | inl h =>
        obtain ⟨e, he, hde⟩ := h
        have hc : SnocList.snoc dec dig = SnocList.wrap e := hde
        nomatch hc
      | inr h =>
        obtain ⟨p, hp, q, hq, hsnoc⟩ := h
        obtain ⟨pa, pd⟩ := p
        obtain ⟨qa, qd⟩ := q
        obtain ⟨hcata, hpq⟩ := hq
        obtain ⟨hda, hdd⟩ := SnocList.snoc.inj hsnoc
        refine ⟨pa, ?_, ?_⟩
        · rw [hda]; exact hcata
        · have hpd : pd = dig := hpq.trans hdd.symm
          rw [hpd] at hp; exact hp

/-! ## The datatype as a relator: `list(R)`

  A snoc list is a datatype in its ELEMENT type, so it is the object part of a relator — the note's
  lane `list`, the same wire `AOP.A5_6_ListCombinators.listRelator` is for the cons list.  The LEAF
  type is the datatype's other parameter and stays fixed along the lane, exactly as `unexpandDSL`
  already has it: `[E]` whatever the leaf. -/

/-- Elementwise lifting on snoc lists: the same shape, the same leaf, each element related by `R`. -/
@[expose] public def slistP {A B : Type} (R : dE A ⟶ dE B) : SnocList L A → SnocList L B → Prop
  | SnocList.wrap l, SnocList.wrap l' => l = l'
  | SnocList.wrap _, SnocList.snoc _ _ => False
  | SnocList.snoc _ _, SnocList.wrap _ => False
  | SnocList.snoc x a, SnocList.snoc y b => slistP R x y ∧ R a b

/-- The relator's action `list(R) : [A]⟶[B]`. -/
@[expose] public def slist {A B : Type} (R : dE A ⟶ dE B) : dSL L A ⟶ dSL L B := slistP R

public theorem slistP_id {A : Type} : ∀ x y : SnocList L A, slistP (𝟙 (dE A)) x y ↔ x = y
  | SnocList.wrap l, SnocList.wrap l' =>
      ⟨fun h => by rw [show l = l' from h], fun h => by cases h; rfl⟩
  | SnocList.wrap _, SnocList.snoc _ _ => ⟨False.elim, fun h => nomatch h⟩
  | SnocList.snoc _ _, SnocList.wrap _ => ⟨False.elim, fun h => nomatch h⟩
  | SnocList.snoc x a, SnocList.snoc y b =>
      ⟨fun h => by rw [(slistP_id x y).mp h.1, show a = b from h.2],
       fun h => by cases h; exact ⟨(slistP_id x x).mpr rfl, rfl⟩⟩

/-- `list(𝟙) = 𝟙`. -/
public theorem slist_id {A : Type} : slist (L := L) (𝟙 (dE A)) = 𝟙 (dSL L A) := hom_ext slistP_id

public theorem slistP_comp {A B C : Type} (R : dE A ⟶ dE B) (S : dE B ⟶ dE C) :
    ∀ (x : SnocList L A) (z : SnocList L C),
      slistP (R ≫ S) x z ↔ ∃ y, slistP R x y ∧ slistP S y z
  | SnocList.wrap l, SnocList.wrap n =>
      ⟨fun h => ⟨SnocList.wrap l, rfl, h⟩,
       fun ⟨y, h1, h2⟩ => by cases y with
        | wrap m => exact (h1 : l = m).trans h2
        | snoc _ _ => exact h1.elim⟩
  | SnocList.wrap _, SnocList.snoc _ _ =>
      ⟨False.elim, fun ⟨y, h1, h2⟩ => by cases y with
        | wrap _ => exact h2
        | snoc _ _ => exact h1⟩
  | SnocList.snoc _ _, SnocList.wrap _ =>
      ⟨False.elim, fun ⟨y, h1, h2⟩ => by cases y with
        | wrap _ => exact h1
        | snoc _ _ => exact h2⟩
  | SnocList.snoc x a, SnocList.snoc z c => by
      constructor
      · rintro ⟨hxz, ⟨b, hR, hS⟩⟩
        obtain ⟨y, hy1, hy2⟩ := (slistP_comp R S x z).mp hxz
        exact ⟨SnocList.snoc y b, ⟨hy1, hR⟩, hy2, hS⟩
      · rintro ⟨y, h1, h2⟩
        cases y with
        | wrap _ => exact h1.elim
        | snoc ys b =>
            exact ⟨(slistP_comp R S x z).mpr ⟨ys, h1.1, h2.1⟩, b, h1.2, h2.2⟩

/-- `list(RS) = list(R) list(S)`. -/
public theorem slist_comp {A B C : Type} (R : dE A ⟶ dE B) (S : dE B ⟶ dE C) :
    slist (L := L) (R ≫ S) = slist R ≫ slist S := hom_ext (slistP_comp R S)

public theorem slistP_mono {A B : Type} {R S : dE A ⟶ dE B} (h : ∀ a b, R a b → S a b) :
    ∀ (x : SnocList L A) (y : SnocList L B), slistP R x y → slistP S x y
  | SnocList.wrap _, SnocList.wrap _, hxy => hxy
  | SnocList.wrap _, SnocList.snoc _ _, hxy => hxy.elim
  | SnocList.snoc _ _, SnocList.wrap _, hxy => hxy.elim
  | SnocList.snoc x a, SnocList.snoc y b, hxy =>
      ⟨slistP_mono h x y hxy.1, h a b hxy.2⟩

/-- `R ⊑ S ⟹ list(R) ⊑ list(S)` — `list` is monotonic. -/
public theorem slist_mono {A B : Type} {R S : dE A ⟶ dE B} (h : R ⊑ S) :
    slist (L := L) R ⊑ slist S := le_iff.mpr (slistP_mono (le_iff.mp h))

/-- `list` BUNDLED as a relator, at one leaf type: the note's lane over `[Job]`, `[Char]` and every
    other snoc list, where the object alone leaves the reader a point nothing peels. -/
@[expose] public def snocRelator (L : Type) : Relator RelSet.{0} RelSet.{0} where
  obj a := dSL L a.carrier
  map R := slist R
  map_id _ := slist_id
  map_comp R S := slist_comp R S
  map_mono h := slist_mono h

-- printing-only unexpanders: the note's spelling, the same ones `AOP.A6_ConsList` gives the cons
-- list.  A snoc list IS a list — the note writes `[Char]`, `[Code]`, `[Job]` — and which leaf type
-- it is built over is the datatype's parameter, not part of the object's name.  On the TYPE FORMER,
-- so every instance prints alike; they change no statement and no `stmt_key`.
open Lean PrettyPrinter in
@[app_unexpander SnocList] public meta def unexpandSnocListObj : Unexpander
  | `($_ $_ $E) => `([$E])
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander dSL] public meta def unexpandDSL : Unexpander
  | `($_ $_ $E) => `([$E])
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander F] public meta def unexpandF : Unexpander
  | `($_ $_ $_) => `($(mkIdent `F))
  | _ => throw ()

-- The leaf at the EMPTY leaf type is the note's `nil`, and at any other leaf type it is a leaf
-- carrying a value: the unit argument is matched, not the constructor alone.
open Lean PrettyPrinter in
@[app_unexpander SnocList.wrap] public meta def unexpandNil : Unexpander
  | `($_ ()) => `($(mkIdent `nil))
  | `($_ $x) => `($(mkIdent `wrap) $x)
  | _ => throw ()

-- The constructor as an arrow wears the note's own word, as the cons list's `cons` does.
open Lean PrettyPrinter in
@[app_unexpander snocR] public meta def unexpandSnocR : Unexpander
  | _ => `($(mkIdent `snoc))

-- The structural fold wears the note's banana, for the reason `AOP.A6_ConsList.cataR`'s does: a
-- picture says which arrow it draws by the algebra in the brackets.
open Lean PrettyPrinter in
@[app_unexpander cataR] public meta def unexpandCataR : Unexpander
  | `($_ $φ) => `(⦇$φ⦈)
  | _ => throw ()

end Freyd.Alg.RelSet.SL
