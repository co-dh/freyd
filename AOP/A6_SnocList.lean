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
abbrev dE (E : Type) : RelSet.{0} := ⟨E⟩

/-! ## The functor `F X = L + (X × E)` -/

/-- Carrier of `F X`. -/
@[expose] public def Fobj (L E : Type) (c : RelSet.{0}) : RelSet.{0} := ⟨L ⊕ (c.carrier × E)⟩

/-- Action of `F` on a relation: identity on the `L` summand, `R × id` on `X × E`. -/
@[expose] public def Fmap (L E : Type) {c c' : RelSet.{0}} (R : c ⟶ c') : Fobj L E c ⟶ Fobj L E c' :=
  fun u v => match u, v with
    | Sum.inl d, Sum.inl d' => d = d'
    | Sum.inr p, Sum.inr q => R p.1 q.1 ∧ p.2 = q.2
    | _, _ => False

@[simp] theorem Fmap_ll (L E : Type) {c c' : RelSet.{0}} (R : c ⟶ c') (d d' : L) :
    Fmap L E R (Sum.inl d) (Sum.inl d') = (d = d') := rfl
@[simp] theorem Fmap_rr (L E : Type) {c c' : RelSet.{0}} (R : c ⟶ c') (p : c.carrier × E)
    (q : c'.carrier × E) : Fmap L E R (Sum.inr p) (Sum.inr q) = (R p.1 q.1 ∧ p.2 = q.2) := rfl
@[simp] theorem Fmap_lr (L E : Type) {c c' : RelSet.{0}} (R : c ⟶ c') (d : L) (q : c'.carrier × E) :
    Fmap L E R (Sum.inl d) (Sum.inr q) = False := rfl
@[simp] theorem Fmap_rl (L E : Type) {c c' : RelSet.{0}} (R : c ⟶ c') (p : c.carrier × E) (d : L) :
    Fmap L E R (Sum.inr p) (Sum.inl d) = False := rfl

/-- `F` is a relator (monotone functor) on `Rel(Set)`. -/
@[expose] public def F (L E : Type) : Relator RelSet.{0} RelSet.{0} where
  obj := Fobj L E
  map R := Fmap L E R
  map_id c := hom_ext fun u v => by
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
  map_mono {c c' R S} h := le_iff.mpr fun u v => by
    cases u <;> cases v <;> simp only [Fmap_ll, Fmap_rr, Fmap_lr, Fmap_rl] <;>
      first | exact id | exact fun hh => ⟨le_iff.mp h _ _ hh.1, hh.2⟩ | exact False.elim

/-- `F` preserves converse. -/
public theorem F_preservesRecip (L E : Type) : (F L E).PreservesRecip := by
  intro c c' R
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
@[expose] public def cataFold {c : RelSet.{0}} (f : Fobj L E c ⟶ c) : SnocList L E → c.carrier → Prop
  | SnocList.wrap d => fun r => f (Sum.inl d) r
  | SnocList.snoc dec dig => fun r => ∃ r', cataFold f dec r' ∧ f (Sum.inr (r', dig)) r

@[simp] public theorem cataFold_wrap {c : RelSet.{0}} (f : Fobj L E c ⟶ c) (d : L)
    (r : c.carrier) : cataFold f (SnocList.wrap d) r = f (Sum.inl d) r := rfl
@[simp] public theorem cataFold_snoc {c : RelSet.{0}} (f : Fobj L E c ⟶ c)
    (dec : SnocList L E) (dig : E) (r : c.carrier) :
    cataFold f (SnocList.snoc dec dig) r = ∃ r', cataFold f dec r' ∧ f (Sum.inr (r', dig)) r := rfl

public theorem cataFold_total {c : RelSet.{0}} (f : Fobj L E c ⟶ c) (hf : Map f) :
    ∀ dec : SnocList L E, ∃ r, cataFold f dec r
  | SnocList.wrap d => entire_total hf.1 (Sum.inl d)
  | SnocList.snoc dec dig => by
    obtain ⟨r', hr'⟩ := cataFold_total f hf dec
    obtain ⟨r, hr⟩ := entire_total hf.1 (Sum.inr (r', dig))
    exact ⟨r, r', hr', hr⟩

public theorem cataFold_functional {c : RelSet.{0}} (f : Fobj L E c ⟶ c) (hf : Map f) :
    ∀ (dec : SnocList L E) (r r' : c.carrier), cataFold f dec r → cataFold f dec r' → r = r'
  | SnocList.wrap d, r, r', h1, h2 => simple_uniq hf.2 h1 h2
  | SnocList.snoc dec dig, r, r', h1, h2 => by
    obtain ⟨s, hs, hfs⟩ := h1
    obtain ⟨s', hs', hfs'⟩ := h2
    have hss : s = s' := cataFold_functional f hf dec s s' hs hs'
    subst hss
    exact simple_uniq hf.2 hfs hfs'

public theorem cataFold_map {c : RelSet.{0}} (f : Fobj L E c ⟶ c) (hf : Map f) :
    Map (a := dSL L E) (b := c) (cataFold f) := by
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
@[expose] public def initial (L E : Type) : InitialAlgebra (F L E) where
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
@[expose] public def cataR {c : RelSet.{0}} (φ : Fobj L E c ⟶ c) : dSL L E ⟶ c := cataFold φ

/-- The book's banana brackets for the catamorphism — one global overload per datatype engine,
    disambiguated by the algebra's type. -/
notation:max "⦇" φ "⦈" => cataR φ

/-- The catamorphism computation rule holds for ANY algebra-relation `φ` (not just maps):
    `α ≫ cataFold φ = F(cataFold φ) ≫ φ`.  (The structural proof never uses `Map φ` — it is the
    `Map`-free form of `initial`'s own `cata_comm` field.) -/
public theorem cataFold_comm {c : RelSet.{0}} (φ : Fobj L E c ⟶ c) :
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
public theorem cataR_eq_relCata {c : RelSet.{0}} (φ : Fobj L E c ⟶ c) :
    cataR φ = relCata (initial L E) φ :=
  (relCata_UP (initial L E) φ (cataR φ)).mp (cataFold_comm φ)

/-- The `wrap`-component of an algebra `φ = [g, h]`. -/
def algWrap {c : RelSet.{0}} (φ : Fobj L E c ⟶ c) : dL L ⟶ c :=
  fun d r => φ (Sum.inl d) r
/-- The `snoc`-component of an algebra `φ = [g, h]`. -/
def algSnoc {c : RelSet.{0}} (φ : Fobj L E c ⟶ c) :
    (⟨c.carrier × E⟩ : RelSet.{0}) ⟶ c := fun p r => φ (Sum.inr p) r

/-- The constructor `wrap` as a relation. -/
def wrapR : dL L ⟶ dSL L E := graph SnocList.wrap
/-- The constructor `snoc` as a relation. -/
def snocR : (⟨SnocList L E × E⟩ : RelSet.{0}) ⟶ dSL L E := graph (fun p => SnocList.snoc p.1 p.2)

/-- **The §6.1/§6.4 recursive equation** (B&dM p.138/145): the converse of a catamorphism over a
    snoc-list datatype satisfies `val° = (wrap·g°) ∪ (snoc·(val°×id)·h°)` (mirrored to diagram
    order), for any algebra `φ = [g, h]`. -/
theorem cata_converse_eq {c : RelSet.{0}} (φ : Fobj L E c ⟶ c) :
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

end Freyd.Alg.RelSet.SL
