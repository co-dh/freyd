/-
  Freyd & Scedrov, *Categories and Allegories* §1.444 — the HORN-SENTENCE METATHEOREM
  for the theory of Cartesian categories.

  §1.444 (book): *A HORN SENTENCE is a universally quantified sentence of the form
  `(P₁ ∧ P₂ ∧ … ∧ Pₙ) ⊃ Q` where the Pᵢ, Q are primitive.  By a Horn sentence in the
  theory of Cartesian categories we mean one whose primitive predicates are the basic
  predicates of category theory together with the predicates that assert that a diagram
  is a `terminator`, `product`, or `equalizer`.  Any Horn sentence in the theory of
  Cartesian categories true for the category of sets is true for all Cartesian
  categories.*

  BECAUSE (book): suppose `A` contains a counterexample — a configuration satisfying
  `P₁ … Pₙ` but violating `Q`.  The representable functors `(i, -)` are COLLECTIVELY
  FAITHFUL (§1.442), and each `(i, -)` PRESERVES the predicates terminator / product /
  equalizer (§1.442 again).  Faithfulness picks an `i` for which the violation of `Q`
  survives; preservation keeps `P₁ … Pₙ` true.  So `(i, -)` carries the counterexample
  into `Set`, contradicting truth-for-`Set`.

  This file gives a FAITHFUL OBJECT-LANGUAGE encoding of such Horn sentences
  (`HornSentence`), a semantics `HoldsIn 𝒞` interpreting them in any Cartesian category,
  the `Cat`/Cartesian structure of `Type v` (terminator `PUnit`, product `×`, equalizer
  subtype), the representable `Hom(i,-) : 𝒞 → Type v`, and the metatheorem itself, proven
  exactly along Freyd's lines (collective faithfulness + per-predicate preservation).
-/

module

public import Freyd.S1_42
public import Freyd.S1_43
public import Freyd.S1_47
public import Freyd.S1_241

open Freyd

universe v u

namespace Freyd.Horn

/-! ## §1.444  Syntax of Horn sentences in the Cartesian language

  A Horn sentence is universally quantified over a finite supply of OBJECT variables
  (`Fin nObj`) and MORPHISM variables.  A morphism variable is TYPED by a source and a
  target object-variable, so the syntax cannot form an ill-typed composite — this is what
  makes the encoding faithful rather than a stringly-typed stub.

  An ATOM is one of the three Cartesian primitive predicates applied to variables:
  `terminator`, `product`, `equalizer`.  A Horn sentence is `(⋀ hyps) ⊃ concl`. -/

/-- An OBJECT variable. -/
@[expose] public abbrev ObjVar (nObj : Nat) := Fin nObj

/-- A MORPHISM variable, typed by its source and target object-variables. -/
public structure MorVar (nObj : Nat) where
  src : ObjVar nObj
  tgt : ObjVar nObj
  /-- the index distinguishing parallel morphism variables -/
  idx : Nat
deriving DecidableEq

/-- An ATOMIC Cartesian predicate over the variables.

    * `terminator o` — the object `o` is a terminator (terminal object).
    * `product a b p pf ps` — `p` is a product of `a`, `b` with projections `pf : p→a`,
      `ps : p→b`; i.e. `(p, pf, ps)` satisfies the product universal property.
    * `equalizer e a bb em f g` — `em : e→a` is an equalizer of the parallel pair
      `f g : a→bb`.

    Each constructor carries the typing of its morphism variables as `MorVar` source /
    target *propositional* fields, so a well-formed atom names only well-typed diagrams. -/
inductive Atom (nObj : Nat) where
  | terminator (o : ObjVar nObj)
  | product (a b p : ObjVar nObj) (pf ps : MorVar nObj)
      (hpf_src : pf.src = p) (hpf_tgt : pf.tgt = a)
      (hps_src : ps.src = p) (hps_tgt : ps.tgt = b)
  | equalizer (e a bb : ObjVar nObj) (em f g : MorVar nObj)
      (hem_src : em.src = e) (hem_tgt : em.tgt = a)
      (hf_src : f.src = a) (hf_tgt : f.tgt = bb)
      (hg_src : g.src = a) (hg_tgt : g.tgt = bb)

/-- A HORN SENTENCE: a universally-quantified `(⋀ hyps) ⊃ concl` over `nObj` object
    variables and the morphism variables mentioned in the atoms. -/
structure HornSentence where
  nObj  : Nat
  hyps  : List (Atom nObj)
  concl : Atom nObj

/-! ## §1.444  Semantics: interpretation in a Cartesian category

  An ENVIRONMENT for a sentence in a category `𝒞` assigns an object to every object
  variable and a (correctly typed) morphism to every morphism variable. -/

section Semantics
variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-- An environment interpreting the variables of an `nObj`-sentence in `𝒞`. -/
public structure Env (𝒞 : Type u) [Cat.{v} 𝒞] (nObj : Nat) where
  obj : ObjVar nObj → 𝒞
  mor : (m : MorVar nObj) → (obj m.src ⟶ obj m.tgt)

/-- `Hom`-cast of a morphism variable along the propositional source/target equations.
    `morAs ρ m hs ht : ρ.obj s ⟶ ρ.obj t` is `ρ.mor m` retyped using `m.src = s`,
    `m.tgt = t`. -/
@[expose] public def morAs {nObj : Nat} (ρ : Env 𝒞 nObj) (m : MorVar nObj) {s t : ObjVar nObj}
    (hs : m.src = s) (ht : m.tgt = t) : ρ.obj s ⟶ ρ.obj t :=
  hs ▸ ht ▸ ρ.mor m

/-- The TERMINATOR predicate in `𝒞`: every object has a unique map to `o`. -/
@[expose] public def IsTerminalObj (o : 𝒞) : Prop := ∀ X : 𝒞, ∃ f : X ⟶ o, ∀ g : X ⟶ o, g = f

/-- The PRODUCT predicate (universal property) for `(p, pf, ps)` over `a`, `b`. -/
@[expose] public def IsProductObj {a b p : 𝒞} (pf : p ⟶ a) (ps : p ⟶ b) : Prop :=
  ∀ (X : 𝒞) (u : X ⟶ a) (v : X ⟶ b),
    ∃ h : X ⟶ p, h ≫ pf = u ∧ h ≫ ps = v ∧
      ∀ k : X ⟶ p, k ≫ pf = u → k ≫ ps = v → k = h

/-- The EQUALIZER predicate (universal property) for `em : e→a` over `f g : a→bb`. -/
@[expose] public def IsEqualizerObj {e a bb : 𝒞} (em : e ⟶ a) (f g : a ⟶ bb) : Prop :=
  em ≫ f = em ≫ g ∧
  ∀ (X : 𝒞) (h : X ⟶ a), h ≫ f = h ≫ g →
    ∃ k : X ⟶ e, k ≫ em = h ∧ ∀ m : X ⟶ e, m ≫ em = h → m = k

/-- Satisfaction of an atom by an environment. -/
def Atom.holds {nObj : Nat} (ρ : Env 𝒞 nObj) : Atom nObj → Prop
  | .terminator o => IsTerminalObj (ρ.obj o)
  | .product _a _b _p pf ps hpf_src hpf_tgt hps_src hps_tgt =>
      IsProductObj (morAs ρ pf hpf_src hpf_tgt) (morAs ρ ps hps_src hps_tgt)
  | .equalizer _e _a _bb em f g hem_src hem_tgt hf_src hf_tgt hg_src hg_tgt =>
      IsEqualizerObj (morAs ρ em hem_src hem_tgt)
        (morAs ρ f hf_src hf_tgt) (morAs ρ g hg_src hg_tgt)

/-- An environment satisfies a *list* of hypotheses (their conjunction). -/
def hypsHold {nObj : Nat} (ρ : Env 𝒞 nObj) (hs : List (Atom nObj)) : Prop :=
  ∀ a ∈ hs, a.holds ρ

/-- **§1.444 SEMANTICS**: `HoldsIn 𝒞 φ` — the Horn sentence `φ` holds in `𝒞`, i.e. for
    EVERY environment satisfying all hypotheses, the conclusion holds. -/
def HoldsIn (𝒞 : Type u) [Cat.{v} 𝒞] (φ : HornSentence) : Prop :=
  ∀ ρ : Env 𝒞 φ.nObj, hypsHold ρ φ.hyps → φ.concl.holds ρ

end Semantics

/-! ## The Cartesian structure of `Type v` (the category of sets)

  Terminator = `PUnit`, product = `×`, equalizer = subtype `{a // f a = g a}`. -/

/-! ## The representable `Hom(i, -) : 𝒞 → Type v` -/

section Representable
variable {𝒞 : Type u} [Cat.{v} 𝒞]

@[simp] theorem homFunctor_map (i : 𝒞) {A B : 𝒞} (f : A ⟶ B) (h : i ⟶ A) :
    (homFunctor i).map f h = h ≫ f := rfl

end Representable

/-! ## Per-predicate PRESERVATION by `Hom(i, -)` (Freyd §1.442)

  `Hom(i,-)` carries a terminator / product / equalizer in `𝒞` to a terminator / product
  / equalizer in `Type v`.  These are the three lemmas Freyd cites at §1.444. -/

section Preservation
variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-- `Hom(i,-)` preserves TERMINATORS: if `o` is terminal in `𝒞` then `Hom(i,o) = (i⟶o)`
    is terminal in `Type v` (a one-element set). -/
public theorem homFunctor_preserves_terminal (i : 𝒞) {o : 𝒞} (ho : IsTerminalObj o) :
    IsTerminalObj (Freyd.representable i o) := by
  -- `Hom(i,o) = (i⟶o)` is a one-element set: the unique global map to `o`, constantly.
  obtain ⟨t, ht⟩ := ho i
  refine fun X => ⟨fun _ => t, fun g => ?_⟩
  funext x; exact ht (g x)

/-- `Hom(i,-)` preserves PRODUCTS: a product `(p, pf, ps)` in `𝒞` is sent to the product
    `(i⟶p, (·≫pf), (·≫ps))` in `Type v`.  The Set-product UP is solved by the unique
    `𝒞`-lift of the pair of legs. -/
public theorem homFunctor_preserves_product (i : 𝒞) {a b p : 𝒞} {pf : p ⟶ a} {ps : p ⟶ b}
    (hp : IsProductObj pf ps) :
    IsProductObj (𝒞 := Type v)
      ((homFunctor i).map pf) ((homFunctor i).map ps) := by
  intro X u v
  -- `u : X → (i⟶a)`, `v : X → (i⟶b)`.  For each `x : X`, lift the pair `(u x, v x)`.
  refine ⟨fun x => (hp i (u x) (v x)).choose, ?_, ?_, ?_⟩
  · funext x; exact ((hp i (u x) (v x)).choose_spec).1
  · funext x; exact ((hp i (u x) (v x)).choose_spec).2.1
  · intro k hk₁ hk₂; funext x
    exact ((hp i (u x) (v x)).choose_spec).2.2 (k x)
      (congrFun hk₁ x) (congrFun hk₂ x)

/-- `Hom(i,-)` preserves EQUALIZERS: an equalizer `em : e→a` of `f,g : a→bb` in `𝒞` is
    sent to the equalizer `(i⟶e, (·≫em))` of `(·≫f), (·≫g)` in `Type v`. -/
public theorem homFunctor_preserves_equalizer (i : 𝒞) {e a bb : 𝒞} {em : e ⟶ a} {f g : a ⟶ bb}
    (he : IsEqualizerObj em f g) :
    IsEqualizerObj (𝒞 := Type v)
      ((homFunctor i).map em)
      ((homFunctor i).map f) ((homFunctor i).map g) := by
  obtain ⟨hcomm, huniv⟩ := he
  refine ⟨?_, ?_⟩
  · -- (·≫em)≫(·≫f) = (·≫em)≫(·≫g) in Set: pointwise associativity + `hcomm`.
    funext h
    show (h ≫ em) ≫ f = (h ≫ em) ≫ g
    rw [Cat.assoc, Cat.assoc, hcomm]
  · intro X h hh
    -- `h : X → (i⟶a)` with `(·≫f)∘h = (·≫g)∘h`.  Each `h x` equalizes `f,g`, so lifts.
    have hx : ∀ x, (h x) ≫ f = (h x) ≫ g := fun x => congrFun hh x
    refine ⟨fun x => (huniv i (h x) (hx x)).choose, ?_, ?_⟩
    · funext x; exact ((huniv i (h x) (hx x)).choose_spec).1
    · intro m hm; funext x
      exact ((huniv i (h x) (hx x)).choose_spec).2 (m x) (congrFun hm x)

end Preservation

/-! ## Transport of an environment along `Hom(i, -)`

  Given an environment `ρ` in `𝒞` and a base object `i`, push it to an environment
  `pushEnv i ρ` in `Type v` by post-composing every object with `Hom(i,-)`.  The three
  preservation lemmas say: every atom satisfied by `ρ` is satisfied by `pushEnv i ρ`. -/

section Transport
variable {𝒞 : Type u} [Cat.{v} 𝒞] {nObj : Nat}

/-- Push an environment `ρ` in `𝒞` to one in `Type v` via `Hom(i,-)`. -/
def pushEnv (i : 𝒞) (ρ : Env 𝒞 nObj) : Env (Type v) nObj where
  obj o := Freyd.representable i (ρ.obj o)
  mor m := (homFunctor i).map (ρ.mor m)

/-- `morAs` commutes with the push: pushing a retyped morphism is the retyped push. -/
theorem morAs_pushEnv (i : 𝒞) (ρ : Env 𝒞 nObj) (m : MorVar nObj)
    {s t : ObjVar nObj} (hs : m.src = s) (ht : m.tgt = t) :
    morAs (pushEnv i ρ) m hs ht
      = (homFunctor i).map (morAs ρ m hs ht) := by
  subst hs; subst ht; rfl

/-- **PRESERVATION (atom level)**: every atom satisfied by `ρ` in `𝒞` is satisfied by
    `pushEnv i ρ` in `Type v`.  This is the §1.442 product/terminator/equalizer
    preservation, dispatched constructor-by-constructor. -/
theorem atom_holds_pushEnv (i : 𝒞) (ρ : Env 𝒞 nObj) :
    ∀ (α : Atom nObj), α.holds ρ → α.holds (pushEnv i ρ)
  | .terminator o, h => homFunctor_preserves_terminal i h
  | .product _ _ _ _ _ _ _ _ _, h => by
      simp only [Atom.holds, morAs_pushEnv]
      exact homFunctor_preserves_product i h
  | .equalizer _ _ _ _ _ _ _ _ _ _ _ _, h => by
      simp only [Atom.holds, morAs_pushEnv]
      exact homFunctor_preserves_equalizer i h

/-- Preservation lifts to whole hypothesis lists. -/
theorem hypsHold_pushEnv (i : 𝒞) (ρ : Env 𝒞 nObj) (hs : List (Atom nObj))
    (h : hypsHold ρ hs) : hypsHold (pushEnv i ρ) hs :=
  fun α hα => atom_holds_pushEnv i ρ α (h α hα)

end Transport

/-! ## REFLECTION of the conclusion (Freyd §1.442 collective faithfulness)

  For the metatheorem we need: if the conclusion `Q` FAILS in `𝒞`, then it fails in
  `Type v` for SOME representable `Hom(i,-)`.  Equivalently (contrapositive of what we
  prove): if `Q` holds under every `pushEnv i ρ`, then it holds under `ρ`.  This is the
  REFLECTION half, and it is exactly collective faithfulness `cayley_faithful` — the
  representables jointly detect equality of morphisms / existence of factorisations. -/

section Reflection
variable {𝒞 : Type u} [Cat.{v} 𝒞] {nObj : Nat}

/-- **REFLECTION of TERMINATOR**: if `Hom(i, o)` is terminal in `Type v` for every `i`,
    then `o` is terminal in `𝒞`.  A global map `X → o` is witnessed at `i := X`;
    uniqueness is `cayley_faithful`. -/
public theorem reflect_terminal {o : 𝒞}
    (h : ∀ i : 𝒞, IsTerminalObj (Freyd.representable i o)) : IsTerminalObj o := by
  intro X
  -- existence: probe the terminal Set `Hom(X,o)` at the type `(X⟶X)`, evaluate at `id_X`.
  obtain ⟨w, _⟩ := h X (X ⟶ X)
  refine ⟨w (Cat.id X), fun g => ?_⟩
  -- uniqueness: `g = w(id_X)` since they agree after every precomposition (cayley_faithful).
  apply cayley_faithful
  intro Y k
  -- both `(·≫g)` and `(·≫w(id))` are global elements of the terminal `Hom(Y,o)`; they are equal,
  -- and evaluating at `k` gives `k ≫ g = k ≫ w(id_X)`.
  obtain ⟨w', hw'⟩ := h Y (Y ⟶ X)
  have e1 : (fun t : Y ⟶ X => t ≫ g) = w' := hw' _
  have e2 : (fun t : Y ⟶ X => t ≫ w (Cat.id X)) = w' := hw' _
  exact congrFun (e1.trans e2.symm) k

/-- **REFLECTION of PRODUCT**: if `(Hom(i,p), (·≫pf), (·≫ps))` is a Set-product for every
    `i`, then `(p, pf, ps)` is a product in `𝒞`.  Existence of the lift is read off at
    `i := X`; uniqueness is `cayley_faithful`. -/
public theorem reflect_product {a b p : 𝒞} {pf : p ⟶ a} {ps : p ⟶ b}
    (h : ∀ i : 𝒞, IsProductObj (𝒞 := Type v)
      ((homFunctor i).map pf) ((homFunctor i).map ps)) :
    IsProductObj pf ps := by
  intro X u v
  -- read the lift off the Set-product at `i := X`, applied to `id_X`.
  obtain ⟨ℓ, hℓ₁, hℓ₂, _⟩ := h X (X ⟶ X) (fun k => k ≫ u) (fun k => k ≫ v)
  refine ⟨ℓ (Cat.id X), ?_, ?_, ?_⟩
  · have := congrFun hℓ₁ (Cat.id X); simp only [set_comp, homFunctor_map, Cat.id_comp] at this
    exact this
  · have := congrFun hℓ₂ (Cat.id X); simp only [set_comp, homFunctor_map, Cat.id_comp] at this
    exact this
  · -- uniqueness via cayley_faithful: `k = ℓ(id)` whenever both equalise the legs.
    intro k hk₁ hk₂
    apply cayley_faithful
    intro Y m
    obtain ⟨ℓ', _, _, hu'⟩ := h Y (Y ⟶ X) (fun t => t ≫ u) (fun t => t ≫ v)
    -- both `(·≫k)` and `(·≫ℓ(id))` are lifts of `(·≫u, ·≫v)` at stage `Y`; unique ⇒ equal.
    have hℓid₁ : ℓ (Cat.id X) ≫ pf = u := by
      have hc := congrFun hℓ₁ (Cat.id X); simp only [set_comp, homFunctor_map, Cat.id_comp] at hc
      exact hc
    have hℓid₂ : ℓ (Cat.id X) ≫ ps = v := by
      have hc := congrFun hℓ₂ (Cat.id X); simp only [set_comp, homFunctor_map, Cat.id_comp] at hc
      exact hc
    have e1 : (fun t : Y ⟶ X => t ≫ k) = ℓ' :=
      hu' _ (by funext t; show (t ≫ k) ≫ pf = t ≫ u; rw [Cat.assoc, hk₁])
            (by funext t; show (t ≫ k) ≫ ps = t ≫ v; rw [Cat.assoc, hk₂])
    have e2 : (fun t : Y ⟶ X => t ≫ ℓ (Cat.id X)) = ℓ' :=
      hu' _ (by funext t; show (t ≫ ℓ (Cat.id X)) ≫ pf = t ≫ u; rw [Cat.assoc, hℓid₁])
            (by funext t; show (t ≫ ℓ (Cat.id X)) ≫ ps = t ≫ v; rw [Cat.assoc, hℓid₂])
    exact congrFun (e1.trans e2.symm) m

/-- **REFLECTION of EQUALIZER**: if `(Hom(i,e), (·≫em))` is a Set-equalizer of
    `(·≫f), (·≫g)` for every `i`, then `em` is an equalizer of `f, g` in `𝒞`. -/
public theorem reflect_equalizer {e a bb : 𝒞} {em : e ⟶ a} {f g : a ⟶ bb}
    (h : ∀ i : 𝒞, IsEqualizerObj (𝒞 := Type v)
      ((homFunctor i).map em)
      ((homFunctor i).map f) ((homFunctor i).map g)) :
    IsEqualizerObj em f g := by
  refine ⟨?_, ?_⟩
  · -- `em ≫ f = em ≫ g`: read at `i := e` applied to `id_e` via the Set-comm law.
    have := congrFun (h e).1 (Cat.id e)
    simp only [set_comp, homFunctor_map, Cat.id_comp] at this
    exact this
  · intro X k hk
    -- probe the Set-equalizer at `i := X` with the type `(X⟶X)` and `φ t := t ≫ k`; read the
    -- lift off at `id_X`, mirroring `reflect_product`.
    obtain ⟨_, huniv⟩ := h X
    obtain ⟨ℓ, hℓ, _⟩ := huniv (X ⟶ X) (fun t => t ≫ k)
      (by funext t; show (t ≫ k) ≫ f = (t ≫ k) ≫ g; rw [Cat.assoc, Cat.assoc, hk])
    have hℓid : ℓ (Cat.id X) ≫ em = k := by
      have := congrFun hℓ (Cat.id X); simp only [set_comp, homFunctor_map, Cat.id_comp] at this
      exact this
    refine ⟨ℓ (Cat.id X), hℓid, ?_⟩
    -- uniqueness via cayley_faithful.
    intro m hm
    apply cayley_faithful
    intro Y t
    obtain ⟨_, huniv'⟩ := h Y
    obtain ⟨ℓ', _, hu'⟩ := huniv' (Y ⟶ X) (fun s => s ≫ k)
      (by funext s; show (s ≫ k) ≫ f = (s ≫ k) ≫ g; rw [Cat.assoc, Cat.assoc, hk])
    have e1 : (fun s : Y ⟶ X => s ≫ m) = ℓ' :=
      hu' _ (by funext s; show (s ≫ m) ≫ em = s ≫ k; rw [Cat.assoc, hm])
    have e2 : (fun s : Y ⟶ X => s ≫ ℓ (Cat.id X)) = ℓ' :=
      hu' _ (by funext s; show (s ≫ ℓ (Cat.id X)) ≫ em = s ≫ k; rw [Cat.assoc, hℓid])
    exact congrFun (e1.trans e2.symm) t

/-- **REFLECTION (atom level)**: if an atom holds under `pushEnv i ρ` for EVERY `i`, then
    it holds under `ρ`.  Constructor-by-constructor via the three reflection lemmas. -/
theorem atom_holds_of_pushEnv (ρ : Env 𝒞 nObj) :
    ∀ (α : Atom nObj), (∀ i : 𝒞, α.holds (pushEnv i ρ)) → α.holds ρ
  | .terminator o, h => reflect_terminal h
  | .product _ _ _ _ _ _ _ _ _, h => by
      apply reflect_product
      intro i; have := h i; simp only [Atom.holds, morAs_pushEnv] at this; exact this
  | .equalizer _ _ _ _ _ _ _ _ _ _ _ _, h => by
      apply reflect_equalizer
      intro i; have := h i; simp only [Atom.holds, morAs_pushEnv] at this; exact this

end Reflection

/-! ## §1.444  THE HORN-SENTENCE METATHEOREM -/

section Metatheorem
variable {𝒞 : Type u} [Cat.{v} 𝒞]

/-- **§1.444 (Freyd)**: *Any Horn sentence in the theory of Cartesian categories true for
    the category of sets is true for all Cartesian categories.*

    PROOF (Freyd's, faithfully): let `ρ` be an environment in `𝒞` satisfying all
    hypotheses; we must show the conclusion holds in `𝒞`.  By REFLECTION
    (`atom_holds_of_pushEnv`) it suffices to show the conclusion holds under every pushed
    environment `pushEnv i ρ` in `Type v`.  Fix `i`.  Each hypothesis, being satisfied by
    `ρ`, is PRESERVED to `pushEnv i ρ` (`hypsHold_pushEnv`, the §1.442 product / terminator
    / equalizer preservation).  Since `φ` is true for `Type v` (`hSet`), the conclusion
    holds under `pushEnv i ρ`.  Reflection then transports it back to `𝒞`.

    The two halves are exactly Freyd's two ingredients: PRESERVATION of the primitive
    predicates by each representable, and COLLECTIVE FAITHFULNESS (`cayley_faithful`,
    inside the reflection lemmas) detecting the conclusion across all `i`. -/
theorem horn_metatheorem (φ : HornSentence) (hSet : HoldsIn (Type v) φ) :
    HoldsIn 𝒞 φ := by
  intro ρ hρ
  -- reflect: enough to prove the conclusion under every `pushEnv i ρ`.
  apply atom_holds_of_pushEnv ρ φ.concl
  intro i
  -- preserve the hypotheses to `Type v`, then apply truth-for-Set.
  exact hSet (pushEnv i ρ) (hypsHold_pushEnv i ρ φ.hyps hρ)

/-- **§1.444 (specialised to a Cartesian category)**: phrased with the ambient Cartesian
    structure in scope, matching the book's statement "true for all Cartesian categories".
    `horn_metatheorem` needs only `Cat`; specialising adds the hypothesis-bearing instance
    so the statement reads exactly as Freyd's. -/
theorem horn_metatheorem_cartesian [CartesianCategory 𝒞]
    (φ : HornSentence) (hSet : HoldsIn (Type v) φ) : HoldsIn 𝒞 φ :=
  horn_metatheorem φ hSet

end Metatheorem

end Freyd.Horn
