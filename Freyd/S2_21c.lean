module

universe u

/-
  Freyd & Scedrov, *Categories and Allegories* — §2.21(10).

  "The equational theory of representable distributive allegories reduces easily to the
  equational theory of representable allegories."

  The book's argument, formalized syntax-and-semantics style:

  (a)  Because union distributes with the other operations, every distributive-allegory
       expression is equivalent to one of the form `E₁ ∪ E₂ ∪ ⋯ ∪ Eₙ` where the `Eᵢ` are
       union-free   (`DTerm.eval_toUnion`).

  (b)  If `E₁ ∪ ⋯ ∪ Eₙ ⊆ E₁' ∪ ⋯ ∪ Eₘ'` in `Rel(Set)`, where each `Eᵢ, Eⱼ'` is union-free,
       then for each `i` there is a `j` such that `Eᵢ ⊆ Eⱼ'` in `Rel(Set)`; if not, there
       would be an `i` such that for each `j` there exists a counterexample for `Eᵢ ⊆ Eⱼ'`;
       the CARTESIAN PRODUCT of the counterexamples would yield a counterexample for
       `Eᵢ ⊆ E₁' ∪ ⋯ ∪ Eₘ'`   (`union_incl_iff`).

       (Cartesian product yields a representation of allegories `Rel(Set)^m → Rel(Set)` —
       it preserves the union-free operations `1, ∘, °, ∩` (`UTerm.eval_pi`).  It is NOT a
       representation of distributive allegories — it does not preserve `∪`
       (`piAssign_not_union`) — which is exactly why the argument works.)

  (c)  The equations true for `Rel(Set)` are therefore known iff the union-free equations
       are known: every distributive inclusion/equation is equivalent to a finite set of
       union-free inclusions (`dIncl_iff_unionFree`, `dEq_iff_unionFree`), and a union-free
       inclusion `E ⊆ F` is itself the union-free equation `E ∩ F = E` (`uIncl_iff_inter_eq`).

  DESIGN.  Expressions are ONE-SORTED: every variable denotes an endo-relation on a single
  set `A`, i.e. one hom-set of `Rel(Set)`.  This suffices for the book's argument — the
  counterexamples and their cartesian product never need more than one object — and keeps
  the syntax free of a sort context.  The union-free fragment is a separate inductive
  `UTerm` (with an embedding `UTerm.toD` into the distributive terms `DTerm`), so that
  "union-free" is enforced by the type, not by a side predicate.  Freyd's zero `0` is not
  included: the book's normal form `E₁ ∪ ⋯ ∪ Eₙ` has `n ≥ 1`, and omitting `0` keeps the
  normal-form lists automatically nonempty (`DTerm.exists_mem_toUnion`).

  The final book remark — combining with [2.158] to conclude that no finite set of
  distributive-allegory equations axiomatizes `Rel(Set)` — is out of scope (§2.158 is not
  formalized).

  Self-contained: no imports beyond Lean core.  Composition is written in DIAGRAM ORDER
  (`comp s t` = "first `s` then `t`", `(R ≫ S) a c ↔ ∃ b, R a b ∧ S b c`).
-/

namespace Freyd.S2_21c

/-- One hom-set of `Rel(Set)`: binary relations on the set `A`. -/
abbrev Rel (A : Type u) := A → A → Prop

/-! ## Syntax

  `UTerm V` — union-free allegory expressions in variables `V`;
  `DTerm V` — distributive-allegory expressions (the same operations plus `∪`). -/

/-- Union-free (allegory) expressions: variables, identity `1`, composition (diagram
    order), reciprocation `°`, intersection `∩`. -/
inductive UTerm (V : Type) : Type
  | var   : V → UTerm V
  | id    : UTerm V
  | comp  : UTerm V → UTerm V → UTerm V
  | recip : UTerm V → UTerm V
  | inter : UTerm V → UTerm V → UTerm V

/-- Distributive-allegory expressions: the union-free operations plus binary union `∪`. -/
inductive DTerm (V : Type) : Type
  | var   : V → DTerm V
  | id    : DTerm V
  | comp  : DTerm V → DTerm V → DTerm V
  | recip : DTerm V → DTerm V
  | inter : DTerm V → DTerm V → DTerm V
  | union : DTerm V → DTerm V → DTerm V

variable {V : Type} {A : Type u}

/-- The union-free fragment embeds into the distributive expressions. -/
def UTerm.toD : UTerm V → DTerm V
  | .var v     => .var v
  | .id        => .id
  | .comp s t  => .comp s.toD t.toD
  | .recip t   => .recip t.toD
  | .inter s t => .inter s.toD t.toD

/-! ## Semantics in `Rel(Set)`

  A term is evaluated at an assignment `ρ : V → Rel A` of relations to variables. -/

/-- Evaluation of union-free expressions.  Composition in diagram order. -/
def UTerm.eval : UTerm V → (V → Rel A) → A → A → Prop
  | .var v,     ρ, a, b => ρ v a b
  | .id,        _, a, b => a = b
  | .comp s t,  ρ, a, c => ∃ b, s.eval ρ a b ∧ t.eval ρ b c
  | .recip t,   ρ, a, b => t.eval ρ b a
  | .inter s t, ρ, a, b => s.eval ρ a b ∧ t.eval ρ a b

/-- Evaluation of distributive expressions. -/
def DTerm.eval : DTerm V → (V → Rel A) → A → A → Prop
  | .var v,     ρ, a, b => ρ v a b
  | .id,        _, a, b => a = b
  | .comp s t,  ρ, a, c => ∃ b, s.eval ρ a b ∧ t.eval ρ b c
  | .recip t,   ρ, a, b => t.eval ρ b a
  | .inter s t, ρ, a, b => s.eval ρ a b ∧ t.eval ρ a b
  | .union s t, ρ, a, b => s.eval ρ a b ∨ t.eval ρ a b

/-- The embedding preserves evaluation. -/
theorem UTerm.eval_toD (E : UTerm V) (ρ : V → Rel A) (a b : A) :
    E.toD.eval ρ a b ↔ E.eval ρ a b := by
  induction E generalizing a b with
  | var v => exact Iff.rfl
  | id => exact Iff.rfl
  | comp s t ihs iht => simp only [toD, DTerm.eval, eval, ihs, iht]
  | recip t iht => simp only [toD, DTerm.eval, eval, iht]
  | inter s t ihs iht => simp only [toD, DTerm.eval, eval, ihs, iht]

/-! ## (a)  Normal form: every expression is a finite union of union-free ones

  `toUnion` pushes `∪` out of `∘`, `°`, `∩` using the distributive laws of §2.21:
  `(s ∪ t)u = su ∪ tu`, `(s ∪ t)° = s° ∪ t°`, `r ∩ (s ∪ t) = (r ∩ s) ∪ (r ∩ t)`, …
  The result is a (nonempty) list of UNION-FREE terms whose union is the original term. -/

/-- The list of union-free disjuncts `E₁, …, Eₙ` with `t = E₁ ∪ ⋯ ∪ Eₙ`. -/
def DTerm.toUnion : DTerm V → List (UTerm V)
  | .var v     => [.var v]
  | .id        => [.id]
  | .comp s t  => s.toUnion.flatMap fun E => t.toUnion.map fun F => .comp E F
  | .recip t   => t.toUnion.map .recip
  | .inter s t => s.toUnion.flatMap fun E => t.toUnion.map fun F => .inter E F
  | .union s t => s.toUnion ++ t.toUnion

/-- The normal form is a NONEMPTY union (the book's `n ≥ 1`). -/
theorem DTerm.exists_mem_toUnion (t : DTerm V) : ∃ E, E ∈ t.toUnion := by
  induction t with
  | var v => exact ⟨.var v, List.mem_singleton.mpr rfl⟩
  | id => exact ⟨.id, List.mem_singleton.mpr rfl⟩
  | comp s t ihs iht =>
    obtain ⟨E, hE⟩ := ihs; obtain ⟨F, hF⟩ := iht
    exact ⟨.comp E F, List.mem_flatMap.mpr ⟨E, hE, List.mem_map.mpr ⟨F, hF, rfl⟩⟩⟩
  | recip t iht =>
    obtain ⟨E, hE⟩ := iht
    exact ⟨.recip E, List.mem_map.mpr ⟨E, hE, rfl⟩⟩
  | inter s t ihs iht =>
    obtain ⟨E, hE⟩ := ihs; obtain ⟨F, hF⟩ := iht
    exact ⟨.inter E F, List.mem_flatMap.mpr ⟨E, hE, List.mem_map.mpr ⟨F, hF, rfl⟩⟩⟩
  | union s t ihs _ =>
    obtain ⟨E, hE⟩ := ihs
    exact ⟨E, List.mem_append.mpr (Or.inl hE)⟩

/-- **§2.21(10)(a).**  Every distributive expression is equivalent to the union of its
    union-free disjuncts: `⟦t⟧ρ = ⟦E₁⟧ρ ∪ ⋯ ∪ ⟦Eₙ⟧ρ` where `toUnion t = [E₁, …, Eₙ]`. -/
theorem DTerm.eval_toUnion (t : DTerm V) (ρ : V → Rel A) (a b : A) :
    t.eval ρ a b ↔ ∃ E ∈ t.toUnion, E.eval ρ a b := by
  induction t generalizing a b with
  | var v => simp [toUnion, eval, UTerm.eval]
  | id => simp [toUnion, eval, UTerm.eval]
  | comp s t ihs iht =>
    simp only [eval, toUnion, ihs, iht, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨m, ⟨E, hE, hEa⟩, F, hF, hFb⟩
      exact ⟨.comp E F, ⟨E, hE, F, hF, rfl⟩, m, hEa, hFb⟩
    · rintro ⟨G, ⟨E, hE, F, hF, rfl⟩, m, hEa, hFb⟩
      exact ⟨m, ⟨E, hE, hEa⟩, F, hF, hFb⟩
  | recip t iht =>
    simp only [eval, toUnion, iht, List.mem_map]
    constructor
    · rintro ⟨E, hE, h⟩
      exact ⟨.recip E, ⟨E, hE, rfl⟩, h⟩
    · rintro ⟨G, ⟨E, hE, rfl⟩, h⟩
      exact ⟨E, hE, h⟩
  | inter s t ihs iht =>
    simp only [eval, toUnion, ihs, iht, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨⟨E, hE, hEa⟩, F, hF, hFb⟩
      exact ⟨.inter E F, ⟨E, hE, F, hF, rfl⟩, hEa, hFb⟩
    · rintro ⟨G, ⟨E, hE, F, hF, rfl⟩, hEa, hFb⟩
      exact ⟨⟨E, hE, hEa⟩, F, hF, hFb⟩
  | union s t ihs iht =>
    simp only [eval, toUnion, ihs, iht, List.mem_append]
    constructor
    · rintro (⟨E, hE, h⟩ | ⟨E, hE, h⟩)
      · exact ⟨E, Or.inl hE, h⟩
      · exact ⟨E, Or.inr hE, h⟩
    · rintro ⟨E, hE | hE, h⟩
      · exact Or.inl ⟨E, hE, h⟩
      · exact Or.inr ⟨E, hE, h⟩

/-! ## The cartesian-product representation `Rel(Set)^m → Rel(Set)`

  Given assignments `ρ j` on sets `A j` (`j : Fin m`), the product assignment interprets
  each variable as the product relation on `∀ j, A j`.  On UNION-FREE expressions this is a
  representation: evaluation commutes with the product (`UTerm.eval_pi`).  It does NOT
  preserve `∪` (`piAssign_not_union`). -/

/-- The product assignment: each variable becomes the product relation on `∀ j, A j`. -/
def piAssign {m : Nat} (A : Fin m → Type u) (ρ : ∀ j, V → Rel (A j)) : V → Rel (∀ j, A j) :=
  fun v x y => ∀ j, ρ j v (x j) (y j)

/-- Finite dependent choice over `Fin m`, by induction on `m` — CONSTRUCTIVE (no
    `Classical.choice`): the finitely many witnesses are assembled one coordinate at a
    time by `∃`-elimination.  Needed for the composition case of `UTerm.eval_pi`, where an
    intermediate point must be chosen PER COORDINATE. -/
public theorem finChoice : ∀ {m : Nat} {A : Fin m → Type u} {P : ∀ j, A j → Prop},
    (∀ j, ∃ b, P j b) → ∃ f : ∀ j, A j, ∀ j, P j (f j)
  | 0, _, _, _ => ⟨fun j => j.elim0, fun j => j.elim0⟩
  | _ + 1, _, _, h => by
    obtain ⟨b₀, hb₀⟩ := h 0
    obtain ⟨f, hf⟩ := finChoice fun i => h i.succ
    refine ⟨Fin.cases b₀ f, fun j => ?_⟩
    induction j using Fin.cases with
    | zero => simpa using hb₀
    | succ i => simpa using hf i

/-- **Cartesian product is a representation of ALLEGORIES**: evaluation of a UNION-FREE
    expression at the product assignment is the product of the coordinatewise evaluations.
    The composition case chooses the intermediate point per coordinate (`finChoice`) — this
    is exactly what fails for `∪`, see `piAssign_not_union`. -/
theorem UTerm.eval_pi {m : Nat} {A : Fin m → Type u} (ρ : ∀ j, V → Rel (A j)) :
    ∀ (E : UTerm V) (x y : ∀ j, A j),
      E.eval (piAssign A ρ) x y ↔ ∀ j, E.eval (ρ j) (x j) (y j)
  | .var v, x, y => Iff.rfl
  | .id, x, y => ⟨fun h j => congrFun h j, funext⟩
  | .comp s t, x, y => by
    constructor
    · rintro ⟨z, hs, ht⟩ j
      exact ⟨z j, (eval_pi ρ s x z).mp hs j, (eval_pi ρ t z y).mp ht j⟩
    · intro h
      obtain ⟨z, hz⟩ := finChoice
        (P := fun j b => s.eval (ρ j) (x j) b ∧ t.eval (ρ j) b (y j)) h
      exact ⟨z, (eval_pi ρ s x z).mpr fun j => (hz j).1,
                (eval_pi ρ t z y).mpr fun j => (hz j).2⟩
  | .recip t, x, y => eval_pi ρ t y x
  | .inter s t, x, y => by
    constructor
    · rintro ⟨hs, ht⟩ j
      exact ⟨(eval_pi ρ s x y).mp hs j, (eval_pi ρ t x y).mp ht j⟩
    · intro h
      exact ⟨(eval_pi ρ s x y).mpr fun j => (h j).1,
             (eval_pi ρ t x y).mpr fun j => (h j).2⟩

/-- The cartesian product is **not** a representation of DISTRIBUTIVE allegories: it does
    not preserve `∪`.  Two coordinates, one variable true in each coordinate only: the
    union holds coordinatewise everywhere, but at the product assignment neither disjunct
    holds.  (This failure is exactly why `union_incl_iff` works.) -/
theorem piAssign_not_union :
    ∃ (t : DTerm Bool) (ρ : ∀ _ : Fin 2, Bool → Rel Unit),
      (∀ j, t.eval (ρ j) () ()) ∧
      ¬ t.eval (piAssign (fun _ => Unit) ρ) (fun _ => ()) (fun _ => ()) := by
  refine ⟨.union (.var true) (.var false), fun j v _ _ => v = decide (j.1 = 0),
    fun j => ?_, fun h => ?_⟩
  · match j with
    | ⟨0, _⟩ => exact Or.inl rfl
    | ⟨1, _⟩ => exact Or.inr rfl
    | ⟨n + 2, h⟩ => exact absurd h (by omega)
  · rcases h with h | h
    · exact absurd (h ⟨1, by omega⟩) (by decide)
    · exact absurd (h ⟨0, by omega⟩) (by decide)

/-! ## Validity in `Rel(Set)`

  An inclusion is VALID if it holds for every set `A` and every assignment of relations on
  `A` to the variables — i.e. it holds in the representable allegory `Rel(Set)`. -/

/-- Validity of the union-free inclusion `E ⊆ F` in `Rel(Set)`. -/
def UIncl (E F : UTerm V) : Prop :=
  ∀ (A : Type u) (ρ : V → Rel A) (a b : A), E.eval ρ a b → F.eval ρ a b

/-- Validity of the inclusion `E₁ ∪ ⋯ ∪ Eₙ ⊆ F₁ ∪ ⋯ ∪ Fₘ` in `Rel(Set)`. -/
def UnionIncl (l r : List (UTerm V)) : Prop :=
  ∀ (A : Type u) (ρ : V → Rel A) (a b : A),
    (∃ E ∈ l, E.eval ρ a b) → ∃ F ∈ r, F.eval ρ a b

/-- Validity of the inclusion `s ⊆ t` between distributive expressions in `Rel(Set)`. -/
def DIncl (s t : DTerm V) : Prop :=
  ∀ (A : Type u) (ρ : V → Rel A) (a b : A), s.eval ρ a b → t.eval ρ a b

/-- Validity of the union-free equation `E = F` in `Rel(Set)`. -/
def UEq (E F : UTerm V) : Prop :=
  ∀ (A : Type u) (ρ : V → Rel A) (a b : A), E.eval ρ a b ↔ F.eval ρ a b

/-- Validity of the equation `s = t` between distributive expressions in `Rel(Set)`. -/
def DEq (s t : DTerm V) : Prop :=
  ∀ (A : Type u) (ρ : V → Rel A) (a b : A), s.eval ρ a b ↔ t.eval ρ a b

/-- An invalid union-free inclusion has a counterexample: a set, an assignment, and a pair
    in `⟦E⟧ρ \ ⟦F⟧ρ`. -/
theorem not_uIncl_counterexample {E F : UTerm V} (h : ¬ UIncl.{u} E F) :
    ∃ (A : Type u) (ρ : V → Rel A) (a b : A), E.eval ρ a b ∧ ¬ F.eval ρ a b :=
  Classical.byContradiction fun hc =>
    h fun A ρ a b hE => Classical.byContradiction fun hF => hc ⟨A, ρ, a, b, hE, hF⟩

/-! ## (b)  The key lemma -/

/-- **§2.21(10)(b), the key lemma.**  `E₁ ∪ ⋯ ∪ Eₙ ⊆ F₁ ∪ ⋯ ∪ Fₘ` is valid in `Rel(Set)`
    iff for each `i` there is a `j` with `Eᵢ ⊆ Fⱼ` valid — the inclusion of unions reduces
    to inclusions of union-free expressions, i.e. to the theory of representable
    allegories.

    Book proof, followed exactly: (⇐) is trivial.  (⇒) by contradiction: if some `Eᵢ = E`
    is contained in no `Fⱼ`, pick for each `j` a counterexample `(Aⱼ, ρⱼ, xⱼ, yⱼ)` with
    `(xⱼ, yⱼ) ∈ ⟦E⟧ρⱼ \ ⟦Fⱼ⟧ρⱼ`; the CARTESIAN PRODUCT of the counterexamples — the product
    set `∀ j, Aⱼ`, the product assignment, and the tupled pair — satisfies `E`
    (`UTerm.eval_pi`, using that `E` is union-free) but no `Fⱼ` (projecting `eval_pi` at
    coordinate `j`), contradicting the union inclusion. -/
theorem union_incl_iff (l r : List (UTerm V)) :
    UnionIncl.{u} l r ↔ ∀ E ∈ l, ∃ F ∈ r, UIncl.{u} E F := by
  constructor
  · intro h E hE
    refine Classical.byContradiction fun hno => ?_
    -- for each j, a counterexample (Aⱼ, ρⱼ, xⱼ, yⱼ) to E ⊆ r[j]
    have hcex : ∀ j : Fin r.length, ∃ (A : Type u) (ρ : V → Rel A) (a b : A),
        E.eval ρ a b ∧ ¬ (r[j.1]'j.isLt).eval ρ a b := fun j =>
      not_uIncl_counterexample fun hI =>
        hno ⟨r[j.1]'j.isLt, List.getElem_mem j.isLt, hI⟩
    obtain ⟨A, hA⟩ := Classical.axiomOfChoice hcex
    obtain ⟨ρ, hρ⟩ := Classical.axiomOfChoice hA
    obtain ⟨x, hx⟩ := Classical.axiomOfChoice hρ
    obtain ⟨y, hy⟩ := Classical.axiomOfChoice hx
    -- the cartesian product of the counterexamples is a counterexample to E ⊆ ⋃ⱼ Fⱼ
    obtain ⟨F, hFr, hF⟩ :=
      h _ (piAssign A ρ) x y ⟨E, hE, (UTerm.eval_pi ρ E x y).mpr fun j => (hy j).1⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hFr
    exact (hy ⟨i, hi⟩).2 ((UTerm.eval_pi ρ _ x y).mp hF ⟨i, hi⟩)
  · rintro h A ρ a b ⟨E, hE, hEab⟩
    obtain ⟨F, hFr, hEF⟩ := h E hE
    exact ⟨F, hFr, hEF A ρ a b hEab⟩

/-! ## (c)  The equational theory reduces -/

/-- **§2.21(10)(c) for inclusions.**  An inclusion between distributive expressions is
    valid in `Rel(Set)` iff the associated finite set of union-free inclusions is valid. -/
theorem dIncl_iff_unionFree (s t : DTerm V) :
    DIncl.{u} s t ↔ ∀ E ∈ s.toUnion, ∃ F ∈ t.toUnion, UIncl.{u} E F := by
  rw [← union_incl_iff]
  constructor
  · intro h A ρ a b hab
    exact (t.eval_toUnion ρ a b).mp (h A ρ a b ((s.eval_toUnion ρ a b).mpr hab))
  · intro h A ρ a b hab
    exact (t.eval_toUnion ρ a b).mpr (h A ρ a b ((s.eval_toUnion ρ a b).mp hab))

/-- **§2.21(10)(c), headline.**  An EQUATION between distributive expressions holds in
    `Rel(Set)` iff a finite set of union-free inclusions holds: the equational theory of
    representable distributive allegories reduces to the equational theory of representable
    allegories. -/
theorem dEq_iff_unionFree (s t : DTerm V) :
    DEq.{u} s t ↔
      ((∀ E ∈ s.toUnion, ∃ F ∈ t.toUnion, UIncl.{u} E F) ∧
       (∀ F ∈ t.toUnion, ∃ E ∈ s.toUnion, UIncl.{u} F E)) := by
  rw [← dIncl_iff_unionFree, ← dIncl_iff_unionFree]
  exact ⟨fun h => ⟨fun A ρ a b => (h A ρ a b).mp, fun A ρ a b => (h A ρ a b).mpr⟩,
         fun h A ρ a b => ⟨h.1 A ρ a b, h.2 A ρ a b⟩⟩

/-- A union-free INCLUSION is itself a union-free EQUATION: `E ⊆ F` iff `E ∩ F = E`.
    Hence `dEq_iff_unionFree` indeed lands in the EQUATIONAL theory of representable
    allegories. -/
theorem uIncl_iff_inter_eq (E F : UTerm V) :
    UIncl.{u} E F ↔ UEq.{u} (.inter E F) E :=
  ⟨fun h A ρ a b => ⟨fun hEF => hEF.1, fun hE => ⟨hE, h A ρ a b hE⟩⟩,
   fun h A ρ a b hE => ((h A ρ a b).mpr hE).2⟩

end Freyd.S2_21c
