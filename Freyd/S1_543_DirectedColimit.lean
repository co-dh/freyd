module

/-
  Directed (filtered) colimits of types — mathlib-free.

  Foundation for the §1.543 Capitalization Lemma: that proof takes a directed
  colimit of a system of categories indexed by ordinals.  A colimit of categories
  is built on the colimit of its object-types and hom-types, so the bedrock is the
  directed colimit of *types*, developed here from scratch (no `Ordinal`, no
  mathlib `CategoryTheory`).

  Milestone 1 of the §1.543 capitalization construction:
  the directed colimit of types, its canonical inclusions, their compatibility,
  and the universal property (`desc`).  All Sorry-free.
-/

namespace Freyd.Colim

universe u w t

/-- A directed preorder on `ι`: reflexive, transitive, and any two elements have a
    common upper bound.  (`le` is a `Prop`, so proof irrelevance identifies the
    different routes to a bound — essential for the colimit to be well-defined.) -/
public structure Directed (ι : Type u) where
  le : ι → ι → Prop
  refl : ∀ i, le i i
  trans : ∀ {i j k}, le i j → le j k → le i k
  bound : ∀ i j, ∃ k, le i k ∧ le j k

/-- A directed system of types over `(ι, D)`: a family `X` with transition maps
    `tr` respecting identity and composition. -/
public structure System (ι : Type u) (D : Directed ι) where
  X : ι → Type w
  tr : ∀ {i j}, D.le i j → X i → X j
  tr_refl : ∀ {i} (x : X i), tr (D.refl i) x = x
  tr_trans : ∀ {i j k} (hij : D.le i j) (hjk : D.le j k) (x : X i),
    tr (D.trans hij hjk) x = tr hjk (tr hij x)

variable {ι : Type u} {D : Directed ι}

/-- Germ equivalence: `⟨i,x⟩ ~ ⟨j,y⟩` iff they become equal at some common upper
    bound `k`. -/
@[expose] public def Rel (S : System ι D) : (Σ i, S.X i) → (Σ i, S.X i) → Prop :=
  fun p q => ∃ (k : ι) (hik : D.le p.1 k) (hjk : D.le q.1 k), S.tr hik p.2 = S.tr hjk q.2

public theorem rel_symm (S : System ι D) {p q : Σ i, S.X i} (h : Rel S p q) : Rel S q p := by
  obtain ⟨k, hik, hjk, e⟩ := h
  exact ⟨k, hjk, hik, e.symm⟩

public theorem rel_trans (S : System ι D) {p q r : Σ i, S.X i}
    (hpq : Rel S p q) (hqr : Rel S q r) : Rel S p r := by
  obtain ⟨k₁, h1, h2, e1⟩ := hpq
  obtain ⟨k₂, h3, h4, e2⟩ := hqr
  obtain ⟨m, hm1, hm2⟩ := D.bound k₁ k₂
  refine ⟨m, D.trans h1 hm1, D.trans h4 hm2, ?_⟩
  have lhs : S.tr (D.trans h1 hm1) p.2 = S.tr hm1 (S.tr h2 q.2) := by
    rw [S.tr_trans h1 hm1 p.2, e1]
  have rhs : S.tr (D.trans h4 hm2) r.2 = S.tr hm2 (S.tr h3 q.2) := by
    rw [S.tr_trans h4 hm2 r.2, ← e2]
  have mid : S.tr hm1 (S.tr h2 q.2) = S.tr hm2 (S.tr h3 q.2) := by
    rw [← S.tr_trans h2 hm1 q.2, ← S.tr_trans h3 hm2 q.2]
  rw [lhs, rhs]; exact mid

/-- The colimit setoid. -/
@[expose] public def setoid (S : System ι D) : Setoid (Σ i, S.X i) where
  r := Rel S
  iseqv := ⟨fun p => ⟨p.1, D.refl p.1, D.refl p.1, rfl⟩, rel_symm S, rel_trans S⟩

/-- The directed colimit `colim X` of a system of types. -/
@[expose] public def Colimit (S : System ι D) : Type _ := Quotient (setoid S)

/-- The canonical inclusion `X i → colim X`. -/
@[expose] public def incl (S : System ι D) (i : ι) (x : S.X i) : Colimit S := Quotient.mk (setoid S) ⟨i, x⟩

/-- Inclusions are compatible with the transition maps: pushing along `tr` then
    including equals including directly. -/
public theorem incl_compat (S : System ι D) {i j : ι} (hij : D.le i j) (x : S.X i) :
    incl S j (S.tr hij x) = incl S i x :=
  Quotient.sound ⟨j, D.refl j, hij, by rw [S.tr_refl]⟩

/-- Every element of the colimit is `incl S i x` for some stage `i` and `x`. -/
public theorem incl_surjective (S : System ι D) (c : Colimit S) :
    ∃ (i : ι) (x : S.X i), incl S i x = c := by
  refine Quotient.inductionOn c (fun p => ⟨p.1, p.2, rfl⟩)

/-- **Universal property.**  A cocone `g : ∀ i, X i → T` compatible with the
    transition maps factors uniquely through the colimit. -/
def desc (S : System ι D) {T : Type t} (g : ∀ i, S.X i → T)
    (hg : ∀ {i j : ι} (hij : D.le i j) (x : S.X i), g j (S.tr hij x) = g i x) :
    Colimit S → T :=
  Quotient.lift (fun p => g p.1 p.2) (by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, hik, hjk, hxy⟩
    calc g i x = g k (S.tr hik x) := (hg hik x).symm
      _ = g k (S.tr hjk y) := by rw [hxy]
      _ = g j y := hg hjk y)

@[simp] theorem desc_incl (S : System ι D) {T : Type t} (g : ∀ i, S.X i → T)
    (hg : ∀ {i j : ι} (hij : D.le i j) (x : S.X i), g j (S.tr hij x) = g i x)
    (i : ι) (x : S.X i) : desc S g hg (incl S i x) = g i x := rfl

/-- `desc` is the unique factorisation: any `h` agreeing with the cocone on the
    inclusions equals `desc`. -/
theorem desc_uniq (S : System ι D) {T : Type t} (g : ∀ i, S.X i → T)
    (hg : ∀ {i j : ι} (hij : D.le i j) (x : S.X i), g j (S.tr hij x) = g i x)
    (h : Colimit S → T) (hcompat : ∀ i x, h (incl S i x) = g i x) :
    h = desc S g hg := by
  funext c
  obtain ⟨i, x, rfl⟩ := incl_surjective S c
  rw [hcompat, desc_incl]

end Freyd.Colim
