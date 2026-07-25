/-
  Mathlib-free well-ordering theorem (Zermelo), from `Classical.choice`.

  ## Why this file exists

  Freyd §1.543's last open obligation `hwall_cap` reduces (Freyd/CapitalizationTransfinite.lean) to a
  *cofinal* points-acquisition: the successor tower must point EVERY well-supported object of the
  colimit.  A strict `Colim.CatSystem` transition forces the index to be a LINEAR chain, so a countable
  ℕ-chain reaches only countably many objects.  Pointing an uncountable object type `A : Type u`
  cofinally needs an UNCOUNTABLE linearly-ordered cofinal family — i.e. a WELL-ORDER of the objects,
  with limit stages formed as the generic directed `Colim.Colimit`.

  mathlib supplies `WellOrderingRel` / Zermelo's theorem, but the repo is deliberately mathlib-free.
  This file proves Zermelo from core Lean's `Classical.choice` ALONE, so the index type of
  `Freyd.Colim.Directed` / `Freyd.Inflation.OrdChain` can be any type, mathlib-free.

  ## What is proved

  * `IsWellOrder r`           — `r : α → α → Prop` is irreflexive, transitive, trichotomous, and
                                well-founded (every nonempty predicate has an `r`-least witness).
  * `exists_wellOrder α`      — Zermelo: `∃ r, IsWellOrder r` for every type `α`.
  * `IsWellOrder.least`       — least element of any nonempty predicate (the cofinal-enumeration engine).
  * `IsWellOrder.toDirected`  — a well-order is a `Freyd.Colim.Directed` (`bound = max`), ready to index
                                `OrdChain`/`CatSystem`.

  ## Method

  Zorn-free "g-tower" route (Zermelo 1904 / Bourbaki).  We develop the tiny amount of order theory we
  need (sets as predicates, initial segments) inline.  See `exists_wellOrder` for the construction.
-/
import Freyd.PredicateSet
import Freyd.S1_543_DirectedColimit

namespace Freyd

universe u

/-! ## Sets as predicates

The ONE copy of "a subset of `α`, as a predicate" for the whole repo.  Shared by the well-ordering
construction (§1.543), its Zorn machinery, and the §1.646 ultrafilter development.  The
filter-specific boolean operations (`univ`, `empty`, `compl` / `ᶜ`, `inter` / `∩ᵤ`) stay in
`S1_646_Ultrafilter.lean` — a global `ᶜ` would clash with the Heyting complement. -/

namespace Sub
variable {α : Type u}

@[ext] theorem ext {s t : Sub α} (h : ∀ a, s a ↔ t a) : s = t := funext fun a => propext (h a)

/-- `s ⊆ t`. -/
def Subset (s t : Sub α) : Prop := ∀ ⦃a⦄, s a → t a

@[inherit_doc] infixl:50 " ⊆ₛ " => Sub.Subset

theorem Subset.refl (s : Sub α) : s ⊆ₛ s := fun _ h => h
theorem Subset.trans {s t u : Sub α} (h₁ : s ⊆ₛ t) (h₂ : t ⊆ₛ u) : s ⊆ₛ u := fun _ h => h₂ (h₁ h)
theorem Subset.antisymm {s t : Sub α} (h₁ : s ⊆ₛ t) (h₂ : t ⊆ₛ s) : s = t :=
  Sub.ext fun a => ⟨@h₁ a, @h₂ a⟩

end Sub

namespace WO

/-! ## The well-order, bundled

We target a usable strict order: irreflexive, transitive, trichotomous (any two distinct elements are
comparable), and well-founded via a *least-element* operator on nonempty predicates.  Trichotomy +
well-foundedness give a genuine well-order. -/

/-- `r` is a well-order on `α`: a strict order (irreflexive, transitive), trichotomous, and every
    inhabited predicate `p` has an `r`-least witness.  This is the form the cofinal-enumeration engine
    of §1.543 consumes (it needs to repeatedly take the least not-yet-pointed object). -/
structure IsWellOrder {α : Type u} (r : α → α → Prop) : Prop where
  irrefl : ∀ a, ¬ r a a
  trans  : ∀ {a b c}, r a b → r b c → r a c
  /-- trichotomy: for any `a b`, exactly one of `r a b`, `a = b`, `r b a`. -/
  tri    : ∀ a b, r a b ∨ a = b ∨ r b a
  /-- well-foundedness as a least-element operator: any inhabited predicate has an `r`-least witness. -/
  least  : ∀ (p : α → Prop), (∃ a, p a) → ∃ m, p m ∧ ∀ b, p b → ¬ r b m

/-! ## Zermelo's construction

Fix a choice function `g : Sub α → α` that, on any set whose complement is inhabited, returns an element
*outside* it.  We build the well-order from `g`-towers.

The clean non-Zorn formulation (Zermelo / Bourbaki): consider sets `s : Sub α` equipped with a relation
making them well-ordered such that every element `x ∈ s` is `g` of its own strict-down-set within `s`.
Any two such "`g`-well-ordered sets" are comparable (one is an initial segment of the other), and their
union is again one and is `g`-closed, hence must be all of `α` — else `g (union)` would extend it.  We
encode "`x = g (down-set of x)`" *intrinsically* through the order, avoiding a separately-carried
relation, by working with the family of `g`-closed initial-segment systems.

We phrase it via **attainable sets**: `t : Sub α` is *attainable* when it is `g`-inductive, i.e. closed
and built up by `g` on initial segments.  We then read the order off inclusion of down-sets. -/

section Zermelo
variable {α : Type u}

open Classical

/-- The choice function on a NONEMPTY type (default `d`): on a set with inhabited complement, returns
    an element outside it; otherwise the default `d` (a branch the proof never relies on). -/
noncomputable def gChoice (d : α) : Sub α → α :=
  fun s => if h : ∃ a, ¬ s a then Classical.choose h else d

/-- Defining property of `gChoice`: if `s` misses some element, `gChoice d s` is one such (∉ s). -/
theorem gChoice_not_mem (d : α) {s : Sub α} (h : ∃ a, ¬ s a) : ¬ s (gChoice d s) := by
  unfold gChoice; rw [dif_pos h]; exact Classical.choose_spec h

/-! ### Bourbaki–Witt towers

Fix `g : Sub α → α`.  The *successor* of a set `s` is `succ s = s ∪ {g s}`.  A **tower** is any set
reachable from `∅` by iterating `succ` and taking unions of sub-collections.  We show towers form a
chain (any two are `⊆`-comparable) and are `succ`-closed, which is the Bourbaki–Witt fixpoint engine. -/

variable (g : Sub α → α)

/-- Successor of a set: adjoin the chosen new point `g s`. -/
def succ (s : Sub α) : Sub α := fun x => s x ∨ x = g s

theorem subset_succ (s : Sub α) : s ⊆ₛ succ g s := fun _ h => Or.inl h

theorem mem_succ_self (s : Sub α) : succ g s (g s) := Or.inr rfl

/-- A **tower**: built from `∅` by `succ` and arbitrary unions. -/
inductive Tower : Sub α → Prop
  | step (s : Sub α) : Tower s → Tower (succ g s)
  | sUnion (P : Sub α → Prop) (h : ∀ s, P s → Tower s) :
      Tower (fun x => ∃ s : Sub α, P s ∧ s x)

variable {g}

/-- The empty set is a tower (union of the empty family). -/
theorem Tower.empty : Tower g (fun _ => False) := by
  have h := Tower.sUnion (g := g) (fun _ => False) (fun s hs => hs.elim)
  have e : (fun x : α => ∃ s : Sub α, (fun _ => False) s ∧ s x) = (fun _ : α => False) :=
    Sub.ext fun x => ⟨fun ⟨_, hf, _⟩ => hf.elim, fun hf => hf.elim⟩
  rwa [e] at h

/-! #### Comparability (Bourbaki–Witt chain lemma)

A tower `c` is **narrow** if every tower `s ⊆ c` is either `c` itself or has `succ s ⊆ c` (i.e. `c`
admits no tower strictly between `s` and `succ s`).  We prove every tower is narrow, and that narrow
towers are comparable with all towers; hence any two towers are `⊆`-comparable. -/

/-- `c` is narrow: no tower sits strictly between any `s ⊆ c` and its successor. -/
def Narrow (c : Sub α) : Prop :=
  ∀ s, Tower g s → s ⊆ₛ c → s = c ∨ succ g s ⊆ₛ c

/-- If `c` is a narrow tower then every tower `s` is comparable with it.  Induction on `s`:
    successor and union steps both reduce to narrowness of `c`. -/
theorem compare_of_narrow {c : Sub α} (hcN : Narrow (g := g) c) :
    ∀ {s}, Tower g s → s ⊆ₛ c ∨ c ⊆ₛ s := by
  intro s hs
  induction hs with
  | step t ht ih =>
    -- t is a tower; either t ⊆ c or c ⊆ t.
    rcases ih with htc | hct
    · -- t ⊆ c.  Narrowness: t = c or succ t ⊆ c.
      rcases hcN t ht htc with heq | hsc
      · -- t = c, so c ⊆ succ t.
        exact Or.inr (heq ▸ subset_succ g t)
      · exact Or.inl hsc
    · -- c ⊆ t ⊆ succ t.
      exact Or.inr (Sub.Subset.trans hct (subset_succ g t))
  | sUnion P hP ih =>
    -- union U = {x | ∃ s, P s ∧ s x}.  If every P-member ⊆ c then U ⊆ c; else some member ⊇ c.
    by_cases hall : ∀ s, P s → s ⊆ₛ c
    · exact Or.inl (fun x ⟨s, hPs, hsx⟩ => hall s hPs hsx)
    · -- some P-member s is not ⊆ c; by ih s is comparable, so c ⊆ s ⊆ U.
      have : ∃ s, P s ∧ ¬ s ⊆ₛ c := by
        refine Classical.byContradiction (fun hcon => hall (fun s hPs => ?_))
        exact Classical.byContradiction (fun hns => hcon ⟨s, hPs, hns⟩)
      obtain ⟨s, hPs, hns⟩ := this
      rcases ih s hPs with hsc | hcs
      · exact absurd hsc hns
      · exact Or.inr (fun x hcx => ⟨s, hPs, hcs hcx⟩)

/-- Every tower is narrow.  Induction on the tower; the successor and union cases each use
    comparability (`compare_of_narrow`) of the relevant sub-tower, available by the IH. -/
theorem Tower.narrow : ∀ {c}, Tower g c → Narrow (g := g) c := by
  intro c hc
  induction hc with
  | step t ht iht =>
    -- c = succ t, with `iht : Narrow t`.
    intro s hs hsc
    -- comparability of s with t
    rcases compare_of_narrow iht hs with hst | hts
    · -- s ⊆ t.  Narrowness of t: s = t or succ s ⊆ t ⊆ succ t.
      rcases iht s hs hst with heq | hsub
      · -- s = t, so succ s = succ t = c.
        exact Or.inr (heq ▸ Sub.Subset.refl _)
      · exact Or.inr (Sub.Subset.trans hsub (subset_succ g t))
    · -- t ⊆ s ⊆ succ t.  Either g t ∈ s (⟹ s = succ t) or not (⟹ s = t).
      by_cases hg : s (g t)
      · -- succ t ⊆ s, so s = succ t.
        refine Or.inl (Sub.Subset.antisymm hsc (fun x hx => ?_))
        rcases hx with hxt | rfl
        · exact hts hxt
        · exact hg
      · -- s ⊆ t (drops only g t), and t ⊆ s, so s = t ⟹ succ s = succ t = c.
        have hstt : s ⊆ₛ t := by
          intro x hx
          rcases hsc hx with hxt | rfl
          · exact hxt
          · exact absurd hx hg
        have : s = t := Sub.Subset.antisymm hstt hts
        exact Or.inr (this ▸ Sub.Subset.refl _)
  | sUnion P hP ihP =>
    -- c = ⋃ P.  Each P-member is a narrow tower (ihP).
    intro s hs hsc
    by_cases hsc' : s = (fun x => ∃ t : Sub α, P t ∧ t x)
    · exact Or.inl hsc'
    · -- s ≠ c, so some P-member p ⊄ s; narrowness of p gives succ s ⊆ p ⊆ c.
      refine Or.inr ?_
      -- find p ∈ P with ¬ p ⊆ s
      have hex : ∃ p, P p ∧ ¬ p ⊆ₛ s := by
        refine Classical.byContradiction (fun hcon => hsc' ?_)
        -- ¬∃ ⟹ all p ⊆ s ⟹ c ⊆ s ⊆ c ⟹ s = c
        have hall : ∀ p, P p → p ⊆ₛ s := by
          intro p hPp
          refine Classical.byContradiction (fun hnp => hcon ⟨p, hPp, hnp⟩)
        exact Sub.Subset.antisymm hsc (fun x ⟨p, hPp, hpx⟩ => hall p hPp hpx)
      obtain ⟨p, hPp, hnp⟩ := hex
      -- p ⊄ s; comparability (p narrow by ihP) ⟹ s ⊆ p; narrowness ⟹ succ s ⊆ p ⊆ c
      rcases compare_of_narrow (ihP p hPp) hs with hsp | hps
      · rcases (ihP p hPp) s hs hsp with heq | hsub
        · exact absurd (heq ▸ Sub.Subset.refl p) hnp
        · exact fun x hx => ⟨p, hPp, hsub hx⟩
      · exact absurd hps hnp

/-- **Chain lemma**: any two towers are `⊆`-comparable. -/
theorem tower_compare {s t : Sub α} (hs : Tower g s) (ht : Tower g t) : s ⊆ₛ t ∨ t ⊆ₛ s :=
  compare_of_narrow ht.narrow hs

/-! #### The maximal tower

`univ` is the union of all towers; it is itself a tower and `succ`-closed, so on a nonempty `α` it is
all of `α`.  This is the Bourbaki–Witt fixpoint. -/

/-- The union of all towers. -/
def bigU : Sub α := fun x => ∃ t : Sub α, Tower g t ∧ t x

theorem bigU_tower : Tower g (bigU (g := g)) :=
  Tower.sUnion (g := g) (Tower g) (fun _ h => h)

/-- Membership in `bigU` unfolds to: some tower contains the point. -/
theorem mem_bigU {x : α} : bigU (g := g) x ↔ ∃ t, Tower g t ∧ t x := Iff.rfl

/-- `bigU` is `succ`-closed: `g (bigU) ∈ bigU` (its successor is a tower, hence below `bigU`). -/
theorem g_bigU_mem : bigU (g := g) (g (bigU (g := g))) := by
  have h : Tower g (succ g (bigU (g := g))) := Tower.step _ bigU_tower
  exact ⟨_, h, mem_succ_self g _⟩

/-- With `g = gChoice d`, the maximal tower is all of `α`: otherwise `g bigU ∉ bigU`, contradicting
    `g_bigU_mem`. -/
theorem bigU_univ (d : α) : ∀ x, bigU (g := gChoice d) x := by
  intro x
  refine Classical.byContradiction (fun hx => ?_)
  -- bigU misses x, so gChoice picks an element ∉ bigU, contradicting g_bigU_mem
  have hne : ∃ a, ¬ bigU (g := gChoice d) a := ⟨x, hx⟩
  exact gChoice_not_mem d hne g_bigU_mem

/-! #### The order read off the towers

`r a b := some tower contains `a` but not `b``.  Its strict down-set `seg b = {y | r y b}` is the union
of all towers avoiding `b`, hence a tower; and `g (seg b) = b`.  These two facts deliver trichotomy and
well-foundedness. -/

/-- The strict order: a tower separates `a` (in) from `b` (out). -/
def order (a b : α) : Prop := ∃ t : Sub α, Tower g t ∧ t a ∧ ¬ t b

/-- Strict down-set of `b`: the union of all towers avoiding `b`. -/
def seg (b : α) : Sub α := fun y => order (g := g) y b

theorem seg_eq (b : α) : seg (g := g) b = (fun y => ∃ t : Sub α, (Tower g t ∧ ¬ t b) ∧ t y) := by
  refine Sub.ext (fun _ => ?_)
  constructor
  · rintro ⟨t, ht, hty, htb⟩; exact ⟨t, ⟨ht, htb⟩, hty⟩
  · rintro ⟨t, ⟨ht, htb⟩, hty⟩; exact ⟨t, ht, hty, htb⟩

/-- `seg b` is a tower. -/
theorem seg_tower (b : α) : Tower g (seg (g := g) b) := by
  rw [seg_eq]
  exact Tower.sUnion (g := g) (fun t => Tower g t ∧ ¬ t b) (fun t h => h.1)

/-- `b ∉ seg b` (every tower in the union avoids `b`). -/
theorem not_mem_seg (b : α) : ¬ seg (g := g) b b := by
  rintro ⟨t, _, _, htb⟩; exact htb ‹t b›

/-- Any tower `t` avoiding `b` is `⊆ seg b`. -/
theorem tower_avoid_subset_seg {b : α} {t : Sub α} (ht : Tower g t) (htb : ¬ t b) :
    t ⊆ₛ seg (g := g) b := fun _ hty => ⟨t, ht, hty, htb⟩

/-- The pivotal Zermelo fact: with `g = gChoice d`, `g (seg b) = b` for every `b`.  Hence `b` is the
    `g`-image of its own strict down-set — the well-ordering's defining property. -/
theorem g_seg (d : α) (b : α) : gChoice d (seg (g := gChoice d) b) = b := by
  -- s := seg b avoids b and is a tower; succ s is a tower with new point gChoice d s ∉ s.
  have hsT : Tower (gChoice d) (seg (g := gChoice d) b) := seg_tower b
  have hsb : ¬ seg (g := gChoice d) b b := not_mem_seg b
  -- s ≠ univ (misses b), so gChoice picks ∉ s
  have hgns : ¬ seg (g := gChoice d) b (gChoice d (seg (g := gChoice d) b)) :=
    gChoice_not_mem d ⟨b, hsb⟩
  -- succ s is a tower; if its new point ≠ b it would avoid b, hence ⊆ s, contradiction.
  refine Classical.byContradiction (fun hne => ?_)
  have hsuccT : Tower (gChoice d) (succ (gChoice d) (seg (g := gChoice d) b)) :=
    Tower.step _ hsT
  -- succ s avoids b: s avoids b and new point gChoice d s ≠ b
  have hsuccb : ¬ succ (gChoice d) (seg (g := gChoice d) b) b := by
    rintro (hb | hb)
    · exact hsb hb
    · exact hne hb.symm
  have hsub : succ (gChoice d) (seg (g := gChoice d) b) ⊆ₛ seg (g := gChoice d) b :=
    tower_avoid_subset_seg hsuccT hsuccb
  exact hgns (hsub (mem_succ_self (gChoice d) _))

/-! #### The four well-order properties for `order (gChoice d)` -/

/-- `order a b` is exactly `a ∈ seg b`. -/
theorem order_iff_seg {a b : α} : order (g := g) a b ↔ seg (g := g) b a := Iff.rfl

theorem order_trans {a b c : α} (hab : order (g := g) a b) (hbc : order (g := g) b c) :
    order (g := g) a c := by
  obtain ⟨t, ht, hta, htb⟩ := hab
  obtain ⟨s, hs, hsb, hsc⟩ := hbc
  -- compare towers t, s.  Need a tower containing a, missing c.
  rcases tower_compare ht hs with hts | hst
  · -- t ⊆ s; then a ∈ s.  s misses c.  But does s miss... a ∈ t ⊆ s, c ∉ s. Good.
    exact ⟨s, hs, hts hta, hsc⟩
  · -- s ⊆ t; b ∈ s ⊆ t, but b ∉ t — contradiction, so this branch is vacuous via a ∈ t, c ?
    exact absurd (hst hsb) htb

/-- Trichotomy via comparability of `seg a`, `seg b` and narrowness. -/
theorem order_tri (d : α) (a b : α) :
    order (g := gChoice d) a b ∨ a = b ∨ order (g := gChoice d) b a := by
  -- order a b ↔ seg b a; order b a ↔ seg a b
  rcases tower_compare (seg_tower (g := gChoice d) a) (seg_tower (g := gChoice d) b) with hab | hba
  · -- seg a ⊆ seg b.  Narrowness of seg b: seg a = seg b ∨ succ (seg a) ⊆ seg b.
    rcases (seg_tower (g := gChoice d) b).narrow _ (seg_tower (g := gChoice d) a) hab with heq | hsub
    · -- seg a = seg b ⟹ a = gChoice(seg a) = gChoice(seg b) = b
      refine Or.inr (Or.inl ?_)
      have := g_seg d a; rw [heq, g_seg d b] at this; exact this.symm
    · -- a = gChoice (seg a) ∈ succ (seg a) ⊆ seg b, so order a b
      refine Or.inl ?_
      have ha : succ (gChoice d) (seg (g := gChoice d) a) (gChoice d (seg (g := gChoice d) a)) :=
        mem_succ_self _ _
      rw [g_seg d a] at ha
      exact hsub ha
  · -- symmetric: seg b ⊆ seg a
    rcases (seg_tower (g := gChoice d) a).narrow _ (seg_tower (g := gChoice d) b) hba with heq | hsub
    · refine Or.inr (Or.inl ?_)
      have := g_seg d b; rw [heq, g_seg d a] at this; exact this
    · refine Or.inr (Or.inr ?_)
      have hb : succ (gChoice d) (seg (g := gChoice d) b) (gChoice d (seg (g := gChoice d) b)) :=
        mem_succ_self _ _
      rw [g_seg d b] at hb
      exact hsub hb

/-- The largest tower avoiding a predicate `p`: the union of all towers disjoint from `p`. -/
def avoid (d : α) (p : α → Prop) : Sub α :=
  fun y => ∃ t : Sub α, (Tower (gChoice d) t ∧ ∀ x, p x → ¬ t x) ∧ t y

theorem avoid_tower (d : α) (p : α → Prop) : Tower (gChoice d) (avoid d p) :=
  Tower.sUnion (g := gChoice d) (fun t => Tower (gChoice d) t ∧ ∀ x, p x → ¬ t x) (fun _ h => h.1)

/-- `avoid d p` is disjoint from `p`. -/
theorem avoid_disjoint (d : α) {p : α → Prop} {x : α} (hp : p x) : ¬ avoid d p x := by
  rintro ⟨t, ⟨_, hdis⟩, htx⟩; exact hdis x hp htx

/-- Any tower disjoint from `p` is `⊆ avoid d p`. -/
theorem tower_disjoint_subset_avoid (d : α) {p : α → Prop} {t : Sub α}
    (ht : Tower (gChoice d) t) (hdis : ∀ x, p x → ¬ t x) : t ⊆ₛ avoid d p :=
  fun _ hty => ⟨t, ⟨ht, hdis⟩, hty⟩

/-- **Least-element operator.**  For inhabited `p`, `gChoice d (avoid d p)` is a `p`-element that is
    `order`-least.  Mirrors `g_seg`: the chosen point past the largest `p`-avoiding tower lands in `p`. -/
theorem least_exists (d : α) (p : α → Prop) (hp : ∃ a, p a) :
    ∃ m, p m ∧ ∀ b, p b → ¬ order (g := gChoice d) b m := by
  obtain ⟨a₀, ha₀⟩ := hp
  -- m := gChoice d (avoid d p)
  have hAT : Tower (gChoice d) (avoid d p) := avoid_tower d p
  -- avoid d p misses a₀ (∈ p), so gChoice picks outside avoid
  have hmiss : ¬ avoid d p a₀ := avoid_disjoint d ha₀
  have hgout : ¬ avoid d p (gChoice d (avoid d p)) := gChoice_not_mem d ⟨a₀, hmiss⟩
  refine ⟨gChoice d (avoid d p), ?_, ?_⟩
  · -- p m : else succ (avoid) avoids p ⟹ ⊆ avoid, contradiction
    refine Classical.byContradiction (fun hnp => ?_)
    have hsuccT : Tower (gChoice d) (succ (gChoice d) (avoid d p)) := Tower.step _ hAT
    have hdis : ∀ x, p x → ¬ succ (gChoice d) (avoid d p) x := by
      intro x hpx
      rintro (hx | hx)
      · exact avoid_disjoint d hpx hx
      · exact hnp (hx ▸ hpx)
    have hsub : succ (gChoice d) (avoid d p) ⊆ₛ avoid d p :=
      tower_disjoint_subset_avoid d hsuccT hdis
    exact hgout (hsub (mem_succ_self (gChoice d) _))
  · -- least: any b ∈ p has ¬ order b m
    intro b hpb
    rintro ⟨t, ht, htb, htm⟩
    -- t contains b (∈ p), misses m.  Compare with avoid d p.
    rcases tower_compare ht hAT with hta | hat
    · -- t ⊆ avoid: b ∈ t ⊆ avoid, but avoid avoids p — contradiction
      exact avoid_disjoint d hpb (hta htb)
    · -- avoid ⊆ t.  Narrowness of t: avoid = t ∨ succ avoid ⊆ t.
      rcases ht.narrow _ hAT hat with heq | hsub
      · -- avoid = t ⟹ b ∈ t = avoid, contradiction
        exact avoid_disjoint d hpb (heq ▸ htb)
      · -- m = gChoice avoid ∈ succ avoid ⊆ t, contradicting m ∉ t
        have hm : succ (gChoice d) (avoid d p) (gChoice d (avoid d p)) := mem_succ_self _ _
        exact htm (hsub hm)

end Zermelo

/-! ## Zermelo's theorem (the linchpin) -/

/-- **Zermelo's well-ordering theorem, mathlib-free.**  Every type carries a well-order, proved from
    `Classical.choice` alone.  This is the linchpin that makes §1.543's transfinite cofinal tower
    mathlib-free: feed `(exists_wellOrder A).choose` into `IsWellOrder.toDirected` to index a transfinite
    `OrdChain`/`CatSystem` over the well-supported objects. -/
theorem exists_wellOrder (α : Type u) : ∃ r : α → α → Prop, IsWellOrder r := by
  by_cases hne : Nonempty α
  · -- nonempty: fix d, use order (gChoice d)
    obtain ⟨d⟩ := hne
    refine ⟨order (g := gChoice d), ?_⟩
    exact
      { irrefl := not_mem_seg
        trans := fun {a b c} => order_trans
        tri := order_tri d
        least := least_exists d }
  · -- empty: the always-false relation; `least`'s hypothesis `∃ a, p a` is impossible
    refine ⟨fun _ _ => False, ?_⟩
    exact
      { irrefl := fun _ h => h
        trans := fun h _ => h.elim
        tri := fun a _ => absurd ⟨a⟩ hne
        least := fun _ h => absurd ⟨h.choose⟩ hne }

/-! ## Downstream plumbing (independent of the Zermelo proof)

These show that ONCE `IsWellOrder r` is available, it feeds the existing §1.543 machinery directly:
`least` is the cofinal-enumeration engine, and `toDirected` packages the order as a `Colim.Directed`
index (bound = the `r`-max of two elements, which exists by trichotomy).  Both are Sorry-free, so the
ONLY thing standing between mathlib-free §1.543 and a closed `hwall_cap` is `exists_wellOrder`. -/

namespace IsWellOrder
variable {α : Type u} {r : α → α → Prop}

/-- A well-order is a directed preorder for `Colim.Directed`, using the reflexive closure `r a b ∨ a = b`
    as `le` and the `r`-greater of `i j` as the common bound.  This is the index a transfinite
    `OrdChain`/`CatSystem` consumes — so a well-order on the object type drives the cofinal outer tower
    with limit stages = the generic `Colim.Colimit`. -/
def toDirected (w : IsWellOrder r) : Colim.Directed α where
  le a b := r a b ∨ a = b
  refl a := Or.inr rfl
  trans {a b c} hab hbc := by
    rcases hab with hab | rfl
    · rcases hbc with hbc | rfl
      · exact Or.inl (w.trans hab hbc)
      · exact Or.inl hab
    · exact hbc
  bound a b := by
    rcases w.tri a b with h | h | h
    · exact ⟨b, Or.inl h, Or.inr rfl⟩
    · exact ⟨b, Or.inr h, Or.inr rfl⟩
    · exact ⟨a, Or.inr rfl, Or.inl h⟩

end IsWellOrder

/-! ## Zorn's lemma (mathlib-free), from the Bourbaki–Witt tower engine

  The same `Tower`/`bigU` machinery yields Zorn directly, with NO well-order detour.  We phrase it
  for a type `T` carrying a preorder `le` in which every `le`-CHAIN (a `⊆`-set of pairwise comparable
  points) has an upper bound: then `T` has a `le`-maximal element.

  Construction (standard).  Fix a default `d : T` and a choice function `g : Sub T → T` that, on a
  set `s` admitting a *strict* upper bound, returns one; else returns an arbitrary upper bound of `s`
  (which exists by the chain hypothesis once `s` is a chain).  Every tower is then a chain (induction
  on the tower: `succ s = s ∪ {g s}` stays a chain because `g s` is `≥` every element of the chain
  `s`).  Hence `bigU` is a chain, so it has an upper bound `b`.  And `b` is maximal: if some `c > b`
  then `g bigU` is a strict upper bound of `bigU`, so `g bigU ∉ bigU` (it is `>` every member),
  contradicting `g_bigU_mem`. -/

section Zorn
variable {T : Type u}
open Classical

/-- A `Sub T` is a `le`-CHAIN: any two of its members are `le`-comparable. -/
def IsChain (le : T → T → Prop) (s : Sub T) : Prop :=
  ∀ ⦃x⦄, s x → ∀ ⦃y⦄, s y → le x y ∨ le y x

/-- `b` is an upper bound of `s`. -/
def IsUB (le : T → T → Prop) (s : Sub T) (b : T) : Prop := ∀ ⦃x⦄, s x → le x b

/-- `c` is a STRICT upper bound of `s`: an upper bound of `s` that is `le`-below NO member of `s`.
    (Reflexivity then forces `c ∉ s`, which is the contradiction that terminates the tower.) -/
def IsStrictUB (le : T → T → Prop) (s : Sub T) (c : T) : Prop :=
  IsUB le s c ∧ ∀ x, s x → ¬ le c x

/-- The Zorn choice function.  `zg le d s` returns a STRICT upper bound of `s` if one exists; else
    ANY upper bound of `s` if one exists; else the default `d`.  On every chain (which, by the Zorn
    hypothesis, has an upper bound) `zg le d s` is therefore an upper bound of `s` — this is what
    keeps the towers chains.  When `s` additionally has a strict upper bound, `zg le d s` is one. -/
noncomputable def zg (le : T → T → Prop) (d : T) : Sub T → T :=
  fun s => if hstr : ∃ c, IsStrictUB le s c then Classical.choose hstr
           else if hub : ∃ c, IsUB le s c then Classical.choose hub else d

/-- When `s` has a strict upper bound, `zg le d s` is one. -/
theorem zg_strict {le : T → T → Prop} {d : T} {s : Sub T} (h : ∃ c, IsStrictUB le s c) :
    IsStrictUB le s (zg le d s) := by
  unfold zg; rw [dif_pos h]; exact Classical.choose_spec h

/-- When `s` has any upper bound, `zg le d s` is one (whether or not a strict one exists). -/
theorem zg_ub {le : T → T → Prop} {d : T} {s : Sub T} (h : ∃ c, IsUB le s c) :
    IsUB le s (zg le d s) := by
  unfold zg
  by_cases hstr : ∃ c, IsStrictUB le s c
  · rw [dif_pos hstr]; exact (Classical.choose_spec hstr).1
  · rw [dif_neg hstr, dif_pos h]; exact Classical.choose_spec h

/-- Every tower (for `g = zg le d`) is a `le`-chain.  Induction on the tower: the successor
    `succ s = s ∪ {g s}` stays a chain because `g s` is an upper bound of the chain `s` (`zg_ub`,
    using the Zorn hypothesis `hub` to know `s` has an upper bound). -/
theorem zg_tower_chain (le : T → T → Prop) (hrefl : ∀ a, le a a) (d : T)
    (hub : ∀ s : Sub T, IsChain le s → ∃ b, IsUB le s b) :
    ∀ {t : Sub T}, Tower (zg le d) t → IsChain le t := by
  intro t ht
  induction ht with
  | step s hs ih =>
    -- `s` is a chain (ih), so it has an upper bound, so `g s := zg le d s` is an upper bound of `s`.
    have hUB : IsUB le s (zg le d s) := zg_ub (hub s ih)
    intro x hx y hy
    rcases hx with hxs | rfl <;> rcases hy with hys | rfl
    · exact ih hxs hys
    · exact Or.inl (hUB hxs)
    · exact Or.inr (hUB hys)
    · exact Or.inl (hrefl _)
  | sUnion P hP ih =>
    -- union of towers; compare two members' source towers via `tower_compare`.
    intro x ⟨sx, hPsx, hsx⟩ y ⟨sy, hPsy, hsy⟩
    rcases tower_compare (hP sx hPsx) (hP sy hPsy) with hxy | hyx
    · exact ih sy hPsy (hxy hsx) hsy
    · exact ih sx hPsx hsx (hyx hsy)

/-- **Zorn's lemma (mathlib-free).**  If every `le`-chain in `T` has an upper bound (and `le` is
    reflexive), then `T` has a `le`-maximal element: some `m` such that no `c` is strictly `> m`
    (i.e. `le m c ∧ le c m` for every `c` with `le m c`).

    PROOF.  `bigU` (for `g = zg le d`) is a tower, hence a chain (`zg_tower_chain`); by the chain
    hypothesis it has an upper bound `m`.  `m` is maximal: were there `c` with `le m c` but not
    `le c m`, then `m` itself extends to a strict upper bound `c` of `bigU` (since `m` already bounds
    `bigU`), so `bigU` has a strict upper bound and `g bigU := zg le d bigU` is one
    (`zg_strict`).  But `g bigU ∈ bigU` (`g_bigU_mem`), so applying the strictness clause to
    `b := g bigU` (an upper bound, with `le (g bigU)(g bigU)` by reflexivity) yields `False`. -/
theorem zorn (le : T → T → Prop) (hrefl : ∀ a, le a a)
    (htrans : ∀ {a b c}, le a b → le b c → le a c)
    (hub : ∀ s : Sub T, IsChain le s → ∃ b, IsUB le s b) (hne : Nonempty T) :
    ∃ m : T, ∀ c, le m c → le c m := by
  obtain ⟨d⟩ := hne
  -- `m` := an upper bound of the maximal chain `bigU`.
  have hbigU_chain : IsChain le (bigU (g := zg le d)) :=
    zg_tower_chain le hrefl d hub bigU_tower
  obtain ⟨m, hm⟩ := hub _ hbigU_chain
  refine ⟨m, fun c hmc => ?_⟩
  -- Suppose not `le c m`.  Then `c` is a strict upper bound of `bigU`, contradiction.
  refine Classical.byContradiction (fun hcm => ?_)
  -- `c` upper-bounds bigU (every member `x ≤ m ≤ c`) and lies above no member
  -- (`le c x` ⟹ `le c m` via `le x m`, contradicting `¬ le c m`).
  have hstrUB : IsStrictUB le (bigU (g := zg le d)) c := by
    refine ⟨fun x hx => htrans (hm hx) hmc, fun x hx hcx => ?_⟩
    exact hcm (htrans hcx (hm hx))
  -- `g bigU` is then a strict upper bound, yet `g bigU ∈ bigU` (`g_bigU_mem`): reflexivity clashes.
  have hg_str := zg_strict (le := le) (d := d) ⟨c, hstrUB⟩
  exact hg_str.2 _ g_bigU_mem (hrefl _)

end Zorn

end WO

end Freyd
