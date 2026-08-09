/-
  Freyd & Scedrov, *Categories and Allegories* §2.158, Target 3:
  **The equational theory of `Rel(S)` is NOT finitely axiomatizable.**

  The core §2.158 development (`Freyd/S2_158_GraphAllegory.lean`) gives the graph
  model of the free one-object representable allegory, the tautological Yoneda
  lemma `graph_yoneda`, and the decision procedure `decision`.  This file builds,
  on top of that core, the ingredients of Freyd's no-finite-axiomatizability
  metatheorem (last paragraphs of §2.158):

  * LAYER 2/3 (this file, Sorry-free): a semantic notion `HoldsInRel E₁ E₂`
    ("the containment `E₁ ⊆ E₂` is true in `Rel(S)` for every set `S` and every
    interpretation of the labels"), a term-substitution operation with its
    semantic soundness, the equational **derivation system** `Derives Ax` of an
    axiom set `Ax` (axiom-instances closed under reflexivity, transitivity, and
    the monotone congruences of `∩`, `;`, `°`), and the **soundness bridge**
    `Derives_sound`: every containment derivable from a *valid* axiom set is true
    in `Rel(S)`.

  * LAYER 1 (this file, Sorry-free): the **rhombus families** — the series
    ladder (`ladder_holds`) and Freyd's genuine ENTANGLED `n`-rhombus chain
    (`entL`, `entR`, `ent_holds`), reconstructed from the book's figures.

  * ERRATUM (this file, machine-checked): the book's own two-rhombus example
    IS derivable from a finite valid axiom list (`ent0_derivable`) — its
    "identifying any one or any two of those pairs leaves `Ḡ`" claim fails for
    the `{s,t}`-containing pairs.  The corrected minimal witness needs ≥ 3
    rhombi; see the erratum section and the OPEN note.

  * LAYER 4a (this file, Sorry-free): **chain normalization**
    (`derives_iff_chain` — every derivation is a chain of single axiom-instance
    rewrites in one-hole contexts) and **jump extraction**
    (`Chain.exists_jump` — Freyd's "there must exist `i` …" skeleton).

  * LAYER 4 (metatheorem): the counting argument is isolated as an explicit,
    precisely-stated combinatorial hypothesis `RhombusHard`, and the headline
    `no_finite_axiomatization` is proved *conditionally* on it (a faithful
    reduction — NO hole, no new axiom); `ent_no_finite_axiomatization` pins it
    to the entangled family.  The OPEN note at the end states the three
    remaining graph-level lemmas (SP-wall dichotomy, bounded step, rigidity).

  STRICTLY MATHLIB-FREE.  Only Lean 4 core + `Freyd.*`.  Composition is in
  diagram order (`comp a b` = "first `a`, then `b`"), matching the core.
-/

module

public import Freyd.S2_158_GraphAllegory

namespace Freyd.S2_158

variable {L : Type}

/-! ## Layer 2/3 — semantics of containments in `Rel(S)`

  A model of the labels `L` on a carrier `V` is an interpretation
  `ι : L → V → V → Prop` (each label a binary relation on `V`).  This is exactly
  an object of `Rel(S)` together with a chosen family of relations, i.e. Freyd's
  "set `S` with a family of binary relations `A, B, C, …`".  `eval ι E` is the
  relation that the allegorical term `E` denotes. -/

/-- The relation denoted by a term in the model `(V, ι)`.  Mirrors the core's
    `toRel` but over an arbitrary interpretation rather than a graph's edges. -/
def eval {V : Type} (ι : L → V → V → Prop) : Term L → V → V → Prop
  | .var A => ι A
  | .one => fun x y => x = y
  | .recip e => fun x y => eval ι e y x
  | .meet a b => fun x y => eval ι a x y ∧ eval ι b x y
  | .comp a b => fun x y => ∃ z, eval ι a x z ∧ eval ι b z y

/-- **"true for `Rel(S)`".**  The containment `E₁ ⊆ E₂` holds in every model. -/
def HoldsInRel (E₁ E₂ : Term L) : Prop :=
  ∀ {V : Type} (ι : L → V → V → Prop) (x y : V), eval ι E₁ x y → eval ι E₂ x y

theorem HoldsInRel.refl (E : Term L) : HoldsInRel E E := fun _ _ _ h => h

theorem HoldsInRel.trans {E₁ E₂ E₃ : Term L}
    (h₁ : HoldsInRel E₁ E₂) (h₂ : HoldsInRel E₂ E₃) : HoldsInRel E₁ E₃ :=
  fun ι x y h => h₂ ι x y (h₁ ι x y h)

/-! ### Monotone congruences of the operations

  `°`, `∩`, `;` are order-preserving in `Rel(S)`, so a valid containment stays
  valid under each of them.  These are the semantic content of the `recip`,
  `meet`, `comp` rules of `Derives`, isolated as reusable lemmas (they let a
  containment be transported inside a bigger term). -/

/-- Reciprocation is monotone: `E₁ ⊆ E₂ ⟹ E₁° ⊆ E₂°`. -/
theorem HoldsInRel.recip {E₁ E₂ : Term L} (h : HoldsInRel E₁ E₂) :
    HoldsInRel (.recip E₁) (.recip E₂) :=
  fun _ x y h1 => h _ y x h1

/-- Intersection is monotone in both arguments. -/
theorem HoldsInRel.meet {A A' B B' : Term L}
    (hA : HoldsInRel A A') (hB : HoldsInRel B B') :
    HoldsInRel (.meet A B) (.meet A' B') :=
  fun ι x y h => ⟨hA ι x y h.1, hB ι x y h.2⟩

/-- Composition is monotone in both arguments (diagram order). -/
theorem HoldsInRel.comp {A A' B B' : Term L}
    (hA : HoldsInRel A A') (hB : HoldsInRel B B') :
    HoldsInRel (.comp A B) (.comp A' B') := by
  intro V ι x y h
  obtain ⟨z, ha, hb⟩ := h
  exact ⟨z, hA ι x z ha, hB ι z y hb⟩

/-! ### Bridge to the core graph model

  A graph `H` is the model `(H.V, fun A a b => H.edge a b A)`, and under this
  interpretation `eval` is exactly the core's `toRel`; conversely every model
  arises from a graph.  Hence `HoldsInRel` coincides with the core's `Gle` on
  term-graphs, and (via `decision`) with the existence of a graph map — Freyd's
  "a containment holds in `Rel(S)` iff it holds in **G**". -/

/-- Under the graph interpretation `eval` reduces to the core's `toRel`. -/
theorem eval_graphInterp (H : LGraph L) (e : Term L) (x y : H.V) :
    eval (fun A a b => H.edge a b A) e x y ↔ toRel H e x y := by
  induction e generalizing x y with
  | var A => exact Iff.rfl
  | one => exact Iff.rfl
  | recip e ih => exact ih y x
  | meet a b iha ihb => exact and_congr (iha x y) (ihb x y)
  | comp a b iha ihb => exact exists_congr (fun z => and_congr (iha x z) (ihb z y))

/-- `HoldsInRel` is exactly the core's graph containment `Gle` on term-graphs. -/
theorem holdsInRel_iff_Gle (E₁ E₂ : Term L) :
    HoldsInRel E₁ E₂ ↔ Gle (toGraph E₁) (toGraph E₂) := by
  constructor
  · intro h H x y h1
    rw [← toRel_eq_Trel] at h1 ⊢
    exact (eval_graphInterp H E₂ x y).mp
      (h (fun A a b => H.edge a b A) x y ((eval_graphInterp H E₁ x y).mpr h1))
  · intro h V ι x y h1
    let H : LGraph L := ⟨V, fun a b A => ι A a b, x, x⟩
    have h1' : toRel H E₁ x y := (eval_graphInterp H E₁ x y).mp h1
    have h2' : Trel (toGraph E₁) H x y := (toRel_eq_Trel H E₁ x y).mp h1'
    have h3' : toRel H E₂ x y := (toRel_eq_Trel H E₂ x y).mpr (h H x y h2')
    exact (eval_graphInterp H E₂ x y).mpr h3'

/-- **Freyd's decision procedure, in the `HoldsInRel` phrasing.**  A containment
    is true in `Rel(S)` for every `S` iff there is a graph map between the two
    term-graphs.  (Reuses the core `decision`.) -/
theorem holdsInRel_iff_hom (E₁ E₂ : Term L) :
    HoldsInRel E₁ E₂ ↔ Nonempty (Hom (toGraph E₂) (toGraph E₁)) := by
  rw [holdsInRel_iff_Gle]; exact (graph_yoneda (toGraph E₁) (toGraph E₂)).symm

/-! ### Substitution

  An equational axiom is used at *instances*: to apply `A ⊆ B` we substitute a
  term for each variable.  `subst σ E` replaces each label `A` in `E` by `σ A`. -/

/-- Substitute a term `σ A` for each label `A` in a term. -/
@[expose] public def subst (σ : L → Term L) : Term L → Term L
  | .var A => σ A
  | .one => .one
  | .recip e => .recip (subst σ e)
  | .meet a b => .meet (subst σ a) (subst σ b)
  | .comp a b => .comp (subst σ a) (subst σ b)

/-- Evaluating a substituted term is evaluating the original under the
    reinterpreted labels `A ↦ eval ι (σ A)`. -/
theorem eval_subst {V : Type} (ι : L → V → V → Prop) (σ : L → Term L)
    (E : Term L) (x y : V) :
    eval ι (subst σ E) x y ↔ eval (fun A => eval ι (σ A)) E x y := by
  induction E generalizing x y with
  | var A => exact Iff.rfl
  | one => exact Iff.rfl
  | recip e ih => exact ih y x
  | meet a b iha ihb => exact and_congr (iha x y) (ihb x y)
  | comp a b iha ihb => exact exists_congr (fun z => and_congr (iha x z) (ihb z y))

/-- Validity is closed under substitution: an instance of a valid containment is
    valid.  This is the semantic content of the equational "axiom" rule. -/
theorem HoldsInRel.subst {E₁ E₂ : Term L} (h : HoldsInRel E₁ E₂) (σ : L → Term L) :
    HoldsInRel (subst σ E₁) (subst σ E₂) := by
  intro V ι x y h1
  rw [eval_subst] at h1 ⊢
  exact h (fun A => eval ι (σ A)) x y h1

/-! ## Layer 2 — the equational derivation system

  `Derives Ax E₁ E₂` : the containment `E₁ ⊆ E₂` is derivable from the axiom set
  `Ax` (a finite list of term-pairs) using the proof rules of the equational
  theory of allegories: substitution instances of the axioms, reflexivity,
  transitivity, and the monotone congruences of `°`, `∩`, `;`.  (`∩`, `;` and `°`
  are order-preserving in every allegory, so these congruences are sound.) -/

/-- Derivability of containments from an axiom set `Ax`. -/
inductive Derives (Ax : List (Term L × Term L)) : Term L → Term L → Prop
  | ax {E₁ E₂ : Term L} (σ : L → Term L) : (E₁, E₂) ∈ Ax →
      Derives Ax (subst σ E₁) (subst σ E₂)
  | refl (E : Term L) : Derives Ax E E
  | trans {E₁ E₂ E₃ : Term L} : Derives Ax E₁ E₂ → Derives Ax E₂ E₃ → Derives Ax E₁ E₃
  | recip {E₁ E₂ : Term L} : Derives Ax E₁ E₂ → Derives Ax (.recip E₁) (.recip E₂)
  | meet {E₁ E₁' E₂ E₂' : Term L} : Derives Ax E₁ E₁' → Derives Ax E₂ E₂' →
      Derives Ax (.meet E₁ E₂) (.meet E₁' E₂')
  | comp {E₁ E₁' E₂ E₂' : Term L} : Derives Ax E₁ E₁' → Derives Ax E₂ E₂' →
      Derives Ax (.comp E₁ E₂) (.comp E₁' E₂')

/-! ## Layer 3 — soundness

  Every containment derivable from a *valid* axiom set is true in `Rel(S)`. -/

/-- **Soundness of `Derives`.**  If every axiom of `Ax` is valid in `Rel(S)`,
    every containment derivable from `Ax` is valid in `Rel(S)`. -/
theorem Derives_sound {Ax : List (Term L × Term L)}
    (hAx : ∀ p ∈ Ax, HoldsInRel p.1 p.2) :
    ∀ {E₁ E₂ : Term L}, Derives Ax E₁ E₂ → HoldsInRel E₁ E₂ := by
  intro E₁ E₂ h
  induction h with
  | ax σ hmem => exact HoldsInRel.subst (hAx _ hmem) σ
  | refl E => exact HoldsInRel.refl E
  | trans _ _ ih1 ih2 => exact HoldsInRel.trans ih1 ih2
  | recip _ ih => intro V ι x y h1; exact ih ι y x h1
  | meet _ _ ih1 ih2 => intro V ι x y h1; exact ⟨ih1 ι x y h1.1, ih2 ι x y h1.2⟩
  | comp _ _ ih1 ih2 =>
      intro V ι x y h1; obtain ⟨z, ha, hb⟩ := h1; exact ⟨z, ih1 ι x z ha, ih2 ι z y hb⟩

/-! ### The derivation ⇒ graph-map bridge (Layer 4, ingredient (a) — endpoint form)

  Freyd's counting argument needs to turn a *derivation* into a *graph map*
  `[E₂] → [E₁]`.  The endpoint form is immediate from soundness composed with
  the decision bridge `holdsInRel_iff_hom`: any containment derivable from a
  valid axiom set is realised by an honest graph map on the term-graphs.  (The
  hard, still-open refinement is the *structural* version: unfolding the
  derivation into a CHAIN of graph maps `[E₂] → H₁ → ⋯ → [E₁]` with every
  intermediate `Hᵢ` in the series-parallel suballegory `Ḡ` and each single step
  the graphical interpretation of one axiom-instance — see the OPEN note.) -/

/-- **Derivation ⇒ collapse map.**  If `Ax` is valid and `E₁ ⊆ E₂` is derivable
    from `Ax`, then there is a graph map `[E₂] → [E₁]` — the collapse witnessing
    the containment.  (Soundness `Derives_sound` into the decision bridge.) -/
theorem Derives_hom {Ax : List (Term L × Term L)}
    (hAx : ∀ p ∈ Ax, HoldsInRel p.1 p.2) {E₁ E₂ : Term L}
    (h : Derives Ax E₁ E₂) : Nonempty (Hom (toGraph E₂) (toGraph E₁)) :=
  (holdsInRel_iff_hom E₁ E₂).mp (Derives_sound hAx h)

/-! ### The `B = 0` case of the counting obstruction (Layer 4, seed of (c))

  With NO axioms the derivation system is *pure* (reflexivity, transitivity, and
  the three congruences).  Such a derivation can identify **no** vertex-pair: its
  two sides are forced to be the SAME term.  This is exactly Freyd's "each step
  identifies at most `B(Ax)` pairs" at the extreme `B = 0`, and it already
  refutes completeness of the empty axiom set — the base instance of the
  no-finite-axiomatization phenomenon.  The general finite-`Ax` bound (ingredient
  (b), `B(Ax) > 0`) plus the "no proper partial collapse" heart (ingredient (c))
  are what remain open. -/

/-- **Purity of the axiom-free theory.**  `Derives []` proves a containment only
    between *syntactically equal* terms: it can collapse nothing.  (Induction on
    the derivation; the `ax` rule is unreachable since `_ ∈ []` is false.) -/
theorem Derives_nil_eq {E₁ E₂ : Term L} (h : Derives [] E₁ E₂) : E₁ = E₂ := by
  induction h with
  | ax σ hmem => nomatch hmem
  | refl E => rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | recip _ ih => exact congrArg Term.recip ih
  | meet _ _ ih1 ih2 => exact congr (congrArg Term.meet ih1) ih2
  | comp _ _ ih1 ih2 => exact congr (congrArg Term.comp ih1) ih2

/-! ## Layer 1 — the rhombus family and its validity

  Freyd's §2.158 first explicit example is the "single rhombus" containment
  obtained from the map that collapses the four-vertex square `G₁` onto `G₂` (`s`
  and `t` identified, the two top vertices identified, the two bottom vertices
  identified).  It is the SEPARATED containment

    `1 ∩ (R₁∩R₄°)(R₂∩R₃°)(S₂°∩S₃)(S₁°∩S₄) ⊆ (R₁R₂∩S₁S₂)(R₃R₄∩S₃S₄)`

  (each variable occurs once per side).  We prove it valid in `Rel(S)` directly
  from the semantics; the witnessing midpoint of the right side is the middle
  vertex `p₂` of the left side's four-step walk (with `x = y` supplying the two
  edges that cross the identified `s = t`).  This is the base member (`n = 1`) of
  Freyd's rhombus family. -/

/-- Left side of the single-rhombus containment (`G₂`, the collapsed square). -/
def rhombusLHS (r1 r2 r3 r4 s1 s2 s3 s4 : L) : Term L :=
  .meet .one
    (.comp (.comp (.meet (.var r1) (.recip (.var r4)))
                  (.meet (.var r2) (.recip (.var r3))))
           (.comp (.meet (.recip (.var s2)) (.var s3))
                  (.meet (.recip (.var s1)) (.var s4))))

/-- Right side of the single-rhombus containment (`G₁`, the four distinct
    vertices: two composed lenses `R₁R₂∩S₁S₂` and `R₃R₄∩S₃S₄`). -/
def rhombusRHS (r1 r2 r3 r4 s1 s2 s3 s4 : L) : Term L :=
  .comp (.meet (.comp (.var r1) (.var r2)) (.comp (.var s1) (.var s2)))
        (.meet (.comp (.var r3) (.var r4)) (.comp (.var s3) (.var s4)))

/-- **Layer 1 (base rhombus, `n = 1`).**  The single-rhombus separated
    containment is valid in `Rel(S)` for every `S`.  This is the first member of
    the family whose *infinite* extension defies finite axiomatization. -/
theorem rhombus1_holds (r1 r2 r3 r4 s1 s2 s3 s4 : L) :
    HoldsInRel (rhombusLHS r1 r2 r3 r4 s1 s2 s3 s4)
               (rhombusRHS r1 r2 r3 r4 s1 s2 s3 s4) := by
  intro V ι x y h
  obtain ⟨hxy, z, ⟨w, ⟨hr1, hr4⟩, hr2, hr3⟩, u, ⟨hs2, hs3⟩, hs1, hs4⟩ := h
  subst hxy
  exact ⟨z, ⟨⟨w, hr1, hr2⟩, ⟨u, hs1, hs2⟩⟩, ⟨w, hr3, hr4⟩, ⟨u, hs3, hs4⟩⟩

/-! ### An infinite family of valid separated containments (Layer 1, general `n`)

  We package `rhombus1_holds` into an explicit *infinite* family of valid
  separated containments over the concrete label set `ℕ`, obtained by putting
  `n+1` rhombi in series (`;`) with a fresh block of eight labels per rhombus
  (`8·b … 8·b+7`).  Each member is separated (every label occurs once on each
  side) and valid in `Rel(S)` for every `S`; validity for all `n` is proved by
  induction from the base rhombus and the composition congruence
  `HoldsInRel.comp`.  This realises Freyd's "there is no finite bound: the family
  of rhombus containments is infinite" at the level of *validity* (Layer 1).

  The genuine **hard** family of §2.158 — the single `n`-fold rhombus chain
  whose collapse map identifies `Θ(n)` vertex-pairs *simultaneously* — is a
  *connected, entangled* graph, not a series bouquet; the series family below is
  derivable rhombus-by-rhombus once one rhombus is, so it does NOT witness
  `RhombusHard`.  The entangled family is built next (`entL`, `entR`,
  reconstructed from the book's figures); see the OPEN note at the end for what
  remains of the counting argument. -/

/-- The `i`-th of the eight labels in the `b`-th fresh block.  (Labels live in
    `Nat`; each rhombus gets a disjoint block, so the family is *separated*.) -/
def lbl (b i : Nat) : Nat := 8 * b + i

/-- The base rhombus LHS on the `b`-th fresh block of eight `Nat`-labels. -/
def rhL1 (b : Nat) : Term Nat :=
  rhombusLHS (lbl b 0) (lbl b 1) (lbl b 2) (lbl b 3)
             (lbl b 4) (lbl b 5) (lbl b 6) (lbl b 7)

/-- The base rhombus RHS on the `b`-th fresh block of eight `Nat`-labels. -/
def rhR1 (b : Nat) : Term Nat :=
  rhombusRHS (lbl b 0) (lbl b 1) (lbl b 2) (lbl b 3)
             (lbl b 4) (lbl b 5) (lbl b 6) (lbl b 7)

/-- LHS of the `n`-fold series rhombus: `n+1` collapsed rhombi composed in `;`. -/
def ladderL : Nat → Term Nat
  | 0 => rhL1 0
  | n+1 => .comp (ladderL n) (rhL1 (n+1))

/-- RHS of the `n`-fold series rhombus: `n+1` expanded rhombi composed in `;`. -/
def ladderR : Nat → Term Nat
  | 0 => rhR1 0
  | n+1 => .comp (ladderR n) (rhR1 (n+1))

/-- **Layer 1, all `n`.**  Every member of the infinite series-rhombus family is
    a valid separated containment in `Rel(S)`.  (Base = `rhombus1_holds`; step =
    `HoldsInRel.comp`.)  This supplies the `hvalid` hypothesis of
    `no_finite_axiomatization` for the family `ladderL, ladderR`. -/
theorem ladder_holds : ∀ n : Nat, HoldsInRel (ladderL n) (ladderR n) := by
  intro n
  induction n with
  | zero => exact rhombus1_holds _ _ _ _ _ _ _ _
  | succ m ih => exact HoldsInRel.comp ih (rhombus1_holds _ _ _ _ _ _ _ _)

/-! ## Layer 1″ — the ENTANGLED rhombus family (Freyd's `G₁ → G₂`, general `n`)

  Freyd's counting family (§2.158, last two pages, figures on pp. 18–19 of the
  chapter scan).  `G₁` is a CHAIN of `k` rhombi sharing corner vertices
  `v₀ … v_k` (marks `s = v₀`, `t = v_k`): rhombus `i` has a top midpoint `pᵢ`
  with the two `R`-edges `aᵢ : vᵢ → pᵢ`, `bᵢ : pᵢ → vᵢ₊₁` and a bottom midpoint
  `qᵢ` with the two `S`-edges `cᵢ : vᵢ → qᵢ`, `dᵢ : qᵢ → vᵢ₊₁`.  `G₂` is the
  collapse identifying `s` with `t`, the whole top row `p₀ = ⋯ = p_{k-1}`, and
  the whole bottom row `q₀ = ⋯ = q_{k-1}` — i.e. `2k - 1` vertex-pair
  identifications at once.  The containment `[G₂-term] ⊆ [G₁-term]` is
  separated, and valid in `Rel(S)` (`ent_holds` below).

  `G₁`-term: the composite of the `k` lenses `aᵢbᵢ ∩ cᵢdᵢ`.  `G₂`-term (the
  book's display): a first border factor `a₀ ∩ b_max°` (the edges joining `s̄`
  to the collapsed top vertex `P`), a big MEET of interior *branches* — branch
  `j` is the two-step path `P → v_{j+1} → Q` bundling the four `G₁`-edges
  incident to the interior chain vertex `v_{j+1}`, namely
  `(b_j ∩ a_{j+1}°)(d_j° ∩ c_{j+1})` — and a last border factor `c₀° ∩ d_max`,
  all inside `1 ∩ [·]` (which glues `s = t`).

  Reconstruction note: the book prints the labels of the `n`-rhombus chain as
  `R₀ … Rₙ, S₀ … Sₙ`, which cannot be literal — the chain has `2n` top edges,
  and reusing a label across consecutive factors of the right side would break
  the separatedness the argument demands.  We use a fresh block of four labels
  per rhombus and fix the shape against the exact two-rhombus display
  `1 ∩ (R₁ ∩ R₄°)(R₂ ∩ R₃°)(S₂° ∩ S₃)(S₁° ∩ S₄) ⊆ (R₁R₂ ∩ S₁S₂)(R₃R₄ ∩ S₃S₄)`,
  which is the `n = 0` member (`ent_book0` below pins the right side literally;
  the left side agrees up to `;`-association).

  `entL n ⊆ entR n` has `n+2` rhombi, so the family starts at the book's
  two-rhombus example. -/

/-- Top-in label of the `i`-th rhombus (edge `vᵢ → pᵢ`; the book's `R₂ᵢ₊₁`). -/
@[expose] public def aL (i : Nat) : Nat := 4 * i
/-- Top-out label of the `i`-th rhombus (edge `pᵢ → vᵢ₊₁`; the book's `R₂ᵢ₊₂`). -/
@[expose] public def bL (i : Nat) : Nat := 4 * i + 1
/-- Bottom-in label of the `i`-th rhombus (edge `vᵢ → qᵢ`; the book's `S₂ᵢ₊₁`). -/
@[expose] public def cL (i : Nat) : Nat := 4 * i + 2
/-- Bottom-out label of the `i`-th rhombus (edge `qᵢ → vᵢ₊₁`; the book's `S₂ᵢ₊₂`). -/
@[expose] public def dL (i : Nat) : Nat := 4 * i + 3

/-- Arithmetic injectivity shared by the four stride-four label families. -/
@[expose] public def strideFour_injective (r : Nat) : Function.Injective (fun i => 4 * i + r) := by
  intro i j h
  change 4 * i + r = 4 * j + r at h
  omega
/-- The `i`-th rhombus as a term: the lens `aᵢbᵢ ∩ cᵢdᵢ`. -/
@[expose] public def lens (i : Nat) : Term Nat :=
  .meet (.comp (.var (aL i)) (.var (bL i))) (.comp (.var (cL i)) (.var (dL i)))

/-- `lens 0 ; lens 1 ; ⋯ ; lens k` — the `(k+1)`-rhombus chain `G₁` as a term. -/
@[expose] public def chainT : Nat → Term Nat
  | 0 => lens 0
  | k+1 => .comp (chainT k) (lens (k+1))

/-- Right side of the `n`-th entangled containment: the `(n+2)`-rhombus chain. -/
@[expose] public def entR (n : Nat) : Term Nat := chainT (n+1)

/-- The `j`-th interior branch of the collapse `G₂`: the two-step path
    `P → v_{j+1} → Q` bundling the four chain edges at the interior vertex
    `v_{j+1}`, i.e. `(b_j ∩ a_{j+1}°)(d_j° ∩ c_{j+1})`. -/
@[expose] public def branch (j : Nat) : Term Nat :=
  .comp (.meet (.var (bL j)) (.recip (.var (aL (j+1)))))
        (.meet (.recip (.var (dL j))) (.var (cL (j+1))))

/-- `branch 0 ∩ ⋯ ∩ branch k` — the book's big `⋂` of interior branches. -/
@[expose] public def mids : Nat → Term Nat
  | 0 => branch 0
  | k+1 => .meet (mids k) (branch (k+1))

/-- Left side of the `n`-th entangled containment: the collapse `G₂` of the
    `(n+2)`-rhombus chain, `1 ∩ (a₀ ∩ b_{n+1}°) ; mids n ; (c₀° ∩ d_{n+1})`. -/
@[expose] public def entL (n : Nat) : Term Nat :=
  .meet .one
    (.comp (.meet (.var (aL 0)) (.recip (.var (bL (n+1)))))
      (.comp (mids n)
        (.meet (.recip (.var (cL 0))) (.var (dL (n+1))))))

/-- Sanity pin: the `n = 0` right side is literally the book's two-rhombus
    right side `(R₁R₂ ∩ S₁S₂)(R₃R₄ ∩ S₃S₄)`. -/
theorem ent_book0 :
    entR 0 = rhombusRHS (aL 0) (bL 0) (aL 1) (bL 1) (cL 0) (dL 0) (cL 1) (dL 1) :=
  rfl

/-- **Chain builder** for `ent_holds`: interior branches `0 … k` between the
    collapsed top vertex `P` and bottom vertex `Q`, plus the two entry edges
    `a₀ : x → P`, `c₀ : x → Q`, assemble the lens chain `lens 0 ; ⋯ ; lens k`
    from `x` to the `k`-th interior vertex, handing on that vertex's exit edges
    `a_{k+1}, c_{k+1}` for the next lens.  (This is the collapse-preimage walk:
    the witness for every top midpoint is `P`, for every bottom midpoint `Q`.) -/
theorem chainT_build {V : Type} (ι : Nat → V → V → Prop) {x P Q : V}
    (ha0 : ι (aL 0) x P) (hc0 : ι (cL 0) x Q) :
    ∀ k, eval ι (mids k) P Q →
      ∃ w, eval ι (chainT k) x w ∧ ι (aL (k+1)) w P ∧ ι (cL (k+1)) w Q := by
  intro k
  induction k with
  | zero =>
    rintro ⟨v, ⟨hb, ha⟩, hd, hc⟩
    exact ⟨v, ⟨⟨P, ha0, hb⟩, ⟨Q, hc0, hd⟩⟩, ha, hc⟩
  | succ m ih =>
    rintro ⟨hmid, v, ⟨hb, ha⟩, hd, hc⟩
    obtain ⟨w, hch, haw, hcw⟩ := ih hmid
    exact ⟨v, ⟨w, hch, ⟨P, haw, hb⟩, ⟨Q, hcw, hd⟩⟩, ha, hc⟩

/-- **Layer 1″ (entangled family): validity in `Rel(S)`, all `n`.**  This is
    the `hvalid` input of `no_finite_axiomatization` for the entangled family.
    Unlike `ladder_holds` the proof is a genuine induction along the collapsed
    graph (`chainT_build`), not a `.comp` of independent single rhombi. -/
theorem ent_holds (n : Nat) : HoldsInRel (entL n) (entR n) := by
  intro V ι x y h
  obtain ⟨hxy, P, ⟨ha0, hbn⟩, Q, hmid, hc0, hdn⟩ := h
  subst hxy
  obtain ⟨w, hch, haw, hcw⟩ := chainT_build ι ha0 hc0 n hmid
  exact ⟨w, hch, ⟨P, haw, hbn⟩, ⟨Q, hcw, hdn⟩⟩

/-! ## ERRATUM (machine-checked) — the book's two-rhombus example IS derivable

  §2.158 (p. 18 of the chapter scan) claims that the two-rhombus containment

    `1 ∩ (R₁∩R₄°)(R₂∩R₃°)(S₂°∩S₃)(S₁°∩S₄) ⊆ (R₁R₂∩S₁S₂)(R₃R₄∩S₃S₄)`

  "is not a consequence of the definition of allegories", arguing: (i) `G₂` is
  obtained from `G₁` by identifying three vertex pairs (`{s,t}`, top pair,
  bottom pair); (ii) *"if one identifies any one or any two of those pairs of
  vertices, the resulting graph is not in `Ḡ`"*; (iii) each defining
  containment identifies at most one pair, so a derivation chain — whose
  intermediate graphs all lie in `Ḡ` — cannot reach the three-pair collapse.

  Claim (ii) is FALSE for the subsets containing `{s,t}`, and with it the
  conclusion:

  * the `{s,t}`-only collapse of `G₁` is the graph of the term
    `1 ∩ (R₁R₂∩S₁S₂)(R₃R₄∩S₃S₄)` — in `Ḡ`;
  * the `{s,t}`+top-pair collapse is the graph of the term
    `1 ∩ (R₁∩R₄°)(R₂∩R₃°)((S₂°S₁°)∩(S₃S₄))` — in `Ḡ`.

  Walking DOWN this ladder of partial collapses, one pair per step, yields an
  honest derivation, machine-checked below (`ent0_derivable`) in the calculus
  `Derives` from the finite valid axiom list `allegoryAxioms`:

    `entL 0 ⊆ [semidistrib] 1∩(R₁∩R₄°)(R₂∩R₃°)((S₂°S₁°)∩(S₃S₄))`
    `      ⊆ [semidistrib] 1∩((R₁R₂∩R₄°R₃°)((S₂°S₁°)∩(S₃S₄))) = 1∩(X;Y)`
    `      ⊆ [cut law]     (X∩Y°)(Y∩X°) ⊆ [∩-elim, ° computation] entR 0`

  where `X = R₁R₂∩(R₃R₄)°`, `Y = (S₁S₂)°∩S₃S₄`, and the *cut law*
  `1∩XY ⊆ (X∩Y°)(Y∩X°)` (`dCut`) is derived from the modular law and its
  mirror.  Every axiom in `allegoryAxioms` is valid in `Rel(S)`
  (`allegoryAxioms_valid`), is a standard consequence of the definition of
  allegories, and — the pointed refutation of (iii)'s premise — has a graph
  interpretation identifying AT MOST ONE vertex pair.

  Consequences for §2.158: the two-rhombus example does not witness the
  metatheorem; the smallest candidate is the THREE-rhombus chain, whose
  `{s,t}`-collapse `1 ∩ (lens₀ lens₁ lens₂)` is still in `Ḡ` but whose further
  proper partial collapses contain a `K₄` minor (term graphs have treewidth
  ≤ 2), so the jump from the `{s,t}`-collapse to the full collapse needs
  `2k - 2 ≥ 4` simultaneous identifications.  The corrected counting argument
  survives for `n` rhombi with `2n - 2` exceeding the per-axiom bound; see the
  OPEN note. -/

/-- A finite list of containments, each **valid in `Rel(S)`**
    (`allegoryAxioms_valid`) and each a standard consequence of the definition
    of allegories: `∩`-semilattice laws, `;`-monoid laws, `°`-computation laws,
    Freyd's recast separated semidistributive law, and the modular law with its
    mirror form.  Graphically each member identifies at most one vertex pair. -/
@[expose] public def allegoryAxioms : List (Term Nat × Term Nat) :=
  [ (.meet (.var 0) (.var 1), .var 0),                                      -- ∩-elim-l
    (.meet (.var 0) (.var 1), .var 1),                                      -- ∩-elim-r
    (.meet (.var 0) (.var 1), .meet (.var 1) (.var 0)),                     -- ∩-comm
    (.meet (.var 0) (.meet (.var 1) (.var 2)),
      .meet (.meet (.var 0) (.var 1)) (.var 2)),                            -- ∩-assoc
    (.one, .meet .one .one),                                                -- 1 ⊆ 1∩1
    (.comp (.comp (.var 0) (.var 1)) (.var 2),
      .comp (.var 0) (.comp (.var 1) (.var 2))),                            -- ;-assoc →
    (.comp (.var 0) (.comp (.var 1) (.var 2)),
      .comp (.comp (.var 0) (.var 1)) (.var 2)),                            -- ;-assoc ←
    (.comp .one (.var 0), .var 0),                                          -- 1;X ⊆ X
    (.comp (.var 0) .one, .var 0),                                          -- X;1 ⊆ X
    (.recip (.comp (.var 0) (.var 1)),
      .comp (.recip (.var 1)) (.recip (.var 0))),                           -- (XY)° ⊆ Y°X°
    (.recip (.recip (.var 0)), .var 0),                                     -- X°° ⊆ X
    (.comp (.meet (.var 0) (.var 1)) (.meet (.var 2) (.var 3)),
      .meet (.comp (.var 0) (.var 2)) (.comp (.var 1) (.var 3))),           -- semidistrib
    (.meet (.comp (.var 0) (.var 1)) (.var 2),
      .comp (.meet (.var 0) (.comp (.var 2) (.recip (.var 1)))) (.var 1)),  -- modular
    (.meet (.comp (.var 0) (.var 1)) (.var 2),
      .comp (.var 0) (.meet (.var 1) (.comp (.recip (.var 0)) (.var 2)))) ] -- mirror modular

/-- Every member of `allegoryAxioms` is valid in `Rel(S)`. -/
theorem allegoryAxioms_valid : ∀ p ∈ allegoryAxioms, HoldsInRel p.1 p.2 := by
  intro p hp
  simp only [allegoryAxioms, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact fun ι x y h => h.1
  · exact fun ι x y h => h.2
  · exact fun ι x y h => ⟨h.2, h.1⟩
  · exact fun ι x y h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  · exact fun ι x y h => ⟨h, h⟩
  · rintro V ι x y ⟨z, ⟨w, hx, hy⟩, hz⟩; exact ⟨w, hx, z, hy, hz⟩
  · rintro V ι x y ⟨w, hx, z, hy, hz⟩; exact ⟨z, ⟨w, hx, hy⟩, hz⟩
  · rintro V ι x y ⟨z, rfl, h⟩; exact h
  · rintro V ι x y ⟨z, h, rfl⟩; exact h
  · rintro V ι x y ⟨z, h1, h2⟩; exact ⟨z, h2, h1⟩
  · exact fun ι x y h => h
  · rintro V ι x y ⟨z, ⟨h0, h1⟩, h2, h3⟩; exact ⟨⟨z, h0, h2⟩, ⟨z, h1, h3⟩⟩
  · rintro V ι x y ⟨⟨z, h0, h1⟩, h2⟩; exact ⟨z, ⟨h0, y, h2, h1⟩, h1⟩
  · rintro V ι x y ⟨⟨z, h0, h1⟩, h2⟩; exact ⟨z, h0, h1, x, h0, h2⟩

/-! ### The axioms, applied to arbitrary terms (substitution sugar) -/

theorem dMeetL (X Y : Term Nat) : Derives allegoryAxioms (.meet X Y) X :=
  Derives.ax (E₁ := .meet (.var 0) (.var 1)) (E₂ := .var 0)
    (fun k => match k with | 0 => X | _ => Y) (by simp [allegoryAxioms])

theorem dMeetR (X Y : Term Nat) : Derives allegoryAxioms (.meet X Y) Y :=
  Derives.ax (E₁ := .meet (.var 0) (.var 1)) (E₂ := .var 1)
    (fun k => match k with | 0 => X | _ => Y) (by simp [allegoryAxioms])

theorem dMeetComm (X Y : Term Nat) :
    Derives allegoryAxioms (.meet X Y) (.meet Y X) :=
  Derives.ax (E₁ := .meet (.var 0) (.var 1)) (E₂ := .meet (.var 1) (.var 0))
    (fun k => match k with | 0 => X | _ => Y) (by simp [allegoryAxioms])

theorem dMeetAssoc (X Y Z : Term Nat) :
    Derives allegoryAxioms (.meet X (.meet Y Z)) (.meet (.meet X Y) Z) :=
  Derives.ax (E₁ := .meet (.var 0) (.meet (.var 1) (.var 2)))
    (E₂ := .meet (.meet (.var 0) (.var 1)) (.var 2))
    (fun k => match k with | 0 => X | 1 => Y | _ => Z) (by simp [allegoryAxioms])

theorem dOneDiag : Derives allegoryAxioms (.one : Term Nat) (.meet .one .one) :=
  Derives.ax (E₁ := .one) (E₂ := .meet .one .one)
    (fun _ => .one) (by simp [allegoryAxioms])

theorem dCompAssocR (X Y Z : Term Nat) :
    Derives allegoryAxioms (.comp (.comp X Y) Z) (.comp X (.comp Y Z)) :=
  Derives.ax (E₁ := .comp (.comp (.var 0) (.var 1)) (.var 2))
    (E₂ := .comp (.var 0) (.comp (.var 1) (.var 2)))
    (fun k => match k with | 0 => X | 1 => Y | _ => Z) (by simp [allegoryAxioms])

theorem dCompAssocL (X Y Z : Term Nat) :
    Derives allegoryAxioms (.comp X (.comp Y Z)) (.comp (.comp X Y) Z) :=
  Derives.ax (E₁ := .comp (.var 0) (.comp (.var 1) (.var 2)))
    (E₂ := .comp (.comp (.var 0) (.var 1)) (.var 2))
    (fun k => match k with | 0 => X | 1 => Y | _ => Z) (by simp [allegoryAxioms])

theorem dOneComp (X : Term Nat) : Derives allegoryAxioms (.comp .one X) X :=
  Derives.ax (E₁ := .comp .one (.var 0)) (E₂ := .var 0)
    (fun _ => X) (by simp [allegoryAxioms])

theorem dCompOne (X : Term Nat) : Derives allegoryAxioms (.comp X .one) X :=
  Derives.ax (E₁ := .comp (.var 0) .one) (E₂ := .var 0)
    (fun _ => X) (by simp [allegoryAxioms])

theorem dRecipComp (X Y : Term Nat) :
    Derives allegoryAxioms (.recip (.comp X Y)) (.comp (.recip Y) (.recip X)) :=
  Derives.ax (E₁ := .recip (.comp (.var 0) (.var 1)))
    (E₂ := .comp (.recip (.var 1)) (.recip (.var 0)))
    (fun k => match k with | 0 => X | _ => Y) (by simp [allegoryAxioms])

theorem dRecipRecip (X : Term Nat) : Derives allegoryAxioms (.recip (.recip X)) X :=
  Derives.ax (E₁ := .recip (.recip (.var 0))) (E₂ := .var 0)
    (fun _ => X) (by simp [allegoryAxioms])

theorem dSemidist (P Q R S : Term Nat) :
    Derives allegoryAxioms (.comp (.meet P Q) (.meet R S))
      (.meet (.comp P R) (.comp Q S)) :=
  Derives.ax (E₁ := .comp (.meet (.var 0) (.var 1)) (.meet (.var 2) (.var 3)))
    (E₂ := .meet (.comp (.var 0) (.var 2)) (.comp (.var 1) (.var 3)))
    (fun k => match k with | 0 => P | 1 => Q | 2 => R | _ => S)
    (by simp [allegoryAxioms])

theorem dModular (R S T : Term Nat) :
    Derives allegoryAxioms (.meet (.comp R S) T)
      (.comp (.meet R (.comp T (.recip S))) S) :=
  Derives.ax (E₁ := .meet (.comp (.var 0) (.var 1)) (.var 2))
    (E₂ := .comp (.meet (.var 0) (.comp (.var 2) (.recip (.var 1)))) (.var 1))
    (fun k => match k with | 0 => R | 1 => S | _ => T) (by simp [allegoryAxioms])

theorem dMModular (R S T : Term Nat) :
    Derives allegoryAxioms (.meet (.comp R S) T)
      (.comp R (.meet S (.comp (.recip R) T))) :=
  Derives.ax (E₁ := .meet (.comp (.var 0) (.var 1)) (.var 2))
    (E₂ := .comp (.var 0) (.meet (.var 1) (.comp (.recip (.var 0)) (.var 2))))
    (fun k => match k with | 0 => R | 1 => S | _ => T) (by simp [allegoryAxioms])

/-- **The derived CUT law** `1 ∩ XY ⊆ (X ∩ Y°)(Y ∩ X°)` — the move Freyd's
    counting overlooked.  Graphically it cuts the loop `1 ∩ XY` open at the
    marked vertex, identifying the pair `{s, t}` of `(X∩Y°)(Y∩X°)`'s graph —
    ONE vertex pair.  Derivation: `1∩XY ⊆ (XY∩1)∩1` (∩-laws), modular law with
    `T = 1` inside the ambient `∩1`, then the mirror modular law with `T = 1`. -/
theorem dCut (X Y : Term Nat) :
    Derives allegoryAxioms (.meet .one (.comp X Y))
      (.comp (.meet X (.recip Y)) (.meet Y (.recip X))) := by
  -- 1∩XY ⊆ XY∩1 ⊆ XY∩(1∩1) ⊆ (XY∩1)∩1
  have h1 : Derives allegoryAxioms (.meet .one (.comp X Y))
      (.meet (.meet (.comp X Y) .one) .one) :=
    (dMeetComm _ _).trans (((Derives.refl _).meet dOneDiag).trans (dMeetAssoc _ _ _))
  -- modular (T = 1) in the ambient ∩1, then 1·Y° ⊆ Y°
  have h2 : Derives allegoryAxioms (.meet (.comp X Y) .one)
      (.comp (.meet X (.recip Y)) Y) :=
    (dModular X Y .one).trans
      (((Derives.refl X).meet (dOneComp (.recip Y))).comp (Derives.refl Y))
  -- mirror modular (T = 1), then (X∩Y°)°·1 ⊆ (X∩Y°)° ⊆ X°
  have h5 : Derives allegoryAxioms
      (.comp (.recip (.meet X (.recip Y))) .one) (.recip X) :=
    (dCompOne _).trans (Derives.recip (dMeetL X (.recip Y)))
  exact h1.trans ((h2.meet (Derives.refl .one)).trans
    ((dMModular (.meet X (.recip Y)) Y .one).trans
      ((Derives.refl (.meet X (.recip Y))).comp ((Derives.refl Y).meet h5))))

/-- The four two-edge factors of `entL 0`'s collapsed walk (in order). -/
private def ef₁ : Term Nat := .meet (.var (aL 0)) (.recip (.var (bL 1)))
private def ef₂ : Term Nat := .meet (.var (bL 0)) (.recip (.var (aL 1)))
private def ef₃ : Term Nat := .meet (.recip (.var (dL 0))) (.var (cL 1))
private def ef₄ : Term Nat := .meet (.recip (.var (cL 0))) (.var (dL 1))
/-- The composite sides `A = R₁R₂`, `B' = (R₃R₄)°`, `C' = (S₁S₂)°`, `D = S₃S₄`. -/
private def eA : Term Nat := .comp (.var (aL 0)) (.var (bL 0))
private def eB : Term Nat := .comp (.recip (.var (bL 1))) (.recip (.var (aL 1)))
private def eC : Term Nat := .comp (.recip (.var (dL 0))) (.recip (.var (cL 0)))
private def eD : Term Nat := .comp (.var (cL 1)) (.var (dL 1))

/-- **ERRATUM THEOREM.**  The book's two-rhombus separated containment (= the
    `n = 0` member of the entangled family) IS derivable from the finite valid
    axiom list `allegoryAxioms` — contradicting §2.158's claim that it "is not
    a consequence of the definition of allegories".  See the section header for
    where the book's counting argument breaks (its claim (ii)) and why the
    corrected minimal example needs at least three rhombi. -/
theorem ent0_derivable : Derives allegoryAxioms (entL 0) (entR 0) := by
  show Derives allegoryAxioms
    (.meet .one (.comp ef₁ (.comp (.comp ef₂ ef₃) ef₄)))
    (.comp (lens 0) (lens 1))
  -- reassociate ef₁((ef₂ef₃)ef₄) to (ef₁ef₂)(ef₃ef₄), then semidistribute both
  have t1 : Derives allegoryAxioms (.comp ef₁ (.comp (.comp ef₂ ef₃) ef₄))
      (.comp (.comp ef₁ ef₂) (.comp ef₃ ef₄)) :=
    ((Derives.refl ef₁).comp (dCompAssocR ef₂ ef₃ ef₄)).trans
      (dCompAssocL ef₁ ef₂ (.comp ef₃ ef₄))
  have sd1 : Derives allegoryAxioms (.comp ef₁ ef₂) (.meet eA eB) :=
    dSemidist (.var (aL 0)) (.recip (.var (bL 1))) (.var (bL 0)) (.recip (.var (aL 1)))
  have sd2 : Derives allegoryAxioms (.comp ef₃ ef₄) (.meet eC eD) :=
    dSemidist (.recip (.var (dL 0))) (.var (cL 1)) (.recip (.var (cL 0))) (.var (dL 1))
  -- first factor of the cut: X ∩ Y° ⊆ R₁R₂ ∩ S₁S₂ = lens 0
  have fst : Derives allegoryAxioms
      (.meet (.meet eA eB) (.recip (.meet eC eD))) (lens 0) :=
    (dMeetL eA eB).meet
      ((Derives.recip (dMeetL eC eD)).trans
        ((dRecipComp (.recip (.var (dL 0))) (.recip (.var (cL 0)))).trans
          ((dRecipRecip (.var (cL 0))).comp (dRecipRecip (.var (dL 0))))))
  -- second factor of the cut: Y ∩ X° ⊆ R₃R₄ ∩ S₃S₄ = lens 1
  have snd : Derives allegoryAxioms
      (.meet (.meet eC eD) (.recip (.meet eA eB))) (lens 1) :=
    ((dMeetR eC eD).meet
      ((Derives.recip (dMeetR eA eB)).trans
        ((dRecipComp (.recip (.var (bL 1))) (.recip (.var (aL 1)))).trans
          ((dRecipRecip (.var (aL 1))).comp (dRecipRecip (.var (bL 1))))))).trans
      (dMeetComm eD (.comp (.var (aL 1)) (.var (bL 1))))
  exact ((Derives.refl .one).meet (t1.trans (sd1.comp sd2))).trans
    ((dCut (.meet eA eB) (.meet eC eD)).trans (fst.comp snd))

/-! ## Layer 4a — CHAIN NORMALIZATION: derivations are single-rewrite chains

  Freyd's counting argument opens: "we would obtain a sequence of containments,
  each of which is a direct instance of one of the defining containments, which
  sequence would — by transitivity of containment — yield the above
  containment."  That is a proof-theoretic normal form, proved here: every
  derivation in the congruence calculus `Derives` flattens into a CHAIN of
  single rewrites, each replacing one axiom instance inside one one-hole
  context (every position is positive, since `°`, `∩`, `;` are all monotone).

  `derives_iff_chain` is the *syntactic* half of Freyd's "sequence of maps
  `G₁ → H₁ → ⋯ → Hₙ → G₂` where each `Hᵢ` is in `Ḡ`": the intermediate stages
  of the chain are TERMS, so their graphs are automatically in `Ḡ`, and each
  link `Fᵢ ⊆ Fᵢ₊₁` is one axiom instance in one context, hence (for valid
  axioms, via `Derives_hom` on `Step.toDerives`) one graph map
  `[Fᵢ₊₁] → [Fᵢ]`. -/

/-- One-hole contexts over `Term L`. -/
public inductive Ctx (L : Type) where
  | hole : Ctx L
  | recip : Ctx L → Ctx L
  | meetL : Ctx L → Term L → Ctx L
  | meetR : Term L → Ctx L → Ctx L
  | compL : Ctx L → Term L → Ctx L
  | compR : Term L → Ctx L → Ctx L

/-- Plug a term into the hole. -/
@[expose] public def Ctx.fill : Ctx L → Term L → Term L
  | .hole, E => E
  | .recip C, E => .recip (C.fill E)
  | .meetL C T, E => .meet (C.fill E) T
  | .meetR T C, E => .meet T (C.fill E)
  | .compL C T, E => .comp (C.fill E) T
  | .compR T C, E => .comp T (C.fill E)

/-- Plug a context into the hole of another context. -/
def Ctx.plug : Ctx L → Ctx L → Ctx L
  | .hole, D => D
  | .recip C, D => .recip (C.plug D)
  | .meetL C T, D => .meetL (C.plug D) T
  | .meetR T C, D => .meetR T (C.plug D)
  | .compL C T, D => .compL (C.plug D) T
  | .compR T C, D => .compR T (C.plug D)

/-- Context composition is substitution of fillings. -/
theorem Ctx.fill_plug (C D : Ctx L) (E : Term L) :
    (C.plug D).fill E = C.fill (D.fill E) := by
  induction C with
  | hole => rfl
  | recip C ih => exact congrArg Term.recip ih
  | meetL C T ih => exact congrArg (fun t => Term.meet t T) ih
  | meetR T C ih => exact congrArg (fun t => Term.meet T t) ih
  | compL C T ih => exact congrArg (fun t => Term.comp t T) ih
  | compR T C ih => exact congrArg (fun t => Term.comp T t) ih

/-- A SINGLE REWRITE: one substitution instance of one axiom of `Ax`, in one
    one-hole context — Freyd's "direct instance of one of the defining
    containments". -/
public inductive Step (Ax : List (Term L × Term L)) : Term L → Term L → Prop
  | mk {A B : Term L} (C : Ctx L) (σ : L → Term L) :
      (A, B) ∈ Ax → Step Ax (C.fill (subst σ A)) (C.fill (subst σ B))

/-- Chains of single rewrites: the reflexive-transitive closure of `Step`. -/
inductive Chain (Ax : List (Term L × Term L)) : Term L → Term L → Prop
  | refl (E : Term L) : Chain Ax E E
  | cons {E₁ E₂ E₃ : Term L} : Step Ax E₁ E₂ → Chain Ax E₂ E₃ → Chain Ax E₁ E₃

theorem Chain.trans {Ax : List (Term L × Term L)} {E₁ E₂ E₃ : Term L}
    (h₁ : Chain Ax E₁ E₂) : Chain Ax E₂ E₃ → Chain Ax E₁ E₃ := by
  induction h₁ with
  | refl E => exact id
  | cons s _ ih => exact fun h₂ => .cons s (ih h₂)

/-- A single rewrite inside a further context is a single rewrite. -/
theorem Step.inCtx {Ax : List (Term L × Term L)} {E F : Term L} (C : Ctx L)
    (h : Step Ax E F) : Step Ax (C.fill E) (C.fill F) := by
  cases h with
  | mk D σ hmem =>
      rw [← Ctx.fill_plug, ← Ctx.fill_plug]
      exact .mk (C.plug D) σ hmem

/-- Chains are stable under contexts (every position is monotone). -/
theorem Chain.inCtx {Ax : List (Term L × Term L)} {E F : Term L} (C : Ctx L)
    (h : Chain Ax E F) : Chain Ax (C.fill E) (C.fill F) := by
  induction h with
  | refl E => exact .refl _
  | cons s _ ih => exact .cons (s.inCtx C) ih

/-- **Derivations flatten to chains.**  Congruence steps map through the
    matching one-hole context, one argument at a time. -/
theorem Derives.toChain {Ax : List (Term L × Term L)} {E F : Term L}
    (h : Derives Ax E F) : Chain Ax E F := by
  induction h with
  | ax σ hmem => exact .cons (.mk .hole σ hmem) (.refl _)
  | refl E => exact .refl E
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | recip _ ih => exact ih.inCtx (.recip .hole)
  | @meet E₁ E₁' E₂ E₂' _ _ ih₁ ih₂ =>
      exact (ih₁.inCtx (.meetL .hole E₂)).trans (ih₂.inCtx (.meetR E₁' .hole))
  | @comp E₁ E₁' E₂ E₂' _ _ ih₁ ih₂ =>
      exact (ih₁.inCtx (.compL .hole E₂)).trans (ih₂.inCtx (.compR E₁' .hole))

/-- A single rewrite is derivable (structural induction on the context). -/
theorem Step.toDerives {Ax : List (Term L × Term L)} {E F : Term L}
    (h : Step Ax E F) : Derives Ax E F := by
  cases h with
  | mk C σ hmem =>
      induction C with
      | hole => exact .ax σ hmem
      | recip C ih => exact .recip ih
      | meetL C T ih => exact .meet ih (.refl T)
      | meetR T C ih => exact .meet (.refl T) ih
      | compL C T ih => exact .comp ih (.refl T)
      | compR T C ih => exact .comp (.refl T) ih

/-- Chains are derivable. -/
theorem Chain.toDerives {Ax : List (Term L × Term L)} {E F : Term L}
    (h : Chain Ax E F) : Derives Ax E F := by
  induction h with
  | refl E => exact .refl E
  | cons s _ ih => exact (s.toDerives).trans ih

/-- **CHAIN NORMALIZATION.**  A containment is derivable from `Ax` iff it is
    reachable by a finite chain of single axiom-instance rewrites.  This is the
    exact formal content of Freyd's opening reduction of the §2.158 counting
    argument, and the entry point for any future proof of `RhombusHard`: it
    turns an arbitrary derivation into a chain
    `entL n = F₀ ⊆ F₁ ⊆ ⋯ ⊆ F_m = entR n` of TERMS (graphs in `Ḡ`) with each
    link a single bounded rewrite. -/
theorem derives_iff_chain {Ax : List (Term L × Term L)} {E F : Term L} :
    Derives Ax E F ↔ Chain Ax E F :=
  ⟨Derives.toChain, Chain.toDerives⟩

/-- A single rewrite from a valid axiom set is a valid containment (so, via
    `holdsInRel_iff_hom`, each chain link carries a graph map `[F] → [E]`). -/
theorem Step_sound {Ax : List (Term L × Term L)}
    (hAx : ∀ p ∈ Ax, HoldsInRel p.1 p.2) {E F : Term L}
    (h : Step Ax E F) : HoldsInRel E F :=
  Derives_sound hAx h.toDerives

/-- Helper for `Chain.exists_jump`, with everything the induction needs riding
    in the motive. -/
theorem Chain.exists_jump_aux {Ax : List (Term L × Term L)} {P Q : Term L → Prop} :
    ∀ {E' Eω : Term L}, Chain Ax E' Eω → ∀ {E₀ : Term L},
      (∀ p ∈ Ax, HoldsInRel p.1 p.2) →
      (∀ E, HoldsInRel E₀ E → HoldsInRel E Eω → P E ∨ Q E) →
      HoldsInRel E₀ E' → P E' → ¬ P Eω →
      ∃ E F, Step Ax E F ∧ P E ∧ Q F ∧ HoldsInRel E₀ E ∧ HoldsInRel F Eω := by
  intro E' Eω h
  induction h with
  | refl E => intro E₀ _ _ _ hPE hnP; exact absurd hPE hnP
  | @cons E₁ E₂ E₃ s c ih =>
      intro E₀ hAx hdich hup hPE hnP
      have hup2 : HoldsInRel E₀ E₂ := hup.trans (Step_sound hAx s)
      rcases hdich E₂ hup2 (Derives_sound hAx c.toDerives) with hP2 | hQ2
      · exact ih hAx hdich hup2 hP2 hnP
      · exact ⟨E₁, E₂, s, hPE, hQ2, hup, Derives_sound hAx c.toDerives⟩

/-- **JUMP EXTRACTION** — the transitivity skeleton of Freyd's "there must
    exist `i` such that `G₁ → Hᵢ` is an inclusion and the image of
    `G₁ → Hᵢ₊₁` is isomorphic to `G₂`."  If every valid interpolant of
    `E₀ ⊆ Eω` is `P` ("still fully collapsed") or `Q` ("hardly collapsed"),
    the chain starts at a `P`-term and ends at a non-`P`-term, then some SINGLE
    rewrite jumps from a `P`-stage to a `Q`-stage — and both stages come with
    their interpolation containments, ready for a graph-level analysis of that
    one step.  (The dichotomy hypothesis is per-*term*; Freyd's own dichotomy
    is per-*composite-map*, which a future proof can encode by choosing `P`/`Q`
    to quantify over the composite maps.) -/
theorem Chain.exists_jump {Ax : List (Term L × Term L)}
    (hAx : ∀ p ∈ Ax, HoldsInRel p.1 p.2) {P Q : Term L → Prop} {E₀ Eω : Term L}
    (hdich : ∀ E, HoldsInRel E₀ E → HoldsInRel E Eω → P E ∨ Q E)
    (hP0 : P E₀) (hnPω : ¬ P Eω) (h : Chain Ax E₀ Eω) :
    ∃ E F, Step Ax E F ∧ P E ∧ Q F ∧ HoldsInRel E₀ E ∧ HoldsInRel F Eω :=
  Chain.exists_jump_aux h hAx hdich (HoldsInRel.refl E₀) hP0 hnPω

/-! ## Layer 4 — the no-finite-axiomatization metatheorem (reduction)

  Freyd's argument: recast the allegory axioms as *separated* containments; then
  the infinite rhombus family is valid in `Rel(S)` but, by a counting argument on
  the graph maps that any derivation must factor through, no fixed finite axiom
  set entails all of it.  We isolate that counting argument as the explicit
  hypothesis `RhombusHard` and reduce the metatheorem to it — a faithful
  reduction, hole-free and axiom-clean.  See the module report for the exact
  remaining content of `RhombusHard` and why it is hard. -/

/-- An axiom set is **complete** for `Rel(S)` when every valid containment is
    derivable from it. -/
def Complete (Ax : List (Term L × Term L)) : Prop :=
  ∀ E₁ E₂ : Term L, HoldsInRel E₁ E₂ → Derives Ax E₁ E₂

/-- **The empty axiom set is not complete** — the fully-provable base instance of
    the metatheorem.  `E ∩ E ⊆ E` is valid in `Rel(S)` yet its two sides are
    distinct terms, so by `Derives_nil_eq` it is not derivable from no axioms.
    (This is `no_finite_axiomatization` for the finite valid set `∅`, proved
    unconditionally — the general finite set is the open `RhombusHard`.) -/
theorem not_complete_nil : ¬ Complete ([] : List (Term L × Term L)) := by
  intro hC
  have hvalid : HoldsInRel (Term.meet Term.one Term.one) (Term.one : Term L) := by
    intro V ι x y h; exact h.1
  have heq : (Term.meet Term.one Term.one : Term L) = Term.one :=
    Derives_nil_eq (hC _ _ hvalid)
  nomatch heq

/-- **Freyd's counting obstruction** (corrected form).  For any finite axiom
    set of *valid* containments, some member of the rhombus family is NOT
    derivable from it.  (The graph map collapsing the `n`-rhombus identifies
    unboundedly many vertex pairs; each single axiom instance, as a graph map,
    merges a bounded number; and — the corrected heart, see the OPEN note — the
    only partial collapses of the chain that stay in `Ḡ` are the trivial one,
    the `{s,t}`-gluing, and the full collapse, so for large `n` some single
    step would have to merge unboundedly many pairs.)  Note the `∃ n`: small
    members may well be derivable — `ent0_derivable` shows the two-rhombus
    member is. -/
def RhombusHard (rhL rhR : ℕ → Term L) : Prop :=
  ∀ Ax : List (Term L × Term L), (∀ p ∈ Ax, HoldsInRel p.1 p.2) →
    ∃ n, ¬ Derives Ax (rhL n) (rhR n)

/-- **§2.158 Target 3 — no finite axiomatization (reduction to the counting
    obstruction).**  Given a family `rhL n ⊆ rhR n` that is (i) valid in `Rel(S)`
    and (ii) satisfies Freyd's counting obstruction, NO finite set of equations
    true for `Rel(S)` accounts for all equations true for `Rel(S)`: no finite
    *valid* axiom set is complete.  (`rhombus1_holds` is the base case of (i);
    the full family and (ii) are the remaining Layer-1/Layer-4 content.) -/
theorem no_finite_axiomatization {rhL rhR : ℕ → Term L}
    (hvalid : ∀ n, HoldsInRel (rhL n) (rhR n))
    (hhard : RhombusHard rhL rhR) :
    ¬ ∃ Ax : List (Term L × Term L),
        (∀ p ∈ Ax, HoldsInRel p.1 p.2) ∧ Complete Ax := by
  rintro ⟨Ax, hAxValid, hComplete⟩
  obtain ⟨n, hn⟩ := hhard Ax hAxValid
  exact hn (hComplete (rhL n) (rhR n) (hvalid n))

/-- **The reduction, pinned to the entangled family**: the headline now rests
    on the single open hypothesis `RhombusHard entL entR`. -/
theorem ent_no_finite_axiomatization (hhard : RhombusHard entL entR) :
    ¬ ∃ Ax : List (Term Nat × Term Nat),
        (∀ p ∈ Ax, HoldsInRel p.1 p.2) ∧ Complete Ax :=
  no_finite_axiomatization ent_holds hhard

/-! ## OPEN — the remaining content of `RhombusHard entL entR`

  What is CLOSED here (all Sorry-free, axioms ⊆ `[propext]`):

  * **Layer 1 validity, all `n`** — `ladder_holds` (series family) and
    `ent_holds` (the genuine entangled family `entL/entR`, reconstructed from
    the book's figures; `n` indexes `n+2` rhombi).
  * **ERRATUM** — `ent0_derivable`: the book's own two-rhombus example is
    derivable from the finite valid list `allegoryAxioms`; the book's claim
    that its one- and two-pair partial collapses all leave `Ḡ` is false for
    the `{s,t}`-containing ones (`1 ∩ entR n` is a TERM presenting the
    `{s,t}`-collapse).  Any faithful counting argument must let derivations
    pass through the `{s,t}`-collapse stage.
  * **Chain normalization** — `derives_iff_chain`: a derivation is a chain of
    single rewrites `Step` (one axiom instance in one one-hole context); the
    stages are terms, so their graphs are automatically in `Ḡ`; each link is
    valid (`Step_sound`) hence carries a graph map (`holdsInRel_iff_hom`).
  * **Jump extraction** — `Chain.exists_jump`: given a P/Q-dichotomy on valid
    interpolants, some SINGLE rewrite jumps from a `P`-stage to a `Q`-stage
    (Freyd's "there must exist `i` …"), with both interpolation containments
    in hand.
  * **Endpoint maps** — `Derives_hom`; **`B = 0` case** — `Derives_nil_eq`,
    `not_complete_nil`; the **reduction** — `no_finite_axiomatization`,
    `ent_no_finite_axiomatization`.

  What remains OPEN in `RhombusHard entL entR` — three graph-level lemmas.
  Sketch of the corrected counting argument they support: normalize a
  derivation of `entL n ⊆ entR n` to a chain; choose per-link graph maps and
  compose them into `gᵢ : [entR n] → [Fᵢ]`; kernels grow monotonically from
  trivial to the full designated collapse (rigidity at the `entL n` end);
  by (a) every stage kernel is `≤ {s,t}` or `⊇` all designated pairs; by
  `Chain.exists_jump` some single step jumps, merging all `2n + 3` designated
  pairs at once; by (b) a single axiom instance cannot, once `n` exceeds the
  bound read off `Ax`.

  (a) **SP-WALL (kernel dichotomy, `n ≥ 1`, i.e. ≥ 3 rhombi).**  For a chain
      stage `F` with composite map `g : [entR n] → [F]` whose continuation to
      `[entL n]` is the collapse: `ker g ≤` the `{s,t}`-pair, or `ker g ⊇` all
      designated pairs.  Needs (i) the subgraph lemma — a connected subgraph
      of a `Ḡ`-graph containing the marks is in `Ḡ` (Freyd's "one may show") —
      applied to the image of `g`, and (ii) the obstruction: every OTHER
      partial collapse of the `≥ 3`-rhombus chain has a `K₄` minor with the
      `s`,`t`-edge added, while term graphs have treewidth ≤ 2.  Neither the
      minor theory nor a treewidth bound on `toGraph` exists in the repo; this
      is the genuinely combinatorial core.  (For 2 rhombi the dichotomy is
      FALSE — that is exactly `ent0_derivable`.)

  (b) **BOUNDED STEP.**  For a single rewrite `C[σA] ⊆ C[σB]`, a CANONICAL
      graph map `[C[σB]] → [C[σA]]` — identity outside the redex, the
      `σ`-blow-up of a fixed map `[B] → [A]` inside — whose fibres have size
      bounded by the size of `B`, independent of `σ` and `C`.  Needs
      substitution- and context-functoriality of `toGraph` (blob analysis on
      the glued `Quot` towers).  Note this makes Freyd's separatedness
      reduction for added axioms unnecessary: fibres, unlike vertex counts,
      are bounded for arbitrary valid axioms.

  (c) **RIGIDITY at the collapsed end.**  Explicit designated vertices of the
      tower `[entR n]` (`pVert/qVert` by recursion over `chainT`), and: every
      mark-preserving `EHom [entR n] → [entL n]` merges all designated pairs
      (by uniqueness of each label's edge in the `entL n` tower — an
      edge-uniqueness induction, no vertex counting).

  Of these, (c) is bookkeeping, (b) is a solid infrastructure chunk, and (a)
  is the hard mathematics.  All three are stated so that `Chain.exists_jump`
  assembles them into `RhombusHard entL entR` without further ideas. -/

end Freyd.S2_158
