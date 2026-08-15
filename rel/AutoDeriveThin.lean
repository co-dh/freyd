/-
  AUTO-DERIVE, increment 2: the THINNING (Pareto-frontier) dynamic program, mechanised.

  B&dM's THEOREM 8.1 / Corollary 8.1 (`AOP.A8_1.thinning` / `thinning_min`) refine an
  optimisation `min R · Λ⦇S⦈` into a fold that carries a THINNED SET of partial solutions:
  at every step, extend all kept candidates, then discard any candidate that another one
  `Q`-dominates (`Q` a preorder below `R` on which the step algebra `S` is monotonic).
  Unlike the greedy scalar/pair case (`RunningBest`), the concrete program state is a
  CANDIDATE LIST, so the concrete layer needs a verified Pareto prune (`thinList`) and a
  set-valued fold-bridge into the abstract thinning catamorphism.

  `ThinBest L E St` bundles the CREATIVE inputs of such a derivation —

  * `leafOne`, `stepOne` — the nondeterministic generator's candidate lists (the search space;
    the algebra `S` is their membership relation, so program and generator share one source);
  * `Q`, `qDec`          — the thinning preorder and a sound Boolean test for it;
  * `R`, `rDec`          — the final selection preorder and a total Boolean comparison;
  * `step_mono`          — THE mathematical insight: a dominating state can match any
    extension of a dominated one —

  plus seven one-line order facts.  From these the drivers discharge every side condition of
  THEOREM 8.1 (`Qm` transitive/reflexive, `MonotonicAlg gen Qm°`, `Q ⊑ R`, …), build the
  program `foldFn` (extend-all + `thinList` prune) and its fold-bridge into
  `⦇Λ(S·F∈)·thin Q⦈`, and emit:

  * `frontier`      — Pareto-frontier correctness (THEOREM 8.1 read concretely): every kept
                      candidate is generatable, every generatable candidate is dominated by a
                      kept one;
  * `correct`       — optimum correctness (Corollary 8.1 read concretely): the `R`-best kept
                      candidate is an `R`-minimum of ALL generatable states;
  * `correct_value` — the scalar-answer packaging via a problem-specific spec
                      characterisation (`gen_spec`/`spec_gen`), as in `RunningBest.correct`.

  What remains HUMAN, per problem: the bundle's fields and the generator-vs-spec
  characterisation.

  Demo (same file, `namespace Knapsack`): concrete 0/1 knapsack — the book's own §8.4
  binary-thinning example, whose concrete program `AOP.A8_4_Knapsack` had deferred.

  Mathlib-free.  Axioms ⊆ {propext, Classical.choice, Quot.sound} (the `Classical.choice`
  is inherited from `cataR_eq_relCata`, the honest cost of applying the relational
  catamorphism theory — same as `RunningBest`).
-/
import AOP.A8_1
import AOP.A7_4_Horner

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.SL

open Freyd

/-! ## Pointwise Rel(Set) readings: the transpose and `thinRel` -/

/-- In Rel(Set) the transpose `A W` sends `u` to exactly its `W`-successor set (the pointwise
    content of `A_eq_classifier`). -/
theorem Λ_apply_iff {b c : RelSet.{0}} (W : c ⟶ b) (u : c.carrier) (G : (pow b).carrier) :
    Λ W u G ↔ G = fun y => W u y := by
  rw [Λ_eq_classifier]; exact Iff.rfl

/-- Pointwise form of `thinRel` in Rel(Set): `Y` is a `thin Q`-refinement of `P` iff `Y ⊆ P`
    and every member of `P` has a `Q`-improvement in `Y` (`Q z w` = "`w` at least as good as
    `z`", the `minRel` convention). -/
theorem thinRel_pt {α : RelSet.{0}} (Q : α ⟶ α) (P Y : (pow α).carrier) :
    thinRel Q P Y ↔ (∀ y, Y y → P y) ∧ (∀ z, P z → ∃ w, Q z w ∧ Y w) := Iff.rfl

/-! ## The generic Pareto prune on candidate lists

  `thinList q` implements §8.3's `thinlist`: insert each candidate, dropping it if a kept one
  dominates it and evicting the kept ones it dominates.  Its two correctness lemmas are
  exactly the two halves of `thinRel_pt`, against ANY preorder `Q` for which `q` is a SOUND
  test (completeness of `q` is not needed — an incomplete test only prunes less). -/

/-- Insert `s` into a pruned accumulator: drop `s` if some kept `t` dominates it (`q s t`),
    else keep `s` and evict the kept elements it dominates. -/
def insertThin {St : Type} (q : St → St → Bool) (acc : List St) (s : St) : List St :=
  if acc.any (fun t => q s t) then acc else s :: acc.filter (fun t => !(q t s))

/-- Prune a candidate list to a dominating sublist. -/
def thinList {St : Type} (q : St → St → Bool) : List St → List St
  | [] => []
  | s :: rest => insertThin q (thinList q rest) s

theorem insertThin_sub {St : Type} {q : St → St → Bool} {acc : List St} {s t : St}
    (h : t ∈ insertThin q acc s) : t = s ∨ t ∈ acc := by
  unfold insertThin at h
  split at h
  · exact Or.inr h
  · rcases List.mem_cons.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_filter.mp h).1

/-- Pruning only discards: the kept candidates were candidates. -/
theorem thinList_sub {St : Type} {q : St → St → Bool} : ∀ {cands : List St} {t : St},
    t ∈ thinList q cands → t ∈ cands
  | _ :: _, _, h => by
    rcases insertThin_sub h with h | h
    · exact List.mem_cons.mpr (Or.inl h)
    · exact List.mem_cons.mpr (Or.inr (thinList_sub h))

/-- A candidate with a dominator among the kept ones keeps a dominator after one insertion:
    either its old dominator survives the eviction filter, or the evictor `s` dominates it
    transitively. -/
theorem insertThin_dom_old {St : Type} {q : St → St → Bool} {Q : St → St → Prop}
    (hq : ∀ s t, q s t = true → Q s t) (htrans : ∀ a b c, Q a b → Q b c → Q a c)
    {acc : List St} {s z w : St} (hw : w ∈ acc) (hzw : Q z w) :
    ∃ w' ∈ insertThin q acc s, Q z w' := by
  unfold insertThin
  split
  · exact ⟨w, hw, hzw⟩
  · cases hqe : q w s with
    | false =>
      exact ⟨w, List.mem_cons.mpr (Or.inr (List.mem_filter.mpr
        ⟨hw, by rw [hqe]; rfl⟩)), hzw⟩
    | true => exact ⟨s, List.mem_cons.mpr (Or.inl rfl), htrans z w s hzw (hq w s hqe)⟩

/-- The freshly inserted candidate is dominated by a kept one: itself if kept, or the kept
    element that caused the drop. -/
theorem insertThin_dom_self {St : Type} {q : St → St → Bool} {Q : St → St → Prop}
    (hq : ∀ s t, q s t = true → Q s t) (hrefl : ∀ s, Q s s)
    (acc : List St) (s : St) : ∃ w ∈ insertThin q acc s, Q s w := by
  unfold insertThin
  split
  next h =>
    obtain ⟨t, ht, hqt⟩ := List.any_eq_true.mp h
    exact ⟨t, ht, hq s t hqt⟩
  next h => exact ⟨s, List.mem_cons.mpr (Or.inl rfl), hrefl s⟩

/-- Pruning loses no optimum: every candidate is `Q`-dominated by a kept one. -/
theorem thinList_dom {St : Type} {q : St → St → Bool} {Q : St → St → Prop}
    (hq : ∀ s t, q s t = true → Q s t) (hrefl : ∀ s, Q s s)
    (htrans : ∀ a b c, Q a b → Q b c → Q a c) :
    ∀ {cands : List St} {z : St}, z ∈ cands → ∃ w ∈ thinList q cands, Q z w
  | s :: rest, z, hz => by
    rcases List.mem_cons.mp hz with hzs | hz
    · subst hzs
      exact insertThin_dom_self hq hrefl (thinList q rest) z
    · obtain ⟨w, hw, hzw⟩ := thinList_dom hq hrefl htrans hz
      exact insertThin_dom_old hq htrans hw hzw

theorem thinList_ne_nil {St : Type} {q : St → St → Bool} : ∀ {cands : List St},
    cands ≠ [] → thinList q cands ≠ []
  | s :: rest, _ => by
    show insertThin q (thinList q rest) s ≠ []
    unfold insertThin
    split
    next h =>
      obtain ⟨t, ht, _⟩ := List.any_eq_true.mp h
      exact List.ne_nil_of_mem ht
    next h => exact List.cons_ne_nil _ _

/-! ## The bundle of creative inputs -/

/-- The creative inputs of a thinning derivation (B&dM ch. 8), plus the one-line order facts
    its mechanical side conditions reduce to.  The program state is a LIST of kept candidate
    states; the answer is the `R`-best kept candidate at the end.  Orders follow the `minRel`
    convention: `Q z w` / `R z w` = "`w` is at least as good as `z`". -/
structure ThinBest (L E St : Type) where
  /-- Candidate states generated from a leaf. -/
  leafOne : L → List St
  /-- Candidate one-step extensions of a single state by a new element. -/
  stepOne : St → E → List St
  /-- The thinning preorder (Pareto dominance): `Q z w` = "`w` at least as good as `z`". -/
  Q : St → St → Prop
  /-- The final selection preorder: the answer must `R`-dominate every candidate. -/
  R : St → St → Prop
  /-- A sound Boolean test for `Q` (used by the prune; completeness not required). -/
  qDec : St → St → Bool
  /-- A total Boolean comparison for `R` (used by the final pick). -/
  rDec : St → St → Bool
  Q_refl : ∀ s, Q s s
  Q_trans : ∀ {s t u}, Q s t → Q t u → Q s u
  /-- The thinning order refines the selection order (Cor 8.1's `Q ⊑ R`). -/
  Q_le_R : ∀ {s t}, Q s t → R s t
  R_trans : ∀ {s t u}, R s t → R t u → R s u
  qDec_sound : ∀ {s t}, qDec s t = true → Q s t
  /-- `rDec s t = true` means `s` is at least as good as `t`. -/
  rDec_t : ∀ {s t}, rDec s t = true → R t s
  /-- ... and `false` means `t` is at least as good as `s` (totality of the comparison). -/
  rDec_f : ∀ {s t}, rDec s t = false → R s t
  /-- MONOTONICITY (the §8.1 insight, = `MonotonicAlg S Q°`): a dominating state can match
      any extension of a dominated one. -/
  step_mono : ∀ {s s' : St} (e : E) {y : St}, Q s' s → y ∈ stepOne s' e →
    ∃ y' ∈ stepOne s e, Q y y'

namespace ThinBest

variable {L E St : Type} (P : ThinBest L E St)

/-! ## The derived generator, orders and program -/

/-- The nondeterministic generator: at a leaf any leaf candidate, at a `snoc` any one-step
    extension.  This is the `S` of `⦇S⦈` — the search space. -/
def genFn : (Fobj L E (⟨St⟩ : RelSet.{0})).carrier → St → Prop
  | Sum.inl x => fun y => y ∈ P.leafOne x
  | Sum.inr (s, e) => fun y => y ∈ P.stepOne s e

/-- The generator as a `Rel(Set)` morphism. -/
def gen : Fobj L E (⟨St⟩ : RelSet.{0}) ⟶ (⟨St⟩ : RelSet.{0}) := P.genFn

/-- The thinning preorder as a morphism. -/
def Qm : (⟨St⟩ : RelSet.{0}) ⟶ (⟨St⟩ : RelSet.{0}) := fun s t => P.Q s t

/-- The selection preorder as a morphism. -/
def Rm : (⟨St⟩ : RelSet.{0}) ⟶ (⟨St⟩ : RelSet.{0}) := fun s t => P.R s t

/-- One step of the PROGRAM: extend every kept candidate by every one-step choice, then
    prune to a dominating sublist. -/
def stepList (cs : List St) (e : E) : List St :=
  thinList P.qDec (cs.flatMap (fun s => P.stepOne s e))

/-- The concrete fold: the thinned candidate list (the PROGRAM, up to the final pick). -/
def foldFn : SnocList L E → List St
  | SnocList.wrap x => thinList P.qDec (P.leafOne x)
  | SnocList.snoc xs e => P.stepList (foldFn xs) e

/-- `thinList_dom` at the bundle's own order data. -/
theorem thin_dom {cands : List St} {z : St} (hz : z ∈ cands) :
    ∃ w ∈ thinList P.qDec cands, P.Q z w :=
  thinList_dom (Q := P.Q) (fun s t h => P.qDec_sound (s := s) (t := t) h) P.Q_refl
    (fun a b c h1 h2 => P.Q_trans (s := a) (t := b) (u := c) h1 h2) hz

/-! ## The mechanical side conditions, discharged once -/

theorem Qm_refl_le : Cat.id (⟨St⟩ : RelSet.{0}) ⊑ P.Qm := by
  rw [le_iff]; intro s t h; exact h ▸ P.Q_refl s

theorem Qm_trans_le : P.Qm ≫ P.Qm ⊑ P.Qm := by
  rw [le_iff]; rintro s u ⟨t, h1, h2⟩; exact P.Q_trans h1 h2

theorem Qm_le_Rm : P.Qm ⊑ P.Rm := by
  rw [le_iff]; intro s t h; exact P.Q_le_R h

theorem Rm_trans_le : P.Rm ≫ P.Rm ⊑ P.Rm := by
  rw [le_iff]; rintro s u ⟨t, h1, h2⟩; exact P.R_trans h1 h2

/-- The generator is MONOTONIC on `Q°` (THEOREM 8.1's hypothesis): `step_mono` on the `snoc`
    summand, reflexivity of `Q` on the leaf summand. -/
theorem gen_mono : MonotonicAlg (F := F L E) P.gen P.Qm° := by
  show (F L E).map P.Qm° ≫ P.gen ⊑ P.gen ≫ P.Qm°
  rw [le_iff]; rintro u y ⟨u', hF, hgen⟩
  cases u with
  | inl x =>
    cases u' with
    | inl x' =>
      have hx : x = x' := hF
      subst hx
      exact ⟨y, hgen, P.Q_refl y⟩
    | inr q => exact hF.elim
  | inr p =>
    obtain ⟨s, e⟩ := p
    cases u' with
    | inl x' => exact hF.elim
    | inr q =>
      obtain ⟨s', e'⟩ := q
      obtain ⟨hss, hee⟩ := hF
      have hee' : e = e' := hee
      subst hee'
      obtain ⟨y', hy', hQ⟩ := P.step_mono e hss hgen
      exact ⟨y', hy', hQ⟩

/-! ## The fold-bridge into the abstract thinning DP -/

/-- The thinning-DP algebra `Λ(S·F∈)·thin Q` of THEOREM 8.1, at the generator. -/
def thinAlg : Fobj L E (pow (⟨St⟩ : RelSet.{0})) ⟶ pow (⟨St⟩ : RelSet.{0}) :=
  Λ ((F L E).map (∋ (⟨St⟩ : RelSet.{0})) ≫ P.gen) ≫ thinRel P.Qm

/-- **The fold-bridge**: the program's candidate list, read as a set, is one run of the
    abstract thinning DP `⦇Λ(S·F∈)·thin Q⦈` — at each step the pruned list is a valid
    `thin Q`-refinement (`thinList_sub`/`thin_dom`) of the full one-step extension set. -/
theorem bridge : ∀ xs : SnocList L E, cataFold P.thinAlg xs (fun s => s ∈ P.foldFn xs) := by
  intro xs; induction xs with
  | wrap x =>
    refine ⟨fun y => ((F L E).map (∋ (⟨St⟩ : RelSet.{0})) ≫ P.gen) (Sum.inl x) y,
      (Λ_apply_iff _ _ _).mpr rfl, (thinRel_pt _ _ _).mpr ⟨?_, ?_⟩⟩
    · intro y hy
      have hy' : y ∈ thinList P.qDec (P.leafOne x) := hy
      exact ⟨Sum.inl x, rfl, thinList_sub hy'⟩
    · rintro z ⟨u', hFu, hgen⟩
      cases u' with
      | inl x' =>
        have hx : x = x' := hFu
        subst hx
        have hgen' : z ∈ P.leafOne x := hgen
        obtain ⟨w, hw, hQ⟩ := P.thin_dom hgen'
        exact ⟨w, hQ, hw⟩
      | inr q => exact hFu.elim
  | snoc xs e ih =>
    refine ⟨fun s => s ∈ P.foldFn xs, ih,
      fun y => ((F L E).map (∋ (⟨St⟩ : RelSet.{0})) ≫ P.gen)
        (Sum.inr (fun s => s ∈ P.foldFn xs, e)) y,
      (Λ_apply_iff _ _ _).mpr rfl, (thinRel_pt _ _ _).mpr ⟨?_, ?_⟩⟩
    · intro y hy
      have hy' : y ∈ thinList P.qDec ((P.foldFn xs).flatMap (fun s => P.stepOne s e)) := hy
      obtain ⟨s, hs, hys⟩ := List.mem_flatMap.mp (thinList_sub hy')
      exact ⟨Sum.inr (s, e), ⟨hs, rfl⟩, hys⟩
    · rintro z ⟨u', hFu, hgen⟩
      cases u' with
      | inl x' => exact hFu.elim
      | inr q =>
        obtain ⟨s, e'⟩ := q
        obtain ⟨hmem, hee⟩ := hFu
        have hee' : e = e' := hee
        subst hee'
        have hmem' : s ∈ P.foldFn xs := hmem
        have hgen' : z ∈ P.stepOne s e := hgen
        have hzf : z ∈ (P.foldFn xs).flatMap (fun t => P.stepOne t e) :=
          List.mem_flatMap.mpr ⟨s, hmem', hgen'⟩
        obtain ⟨w, hw, hQ⟩ := P.thin_dom hzf
        exact ⟨w, hQ, hw⟩

/-! ## The drivers: THEOREM 8.1 / Corollary 8.1, read concretely -/

/-- **The §8.1 morphism headline**: the program's candidate-set map lies inside
    `thin Q · Λ⦇S⦈` — THEOREM 8.1 applied across the fold-bridge. -/
theorem le_Λ_cata_thinRel :
    (graph (fun xs => fun s => s ∈ P.foldFn xs) : dSL L E ⟶ pow (⟨St⟩ : RelSet.{0}))
      ⊑ Λ (cataR P.gen) ≫ thinRel P.Qm := by
  have Hcore := thinning (F_preservesRecip L E) (initial L E) P.Qm_trans_le P.gen_mono
  rw [← cataR_eq_relCata (Λ ((F L E).map (∋ (⟨St⟩ : RelSet.{0})) ≫ P.gen) ≫ thinRel P.Qm),
    ← cataR_eq_relCata P.gen] at Hcore
  rw [le_iff]; intro xs Y hY
  have hYe : Y = fun s => s ∈ P.foldFn xs := hY
  subst hYe
  exact le_iff.mp Hcore xs _ (P.bridge xs)

/-- **Auto-derived Pareto-frontier correctness** (THEOREM 8.1 read concretely): every kept
    candidate is generatable, and every generatable candidate is `Q`-dominated by a kept
    one. -/
theorem frontier (xs : SnocList L E) :
    (∀ s, s ∈ P.foldFn xs → cataFold P.gen xs s) ∧
    (∀ z, cataFold P.gen xs z → ∃ w ∈ P.foldFn xs, P.Q z w) := by
  obtain ⟨G, hAG, hthin⟩ := le_iff.mp P.le_Λ_cata_thinRel xs (fun s => s ∈ P.foldFn xs) rfl
  have hGeq : G = fun s => cataR P.gen xs s := (Λ_apply_iff _ _ _).mp hAG
  subst hGeq
  obtain ⟨hsub, hdom⟩ := (thinRel_pt _ _ _).mp hthin
  exact ⟨hsub, fun z hz => by
    obtain ⟨w, hQ, hw⟩ := hdom z hz
    exact ⟨w, hw, hQ⟩⟩

/-! ## The final pick and the optimum theorem -/

/-- The better of two candidates under the `rDec` comparison. -/
def pick (b s : St) : St := if P.rDec b s then b else s

theorem pick_left (b s : St) : P.R b (P.pick b s) := by
  show P.R b (if P.rDec b s then b else s)
  cases hrd : P.rDec b s with
  | true => rw [if_pos rfl]; exact P.Q_le_R (P.Q_refl b)
  | false => rw [if_neg Bool.false_ne_true]; exact P.rDec_f hrd

theorem pick_right (b s : St) : P.R s (P.pick b s) := by
  show P.R s (if P.rDec b s then b else s)
  cases hrd : P.rDec b s with
  | true => rw [if_pos rfl]; exact P.rDec_t hrd
  | false => rw [if_neg Bool.false_ne_true]; exact P.Q_le_R (P.Q_refl s)

theorem pick_mem (b s : St) : P.pick b s = b ∨ P.pick b s = s := by
  show (if P.rDec b s then b else s) = b ∨ (if P.rDec b s then b else s) = s
  cases P.rDec b s with
  | true => exact Or.inl (if_pos rfl)
  | false => exact Or.inr (if_neg Bool.false_ne_true)

/-- Running `R`-best of a list, seeded. -/
def best1 : St → List St → St
  | b, [] => b
  | b, s :: rest => best1 (P.pick b s) rest

theorem best1_spec : ∀ (cs : List St) (b : St),
    (P.best1 b cs = b ∨ P.best1 b cs ∈ cs) ∧ P.R b (P.best1 b cs) ∧
      ∀ z ∈ cs, P.R z (P.best1 b cs)
  | [], b => ⟨Or.inl rfl, P.Q_le_R (P.Q_refl b), fun z hz => nomatch hz⟩
  | s :: rest, b => by
    obtain ⟨hmem, hseed, hall⟩ := best1_spec rest (P.pick b s)
    refine ⟨?_, P.R_trans (P.pick_left b s) hseed, ?_⟩
    · rcases hmem with h | h
      · rcases P.pick_mem b s with hp | hp
        · exact Or.inl (h.trans hp)
        · exact Or.inr (List.mem_cons.mpr (Or.inl (h.trans hp)))
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))
    · intro z hz
      rcases List.mem_cons.mp hz with hzs | hz
      · subst hzs
        exact P.R_trans (P.pick_right b z) hseed
      · exact hall z hz

/-- The `R`-best of the final candidate list (`none` on an empty list). -/
def bestOf : List St → Option St
  | [] => none
  | s :: rest => some (P.best1 s rest)

theorem bestOf_spec {cs : List St} {b : St} (hb : P.bestOf cs = some b) :
    b ∈ cs ∧ ∀ z ∈ cs, P.R z b := by
  cases cs with
  | nil => exact nomatch (show (none : Option St) = some b from hb)
  | cons s rest =>
    have hbe : b = P.best1 s rest := (Option.some.inj hb).symm
    subst hbe
    obtain ⟨hmem, hseed, hall⟩ := P.best1_spec rest s
    refine ⟨?_, ?_⟩
    · rcases hmem with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons.mpr (Or.inr h)
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hseed
      · exact hall z hz

/-- The full program: fold the thinned frontier, then pick the `R`-best kept candidate. -/
def solveFn (xs : SnocList L E) : Option St := P.bestOf (P.foldFn xs)

/-- **Auto-derived optimum correctness** (Corollary 8.1 read concretely): the `R`-best kept
    candidate is a genuine `R`-minimum of ALL generatable states.  Routed through the
    abstract `thinning_min` at the fold-bridge and the `bestOf` pick. -/
theorem correct (xs : SnocList L E) (b : St) (hb : P.solveFn xs = some b) :
    cataFold P.gen xs b ∧ ∀ z, cataFold P.gen xs z → P.R z b := by
  obtain ⟨hbmem, hblb⟩ := P.bestOf_spec hb
  have Hcore := thinning_min (F_preservesRecip L E) (initial L E) P.Qm_le_Rm P.Qm_refl_le
    P.Qm_trans_le P.Rm_trans_le P.gen_mono
  rw [← cataR_eq_relCata (Λ ((F L E).map (∋ (⟨St⟩ : RelSet.{0})) ≫ P.gen) ≫ thinRel P.Qm),
    ← cataR_eq_relCata P.gen] at Hcore
  have hminb : minRel P.Rm (fun s => s ∈ P.foldFn xs) b :=
    ⟨hbmem, fun z hz => hblb z hz⟩
  have hlhs : (cataR P.thinAlg ≫ minRel P.Rm) xs b :=
    ⟨fun s => s ∈ P.foldFn xs, P.bridge xs, hminb⟩
  obtain ⟨G, hAG, hmin⟩ := le_iff.mp Hcore xs b hlhs
  have hGeq : G = fun s => cataR P.gen xs s := (Λ_apply_iff _ _ _).mp hAG
  subst hGeq
  have hmin' : (fun s => cataR P.gen xs s) b ∧
      ∀ z, (fun s => cataR P.gen xs s) z → P.Rm z b := hmin
  exact ⟨hmin'.1, fun z hz => hmin'.2 z hz⟩

/-- An empty pick certifies an empty search space (via frontier completeness). -/
theorem correct_empty (xs : SnocList L E) (hb : P.solveFn xs = none) :
    ∀ z, ¬ cataFold P.gen xs z := by
  intro z hz
  obtain ⟨w, hw, _⟩ := (P.frontier xs).2 z hz
  have hne : P.foldFn xs ≠ [] := List.ne_nil_of_mem hw
  cases hfe : P.foldFn xs with
  | nil => exact absurd hfe hne
  | cons s rest =>
    have hsome : P.solveFn xs = some (P.best1 s rest) := by
      show P.bestOf (P.foldFn xs) = some (P.best1 s rest)
      rw [hfe]
      rfl
    exact nomatch hsome.symm.trans hb

/-- Spec-level packaging (the `RunningBest.correct` analogue): given the problem-specific
    generator-vs-spec characterisation (`gen_spec`/`spec_gen`) and an `R`-monotone answer
    projection `out`, the picked optimum's value is the `vle`-extremum of the spec. -/
theorem correct_value {V : Type} (spec : SnocList L E → V → Prop) (out : St → V)
    (vle : V → V → Prop) (hRout : ∀ {z w}, P.R z w → vle (out z) (out w))
    (gen_spec : ∀ xs s, cataFold P.gen xs s → spec xs (out s))
    (spec_gen : ∀ xs v, spec xs v → ∃ s, cataFold P.gen xs s ∧ out s = v)
    (xs : SnocList L E) (b : St) (hb : P.solveFn xs = some b) :
    spec xs (out b) ∧ ∀ v, spec xs v → vle v (out b) := by
  obtain ⟨hgen, hopt⟩ := P.correct xs b hb
  refine ⟨gen_spec xs b hgen, fun v hv => ?_⟩
  obtain ⟨s, hs, hout⟩ := spec_gen xs v hv
  exact hout ▸ hRout (hopt s hs)

/-- Totality: nonempty candidate lists at every step keep the pick defined. -/
theorem foldFn_ne_nil (hleaf : ∀ x, P.leafOne x ≠ []) (hstep : ∀ s e, P.stepOne s e ≠ [])
    (xs : SnocList L E) : P.foldFn xs ≠ [] := by
  induction xs with
  | wrap x => exact thinList_ne_nil (hleaf x)
  | snoc xs e ih =>
    show thinList P.qDec ((P.foldFn xs).flatMap (fun s => P.stepOne s e)) ≠ []
    apply thinList_ne_nil
    cases hfe : P.foldFn xs with
    | nil => exact absurd hfe ih
    | cons s rest =>
      intro hflat
      rw [List.flatMap_cons] at hflat
      exact hstep s e (List.append_eq_nil_iff.mp hflat).1

theorem solveFn_isSome (hleaf : ∀ x, P.leafOne x ≠ []) (hstep : ∀ s e, P.stepOne s e ≠ [])
    (xs : SnocList L E) : (P.solveFn xs).isSome = true := by
  have hne := P.foldFn_ne_nil hleaf hstep xs
  cases hfe : P.foldFn xs with
  | nil => exact absurd hfe hne
  | cons s rest =>
    show (P.bestOf (P.foldFn xs)).isSome = true
    rw [hfe]
    rfl

end ThinBest

/-! ## Demo: 0/1 knapsack (B&dM §8.4 — the book's binary-thinning example), concretely

  `AOP.A8_4_Knapsack` states the §8.4 refinement abstractly (an instance of `thinning_min`)
  and defers the concrete program.  The driver produces it here: state = (weight, value) of a
  selection, generator = skip / take-if-it-fits, thinning order = Pareto dominance (lighter
  AND at least as valuable), selection order = value. -/

namespace Knapsack

/-- An item: `(weight, value)`. -/
abbrev Item := Nat × Nat

/-- The 0/1-knapsack thinning bundle at capacity `W`. -/
def knap (W : Nat) : ThinBest Unit Item (Nat × Nat) where
  leafOne _ := [(0, 0)]
  stepOne s e := if s.1 + e.1 ≤ W then [s, (s.1 + e.1, s.2 + e.2)] else [s]
  Q z w := w.1 ≤ z.1 ∧ z.2 ≤ w.2
  R z w := z.2 ≤ w.2
  qDec z w := decide (w.1 ≤ z.1 ∧ z.2 ≤ w.2)
  rDec s t := decide (t.2 ≤ s.2)
  Q_refl s := ⟨Nat.le_refl _, Nat.le_refl _⟩
  Q_trans h1 h2 := ⟨Nat.le_trans h2.1 h1.1, Nat.le_trans h1.2 h2.2⟩
  Q_le_R h := h.2
  R_trans h1 h2 := Nat.le_trans h1 h2
  qDec_sound h := of_decide_eq_true h
  rDec_t h := of_decide_eq_true h
  rDec_f h := Nat.le_of_lt (Nat.not_le.mp (of_decide_eq_false h))
  step_mono := by
    intro s s' e y hq hy
    -- `hq : Q s' s` — `s` is lighter and at least as valuable
    have hskip : ∀ t : Nat × Nat,
        t ∈ (if t.1 + e.1 ≤ W then [t, (t.1 + e.1, t.2 + e.2)] else [t]) := by
      intro t
      by_cases hf : t.1 + e.1 ≤ W
      · rw [if_pos hf]; exact List.mem_cons.mpr (Or.inl rfl)
      · rw [if_neg hf]; exact List.mem_cons.mpr (Or.inl rfl)
    by_cases hf' : s'.1 + e.1 ≤ W
    · rw [if_pos hf'] at hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨s, hskip s, hq⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · -- the "take" extension: `s` also fits, and its extension dominates
          have hf : s.1 + e.1 ≤ W := Nat.le_trans (Nat.add_le_add_right hq.1 e.1) hf'
          refine ⟨(s.1 + e.1, s.2 + e.2), ?_, ?_⟩
          · rw [if_pos hf]
            exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
          · exact ⟨Nat.add_le_add_right hq.1 e.1, Nat.add_le_add_right hq.2 e.2⟩
        · exact nomatch hy
    · rw [if_neg hf'] at hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨s, hskip s, hq⟩
      · exact nomatch hy

/-- Feasible selections: `Choice W xs s` — `s` is the (total weight, total value) of a
    subset of the items `xs` whose weight stays within `W` at every take. -/
inductive Choice (W : Nat) : SnocList Unit Item → Nat × Nat → Prop where
  | base : Choice W (SnocList.wrap ()) (0, 0)
  | skip {xs e s} : Choice W xs s → Choice W (SnocList.snoc xs e) s
  | take {xs e s} : Choice W xs s → s.1 + e.1 ≤ W →
      Choice W (SnocList.snoc xs e) (s.1 + e.1, s.2 + e.2)

/-- The generator's reachable states are exactly the feasible selections (the
    problem-specific `gen_spec`/`spec_gen` characterisation, one induction). -/
theorem gen_iff_choice (W : Nat) : ∀ (xs : SnocList Unit Item) (s : Nat × Nat),
    cataFold (knap W).gen xs s ↔ Choice W xs s := by
  intro xs; induction xs with
  | wrap u =>
    intro s
    cases u
    constructor
    · intro h
      have hs : s = (0, 0) := List.mem_singleton.mp h
      exact hs ▸ Choice.base
    · intro h
      cases h
      exact List.mem_cons.mpr (Or.inl rfl)
  | snoc xs e ih =>
    intro s
    constructor
    · rintro ⟨s', hs', hstep⟩
      have hch := (ih s').mp hs'
      have hstep' : s ∈ (if s'.1 + e.1 ≤ W then [s', (s'.1 + e.1, s'.2 + e.2)] else [s']) :=
        hstep
      by_cases hf : s'.1 + e.1 ≤ W
      · rw [if_pos hf] at hstep'
        rcases List.mem_cons.mp hstep' with rfl | hstep'
        · exact Choice.skip hch
        · rcases List.mem_cons.mp hstep' with rfl | hstep'
          · exact Choice.take hch hf
          · exact nomatch hstep'
      · rw [if_neg hf] at hstep'
        rcases List.mem_cons.mp hstep' with rfl | hstep'
        · exact Choice.skip hch
        · exact nomatch hstep'
    · intro hch
      cases hch with
      | skip h' =>
        refine ⟨s, (ih s).mpr h', ?_⟩
        show s ∈ (if s.1 + e.1 ≤ W then [s, (s.1 + e.1, s.2 + e.2)] else [s])
        by_cases hf : s.1 + e.1 ≤ W
        · rw [if_pos hf]; exact List.mem_cons.mpr (Or.inl rfl)
        · rw [if_neg hf]; exact List.mem_cons.mpr (Or.inl rfl)
      | take h' hf =>
        rename_i s0
        refine ⟨s0, (ih s0).mpr h', ?_⟩
        show (s0.1 + e.1, s0.2 + e.2)
            ∈ (if s0.1 + e.1 ≤ W then [s0, (s0.1 + e.1, s0.2 + e.2)] else [s0])
        rw [if_pos hf]
        exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

/-- The problem spec: `v` is the value of some feasible selection. -/
def knapSpec (W : Nat) (xs : SnocList Unit Item) (v : Nat) : Prop :=
  ∃ s, Choice W xs s ∧ s.2 = v

/-- The executable solver: fold the thinned Pareto frontier, pick the best kept value. -/
def solve (W : Nat) (xs : SnocList Unit Item) : Option Nat :=
  ((knap W).solveFn xs).map (·.2)

/-- The solver is total (leaf and step candidate lists are never empty). -/
theorem solve_isSome (W : Nat) (xs : SnocList Unit Item) : (solve W xs).isSome = true := by
  have h := (knap W).solveFn_isSome (fun _ => List.cons_ne_nil _ _) (fun s e => ?_) xs
  · show (((knap W).solveFn xs).map (·.2)).isSome = true
    cases hb : (knap W).solveFn xs with
    | none => rw [hb] at h; exact nomatch h
    | some b => rfl
  · show (if s.1 + e.1 ≤ W then [s, (s.1 + e.1, s.2 + e.2)] else [s]) ≠ []
    by_cases hf : s.1 + e.1 ≤ W
    · rw [if_pos hf]; exact List.cons_ne_nil _ _
    · rw [if_neg hf]; exact List.cons_ne_nil _ _

/-- **Headline**: the binary-thinning knapsack program returns the MAXIMUM value over all
    feasible selections — Corollary 8.1's `⦇thin Q·Λ(S·F∈)⦈ · min R`, executed. -/
theorem solve_correct (W : Nat) (xs : SnocList Unit Item) (v : Nat)
    (hv : solve W xs = some v) :
    knapSpec W xs v ∧ ∀ v', knapSpec W xs v' → v' ≤ v := by
  cases hb : (knap W).solveFn xs with
  | none => rw [solve, hb] at hv; exact nomatch hv
  | some b =>
    have hvb : v = b.2 := by
      rw [solve, hb] at hv
      exact (Option.some.inj hv).symm
    subst hvb
    exact (knap W).correct_value (knapSpec W) (·.2) (· ≤ ·) (fun h => h)
      (fun xs s hgen => ⟨s, (gen_iff_choice W xs s).mp hgen, rfl⟩)
      (fun xs v hv => by
        obtain ⟨s, hch, hout⟩ := hv
        exact ⟨s, (gen_iff_choice W xs s).mpr hch, hout⟩)
      xs b hb

/-- Items as a snoc-list. -/
def ofItems (items : List Item) : SnocList Unit Item :=
  items.foldl SnocList.snoc (SnocList.wrap ())

-- capacity 10, items (weight, value): best is (4,40) + (3,50) → weight 7, value 90
example : solve 10 (ofItems [(5, 10), (4, 40), (6, 30), (3, 50)]) = some 90 := by decide
-- capacity 5: (2,3) + (3,4) → weight 5, value 7
example : solve 5 (ofItems [(2, 3), (3, 4), (4, 5), (5, 6)]) = some 7 := by decide
-- capacity 0: only the empty selection fits
example : solve 0 (ofItems [(1, 100), (2, 200)]) = some 0 := by decide
-- no items: the empty selection
example : solve 7 (ofItems []) = some 0 := by decide

end Knapsack
end Freyd.Alg.RelSet.SL
