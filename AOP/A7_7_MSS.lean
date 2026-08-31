/-
  Bird & de Moor, Exercise 7.40 (p. 174-175) — the maximum segment sum by the BOOK route.

  SPEC.  `mss = max ≤ · Λ(sum · segment)`: the greatest of the sums of the segments of a list.
  Mirrored to diagram order and to this repo's one operator (`max R = est(R°)`), that is the
  note's `mss-defn`
      `mss ≜ Λ(segment sum) est(≥)`,   `⊕ ≜ Λ(⊸ zero ∪ plus) est(≥)`.
  `A := Int`: over `Nat` every `⊕` would take its right branch and `mss` would be `sum`.

  WHAT IS HERE — the INNER fold of the note's `mss-deriv`, i.e. the rows Ex 7.40's own hint asks
  for ("express `prefix` as a catamorphism … hence use the greedy theorem to show that
  `⦇[zero,⊕]⦈ ⊆ max Λ(sum·prefix)`"):

  - `mss_prefix_sum`: `prefix sum = ⦇[zero, ⊸ zero ∪ plus]⦈`   (note `mss-prefix-sum`)
  - `mss_mono`:       `F(≥) S ⊑ S ≥`                            (note `mss-mono`)
  - `mss_greedy`:     `⦇Λ(S) est(≥)⦈ ⊑ Λ(⦇S⦈) est(≥)`           (Theorem 7.2)
  - `mss_step`:       `Λ(S) est(≥) = [zero, ⊕]`                 (note `mss-step`)
  - `mssPre_eq_cata`: `Λ(prefix sum) est(≥) = ⦇[zero, ⊕]⦈`      (the greedy `⊑` closed to `=`)
  - `mss_shape`:      `Λ(segment sum) est(≥) = Λ(suffix) E(Λ(prefix sum) est(≥)) est(≥)`
                                                                (note `mss-shape`)

  `mss_shape`'s first step is the note's (`segment = suffix prefix`, then `Λ_absorption`); its
  remaining four (`union`, the `E`/`est` distribution, the relator) are collapsed into the one
  pointwise `mss_shape_union`, because the `⊒` half of `E(est R) est R = union est R` — the note's
  "the sets non-empty" side condition — is not in the repo.  Here the sets are non-empty because
  `Λ(prefix sum) est(≥)` is entire, which `mssPre_eq_cata` already gives.

  WHAT IS NOT HERE.  `mss-scan`'s fusion of `tails list(g)`, so the note's headline
  `mss = ⦇[zero wrap,⟨(𝟙×head)⊕,π₂⟩ cons]⦈ est(≥)` is NOT proved here.  That row also needs a
  bridge the note leaves informal: `tails` "implements" `Λ(suffix)` and `list(f)` "implements"
  `E(f)`, i.e. a LIST where the specification has a power object, so the trailing `est(≥)` there
  is `est` at `∋ := inlist` rather than at the power object's `∋`.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
module

public import AOP.A7_2
public import AOP.A7_4_Horner
public import AOP.A6_GenFold
public import AOP.A5_6_ListCombinators

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.MSS

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.ListRel

/-! ## The note's `mss-defn` -/

/-- The note's `≥` on `Int`, the order `est` maximises over. -/
@[expose] public def geq : (⟨Int⟩ : RelSet.{0}) ⟶ ⟨Int⟩ := fun a b => b ≤ a

/-- `≥` is transitive — the greedy theorem's preorder hypothesis. -/
public theorem geq_trans : geq ≫ geq ⊑ geq :=
  le_iff.mpr fun x z h => by
    obtain ⟨y, h1, h2⟩ := h
    exact Int.le_trans h2 h1

/-- `⊸ zero ∪ plus : Int×Int ⟶ Int` — start again at `zero`, or add the head to the running
    total. -/
@[expose] public def zeroPlus : (⟨Int × Int⟩ : RelSet.{0}) ⟶ ⟨Int⟩ :=
  (graph fun _ => (0 : Int)) ∪ (graph fun q => q.1 + q.2)

/-- The note's `S ≜ [zero, ⊸ zero ∪ plus]` — `prefix`'s algebra with `sum` fused in. -/
@[expose] public def Salg : Fobj Unit Int (⟨Int⟩ : RelSet.{0}) ⟶ ⟨Int⟩ :=
  junc (sumCop (dL Unit) ⟨Int × Int⟩) (graph fun _ => (0 : Int)) zeroPlus

theorem zeroPlus_apply (a b w : Int) : zeroPlus (a, b) w ↔ w = 0 ∨ w = a + b := Iff.rfl

theorem Salg_inl (d : Unit) (w : Int) : Salg (Sum.inl d) w ↔ w = 0 := by
  unfold Salg; exact junc_sum_inl _ _ _ _

theorem Salg_inr (a b w : Int) : Salg (Sum.inr (a, b)) w ↔ w = 0 ∨ w = a + b := by
  unfold Salg; exact junc_sum_inr _ _ _ _

/-- The note's `⊕ ≜ Λ(⊸ zero ∪ plus) est(≥)`: the set at `(a,b)` is `{0, a+b}`, so `⊕` is the
    larger of the two. -/
@[expose] public def oplus : (⟨Int × Int⟩ : RelSet.{0}) ⟶ ⟨Int⟩ := zeroPlus%∋ ≫ est(geq)

/-- Ex 7.40's specification `mss ≜ Λ(segment sum) est(≥)` — the greatest of the segment sums. -/
@[expose] public def mss : dCL Unit Int ⟶ (⟨Int⟩ : RelSet.{0}) :=
  (segment ≫ sumR)%∋ ≫ est(geq)

/-- The inner specification `Λ(prefix sum) est(≥)` — the greatest of the prefix sums, which is
    what the greedy theorem turns into a fold. -/
@[expose] public def mssPre : dCL Unit Int ⟶ (⟨Int⟩ : RelSet.{0}) :=
  (prefixR ≫ sumR)%∋ ≫ est(geq)

/-! ## The note's `mss-prefix-sum`: `prefix sum` is a catamorphism -/

/-- The `mss-prefix-sum` row: `prefix sum = ⦇[zero, ⊸ zero ∪ plus]⦈` — `prefix` is the reduce and
    `sum` the map fused into it, so the intermediate list is gone. -/
public theorem mss_prefix_sum : prefixR ≫ sumR = cataR Salg := by
  rw [cataR_eq_relCata]
  refine (relCata_UP (initial Unit Int) Salg (prefixR ≫ sumR)).mp
    ((cata_square_junc_iff _ _ _).mpr ⟨fun d r => ?_, fun a x r => ?_⟩)
  · constructor
    · rintro ⟨ys, hs, hl⟩
      cases ys with
      | wrap v => exact hl
      | cons b z => exact hs.elim
    · intro h
      exact ⟨ConsList.wrap (), prefixP.nil _, h⟩
  · constructor
    · rintro ⟨ys, hs, hl⟩
      cases ys with
      | wrap v =>
          exact ⟨0, ⟨ConsList.wrap (), prefixP.nil _, rfl⟩, Or.inl hl⟩
      | cons b z =>
          obtain ⟨hba, hzx⟩ := hs
          refine ⟨csum z, ⟨z, hzx, rfl⟩, Or.inr ?_⟩
          show r = a + csum z
          rw [hba] at hl
          exact hl
    · rintro ⟨y, ⟨zs, hzs, hy⟩, hcase⟩
      rcases hcase with hr | hr
      · exact ⟨ConsList.wrap (), prefixP.nil _, hr⟩
      · refine ⟨ConsList.cons a zs, ⟨rfl, hzs⟩, ?_⟩
        show r = a + csum zs
        rw [hr, hy]

/-! ## The note's `mss-mono` and the greedy row -/

/-- The `mss-mono` row: `F(≥) S ⊑ S ≥`, whose `plus` branch is `(𝟙×≥)(⊸ zero ∪ plus) ⊑
    (⊸ zero ∪ plus)≥` — `plus` is monotonic, so a bigger running total gives a bigger step;
    the `zero` branch is `zero ⊑ zero ≥`. -/
public theorem mss_mono : MonotonicAlg (F := F Unit Int) Salg geq := by
  show (F Unit Int).map geq ≫ Salg ⊑ Salg ≫ geq
  apply le_iff.mpr
  intro u w h
  obtain ⟨v, hv, hS⟩ := h
  cases u with
  | inl d =>
      cases v with
      | inl d' =>
          have hw : w = 0 := (Salg_inl d' w).mp hS
          subst hw
          exact ⟨0, (Salg_inl d 0).mpr rfl, Int.le_refl 0⟩
      | inr q => exact hv.elim
  | inr q =>
      obtain ⟨a, c⟩ := q
      cases v with
      | inl d' => exact hv.elim
      | inr q' =>
          obtain ⟨a', c'⟩ := q'
          obtain ⟨ha, hc⟩ := hv
          cases ha
          rcases (Salg_inr a c' w).mp hS with hw | hw
          · subst hw
            exact ⟨0, (Salg_inr a c 0).mpr (Or.inl rfl), Int.le_refl 0⟩
          · subst hw
            exact ⟨a + c, (Salg_inr a c _).mpr (Or.inr rfl), Int.add_le_add_left hc a⟩

/-- The greedy row: `⦇Λ(S) est(≥)⦈ ⊑ Λ(⦇S⦈) est(≥)` — Theorem 7.2 at the preorder `≥`, with
    `mss_mono` for its hypothesis. -/
public theorem mss_greedy : cataR (Salg%∋ ≫ est(geq)) ⊑ (cataR Salg)%∋ ≫ est(geq) := by
  rw [cataR_eq_relCata, cataR_eq_relCata]
  exact greedy (F_preservesRecip Unit Int) (initial Unit Int) geq_trans mss_mono

/-! ## The note's `mss-step`: the program algebra -/

/-- The `mss-step` row: `Λ(S) est(≥) = [zero, ⊕]` — the `zero` branch is a singleton, and the
    `plus` branch is `⊕`'s definition. -/
public theorem mss_step :
    Salg%∋ ≫ est(geq)
      = junc (sumCop (dL Unit) ⟨Int × Int⟩) (graph fun _ => (0 : Int)) oplus := by
  apply hom_ext; intro u w
  rw [Λ_comp_est_apply]
  cases u with
  | inl d =>
      rw [junc_sum_inl]
      constructor
      · rintro ⟨hS, -⟩
        exact (Salg_inl d w).mp hS
      · intro h
        refine ⟨(Salg_inl d w).mpr h, fun z hz => ?_⟩
        rw [(Salg_inl d z).mp hz, h]
        exact Int.le_refl 0
  | inr q =>
      obtain ⟨a, b⟩ := q
      rw [junc_sum_inr]
      show (Salg (Sum.inr (a, b)) w ∧ ∀ z, Salg (Sum.inr (a, b)) z → geq w z)
        ↔ (Λ zeroPlus ≫ est(geq)) (a, b) w
      rw [Λ_comp_est_apply]
      exact ⟨fun ⟨h1, h2⟩ => ⟨(Salg_inr a b w).mp h1,
               fun z hz => h2 z ((Salg_inr a b z).mpr hz)⟩,
             fun ⟨h1, h2⟩ => ⟨(Salg_inr a b w).mpr h1,
               fun z hz => h2 z ((Salg_inr a b z).mp hz)⟩⟩

/-- `⊕` as a function: the larger of `0` and `a+b`. -/
@[expose] public def oplusFn (a b : Int) : Int := if 0 ≤ a + b then a + b else 0

/-- `⊕` IS that function — the maximum of the two-element set `{0, a+b}` exists and is it. -/
public theorem oplus_eq :
    oplus = (graph (fun q : Int × Int => oplusFn q.1 q.2)
      : (⟨Int × Int⟩ : RelSet.{0}) ⟶ ⟨Int⟩) := by
  apply hom_ext
  rintro ⟨a, b⟩ w
  show (Λ zeroPlus ≫ est(geq)) (a, b) w ↔ w = oplusFn a b
  rw [Λ_comp_est_apply]
  unfold oplusFn
  rcases (inferInstance : Decidable (0 ≤ a + b)) with hneg | hpos
  · rw [if_neg hneg]
    have hab : a + b ≤ 0 := (Int.le_total 0 (a + b)).resolve_left hneg
    constructor
    · rintro ⟨h1, h2⟩
      rcases (zeroPlus_apply a b w).mp h1 with hw | hw
      · exact hw
      · have h0 : (0 : Int) ≤ w := h2 0 ((zeroPlus_apply a b 0).mpr (Or.inl rfl))
        rw [hw] at h0
        exact absurd h0 hneg
    · rintro rfl
      refine ⟨(zeroPlus_apply a b 0).mpr (Or.inl rfl), fun z hz => ?_⟩
      rcases (zeroPlus_apply a b z).mp hz with hz' | hz'
      · subst hz'; exact Int.le_refl 0
      · subst hz'; exact hab
  · rw [if_pos hpos]
    constructor
    · rintro ⟨h1, h2⟩
      refine Int.le_antisymm ?_ (h2 (a + b) ((zeroPlus_apply a b (a + b)).mpr (Or.inr rfl)))
      rcases (zeroPlus_apply a b w).mp h1 with hw | hw
      · subst hw; exact hpos
      · subst hw; exact Int.le_refl _
    · rintro rfl
      refine ⟨(zeroPlus_apply a b (a + b)).mpr (Or.inr rfl), fun z hz => ?_⟩
      rcases (zeroPlus_apply a b z).mp hz with hz' | hz'
      · subst hz'; exact hpos
      · subst hz'; exact Int.le_refl _

/-- The note's `[zero,⊕]` IS the program algebra `consScalarAlg zero ⊕`. -/
public theorem zero_oplus_eq_prog :
    junc (sumCop (dL Unit) ⟨Int × Int⟩) (graph fun _ => (0 : Int)) oplus
      = consScalarAlg (fun _ : Unit => (0 : Int)) oplusFn := by
  rw [oplus_eq]
  apply hom_ext; intro u w
  cases u with
  | inl d => rw [junc_sum_inl]; exact Iff.rfl
  | inr q => obtain ⟨a, b⟩ := q; rw [junc_sum_inr]; exact Iff.rfl

/-! ## Closing the greedy `⊑` to an equality -/

/-- The program: the running maximum prefix sum, by the recursion of `[zero,⊕]`. -/
@[expose] public def mssPreFn : ConsList Unit Int → Int
  | ConsList.wrap _ => 0
  | ConsList.cons a x => oplusFn a (mssPreFn x)

/-- **The program is produced by the fold law**: `mssPreFn` obeys the cons-list recursion of
    `zero` / `⊕`, so it IS the catamorphism of `[zero,⊕]`. -/
public theorem mssPre_emerges :
    (graph mssPreFn : dCL Unit Int ⟶ ⟨Int⟩)
      = cataR (consScalarAlg (fun _ : Unit => (0 : Int)) oplusFn) :=
  consFold_unique (fun _ => 0) oplusFn mssPreFn (fun _ => rfl) (fun _ _ => rfl)

/-- The specification is simple: two maxima of one set of prefix sums are equal (`≤` on `Int` is
    antisymmetric), so `Λ(prefix sum) est(≥)` is THE greatest, not A greatest. -/
public theorem mssPre_simple : Simple mssPre := by
  show mssPre° ≫ mssPre ⊑ Cat.id _
  apply le_iff.mpr
  intro w z h
  obtain ⟨u, h1, h2⟩ := h
  have h1' := (Λ_comp_est_apply (prefixR ≫ sumR) geq u w).mp h1
  have h2' := (Λ_comp_est_apply (prefixR ≫ sumR) geq u z).mp h2
  exact Int.le_antisymm (h2'.2 w h1'.1) (h1'.2 z h2'.1)

/-- **Ex 7.40's inner headline**: `Λ(prefix sum) est(≥) = ⦇[zero,⊕]⦈`.  B&dM ask only for the
    containment `⦇[zero,⊕]⦈ ⊆ max Λ(sum·prefix)`, which is the greedy row; it is an equality
    because the program is entire (a reduce of maps) and the specification simple. -/
public theorem mssPre_eq_cata :
    mssPre = cataR (consScalarAlg (fun _ : Unit => (0 : Int)) oplusFn) := by
  have hle : cataR (consScalarAlg (fun _ : Unit => (0 : Int)) oplusFn) ⊑ mssPre := by
    rw [← zero_oplus_eq_prog, ← mss_step]
    show cataR (Salg%∋ ≫ est(geq)) ⊑ (prefixR ≫ sumR)%∋ ≫ est(geq)
    rw [mss_prefix_sum]
    exact mss_greedy
  have hentire : Entire (cataR (consScalarAlg (fun _ : Unit => (0 : Int)) oplusFn)) := by
    rw [← mssPre_emerges]
    exact graph_entire _
  exact (eq_of_le_entire_simple hentire mssPre_simple hle).symm

/-! ## The note's `mss-shape` -/

/-- The specification IS the program function: `Λ(prefix sum) est(≥) = graph mssPreFn`. -/
public theorem mssPre_eq_graph : mssPre = (graph mssPreFn : dCL Unit Int ⟶ ⟨Int⟩) := by
  rw [mssPre_eq_cata, ← mssPre_emerges]

theorem mssPre_apply (s : ConsList Unit Int) (v : Int) : mssPre s v ↔ v = mssPreFn s := by
  rw [mssPre_eq_graph]; exact Iff.rfl

/-- `mssPreFn s` is a prefix sum of `s`, and it dominates every prefix sum of `s` — the two
    halves `est(≥)` asks for, read off the inner headline. -/
theorem mssPreFn_spec (s : ConsList Unit Int) :
    (prefixR ≫ sumR) s (mssPreFn s) ∧ ∀ z, (prefixR ≫ sumR) s z → z ≤ mssPreFn s :=
  (Λ_comp_est_apply (prefixR ≫ sumR) geq s (mssPreFn s)).mp ((mssPre_apply s _).mpr rfl)

/-- The `mss-shape` rows that move `est(≥)` inside the `E`: maximising over all prefix sums of
    all the suffixes is maximising over the per-suffix maxima.  (The note gets this from
    absorption, `union = E(∋)` and the `E`/`est` distribution; here it is one pointwise
    argument, and the per-suffix maximum exists because `Λ(prefix sum) est(≥)` is entire.) -/
public theorem mss_shape_union :
    existsImage (prefixR ≫ sumR) ≫ est(geq) = existsImage mssPre ≫ est(geq) := by
  apply hom_ext; intro P w
  rw [existsImage_comp_est_apply, existsImage_comp_est_apply]
  constructor
  · rintro ⟨⟨s, hPs, hTw⟩, hdom⟩
    have hw : w = mssPreFn s :=
      Int.le_antisymm ((mssPreFn_spec s).2 w hTw)
        (hdom (mssPreFn s) ⟨s, hPs, (mssPreFn_spec s).1⟩)
    refine ⟨⟨s, hPs, (mssPre_apply s w).mpr hw⟩, ?_⟩
    rintro z ⟨s', hPs', hz⟩
    exact hdom z ⟨s', hPs', by rw [(mssPre_apply s' z).mp hz]; exact (mssPreFn_spec s').1⟩
  · rintro ⟨⟨s, hPs, hw⟩, hdom⟩
    have hws : w = mssPreFn s := (mssPre_apply s w).mp hw
    refine ⟨⟨s, hPs, by rw [hws]; exact (mssPreFn_spec s).1⟩, ?_⟩
    rintro z ⟨s', hPs', hTz⟩
    exact Int.le_trans ((mssPreFn_spec s').2 z hTz)
      (hdom (mssPreFn s') ⟨s', hPs', (mssPre_apply s' _).mpr rfl⟩)

/-- **The `mss-shape` display**: `Λ(segment sum) est(≥) = Λ(suffix) E(Λ(prefix sum) est(≥)) est(≥)`
    — the greatest segment sum is the greatest of the per-suffix greatest prefix sums. -/
public theorem mss_shape : mss = suffixR%∋ ≫ existsImage mssPre ≫ est(geq) := by
  show (segment ≫ sumR)%∋ ≫ est(geq) = _
  rw [segment_eq, Cat.assoc, ← Λ_absorption, Cat.assoc, mss_shape_union]

/-! ## Executable sanity checks -/

/-- The greatest prefix sum of `[1,-2,3]` is `2` (the whole list). -/
example : mssPreFn (ofList [(1 : Int), -2, 3]) = 2 := by decide
/-- Every prefix sum negative ⇒ the empty prefix wins with `0`. -/
example : mssPreFn (ofList [(-1 : Int), -2]) = 0 := by decide

end Freyd.Alg.RelSet.MSS
