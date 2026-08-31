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

  WHAT IS NOT HERE, AND WHY IT CANNOT BE.  `mss-scan`'s fusion of `tails list(g)`, so the note's
  headline `mss = ⦇[zero wrap,⟨(𝟙×head)⊕,π₂⟩ cons]⦈ est(≥)` is NOT proved here.  The list in that
  row is not notational laziness for the power object: `suffixMax_not_relCata` shows NO algebra
  `h : 𝟏+Int×E(Int) ⟶ E(Int)` has `Λ(suffix) E(g) = ⦇h⦈`, `g ≜ ⦇[zero,⊕]⦈`.  `head` reads `g x`
  back off `tails x list(g)` because the list keeps the whole of `x` first; a set has no first
  element, so `E(g)` loses that value and the fold has nothing to feed `⊕`.

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

/-! ## Why `mss-scan` keeps the list

  The note's last row fuses `tails list(g)` into one fold through `head`, which reads `g x` back
  off the already-computed list because `tails` puts the whole of `x` first.  A set has no first
  element and `g` is not monotonic in the suffix order (`g[-1,2] = 1 < 2 = g[2]`), so `E(g)` loses
  that value: `xs = [1,-1]` and `ys = [-1,1]` have the SAME set of suffix maxima `{0,1}` while `g`
  gives them `1` and `0`, and `cons 3` separates the two sets again (`{4,1,0}` against `{3,1,0}`).
  A fold must send equal carriers to equal carriers, so it cannot do both. -/

/-- **`est(suffix)` is the power object's `head`**: the longest suffix of `x` is `x` itself, so
    `Λ(suffix) est(suffix) = 𝟙`.  The recovery `mss-scan` uses `head` for IS available here — what
    the power object loses is the recovered list's `g`-value, which is where `E(g)` bites. -/
public theorem Λ_suffix_comp_est {A : Type} : suffixR%∋ ≫ est(suffixR) = 𝟙 (dList A) := by
  apply hom_ext; intro x w
  rw [Λ_comp_est_apply]
  exact ⟨fun ⟨hw, hall⟩ => (suffixP_antisymm hw (hall x (suffixP.refl x))).symm,
    fun (h : x = w) => h ▸ ⟨suffixP.refl x, fun _ hz => hz⟩⟩

/-- `[1,-1]`: `g xs = 1`. -/
private def xs : ConsList Unit Int := ConsList.cons 1 (ConsList.cons (-1) (ConsList.wrap ()))
/-- `[-1,1]`: the same suffix maxima as `xs`, but `g ys = 0`. -/
private def ys : ConsList Unit Int := ConsList.cons (-1) (ConsList.cons 1 (ConsList.wrap ()))

/-- `suffix g` pointwise: `v` is `g` at some suffix of `s`. -/
private theorem suffix_mssPre_apply (s : ConsList Unit Int) (v : Int) :
    (suffixR ≫ mssPre) s v ↔ ∃ y, suffixP y s ∧ v = mssPreFn y :=
  ⟨fun ⟨y, hy, hv⟩ => ⟨y, hy, (mssPre_apply y v).mp hv⟩,
   fun ⟨y, hy, hv⟩ => ⟨y, hy, (mssPre_apply y v).mpr hv⟩⟩

/-- The suffix maxima of `[1,-1]`: `g[1,-1] = 1`, `g[-1] = 0`, `g[] = 0`. -/
private theorem suffix_mssPre_xs (v : Int) : (suffixR ≫ mssPre) xs v ↔ (v = 1 ∨ v = 0) := by
  rw [suffix_mssPre_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y = xs ∨ y = ConsList.cons (-1) (ConsList.wrap ()) ∨ y = ConsList.wrap () := hy
    rcases hy' with rfl | rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inr (by decide)
    · exact Or.inr (by decide)
  · rintro (rfl | rfl)
    · exact ⟨xs, show suffixP xs xs from Or.inl rfl, by decide⟩
    · exact ⟨ConsList.wrap (), show suffixP (ConsList.wrap ()) xs from Or.inr (Or.inr rfl),
        by decide⟩

/-- The suffix maxima of `[-1,1]`: `g[-1,1] = 0`, `g[1] = 1`, `g[] = 0` — the same set. -/
private theorem suffix_mssPre_ys (v : Int) : (suffixR ≫ mssPre) ys v ↔ (v = 1 ∨ v = 0) := by
  rw [suffix_mssPre_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y = ys ∨ y = ConsList.cons 1 (ConsList.wrap ()) ∨ y = ConsList.wrap () := hy
    rcases hy' with rfl | rfl | rfl
    · exact Or.inr (by decide)
    · exact Or.inl (by decide)
    · exact Or.inr (by decide)
  · rintro (rfl | rfl)
    · exact ⟨ConsList.cons 1 (ConsList.wrap ()),
        show suffixP (ConsList.cons 1 (ConsList.wrap ())) ys from Or.inr (Or.inl rfl), by decide⟩
    · exact ⟨ConsList.wrap (), show suffixP (ConsList.wrap ()) ys from Or.inr (Or.inr rfl),
        by decide⟩

/-- **The power object cannot take the note's last step.**  There is no algebra
    `h : 𝟏+Int×E(Int) ⟶ E(Int)` with `Λ(suffix) E(⦇[zero,⊕]⦈) = ⦇h⦈`: such an `h` would have to
    read `⦇[zero,⊕]⦈ x` back out of the SET of that fold's values on the suffixes of `x`, and
    `xs`, `ys` are two lists where the set is the same and the value is not. -/
public theorem suffixMax_not_relCata :
    ¬ ∃ h : (F Unit Int).obj (PowerAllegory.powerObj (⟨Int⟩ : RelSet.{0}))
              ⟶ PowerAllegory.powerObj (⟨Int⟩ : RelSet.{0}),
        suffixR%∋ ≫ existsImage mssPre = ⦇h⦈ := by
  rintro ⟨h, hh⟩
  have hcomm := (relCata_UP (initial Unit Int) h _).mpr hh
  rw [Λ_absorption, Λ_eq_classifier] at hcomm
  -- The fold's step at `cons a s` sees only `a` and the SET at `s`.
  have hstep : ∀ (a : Int) (s : ConsList Unit Int) (P : Int → Prop),
      classifier (suffixR ≫ mssPre) (ConsList.cons a s) P
        ↔ h (Sum.inr (a, fun v => (suffixR ≫ mssPre) s v)) P := by
    intro a s P
    have e := congrFun (congrFun hcomm (Sum.inr (a, s))) P
    constructor
    · intro hP
      have hl : ((initial Unit Int).α ≫ classifier (suffixR ≫ mssPre)) (Sum.inr (a, s)) P :=
        ⟨ConsList.cons a s, rfl, hP⟩
      rw [e] at hl
      obtain ⟨u, hu, hhu⟩ := hl
      cases u with
      | inl d => exact hu.elim
      | inr q =>
        obtain ⟨b, T⟩ := q
        obtain ⟨hab, hT⟩ := hu
        cases (hab : a = b)
        have hTeq : T = fun v => (suffixR ≫ mssPre) s v := hT
        rw [hTeq] at hhu
        exact hhu
    · intro hP
      have hr : ((F Unit Int).map (classifier (suffixR ≫ mssPre)) ≫ h) (Sum.inr (a, s)) P :=
        ⟨Sum.inr (a, fun v => (suffixR ≫ mssPre) s v), ⟨rfl, rfl⟩, hP⟩
      rw [← e] at hr
      obtain ⟨w, hw, hPw⟩ := hr
      have hweq : w = ConsList.cons a s := hw
      rw [hweq] at hPw
      exact hPw
  -- `xs` and `ys` carry the same set, so `cons 3` must give them the same set too.
  have hsame : (fun v => (suffixR ≫ mssPre) xs v) = fun v => (suffixR ≫ mssPre) ys v :=
    funext fun v => propext ((suffix_mssPre_xs v).trans (suffix_mssPre_ys v).symm)
  have hxs := (hstep 3 xs (fun v => (suffixR ≫ mssPre) (ConsList.cons 3 xs) v)).mp rfl
  rw [hsame] at hxs
  have hboth : (fun v => (suffixR ≫ mssPre) (ConsList.cons 3 xs) v)
      = fun v => (suffixR ≫ mssPre) (ConsList.cons 3 ys) v :=
    (hstep 3 ys (fun v => (suffixR ≫ mssPre) (ConsList.cons 3 xs) v)).mpr hxs
  -- But `4` is the maximum prefix sum of `[3,1,-1]`, and of no suffix of `[3,-1,1]`.
  have h4 : (suffixR ≫ mssPre) (ConsList.cons 3 xs) 4 :=
    (suffix_mssPre_apply _ 4).mpr
      ⟨ConsList.cons 3 xs, show suffixP (ConsList.cons 3 xs) (ConsList.cons 3 xs) from Or.inl rfl,
        by decide⟩
  obtain ⟨y, hy, hv⟩ := (suffix_mssPre_apply _ 4).mp (cast (congrFun hboth 4) h4)
  have hy' : y = ConsList.cons 3 ys ∨ y = ys ∨ y = ConsList.cons 1 (ConsList.wrap ())
      ∨ y = ConsList.wrap () := hy
  rcases hy' with rfl | rfl | rfl | rfl <;> exact absurd hv (by decide)

/-! ## Executable sanity checks -/

/-- The greatest prefix sum of `[1,-2,3]` is `2` (the whole list). -/
example : mssPreFn (ofList [(1 : Int), -2, 3]) = 2 := by decide
/-- Every prefix sum negative ⇒ the empty prefix wins with `0`. -/
example : mssPreFn (ofList [(-1 : Int), -2]) = 0 := by decide

end Freyd.Alg.RelSet.MSS
