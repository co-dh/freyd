/-
  Bird & de Moor, Exercise 7.41 (p. 174) — `filter` by the BOOK route, the greedy theorem.

  SPEC.  The book writes `filter p = max R · Λ(list p · subseq)`: the longest subsequence of `x`
  all of whose elements pass `p`, `R` the length preorder.  In diagram order and with this repo's
  one operator (`max R = est(R°)`) that is the note's `sec-filter` headline
      `filter(p) ≜ Λ(subseq list(p)) est(R°)`.

  ROUTE.  `sec-takewhile` with `subseq` for `prefix`: same `F`, `α`, `p`, `R`, same greedy theorem,
  and only the second branch of the algebra differs — `π₂` (drop the head) where takewhile has
  `⊸ nil` (stop).  One public theorem per row of the note's `filter-deriv`:

  - `filter_alg_comm` / `filter_alg`: `α subseq list(p) = F(subseq list(p)) S`, read off as
    `subseq list(p) = ⦇S⦈` by `relCata_UP`.  Fusion cannot derive it (`list(p)` is not entire),
    exactly as for takewhile, so the defining equation is proved pointwise.
  - `filter_mono`: `MonotonicAlg S R°` (`F(R°) S ⊑ S R°`).
  - `filter_greedy`: `⦇Λ(S) est(R°)⦈ ⊑ Λ(⦇S⦈) est(R°)` by Theorem 7.2.
  - `filter_step`: `Λ(S) est(R°) = [nil,(π₁p→cons,π₂)]`.
  - `filter_simple` / `filter_entire` / `filter_eq_cata`: the closing rows.  Simplicity does NOT
    come from the takewhile argument — two `p`-subsequences of one list can have equal length and
    differ — so it is proved through the canonical witness `filtCL`: every `p`-subsequence is a
    subsequence of `filtCL`, which is itself one, and a subsequence of its own length is the whole
    list.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
module

public import AOP.A7_7_TakeWhile
public import AOP.A5_6_ListCombinators

set_option linter.unusedVariables false

namespace Freyd.Alg.RelSet.Filter

open Freyd Freyd.Alg Freyd.Alg.RelSet.CL Freyd.Alg.RelSet.GCTakeWhile
open Freyd.Alg.RelSet.ListRel hiding listP prefixR

variable {A : Type}

/-! ## The note's `filter-defn`: the algebra `S` and the specification -/

/-- The note's `S ≜ [nil, π₂ ∪ (p×𝟙) cons]` — `subseq`'s algebra with one extra `p`: drop the
    head, or keep a head that passes `p`.  `π₂` is spelled as its Rel(Set) value `graph (·.2)`,
    as in `subseq_cata`, to keep `Classical.choice` out of the axioms. -/
@[expose] public def Salg (p : A → Bool) :
    Fobj Unit A (⟨List A⟩ : RelSet.{0}) ⟶ ⟨List A⟩ :=
  junc (sumCop (dL Unit) ⟨A × List A⟩) (graph fun _ => [])
    ((graph fun q => q.2) ∪ pcons p)

/-- Ex 7.41's specification: `filter(p) ≜ Λ(subseq list(p)) est(R°)` — the longest subsequence
    all of whose elements pass `p`. -/
@[expose] public def filter (p : A → Bool) : dCL Unit A ⟶ (⟨List A⟩ : RelSet.{0}) :=
  (subseq ≫ listP p)%∋ ≫ est(lenLE°)

/-- The `filter-defn` table's last row, `𝟙 ⊑ π₂ R cons°`: the tail is one shorter than the cons,
    so `π₂` loses the `est(R°)` at every step — where takewhile's loser is `nil`. -/
public theorem id_le_pi2_lenLE_cons :
    Cat.id (⟨A × List A⟩ : RelSet.{0})
      ⊑ (graph fun q => q.2) ≫ lenLE ≫ (graph fun q : A × List A => q.1 :: q.2)° :=
  le_iff.mpr fun q q' h => by
    obtain rfl : q = q' := h
    exact ⟨q.2, rfl, q.1 :: q.2, Nat.le_succ _, rfl⟩

/-! ### Pointwise unfolds of `S` -/

theorem Salg_inl (p : A → Bool) (D : Unit) (ws : List A) :
    Salg p (Sum.inl D) ws ↔ ws = [] := by
  unfold Salg; exact junc_sum_inl _ _ _ _

/-- `S`'s cons branch `π₂ ∪ (p×𝟙) cons` at `(x,c)`: drop the head, or keep a passing one. -/
public theorem Scons_apply (p : A → Bool) (x : A) (c ws : List A) :
    ((graph fun q : A × List A => q.2) ∪ pcons p) (x, c) ws
      ↔ ws = c ∨ (p x = true ∧ ws = x :: c) := by
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ((pcons_apply p x c ws).mp h)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ((pcons_apply p x c ws).mpr h)

theorem Salg_inr (p : A → Bool) (x : A) (c ws : List A) :
    Salg p (Sum.inr (x, c)) ws ↔ ws = c ∨ (p x = true ∧ ws = x :: c) := by
  unfold Salg
  exact (junc_sum_inr _ _ _ _).trans (Scons_apply p x c ws)

/-! ## The note's `filter-alg`: the defining equation -/

/-- The `filter-alg` display's headline: `α subseq list(p) = F(subseq list(p)) S` — building the
    list and then keeping a `p`-passing subsequence of it is keeping one of the tail first, and
    then building with `S`.  (Fusion is blocked — `list(p)` is not entire — so this is proved
    pointwise and fed to the universal property below.) -/
public theorem filter_alg_comm (p : A → Bool) :
    (initial Unit A).α ≫ (subseq ≫ listP p)
      = (F Unit A).map (subseq ≫ listP p) ≫ Salg p := by
  refine (cata_square_junc_iff _ _ _).mpr ⟨fun D r => ?_, fun a x r => ?_⟩
  · constructor
    · rintro ⟨ys, hs, hl⟩
      cases ys with
      | wrap v => exact (listPAlg_inl p v r).mp hl
      | cons b z => exact hs.elim
    · intro h
      exact ⟨ConsList.wrap (), subseqP.nil _, (listPAlg_inl p () r).mpr h⟩
  · constructor
    · rintro ⟨ys, hs, hl⟩
      cases ys with
      | wrap v =>
          have hr : r = [] := (listPAlg_inl p v r).mp hl
          exact ⟨[], ⟨ConsList.wrap (), subseqP.nil _, (listPAlg_inl p () _).mpr rfl⟩,
            (Scons_apply p a [] r).mpr (Or.inl hr)⟩
      | cons b z =>
          obtain ⟨y, hzy, hstep⟩ := hl
          obtain ⟨hpb, hr⟩ := (listPAlg_inr p b y r).mp hstep
          rcases hs with ⟨hba, hzx⟩ | hsub
          · exact ⟨y, ⟨z, hzx, hzy⟩,
              (Scons_apply p a y r).mpr (Or.inr ⟨hba ▸ hpb, hba ▸ hr⟩)⟩
          · exact ⟨r, ⟨ConsList.cons b z, hsub, y, hzy,
              (listPAlg_inr p b y r).mpr ⟨hpb, hr⟩⟩, (Scons_apply p a r r).mpr (Or.inl rfl)⟩
    · rintro ⟨y, ⟨zs, hzs, hzy⟩, hcase⟩
      rcases (Scons_apply p a y r).mp hcase with hr | ⟨hp, hr⟩
      · exact ⟨zs, subseqP.weaken hzs, hr ▸ hzy⟩
      · exact ⟨ConsList.cons a zs, Or.inl ⟨rfl, hzs⟩, y, hzy,
          (listPAlg_inr p a y r).mpr ⟨hp, hr⟩⟩

/-- The `filter-alg` row: `subseq list(p) = ⦇S⦈`, read off the defining equation above by the
    Eilenberg–Wright universal property. -/
public theorem filter_alg (p : A → Bool) : subseq ≫ listP p = cataR (Salg p) := by
  rw [cataR_eq_relCata]
  exact (relCata_UP (initial Unit A) (Salg p) (subseq ≫ listP p)).mp (filter_alg_comm p)

/-! ## The note's `filter-mono` and the greedy row -/

/-- **`filter-mono`'s first step**: `(𝟙×R°)(π₂ ∪ (p×𝟙) cons)=(𝟙×R°)π₂ ∪ (p×R°) cons` — `R°`
    reaches each operand of the `∪` on its own, and on the `cons` one it stands beside `p` as the
    pair's second strand. -/
public theorem filter_mono_step1 (p : A → Bool) :
    rprodMap (𝟙 (dE A)) (lenLE (A := A))° ≫ ((graph fun q : A × List A => q.2) ∪ pcons p)
      = rprodMap (𝟙 (dE A)) (lenLE (A := A))° ≫ (graph fun q : A × List A => q.2)
        ∪ rprodMap (pcor p) (lenLE (A := A))° ≫ graph fun q : A × List A => q.1 :: q.2 := by
  have hcons : rprodMap (𝟙 (dE A)) (lenLE (A := A))° ≫ pcons p
      = rprodMap (pcor p) (lenLE (A := A))° ≫ graph fun q : A × List A => q.1 :: q.2 := by
    unfold pcons
    rw [← Cat.assoc, rprodMap_comp, Cat.id_comp, Cat.comp_id]
  rw [DistributiveAllegory.comp_union_distrib, hcons]

/-- **`filter-mono`'s second step**: `(𝟙×R°)π₂ ∪ (p×R°) cons=π₂R° ∪ (p×R°) cons` — the
    projection's naturality square, `(𝟙×R°)π₂=π₂R°`. -/
public theorem filter_mono_step2 (p : A → Bool) :
    rprodMap (𝟙 (dE A)) (lenLE (A := A))° ≫ (graph fun q : A × List A => q.2)
        ∪ rprodMap (pcor p) (lenLE (A := A))° ≫ (graph fun q : A × List A => q.1 :: q.2)
      = (graph fun q : A × List A => q.2) ≫ (lenLE (A := A))°
        ∪ rprodMap (pcor p) (lenLE (A := A))° ≫ graph fun q : A × List A => q.1 :: q.2 := by
  rw [rprodMap_id_snd]

/-- **`filter-mono`'s third step**: `π₂R° ∪ (p×R°) cons ⊑ π₂R° ∪ (p×𝟙) cons R°` — the `cons`
    operand slides its `R°` out, which is `takewhile-mono`'s own step. -/
public theorem filter_mono_step3 (p : A → Bool) :
    (graph fun q : A × List A => q.2) ≫ (lenLE (A := A))°
        ∪ rprodMap (pcor p) (lenLE (A := A))° ≫ (graph fun q : A × List A => q.1 :: q.2)
      ⊑ (graph fun q : A × List A => q.2) ≫ (lenLE (A := A))°
        ∪ rprodMap (pcor p) (𝟙 (⟨List A⟩ : RelSet.{0}))
          ≫ (graph fun q : A × List A => q.1 :: q.2) ≫ lenLE° := by
  refine union_mono (le_refl _) ?_
  rw [← Cat.assoc]
  exact takewhile_mono_slide p

/-- The `filter-mono` row: `F(R°) S ⊑ S R°` — shortening the tail and then taking the step lands
    inside taking the step and then shortening the result.  The `π₂` branch is an equality
    (`π₂` is natural), where takewhile's `⊸ nil` branch buys it with `nil R° = nil`. -/
public theorem filter_mono_cons (p : A → Bool) :
    rprodMap (𝟙 (dE A)) (lenLE (A := A))° ≫ ((graph fun q : A × List A => q.2) ∪ pcons p)
      ⊑ ((graph fun q : A × List A => q.2) ∪ pcons p) ≫ lenLE° :=
  calc rprodMap (𝟙 (dE A)) (lenLE (A := A))° ≫ ((graph fun q : A × List A => q.2) ∪ pcons p)
      = rprodMap (𝟙 (dE A)) (lenLE (A := A))° ≫ (graph fun q : A × List A => q.2)
          ∪ rprodMap (pcor p) (lenLE (A := A))° ≫ graph fun q : A × List A => q.1 :: q.2 :=
        filter_mono_step1 p
    _ = (graph fun q : A × List A => q.2) ≫ (lenLE (A := A))°
          ∪ rprodMap (pcor p) (lenLE (A := A))° ≫ graph fun q : A × List A => q.1 :: q.2 :=
        filter_mono_step2 p
    _ ⊑ (graph fun q : A × List A => q.2) ≫ (lenLE (A := A))°
          ∪ rprodMap (pcor p) (𝟙 (⟨List A⟩ : RelSet.{0}))
            ≫ (graph fun q : A × List A => q.1 :: q.2) ≫ lenLE° := filter_mono_step3 p
    _ = ((graph fun q : A × List A => q.2) ∪ pcons p) ≫ lenLE° := by
        rw [← Cat.assoc]
        exact (union_comp_distrib _ _ _).symm

/-- The `filter-mono` header: **`F(R°) S ⊑ S R°`** — the `cons` chain above, with the leaf arm
    `nil ⊑ nil R°`. -/
public theorem filter_mono (p : A → Bool) :
    MonotonicAlg (F := F Unit A) (Salg p) lenLE° := by
  show (F Unit A).map lenLE° ≫ Salg p ⊑ Salg p ≫ lenLE°
  apply le_iff.mpr
  intro u ws h
  obtain ⟨v, hv, hS⟩ := h
  cases u with
  | inl D =>
      cases v with
      | inl d' =>
          have hws : ws = [] := (Salg_inl p d' ws).mp hS
          subst hws
          exact ⟨[], (Salg_inl p D []).mpr rfl, Nat.le_refl 0⟩
      | inr q => exact hv.elim
  | inr q =>
      cases v with
      | inl d' => exact hv.elim
      | inr q' =>
          -- `Salg`'s `cons` summand IS the `∪` the chain above works on, and `F(R°)` there is `𝟙×R°`.
          obtain ⟨vs, hvs, hlen⟩ :=
            le_iff.mp (filter_mono_cons p) q ws ⟨q', hv, (junc_sum_inr _ _ _ _).mp hS⟩
          exact ⟨vs, (junc_sum_inr _ _ _ _).mpr hvs, hlen⟩

/-- The greedy row: `⦇Λ(S) est(R°)⦈ ⊑ Λ(⦇S⦈) est(R°)` — Theorem 7.2 at the preorder `R°`, with
    `filter_mono` for its hypothesis: one longest `p`-subsequence kept at each `cons` refines
    every `p`-subsequence collected and one chosen at the end. -/
public theorem filter_greedy (p : A → Bool) :
    cataR ((Salg p)%∋ ≫ est(lenLE°)) ⊑ (cataR (Salg p))%∋ ≫ est(lenLE°) := by
  rw [cataR_eq_relCata, cataR_eq_relCata]
  exact greedy (F_preservesRecip Unit A) (initial Unit A) lenLE_recip_trans (filter_mono p)

/-! ## The note's `filter-step`: the program algebra -/

/-- The step of `filter`: keep a head that passes `p`, drop it otherwise. -/
@[expose] public def fStep (p : A → Bool) (x : A) (c : List A) : List A :=
  match p x with
  | true  => x :: c
  | false => c

theorem fStep_pos {p : A → Bool} {x : A} (h : p x = true) (c : List A) : fStep p x c = x :: c := by
  unfold fStep; rw [h]

theorem fStep_neg {p : A → Bool} {x : A} (h : p x = false) (c : List A) : fStep p x c = c := by
  unfold fStep; rw [h]

/-- The power object of `[A]`, and the product of two copies of it — where the `∪` of two
    transposes is taken. -/
public abbrev PL : RelProd (PowerAllegory.powerObj (⟨List A⟩ : RelSet.{0}))
    (PowerAllegory.powerObj (⟨List A⟩ : RelSet.{0})) :=
  relProd _ _

/-- Step 1 of `filter-step`: `S%∋ est(R°) = [nil%∋ est(R°),(π₂ ∪ (p×𝟙) cons)%∋ est(R°)]` — the
    transpose of a coproduct is the coproduct of the transposes, and `est(R°)` after a coproduct
    is the coproduct of the composites. -/
public theorem filter_step1 (p : A → Bool) (R : (⟨List A⟩ : RelSet.{0}) ⟶ ⟨List A⟩) :
    (Salg p)%∋ ≫ est(R°)
      = junc (sumCop (dL Unit) ⟨A × List A⟩)
          ((graph (fun _ => ([] : List A)) : dL Unit ⟶ (⟨List A⟩ : RelSet.{0}))%∋ ≫ est(R°))
          ((((graph fun q : A × List A => q.2)) ∪ pcons p)%∋ ≫ est(R°)) := by
  unfold Salg; exact junc_Λ_est _ _ _ R°

/-- Step 2 of `filter-step`: `nil%∋ est(R°) = nil` for reflexive `R°` — the `nil` arm, as in
    `takewhile-step`. -/
public theorem filter_step2 (p : A → Bool) {R : (⟨List A⟩ : RelSet.{0}) ⟶ ⟨List A⟩}
    (hrefl : Cat.id (⟨List A⟩ : RelSet.{0}) ⊑ R°) :
    junc (sumCop (dL Unit) ⟨A × List A⟩)
        ((graph (fun _ => ([] : List A)) : dL Unit ⟶ (⟨List A⟩ : RelSet.{0}))%∋ ≫ est(R°))
        ((((graph fun q : A × List A => q.2)) ∪ pcons p)%∋ ≫ est(R°))
      = junc (sumCop (dL Unit) ⟨A × List A⟩)
          (graph (fun _ => ([] : List A)) : dL Unit ⟶ (⟨List A⟩ : RelSet.{0}))
          ((((graph fun q : A × List A => q.2)) ∪ pcons p)%∋ ≫ est(R°)) := by
  rw [Λ_nil_comp_est hrefl]

/-- Step 3 of `filter-step`: `(π₂ ∪ (p×𝟙) cons)%∋ = ⟨π₂%∋,((p×𝟙) cons)%∋⟩ cup` — the transpose of
    a union is the pair of the transposes followed by the power object's union. -/
public theorem filter_step3 (p : A → Bool) (R : (⟨List A⟩ : RelSet.{0}) ⟶ ⟨List A⟩) :
    junc (sumCop (dL Unit) ⟨A × List A⟩)
        (graph (fun _ => ([] : List A)) : dL Unit ⟶ (⟨List A⟩ : RelSet.{0}))
        ((((graph fun q : A × List A => q.2)) ∪ pcons p)%∋ ≫ est(R°))
      = junc (sumCop (dL Unit) ⟨A × List A⟩)
          (graph (fun _ => ([] : List A)) : dL Unit ⟶ (⟨List A⟩ : RelSet.{0}))
          (rpair ((graph fun q : A × List A => q.2)%∋) ((pcons p)%∋)
            ≫ cup (PL (A := A)) ≫ est(R°)) := by
  rw [Λ_union _ _ (PL (A := A)), pair_eq_rpair, Cat.assoc]

/-- Step 4 of `filter-step`: `[nil,⟨π₂%∋,((p×𝟙) cons)%∋⟩ cup est(R°)] = [nil,(π₁p→cons,π₂)]` — at
    `(a,xs)` the union is `{xs}` where `p` fails on `a` and `{xs,cons(a,xs)}` where it holds, and
    `xs` loses the second.  The head is dropped, not the whole tail: the one place `π₂` shows
    against takewhile's `⊸ nil`. -/
public theorem filter_step4 (p : A → Bool) :
    junc (sumCop (dL Unit) ⟨A × List A⟩)
        (graph (fun _ => ([] : List A)) : dL Unit ⟶ (⟨List A⟩ : RelSet.{0}))
        (rpair ((graph fun q : A × List A => q.2)%∋) ((pcons p)%∋)
          ≫ cup (PL (A := A)) ≫ est(lenLE°))
      = consScalarAlg (fun _ : Unit => ([] : List A)) (fStep p) := by
  rw [← filter_step3]
  apply hom_ext; intro u ws
  cases u with
  | inl D => rw [junc_sum_inl]; exact Iff.rfl
  | inr q =>
      obtain ⟨x, c⟩ := q
      rw [junc_sum_inr, Λ_comp_est_apply]
      constructor
      · rintro ⟨hS, hmax⟩
        show ws = fStep p x c
        rcases (Scons_apply p x c ws).mp hS with hws | ⟨hp, hws⟩
        · subst hws
          cases hpx : p x with
          | false => rw [fStep_neg hpx]
          | true =>
              have hz := hmax (x :: ws) ((Scons_apply p x ws _).mpr (Or.inr ⟨hpx, rfl⟩))
              exact absurd hz (Nat.not_succ_le_self _)
        · rw [fStep_pos hp, hws]
      · intro h0
        have hws : ws = fStep p x c := h0
        cases hpx : p x with
        | true =>
            rw [fStep_pos hpx] at hws
            subst hws
            refine ⟨(Scons_apply p x c _).mpr (Or.inr ⟨hpx, rfl⟩), fun z hz => ?_⟩
            rcases (Scons_apply p x c z).mp hz with hz' | ⟨-, hz'⟩
            · subst hz'; exact Nat.le_succ _
            · subst hz'; exact Nat.le_refl _
        | false =>
            rw [fStep_neg hpx] at hws
            subst hws
            refine ⟨(Scons_apply p x ws _).mpr (Or.inl rfl), fun z hz => ?_⟩
            rcases (Scons_apply p x ws z).mp hz with hz' | ⟨hp', hz'⟩
            · subst hz'; exact Nat.le_refl _
            · rw [hpx] at hp'; nomatch hp'

/-- The `filter-step` row: `Λ(S) est(R°) = [nil,(π₁p→cons,π₂)]` — at `(a,xs)` the algebra allows
    `{xs}` where `p` fails on `a` and `{xs,cons(a,xs)}` where it holds, and `xs` loses the second.
    The head is dropped, not the whole tail: the one place `π₂` shows against takewhile's
    `⊸ nil`. -/
public theorem filter_step (p : A → Bool) :
    (Salg p)%∋ ≫ est(lenLE°) = consScalarAlg (fun _ : Unit => ([] : List A)) (fStep p) :=
  (filter_step1 p lenLE).trans ((filter_step2 p lenLE_recip_refl).trans
    ((filter_step3 p lenLE).trans (filter_step4 p)))

/-! ## The closing rows: the program, its entirety, and the specification's simplicity -/

/-- `filter p` on `ConsList Unit E`, by the very recursion whose base/step is `fun _ => []` /
    `fStep p`. -/
@[expose] public def filtCL (p : A → Bool) : ConsList Unit A → List A
  | ConsList.wrap _ => []
  | ConsList.cons x xs => fStep p x (filtCL p xs)

theorem filtCL_wrap (p : A → Bool) (D : Unit) : filtCL p (ConsList.wrap D) = [] := rfl

theorem filtCL_cons (p : A → Bool) (x : A) (t : ConsList Unit A) :
    filtCL p (ConsList.cons x t) = fStep p x (filtCL p t) := rfl

/-- **The program is produced by the fold law**: `filtCL p` obeys the cons-list recursion of its
    base/step, so it IS the catamorphism of `consScalarAlg (fun _ => []) (fStep p)`. -/
public theorem filter_emerges (p : A → Bool) :
    (graph (filtCL p) : dCL Unit A ⟶ ⟨List A⟩)
      = cataR (consScalarAlg (fun _ : Unit => ([] : List A)) (fStep p)) :=
  consFold_unique (fun _ => []) (fStep p) (filtCL p) (fun _ => rfl) (fun _ _ => rfl)

/-- `ws` is a subsequence of `xs` (drop elements) — `subseqP` on the raw-list carrier, as `Pre`
    is `prefixP` there. -/
@[expose] public def Sub : List A → List A → Prop
  | [], _ => True
  | _ :: _, [] => False
  | w :: ws, x :: xs => (w = x ∧ Sub ws xs) ∨ Sub (w :: ws) xs

/-- The empty list is a subsequence of every list. -/
theorem Sub.nil : ∀ b : List A, Sub [] b
  | [] => trivial
  | _ :: _ => trivial

/-- A subsequence is no longer than its host. -/
theorem sub_length : ∀ {a b : List A}, Sub a b → a.length ≤ b.length
  | [], _, _ => Nat.zero_le _
  | _ :: _, [], h => h.elim
  | w :: ws, x :: xs, h => by
      rcases h with ⟨-, hs⟩ | hs
      · exact Nat.succ_le_succ (sub_length hs)
      · exact Nat.le_trans (sub_length hs) (Nat.le_succ _)

/-- A subsequence of its host's length IS the host. -/
theorem sub_eq_of_length : ∀ {a b : List A}, Sub a b → b.length ≤ a.length → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, _, hlen => absurd hlen (Nat.not_succ_le_zero _)
  | _ :: _, [], h, _ => h.elim
  | w :: ws, x :: xs, h, hlen => by
      rcases h with ⟨hwx, hs⟩ | hs
      · rw [hwx, sub_eq_of_length hs (Nat.le_of_succ_le_succ hlen)]
      · exact absurd (Nat.le_trans hlen (sub_length hs)) (Nat.not_succ_le_self _)

/-- Achievability: `filtCL p u` is itself a `p`-passing subsequence of the list `u` carries. -/
public theorem filt_sound (p : A → Bool) :
    ∀ u : ConsList Unit A, (subseq ≫ listP p) u (filtCL p u)
  | ConsList.wrap D => ⟨ConsList.wrap (), subseqP.nil _, (listPAlg_inl p () _).mpr (filtCL_wrap p D)⟩
  | ConsList.cons x t => by
      obtain ⟨ys, hs, hl⟩ := filt_sound p t
      rw [filtCL_cons]
      cases hpx : p x with
      | true =>
          refine ⟨ConsList.cons x ys, Or.inl ⟨rfl, hs⟩, filtCL p t, hl, ?_⟩
          exact (listPAlg_inr p x (filtCL p t) _).mpr ⟨hpx, fStep_pos hpx _⟩
      | false =>
          exact ⟨ys, subseqP.weaken hs, by rw [fStep_neg hpx]; exact hl⟩

/-- Domination: every `p`-passing subsequence is a subsequence of `filtCL p u` — a subsequence
    that drops a passing element is beaten by the one that keeps it. -/
public theorem filt_best (p : A → Bool) :
    ∀ (u : ConsList Unit A) (ws : List A), (subseq ≫ listP p) u ws → Sub ws (filtCL p u)
  | ConsList.wrap D, ws, ⟨ys, hs, hl⟩ => by
      cases ys with
      | wrap v =>
          have hws : ws = [] := (listPAlg_inl p v ws).mp hl
          subst hws; exact Sub.nil _
      | cons b z => exact hs.elim
  | ConsList.cons x t, ws, ⟨ys, hs, hl⟩ => by
      rw [filtCL_cons]
      cases ys with
      | wrap v =>
          have hws : ws = [] := (listPAlg_inl p v ws).mp hl
          subst hws; exact Sub.nil _
      | cons b z =>
          obtain ⟨y, hzy, hstep⟩ := hl
          obtain ⟨hpb, hws⟩ := (listPAlg_inr p b y ws).mp hstep
          subst hws
          rcases hs with ⟨hbx, hzt⟩ | hsub
          · rw [fStep_pos (hbx ▸ hpb : p x = true)]
            exact Or.inl ⟨hbx, filt_best p t y ⟨z, hzt, hzy⟩⟩
          · have htail : Sub (b :: y) (filtCL p t) :=
              filt_best p t (b :: y) ⟨ConsList.cons b z, hsub, y, hzy,
                (listPAlg_inr p b y _).mpr ⟨hpb, rfl⟩⟩
            cases hpx : p x with
            | true => rw [fStep_pos hpx]; exact Or.inr htail
            | false => rw [fStep_neg hpx]; exact htail

/-- The simplicity row: `filter(p)° filter(p) ⊑ 𝟙`.  NOT the takewhile argument — two
    `p`-subsequences of one list can be of equal length and different — but through `filtCL`:
    a longest `p`-subsequence is a subsequence of `filtCL p u` of its length, hence IS it. -/
public theorem filter_simple (p : A → Bool) : Simple (filter p) := by
  show (filter p)° ≫ filter p ⊑ Cat.id _
  apply le_iff.mpr
  intro ws zs h
  obtain ⟨u, h1, h2⟩ := h
  have h1' := (Λ_comp_est_apply (subseq ≫ listP p) ((lenLE (A := A))°) u ws).mp h1
  have h2' := (Λ_comp_est_apply (subseq ≫ listP p) ((lenLE (A := A))°) u zs).mp h2
  have e1 : ws = filtCL p u :=
    sub_eq_of_length (filt_best p u ws h1'.1) (h1'.2 _ (filt_sound p u))
  have e2 : zs = filtCL p u :=
    sub_eq_of_length (filt_best p u zs h2'.1) (h2'.2 _ (filt_sound p u))
  rw [e1, e2]
  exact rfl

/-- **Ex 7.41's headline** (the note's `filter-deriv`): `filter(p) = ⦇[nil,(π₁p→cons,π₂)]⦈`.
    The greedy `⊒` becomes `=`: the program is entire (a reduce of maps) and the specification
    is simple, so `eq_of_le_entire_simple` closes the gap. -/
public theorem filter_eq_cata (p : A → Bool) :
    filter p = cataR (consScalarAlg (fun _ : Unit => ([] : List A)) (fStep p)) := by
  have hle : cataR (consScalarAlg (fun _ : Unit => ([] : List A)) (fStep p)) ⊑ filter p := by
    rw [← filter_step p]
    show cataR ((Salg p)%∋ ≫ est(lenLE°)) ⊑ (subseq ≫ listP p)%∋ ≫ est(lenLE°)
    rw [filter_alg p]
    exact filter_greedy p
  have hentire : Entire (cataR (consScalarAlg (fun _ : Unit => ([] : List A)) (fStep p))) := by
    rw [← filter_emerges p]
    exact graph_entire _
  exact (eq_of_le_entire_simple hentire (filter_simple p) hle).symm

/-- The entirety row: `Λ(subseq list(p)) est(R°)` is entire — `nil` is always a `p`-subsequence
    and a longest one exists; read off the headline, whose program is a reduce of maps. -/
public theorem filter_entire (p : A → Bool) : Entire (filter p) := by
  rw [filter_eq_cata p, ← filter_emerges p]
  exact graph_entire _

/-! ## Executable sanity checks -/

/-- `filter even [1,2,3,4] = [2,4]`. -/
example : filtCL (fun n => decide (n % 2 = 0)) (ofList [1, 2, 3, 4]) = [2, 4] := by decide
/-- Nothing passes ⇒ the empty list. -/
example : filtCL (fun n => decide (n % 2 = 0)) (ofList [1, 3]) = [] := by decide
/-- The head fails but the tail survives — where `takewhile` would stop. -/
example : filtCL (fun n => decide (n < 3)) (ofList [5, 1, 2]) = [1, 2] := by decide

-- printing-only: the note calls the algebra a fold folds with `S`.  WHICH predicate it filters on
-- is the context every panel of the section is drawn in, not part of the arrow's name.
open Lean PrettyPrinter in
@[app_unexpander Salg] public meta def unexpandSalg : Unexpander
  | _ => `($(mkIdent `S))

end Freyd.Alg.RelSet.Filter
