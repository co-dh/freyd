/-
  Bird & de Moor, *Algebra of Programming* §10.3  The minimum tardiness problem (book pp. 253-258)
  — a worked program in the Set model, over snoc-lists of jobs.

  Given a BAG of jobs, find an ordering of it — a SCHEDULE — whose maximum penalty is least.
  The specification is `schedule ⊆ min R·Λbagify°` with `R = cost°·leq·cost`, mirrored
  `Λ (bagify°) ≫ est R`.

  Why §10.3 needs more than §10.2's `greedy_dp`: B&dM p.255 says "for this problem we need to
  bring context into both the monotonicity and greedy conditions".  `[nil,snoc]` is NOT monotonic
  on `R` — `cost x ≤ cost y` says nothing about `penalty (x,j)` versus `penalty (y,j)`, which
  reads the COMPLETION TIME of the schedule, not its cost.  It is monotonic on `R ∩ (bagify°
  bagify)`: two schedules of the SAME BAG have the same completion time, so the penalties agree
  and `bmax` is monotone.  §10.2's `greedy_dp` (`AOP.A10_1`) has no such context, so the context
  form of Theorem 10.1 is proved here first — `greedy_dp_context`, which stands to `greedy_dp`
  exactly as `AOP.A9_1`'s `dynamic_programming_thin_context` (Ex 9.2) stands to
  `dynamic_programming_thin`, and reuses that file's two context hypotheses verbatim.
-/
module

public import AOP.A10_1
public import AOP.A6_SnocList
public import AOP.A6_MonoFactor
public import AOP.A7_4_Horner
import AOP.CalcSteps

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [TabularUnitaryUnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {A B : 𝒜}

/-! ## Theorem 10.1 in context (B&dM p.255) — the greedy theorem on domains of definition -/

/-- The sharpened tail bound: greedily choosing an `est Q`-minimum decomposition after unfolding
    by `T` only ever needs `Q` on `T`'s own domain of definition, `T ≫ T°`.  The `est` twin of
    `AOP.A9_1`'s `thin_unfold_context_le`; both halves come from the `min` universal property
    (`inter_lb_left` for membership, `recip_eps_comp_est_le` for the lower bound). -/
public theorem est_unfold_context_le (T : F.obj B ⟶ B) (Q : F.obj B ⟶ F.obj B) :
    T ≫ Λ (T°) ≫ est Q ⊑ (Q ∩ (T ≫ T°))° := by
  have hTA : T ≫ Λ (T°) ⊑ (∋ (F.obj B))° := by
    have h0 := recip_comp_Λ_le_recip_eps (T°)
    rwa [Allegory.recip_recip] at h0
  have hQ : T ≫ Λ (T°) ≫ est Q ⊑ Q° := by
    have t1 : T ≫ Λ (T°) ≫ est Q ⊑ (∋ (F.obj B))° ≫ est Q := by
      rw [← Cat.assoc T (Λ (T°)) _]
      exact comp_mono_right hTA _
    exact le_trans t1 (recip_eps_comp_est_le Q)
  have hT : T ≫ Λ (T°) ≫ est Q ⊑ T ≫ T° := by
    have t1 : T ≫ Λ (T°) ≫ est Q ⊑ T ≫ Λ (T°) ≫ ∋ (F.obj B) :=
      comp_mono_left _ (comp_mono_left _ (show est Q ⊑ ∋ (F.obj B) from inter_lb_left _ _))
    rwa [Λ_eps_eq'] at t1
  have hrec : (Q ∩ (T ≫ T°))° = Q° ∩ (T ≫ T°) := by
    rw [Allegory.recip_inter, Allegory.recip_comp, Allegory.recip_recip]
  rw [hrec]
  exact le_inter hQ hT

/-- **Core of Theorem 10.1 in context** (B&dM p.255): `M = min R°·ΛH` is a prefixed point of the
    greedy body even when monotonicity holds only on `R° ∩ (H°·H)` and the greedy condition only
    on `Q ∩ (T·T°)` — the two hypotheses `AOP.A9_1`'s `dp_thin_prefixed_context` uses.  Same
    skeleton as `AOP.A10_1`'s `greedy_dp_prefixed`, with `est_unfold_context_le` in place of the
    unrestricted tail bound and `hctx1` in place of `MonotonicAlg h R`. -/
public theorem greedy_dp_prefixed_context {h : F.obj A ⟶ A}
    {T : F.obj B ⟶ B} {R : A ⟶ A} {Q : F.obj B ⟶ F.obj B} {H : B ⟶ A} (hh : Map h)
    (hctx1 : F.map (R° ∩ (H° ≫ H)) ≫ h ⊑ h ≫ R°) (htrans : R ≫ R ⊑ R)
    (hHfix : T° ≫ F.map H ≫ h = H)
    (hctx2 : (Q ∩ (T ≫ T°)) ≫ F.map H ≫ h ⊑ F.map H ≫ h ≫ R) :
    Λ (T°) ≫ est Q ≫ F.map (Λ H ≫ est R) ≫ h ⊑ Λ H ≫ est R := by
  have htrans' : R° ≫ R° ⊑ R° := by
    have h0 := recip_mono htrans
    rwa [Allegory.recip_comp] at h0
  obtain ⟨hMH, hHMR⟩ := le_Λ_comp_est_iff.mp (le_refl (Λ H ≫ est R))
  apply le_Λ_comp_est_iff.mpr
  constructor
  · -- component (i): greedy body ⊑ H, via `min Q° ⊆ ∈` and the fixed-point equation
    have s1 : Λ (T°) ≫ est Q ≫ F.map (Λ H ≫ est R) ≫ h
        ⊑ Λ (T°) ≫ ∋ (F.obj B) ≫ F.map (Λ H ≫ est R) ≫ h :=
      comp_mono_left _ (comp_mono_right (show est Q ⊑ ∋ (F.obj B) from inter_lb_left _ _) _)
    have s2 : Λ (T°) ≫ ∋ (F.obj B) ≫ F.map (Λ H ≫ est R) ≫ h
        = T° ≫ F.map (Λ H ≫ est R) ≫ h := by
      rw [← Cat.assoc (Λ (T°)) (∋ (F.obj B)) _, Λ_eps_eq']
    have s3 : T° ≫ F.map (Λ H ≫ est R) ≫ h ⊑ T° ≫ F.map H ≫ h :=
      comp_mono_left _ (comp_mono_right (F.map_mono hMH) h)
    rw [s2] at s1
    rw [hHfix] at s3
    exact le_trans s1 s3
  · -- component (ii): `H°·(greedy body) ⊑ R°`, at `Q ∩ (T ≫ T°)` throughout
    have hHrec : H° = h° ≫ F.map (H°) ≫ T := by
      have h1 : (T° ≫ F.map H ≫ h)° = h° ≫ F.map (H°) ≫ T := by
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, ← Relator.preservesRecip_of_tabular F H, Cat.assoc]
      rw [← h1, hHfix]
    have htail : T ≫ Λ (T°) ≫ est Q ⊑ (Q ∩ (T ≫ T°))° := est_unfold_context_le T Q
    have c1 : H° ≫ Λ (T°) ≫ est Q ≫ F.map (Λ H ≫ est R) ≫ h
        = (h° ≫ F.map (H°) ≫ T) ≫ Λ (T°) ≫ est Q ≫ F.map (Λ H ≫ est R) ≫ h := by
      rw [← hHrec]
    have c2 : (h° ≫ F.map (H°) ≫ T) ≫ Λ (T°) ≫ est Q ≫ F.map (Λ H ≫ est R) ≫ h
        = (h° ≫ F.map (H°)) ≫ (T ≫ Λ (T°) ≫ est Q) ≫ F.map (Λ H ≫ est R) ≫ h := by
      simp only [Cat.assoc]
    have hbound : (h° ≫ F.map (H°)) ≫ (T ≫ Λ (T°) ≫ est Q) ≫ F.map (Λ H ≫ est R) ≫ h
        ⊑ (h° ≫ F.map (H°)) ≫ (Q ∩ (T ≫ T°))° ≫ F.map (Λ H ≫ est R) ≫ h :=
      comp_mono_left _ (comp_mono_right htail _)
    have hctx2rec : h° ≫ F.map (H°) ≫ (Q ∩ (T ≫ T°))° ⊑ R° ≫ h° ≫ F.map (H°) := by
      have hrm := recip_mono hctx2
      have eL : ((Q ∩ (T ≫ T°)) ≫ F.map H ≫ h)° = h° ≫ F.map (H°) ≫ (Q ∩ (T ≫ T°))° := by
        rw [Allegory.recip_comp, Allegory.recip_comp, ← Relator.preservesRecip_of_tabular F H, Cat.assoc]
      have eR : (F.map H ≫ h ≫ R)° = R° ≫ h° ≫ F.map (H°) := by
        rw [Allegory.recip_comp, Allegory.recip_comp, ← Relator.preservesRecip_of_tabular F H, Cat.assoc]
      rwa [eL, eR] at hrm
    have hre1 : (h° ≫ F.map (H°)) ≫ (Q ∩ (T ≫ T°))° ≫ F.map (Λ H ≫ est R) ≫ h
        = (h° ≫ F.map (H°) ≫ (Q ∩ (T ≫ T°))°) ≫ F.map (Λ H ≫ est R) ≫ h := by
      simp only [Cat.assoc]
    have step6 : (h° ≫ F.map (H°) ≫ (Q ∩ (T ≫ T°))°) ≫ F.map (Λ H ≫ est R) ≫ h
        ⊑ (R° ≫ h° ≫ F.map (H°)) ≫ F.map (Λ H ≫ est R) ≫ h :=
      comp_mono_right hctx2rec _
    have hre2 : (R° ≫ h° ≫ F.map (H°)) ≫ F.map (Λ H ≫ est R) ≫ h
        = R° ≫ (h° ≫ F.map (H°) ≫ F.map (Λ H ≫ est R) ≫ h) := by
      simp only [Cat.assoc]
    -- the context collapse: `F(H°·M) ⊆ F(R° ∩ H°·H)`, then `hctx1` and simplicity of `h`
    have hHM_ctx : H° ≫ (Λ H ≫ est R) ⊑ R° ∩ (H° ≫ H) :=
      le_inter hHMR (comp_mono_left H° hMH)
    have hFRM_ctx : F.map (H°) ≫ F.map (Λ H ≫ est R) ⊑ F.map (R° ∩ (H° ≫ H)) := by
      rw [← F.map_comp]; exact F.map_mono hHM_ctx
    have hx_ctx : h° ≫ F.map (H°) ≫ F.map (Λ H ≫ est R) ≫ h
        ⊑ h° ≫ F.map (R° ∩ (H° ≫ H)) ≫ h := by
      rw [← Cat.assoc (F.map (H°)) (F.map (Λ H ≫ est R)) h]
      exact comp_mono_left _ (comp_mono_right hFRM_ctx h)
    have hshunt : h° ≫ (F.map (R° ∩ (H° ≫ H)) ≫ h) ⊑ h° ≫ (h ≫ R°) := comp_mono_left h° hctx1
    have hcollapse : h° ≫ (h ≫ R°) ⊑ R° := by
      have e : h° ≫ (h ≫ R°) = (h° ≫ h) ≫ R° := by rw [Cat.assoc]
      rw [e]
      have e2 := comp_mono_right hh.2 R°
      rwa [Cat.id_comp] at e2
    have hinner : h° ≫ F.map (H°) ≫ F.map (Λ H ≫ est R) ≫ h ⊑ R° :=
      le_trans hx_ctx (le_trans hshunt hcollapse)
    have step7 : R° ≫ (h° ≫ F.map (H°) ≫ F.map (Λ H ≫ est R) ≫ h) ⊑ R° ≫ R° :=
      comp_mono_left R° hinner
    rw [c1, c2]
    refine le_trans hbound ?_
    rw [hre1]
    refine le_trans step6 ?_
    rw [hre2]
    exact le_trans step7 htrans'

/-- **Theorem 10.1 in context** (B&dM p.255): the greedy recursion refines `min R°·ΛH` when
    monotonicity holds only on `R° ∩ (H°·H)` and the greedy condition only on `Q ∩ (T·T°)` — the
    form §10.3 needs, where only schedules of the SAME BAG are ever compared.  By Knaster-Tarski
    via `greedy_dp_prefixed_context`. -/
public theorem greedy_dp_context (I : InitialAlgebra F)
    {h : F.obj A ⟶ A} {T : F.obj B ⟶ B} {R : A ⟶ A} {Q : F.obj B ⟶ F.obj B} (hh : Map h)
    (hctx1 : F.map (R° ∩ (((relCata T)° ≫ relCata h)° ≫ (relCata T)° ≫ relCata h)) ≫ h
        ⊑ h ≫ R°)
    (htrans : R ≫ R ⊑ R)
    (hctx2 : (Q ∩ (T ≫ T°)) ≫ F.map ((relCata T)° ≫ relCata h) ≫ h
        ⊑ F.map ((relCata T)° ≫ relCata h) ≫ h ≫ R) :
    mu (fun X : B ⟶ A => Λ (T°) ≫ est Q ≫ F.map X ≫ h)
      ⊑ Λ ((relCata T)° ≫ relCata h) ≫ est R :=
  LocallyCompleteDistributiveAllegory.Sup_le (fun _S hS => hS _
    (greedy_dp_prefixed_context hh hctx1 htrans (hylo_fixed I h T) hctx2))

end Freyd.Alg

namespace Freyd.Alg.RelSet.Tardy

open Freyd Freyd.Alg.RelSet Freyd.Alg.RelSet.SL

variable {Job : Type}

/-! ## Bags of jobs (`tardy-defn`)

  A bag is a list up to permutation.  `bagify` is the catamorphism of `β ≜ [nil,snag]`, so the
  bag of a schedule is its underlying list of jobs with the order forgotten; `H = bagify°` sends
  a bag to every ordering of it. -/

/-- Permutation, the equivalence a bag quotients by. -/
public instance permSetoid (Job : Type) : Setoid (List Job) where
  r := List.Perm
  iseqv := ⟨List.Perm.refl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- **tardy-defn**: the object `Bag Job`. -/
@[expose] public abbrev Bag (Job : Type) : RelSet.{0} := ⟨Quotient (permSetoid Job)⟩

-- The note's object language spells a datatype's object lower case and bracketed where the argument
-- is applied (`bag(Job)`); a NOTATION for the reason `thin(` is one: no term prints its own brackets.
notation:max "bag(" J ")" => Bag J

/-- **tardy-defn**: `nil`, the empty bag. -/
@[expose] public def nilBag : (Bag Job).carrier := Quotient.mk (permSetoid Job) []

/-- **tardy-defn**: `snag (u,j)` places the job `j` in the bag `u`. -/
@[expose] public def snag (p : (Bag Job).carrier × Job) : (Bag Job).carrier :=
  Quotient.liftOn p.1 (fun xs => Quotient.mk (permSetoid Job) (p.2 :: xs))
    fun _ _ h => Quotient.sound (h.cons p.2)

/-- **tardy-defn**: the algebra `β≜[nil,snag] : F(Bag Job)⟶Bag Job` as a function. -/
@[expose] public def bagAlgFn : (Fobj Unit Job (Bag Job)).carrier → (Bag Job).carrier
  | Sum.inl _ => nilBag
  | Sum.inr p => snag p

/-- **tardy-defn**: `β≜[nil,snag]`, a map. -/
@[expose] public def bagAlg : (F Unit Job).obj (Bag Job) ⟶ Bag Job := graph bagAlgFn

/-- The jobs of a schedule, as a plain list — a representative of its bag. -/
@[expose] public def blist : SnocList Unit Job → List Job
  | SnocList.wrap _ => []
  | SnocList.snoc x a => a :: blist x

/-- **tardy-defn**: `bagify≜⦇β⦈ : [Job]⟶Bag Job`, read as the function it is. -/
@[expose] public def bagifyFn (s : SnocList Unit Job) : (Bag Job).carrier :=
  Quotient.mk (permSetoid Job) (blist s)

/-- **tardy-defn**, pointwise: the empty schedule has the empty bag. -/
public theorem bagifyFn_wrap (u : Unit) : bagifyFn (SnocList.wrap u : SnocList Unit Job) = nilBag := rfl

/-- **tardy-defn**, pointwise: the last job of a schedule joins the bag of its front. -/
public theorem bagifyFn_snoc (xs : SnocList Unit Job) (a : Job) :
    bagifyFn (SnocList.snoc xs a) = snag (bagifyFn xs, a) := rfl

/-- **tardy-defn**: `bagify` as a morphism; `H = bagify°`. -/
@[expose] public def bagify : dSL Unit Job ⟶ Bag Job := graph bagifyFn

/-- **tardy-defn**: the catamorphism of `β` IS `bagify`. -/
public theorem bagify_cata : cataR (bagAlg (Job := Job)) = bagify := by
  apply hom_ext; intro s
  induction s with
  | wrap _ => exact fun u => Iff.rfl
  | snoc x a ih =>
    intro u
    constructor
    · rintro ⟨u', hu', hstep⟩
      obtain rfl : u' = bagifyFn x := (ih u').mp hu'
      exact hstep
    · intro (h : u = bagAlgFn (Sum.inr (bagifyFn x, a)))
      exact ⟨bagifyFn x, (ih _).mpr rfl, h⟩

/-- Every bag is the bag of some list — bags have representatives, which is how the greedy step
    gets a schedule to delete a job from. -/
public theorem exists_rep (b : (Bag Job).carrier) :
    ∃ xs : List Job, Quotient.mk (permSetoid Job) xs = b :=
  Quotient.inductionOn b fun xs => ⟨xs, rfl⟩

/-- **Proposition 10.1**: `nil` and `snag` have disjoint ranges — a snagged bag is not empty. -/
public theorem nil_ne_snag (u : (Bag Job).carrier) (j : Job) : nilBag ≠ snag (u, j) := by
  refine Quotient.inductionOn u ?_
  intro xs hEq
  have hl := (Quotient.exact hEq : ([] : List Job).Perm (j :: xs)).length_eq
  simp only [List.length_nil, List.length_cons] at hl
  omega

/-! ## Cost (`tardy-defn`)

  `ct`, `dt`, `wt` are the completion, due and weighting quantities of a job; `Real` is `Int`
  here.  `penalty (xs,j)` reads only the COMPLETION TIME of `xs`, so it factors through
  `bagify` — that is `penalty_eq_bagPenalty`, and it is what makes the context hypotheses true
  where the unrestricted ones are false. -/

variable (ct dt wt : Job → Int)

/-- `sum·list ct` on a plain list of jobs. -/
@[expose] public def ctsumL : List Job → Int
  | [] => 0
  | a :: as => ct a + ctsumL as

/-- Reordering jobs does not change their total completion time. -/
public theorem ctsumL_perm {xs ys : List Job} (h : xs.Perm ys) : ctsumL ct xs = ctsumL ct ys := by
  induction h with
  | nil => rfl
  | cons a _ ih => show ct a + _ = ct a + _; rw [ih]
  | swap a b l => show ct b + (ct a + _) = ct a + (ct b + _); omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **tardy-defn**: `sum(list(ct)(xs))`, the completion time of the schedule `xs`. -/
@[expose] public def ctsum (s : SnocList Unit Job) : Int := ctsumL ct (blist s)

/-- The completion time of a BAG: `sum·list ct` factors through `bagify`. -/
@[expose] public def bagCt (u : (Bag Job).carrier) : Int :=
  Quotient.liftOn u (ctsumL ct) fun _ _ h => ctsumL_perm ct h

/-- **tardy-defn**: `(bagify°×𝟙) penalty`, the penalty of putting `j` last after ANY ordering of
    the bag `u`. -/
@[expose] public def bagPenalty (p : (Bag Job).carrier × Job) : Int :=
  (bagCt ct p.1 + ct p.2 - dt p.2) * wt p.2

/-- **tardy-defn**: `penalty(xs,j)=(sum(list(ct)(xs))+ct(j)−dt(j))×wt(j)`. -/
@[expose] public def penalty (xs : SnocList Unit Job) (j : Job) : Int :=
  (ctsum ct xs + ct j - dt j) * wt j

/-- **B&dM p.255**: `penalty (x,j)` depends only on the JOBS in `x`, not on their order — the
    fact the whole context argument rests on. -/
public theorem penalty_eq_bagPenalty (s : SnocList Unit Job) (j : Job) :
    penalty ct dt wt s j = bagPenalty ct dt wt (bagifyFn s, j) := rfl

/-- `bmax`, the binary maximum. -/
@[expose] public def bmax (a b : Int) : Int := if a ≤ b then b else a

public theorem le_bmax_left (a b : Int) : a ≤ bmax a b := by
  show a ≤ if a ≤ b then b else a
  split <;> omega

public theorem le_bmax_right (a b : Int) : b ≤ bmax a b := by
  show b ≤ if a ≤ b then b else a
  split <;> omega

public theorem bmax_le {a b c : Int} (ha : a ≤ c) (hb : b ≤ c) : bmax a b ≤ c := by
  show (if a ≤ b then b else a) ≤ c
  split <;> omega

/-- **tardy-defn**: `cost []=0`, `cost (xs⧺[j])=bmax (cost xs,penalty (xs,j))`. -/
@[expose] public def cost : SnocList Unit Job → Int
  | SnocList.wrap _ => 0
  | SnocList.snoc xs a => bmax (cost xs) (penalty ct dt wt xs a)

/-- **tardy-defn**: `R≜cost≤cost°`. -/
@[expose] public def R : dSL Unit Job ⟶ dSL Unit Job :=
  fun xs ys => cost ct dt wt xs ≤ cost ct dt wt ys

public theorem R_trans : R ct dt wt ≫ R ct dt wt ⊑ R ct dt wt :=
  le_iff.mpr fun u w h => by
    obtain ⟨v, h1, h2⟩ := h
    exact Int.le_trans (h1 : cost ct dt wt u ≤ cost ct dt wt v) h2

/-- **tardy-defn**: `f≜[zero,(bagify°×𝟙) penalty]`. -/
@[expose] public def fFn : ((F Unit Job).obj (Bag Job)).carrier → Int
  | Sum.inl _ => 0
  | Sum.inr p => bagPenalty ct dt wt p

/-- **tardy-defn**: `Q≜f≤f°` — a minimum under `Q` identifies a job of least penalty. -/
@[expose] public def Q : (F Unit Job).obj (Bag Job) ⟶ (F Unit Job).obj (Bag Job) :=
  fun u v => fFn ct dt wt u ≤ fFn ct dt wt v

/-- **tardy-defn**: `Q'≜(bagify°×𝟙) penalty≤penalty°(bagify×𝟙)`, `Q` on the `snag` branch alone —
    what B&dM's Proposition 10.1 step leaves, and what `pick` refines. -/
@[expose] public def Q' : (⟨(Bag Job).carrier × Job⟩ : RelSet.{0}) ⟶ ⟨(Bag Job).carrier × Job⟩ :=
  fun p q => bagPenalty ct dt wt p ≤ bagPenalty ct dt wt q

/-! ## (10.7): the cost of a schedule only increases when jobs are added

  B&dM state this as `add ⊆ R°·outl` and leave it to Exercise 10.7.  Constructively it is a
  DELETION: `del j s` drops the last `j` from the schedule `s`, and the greedy step feeds the
  resulting sub-schedule back through `bagify°`.  Both halves need the book's standing assumption
  that `ct` and `wt` are positive. -/

/-- Drop the last occurrence of the job `j` from a schedule. -/
@[expose] public def del [DecidableEq Job] (j : Job) : SnocList Unit Job → SnocList Unit Job
  | SnocList.wrap d => SnocList.wrap d
  | SnocList.snoc x a => if a = j then x else SnocList.snoc (del j x) a

/-- Deleting one `j` and putting it back is a permutation of the original bag. -/
public theorem blist_del [DecidableEq Job] (j : Job) (s : SnocList Unit Job) :
    j ∈ blist s → (j :: blist (del j s)).Perm (blist s) := by
  induction s with
  | wrap d => intro hm; simp only [blist, List.not_mem_nil] at hm
  | snoc x a ih =>
    intro hm
    simp only [del]
    split
    · next hja => rw [← hja]; exact List.Perm.refl _
    · next hja =>
      have hm' : j ∈ blist x := by
        rcases List.mem_cons.mp hm with h | h
        · exact absurd h.symm hja
        · exact h
      exact (List.Perm.swap a j (blist (del j x))).trans ((ih hm').cons a)

/-- `add (xs,j)=ys⧺[j]⧺zs` for some `xs=ys⧺zs`: `j` put anywhere in the schedule `xs`, stated by
    where it goes — last, or under the last job `a` of `xs`. -/
public inductive AddP : SnocList Unit Job → Job → SnocList Unit Job → Prop
  | last (x : SnocList Unit Job) (j : Job) : AddP x j (SnocList.snoc x j)
  | skip {x w : SnocList Unit Job} {j : Job} (a : Job) :
      AddP x j w → AddP (SnocList.snoc x a) j (SnocList.snoc w a)

/-- **tardy-defn**: `add`, the step of `perm=⦇[nil,add]⦈`. -/
@[expose] public def add : (⟨(dSL Unit Job).carrier × Job⟩ : RelSet.{0}) ⟶ dSL Unit Job :=
  fun p ys => AddP p.1 p.2 ys

/-- Adding `j` puts it in the bag. -/
public theorem blist_add {x w : SnocList Unit Job} {j : Job} :
    AddP x j w → (blist w).Perm (j :: blist x)
  | .last _ _ => List.Perm.refl _
  | .skip a h => ((blist_add h).cons a).trans (List.Perm.swap j a _)

/-- Deleting the last `j` and adding it back where it was gives the schedule again. -/
public theorem add_del [DecidableEq Job] (j : Job) :
    ∀ w : SnocList Unit Job, j ∈ blist w → AddP (del j w) j w
  | .wrap _, hm => absurd hm List.not_mem_nil
  | .snoc x a, hm => by
    simp only [del]
    split
    · next h => subst h; exact .last x a
    · next h =>
      refine .skip a (add_del j x ?_)
      rcases List.mem_cons.mp hm with h' | h'
      · exact absurd h'.symm h
      · exact h'

/-- A job not in the schedule deletes nothing. -/
public theorem del_of_not_mem [DecidableEq Job] (j : Job) :
    ∀ w : SnocList Unit Job, j ∉ blist w → del j w = w
  | .wrap _, _ => rfl
  | .snoc x a, hm => by
    simp only [del]
    split
    · next h => exact absurd (List.mem_cons.mpr (Or.inl h.symm)) hm
    · next h => rw [del_of_not_mem j x fun h' => hm (List.mem_cons.mpr (Or.inr h'))]

/-- Adding a job lengthens the completion time (the jobs' `ct` are positive). -/
public theorem ctsum_add_le (hct : ∀ j, 0 ≤ ct j) {x w : SnocList Unit Job} {j : Job} :
    AddP x j w → ctsum ct x ≤ ctsum ct w
  | .last _ _ => by show ctsum ct _ ≤ ct j + ctsum ct _; have := hct j; omega
  | .skip a h => by
    show ct a + ctsum ct _ ≤ ct a + ctsum ct _; have := ctsum_add_le hct h; omega

/-- Adding a job never lowers the cost of a schedule — every job it passes starts later, so no
    penalty falls, and one penalty is added. -/
public theorem cost_add_le (hct : ∀ j, 0 ≤ ct j) (hwt : ∀ j, 0 ≤ wt j)
    {x w : SnocList Unit Job} {j : Job} : AddP x j w → cost ct dt wt x ≤ cost ct dt wt w
  | .last _ _ => le_bmax_left _ _
  | .skip a h => by
    refine bmax_le (Int.le_trans (cost_add_le hct hwt h) (le_bmax_left _ _))
      (Int.le_trans ?_ (le_bmax_right _ _))
    show (ctsum ct _ + ct a - dt a) * wt a ≤ (ctsum ct _ + ct a - dt a) * wt a
    refine Int.mul_le_mul_of_nonneg_right ?_ (hwt a)
    have := ctsum_add_le ct hct h
    omega

/-- Deleting a job never increases the cost of a schedule: `cost_add_le` read backwards. -/
public theorem cost_del_le [DecidableEq Job] (hct : ∀ j, 0 ≤ ct j) (hwt : ∀ j, 0 ≤ wt j)
    (j : Job) (s : SnocList Unit Job) : cost ct dt wt (del j s) ≤ cost ct dt wt s := by
  by_cases hm : j ∈ blist s
  · exact cost_add_le ct dt wt hct hwt (add_del j s hm)
  · rw [del_of_not_mem j s hm]; exact Int.le_refl _

/-- **(10.7)** (B&dM p.256, Exercise 10.7): `add⊑π₁R` — adding a job to a schedule never lowers
    its cost. -/
public theorem add_le (hct : ∀ j, 0 ≤ ct j) (hwt : ∀ j, 0 ≤ wt j) :
    add (Job := Job) ⊑ (relProd (dSL Unit Job) (⟨Job⟩ : RelSet.{0})).outl ≫ R ct dt wt :=
  le_iff.mpr fun p _ h => ⟨p.1, rfl, cost_add_le ct dt wt hct hwt h⟩

/-- **(10.8)** (B&dM p.256, Exercise 10.8): `β bagify°=F(bagify°)[nil,add]` — `bagify°` is a fold
    on bags. -/
public theorem bagify_recip_cata [DecidableEq Job] :
    bagAlg ≫ (bagify (Job := Job))°
      = (F Unit Job).map (bagify (Job := Job))°
          ≫ junc (sumCop (dL Unit) ⟨(dSL Unit Job).carrier × Job⟩) nilR add := by
  apply hom_ext; intro u w
  rw [comp_apply, comp_apply]
  cases u with
  | inl d =>
    constructor
    · rintro ⟨b, hb, hw⟩
      obtain rfl : b = nilBag := hb
      refine ⟨Sum.inl d, rfl, (ListRel.junc_sum_inl _ _ _ _).mpr ?_⟩
      show w = SnocList.wrap ()
      cases w with
      | wrap _ => rfl
      | snoc x a => exact absurd hw (nil_ne_snag (bagifyFn x) a)
    · rintro ⟨v, hv, hj⟩
      cases v with
      | inr _ => exact hv.elim
      | inl d' =>
        have hw : w = SnocList.wrap () := (ListRel.junc_sum_inl nilR add d' w).mp hj
        subst hw
        exact ⟨nilBag, rfl, rfl⟩
  | inr p =>
    obtain ⟨b, j⟩ := p
    constructor
    · rintro ⟨b', hb', hw⟩
      obtain rfl : b' = snag (b, j) := hb'
      obtain ⟨xs, rfl⟩ := exists_rep b
      have hperm : (blist w).Perm (j :: xs) := Quotient.exact (hw.symm : bagifyFn w = _)
      have hmem : j ∈ blist w := hperm.symm.mem_iff.mp List.mem_cons_self
      refine ⟨Sum.inr (del j w, j), ⟨?_, rfl⟩, (ListRel.junc_sum_inr _ _ _ _).mpr (add_del j w hmem)⟩
      exact Quotient.sound ((blist_del j w hmem).trans hperm).cons_inv.symm
    · rintro ⟨v, hv, hj⟩
      cases v with
      | inl _ => exact hv.elim
      | inr q =>
        obtain ⟨x, j'⟩ := q
        obtain ⟨hb, rfl⟩ := hv
        obtain rfl : b = bagifyFn x := hb
        exact ⟨_, rfl, Quotient.sound (blist_add ((ListRel.junc_sum_inr nilR add _ w).mp hj)).symm⟩

/-! ## `cost` as an arrow, and the calculation of (10.3)'s tail bound (B&dM p.256) -/

/-- **tardy-defn**: `cost : [Job]⟶Int`, the arrow the calculations compose. -/
@[expose] public def costR : dSL Unit Job ⟶ (⟨Int⟩ : RelSet.{0}) := graph (cost ct dt wt)

/-- **tardy-defn**: `penalty : [Job]×Job⟶Int` as an arrow. -/
@[expose] public def penaltyR : (⟨(dSL Unit Job).carrier × Job⟩ : RelSet.{0}) ⟶ ⟨Int⟩ :=
  graph fun p => penalty ct dt wt p.1 p.2

/-- **tardy-defn**: `bmax : Int×Int⟶Int` as an arrow. -/
@[expose] public def bmaxR : (⟨Int × Int⟩ : RelSet.{0}) ⟶ ⟨Int⟩ := graph fun p => bmax p.1 p.2

/-- **(10.5)**: `g≜[zero,penalty]`, the penalty of the last job. -/
@[expose] public def g : (F Unit Job).obj (dSL Unit Job) ⟶ ⟨Int⟩ :=
  junc (sumCop (dL Unit) ⟨(dSL Unit Job).carrier × Job⟩) ListRel.zero (penaltyR ct dt wt)

/-- **(10.6)**: `m≜[zero,π₁ cost]`, the cost of the schedule before the last job (B&dM's `h`). -/
@[expose] public def m : (F Unit Job).obj (dSL Unit Job) ⟶ ⟨Int⟩ :=
  junc (sumCop (dL Unit) ⟨(dSL Unit Job).carrier × Job⟩) ListRel.zero
    ((relProd (dSL Unit Job) (⟨Job⟩ : RelSet.{0})).outl ≫ costR ct dt wt)

/-- **(10.4)** (B&dM p.256, Exercise 10.6): `α cost=⟨g,m⟩ bmax` — the cost of a schedule is the
    larger of its last penalty and the cost of the rest. -/
public theorem cost_alg_bmax :
    graph (con (L := Unit) (E := Job)) ≫ costR ct dt wt
      = (relProd (⟨Int⟩ : RelSet.{0}) (⟨Int⟩ : RelSet.{0})).pair (g ct dt wt) (m ct dt wt)
          ≫ bmaxR := by
  rw [pair_eq_rpair]
  apply hom_ext; intro u c
  rw [comp_apply, comp_apply]
  cases u with
  | inl d =>
    constructor
    · rintro ⟨_, rfl, rfl⟩
      exact ⟨(0, 0), ⟨(ListRel.junc_sum_inl _ _ _ _).mpr rfl, (ListRel.junc_sum_inl _ _ _ _).mpr rfl⟩, rfl⟩
    · rintro ⟨⟨q1, q2⟩, ⟨h1, h2⟩, rfl⟩
      have e1 : q1 = 0 := (ListRel.junc_sum_inl ListRel.zero (penaltyR ct dt wt) d q1).mp h1
      have e2 : q2 = 0 := (ListRel.junc_sum_inl ListRel.zero ((relProd (dSL Unit Job) (⟨Job⟩ : RelSet.{0})).outl ≫ costR ct dt wt) d q2).mp h2
      subst e1; subst e2
      exact ⟨_, rfl, show bmax 0 0 = 0 by unfold bmax; split <;> rfl⟩
  | inr p =>
    constructor
    · rintro ⟨_, rfl, rfl⟩
      refine ⟨(penalty ct dt wt p.1 p.2, cost ct dt wt p.1),
        ⟨(ListRel.junc_sum_inr _ _ _ _).mpr rfl, (ListRel.junc_sum_inr _ _ _ _).mpr ⟨p.1, rfl, rfl⟩⟩, ?_⟩
      show bmax (cost ct dt wt p.1) (penalty ct dt wt p.1 p.2)
        = bmax (penalty ct dt wt p.1 p.2) (cost ct dt wt p.1)
      unfold bmax; split <;> split <;> omega
    · rintro ⟨⟨q1, q2⟩, ⟨h1, h2⟩, rfl⟩
      have e1 : q1 = penalty ct dt wt p.1 p.2 := (ListRel.junc_sum_inr ListRel.zero (penaltyR ct dt wt) p q1).mp h1
      subst e1
      obtain ⟨_, rfl, rfl⟩ := (ListRel.junc_sum_inr ListRel.zero ((relProd (dSL Unit Job) (⟨Job⟩ : RelSet.{0})).outl ≫ costR ct dt wt) p q2).mp h2
      refine ⟨_, rfl, ?_⟩
      show bmax (penalty ct dt wt p.1 p.2) (cost ct dt wt p.1)
        = bmax (cost ct dt wt p.1) (penalty ct dt wt p.1 p.2)
      unfold bmax; split <;> split <;> omega

/-- `[nil,outl R]⊑[zero,outl cost]≤cost°`: the definition of `R`, and `nil⊑zero≤cost°`. -/
public theorem nil_R_le_cost :
    junc (sumCop (dL Unit) ⟨(dSL Unit Job).carrier × Job⟩) nilR
        ((relProd (dSL Unit Job) (⟨Job⟩ : RelSet.{0})).outl ≫ R ct dt wt)
      ⊑ junc (sumCop (dL Unit) ⟨(dSL Unit Job).carrier × Job⟩) ListRel.zero
          ((relProd (dSL Unit Job) (⟨Job⟩ : RelSet.{0})).outl ≫ costR ct dt wt)
        ≫ ListRel.leq ≫ (costR ct dt wt)° :=
  le_iff.mpr fun v w hj => by
    cases v with
    | inl d =>
      have hw : w = SnocList.wrap () := (ListRel.junc_sum_inl nilR _ d w).mp hj
      subst hw
      exact ⟨0, (ListRel.junc_sum_inl _ _ _ _).mpr rfl, 0, Int.le_refl 0, rfl⟩
    | inr q =>
      obtain ⟨_, rfl, hR⟩ := (ListRel.junc_sum_inr _ _ _ _).mp hj
      exact ⟨cost ct dt wt q.1, (ListRel.junc_sum_inr _ _ _ _).mpr ⟨q.1, rfl, rfl⟩,
        cost ct dt wt w, hR, rfl⟩

/-- B&dM p.256, "putting (10.7) and (10.8) together": `β bagify°⊑F(bagify°) m≤cost°` — a schedule
    of a bag costs at least the cost of the rest after its last job.  One `calc` step per hint:
    (10.8), (10.7) under `[nil,−]`, the definition of `R` with `nil⊑zero≤cost°`, the definition of
    `m`. -/
public theorem bagify_recip_le [DecidableEq Job] (hct : ∀ j, 0 ≤ ct j) (hwt : ∀ j, 0 ≤ wt j) :
    bagAlg ≫ (bagify (Job := Job))°
      ⊑ (F Unit Job).map (bagify (Job := Job))° ≫ m ct dt wt ≫ ListRel.leq ≫ (costR ct dt wt)° :=
  calc bagAlg ≫ (bagify (Job := Job))°
      = (F Unit Job).map (bagify (Job := Job))°
        ≫ junc (sumCop (dL Unit) ⟨(dSL Unit Job).carrier × Job⟩) nilR add := bagify_recip_cata
    _ ⊑ (F Unit Job).map (bagify (Job := Job))°
        ≫ junc (sumCop (dL Unit) ⟨(dSL Unit Job).carrier × Job⟩) nilR
            ((relProd (dSL Unit Job) (⟨Job⟩ : RelSet.{0})).outl ≫ R ct dt wt) :=
        comp_mono_left _ (junc_mono _ (le_refl nilR) (add_le ct dt wt hct hwt))
    _ ⊑ (F Unit Job).map (bagify (Job := Job))°
        ≫ junc (sumCop (dL Unit) ⟨(dSL Unit Job).carrier × Job⟩) ListRel.zero
            ((relProd (dSL Unit Job) (⟨Job⟩ : RelSet.{0})).outl ≫ costR ct dt wt)
        ≫ ListRel.leq ≫ (costR ct dt wt)° := comp_mono_left _ (nil_R_le_cost ct dt wt)
    _ = (F Unit Job).map (bagify (Job := Job))° ≫ m ct dt wt ≫ ListRel.leq ≫ (costR ct dt wt)° :=
        rfl

calc_steps bagify_recip_le

/-! ## (10.2) by Proposition 9.3 (B&dM pp.255–256) -/

/-- **tardy-defn**: `assocr (𝟙×((bagify°×𝟙) penalty)) bmax`, `k`'s arm on a front's cost, its bag
    and the last job: a `def` of its own because its pointwise body is no label the note can write. -/
@[expose] public def kStep (p : (Int × (Bag Job).carrier) × Job) : Int :=
  bmax p.1.1 (bagPenalty ct dt wt (p.1.2, p.2))

/-- **tardy-defn**: `k≜[zero,assocr (𝟙×((bagify°×𝟙) penalty)) bmax]`, the step `cost` is a fold of
    once the schedule carries its bag. -/
@[expose] public def kFn : (Fobj Unit Job ⟨Int × (Bag Job).carrier⟩).carrier → Int
  | Sum.inl _ => 0
  | Sum.inr p => kStep ct dt wt p

/-- **tardy-defn**, pointwise: the empty schedule costs nothing. -/
public theorem kFn_inl (u : Unit) :
    kFn ct dt wt (Sum.inl u : (Fobj Unit Job ⟨Int × (Bag Job).carrier⟩).carrier) = 0 := rfl

/-- **tardy-defn**, pointwise: the larger of the front's cost and the last job's penalty on the bag. -/
public theorem kFn_inr (c : Int) (xs : (Bag Job).carrier) (j : Job) :
    kFn ct dt wt (Sum.inr ((c, xs), j) : (Fobj Unit Job ⟨Int × (Bag Job).carrier⟩).carrier)
      = bmax c (bagPenalty ct dt wt (xs, j)) := rfl

/-- **tardy-defn**: `k` as an arrow. -/
@[expose] public def k :
    (F Unit Job).obj (relProd (⟨Int⟩ : RelSet.{0}) (Bag Job)).p ⟶ (⟨Int⟩ : RelSet.{0}) :=
  graph (kFn ct dt wt)

/-- B&dM p.256: `α cost=F(⟨cost,bagify⟩) k` — `cost` restated so that `penalty` reads the bag of
    the schedule, not the schedule (`penalty_eq_bagPenalty`). -/
public theorem cost_alg_k :
    graph (con (L := Unit) (E := Job)) ≫ costR ct dt wt
      = (F Unit Job).map
          ((relProd (⟨Int⟩ : RelSet.{0}) (Bag Job)).pair (costR ct dt wt) bagify) ≫ k ct dt wt := by
  rw [pair_eq_rpair]
  apply hom_ext; intro u c
  rw [comp_apply, comp_apply]
  cases u with
  | inl d =>
    constructor
    · rintro ⟨_, rfl, rfl⟩; exact ⟨Sum.inl d, rfl, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      cases v with
      | inl _ => exact ⟨_, rfl, rfl⟩
      | inr _ => exact hv.elim
  | inr p =>
    constructor
    · rintro ⟨_, rfl, rfl⟩
      exact ⟨Sum.inr ((cost ct dt wt p.1, bagifyFn p.1), p.2), ⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      cases v with
      | inl _ => exact hv.elim
      | inr q =>
        obtain ⟨⟨c, b⟩, j⟩ := q
        obtain ⟨⟨hc, hb⟩, hj⟩ := hv
        obtain rfl : c = cost ct dt wt p.1 := hc
        obtain rfl : b = bagifyFn p.1 := hb
        obtain rfl : p.2 = j := hj
        exact ⟨_, rfl, rfl⟩

/-- B&dM p.256, Exercise 10.5: `F(≥×𝟙)k⊑k≥` — `bmax` is monotone in its first argument. -/
public theorem k_mono :
    (F Unit Job).map (prodMap (relProd (⟨Int⟩ : RelSet.{0}) (Bag Job))
        (relProd (⟨Int⟩ : RelSet.{0}) (Bag Job)) ListRel.geq (𝟙 (Bag Job))) ≫ k ct dt wt
      ⊑ k ct dt wt ≫ ListRel.geq := by
  rw [prodMap_eq_rprodMap]
  refine le_iff.mpr fun u c ⟨v, hv, hc⟩ => ⟨kFn ct dt wt u, rfl, ?_⟩
  obtain rfl : c = kFn ct dt wt v := hc
  cases u with
  | inl _ =>
    cases v with
    | inl _ => exact Int.le_refl 0
    | inr _ => exact hv.elim
  | inr p =>
    cases v with
    | inl _ => exact hv.elim
    | inr q =>
      obtain ⟨⟨c, b⟩, j⟩ := p
      obtain ⟨⟨c', b'⟩, j'⟩ := q
      obtain ⟨⟨hc, hb⟩, hj⟩ := hv
      obtain rfl : b = b' := hb
      obtain rfl : j = j' := hj
      exact bmax_le (Int.le_trans (hc : c' ≤ c) (le_bmax_left _ _)) (le_bmax_right _ _)

/-! ## The two context conditions (B&dM (10.2) and (10.3)) -/

/-- **(10.2)**, the monotonicity condition IN CONTEXT: `α·F(R ∩ bagify°bagify) ⊆ R·α`, by
    Proposition 9.3 at `S=bagify`, `≤=≥`, from `cost_alg_k` and `k_mono`.  Two schedules of the
    same bag have the same completion time, so `snoc`ing the same job gives the same penalty and
    `bmax` is monotone.  Without the context this is FALSE: `cost x ≤ cost y` bounds no
    completion time. -/
public theorem tardy_mono :
    (F Unit Job).map ((R ct dt wt)° ∩ (bagify ≫ (bagify (Job := Job))°))
        ≫ graph (con (L := Unit) (E := Job))
      ⊑ graph (con (L := Unit) (E := Job)) ≫ (R ct dt wt)° := by
  have e : (R ct dt wt)° = costR ct dt wt ≫ ListRel.geq ≫ (costR ct dt wt)° :=
    hom_ext fun u v => ⟨fun h => ⟨_, rfl, _, h, rfl⟩, fun ⟨_, h1, _, h2, h3⟩ => by
      subst h1; subst h3; exact h2⟩
  rw [e]
  exact pres_in_context (cost := costR ct dt wt) (S := bagify) («≤» := ListRel.geq)
    (k := k ct dt wt) (graph_map _) (graph_simple _) (cost_alg_k ct dt wt) (k_mono ct dt wt)

/-! ## The greedy condition (10.3), B&dM p.257 — the book's calculation, one theorem per hint -/

section Greedy

set_option quotPrecheck false
local notation "αJ" => graph (con (L := Unit) (E := Job))
local notation "FbJ" => (F Unit Job).map (bagify (Job := Job))°
local notation "P2" => relProd (⟨Int⟩ : RelSet.{0}) (⟨Int⟩ : RelSet.{0})

/-- `g` read as the function it is. -/
@[expose] public def gFn : (Fobj Unit Job (dSL Unit Job)).carrier → Int
  | Sum.inl _ => 0
  | Sum.inr p => penalty ct dt wt p.1 p.2

public theorem g_apply (s : (Fobj Unit Job (dSL Unit Job)).carrier) (c : Int) :
    g ct dt wt s c ↔ c = gFn ct dt wt s := by
  cases s with
  | inl d => exact ListRel.junc_sum_inl ListRel.zero (penaltyR ct dt wt) d c
  | inr p => exact ListRel.junc_sum_inr ListRel.zero (penaltyR ct dt wt) p c

/-- `g`, pointwise: zero on the empty schedule. -/
public theorem gFn_inl (u : Unit) : gFn ct dt wt (Sum.inl u : (Fobj Unit Job (dSL Unit Job)).carrier) = 0 := rfl

/-- `g`, pointwise: the penalty of the last job after its front. -/
public theorem gFn_inr (xs : SnocList Unit Job) (j : Job) :
    gFn ct dt wt (Sum.inr (xs, j) : (Fobj Unit Job (dSL Unit Job)).carrier) = penalty ct dt wt xs j := rfl

/-- `F(bagify)` read as the function it is. -/
@[expose] public def FbFn : (Fobj Unit Job (dSL Unit Job)).carrier → (Fobj Unit Job (Bag Job)).carrier
  | Sum.inl d => Sum.inl d
  | Sum.inr p => Sum.inr (bagifyFn p.1, p.2)

public theorem Fbag_apply (s : (Fobj Unit Job (dSL Unit Job)).carrier)
    (v : (Fobj Unit Job (Bag Job)).carrier) :
    (F Unit Job).map (bagify (Job := Job)) s v ↔ v = FbFn s := by
  cases s with
  | inl d => cases v with
    | inl d' =>
      show d = d' ↔ Sum.inl d' = Sum.inl d
      exact ⟨fun h => by subst h; rfl, fun h => by cases h; rfl⟩
    | inr _ => exact ⟨False.elim, fun h => nomatch h⟩
  | inr p => cases v with
    | inl _ => exact ⟨False.elim, fun h => nomatch h⟩
    | inr q =>
      obtain ⟨b, j⟩ := q
      show b = bagifyFn p.1 ∧ p.2 = j ↔ Sum.inr (b, j) = Sum.inr (bagifyFn p.1, p.2)
      exact ⟨fun ⟨h1, h2⟩ => by subst h1; subst h2; rfl, fun h => by cases h; exact ⟨rfl, rfl⟩⟩

public theorem Fb_apply (v : (Fobj Unit Job (Bag Job)).carrier)
    (s : (Fobj Unit Job (dSL Unit Job)).carrier) : FbJ v s ↔ v = FbFn s := by
  refine Iff.trans ?_ (Fbag_apply s v)
  cases v with
  | inl _ => cases s with
    | inl _ => exact eq_comm
    | inr _ => exact Iff.rfl
  | inr _ => cases s with
    | inl _ => exact Iff.rfl
    | inr _ => exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩

public theorem fFn_FbFn (s : (Fobj Unit Job (dSL Unit Job)).carrier) :
    fFn ct dt wt (FbFn s) = gFn ct dt wt s := by
  cases s <;> rfl

public theorem bmax_absorb (a b : Int) : bmax b (bmax a b) = bmax a b := by
  unfold bmax
  by_cases h : a ≤ b
  · rw [if_pos h, if_pos (Int.le_refl b)]
  · rw [if_neg h, if_pos (by omega)]

/-- `R = cost≤cost°`, the definition read as an equation of arrows. -/
public theorem R_eq : R ct dt wt = costR ct dt wt ≫ ListRel.leq ≫ (costR ct dt wt)° :=
  hom_ext fun _ _ => ⟨fun h => ⟨_, rfl, _, h, rfl⟩, fun ⟨_, h1, _, h2, h3⟩ => by
    subst h1; subst h3; exact h2⟩

/-- **tardy-defn**, pointwise: `xs R ys` iff `xs` costs no more than `ys`. -/
public theorem R_apply (xs ys : SnocList Unit Job) :
    R ct dt wt xs ys ↔ cost ct dt wt xs ≤ cost ct dt wt ys :=
  Iff.rfl

/-- `β°F(bagify°)α=bagify°`: the step of the fold `bagify=⦇β⦈`, read backwards. -/
public theorem bagify_recip_alg : (bagAlg (Job := Job))° ≫ FbJ ≫ αJ = (bagify (Job := Job))° := by
  apply hom_ext; intro b w
  constructor
  · rintro ⟨u, hu, s, hs, hw⟩
    obtain rfl : b = bagAlgFn u := hu
    obtain rfl : u = FbFn s := (Fb_apply u s).mp hs
    obtain rfl : w = con s := hw
    cases s <;> rfl
  · intro hw
    obtain rfl : b = bagifyFn w := hw
    cases w with
    | wrap d => exact ⟨Sum.inl d, rfl, Sum.inl d, (Fb_apply _ _).mpr rfl, rfl⟩
    | snoc x j => exact ⟨Sum.inr (bagifyFn x, j), rfl, Sum.inr (x, j), (Fb_apply _ _).mpr rfl, rfl⟩

/-- B&dM p.257, the choice of `Q`: `F(bagify) Q F(bagify°)=g≤g°` — under `Q` a job of least
    penalty is chosen. -/
public theorem Q_choice :
    (F Unit Job).map (bagify (Job := Job)) ≫ Q ct dt wt ≫ FbJ
      = g ct dt wt ≫ ListRel.leq ≫ (g ct dt wt)° := by
  apply hom_ext; intro s s'
  constructor
  · rintro ⟨u, hu, v, hQ, hv⟩
    obtain rfl : u = FbFn s := (Fbag_apply s u).mp hu
    obtain rfl : v = FbFn s' := (Fb_apply v s').mp hv
    refine ⟨gFn ct dt wt s, (g_apply ct dt wt s _).mpr rfl, gFn ct dt wt s', ?_,
      (g_apply ct dt wt s' _).mpr rfl⟩
    have hQ' : fFn ct dt wt (FbFn s) ≤ fFn ct dt wt (FbFn s') := hQ
    have e1 := fFn_FbFn ct dt wt s; have e2 := fFn_FbFn ct dt wt s'
    show gFn ct dt wt s ≤ gFn ct dt wt s'
    omega
  · rintro ⟨c, hc, d, hd, hd'⟩
    obtain rfl : c = gFn ct dt wt s := (g_apply ct dt wt s c).mp hc
    obtain rfl : d = gFn ct dt wt s' := (g_apply ct dt wt s' d).mp hd'
    refine ⟨FbFn s, (Fbag_apply s _).mpr rfl, FbFn s', ?_, (Fb_apply _ _).mpr rfl⟩
    have hd' : gFn ct dt wt s ≤ gFn ct dt wt s' := hd
    have e1 := fFn_FbFn ct dt wt s; have e2 := fFn_FbFn ct dt wt s'
    show fFn ct dt wt (FbFn s) ≤ fFn ct dt wt (FbFn s')
    omega

/-- B&dM p.257: `α cost=⟨g,α cost⟩ bmax`, since the last penalty is below the cost. -/
public theorem alg_cost_self :
    αJ ≫ costR ct dt wt = (P2).pair (g ct dt wt) (αJ ≫ costR ct dt wt) ≫ bmaxR := by
  rw [pair_eq_rpair]; apply hom_ext; intro s c
  have key : cost ct dt wt (con s) = bmax (gFn ct dt wt s) (cost ct dt wt (con s)) := by
    cases s with
    | inl _ => show (0 : Int) = bmax 0 0; unfold bmax; rw [if_pos (Int.le_refl 0)]
    | inr p => exact (bmax_absorb _ _).symm
  constructor
  · rintro ⟨_, rfl, rfl⟩
    exact ⟨(gFn ct dt wt s, cost ct dt wt (con s)), ⟨(g_apply ct dt wt s _).mpr rfl, _, rfl, rfl⟩,
      key⟩
  · rintro ⟨⟨q1, q2⟩, ⟨h1, s', hs', hq2⟩, hb⟩
    obtain rfl : q1 = gFn ct dt wt s := (g_apply ct dt wt s q1).mp h1
    obtain rfl : s' = con s := hs'
    obtain rfl : q2 = cost ct dt wt (con s) := hq2
    exact ⟨_, rfl, (hb : c = _).trans key.symm⟩

/-- The modular law, on both sides: `(Q F(bagify°)α)∩(F(bagify°)M)⊑F(bagify°)((F(bagify) Q F(bagify°))∩(Mα°))α`
    — the two schedules share the decomposition `F(bagify°)` picks, so the meet moves inside it. -/
public theorem tardy_modular {M : (F Unit Job).obj (dSL Unit Job) ⟶ dSL Unit Job} :
    (Q ct dt wt ≫ FbJ ≫ αJ) ∩ (FbJ ≫ M)
      ⊑ FbJ ≫ (((F Unit Job).map (bagify (Job := Job)) ≫ Q ct dt wt ≫ FbJ) ∩ (M ≫ αJ°)) ≫ αJ := by
  refine le_iff.mpr fun u w h => ?_
  rw [inter_apply] at h
  obtain ⟨⟨v, hQ, s, hs, hα⟩, ⟨s', hs', hM⟩⟩ := h
  refine ⟨s', hs', s, ?_, hα⟩
  rw [inter_apply]
  exact ⟨⟨u, (Fbag_apply s' u).mpr ((Fb_apply u s').mp hs'), v, hQ, hs⟩, ⟨w, hM, hα⟩⟩

/-- `cost` is a map, so entire: `𝟙⊑cost cost°`. -/
public theorem costR_entire : 𝟙 _ ⊑ costR ct dt wt ≫ (costR ct dt wt)° := (graph_map _).1

/-- `⟨g,α cost⟩` is simple: both components are maps, so a pair they relate one schedule to is
    the only one. -/
public theorem pair_g_alg_cost_simple :
    ((P2).pair (g ct dt wt) (αJ ≫ costR ct dt wt))° ≫ (P2).pair (g ct dt wt) (αJ ≫ costR ct dt wt)
      ⊑ 𝟙 _ := by
  rw [pair_eq_rpair]
  refine le_iff.mpr fun q q' h => ?_
  obtain ⟨s', ⟨h1, x1, hx1, hc1⟩, ⟨h1', x2, hx2, hc2⟩⟩ := h
  obtain rfl : x1 = con s' := hx1
  obtain rfl : x2 = con s' := hx2
  exact (Prod.ext (((g_apply ct dt wt s' _).mp h1).trans ((g_apply ct dt wt s' _).mp h1').symm)
    ((hc1 : q.2 = _).trans (hc2 : q'.2 = _).symm) : q = q')

/-- `bmax` is monotone: `⟨g≤,m≤⟩ bmax⊑⟨g,m⟩ bmax≤`. -/
public theorem pair_leq_bmax_le :
    (P2).pair (g ct dt wt ≫ ListRel.leq) (m ct dt wt ≫ ListRel.leq) ≫ bmaxR
      ⊑ (P2).pair (g ct dt wt) (m ct dt wt) ≫ bmaxR ≫ ListRel.leq := by
  rw [pair_eq_rpair, pair_eq_rpair]
  refine le_iff.mpr fun s c h => ?_
  obtain ⟨⟨q1, q2⟩, ⟨⟨c1, hc1, h1⟩, ⟨c2, hc2, h2⟩⟩, hb⟩ := h
  refine ⟨(c1, c2), ⟨hc1, hc2⟩, bmax c1 c2, rfl, ?_⟩
  obtain rfl : c = bmax q1 q2 := hb
  exact bmax_le (Int.le_trans (h1 : c1 ≤ q1) (le_bmax_left _ _))
    (Int.le_trans (h2 : c2 ≤ q2) (le_bmax_right _ _))

/-- B&dM p.257, the tail of (10.3): `⟨g≤,m≤⟩⟨g,α cost⟩°α⊑αR` — a job whose penalty is at most
    the last job's, put last after a schedule costing at most the rest, costs at most the whole.
    One `calc` step per hint: `cost` a map, `α cost=⟨g,α cost⟩ bmax`, `⟨g,α cost⟩` simple, `bmax`
    monotone, (10.4), the definition of `R`. -/
public theorem tardy_tail :
    (P2).pair (g ct dt wt ≫ ListRel.leq) (m ct dt wt ≫ ListRel.leq)
        ≫ ((P2).pair (g ct dt wt) (αJ ≫ costR ct dt wt))° ≫ αJ
      ⊑ αJ ≫ R ct dt wt :=
  calc (P2).pair (g ct dt wt ≫ ListRel.leq) (m ct dt wt ≫ ListRel.leq)
        ≫ ((P2).pair (g ct dt wt) (αJ ≫ costR ct dt wt))° ≫ αJ
        ⊑ (P2).pair (g ct dt wt ≫ ListRel.leq) (m ct dt wt ≫ ListRel.leq)
        ≫ ((P2).pair (g ct dt wt) (αJ ≫ costR ct dt wt))° ≫ αJ ≫ costR ct dt wt
        ≫ (costR ct dt wt)° := by
        simpa only [Cat.comp_id, Cat.assoc] using
          comp_mono_left ((P2).pair (g ct dt wt ≫ ListRel.leq) (m ct dt wt ≫ ListRel.leq)
            ≫ ((P2).pair (g ct dt wt) (αJ ≫ costR ct dt wt))° ≫ αJ) (costR_entire ct dt wt)
      _ = (P2).pair (g ct dt wt ≫ ListRel.leq) (m ct dt wt ≫ ListRel.leq)
        ≫ ((P2).pair (g ct dt wt) (αJ ≫ costR ct dt wt))°
        ≫ (P2).pair (g ct dt wt) (αJ ≫ costR ct dt wt) ≫ bmaxR ≫ (costR ct dt wt)° := by
        simpa only [Cat.assoc] using congrArg (fun Z => (P2).pair (g ct dt wt ≫ ListRel.leq)
          (m ct dt wt ≫ ListRel.leq) ≫ ((P2).pair (g ct dt wt) (αJ ≫ costR ct dt wt))° ≫ Z
          ≫ (costR ct dt wt)°) (alg_cost_self ct dt wt)
      _ ⊑ (P2).pair (g ct dt wt ≫ ListRel.leq) (m ct dt wt ≫ ListRel.leq) ≫ bmaxR
        ≫ (costR ct dt wt)° := by
        simpa only [Cat.id_comp, Cat.assoc] using
          comp_mono_left _ (comp_mono_right (pair_g_alg_cost_simple ct dt wt) (bmaxR ≫ (costR ct dt wt)°))
      _ ⊑ (P2).pair (g ct dt wt) (m ct dt wt) ≫ bmaxR ≫ ListRel.leq ≫ (costR ct dt wt)° := by
        simpa only [Cat.assoc] using comp_mono_right (pair_leq_bmax_le ct dt wt) (costR ct dt wt)°
      _ = αJ ≫ costR ct dt wt ≫ ListRel.leq ≫ (costR ct dt wt)° := by
        rw [← Cat.assoc ((P2).pair _ _) bmaxR, ← cost_alg_bmax, Cat.assoc]
      _ = αJ ≫ R ct dt wt := by rw [R_eq]

calc_steps tardy_tail

/-- **(10.3)**, the greedy condition IN CONTEXT: `α·Fbagify°·(Q° ∩ β°β) ⊆ R°·α·Fbagify°`, by the
    book's calculation (B&dM p.257), one `calc` step per hint. -/
public theorem tardy_greedy [DecidableEq Job] (hct : ∀ j, 0 ≤ ct j) (hwt : ∀ j, 0 ≤ wt j) :
    (Q ct dt wt ∩ (bagAlg ≫ (bagAlg (Job := Job))°))
        ≫ (F Unit Job).map ((bagify (Job := Job))°) ≫ graph (con (L := Unit) (E := Job))
      ⊑ (F Unit Job).map ((bagify (Job := Job))°) ≫ graph (con (L := Unit) (E := Job))
          ≫ R ct dt wt :=
  calc (Q ct dt wt ∩ (bagAlg ≫ (bagAlg (Job := Job))°)) ≫ FbJ ≫ αJ
      ⊑ (Q ct dt wt ≫ FbJ ≫ αJ) ∩ (bagAlg ≫ (bagAlg (Job := Job))° ≫ FbJ ≫ αJ) := by
        simpa only [Cat.assoc] using
          inter_comp_le (Q ct dt wt) (bagAlg ≫ (bagAlg (Job := Job))°) (FbJ ≫ αJ)
    _ = (Q ct dt wt ≫ FbJ ≫ αJ) ∩ (bagAlg ≫ (bagify (Job := Job))°) := by
        rw [bagify_recip_alg]
    _ ⊑ (Q ct dt wt ≫ FbJ ≫ αJ) ∩ (FbJ ≫ m ct dt wt ≫ ListRel.leq ≫ (costR ct dt wt)°) :=
        inter_mono (le_refl _) (bagify_recip_le ct dt wt hct hwt)
    _ ⊑ FbJ ≫ (((F Unit Job).map (bagify (Job := Job)) ≫ Q ct dt wt ≫ FbJ)
          ∩ (m ct dt wt ≫ ListRel.leq ≫ (costR ct dt wt)° ≫ αJ°)) ≫ αJ :=
        by simpa only [Cat.assoc] using
          tardy_modular ct dt wt (M := m ct dt wt ≫ ListRel.leq ≫ (costR ct dt wt)°)
    _ = FbJ ≫ ((g ct dt wt ≫ ListRel.leq ≫ (g ct dt wt)°)
          ∩ (m ct dt wt ≫ ListRel.leq ≫ (costR ct dt wt)° ≫ αJ°)) ≫ αJ := by
        rw [Q_choice]
    _ = FbJ ≫ ((g ct dt wt ≫ ListRel.leq ≫ (g ct dt wt)°)
          ∩ (m ct dt wt ≫ ListRel.leq ≫ (αJ ≫ costR ct dt wt)°)) ≫ αJ := by
        rw [Allegory.recip_comp]
    _ = FbJ ≫ (P2).pair (g ct dt wt ≫ ListRel.leq) (m ct dt wt ≫ ListRel.leq)
          ≫ ((P2).pair (g ct dt wt) (αJ ≫ costR ct dt wt))° ≫ αJ := by
        simpa only [Cat.assoc] using congrArg (fun Z => FbJ ≫ Z ≫ αJ)
          (RelProd.pair_recip_pair (P := P2) (g ct dt wt ≫ ListRel.leq) (m ct dt wt ≫ ListRel.leq)
            (g ct dt wt) (αJ ≫ costR ct dt wt)).symm
    _ ⊑ FbJ ≫ αJ ≫ R ct dt wt := comp_mono_left _ (tardy_tail ct dt wt)

calc_steps tardy_greedy

end Greedy

/-- `H = ⦇α⦈·⦇β⦈°` collapses to `bagify°` by reflection (`AOP.A6_SnocList.cataR_con`). -/
public theorem tardy_H :
    (relCata (F := F Unit Job) bagAlg)°
        ≫ relCata (F := F Unit Job) (I := initial Unit Job)
            (graph (con (L := Unit) (E := Job)))
      = (bagify (Job := Job))° := by
  rw [← cataR_eq_relCata, ← cataR_eq_relCata, cataR_con, bagify_cata]
  exact Cat.comp_id _

/-- **tardy-laws**, the prefixed point (Theorem 10.1 in context at `Q≜f≤f°`): at
    `X≜Λ(bagify°) est(R)` the greedy body is below `X`, so the least fixed point `tardy_laws` is
    too. -/
public theorem tardy_laws_prefixed [DecidableEq Job] (hct : ∀ j, 0 ≤ ct j) (hwt : ∀ j, 0 ≤ wt j)
    {X : Bag Job ⟶ dSL Unit Job} (hX : X = Λ ((bagify (Job := Job))°) ≫ est (R ct dt wt)) :
    Λ ((bagAlg (Job := Job))°) ≫ est (Q ct dt wt) ≫ (F Unit Job).map X
        ≫ graph (con (L := Unit) (E := Job))
      ⊑ Λ ((bagify (Job := Job))°) ≫ est (R ct dt wt) := by
  subst hX
  have hfix := hylo_fixed (F := F Unit Job) (initial Unit Job)
    (graph (con (L := Unit) (E := Job))) bagAlg
  rw [tardy_H] at hfix
  exact greedy_dp_prefixed_context (graph_map con)
    (by rw [Allegory.recip_recip]; exact tardy_mono ct dt wt) (R_trans ct dt wt) hfix
    (tardy_greedy ct dt wt hct hwt)

/-- **tardy-laws** (B&dM p.257): the schedule of least maximum penalty is the least fixed point
    of `(μX : [nil,snoc](𝟙+(X×𝟙)) est(Q) Λ[nil,snag]°)` — Theorem 10.1 IN CONTEXT at
    `Q≜f≤f°`, one job of the bag committed to the end of the schedule at each step.  `nil` and
    `snag` having disjoint ranges (`nil_ne_snag`, Proposition 10.1) is what lets the `nil` branch
    be read off; refining `est(Q')Λsnag°` further to the partial function `pick` gives the
    quadratic program of B&dM p.258 — `schedule` below. -/
public theorem tardy_laws [DecidableEq Job] (hct : ∀ j, 0 ≤ ct j) (hwt : ∀ j, 0 ≤ wt j) :
    mu (fun X : Bag Job ⟶ dSL Unit Job =>
        Λ ((bagAlg (Job := Job))°) ≫ est (Q ct dt wt) ≫ (F Unit Job).map X
          ≫ graph (con (L := Unit) (E := Job)))
      ⊑ Λ ((bagify (Job := Job))°) ≫ est (R ct dt wt) :=
  mu_le (tardy_laws_prefixed ct dt wt hct hwt rfl)

/-- **Proposition 10.1** in the shape both arm laws ask for: no bag is built by `nil` and by
    `snag` alike, so a branch of `[nil,snag]°` can be read off on its own. -/
private theorem nil_snag_disjoint (d : Unit) (p : (Bag Job).carrier × Job)
    (y : (Bag Job).carrier) (h1 : bagAlg (Job := Job) (Sum.inl d) y)
    (h2 : bagAlg (Job := Job) (Sum.inr p) y) : False :=
  nil_ne_snag p.1 p.2 (Eq.trans (Eq.symm (h1 : y = _)) (h2 : y = _))

/-- **tardy-laws**, third row (Proposition 10.1): `nil` and `snag` have disjoint ranges
    (`nil_ne_snag`), so the branch `(snag°)%∋ est(Q')(X×𝟙)snoc` refines `tardy_laws`' body
    `([nil,snag]°)%∋ est(Q)[nil,(X×𝟙)snoc]` — `AOP.A9_1.est_arm₂_le` at `[nil,snag]`, whose
    `Q₂` at `Q≜f≤f°` is `Q'`. -/
public theorem tardy_branch (X : Bag Job ⟶ dSL Unit Job) :
    Λ ((arm₂ (bagAlg (Job := Job)))°) ≫ est (Q' ct dt wt)
        ≫ rprodMap X (𝟙 (⟨Job⟩ : RelSet.{0})) ≫ arm₂ (graph (con (L := Unit) (E := Job)))
      ⊑ Λ ((bagAlg (Job := Job))°) ≫ est (Q ct dt wt)
          ≫ (F Unit Job).map X ≫ graph (con (L := Unit) (E := Job)) :=
  est_arm₂_le (X := X) (Q := Q ct dt wt) nil_snag_disjoint

/-! ## The program (B&dM p.258): `pick`, and `schedule` as its least fixed point

  The book's last refinement: the search `est(Q')Λsnag°` — take a job of least penalty out of the
  bag — is replaced by ANY partial function `pick` below it, and the program is the least fixed
  point of the equation that leaves.  `pick` is a PARAMETER, not a definition: the book fixes no
  tie-break, so nothing here may assume an order on `Job`. -/

section Pick

variable (pick : Bag Job ⟶ (⟨(Bag Job).carrier × Job⟩ : RelSet.{0}))
  (hpickS : Simple pick)
  (hpick : pick ⊑ Λ ((arm₂ (bagAlg (Job := Job)))°) ≫ est (Q' ct dt wt))

/-- **tardy-laws**, last row: `null`, the guard the base case is taken on — the empty bag. -/
@[expose] public def null : Bag Job ⟶ Bag Job := fun b b' => b = b' ∧ b = nilBag

/-- The other branch's guard, `null`'s complement among the coreflexives: `RelSet` is no
    `BooleanAllegory`, so `corNeg` — hence `cond` — is unavailable and it is written out. -/
@[expose] public def notNull : Bag Job ⟶ Bag Job := fun b b' => b = b' ∧ b ≠ nilBag

/-- A guard only ever shrinks what it precedes. -/
private theorem notNull_comp_le {c : RelSet.{0}} (S : Bag Job ⟶ c) :
    notNull (Job := Job) ≫ S ⊑ S :=
  le_iff.mpr fun x y h => by
    obtain ⟨z, ⟨hxz, _⟩, hS⟩ := h
    subst hxz
    exact hS

/-- The unique map to the one-point object, which carries the base case's `nil` out of a bag. -/
@[expose] public def bangBag : Bag Job ⟶ dL Unit := graph (fun _ : (Bag Job).carrier => ())

/-- **tardy-laws**, last row: `schedule≜(null→nil,pick (schedule×𝟙) snoc)` (B&dM p.258), the least
    fixed point of the greedy step.  `RelSet` is no `BooleanAllegory`, so the conditional's second
    guard is written out where `cond` would take `corNeg null`. -/
@[expose] public def schedule : Bag Job ⟶ dSL Unit Job :=
  mu fun X : Bag Job ⟶ dSL Unit Job =>
    (null ≫ bangBag ≫ nilR)
      ∪ (notNull ≫ pick
          ≫ rprodMap X (𝟙 (⟨Job⟩ : RelSet.{0})) ≫ arm₂ (graph (con (L := Unit) (E := Job))))

private theorem scheduleBody_monotonic :
    Monotonic (fun X : Bag Job ⟶ dSL Unit Job =>
      (null ≫ bangBag ≫ nilR)
        ∪ (notNull ≫ pick
            ≫ rprodMap X (𝟙 (⟨Job⟩ : RelSet.{0})) ≫ arm₂ (graph (con (L := Unit) (E := Job))))) :=
  fun h =>
    union_mono (le_refl _)
      (comp_mono_left _ (comp_mono_left _ (comp_mono_right (rprodMap_mono h (le_refl _)) _)))

/-- **tardy-laws**: the cell's second claim — `schedule` satisfies the note's equation, the least
    fixed point being a fixed point (Theorem 6.1). -/
public theorem schedule_unfold :
    schedule pick
      = (null ≫ bangBag ≫ nilR)
        ∪ (notNull ≫ pick
            ≫ rprodMap (schedule pick) (𝟙 (⟨Job⟩ : RelSet.{0}))
            ≫ arm₂ (graph (con (L := Unit) (E := Job)))) :=
  (mu_fixed (scheduleBody_monotonic pick)).symm

include hpick in
/-- **tardy-laws**, last row: the step the panel draws — `pick` in place of the search
    `est(Q')Λsnag°` refines the branch `tardy_branch` starts from. -/
public theorem pick_branch_le (X : Bag Job ⟶ dSL Unit Job) :
    pick ≫ rprodMap X (𝟙 (⟨Job⟩ : RelSet.{0}))
        ≫ arm₂ (graph (con (L := Unit) (E := Job)))
      ⊑ Λ ((arm₂ (bagAlg (Job := Job)))°) ≫ est (Q' ct dt wt)
          ≫ rprodMap X (𝟙 (⟨Job⟩ : RelSet.{0}))
          ≫ arm₂ (graph (con (L := Unit) (E := Job))) := by
  have h := comp_mono_right hpick
    (rprodMap X (𝟙 (⟨Job⟩ : RelSet.{0})) ≫ arm₂ (graph (con (L := Unit) (E := Job))))
  rw [Cat.assoc] at h
  exact h

include hpickS in
/-- **tardy-laws**, last row: the step is a PARTIAL FUNCTION whenever the continuation is — that
    is what makes B&dM's p.258 program a program and not a search: `pick` is single-valued and
    `snoc` is a map, so nothing in the step branches. -/
public theorem pick_branch_simple {X : Bag Job ⟶ dSL Unit Job} (hX : Simple X) :
    Simple (pick ≫ rprodMap X (𝟙 (⟨Job⟩ : RelSet.{0}))
      ≫ arm₂ (graph (con (L := Unit) (E := Job)))) := by
  rw [Simple, le_iff]
  intro s s' h
  obtain ⟨b, ⟨p, hp, q, ⟨hq1, hq2⟩, hs⟩, ⟨p', hp', q', ⟨hq1', hq2'⟩, hs'⟩⟩ := h
  have hpp : p = p' := simple_uniq hpickS hp hp'
  subst hpp
  have hq : q = q' := Prod.ext (simple_uniq hX hq1 hq1') (hq2.symm.trans hq2')
  subst hq
  exact hs.trans hs'.symm

/-- The base case: on the empty bag the search `est(Q)Λ[nil,snag]°` leaves `nil` itself, so the
    guarded constant `null≫nil` is below the `nil` arm of the specification's body. -/
private theorem null_nil_le :
    null ≫ bangBag ≫ nilR
      ⊑ Λ ((arm₁ (bagAlg (Job := Job)))°) ≫ est (armQ₁ (Q ct dt wt))
          ≫ arm₁ (graph (con (L := Unit) (E := Job))) := by
  have haux : null ≫ bangBag ⊑ Λ ((arm₁ (bagAlg (Job := Job)))°) ≫ est (armQ₁ (Q ct dt wt)) :=
    le_iff.mpr fun b u h => by
      obtain ⟨_b', ⟨_, hb0⟩, _⟩ := h
      exact (Λ_comp_est_apply _ _ b u).mpr ⟨hb0, fun _z _ => Int.le_refl _⟩
  have h := comp_mono_right haux (nilR (E := Job))
  rw [Cat.assoc, Cat.assoc] at h
  exact h

include hpick in
/-- **tardy-laws**: the cell's first claim — the program refines the specification.  Both branches
    of the step are below `tardy_laws`' body: the base case by `est_arm₁_le`, the greedy step by
    `pick_branch_le` and then `tardy_branch`. -/
public theorem schedule_le [DecidableEq Job] (hct : ∀ j, 0 ≤ ct j) (hwt : ∀ j, 0 ≤ wt j) :
    schedule pick ⊑ Λ ((bagify (Job := Job))°) ≫ est (R ct dt wt) :=
  le_trans
    (mu_le_mu fun X =>
      union_le
        (le_trans (null_nil_le ct dt wt) (est_arm₁_le (X := X) nil_snag_disjoint))
        (le_trans (notNull_comp_le _)
          (le_trans (pick_branch_le ct dt wt pick hpick X) (tardy_branch ct dt wt X))))
    (tardy_laws ct dt wt hct hwt)

end Pick

/-! ## The datatype as a relator: `bag(R)`

  A bag is a datatype in its ELEMENT type, so `bag` is a lane and `bag(Job)` that lane over the
  `Job` wire — where the object alone leaves the picture a point nothing peels.  Two bags are
  related when they have REPRESENTATIVES related element by element: the list lifting, made blind
  to the order by the choice of representative rather than by a side condition. -/

/-- Elementwise lifting on lists — the relation `bag(R)` is read through. -/
@[expose] public def elemsP {A B : Type} (R : dE A ⟶ dE B) : List A → List B → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | a :: xs, b :: ys => R a b ∧ elemsP R xs ys

public theorem elemsP_id {A : Type} :
    ∀ xs ys : List A, elemsP (𝟙 (dE A)) xs ys ↔ xs = ys
  | [], [] => ⟨fun _ => rfl, fun _ => trivial⟩
  | [], _ :: _ => ⟨False.elim, fun h => nomatch h⟩
  | _ :: _, [] => ⟨False.elim, fun h => nomatch h⟩
  | a :: xs, b :: ys =>
      ⟨fun h => by rw [show a = b from h.1, (elemsP_id xs ys).mp h.2],
       fun h => by cases h; exact ⟨rfl, (elemsP_id xs xs).mpr rfl⟩⟩

public theorem elemsP_comp {A B C : Type} (R : dE A ⟶ dE B) (S : dE B ⟶ dE C) :
    ∀ (xs : List A) (zs : List C), elemsP (R ≫ S) xs zs ↔ ∃ ys, elemsP R xs ys ∧ elemsP S ys zs
  | [], [] => ⟨fun _ => ⟨[], trivial, trivial⟩, fun _ => trivial⟩
  | [], _ :: _ =>
      ⟨False.elim, fun ⟨ys, h1, h2⟩ => by cases ys with
        | nil => exact h2
        | cons _ _ => exact h1⟩
  | _ :: _, [] =>
      ⟨False.elim, fun ⟨ys, h1, h2⟩ => by cases ys with
        | nil => exact h1
        | cons _ _ => exact h2⟩
  | a :: xs, c :: zs => by
      constructor
      · rintro ⟨⟨b, hR, hS⟩, hxz⟩
        obtain ⟨ys, hy1, hy2⟩ := (elemsP_comp R S xs zs).mp hxz
        exact ⟨b :: ys, ⟨hR, hy1⟩, hS, hy2⟩
      · rintro ⟨ys, h1, h2⟩
        cases ys with
        | nil => exact h1.elim
        | cons b ys =>
            exact ⟨⟨b, h1.1, h2.1⟩, (elemsP_comp R S xs zs).mpr ⟨ys, h1.2, h2.2⟩⟩

public theorem elemsP_mono {A B : Type} {R S : dE A ⟶ dE B} (h : ∀ a b, R a b → S a b) :
    ∀ xs ys, elemsP R xs ys → elemsP S xs ys
  | [], [], hxy => hxy
  | [], _ :: _, hxy => hxy.elim
  | _ :: _, [], hxy => hxy.elim
  | a :: xs, b :: ys, hxy => ⟨h a b hxy.1, elemsP_mono h xs ys hxy.2⟩

/-- A PERMUTATION OF THE SOURCE CARRIES THE LIFTING WITH IT: re-ordering one list re-orders its
    partner the same way.  This is what makes `bag(R)` independent of the representatives, and it
    is proved by recursion on the permutation itself — no choice, no decidable equality. -/
public theorem elemsP_perm {A B : Type} (R : dE A ⟶ dE B) :
    ∀ {xs xs' : List A}, List.Perm xs xs' → ∀ {zs : List B}, elemsP R xs' zs →
      ∃ zs', elemsP R xs zs' ∧ List.Perm zs' zs := by
  intro xs xs' hp
  induction hp with
  | nil =>
      intro zs hz
      cases zs with
      | nil => exact ⟨[], trivial, List.Perm.nil⟩
      | cons _ _ => exact hz.elim
  | @cons x l₁ l₂ _ ih =>
      intro zs hz
      cases zs with
      | nil => exact hz.elim
      | cons c zt =>
          obtain ⟨zt', h1, h2⟩ := ih hz.2
          exact ⟨c :: zt', ⟨hz.1, h1⟩, h2.cons c⟩
  | @swap x y l =>
      intro zs hz
      cases zs with
      | nil => exact hz.elim
      | cons c zs =>
          cases zs with
          | nil => exact hz.2.elim
          | cons d zt => exact ⟨d :: c :: zt, ⟨hz.2.1, hz.1, hz.2.2⟩, List.Perm.swap c d zt⟩
  | @trans l₁ l₂ l₃ _ _ ih₁ ih₂ =>
      intro zs hz
      obtain ⟨ws, hw1, hw2⟩ := ih₂ hz
      obtain ⟨vs, hv1, hv2⟩ := ih₁ hw1
      exact ⟨vs, hv1, hv2.trans hw2⟩

/-- **tardy-defn**: `bag(R)` relates two bags that have representatives related element by element. -/
@[expose] public def bagP {A B : Type} (R : dE A ⟶ dE B)
    (u : (Bag A).carrier) (v : (Bag B).carrier) : Prop :=
  ∃ xs ys, Quotient.mk (permSetoid A) xs = u ∧ Quotient.mk (permSetoid B) ys = v ∧ elemsP R xs ys

/-- The relator's action `bag(R) : bag(A)⟶bag(B)`. -/
@[expose] public def bagRel {A B : Type} (R : dE A ⟶ dE B) : Bag A ⟶ Bag B := bagP R

/-- `bag(𝟙) = 𝟙`. -/
public theorem bag_id {A : Type} : bagRel (𝟙 (dE A)) = 𝟙 (Bag A) := by
  apply hom_ext
  intro u v
  constructor
  · rintro ⟨xs, ys, rfl, rfl, h⟩
    exact congrArg (Quotient.mk (permSetoid A)) ((elemsP_id xs ys).mp h)
  · intro (h : u = v)
    cases h
    induction u using Quotient.ind with
    | _ xs => exact ⟨xs, xs, rfl, rfl, (elemsP_id xs xs).mpr rfl⟩

/-- `bag(RS) = bag(R) bag(S)` — the middle bag is the image of ONE representative, and a second
    representative of it is reached by `elemsP_perm`. -/
public theorem bag_comp {A B C : Type} (R : dE A ⟶ dE B) (S : dE B ⟶ dE C) :
    bagRel (R ≫ S) = bagRel R ≫ bagRel S := by
  apply hom_ext
  intro u w
  constructor
  · rintro ⟨xs, zs, rfl, rfl, h⟩
    obtain ⟨ys, h1, h2⟩ := (elemsP_comp R S xs zs).mp h
    exact ⟨Quotient.mk (permSetoid B) ys, ⟨xs, ys, rfl, rfl, h1⟩, ⟨ys, zs, rfl, rfl, h2⟩⟩
  · rintro ⟨v, ⟨xs, ys, rfl, hv, h1⟩, ⟨ys', zs, hv', rfl, h2⟩⟩
    obtain ⟨zs', h3, h4⟩ := elemsP_perm S (Quotient.exact (hv.trans hv'.symm)) h2
    exact ⟨xs, zs', rfl, Quotient.sound h4, (elemsP_comp R S xs zs').mpr ⟨ys, h1, h3⟩⟩

/-- `R ⊑ S ⟹ bag(R) ⊑ bag(S)` — `bag` is monotonic. -/
public theorem bag_mono {A B : Type} {R S : dE A ⟶ dE B} (h : R ⊑ S) : bagRel R ⊑ bagRel S :=
  le_iff.mpr fun _ _ ⟨xs, ys, hu, hv, hxy⟩ =>
    ⟨xs, ys, hu, hv, elemsP_mono (le_iff.mp h) xs ys hxy⟩

/-- `bag` BUNDLED as a relator, the lane the tardy-jobs pictures draw over the `Job` wire. -/
@[expose] public def bag : Relator RelSet.{0} RelSet.{0} where
  obj a := Bag a.carrier
  map R := bagRel R
  map_id _ := bag_id
  map_comp R S := bag_comp R S
  map_mono h := bag_mono h

/-- Adding one job to a bag SPLITS `bag(R)`: the added jobs are related and the rest are related.
    The matching a `bagP` hands over is on some representative; `elemsP_perm` re-orders it onto
    `j :: ps`, which is where the split can be read off. -/
public theorem bagP_snag {A B : Type} (R : dE A ⟶ dE B) (u : (Bag A).carrier) (j : A)
    (w : (Bag B).carrier) :
    bagP R (snag (u, j)) w ↔ ∃ v k, bagP R u v ∧ R j k ∧ snag (v, k) = w := by
  obtain ⟨ps, rfl⟩ := exists_rep u
  constructor
  · rintro ⟨xs, ys, hxs, rfl, hel⟩
    obtain ⟨ys', hel', hp⟩ := elemsP_perm R (Quotient.exact hxs.symm) hel
    cases ys' with
    | nil => exact hel'.elim
    | cons k vs =>
      exact ⟨Quotient.mk (permSetoid B) vs, k, ⟨ps, vs, rfl, rfl, hel'.2⟩, hel'.1,
        Quotient.sound hp⟩
  · rintro ⟨v, k, ⟨ps', vs, hps, hvs, hel⟩, hjk, rfl⟩
    obtain ⟨vs', hel', hp⟩ := elemsP_perm R (Quotient.exact hps.symm) hel
    subst hvs
    exact ⟨j :: ps, k :: vs', rfl, Quotient.sound (hp.cons k), hjk, hel'⟩

/-- **`snag` IS STRICTLY NATURAL**: `bag(R)×R` then `snag` is `snag` then `bag(R)` — the square
    `bagP_snag` states, with the two composites spelled out. -/
public theorem snag_strictNatural :
    StrictNatural bag (Relator.prod bag (Relator.idRelator RelSet.{0}))
      (fun A => arm₂ (bagAlg (Job := A.carrier))) := by
  intro A B R
  rw [show (Relator.prod bag (Relator.idRelator RelSet.{0})).map R
      = rprodMap (bagRel R) R from prodMap_eq_rprodMap _ _]
  apply hom_ext
  intro p z
  constructor
  · rintro ⟨q, ⟨hb, hR⟩, rfl⟩
    exact ⟨snag p, rfl, (bagP_snag R p.1 p.2 _).mpr ⟨q.1, q.2, hb, hR, rfl⟩⟩
  · rintro ⟨y, rfl, hb⟩
    obtain ⟨v, k, hb', hR, rfl⟩ := (bagP_snag R p.1 p.2 z).mp hb
    exact ⟨(v, k), ⟨hb', hR⟩, rfl⟩

/-- `snag°`, the bead the tardy pictures carry: `Rel(Set)` is tabular, so the square turns round. -/
public theorem snag_recip_strictNatural :
    StrictNatural (Relator.prod bag (Relator.idRelator RelSet.{0})) bag
      (fun A => (arm₂ (bagAlg (Job := A.carrier)))°) :=
  strictNatural_recip (Relator.preservesRecip_of_tabular _)
    (Relator.preservesRecip_of_tabular _) snag_strictNatural

/-- `bag(R)` relates the empty bag to the empty bag and to nothing else: a representative of `nil`
    is a permutation of `[]`, hence `[]`, and `[]` lifts only to `[]`. -/
public theorem bagP_nil {A B : Type} (R : dE A ⟶ dE B) (w : (Bag B).carrier) :
    bagP R nilBag w ↔ w = nilBag := by
  constructor
  · rintro ⟨xs, ys, h1, rfl, hel⟩
    obtain ⟨zs', hel', hp⟩ := elemsP_perm R (Quotient.exact h1).symm hel
    cases zs' with
    | nil => exact Quotient.sound hp.symm
    | cons _ _ => exact hel'.elim
  · rintro rfl
    exact ⟨[], [], rfl, rfl, trivial⟩

/-- **`[nil,snag]` IS STRICTLY NATURAL** — the whole algebra, not only its `snag` arm: the source is
    the coproduct `𝟏 + bag(Job)×Job` read summand by summand, the leaf arm the constant lane at `𝟏`
    and the pair arm `snag_strictNatural`'s. -/
public theorem bagAlg_strictNatural :
    StrictNatural bag
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod bag (Relator.idRelator RelSet.{0})))
      (fun A => bagAlg (Job := A.carrier)) := by
  intro A B R
  rw [show (Relator.sum (Relator.const (dL Unit))
        (Relator.prod bag (Relator.idRelator RelSet.{0}))).map R
      = sumMap (sumCop (dL Unit) ⟨(Bag A.carrier).carrier × A.carrier⟩)
          (sumCop (dL Unit) ⟨(Bag B.carrier).carrier × B.carrier⟩)
          (𝟙 (dL Unit)) (rprodMap (bagRel R) R) from prodMap_eq_rprodMap _ _ ▸ rfl]
  apply hom_ext
  intro u z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨bagAlgFn u, rfl, ?_⟩
    cases hw with
    | inl h =>
      obtain ⟨d, rfl, d', _, rfl⟩ := h
      exact (bagP_nil R nilBag).mpr rfl
    | inr h =>
      obtain ⟨p, rfl, q, hq, rfl⟩ := h
      exact (bagP_snag R p.1 p.2 _).mpr ⟨q.1, q.2, hq.1, hq.2, rfl⟩
  · rintro ⟨x, rfl, hb⟩
    cases u with
    | inl d =>
      obtain rfl := (bagP_nil R z).mp hb
      exact ⟨Sum.inl d, Or.inl ⟨d, rfl, d, rfl, rfl⟩, rfl⟩
    | inr p =>
      obtain ⟨v, k, hb', hR, rfl⟩ := (bagP_snag R p.1 p.2 z).mp hb
      exact ⟨Sum.inr (v, k), Or.inr ⟨p, rfl, (v, k), ⟨hb', hR⟩, rfl⟩, rfl⟩

/-- `[nil,snag]°`, the bead the tardy picture carries: `Rel(Set)` is tabular, so both lanes preserve
    `°` and the square turns round. -/
public theorem bagAlg_recip_strictNatural :
    StrictNatural
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod bag (Relator.idRelator RelSet.{0})))
      bag
      (fun A => (bagAlg (Job := A.carrier))°) :=
  strictNatural_recip (F := bag)
    (G := Relator.sum (Relator.const (dL Unit))
      (Relator.prod bag (Relator.idRelator RelSet.{0})))
    (Relator.preservesRecip_of_tabular _) (Relator.preservesRecip_of_tabular _)
    bagAlg_strictNatural

/-- The elementwise lifting on a schedule IS the elementwise lifting on its list of jobs. -/
public theorem elemsP_blist {A B : Type} (R : dE A ⟶ dE B) :
    ∀ {s : SnocList Unit A} {t : SnocList Unit B}, slistP R s t → elemsP R (blist s) (blist t)
  | SnocList.wrap _, SnocList.wrap _, _ => trivial
  | SnocList.wrap _, SnocList.snoc _ _, h => h.elim
  | SnocList.snoc _ _, SnocList.wrap _, h => h.elim
  | SnocList.snoc _ _, SnocList.snoc _ _, h => ⟨h.2, elemsP_blist R h.1⟩

/-- A list related elementwise to a schedule's jobs IS a schedule's jobs, at the same shape — the
    converse of `elemsP_blist`, which is what makes `bagify`'s square an equality and not an
    inclusion. -/
public theorem blist_elemsP {A B : Type} (R : dE A ⟶ dE B) :
    ∀ (s : SnocList Unit A) {zs : List B}, elemsP R (blist s) zs →
      ∃ t : SnocList Unit B, slistP R s t ∧ blist t = zs
  | SnocList.wrap u, [], _ => ⟨SnocList.wrap u, rfl, rfl⟩
  | SnocList.wrap _, _ :: _, h => h.elim
  | SnocList.snoc _ _, [], h => h.elim
  | SnocList.snoc x _, _ :: _, h => by
      obtain ⟨t, ht, hb⟩ := blist_elemsP R x h.2
      exact ⟨SnocList.snoc t _, ⟨ht, h.1⟩, congrArg _ hb⟩

/-- `bag(R)` out of a schedule's bag is `list(R)` out of the schedule, the order forgotten after. -/
public theorem bagP_bagify {A B : Type} (R : dE A ⟶ dE B) (s : SnocList Unit A)
    (w : (Bag B).carrier) :
    bagP R (bagifyFn s) w ↔ ∃ t : SnocList Unit B, slistP R s t ∧ bagifyFn t = w := by
  constructor
  · rintro ⟨xs, ys, hxs, rfl, hel⟩
    obtain ⟨ys', hel', hp⟩ := elemsP_perm R (Quotient.exact hxs.symm) hel
    obtain ⟨t, ht, hb⟩ := blist_elemsP R s hel'
    exact ⟨t, ht, Quotient.sound (hb ▸ hp)⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨blist s, blist t, rfl, rfl, elemsP_blist R ht⟩

/-- **`bagify` IS STRICTLY NATURAL**: relating job by job then forgetting the order is forgetting
    it then `bag(R)` — a re-ordering of the jobs carries the matching with it. -/
public theorem bagify_strictNatural :
    StrictNatural bag (snocRelator Unit) (fun A => bagify (Job := A.carrier)) := by
  intro A B R
  apply hom_ext
  intro s w
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨bagifyFn s, rfl, (bagP_bagify R s _).mpr ⟨t, ht, rfl⟩⟩
  · rintro ⟨y, rfl, hb⟩
    obtain ⟨t, ht, rfl⟩ := (bagP_bagify R s w).mp hb
    exact ⟨t, ht, rfl⟩

/-- `H = bagify°`, the bead the tardy pictures carry: `Rel(Set)` is tabular, so the square turns
    round and `H` is strictly natural too. -/
public theorem bagify_recip_strictNatural :
    StrictNatural (snocRelator Unit) bag (fun A => (bagify (Job := A.carrier))°) :=
  strictNatural_recip (F := bag) (G := snocRelator Unit)
    (φ := fun A => bagify (Job := A.carrier))
    (Relator.preservesRecip_of_tabular _) (Relator.preservesRecip_of_tabular _)
    bagify_strictNatural

/-- **`π₁` IS LAX NATURAL** from `F×G` to `F`: relating both components then dropping the second
    is at most dropping it then relating the first — the second component may have no partner. -/
public theorem outl_laxNatural (F G : Relator RelSet.{0} RelSet.{0}) :
    LaxNatural F (Relator.prod F G) (fun A => (relProd (F.obj A) (G.obj A)).outl) := by
  intro A B S
  rw [show (Relator.prod F G).map S = rprodMap (F.map S) (G.map S) from prodMap_eq_rprodMap _ _]
  exact le_iff.mpr fun p _ ⟨q, ⟨h1, _⟩, hq⟩ => ⟨p.1, rfl, by cases hq; exact h1⟩

/-- **`add` IS STRICTLY NATURAL**: relating job by job then inserting `j` is inserting `j` then
    relating job by job — the insertion point is carried across, one `skip` per job it passes. -/
public theorem add_strictNatural :
    StrictNatural (snocRelator Unit) (Relator.prod (snocRelator Unit) (Relator.idRelator RelSet.{0}))
      (fun A => add (Job := A.carrier)) := by
  intro A B S
  rw [show (Relator.prod (snocRelator Unit) (Relator.idRelator RelSet.{0})).map S
      = rprodMap (slist S) S from prodMap_eq_rprodMap _ _]
  apply hom_ext
  intro p w'
  have fwd : ∀ {x' w' : SnocList Unit B.carrier} {j' : B.carrier}, AddP x' j' w' →
      ∀ (x : SnocList Unit A.carrier) (j : A.carrier), slist S x x' → S j j' →
      ∃ w, AddP x j w ∧ slist S w w' := by
    intro x' w' j' h
    induction h with
    | last x' j' => exact fun x j hx hj => ⟨_, .last x j, hx, hj⟩
    | skip a' _ ih =>
      intro x j hx hj
      cases x with
      | wrap _ => exact hx.elim
      | snoc x0 a0 =>
        obtain ⟨w0, hw0, hs⟩ := ih x0 j hx.1 hj
        exact ⟨_, .skip a0 hw0, hs, hx.2⟩
  have bwd : ∀ {x w : SnocList Unit A.carrier} {j : A.carrier}, AddP x j w →
      ∀ w' : SnocList Unit B.carrier, slist S w w' →
      ∃ x' j', (slist S x x' ∧ S j j') ∧ AddP x' j' w' := by
    intro x w j h
    induction h with
    | last x j =>
      intro w' hw
      cases w' with
      | wrap _ => exact hw.elim
      | snoc y b => exact ⟨y, b, ⟨hw.1, hw.2⟩, .last y b⟩
    | skip a _ ih =>
      intro w' hw
      cases w' with
      | wrap _ => exact hw.elim
      | snoc y b =>
        obtain ⟨x0', j', ⟨hx, hj⟩, hy⟩ := ih y hw.1
        exact ⟨SnocList.snoc x0' b, j', ⟨⟨hx, hw.2⟩, hj⟩, .skip b hy⟩
  constructor
  · rintro ⟨q, ⟨h1, h2⟩, hq⟩
    exact fwd hq p.1 p.2 h1 h2
  · rintro ⟨w, hw, hs⟩
    obtain ⟨x', j', hxj, hq⟩ := bwd hw w' hs
    exact ⟨(x', j'), hxj, hq⟩

/-- **`nil` IS LAX NATURAL** in the element type: `list(S)` relates `[]` to `[]`. -/
public theorem nilR_laxNatural :
    LaxNatural (snocRelator Unit) (Relator.const (dL Unit)) (fun a => nilR (E := a.carrier)) := by
  intro x y S
  refine le_iff.mpr fun d ys h => ?_
  obtain ⟨d', _, hys⟩ := h
  obtain rfl : ys = SnocList.wrap () := hys
  exact ⟨SnocList.wrap (), rfl, rfl⟩

/-- **`[nil,(bagify°×𝟙)add]` IS LAX NATURAL**, the step of (10.8)'s fold: `nil`'s square beside
    `bagify°×𝟙` then `add`, both strictly natural. -/
public theorem bagAdd_laxNatural :
    LaxNatural (snocRelator Unit)
      (Relator.sum (Relator.const (dL Unit)) (Relator.prod bag (Relator.idRelator RelSet.{0})))
      (fun a => junc (sumCop (dL Unit) ⟨(Bag a.carrier).carrier × a.carrier⟩) nilR
        (prodMap (relProd (Bag a.carrier) a) (relProd (dSL Unit a.carrier) a)
          (bagify (Job := a.carrier))° (𝟙 a) ≫ add)) := by
  intro A B R
  refine laxNatural_junc (F' := Relator.prod bag (Relator.idRelator RelSet.{0}))
    (ψ := fun a => prodMap (relProd (Bag a.carrier) a) (relProd (dSL Unit a.carrier) a)
      (bagify (Job := a.carrier))° (𝟙 a) ≫ add) nilR_laxNatural ?_ R
  intro A B R
  show _ ≫ (_ ≫ add) ⊑ (_ ≫ add) ≫ _
  refine laxNatural_comp_slide (F := snocRelator Unit)
    (G := Relator.prod (snocRelator Unit) (Relator.idRelator RelSet.{0}))
    (H := Relator.prod bag (Relator.idRelator RelSet.{0}))
    (ψ := fun a => prodMap (relProd (Bag a.carrier) a) (relProd (dSL Unit a.carrier) a)
      (bagify (Job := a.carrier))° (𝟙 a)) (φ := fun a => add (Job := a.carrier)) ?_ ?_
  · exact le_of_eq (strictNatural_prod (F' := Relator.idRelator RelSet.{0}) bagify_recip_strictNatural
      (strictNatural_id _) R)
  · exact le_of_eq (add_strictNatural R)

-- printing-only unexpanders: §10.3's arrows under the book's names, the job data `ct`, `dt`, `wt`
-- dropped.
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Tardy.cost] public meta def unexpandTardyCost : Unexpander
  | `($_ $_ $_ $_ $x $args*) => `($(mkIdent `cost) $x $args*)
  | _ => `($(mkIdent `cost))

open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Tardy.penalty] public meta def unexpandTardyPenalty : Unexpander
  | `($_ $_ $_ $_ $x $args*) => `($(mkIdent `penalty) $x $args*)
  | _ => `($(mkIdent `penalty))

open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Tardy.fFn] public meta def unexpandTardyF : Unexpander
  | `($_ $_ $_ $_ $x $args*) => `($(mkIdent `f) $x $args*)
  | _ => `($(mkIdent `f))

open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Tardy.gFn] public meta def unexpandTardyG : Unexpander
  | `($_ $_ $_ $_ $x $args*) => `($(mkIdent `g) $x $args*)
  | _ => `($(mkIdent `g))

open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Tardy.ctsum] public meta def unexpandCtsum : Unexpander
  | `($_ $_ $x $args*) => `($(mkIdent (Name.mkSimple "sum(list(ct))")) $x $args*)
  | _ => `($(mkIdent (Name.mkSimple "sum(list(ct))")))

open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Tardy.bagifyFn] public meta def unexpandBagifyFn : Unexpander
  | `($_ $args*) => `($(mkIdent `bagify) $args*)
  | _ => `($(mkIdent `bagify))

open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Tardy.bmax] public meta def unexpandBmax : Unexpander
  | `($_ $args*) => `($(mkIdent `bmax) $args*)
  | _ => `($(mkIdent `bmax))

open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Tardy.kFn] public meta def unexpandTardyK : Unexpander
  | `($_ $_ $_ $_ $x $args*) => `($(mkIdent `k) $x $args*)
  | _ => `($(mkIdent `k))

open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Tardy.nilBag] public meta def unexpandNilBag : Unexpander
  | _ => `($(mkIdent `nil))

open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Tardy.snag] public meta def unexpandSnag : Unexpander
  | `($_ $args*) => `($(mkIdent `snag) $args*)
  | _ => `($(mkIdent `snag))

end Freyd.Alg.RelSet.Tardy
