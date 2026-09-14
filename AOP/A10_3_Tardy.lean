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
public theorem greedy_dp_prefixed_context (hFr : F.PreservesRecip) {h : F.obj A ⟶ A}
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
        rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, ← hFr H, Cat.assoc]
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
        rw [Allegory.recip_comp, Allegory.recip_comp, ← hFr H, Cat.assoc]
      have eR : (F.map H ≫ h ≫ R)° = R° ≫ h° ≫ F.map (H°) := by
        rw [Allegory.recip_comp, Allegory.recip_comp, ← hFr H, Cat.assoc]
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
public theorem greedy_dp_context (hFr : F.PreservesRecip) (I : InitialAlgebra F)
    {h : F.obj A ⟶ A} {T : F.obj B ⟶ B} {R : A ⟶ A} {Q : F.obj B ⟶ F.obj B} (hh : Map h)
    (hctx1 : F.map (R° ∩ (((relCata T)° ≫ relCata h)° ≫ (relCata T)° ≫ relCata h)) ≫ h
        ⊑ h ≫ R°)
    (htrans : R ≫ R ⊑ R)
    (hctx2 : (Q ∩ (T ≫ T°)) ≫ F.map ((relCata T)° ≫ relCata h) ≫ h
        ⊑ F.map ((relCata T)° ≫ relCata h) ≫ h ≫ R) :
    mu (fun X : B ⟶ A => Λ (T°) ≫ est Q ≫ F.map X ≫ h)
      ⊑ Λ ((relCata T)° ≫ relCata h) ≫ est R :=
  LocallyCompleteDistributiveAllegory.Sup_le (fun _S hS => hS _
    (greedy_dp_prefixed_context hFr hh hctx1 htrans (hylo_fixed hFr I h T) hctx2))

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
@[expose] public def penalty (s : SnocList Unit Job) (j : Job) : Int :=
  (ctsum ct s + ct j - dt j) * wt j

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
  | SnocList.snoc x a => bmax (cost x) (penalty ct dt wt x a)

/-- **tardy-defn**: `R≜cost≤cost°`. -/
@[expose] public def R : dSL Unit Job ⟶ dSL Unit Job :=
  fun u v => cost ct dt wt u ≤ cost ct dt wt v

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

/-- Deleting a job shortens the completion time (the jobs' `ct` are positive). -/
public theorem ctsum_del_le [DecidableEq Job] (hct : ∀ j, 0 ≤ ct j) (j : Job)
    (s : SnocList Unit Job) : ctsum ct (del j s) ≤ ctsum ct s := by
  induction s with
  | wrap d => exact Int.le_refl _
  | snoc x a ih =>
    show ctsum ct (if a = j then x else SnocList.snoc (del j x) a) ≤ ct a + ctsum ct x
    split
    · have := hct a; omega
    · show ct a + ctsum ct (del j x) ≤ ct a + ctsum ct x
      omega

/-- **(10.7)**: deleting a job never increases the cost of a schedule — every remaining job keeps
    its place and starts no later, so no penalty rises, and one penalty disappears. -/
public theorem cost_del_le [DecidableEq Job] (hct : ∀ j, 0 ≤ ct j) (hwt : ∀ j, 0 ≤ wt j)
    (j : Job) (s : SnocList Unit Job) : cost ct dt wt (del j s) ≤ cost ct dt wt s := by
  induction s with
  | wrap d => exact Int.le_refl _
  | snoc x a ih =>
    show cost ct dt wt (if a = j then x else SnocList.snoc (del j x) a)
      ≤ bmax (cost ct dt wt x) (penalty ct dt wt x a)
    split
    · exact le_bmax_left _ _
    · refine bmax_le (Int.le_trans ih (le_bmax_left _ _)) (Int.le_trans ?_ (le_bmax_right _ _))
      show (ctsum ct (del j x) + ct a - dt a) * wt a ≤ (ctsum ct x + ct a - dt a) * wt a
      refine Int.mul_le_mul_of_nonneg_right ?_ (hwt a)
      have := ctsum_del_le ct hct j x
      omega

/-! ## The two context conditions (B&dM (10.2) and (10.3)) -/

/-- **(10.2)**, the monotonicity condition IN CONTEXT: `α·F(R ∩ bagify°bagify) ⊆ R·α`.  Two
    schedules of the same bag have the same completion time, so `snoc`ing the same job gives the
    same penalty and `bmax` is monotone.  Without the context this is FALSE: `cost x ≤ cost y`
    bounds no completion time. -/
public theorem tardy_mono :
    (F Unit Job).map ((R ct dt wt)° ∩ (bagify ≫ (bagify (Job := Job))°))
        ≫ graph (con (L := Unit) (E := Job))
      ⊑ graph (con (L := Unit) (E := Job)) ≫ (R ct dt wt)° :=
  le_iff.mpr fun u out h => by
    obtain ⟨v, hFv, hout⟩ := h
    obtain rfl : out = con v := hout
    refine ⟨con u, rfl, ?_⟩
    cases u with
    | inl du =>
      cases v with
      | inl dv => exact Int.le_refl 0
      | inr q => exact hFv.elim
    | inr p =>
      cases v with
      | inl dv => exact hFv.elim
      | inr q =>
        obtain ⟨⟨hR, hbag⟩, hij⟩ := hFv
        obtain ⟨b, hb1, hb2⟩ := hbag
        have hbq : bagifyFn p.1 = bagifyFn q.1 := hb1 ▸ hb2
        show bmax (cost ct dt wt q.1) (penalty ct dt wt q.1 q.2)
          ≤ bmax (cost ct dt wt p.1) (penalty ct dt wt p.1 p.2)
        have hpen : penalty ct dt wt q.1 q.2 = penalty ct dt wt p.1 p.2 := by
          rw [penalty_eq_bagPenalty, penalty_eq_bagPenalty, hbq, hij]
        refine bmax_le (Int.le_trans (hR : cost ct dt wt q.1 ≤ cost ct dt wt p.1)
          (le_bmax_left _ _)) ?_
        rw [hpen]
        exact le_bmax_right _ _

/-- **(10.3)**, the greedy condition IN CONTEXT: `α·Fbagify°·(Q° ∩ β°β) ⊆ R°·α·Fbagify°`.  Given a
    schedule `y⧺[jv]` of the bag `snag (bv,jv)` and a job `ju` of no greater penalty in the same
    bag, delete the last `ju` from `y⧺[jv]`: the result orders the bag `bu` (`blist_del`), costs
    no more (`cost_del_le`, (10.7)), and putting `ju` last adds a penalty bounded by `Q`. -/
public theorem tardy_greedy [DecidableEq Job] (hct : ∀ j, 0 ≤ ct j) (hwt : ∀ j, 0 ≤ wt j) :
    (Q ct dt wt ∩ (bagAlg ≫ (bagAlg (Job := Job))°))
        ≫ (F Unit Job).map ((bagify (Job := Job))°) ≫ graph (con (L := Unit) (E := Job))
      ⊑ (F Unit Job).map ((bagify (Job := Job))°) ≫ graph (con (L := Unit) (E := Job))
          ≫ R ct dt wt :=
  le_iff.mpr fun u out h => by
    obtain ⟨v, hQv, w, hFw, hout⟩ := h
    obtain rfl : out = con w := hout
    obtain ⟨hQ, hbag⟩ := hQv
    obtain ⟨b, hb1, hb2⟩ := hbag
    have hbeta : bagAlgFn u = bagAlgFn v := hb1 ▸ hb2
    cases u with
    | inl du =>
      cases v with
      | inl dv =>
        cases w with
        | inl dw => exact ⟨Sum.inl (), rfl, SnocList.wrap (), rfl, Int.le_refl 0⟩
        | inr r => exact hFw.elim
      | inr q => exact absurd hbeta (nil_ne_snag q.1 q.2)
    | inr p =>
      obtain ⟨bu, ju⟩ := p
      cases v with
      | inl dv => exact absurd hbeta.symm (nil_ne_snag bu ju)
      | inr q =>
        obtain ⟨bv, jv⟩ := q
        cases w with
        | inl dw => exact hFw.elim
        | inr r =>
          obtain ⟨y, jy⟩ := r
          obtain ⟨hHy, hjw⟩ := hFw
          have hq1 : bv = bagifyFn y := hHy
          have hq2 : jv = jy := hjw
          obtain ⟨xs, hxs⟩ := exists_rep bu
          have hsnag : snag (Quotient.mk (permSetoid Job) xs, ju)
              = snag (bagifyFn y, jy) := by
            rw [hxs, ← hq1, ← hq2]; exact hbeta
          have hperm : (ju :: xs).Perm (blist (SnocList.snoc y jy)) := Quotient.exact hsnag
          have hmem : ju ∈ blist (SnocList.snoc y jy) := hperm.mem_iff.mp List.mem_cons_self
          have hdel := blist_del ju (SnocList.snoc y jy) hmem
          have hx : (blist (del ju (SnocList.snoc y jy))).Perm xs :=
            (hdel.trans hperm.symm).cons_inv
          have hbagx : bagifyFn (del ju (SnocList.snoc y jy)) = bu := by
            rw [← hxs]; exact Quotient.sound hx
          refine ⟨Sum.inr (del ju (SnocList.snoc y jy), ju), ⟨hbagx.symm, rfl⟩,
            SnocList.snoc (del ju (SnocList.snoc y jy)) ju, rfl, ?_⟩
          show bmax (cost ct dt wt (del ju (SnocList.snoc y jy)))
              (penalty ct dt wt (del ju (SnocList.snoc y jy)) ju)
            ≤ cost ct dt wt (SnocList.snoc y jy)
          refine bmax_le (cost_del_le ct dt wt hct hwt ju _) ?_
          -- the `Q` step: the chosen job's penalty is bounded by the one it replaces
          have hpx : penalty ct dt wt (del ju (SnocList.snoc y jy)) ju
              = bagPenalty ct dt wt (bu, ju) := by
            rw [penalty_eq_bagPenalty, hbagx]
          have hpy : bagPenalty ct dt wt (bv, jv) = penalty ct dt wt y jy := by
            rw [penalty_eq_bagPenalty, ← hq1, ← hq2]
          rw [hpx]
          refine Int.le_trans hQ ?_
          show bagPenalty ct dt wt (bv, jv) ≤ cost ct dt wt (SnocList.snoc y jy)
          rw [hpy]
          show penalty ct dt wt y jy ≤ bmax (cost ct dt wt y) (penalty ct dt wt y jy)
          exact le_bmax_right _ _

/-- `H = ⦇α⦈·⦇β⦈°` collapses to `bagify°` by reflection (`AOP.A6_SnocList.cataR_con`). -/
public theorem tardy_H :
    (relCata (F := F Unit Job) bagAlg)°
        ≫ relCata (F := F Unit Job) (I := initial Unit Job)
            (graph (con (L := Unit) (E := Job)))
      = (bagify (Job := Job))° := by
  rw [← cataR_eq_relCata, ← cataR_eq_relCata, cataR_con, bagify_cata]
  exact Cat.comp_id _

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
      ⊑ Λ ((bagify (Job := Job))°) ≫ est (R ct dt wt) := by
  have key := greedy_dp_context (F := F Unit Job) (F_preservesRecip Unit Job)
    (initial Unit Job) (h := graph (con (L := Unit) (E := Job))) (T := bagAlg)
    (R := R ct dt wt) (Q := Q ct dt wt) (graph_map con)
    (by rw [tardy_H, Allegory.recip_recip]; exact tardy_mono ct dt wt)
    (R_trans ct dt wt)
    (by rw [tardy_H]; exact tardy_greedy ct dt wt hct hwt)
  rwa [tardy_H] at key

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

/-- `∪` is the least upper bound: the allegory axioms give `le_union_left`/`le_union_right` but no
    lub, and in `RelSet` it is pointwise `∨`. -/
private theorem union_le {a b : RelSet.{0}} {S T U : a ⟶ b} (hS : S ⊑ U) (hT : T ⊑ U) :
    S ∪ T ⊑ U :=
  le_iff.mpr fun x y h => ((union_apply S T x y) ▸ h).elim (le_iff.mp hS x y) (le_iff.mp hT x y)

private theorem union_mono {a b : RelSet.{0}} {S S' T T' : a ⟶ b} (hS : S ⊑ S') (hT : T ⊑ T') :
    S ∪ T ⊑ S' ∪ T' :=
  union_le (le_trans hS (le_union_left _ _)) (le_trans hT (le_union_right _ _))

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
public theorem pick_branch_le (schedule : Bag Job ⟶ dSL Unit Job) :
    pick ≫ rprodMap schedule (𝟙 (⟨Job⟩ : RelSet.{0}))
        ≫ arm₂ (graph (con (L := Unit) (E := Job)))
      ⊑ Λ ((arm₂ (bagAlg (Job := Job)))°) ≫ est (Q' ct dt wt)
          ≫ rprodMap schedule (𝟙 (⟨Job⟩ : RelSet.{0}))
          ≫ arm₂ (graph (con (L := Unit) (E := Job))) := by
  have h := comp_mono_right hpick
    (rprodMap schedule (𝟙 (⟨Job⟩ : RelSet.{0})) ≫ arm₂ (graph (con (L := Unit) (E := Job))))
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
@[expose] public def bagRelator : Relator RelSet.{0} RelSet.{0} where
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
    StrictNatural bagRelator (Relator.prod bagRelator (Relator.idRelator RelSet.{0}))
      (fun A => arm₂ (bagAlg (Job := A.carrier))) := by
  intro A B R
  rw [show (Relator.prod bagRelator (Relator.idRelator RelSet.{0})).map R
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
    StrictNatural (Relator.prod bagRelator (Relator.idRelator RelSet.{0})) bagRelator
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
    StrictNatural bagRelator
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod bagRelator (Relator.idRelator RelSet.{0})))
      (fun A => bagAlg (Job := A.carrier)) := by
  intro A B R
  rw [show (Relator.sum (Relator.const (dL Unit))
        (Relator.prod bagRelator (Relator.idRelator RelSet.{0}))).map R
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
        (Relator.prod bagRelator (Relator.idRelator RelSet.{0})))
      bagRelator
      (fun A => (bagAlg (Job := A.carrier))°) :=
  strictNatural_recip (F := bagRelator)
    (G := Relator.sum (Relator.const (dL Unit))
      (Relator.prod bagRelator (Relator.idRelator RelSet.{0})))
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
    StrictNatural bagRelator (snocRelator Unit) (fun A => bagify (Job := A.carrier)) := by
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
    StrictNatural (snocRelator Unit) bagRelator (fun A => (bagify (Job := A.carrier))°) :=
  strictNatural_recip (F := bagRelator) (G := snocRelator Unit)
    (φ := fun A => bagify (Job := A.carrier))
    (Relator.preservesRecip_of_tabular _) (Relator.preservesRecip_of_tabular _)
    bagify_strictNatural

end Freyd.Alg.RelSet.Tardy
