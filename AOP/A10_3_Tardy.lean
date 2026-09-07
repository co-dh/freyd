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

universe u

namespace Freyd.Alg

variable {𝒜 : Type u} [UnguardedPowerLCDA 𝒜] {F : Relator 𝒜 𝒜} {A B : 𝒜}

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
    quadratic program of B&dM p.258, which is not formalised here. -/
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

end Freyd.Alg.RelSet.Tardy
