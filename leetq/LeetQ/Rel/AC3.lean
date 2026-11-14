import LeetQ.Rel.Rep

/-! # AC-3 (arc consistency, Mackworth's algorithm 3): the delta-round kernel of `νX : s ∩ ⋂ₖ Aₖ\(X Cₖ)` and its agreement with the naive rounds -/

namespace LeetQ.Rel.Alg

open LeetQ.Rel

/-- One arc `A\(X C)` of an AC-3 body (`A : V ⟶ V`, `C : D ⟶ D`), with `𝟙(D)` for its division. -/
structure Revise (V D : Obj) where
  A : Rel V V
  C : Rel D D
  UV : Rel V V
  UD : Rel D D

/-- The AC-3 body `s ∩ ⋂ₖ Aₖ\(X Cₖ)`, one naive round: `fixOn` on it is `νX` the naive way. -/
def acRound {V D : Obj} (s : Rel V D) (as : List (Revise V D)) (X : Rel V D) : Rel V D :=
  as.foldl (fun Y a => Y ∩ leftDiv a.A (X ≫ a.C) a.UV.key a.UD.key) s

/-- One delta round of the AC-3 body, from `(X, Δ)`, `Δ ⊑ 𝟙(V)` the variables whose domain shrank last round:
    `X′ = X ∩ ⋂ₖ (Δ Aₖ)\(X Cₖ)` and `Δ′ = dom(X − X′)`. `(Δ A)\…` is `⊤` at every `x ∉ ran(Δ A)`, so each
    division runs only on the rows `ran(Δ A)` (its universe there, so no vacuous row is made) and keeps `X`'s
    other rows; `X − X′` is the anti-join of the pairs. The tie to the naive round is `AC3.acDelta_round`: from
    a state satisfying `AcInv`, one delta round denotes one `acRound`, and `Δ′` keeps `AcInv`; `k` rounds of each
    agree by `AC3.acDelta_iterate`. -/
def acDelta {V D : Obj} (as : List (Revise V D)) (p : Rel V D × Rel V V) : Rel V D × Rel V V :=
  let (X, Δ) := p
  let X' := as.foldl (fun Y a =>
    let R := Δ ≫ a.A; let T := ran R
    (antiJoin Y° T)° ∪ (Y ∩ leftDiv R (Δ ≫ X ≫ a.C) T.key a.UD.key)) X
  (X', ran (outl (antiJoin (idU (X.key, X.val)) (idU (X'.key, X'.val)))))

/-- `νX : s ∩ ⋂ₖ Aₖ\(X Cₖ)` by delta rounds from `(s, 𝟙(V))` — the first the naive round — until `Δ′ = 𝟘`,
    at most `|s| + 1`, with the rounds run. -/
def acFix {V D : Obj} (s : Rel V D) (as : List (Revise V D)) (U : Rel V V) : Rel V D × Nat :=
  let x := s.nub
  let r := iter (x.n.toNat + 1) (fun (_, Δ, _) => Δ.n == 0)
    (fun (X, Δ, k) => let (X', Δ') := acDelta as (X, Δ); (X', Δ', k + 1)) (x, U, 0)
  (r.1, r.2.2)

end LeetQ.Rel.Alg

/-!
  The delta AC-3 round (`Alg.acDelta`) read in `Rel(Set)` against the naive round (`Alg.acRound`): from a state
  satisfying the invariant `AcInv`, one delta round denotes what one naive round does, and its `Δ′` re-establishes
  the invariant.

  Each op of a round is assumed to denote its `Rel(Set)` op at the arguments the round meets (`StepMeets`): that is
  the conclusion `rep_inter`, `rep_leftDiv`, `rep_comp`, `rep_union`, `rep_antiJoin`, `rep_conv` give under their
  own code and fit hypotheses, which this module does not restate.
-/

namespace LeetQ.Rel.AC3


open LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep

variable {V D : Obj}

/-! ## The fold of a round, read pointwise -/

/-- Every step of `as.foldl step s` denotes the relation before it met with `M a`: what the ops of the step give
    at the arguments that step meets (`pre` the arcs already folded). -/
def StepMeets {γ : Type} (step : Rel V D → γ → Rel V D) (s : Rel V D) (as : List γ)
    (M : γ → V.El → D.El → Prop) : Prop :=
  ∀ pre a suf, as = pre ++ a :: suf → ∀ x d,
    rep (step (pre.foldl step s) a) x d ↔ rep (pre.foldl step s) x d ∧ M a x d

/-- **`rep (as.foldl step s) = rep s ∩ ⋂ₐ M a`**, by induction on the arcs. -/
theorem rep_foldl {γ : Type} (step : Rel V D → γ → Rel V D) (M : γ → V.El → D.El → Prop) :
    ∀ (as : List γ) (s : Rel V D), StepMeets step s as M →
      ∀ x d, rep (as.foldl step s) x d ↔ rep s x d ∧ ∀ a ∈ as, M a x d
  | [], s, _, x, d => by simp
  | a :: t, s, h, x, d => by
    have ih := rep_foldl step M t (step s a) (fun pre b suf e => h (a :: pre) b suf (by rw [e]; rfl)) x d
    have h0 := h [] a t rfl x d; rw [List.foldl_nil] at h0
    rw [List.foldl_cons, ih, h0, List.forall_mem_cons, and_assoc]

/-! ## The two rounds, pointwise -/

/-- The vacuous part of `A\(X C)` at `(x, d)`: `x` has an `A`-predecessor, or `x`, `d` are in the universes. -/
def Vac (a : Revise V D) (x : V.El) (d : D.El) : Prop :=
  (∃ w, rep a.A w x) ∨ ((∃ p, a.UV.key.row p = x) ∧ ∃ j, a.UD.key.row j = d)

/-- `A\(X C)` at `(x, d)`, as `rep_leftDiv` reads it with `rep_comp` for `X C`. -/
def Nv (a : Revise V D) (X : V.El → D.El → Prop) (x : V.El) (d : D.El) : Prop :=
  (∀ w, rep a.A w x → ∃ e, X w e ∧ rep a.C e d) ∧ Vac a x d

/-- One delta arc at `(x, d)`, as the laws read `(antiJoin Y° T)° ∪ (Y ∩ (Δ A)\(Δ X C))` after the `Y` they share:
    `x ∉ ran(Δ A)`, or the division by `Δ A` with `rep_comp` for `Δ A` and `Δ X C`, its vacuous part on `T`. -/
def Ld (a : Revise V D) (X : V.El → D.El → Prop) (Δ : V.El → V.El → Prop) (T : Rel V V) (x : V.El) (d : D.El) :
    Prop :=
  (¬ ∃ w v, Δ w v ∧ rep a.A v x) ∨
    ((∀ w, (∃ v, Δ w v ∧ rep a.A v x) → ∃ v e, Δ w v ∧ X v e ∧ rep a.C e d) ∧
      ((∃ w v, Δ w v ∧ rep a.A v x) ∨ ((∃ p, T.key.row p = x) ∧ ∃ j, a.UD.key.row j = d)))

/-- The delta arc after the simplification: `A\(X C)` checked only at the predecessors `w` in `Δ`. -/
def Dl (a : Revise V D) (X : V.El → D.El → Prop) (Δ : V.El → V.El → Prop) (x : V.El) (d : D.El) : Prop :=
  ∀ w, Δ w w → rep a.A w x → ∃ e, X w e ∧ rep a.C e d

/-- **`Ld = Dl` for a coreflexive `Δ`**: the vacuous part of `(Δ A)\…` matters only off `ran(Δ A)`, where the
    anti-join side already holds; on `Δ`, `Δ w v` is `w = v`. -/
theorem ld_iff (a : Revise V D) (X : V.El → D.El → Prop) {Δ : V.El → V.El → Prop} (hΔ : ∀ w v, Δ w v → w = v)
    (T : Rel V V) (x : V.El) (d : D.El) : Ld a X Δ T x d ↔ Dl a X Δ x d := by
  classical
  calc Ld a X Δ T x d
      ↔ ∀ w, (∃ v, Δ w v ∧ rep a.A v x) → ∃ v e, Δ w v ∧ X v e ∧ rep a.C e d := by
        -- excluded middle on `x ∈ ran(Δ A)`: off it both sides hold vacuously, on it the vacuous part is true
        by_cases hr : ∃ w v, Δ w v ∧ rep a.A v x
        · simp only [Ld, hr, not_true_eq_false, true_or, and_true, false_or]
        · simp only [Ld, hr, not_false_eq_true, true_or, true_iff]
          exact fun w hw => (hr ⟨w, hw⟩).elim
    _ ↔ Dl a X Δ x d := by
        -- `Δ` coreflexive: `Δ w v ↔ v = w ∧ Δ w w`
        constructor
        · intro h w hw hA
          obtain ⟨v, e, hv, hX, hC⟩ := h w ⟨w, hw, hA⟩
          exact ⟨e, hΔ w v hv ▸ hX, hC⟩
        · intro h w ⟨v, hv, hA⟩
          have e := hΔ w v hv; subst e
          obtain ⟨e, hX, hC⟩ := h w hv hA
          exact ⟨w, e, hv, hX, hC⟩

/-- The naive round's arc step, as `acRound` folds it. -/
abbrev naiveStep (X : Rel V D) : Rel V D → Revise V D → Rel V D :=
  fun Y a => Y ∩ leftDiv a.A (X ≫ a.C) a.UV.key a.UD.key

/-- The delta round's arc step, as `acDelta` folds it. -/
abbrev deltaStep (X : Rel V D) (Δ : Rel V V) : Rel V D → Revise V D → Rel V D :=
  fun Y a => (antiJoin Y° (Alg.ran (Δ ≫ a.A)))° ∪ (Y ∩ leftDiv (Δ ≫ a.A) (Δ ≫ X ≫ a.C) (Alg.ran (Δ ≫ a.A)).key a.UD.key)

/-- **`rep (acRound s as X) = rep s ∩ ⋂ₐ Aₐ\(X Cₐ)`**. -/
theorem rep_acRound (s : Rel V D) (as : List (Revise V D)) (X : Rel V D)
    (h : StepMeets (naiveStep X) s as fun a => Nv a (rep X)) (x : V.El) (d : D.El) :
    rep (acRound s as X) x d ↔ rep s x d ∧ ∀ a ∈ as, Nv a (rep X) x d :=
  rep_foldl _ _ as s h x d

/-- **`rep (acDelta as (X, Δ)).1 = rep X ∩ ⋂ₐ (Δ Aₐ)\(X Cₐ)`**, `Δ` coreflexive (`ld_iff`). -/
theorem rep_acDelta (as : List (Revise V D)) (X : Rel V D) (Δ : Rel V V) (hΔ : ∀ w v, rep Δ w v → w = v)
    (h : StepMeets (deltaStep X Δ) X as fun a => Ld a (rep X) (rep Δ) (Alg.ran (Δ ≫ a.A))) (x : V.El) (d : D.El) :
    rep (acDelta as (X, Δ)).1 x d ↔ rep X x d ∧ ∀ a ∈ as, Dl a (rep X) (rep Δ) x d := by
  rw [show (acDelta as (X, Δ)).1 = as.foldl (deltaStep X Δ) X from rfl, rep_foldl _ _ as X h x d]
  exact and_congr Iff.rfl (forall₂_congr fun a _ => ld_iff a _ hΔ _ x d)

/-! ## The invariant and one round -/

/-- The state `(X, Δ)` of the delta rounds for the body `s ∩ ⋂ₐ Aₐ\(X Cₐ)`: `Δ` coreflexive; `X ⊑ s`; `X` inside
    every arc's vacuous part; `X ⊒` the naive round on `X`; and every pair of `X` supported, at each predecessor
    outside `Δ`, as the naive round asks — so only the predecessors in `Δ` need checking. -/
def AcInv (s : Rel V D) (as : List (Revise V D)) (X : V.El → D.El → Prop) (Δ : V.El → V.El → Prop) : Prop :=
  (∀ w v, Δ w v → w = v) ∧ (∀ x d, X x d → rep s x d) ∧ (∀ a ∈ as, ∀ x d, X x d → Vac a x d) ∧
    (∀ x d, rep s x d → (∀ a ∈ as, Nv a X x d) → X x d) ∧
    ∀ a ∈ as, ∀ x d, X x d → ∀ w, ¬ Δ w w → rep a.A w x → ∃ e, X w e ∧ rep a.C e d

/-- **One delta round is one naive round, and keeps the invariant**: from `AcInv s as (rep X) (rep Δ)`,
    `rep (acDelta as (X, Δ)).1 = rep (acRound s as X)`, and `AcInv` holds of the new `X′` with the new `Δ′`.
    Hypotheses: each op of either round denotes its `Rel(Set)` op where the round meets it (`hN`, `hD`), and
    `Δ′ = ran(outl(antiJoin(𝟙_X, 𝟙_X′)))` the variables with a pair of `X` not in `X′` (`hΔ'`: `rep_ran_corefl`,
    `rep_outl`, `rep_antiJoin`, `rep_idU` at those arguments). -/
theorem acDelta_round (s : Rel V D) (as : List (Revise V D)) (X : Rel V D) (Δ : Rel V V)
    (hI : AcInv s as (rep X) (rep Δ))
    (hN : StepMeets (naiveStep X) s as fun a => Nv a (rep X))
    (hD : StepMeets (deltaStep X Δ) X as fun a => Ld a (rep X) (rep Δ) (Alg.ran (Δ ≫ a.A)))
    (hΔ' : ∀ w v, rep (acDelta as (X, Δ)).2 w v ↔ w = v ∧ ∃ e, rep X w e ∧ ¬ rep (acDelta as (X, Δ)).1 w e) :
    rep (acDelta as (X, Δ)).1 = rep (acRound s as X) ∧
      AcInv s as (rep (acDelta as (X, Δ)).1) (rep (acDelta as (X, Δ)).2) := by
  classical
  obtain ⟨hΔ, hXs, hXv, hXn, hXo⟩ := hI
  have hd := rep_acDelta as X Δ hΔ hD
  have hn := rep_acRound s as X hN
  -- the two rounds agree pointwise
  have key : ∀ x d, rep (acDelta as (X, Δ)).1 x d ↔ rep (acRound s as X) x d := fun x d => by
    rw [hd, hn]
    constructor
    · rintro ⟨hX, hDl⟩
      refine ⟨hXs x d hX, fun a ha => ⟨fun w hA => ?_, hXv a ha x d hX⟩⟩
      by_cases hw : rep Δ w w
      · exact hDl a ha w hw hA
      · exact hXo a ha x d hX w hw hA
    · rintro ⟨hs, hNv⟩
      exact ⟨hXn x d hs hNv, fun a ha w _ hA => (hNv a ha).1 w hA⟩
  have hle : ∀ x d, rep (acDelta as (X, Δ)).1 x d → rep X x d := fun x d h => ((hd x d).1 h).1
  refine ⟨Freyd.Alg.RelSet.hom_ext key, fun w v h => ((hΔ' w v).1 h).1, fun x d h => hXs x d (hle x d h),
    fun a ha x d h => hXv a ha x d (hle x d h), fun x d hs hNv => ?_, fun a ha x d h w hw hA => ?_⟩
  · -- `Nv` is monotone in `X`, and `X′ ⊑ X`
    refine (key x d).2 ((hn x d).2 ⟨hs, fun a ha => ⟨fun w hA => ?_, (hNv a ha).2⟩⟩)
    obtain ⟨e, hX, hC⟩ := (hNv a ha).1 w hA
    exact ⟨e, hle w e hX, hC⟩
  · -- off `Δ′` the pairs of `X` at `w` are pairs of `X′`
    obtain ⟨e, hX, hC⟩ := (((hn x d).1 ((key x d).1 h)).2 a ha).1 w hA
    refine ⟨e, ?_, hC⟩
    exact Classical.byContradiction fun hX' => hw ((hΔ' w w).2 ⟨rfl, e, hX, hX'⟩)

/-- **The first state satisfies the invariant**: `X₀` denoting `s`, `U` coreflexive and holding every predecessor
    of every arc, and `s` inside every arc's vacuous part (its keys and values in the universes, or keyed by a
    successor). -/
theorem acInv_init (s : Rel V D) (as : List (Revise V D)) (X₀ : Rel V D) (U : Rel V V) (hX₀ : rep X₀ = rep s)
    (hU : ∀ w v, rep U w v → w = v) (hUA : ∀ a ∈ as, ∀ w x, rep a.A w x → rep U w w)
    (hsV : ∀ a ∈ as, ∀ x d, rep s x d → Vac a x d) : AcInv s as (rep X₀) (rep U) := by
  rw [hX₀]
  exact ⟨hU, fun _ _ h => h, hsV, fun _ _ h _ => h, fun a ha _ _ _ w hw hA => (hw (hUA a ha w _ hA)).elim⟩

/-! ## The rounds, one by one -/

/-- **`k` delta rounds are `k` naive rounds**: from `(X₀, U)` with `AcInv`, the `k`-th delta state `Pd k` keeps
    `AcInv` and denotes the `k`-th naive state `Xn k` (each round `nub(acRound s as X)`, as `fixOn` runs it), by
    induction on `k` with `acDelta_round`. Hypotheses: `acDelta_round`'s at every delta state, `rep_acRound`'s at
    every naive state, and `nub` keeping the pairs there (`rep_nub`). -/
theorem acDelta_iterate (s : Rel V D) (as : List (Revise V D)) (X₀ : Rel V D) (U : Rel V V)
    (h₀ : AcInv s as (rep X₀) (rep U)) (hX₀ : rep X₀ = rep s)
    (hNd : ∀ j, StepMeets (naiveStep (Nat.repeat (acDelta as) j (X₀, U)).1) s as fun a => Nv a (rep (Nat.repeat (acDelta as) j (X₀, U)).1))
    (hD : ∀ j, StepMeets (deltaStep (Nat.repeat (acDelta as) j (X₀, U)).1 (Nat.repeat (acDelta as) j (X₀, U)).2)
      (Nat.repeat (acDelta as) j (X₀, U)).1 as
      fun a => Ld a (rep (Nat.repeat (acDelta as) j (X₀, U)).1) (rep (Nat.repeat (acDelta as) j (X₀, U)).2)
        (Alg.ran ((Nat.repeat (acDelta as) j (X₀, U)).2 ≫ a.A)))
    (hΔ' : ∀ j w v, rep (acDelta as (Nat.repeat (acDelta as) j (X₀, U))).2 w v ↔
      w = v ∧ ∃ e, rep (Nat.repeat (acDelta as) j (X₀, U)).1 w e ∧ ¬ rep (acDelta as (Nat.repeat (acDelta as) j (X₀, U))).1 w e)
    (hNn : ∀ j, StepMeets (naiveStep (Nat.repeat (fun X => (acRound s as X).nub) j s)) s as
      fun a => Nv a (rep (Nat.repeat (fun X => (acRound s as X).nub) j s)))
    (hnub : ∀ j, rep (acRound s as (Nat.repeat (fun X => (acRound s as X).nub) j s)).nub =
      rep (acRound s as (Nat.repeat (fun X => (acRound s as X).nub) j s))) :
    ∀ k, AcInv s as (rep (Nat.repeat (acDelta as) k (X₀, U)).1) (rep (Nat.repeat (acDelta as) k (X₀, U)).2) ∧
      rep (Nat.repeat (acDelta as) k (X₀, U)).1 = rep (Nat.repeat (fun X => (acRound s as X).nub) k s) := by
  intro k
  induction k with
  | zero => exact ⟨h₀, hX₀⟩
  | succ k ih =>
    obtain ⟨hI, he⟩ := ih
    obtain ⟨hr, hI'⟩ := acDelta_round s as _ _ hI (hNd k) (hD k) (hΔ' k)
    refine ⟨hI', hr.trans ((Freyd.Alg.RelSet.hom_ext fun x d => ?_).trans (hnub k).symm)⟩
    -- `rep (acRound s as X)` is read off `rep X` alone
    rw [rep_acRound s as _ (hNd k), rep_acRound s as _ (hNn k), he]

end LeetQ.Rel.AC3
