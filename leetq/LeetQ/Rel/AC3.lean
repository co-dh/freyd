import LeetQ.Rel.RepOps2
import LeetQ.Rel.RepComp
import LeetQ.Rel.RepDiv
import LeetQ.Rel.RepMem
import LeetQ.Rel.RepFold

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

/-- `R`'s two columns fit their objects: what `rep_nub` and `nub_rows_inj` take, through `one_ok`. -/
def NubFit {A B : Obj} (R : Rel A B) : Prop :=
  A.CodesFit #v[⟨R.n, R.key⟩] ∧ B.CodesFit #v[⟨R.n, R.val⟩] ∧
    Vals.PickFits A R.key (List.range R.n.toNat) ∧ Vals.PickFits B R.val (List.range R.n.toNat)

/-- The `j`-th delta state from `(X₀, U)`. -/
abbrev dState (as : List (Revise V D)) (X₀ : Rel V D) (U : Rel V V) (j : Nat) : Rel V D × Rel V V :=
  Nat.repeat (acDelta as) j (X₀, U)

/-- The `j`-th naive state from `X₀`, each round `nub(acRound s as X)` as `fixOn` runs it. -/
abbrev nState (s : Rel V D) (as : List (Revise V D)) (X₀ : Rel V D) (j : Nat) : Rel V D :=
  Nat.repeat (fun X => (acRound s as X).nub) j X₀

/-- **`k` delta rounds are `k` naive rounds**: from `(X₀, U)` with `AcInv`, the `k`-th delta state keeps `AcInv`
    and denotes the `k`-th naive state, by induction on `k` with `acDelta_round`. Hypotheses: `acDelta_round`'s
    at every delta state, `rep_acRound`'s at every naive state, and `rep_nub`'s there (`NubFit`). -/
theorem acDelta_iterate (s : Rel V D) (as : List (Revise V D)) (X₀ : Rel V D) (U : Rel V V)
    (h₀ : AcInv s as (rep X₀) (rep U))
    (hNd : ∀ j, StepMeets (naiveStep (dState as X₀ U j).1) s as fun a => Nv a (rep (dState as X₀ U j).1))
    (hD : ∀ j, StepMeets (deltaStep (dState as X₀ U j).1 (dState as X₀ U j).2) (dState as X₀ U j).1 as
      fun a => Ld a (rep (dState as X₀ U j).1) (rep (dState as X₀ U j).2) (Alg.ran ((dState as X₀ U j).2 ≫ a.A)))
    (hΔ' : ∀ j w v, rep (acDelta as (dState as X₀ U j)).2 w v ↔
      w = v ∧ ∃ e, rep (dState as X₀ U j).1 w e ∧ ¬ rep (acDelta as (dState as X₀ U j)).1 w e)
    (hNn : ∀ j, StepMeets (naiveStep (nState s as X₀ j)) s as fun a => Nv a (rep (nState s as X₀ j)))
    (hF : ∀ j, NubFit (acRound s as (nState s as X₀ j))) :
    ∀ k, AcInv s as (rep (dState as X₀ U k).1) (rep (dState as X₀ U k).2) ∧
      rep (dState as X₀ U k).1 = rep (nState s as X₀ k) := by
  intro k
  induction k with
  | zero => exact ⟨h₀, rfl⟩
  | succ k ih =>
    obtain ⟨hI, he⟩ := ih
    obtain ⟨hr, hI'⟩ := acDelta_round s as _ _ hI (hNd k) (hD k) (hΔ' k)
    refine ⟨hI', hr.trans ((Freyd.Alg.RelSet.hom_ext fun x d => ?_).trans
      (rep_nub _ (one_ok _ (hF k).1) (one_ok _ (hF k).2.1) (hF k).2.2.1 (hF k).2.2.2).symm)⟩
    -- `rep (acRound s as X)` is read off `rep X` alone
    rw [rep_acRound s as _ (hNd k), rep_acRound s as _ (hNn k), he]

/-! ## The stop: `iter` read as rounds, and the row count of a duplicate-free relation -/

/-- **What `iter` returns**: on states `g j` with `f (g j) = g (j+1)`, `iter n done f (g k)` is `g j` for a round
    `j` of `k … k+n` that is not `done` before `j`, and is `done` at `j` or is the last. -/
theorem iter_on {α : Type} (done : α → Bool) (f : α → α) (g : Nat → α) (hg : ∀ j, f (g j) = g (j + 1))
    (Q : α → Prop) : ∀ n k, (∀ j, k ≤ j → j ≤ k + n → (∀ i, k ≤ i → i < j → done (g i) = false) →
      (j = k + n ∨ done (g j) = true) → Q (g j)) → Q (iter n done f (g k)) := by
  intro n
  induction n with
  | zero =>
    intro k h
    unfold iter; rw [hylo]
    split
    · exact h k (Nat.le_refl _) (by omega) (fun i h1 h2 => absurd h2 (by omega)) (Or.inl rfl)
    · rename_i hn; simp at hn
  | succ n ih =>
    intro k h
    unfold iter; rw [hylo]
    split
    · rename_i hd
      have hd' : done (g k) = true := by simpa using hd
      exact h k (Nat.le_refl _) (by omega) (fun i h1 h2 => absurd h2 (by omega)) (Or.inr hd')
    · rename_i hd
      have hd' : done (g k) = false := by simpa using hd
      show Q (iter n done f (f (g k)))
      rw [hg k]
      exact ih (k + 1) fun j h1 h2 hlt hst => h j (by omega) (by omega)
        (fun i hi1 hi2 => if e : i = k then e ▸ hd' else hlt i (by omega) hi2) (hst.imp_left fun e => by omega)

/-- The rows of `R` are distinct pairs. -/
def RowsInj {A B : Obj} (R : Rel A B) : Prop :=
  ∀ {t t' : Fin R.n.toNat}, R.key.row t = R.key.row t' → R.val.row t = R.val.row t' → t = t'

/-- The pairs of `R`, one per row. -/
def prs {A B : Obj} (R : Rel A B) : List (A.El × B.El) := (List.finRange R.n.toNat).map fun t => (R.key.row t, R.val.row t)

theorem mem_prs {A B : Obj} (R : Rel A B) (p : A.El × B.El) : p ∈ prs R ↔ rep R p.1 p.2 := by
  obtain ⟨x, y⟩ := p
  simp [prs, rep_apply, Rel.Holds]

/-- An injective family of `a` values, all in `l`, needs `a ≤ |l|`. -/
theorem fin_len_le {β : Type} [DecidableEq β] : ∀ (a : Nat) (f : Fin a → β), (∀ {i j}, f i = f j → i = j) →
    ∀ (l : List β), (∀ i, f i ∈ l) → a ≤ l.length
  | 0, _, _, _, _ => Nat.zero_le _
  | a + 1, f, hf, l, hl => by
    have hlast := hl (Fin.last a)
    have h := fin_len_le a (fun i => f i.castSucc) (fun e => Fin.castSucc_inj.1 (hf e)) (l.erase (f (Fin.last a)))
      fun i => (List.mem_erase_of_ne fun e => by
        have h2 := Fin.castSucc_lt_last i; rw [hf e] at h2; exact Nat.lt_irrefl _ h2).2 (hl _)
    rw [List.length_erase_of_mem hlast] at h
    have := List.length_pos_of_mem hlast
    omega

/-- **A duplicate-free `R` inside `S` has at most `S`'s rows, and fewer when it misses a pair of `S`.** -/
theorem count_lt {A B : Obj} (R S : Rel A B) (hR : RowsInj R) (hle : ∀ x y, rep R x y → rep S x y) :
    R.n.toNat ≤ S.n.toNat ∧ ((∃ x y, rep S x y ∧ ¬ rep R x y) → R.n.toNat < S.n.toNat) := by
  classical
  have hf : ∀ {t t' : Fin R.n.toNat}, (R.key.row t, R.val.row t) = (R.key.row t', R.val.row t') → t = t' :=
    fun e => hR (congrArg Prod.fst e) (congrArg Prod.snd e)
  have hin : ∀ t : Fin R.n.toNat, (R.key.row t, R.val.row t) ∈ prs S := fun t =>
    (mem_prs S _).2 (hle _ _ ((mem_prs R _).1 (List.mem_map_of_mem (List.mem_finRange t))))
  have hlen : (prs S).length = S.n.toNat := by simp [prs]
  refine ⟨hlen ▸ fin_len_le _ _ hf _ hin, fun ⟨x, y, hS, hn⟩ => ?_⟩
  have h := fin_len_le _ _ hf ((prs S).erase (x, y)) fun t => (List.mem_erase_of_ne fun e => hn (by
    have : rep R (R.key.row t) (R.val.row t) := (mem_prs R (_, _)).1 (List.mem_map_of_mem (List.mem_finRange t))
    rw [show R.key.row t = x from congrArg Prod.fst e, show R.val.row t = y from congrArg Prod.snd e] at this
    exact this)).2 (hin t)
  rw [List.length_erase_of_mem ((mem_prs S (x, y)).2 hS), hlen] at h
  have := List.length_pos_of_mem ((mem_prs S (x, y)).2 hS)
  rw [hlen] at this
  omega

/-- A relation has no row iff it holds no pair. -/
theorem n_eq_zero_iff {A B : Obj} (R : Rel A B) : R.n = 0 ↔ ∀ x y, ¬ rep R x y := by
  rw [← USize.toNat_inj, USize.toNat_zero]
  refine ⟨fun h x y hr => ?_, fun h => Nat.eq_zero_of_not_pos fun hp => h (R.key.row ⟨0, hp⟩) (R.val.row ⟨0, hp⟩) ?_⟩
  · obtain ⟨i, -⟩ := hr; have := i.2; omega
  · show R.Holds _ _; unfold Rel.Holds; exact ⟨⟨0, hp⟩, rfl, rfl⟩

/-! ## The agreement -/

/-- **`acFix` is `fixOn` on the naive round**: the delta rounds from `(s.nub, U)` and `fixOn n (acRound s as)` from
    `s` end on one relation. Each delta round is a naive round (`acDelta_iterate`); `acFix` stops at the first
    `Δ = 𝟘`, `fixOn` at the first round leaving the row count, and both are the first round `c` with
    `acRound(Xc) ⊒ Xc` (`n_eq_zero_iff`, `count_lt` on the duplicate-free decreasing chain), which comes within
    `|s.nub|` rounds because each earlier round drops a row. Hypotheses: `n` at least that bound; `s`'s columns fit
    (`hs`); `U` coreflexive, holding every arc's predecessors, and `s` inside every arc's vacuous part
    (`acInv_init`); and `acDelta_iterate`'s per-round ones. -/
theorem acFix_eq_fixOn (s : Rel V D) (as : List (Revise V D)) (U : Rel V V) (n : Nat)
    (hn : s.nub.n.toNat + 1 ≤ n) (hs : NubFit s)
    (hU : ∀ w v, rep U w v → w = v) (hUA : ∀ a ∈ as, ∀ w x, rep a.A w x → rep U w w)
    (hsV : ∀ a ∈ as, ∀ x d, rep s x d → Vac a x d)
    (hNd : ∀ j, StepMeets (naiveStep (dState as s.nub U j).1) s as fun a => Nv a (rep (dState as s.nub U j).1))
    (hD : ∀ j, StepMeets (deltaStep (dState as s.nub U j).1 (dState as s.nub U j).2) (dState as s.nub U j).1 as
      fun a => Ld a (rep (dState as s.nub U j).1) (rep (dState as s.nub U j).2)
        (Alg.ran ((dState as s.nub U j).2 ≫ a.A)))
    (hΔ' : ∀ j w v, rep (acDelta as (dState as s.nub U j)).2 w v ↔
      w = v ∧ ∃ e, rep (dState as s.nub U j).1 w e ∧ ¬ rep (acDelta as (dState as s.nub U j)).1 w e)
    (hNn : ∀ j, StepMeets (naiveStep (nState s as s.nub j)) s as fun a => Nv a (rep (nState s as s.nub j)))
    (hF : ∀ j, NubFit (acRound s as (nState s as s.nub j))) :
    rep (acFix s as U).1 = rep (fixOn n (acRound s as) s).1 := by
  classical
  have hsn : rep s.nub = rep s := rep_nub _ (one_ok _ hs.1) (one_ok _ hs.2.1) hs.2.2.1 hs.2.2.2
  have hit := acDelta_iterate s as s.nub U (acInv_init s as s.nub U hsn hU hUA hsV) hNd hD hΔ' hNn hF
  -- a naive round fixes `Y j` when it keeps all of it
  let Fix := fun j => ∀ x d, rep (nState s as s.nub j) x d → rep (nState s as s.nub (j + 1)) x d
  have hmem : ∀ j x d, rep (nState s as s.nub (j + 1)) x d ↔ rep s x d ∧ ∀ a ∈ as, Nv a (rep (nState s as s.nub j)) x d :=
    fun j x d => by
      rw [show nState s as s.nub (j + 1) = (acRound s as (nState s as s.nub j)).nub from rfl,
        rep_nub _ (one_ok _ (hF j).1) (one_ok _ (hF j).2.1) (hF j).2.2.1 (hF j).2.2.2, rep_acRound s as _ (hNn j)]
  have hsub : ∀ j x d, rep (nState s as s.nub (j + 1)) x d → rep (nState s as s.nub j) x d := fun j x d h => by
    obtain ⟨hs', hNv⟩ := (hmem j x d).1 h
    rw [← (hit j).2] at hNv ⊢
    exact (hit j).1.2.2.2.1 x d hs' hNv
  have hinj : ∀ j, RowsInj (nState s as s.nub j)
    | 0 => nub_rows_inj s (one_ok _ hs.1) (one_ok _ hs.2.1) hs.2.2.1 hs.2.2.2
    | j + 1 => nub_rows_inj (acRound s as (nState s as s.nub j)) (one_ok _ (hF j).1) (one_ok _ (hF j).2.1)
        (hF j).2.2.1 (hF j).2.2.2
  -- `fixOn`'s stop: equal row count is `Fix`
  have hcnt : ∀ j, (nState s as s.nub (j + 1)).n.toNat = (nState s as s.nub j).n.toNat ↔ Fix j := fun j => by
    obtain ⟨hle, hlt⟩ := count_lt _ _ (hinj (j + 1)) (hsub j)
    refine ⟨fun he x d hx => Classical.byContradiction fun hn' => absurd he (Nat.ne_of_lt (hlt ⟨x, d, hx, hn'⟩)),
      fun hf => Nat.le_antisymm hle (count_lt _ _ (hinj j) hf).1⟩
  have hdec : ∀ j, ¬ Fix j → (nState s as s.nub (j + 1)).n.toNat < (nState s as s.nub j).n.toNat := fun j h =>
    Nat.lt_of_le_of_ne (count_lt _ _ (hinj (j + 1)) (hsub j)).1 fun e => h ((hcnt j).1 e)
  -- `acFix`'s stop: `Δ = 𝟘` gives `Fix`, and after the first round is `Fix`
  have hfix : ∀ j, (dState as s.nub U j).2.n = 0 → Fix j := fun j hz x d hx => by
    obtain ⟨-, hXs, hXv, -, hXo⟩ := (hit j).1
    rw [← (hit j).2] at hx
    refine (hmem j x d).2 ⟨hXs x d hx, fun a ha => ⟨fun w hA => ?_, hXv a ha x d hx⟩⟩
    rw [← (hit j).2]
    exact hXo a ha x d hx w (fun hw => (n_eq_zero_iff _).1 hz w w hw) hA
  have hdl : ∀ j, (dState as s.nub U (j + 1)).2.n = 0 ↔ Fix j := fun j => by
    have e1 : rep (acDelta as (dState as s.nub U j)).1 = rep (nState s as s.nub (j + 1)) := (hit (j + 1)).2
    show (acDelta as (dState as s.nub U j)).2.n = 0 ↔ Fix j
    rw [n_eq_zero_iff]
    refine ⟨fun h x d hx => Classical.byContradiction fun hn' => h x x ((hΔ' j x x).2 ⟨rfl, d, ?_, ?_⟩),
      fun h w v hwv => ?_⟩
    · rw [(hit j).2]; exact hx
    · rw [e1]; exact hn'
    · obtain ⟨-, d, h1, h2⟩ := (hΔ' j w v).1 hwv
      exact h2 (by rw [e1]; exact h w d (by rw [← (hit j).2]; exact h1))
  -- the descent: rounds before the first `Fix` each drop a row
  have hdesc : ∀ m, (∀ i < m, ¬ Fix i) → (nState s as s.nub m).n.toNat + m ≤ s.nub.n.toNat := fun m => by
    induction m with
    | zero => intro _; exact Nat.le_refl _
    | succ m ih => intro h; have := hdec m (h m (by omega)); have := ih fun i hi => h i (by omega); omega
  have hfirst : ∀ m, (∀ i < m, ¬ Fix i) ∨ ∃ c < m, Fix c ∧ ∀ i < c, ¬ Fix i := fun m => by
    induction m with
    | zero => exact Or.inl fun i hi => absurd hi (by omega)
    | succ m ih =>
      rcases ih with h | ⟨c, hc, hf, hlt⟩
      · by_cases hm : Fix m
        · exact Or.inr ⟨m, by omega, hm, h⟩
        · exact Or.inl fun i hi => if e : i = m then e ▸ hm else h i (by omega)
      · exact Or.inr ⟨c, by omega, hf, hlt⟩
  obtain ⟨c, hc, hcF, hcl⟩ : ∃ c < s.nub.n.toNat + 1, Fix c ∧ ∀ i < c, ¬ Fix i := by
    rcases hfirst (s.nub.n.toNat + 1) with h | h
    · have := hdesc _ h; omega
    · exact h
  have hcmin : ∀ i, Fix i → c ≤ i := fun i hi => Nat.le_of_not_lt fun h => hcl i h hi
  -- `acFix` ends at round `c + 1`, or at round `0` when `c = 0`
  have hA : rep (acFix s as U).1 = rep (nState s as s.nub (c + 1)) := by
    obtain ⟨j, -, hj, hlt, hst, he⟩ : ∃ j, 0 ≤ j ∧ j ≤ 0 + (s.nub.n.toNat + 1) ∧
        (∀ i, 0 ≤ i → i < j → ((dState as s.nub U i).2.n == 0) = false) ∧
        (j = 0 + (s.nub.n.toNat + 1) ∨ ((dState as s.nub U j).2.n == 0) = true) ∧
        (acFix s as U).1 = (dState as s.nub U j).1 :=
      iter_on (α := Rel V D × Rel V V × Nat) (fun (_, Δ, _) => Δ.n == 0)
        (fun (X, Δ, k) => let (X', Δ') := acDelta as (X, Δ); (X', Δ', k + 1))
        (fun j => ((dState as s.nub U j).1, (dState as s.nub U j).2, j)) (fun _ => rfl)
        (fun r => ∃ j, 0 ≤ j ∧ j ≤ 0 + (s.nub.n.toNat + 1) ∧
          (∀ i, 0 ≤ i → i < j → ((dState as s.nub U i).2.n == 0) = false) ∧
          (j = 0 + (s.nub.n.toNat + 1) ∨ ((dState as s.nub U j).2.n == 0) = true) ∧ r.1 = (dState as s.nub U j).1)
        (s.nub.n.toNat + 1) 0 fun j h0 h1 hlt hst => ⟨j, h0, h1, hlt, hst, rfl⟩
    rw [he, (hit j).2]
    simp only [beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at hlt hst
    cases j with
    | zero =>
      have hF0 := hfix 0 (hst.resolve_left (by omega))
      have hc0 : c = 0 := Nat.le_zero.1 (hcmin 0 hF0)
      subst hc0
      exact Freyd.Alg.RelSet.hom_ext fun x d => ⟨hF0 x d, hsub 0 x d⟩
    | succ j =>
      have hnf : ∀ i < j, ¬ Fix i := fun i hi hf => hlt (i + 1) (by omega) (by omega) ((hdl i).2 hf)
      have hjF : Fix j := by
        rcases hst with e | e
        · exact Classical.byContradiction fun h => by
            have := hdesc (j + 1) fun i hi => if e' : i = j then e' ▸ h else hnf i (by omega); omega
        · exact (hdl j).1 e
      have : c = j := Nat.le_antisymm (hcmin j hjF) (Nat.le_of_not_lt fun h => hnf c h hcF)
      rw [this]
  -- `fixOn` ends at round `c + 1`
  have hB : (fixOn n (acRound s as) s).1 = nState s as s.nub (c + 1) := by
    let cnt : Nat → Nat := fun j => match j with | 0 => s.nub.n.toNat + 1 | i + 1 => (nState s as s.nub i).n.toNat
    obtain ⟨j, -, hj, hlt, hst, he⟩ : ∃ j, 0 ≤ j ∧ j ≤ 0 + n ∧
        (∀ i, 0 ≤ i → i < j → (cnt i == (nState s as s.nub i).n.toNat) = false) ∧
        (j = 0 + n ∨ (cnt j == (nState s as s.nub j).n.toNat) = true) ∧
        (fixOn n (acRound s as) s).1 = nState s as s.nub j :=
      iter_on (α := Nat × Rel V D × Nat) (fun (p, x, _) => p == x.n.toNat) (fun (_, x, k) => (x.n.toNat, (acRound s as x).nub, k + 1))
        (fun j => (cnt j, nState s as s.nub j, j)) (fun _ => rfl)
        (fun r => ∃ j, 0 ≤ j ∧ j ≤ 0 + n ∧
          (∀ i, 0 ≤ i → i < j → (cnt i == (nState s as s.nub i).n.toNat) = false) ∧
          (j = 0 + n ∨ (cnt j == (nState s as s.nub j).n.toNat) = true) ∧ r.2.1 = nState s as s.nub j)
        n 0 fun j h0 h1 hlt hst => ⟨j, h0, h1, hlt, hst, rfl⟩
    rw [he]
    simp only [beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at hlt hst
    have hnf : ∀ i, i + 1 < j → ¬ Fix i := fun i hi hf => hlt (i + 1) (by omega) hi ((hcnt i).2 hf).symm
    cases j with
    | zero => rcases hst with e | e <;> simp [cnt, Nat.repeat] at e <;> omega
    | succ j =>
      have hjF : Fix j := by
        rcases hst with e | e
        · exact Classical.byContradiction fun h => by
            have := hdesc (j + 1) fun i hi => if e' : i = j then e' ▸ h else hnf i (by omega); omega
        · exact (hcnt j).1 e.symm
      rw [Nat.le_antisymm (hcmin j hjF) (Nat.le_of_not_lt fun h => hnf c (by omega) hcF)]
  rw [hA, hB]

end LeetQ.Rel.AC3
