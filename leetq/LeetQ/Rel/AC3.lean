import LeetQ.Rel.RepOps2
import LeetQ.Rel.RepComp
import LeetQ.Rel.RepDiv
import LeetQ.Rel.RepMem
import LeetQ.Rel.RepFold
import LeetQ.Rel.CRelRel
import LeetQ.Rel.CRelLoop
import LeetQ.Rel.AC3Def

/-! # AC-3 (arc consistency, Mackworth's algorithm 3): the delta-round kernel (`AC3Def.lean`) and its agreement with the naive rounds -/

/-!
  The delta AC-3 round (`Alg.acDelta`) read in `Rel(Set)` against the naive round (`Alg.acRound`): from a state
  satisfying the invariant `AcInv`, one delta round denotes what one naive round does, and its `Δ′` re-establishes
  the invariant. Every op is read back under its twin's bit; the bits of a run are one bit, `fixOnC`'s or `acFixC`'s.
-/

namespace LeetQ.Rel.AC3

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF LeetQ.Rel.Rep LeetQ.Rel.Rep.OpsN LeetQ.Rel.Rep.FoldN
open Freyd.Alg.RelSet (comp_apply inter_apply union_apply recip_apply hom_ext)

-- `unionC`'s `hat`, as `CRelLoop`'s (local there): `razeTo`'s read-back of two atom parts
set_option quotPrecheck false in
local notation "hatOK" => ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
  (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
    USize.size), Vals.RazeFits (.atom t) x y → (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList

variable {V D : Obj}

/-! ## The rounds, pointwise -/

/-- **`rep (foldlC step as Y) = rep Y ∩ ⋂ₐ M a`** under its bit, each step denoting the relation before it met with
    `M a` under the step's bit; by induction on the arcs, from any carried bit. -/
theorem rep_foldlC {γ : Type} (step : Rel V D → γ → Rel V D × Bool) (M : γ → V.El → D.El → Prop)
    (h : ∀ Y a, (step Y a).2 = true → ∀ x d, rep (step Y a).1 x d ↔ rep Y x d ∧ M a x d) :
    ∀ (as : List γ) (Y : Rel V D) (b : Bool),
      (as.foldl (fun p a => let r := step p.1 a; (r.1, p.2 && r.2)) (Y, b)).2 = true →
      b = true ∧ ∀ x d, rep (as.foldl (fun p a => let r := step p.1 a; (r.1, p.2 && r.2)) (Y, b)).1 x d ↔
        rep Y x d ∧ ∀ a ∈ as, M a x d
  | [], Y, b, hb => ⟨hb, fun x d => by simp⟩
  | a :: t, Y, b, hb => by
    obtain ⟨hb', ih⟩ := rep_foldlC step M h t (step Y a).1 (b && (step Y a).2) hb
    simp only [Bool.and_eq_true] at hb'
    refine ⟨hb'.1, fun x d => ?_⟩
    rw [List.foldl_cons]
    exact (ih x d).trans (by rw [h Y a hb'.2 x d, List.forall_mem_cons, and_assoc])

/-- The vacuous part of `A\(X C)` at `(x, d)`: `x` has an `A`-predecessor, or `x`, `d` are in the universes. -/
def Vac (a : Revise V D) (x : V.El) (d : D.El) : Prop :=
  (∃ w, rep a.A w x) ∨ ((∃ p, a.UV.key.row p = x) ∧ ∃ j, a.UD.key.row j = d)

/-- `A\(X C)` at `(x, d)`, as `rep_leftDivC` reads it with `rep_compC` for `X C`. -/
def Nv (a : Revise V D) (X : V.El → D.El → Prop) (x : V.El) (d : D.El) : Prop :=
  (∀ w, rep a.A w x → ∃ e, X w e ∧ rep a.C e d) ∧ Vac a x d

/-- The delta arc, for a coreflexive `Δ`: `A\(X C)` checked only at the predecessors `w` in `Δ`. -/
def Dl (a : Revise V D) (X : V.El → D.El → Prop) (Δ : V.El → V.El → Prop) (x : V.El) (d : D.El) : Prop :=
  ∀ w, Δ w w → rep a.A w x → ∃ e, X w e ∧ rep a.C e d

/-- The naive body read in `Rel(Set)`, on a predicate `X`: `s ∩ ⋂ₐ Aₐ\(X Cₐ)`. -/
def body (s : Rel V D) (as : List (Revise V D)) (X : V.El → D.El → Prop) (x : V.El) (d : D.El) : Prop :=
  rep s x d ∧ ∀ a ∈ as, Nv a X x d

/-- **`body` is monotone in `X`**: `Nv` is. -/
theorem body_mono (s : Rel V D) (as : List (Revise V D)) {X Y : V.El → D.El → Prop} (h : ∀ x d, X x d → Y x d) :
    ∀ x d, body s as X x d → body s as Y x d := fun _ _ ⟨hs, hN⟩ =>
  ⟨hs, fun a ha => ⟨fun w hA => let ⟨e, hX, hC⟩ := (hN a ha).1 w hA; ⟨e, h w e hX, hC⟩, (hN a ha).2⟩⟩

theorem body_congr (s : Rel V D) (as : List (Revise V D)) {X Y : V.El → D.El → Prop} (h : ∀ x d, X x d ↔ Y x d) :
    ∀ x d, body s as X x d ↔ body s as Y x d := fun x d =>
  ⟨body_mono s as (fun x d => (h x d).1) x d, body_mono s as (fun x d => (h x d).2) x d⟩

/-- **The naive arc step under its bit**: `rep_interC`, `rep_leftDivC`, `rep_compC`. -/
theorem rep_naiveStepC (X Y : Rel V D) (a : Revise V D) (hb : (naiveStepC X Y a).2 = true) (x : V.El) (d : D.El) :
    rep (naiveStepC X Y a).1 x d ↔ rep Y x d ∧ Nv a (rep X) x d := by
  simp only [naiveStepC, Bool.and_eq_true] at hb ⊢
  obtain ⟨⟨hc, hL⟩, hi⟩ := hb
  rw [rep_interC _ _ hi, inter_apply, rep_leftDivC _ _ _ _ hL]
  simp only [rep_compC _ _ hc, comp_apply]
  exact Iff.rfl

/-- **The delta arc step under its bit**, `Δ` coreflexive: `rep_unionC`, `rep_antiJoinC`, `rep_ranC`, `rep_interC`,
    `rep_leftDivC`, `rep_compC`. The vacuous part of `(Δ A)\…` matters only off `ran(Δ A)`, where the anti-join side
    already holds; on `Δ`, `Δ w v` is `w = v`. -/
theorem rep_deltaStepC (hat : hatOK) (X : Rel V D) (Δ : Rel V V) (hΔ : ∀ w v, rep Δ w v → w = v) (Y : Rel V D)
    (a : Revise V D) (hb : (deltaStepC X Δ Y a).2 = true) (x : V.El) (d : D.El) :
    rep (deltaStepC X Δ Y a).1 x d ↔ rep Y x d ∧ Dl a (rep X) (rep Δ) x d := by
  classical
  simp only [deltaStepC, Bool.and_eq_true] at hb ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨hR, hT⟩, hj⟩, hΔX⟩, hS⟩, hL⟩, hi⟩, hu⟩ := hb
  have hR' : ∀ w, rep (compC Δ a.A).1 w x ↔ rep Δ w w ∧ rep a.A w x := fun w => by
    rw [rep_compC _ _ hR, comp_apply]
    exact ⟨fun ⟨v, h1, h2⟩ => by obtain rfl := hΔ w v h1; exact ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨w, h1, h2⟩⟩
  have hS' : ∀ w, rep (compC (compC Δ X).1 a.C).1 w d ↔ rep Δ w w ∧ ∃ e, rep X w e ∧ rep a.C e d := fun w => by
    rw [rep_compC _ _ hS, comp_apply]
    simp only [rep_compC _ _ hΔX, comp_apply]
    exact ⟨fun ⟨e, ⟨v, h1, h2⟩, h3⟩ => by obtain rfl := hΔ w v h1; exact ⟨h1, e, h2, h3⟩,
      fun ⟨h1, e, h2, h3⟩ => ⟨e, ⟨w, h1, h2⟩, h3⟩⟩
  have hT' : (∃ z, rep (ranC (compC Δ a.A).1).1 z x) ↔ ∃ w, rep (compC Δ a.A).1 w x := by
    rw [rep_ranC _ hT]
    exact ⟨fun ⟨_, _, w, _, h⟩ => ⟨w, h⟩, fun ⟨w, h⟩ => ⟨x, rfl, w, h, h⟩⟩
  rw [rep_unionC hat _ _ hu, union_apply, rep_conv, recip_apply, rep_antiJoinC _ _ hj, comp_apply, rep_conv,
    rep_interC _ _ hi, inter_apply, rep_leftDivC _ _ _ _ hL]
  constructor
  · rintro (⟨y, hY, rfl, hn⟩ | ⟨hY, hall, -⟩)
    · exact ⟨hY, fun w hw hA => (hn (hT'.2 ⟨w, (hR' w).2 ⟨hw, hA⟩⟩)).elim⟩
    · exact ⟨hY, fun w hw hA => ((hS' w).1 (hall w ((hR' w).2 ⟨hw, hA⟩))).2⟩
  · rintro ⟨hY, hDl⟩
    by_cases h : ∃ w, rep (compC Δ a.A).1 w x
    · exact Or.inr ⟨hY, fun w hw => (hS' w).2 ⟨((hR' w).1 hw).1, hDl w ((hR' w).1 hw).1 ((hR' w).1 hw).2⟩,
        Or.inl h⟩
    · exact Or.inl ⟨x, hY, rfl, fun hz => h (hT'.1 hz)⟩

/-! ## The invariant and one round -/

/-- The state `(X, Δ)` of the delta rounds for the body `s ∩ ⋂ₐ Aₐ\(X Cₐ)`: `Δ` coreflexive; `X ⊑ s`; `X` inside
    every arc's vacuous part; `X ⊒` the naive round on `X`; and every pair of `X` supported, at each predecessor
    outside `Δ`, as the naive round asks — so only the predecessors in `Δ` need checking. -/
def AcInv (s : Rel V D) (as : List (Revise V D)) (X : V.El → D.El → Prop) (Δ : V.El → V.El → Prop) : Prop :=
  (∀ w v, Δ w v → w = v) ∧ (∀ x d, X x d → rep s x d) ∧ (∀ a ∈ as, ∀ x d, X x d → Vac a x d) ∧
    (∀ x d, rep s x d → (∀ a ∈ as, Nv a X x d) → X x d) ∧
    ∀ a ∈ as, ∀ x d, X x d → ∀ w, ¬ Δ w w → rep a.A w x → ∃ e, X w e ∧ rep a.C e d

-- `𝟙_X`, the coreflexive on the pairs of `X`; the pairs of `X` not in `X′`, as
-- `acDeltaC` names them (fields applied, not projected: `X.key` would be one identifier, not the parameter `X`)
set_option hygiene false in
local notation "pairsU(" X ")" => idU (t := Obj.prod V D) (Rel.key X, Rel.val X)
set_option hygiene false in
local notation "gone(" X ", " X' ")" => antiJoinC (pairsU(X)) (pairsU(X'))

/-- `rep 𝟙_X` is `𝟙` on the pairs of `X` (`idU_holds`). -/
theorem rep_idU_pairs (X : Rel V D) (p q : V.El × D.El) : rep (pairsU(X)) p q ↔ p = q ∧ rep X p.1 p.2 := by
  rw [rep_apply, idU_holds]
  exact and_congr Iff.rfl ⟨fun ⟨i, e⟩ => by subst e; exact ⟨i, rfl, rfl⟩, fun ⟨i, e1, e2⟩ => ⟨i, Prod.ext e1 e2⟩⟩

/-- **`Δ′ = ran(outl(antiJoin(𝟙_X, 𝟙_X′)))` is the variables with a pair of `X` not in `X′`**, under the bits of
    `antiJoinC` and `ranC`: `rep_ranC`, `outl_holds`, `rep_antiJoinC`, `rep_idU_pairs`. -/
theorem rep_dPrime (X X' : Rel V D) (hg : (gone(X, X')).2 = true) (hr : (ranC (outl (gone(X, X')).1)).2 = true)
    (w v : V.El) : rep (ranC (outl (gone(X, X')).1)).1 w v ↔ w = v ∧ ∃ e, rep X w e ∧ ¬ rep X' w e := by
  have hJ : ∀ a b, rep (gone(X, X')).1 a b ↔ ∃ y, rep (pairsU(X)) a y ∧ y = b ∧ ¬ ∃ x, rep (pairsU(X')) x y :=
    fun a b => by rw [rep_antiJoinC _ _ hg]; exact Iff.rfl
  rw [rep_ranC _ hr]
  show w = v ∧ (∃ a, rep (outl (gone(X, X')).1) a w ∧ rep (outl (gone(X, X')).1) a v) ↔ _
  constructor
  · rintro ⟨rfl, a, ha, -⟩
    obtain ⟨z, hz⟩ := (outl_holds _ a w).1 ha
    obtain ⟨y, hy, rfl, hn⟩ := (hJ a _).1 hz
    obtain ⟨rfl, hX⟩ := (rep_idU_pairs X a _).1 hy
    exact ⟨rfl, z, hX, fun h' => hn ⟨(w, z), (rep_idU_pairs X' _ _).2 ⟨rfl, h'⟩⟩⟩
  · rintro ⟨rfl, e, hX, hn⟩
    have ho : rep (outl (gone(X, X')).1) (w, e) w :=
      (outl_holds _ _ w).2 ⟨e, (hJ _ _).2 ⟨(w, e), (rep_idU_pairs X _ _).2 ⟨rfl, hX⟩, rfl, fun ⟨x, hx⟩ => by
        obtain ⟨rfl, h'⟩ := (rep_idU_pairs X' _ _).1 hx
        exact hn h'⟩⟩
    exact ⟨rfl, (w, e), ho, ho⟩

/-- **One delta round is one naive round, and keeps the invariant**: from `AcInv s as (rep X) (rep Δ)`, under the
    round's bit, `rep (acDelta as (X, Δ)).1 = body s as (rep X)`, and `AcInv` holds of the new `X′` with the new
    `Δ′` (`rep_foldlC` at `rep_deltaStepC`, `rep_dPrime`). -/
theorem acDelta_round (hat : hatOK) (s : Rel V D) (as : List (Revise V D)) (X : Rel V D) (Δ : Rel V V)
    (hI : AcInv s as (rep X) (rep Δ)) (hb : (acDeltaC as (X, Δ)).2 = true) :
    (∀ x d, rep (acDelta as (X, Δ)).1 x d ↔ body s as (rep X) x d) ∧
      AcInv s as (rep (acDelta as (X, Δ)).1) (rep (acDelta as (X, Δ)).2) := by
  classical
  obtain ⟨hΔ, hXs, hXv, hXn, hXo⟩ := hI
  simp only [acDeltaC, Bool.and_eq_true] at hb
  obtain ⟨⟨hf, hg⟩, hr⟩ := hb
  have hd := (rep_foldlC _ _ (rep_deltaStepC hat X Δ hΔ) as X true hf).2
  have hΔ' := rep_dPrime X (foldlC (deltaStepC X Δ) as X).1 hg hr
  -- the two rounds agree pointwise
  have key : ∀ x d, rep (acDelta as (X, Δ)).1 x d ↔ body s as (rep X) x d := fun x d => by
    refine (hd x d).trans ⟨?_, ?_⟩
    · rintro ⟨hX, hDl⟩
      refine ⟨hXs x d hX, fun a ha => ⟨fun w hA => ?_, hXv a ha x d hX⟩⟩
      by_cases hw : rep Δ w w
      · exact hDl a ha w hw hA
      · exact hXo a ha x d hX w hw hA
    · rintro ⟨hs, hNv⟩
      exact ⟨hXn x d hs hNv, fun a ha w _ hA => (hNv a ha).1 w hA⟩
  have hle : ∀ x d, rep (acDelta as (X, Δ)).1 x d → rep X x d := fun x d h => ((hd x d).1 h).1
  refine ⟨key, fun w v h => ((hΔ' w v).1 h).1, fun x d h => hXs x d (hle x d h),
    fun a ha x d h => hXv a ha x d (hle x d h), fun x d hs hNv => ?_, fun a ha x d h w hw hA => ?_⟩
  · -- `Nv` is monotone in `X`, and `X′ ⊑ X`
    refine (key x d).2 ⟨hs, fun a ha => ⟨fun w hA => ?_, (hNv a ha).2⟩⟩
    obtain ⟨e, hX, hC⟩ := (hNv a ha).1 w hA
    exact ⟨e, hle w e hX, hC⟩
  · -- off `Δ′` the pairs of `X` at `w` are pairs of `X′`
    obtain ⟨e, hX, hC⟩ := (((key x d).1 h).2 a ha).1 w hA
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

/-! ## The naive iterates in `Rel(Set)` -/

/-- The `k`-th iterate of the naive body from `s`. -/
def naive (s : Rel V D) (as : List (Revise V D)) : Nat → V.El → D.El → Prop
  | 0 => fun x d => rep s x d
  | k + 1 => body s as (naive s as k)

theorem naive_le (s : Rel V D) (as : List (Revise V D)) : ∀ k x d, naive s as k x d → rep s x d
  | 0, _, _, h => h
  | _ + 1, _, _, h => h.1

/-- **The iterates decrease**: `body ⊑ s`, and `body` is monotone. -/
theorem naive_anti (s : Rel V D) (as : List (Revise V D)) : ∀ k x d, naive s as (k + 1) x d → naive s as k x d
  | 0, x, d, h => naive_le s as 1 x d h
  | k + 1, x, d, h => body_mono s as (naive_anti s as k) x d h

/-- **From a fixed iterate on, the iterates stay**. -/
theorem naive_stable (s : Rel V D) (as : List (Revise V D)) {c : Nat}
    (hc : ∀ x d, naive s as (c + 1) x d ↔ naive s as c x d) : ∀ k, c ≤ k → ∀ x d, naive s as k x d ↔ naive s as c x d := by
  intro k hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction m with
  | zero => exact fun _ _ => Iff.rfl
  | succ m ih => exact fun x d => (body_congr s as ih x d).trans (hc x d)

/-- **Two fixed iterates are one**: the later is the earlier by `naive_stable`. -/
theorem naive_fixed_eq (s : Rel V D) (as : List (Revise V D)) {c j : Nat}
    (hc : ∀ x d, naive s as (c + 1) x d ↔ naive s as c x d) (hj : ∀ x d, naive s as (j + 1) x d ↔ naive s as j x d) :
    ∀ x d, naive s as j x d ↔ naive s as c x d := by
  rcases Nat.le_total c j with h | h
  · exact naive_stable s as hc j h
  · exact fun x d => (naive_stable s as hj c h x d).symm

/-! ## Row counts -/

/-- The rows of `R` are distinct pairs. -/
def RowsInj {A B : Obj} (R : Rel A B) : Prop :=
  ∀ {t t' : Fin R.n.toNat}, R.key.row t = R.key.row t' → R.val.row t = R.val.row t' → t = t'

/-- **`nubC`'s answer has distinct rows under its bit**: `nub_rows_inj` at the premises `rep_nubC` reads. -/
theorem rowsInj_nubC {A B : Obj} (R : Rel A B) (hb : (nubC R).2 = true) : RowsInj (nubC R).1 := by
  simp only [nubC, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨hK, hV⟩, hk⟩, hv⟩ := hb
  rw [nubC_fst]
  exact nub_rows_inj R (oneOK_of_codesC A R.key hK) (oneOK_of_codesC B R.val hV)
    (pickFits_of_fitsN A R.key _ hk _ (by simp)) (pickFits_of_fitsN B R.val _ hv _ (by simp))

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

/-- A weaker test counts fewer, and strictly fewer where it misses an element the stronger one takes. -/
theorem countP_lt {β : Type} (p q : β → Bool) : ∀ l : List β, (∀ x ∈ l, p x = true → q x = true) →
    (∃ x ∈ l, q x = true ∧ p x = false) → l.countP p < l.countP q
  | [], _, ⟨_, h, _⟩ => by simp at h
  | y :: l, hpq, ⟨x, hx, hq, hp⟩ => by
    have hm : l.countP p ≤ l.countP q := List.countP_mono_left fun z hz => hpq z (List.mem_cons_of_mem _ hz)
    have hy := hpq y List.mem_cons_self
    simp only [List.countP_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · simp [hq, hp]; omega
    · have := countP_lt p q l (fun z hz => hpq z (List.mem_cons_of_mem _ hz)) ⟨x, hx, hq, hp⟩
      cases hpy : p y
      · cases q y <;> simp <;> omega
      · simp [hy hpy]; omega

/-- **The naive iterates are fixed within `|s.nub|` rounds**: each earlier one drops a pair of `s.nub`'s rows
    (`countP_lt`). -/
theorem exists_fixed (s : Rel V D) (as : List (Revise V D)) (hsn : ∀ x d, rep s.nub x d ↔ rep s x d) :
    ∃ c ≤ s.nub.n.toNat, ∀ x d, naive s as (c + 1) x d ↔ naive s as c x d := by
  classical
  let cnt : Nat → Nat := fun k => (prs s.nub).countP fun p => decide (naive s as k p.1 p.2)
  have hdrop : ∀ k, ¬ (∀ x d, naive s as (k + 1) x d ↔ naive s as k x d) → cnt (k + 1) < cnt k := fun k h => by
    obtain ⟨x, d, hx, hn⟩ : ∃ x d, naive s as k x d ∧ ¬ naive s as (k + 1) x d :=
      Classical.byContradiction fun hc => h fun x d =>
        ⟨naive_anti s as k x d, fun hk => Classical.byContradiction fun hn => hc ⟨x, d, hk, hn⟩⟩
    exact countP_lt _ _ _ (fun p _ hp => by simp only [decide_eq_true_eq] at hp ⊢; exact naive_anti s as k p.1 p.2 hp)
      ⟨(x, d), (mem_prs _ _).2 ((hsn x d).2 (naive_le s as k x d hx)), by simpa using hx, by simpa using hn⟩
  have hdesc : ∀ m, (∀ i < m, ¬ ∀ x d, naive s as (i + 1) x d ↔ naive s as i x d) → cnt m + m ≤ cnt 0 := by
    intro m
    induction m with
    | zero => intro _; exact Nat.le_refl _
    | succ m ih => intro h; have := hdrop m (h m (by omega)); have := ih fun i hi => h i (by omega); omega
  have h0 : cnt 0 ≤ s.nub.n.toNat := Nat.le_trans List.countP_le_length (by simp [prs])
  refine Classical.byContradiction fun hc => ?_
  have := hdesc (s.nub.n.toNat + 1) fun i hi hf => hc ⟨i, by omega, hf⟩
  omega

/-! ## The agreement -/

/-- **`acFix` is `fixOn` on the naive round**: the delta rounds from `(s.nub, U)` and `fixOn n (acRound s as)` from
    `s` end on one relation, the first fixed naive iterate (`exists_fixed`). Each delta round is a naive round
    (`acDelta_round`); `acFix` stops at `Δ = 𝟘`, a fixed iterate by `AcInv`, or after `|s.nub| + 1` rounds; `fixOn`
    stops at an unchanged row count, a fixed iterate by `count_lt` on `nubC`'s distinct rows, or after `n` rounds.
    Capacity is the two runs' bits, `fixOnC`'s and `acFixC`'s. Hypotheses: `hat` (`rep_unionC`'s); `n` at least
    `|s.nub| + 1`; `U` coreflexive, holding every arc's predecessors, and `s` inside every arc's vacuous part
    (`acInv_init`). -/
theorem acFix_eq_fixOn (hat : hatOK) (s : Rel V D) (as : List (Revise V D)) (U : Rel V V) (n : Nat)
    (hn : s.nub.n.toNat + 1 ≤ n)
    (hU : ∀ w v, rep U w v → w = v) (hUA : ∀ a ∈ as, ∀ w x, rep a.A w x → rep U w w)
    (hsV : ∀ a ∈ as, ∀ x d, rep s x d → Vac a x d)
    (hb : (fixOnC n (acRoundC s as) s).2 = true) (hd : (acFixC s as U).2 = true) :
    rep (acFix s as U).1 = rep (fixOn n (acRound s as) s).1 := by
  classical
  simp only [fixOnC, Bool.and_eq_true] at hb
  obtain ⟨h0, hbit⟩ := hb
  simp only [acFixC, Bool.and_eq_true] at hd
  obtain ⟨-, hdbit⟩ := hd
  have hs0 : ∀ x d, rep (nubC s).1 x d ↔ rep s x d := by rw [rep_nubC s h0]; exact fun _ _ => Iff.rfl
  have hcnt : (nubC s).1.n.toNat = s.nub.n.toNat := by rw [nubC_fst]
  obtain ⟨c, hc, hcF⟩ := exists_fixed s as (by rw [← nubC_fst]; exact hs0)
  -- the naive run: `fixOnC`'s rounds, the state `(count before, X, round)`
  let fr : Nat × Rel V D × Nat → Nat × Rel V D × Nat := fun st =>
    (st.2.1.n.toNat, (nubC (acRoundC s as st.2.1).1).1, st.2.2 + 1)
  let a₀ : Nat × Rel V D × Nat := ((nubC s).1.n.toNat + 1, (nubC s).1, 0)
  have hB : ∀ x d, rep (fixOn n (acRound s as) s).1 x d ↔ naive s as c x d := by
    have e : (fixOn n (acRound s as) s).1 = (iter n (fun st => st.1 == st.2.1.n.toNat) fr a₀).2.1 := by
      rw [show fixOn n (acRound s as) s = (fixOnC n (acRoundC s as) s).1 from (fixOnC_fst n (acRoundC s as) s).symm]
      show (iterC (α := Nat × Rel V D × Nat) n _ _ _).1.2.1 = _
      rw [iterC_fst]
    obtain ⟨J, hJ, he, hst, hlt⟩ := iter_stop (fun st : Nat × Rel V D × Nat => st.1 == st.2.1.n.toNat) fr n a₀
    have hrun : ∀ i < J, (acRoundC s as (fr^[i] a₀).2.1).2 = true ∧
        (nubC (acRoundC s as (fr^[i] a₀).2.1).1).2 = true := fun i hi =>
      have h := iterC_run _ _ _ _ hbit i (by omega) fun i' hi' => hlt i' (by omega); Eq.mp (Bool.and_eq_true _ _) h
    have hsucc : ∀ k, fr^[k + 1] a₀ = fr (fr^[k] a₀) := fun _ => rfl
    have hY : ∀ k ≤ J, ∀ x d, rep (fr^[k] a₀).2.1 x d ↔ naive s as k x d := by
      intro k
      induction k with
      | zero => intro _; exact hs0
      | succ k ih =>
        intro hk x d
        rw [hsucc k]
        show rep (nubC (acRoundC s as (fr^[k] a₀).2.1).1).1 x d ↔ body s as (naive s as k) x d
        rw [rep_nubC _ (hrun k (by omega)).2]
        exact ((rep_foldlC _ _ (rep_naiveStepC _) as s true (hrun k (by omega)).1).2 x d).trans
          (body_congr s as (ih (by omega)) x d)
    rw [e, he]
    intro x d
    refine (hY J (Nat.le_refl _) x d).trans ?_
    rcases hst with hJn | hdone
    · exact naive_stable s as hcF J (by omega) x d
    · cases J with
      | zero => simp [a₀] at hdone; have h : (nubC s).1.n.toNat + 1 = (nubC s).1.n.toNat := hdone; omega
      | succ i =>
        have hY1 := hY (i + 1) (Nat.le_refl _)
        rw [hsucc i] at hdone hY1
        have heq : (fr^[i] a₀).2.1.n.toNat = (fr (fr^[i] a₀)).2.1.n.toNat := by simpa [fr] using hdone
        have hle : ∀ x d, rep (fr (fr^[i] a₀)).2.1 x d → rep (fr^[i] a₀).2.1 x d := fun x d h =>
          (hY i (by omega) x d).2 (naive_anti s as i x d ((hY1 x d).1 h))
        have hlt' := (count_lt (fr (fr^[i] a₀)).2.1 (fr^[i] a₀).2.1 (rowsInj_nubC _ (hrun i (by omega)).2) hle).2
        have hfix : ∀ x d, naive s as (i + 1) x d ↔ naive s as i x d := fun x d =>
          ⟨naive_anti s as i x d, fun h => Classical.byContradiction fun hn' => by
            have := hlt' ⟨x, d, (hY i (by omega) x d).2 h, fun h' => hn' ((hY1 x d).1 h')⟩
            omega⟩
        exact (hfix x d).trans (naive_fixed_eq s as hcF hfix x d)
  -- the delta run: `acFixC`'s rounds, the state `(X, Δ, round)`
  let fd : Rel V D × Rel V V × Nat → Rel V D × Rel V V × Nat := fun st =>
    ((acDeltaC as (st.1, st.2.1)).1.1, (acDeltaC as (st.1, st.2.1)).1.2, st.2.2 + 1)
  let b₀ : Rel V D × Rel V V × Nat := ((nubC s).1, U, 0)
  have hA : ∀ x d, rep (acFix s as U).1 x d ↔ naive s as c x d := by
    have e : (acFix s as U).1 = (iter ((nubC s).1.n.toNat + 1) (fun st => st.2.1.n == 0) fd b₀).1 := by
      show (iterC (α := Rel V D × Rel V V × Nat) _ _ _ _).1.1 = _
      rw [iterC_fst]
    obtain ⟨K, hK, he, hst, hlt⟩ :=
      iter_stop (fun st : Rel V D × Rel V V × Nat => st.2.1.n == 0) fd ((nubC s).1.n.toNat + 1) b₀
    have hrun : ∀ i < K, (acDeltaC as ((fd^[i] b₀).1, (fd^[i] b₀).2.1)).2 = true := fun i hi =>
      have h := iterC_run _ _ _ _ hdbit i (by omega) fun i' hi' => hlt i' (by omega); h
    have hZ : ∀ k ≤ K, AcInv s as (rep (fd^[k] b₀).1) (rep (fd^[k] b₀).2.1) ∧
        ∀ x d, rep (fd^[k] b₀).1 x d ↔ naive s as k x d := by
      intro k
      induction k with
      | zero => intro _; exact ⟨acInv_init s as _ U (rep_nubC s h0) hU hUA hsV, hs0⟩
      | succ k ih =>
        intro hk
        obtain ⟨hI, hk'⟩ := ih (by omega)
        obtain ⟨hr, hI'⟩ := acDelta_round hat s as _ _ hI (hrun k (by omega))
        show AcInv s as (rep (fd (fd^[k] b₀)).1) (rep (fd (fd^[k] b₀)).2.1) ∧ ∀ x d, rep (fd (fd^[k] b₀)).1 x d ↔ _
        exact ⟨hI', fun x d => (hr x d).trans (body_congr s as hk' x d)⟩
    rw [e, he]
    obtain ⟨hI, hK'⟩ := hZ K (Nat.le_refl _)
    intro x d
    refine (hK' x d).trans ?_
    rcases hst with hKf | hdone
    · exact naive_stable s as hcF K (by omega) x d
    · -- `Δ = 𝟘`: every pair of `X` is supported, so `X` is fixed
      have hz := (n_eq_zero_iff _).1 (by simpa using hdone)
      obtain ⟨-, hXs, hXv, hXn, hXo⟩ := hI
      have hfix : ∀ x d, naive s as (K + 1) x d ↔ naive s as K x d := fun x d => by
        refine (body_congr s as (fun x d => (hK' x d).symm) x d).trans ((?_ : _ ↔ _).trans (hK' x d))
        exact ⟨fun ⟨hs, hN⟩ => hXn x d hs hN, fun hx => ⟨hXs x d hx, fun a ha =>
          ⟨fun w hA => hXo a ha x d hx w (hz w w) hA, hXv a ha x d hx⟩⟩⟩
      exact naive_fixed_eq s as hcF hfix x d
  exact hom_ext fun x d => (hA x d).trans (hB x d).symm

#print axioms acFix_eq_fixOn

end LeetQ.Rel.AC3
