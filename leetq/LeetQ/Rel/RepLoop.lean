/-
  `loopOn` read back. `loopOn F P` runs rounds of `iter` on states `(c, ys)` per key: `(c, y :: ys)` to
  `(c', ys)` with `(c, y) F(D) c'`, `(c, [])` to `out`. Each round shortens every array by one and no array of
  `P` is longer than `P`'s payload, so the fuel `P`'s payload plus one always suffices: the result is the left
  fold of `F` along each array of `P`, from its seed.
-/
import LeetQ.Rel.RepFold

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF
open QLean.Dep

/-- `f^[j]`, `f` applied `j` times (core's `Nat.repeat`), as `RepFold`'s local notation. -/
local notation:max f "^[" n "]" => Nat.repeat f n

/-- **The states of a left fold, in `Set`**: `st i r` holds the states `(c, ys)` key `r` reaches after `i`
    rounds, each round taking `(c, y :: ys)` to `(c', ys)` by `F i` (`hst`, for the rounds below `M`). A state
    after `i ≤ M` rounds is a seed `(c₀, xs)` with `ys` the rest of `xs` after `i` elements and `c` the end of a
    chain `g` of `F`-steps along them. -/
theorem loop_closed {K X Y : Type} (F : Nat → X × Y → X → Prop) (st : Nat → K → X × List Y → Prop) (M : Nat)
    (hst : ∀ i, i < M → ∀ r c' ys, st (i + 1) r (c', ys) ↔ ∃ c y, st i r (c, y :: ys) ∧ F i (c, y) c') :
    ∀ i, i ≤ M → ∀ r c ys, st i r (c, ys) ↔ ∃ c₀ xs, st 0 r (c₀, xs) ∧ ∃ hi : i ≤ xs.length, ys = xs.drop i ∧
      ∃ g : Nat → X, g 0 = c₀ ∧ (∀ t (ht : t < i), F t (g t, xs[t]'(Nat.lt_of_lt_of_le ht hi)) (g (t + 1))) ∧
        c = g i := by
  intro i
  induction i with
  | zero =>
    intro _ r c ys
    refine ⟨fun h => ⟨c, ys, h, Nat.zero_le _, (List.drop_zero).symm, fun _ => c, rfl,
      fun t ht => absurd ht (Nat.not_lt_zero _), rfl⟩, ?_⟩
    rintro ⟨c₀, xs, h, -, hys, g, hg0, -, hc⟩
    rw [hc, hg0, hys, List.drop_zero]; exact h
  | succ i ih =>
    intro hM r c' ys
    rw [hst i (by omega)]
    constructor
    · rintro ⟨c, y, hs, hF⟩
      obtain ⟨c₀, xs, h0, hi, hys, g, hg0, hch, hc⟩ := (ih (by omega) r c (y :: ys)).1 hs
      have hl := congrArg List.length hys
      simp only [List.length_cons, List.length_drop] at hl
      have hi' : i + 1 ≤ xs.length := by omega
      have hd := List.drop_eq_getElem_cons (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi')
      rw [hd] at hys
      obtain ⟨hy, hys'⟩ := List.cons.inj hys
      refine ⟨c₀, xs, h0, hi', hys', fun t => if t = i + 1 then c' else g t, by simp [hg0], fun t ht => ?_, by simp⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · simp only [show t ≠ i + 1 by omega, show t + 1 ≠ i + 1 by omega, if_false]
        exact hch t ht
      · simp only [show t ≠ t + 1 by omega, if_true, if_false]
        rw [← hc, ← hy]; exact hF
    · rintro ⟨c₀, xs, h0, hi, hys, g, hg0, hch, hc⟩
      have hd := List.drop_eq_getElem_cons (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi)
      refine ⟨g i, xs[i]'(Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi),
        (ih (by omega) r _ _).2 ⟨c₀, xs, h0, by omega, by rw [hd, hys], g, hg0,
          fun t ht => hch t (by omega), rfl⟩, ?_⟩
      rw [hc]; exact hch i (Nat.lt_succ_self i)

/-- **A left fold's `out` at a stop**: the values `c` of the states `(c, [])` met before round `j` are the ends
    of the chains along whole seeds, when `j` is past every seed's length (`N < j`, seeds at most `N` long) or
    no state is left at `j`. -/
theorem loop_out {K X Y : Type} (F : Nat → X × Y → X → Prop) (st : Nat → K → X × List Y → Prop) (M : Nat)
    (hst : ∀ i, i < M → ∀ r c' ys, st (i + 1) r (c', ys) ↔ ∃ c y, st i r (c, y :: ys) ∧ F i (c, y) c')
    (N j : Nat) (hjM : j ≤ M) (hN : ∀ r s, st 0 r s → s.2.length ≤ N) (hj : N < j ∨ ∀ r s, ¬ st j r s) :
    ∀ r c, (∃ i < j, st i r (c, [])) ↔ ∃ c₀ xs, st 0 r (c₀, xs) ∧ ∃ g : Nat → X, g 0 = c₀ ∧
      (∀ t (ht : t < xs.length), F t (g t, xs[t]'ht) (g (t + 1))) ∧ c = g xs.length := by
  have cl := loop_closed F st M hst
  intro r c
  constructor
  · rintro ⟨i, hij, hs⟩
    obtain ⟨c₀, xs, h0, hi, hys, g, hg0, hch, hc⟩ := (cl i (by omega) r c []).1 hs
    have hl := congrArg List.length hys
    simp only [List.length_nil, List.length_drop] at hl
    obtain rfl : i = xs.length := by omega
    exact ⟨c₀, xs, h0, g, hg0, hch, hc⟩
  · rintro ⟨c₀, xs, h0, g, hg0, hch, hc⟩
    have hlj : xs.length < j := by
      rcases hj with hj | hj
      · exact Nat.lt_of_le_of_lt (hN r _ h0) hj
      · refine Nat.lt_of_not_le fun hle => hj r (g j, xs.drop j) ((cl j hjM r _ _).2
          ⟨c₀, xs, h0, hle, rfl, g, hg0, fun t ht => hch t (by omega), rfl⟩)
    exact ⟨xs.length, hlj, (cl _ (by omega) r c []).2
      ⟨c₀, xs, h0, Nat.le_refl _, List.drop_length.symm, g, hg0, hch, hc⟩⟩

/-- A row of an array side is no longer than the side's payload. -/
theorem arr_row_length {B : Obj} {n : USize} (x : Vals (.arr B) n) (i : Fin n.toNat) :
    (Vals.row x i).length ≤ x.1.toNat := by
  match x with
  | ⟨m, lo, hi, f⟩ =>
    exact Nat.le_trans (List.length_filterMap_le _ _) (Nat.le_of_eq (List.length_finRange ..))

/-- **`loopOn`, read back from its rounds**: `rep (loopOn F P) k c` holds when `k`'s seed `(c₀, xs)` in `P`
    folds to `c` along `xs`, step `t` by `Fr t`. The round `f` is bound by its defining equation (`hf`, its
    values `D`, `u`, `p` with theirs); `hS`, `hO` read each round's states and `out` back (internal: the
    headline discharges them from the primitives). -/
theorem loopOn_rounds {K X Y : Obj} (F : Rel (.prod X Y) (.prod X Y) → Rel (.prod X Y) X)
    (P : Rel K (.prod X (.arr Y)))
    (f : Rel K X × Rel K (.prod X (.arr Y)) → Rel K X × Rel K (.prod X (.arr Y)))
    (hf : ∀ out St D u p, D = ran St → u = outr D ≫ uncons (ran (outr D)).val → p = pair (outl D) (outl u) →
      f (out, St) = (out ∪ St ≫ outl (antiJoin D (dom u)), Rel.nub (St ≫ pair (p ≫ F (ran p)) (outr u))))
    (Fr : Nat → X.El × Y.El → X.El → Prop)
    (hS : ∀ i, i ≤ (Rel.val P).2.1.toNat → ∀ k c' ys, rep (f^[i + 1] (Alg.zero, P)).2 k (c', ys) ↔
      ∃ c y, rep (f^[i] (Alg.zero, P)).2 k (c, y :: ys) ∧ Fr i (c, y) c')
    (hO : ∀ i, i ≤ (Rel.val P).2.1.toNat → ∀ k c, rep (f^[i + 1] (Alg.zero, P)).1 k c ↔
      rep (f^[i] (Alg.zero, P)).1 k c ∨ rep (f^[i] (Alg.zero, P)).2 k (c, [])) :
    ∀ k c, rep (loopOn F P) k c ↔ ∃ c₀ xs, rep P k (c₀, xs) ∧ ∃ g : Nat → X.El, g 0 = c₀ ∧
      (∀ t (ht : t < xs.length), Fr t (g t, xs[t]'ht) (g (t + 1))) ∧ c = g xs.length := by
  obtain ⟨j, hj, he, hs⟩ := iter_stop (fun s : Rel K X × Rel K (.prod X (.arr Y)) => s.2.n == 0) f
    ((Rel.val P).2.1.toNat + 1) (Alg.zero, P)
  have hl : loopOn F P = (f^[j] (Alg.zero, P)).1 := by
    rw [← he]
    refine congrArg (fun g : Rel K X × Rel K (.prod X (.arr Y)) → Rel K X × Rel K (.prod X (.arr Y)) =>
      (iter ((Rel.val P).2.1.toNat + 1) (fun s => s.2.n == 0) g (Alg.zero, P)).1) (funext fun st => ?_)
    obtain ⟨o, S⟩ := st
    rw [hf o S _ _ _ rfl rfl rfl]
  -- `out` after `j` rounds: the values of the empty states met before
  have hout : ∀ j, j ≤ (Rel.val P).2.1.toNat + 1 → ∀ k c, rep (f^[j] (Alg.zero, P)).1 k c ↔
      ∃ i < j, rep (f^[i] (Alg.zero, P)).2 k (c, []) := by
    intro j
    induction j with
    | zero => intro _ k c; exact ⟨fun ⟨i, _⟩ => i.elim0, fun ⟨_, hi, _⟩ => absurd hi (Nat.not_lt_zero _)⟩
    | succ j ih =>
      intro hjN k c
      rw [show f^[j + 1] (Alg.zero, P) = f (f^[j] (Alg.zero, P)) from rfl] at *
      rw [show f (f^[j] (Alg.zero, P)) = f^[j + 1] (Alg.zero, P) from rfl, hO j (by omega), ih (by omega)]
      constructor
      · rintro (⟨i, hi, h⟩ | h)
        · exact ⟨i, by omega, h⟩
        · exact ⟨j, by omega, h⟩
      · rintro ⟨i, hi, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact Or.inl ⟨i, hi, h⟩
        · exact Or.inr h
  have hN : ∀ k (s : X.El × List Y.El), rep (f^[0] (Alg.zero, P)).2 k s → s.2.length ≤ (Rel.val P).2.1.toNat := by
    rintro k s ⟨i, -, hi⟩
    rw [← hi]; exact arr_row_length (Rel.val P).2 i
  have hstop : (Rel.val P).2.1.toNat < j ∨
      ∀ k (s : X.El × List Y.El), ¬ rep (f^[j] (Alg.zero, P)).2 k s := by
    rcases hs with hs | hs
    · exact Or.inl (by omega)
    · refine Or.inr fun k s h => ?_
      obtain ⟨i, -⟩ := h
      have h0 : (f^[j] (Alg.zero, P)).2.n = 0 := beq_iff_eq.1 hs
      have h1 : (f^[j] (Alg.zero, P)).2.n.toNat = 0 := by rw [h0]; rfl
      exact Nat.not_lt_zero _ (Nat.lt_of_lt_of_eq i.2 h1)
  intro k c
  rw [hl, hout j hj]
  exact loop_out Fr (fun i k s => rep (f^[i] (Alg.zero, P)).2 k s) ((Rel.val P).2.1.toNat + 1)
    (fun i hi => hS i (by omega)) (Rel.val P).2.1.toNat j hj hN hstop k c

section Round

open Freyd Freyd.Alg Freyd.Alg.RelSet

/-- **One round of `loopOn`, read back from its primitives' read-backs**: the new states `T.nub` are the states
    `(c, y :: ys)` stepped to `(c', ys)` by `G = F(ran p)`, and the new `out ∪ O` adds the values of the states
    whose array is empty. Each hypothesis is one primitive's read-back at this round's values (`rep_ran` at `St`
    and at `outr D`, `rep_uncons`, `rep_comp`, `rep_pair`, `rep_nub`, `rep_dom`, `rep_antiJoin`,
    `rep_union_full`); the values `D`, `u`, `p`, `Q`, `R`, `T`, `A`, `O` are whatever the hypotheses say. -/
theorem loop_round_set {K X Y : Obj} (out : Rel K X) (St : Rel K (.prod X (.arr Y)))
    (D : Rel (.prod X (.arr Y)) (.prod X (.arr Y))) (u : Rel (.prod X (.arr Y)) (.prod Y (.arr Y)))
    (p : Rel (.prod X (.arr Y)) (.prod X Y)) (G : Rel (.prod X Y) X) (Q : Rel (.prod X (.arr Y)) X)
    (R : Rel (.prod X (.arr Y)) (.prod X (.arr Y))) (T : Rel K (.prod X (.arr Y)))
    (A : Rel (.prod X (.arr Y)) (.prod X (.arr Y))) (O : Rel K X)
    (hD : rep D = corefl (A := (⟨(Obj.prod X (.arr Y)).El⟩ : RelSet.{0})) fun s => ∃ k, rep St k s)
    (hW : rep (ran (outr D)) = corefl (A := (⟨(Obj.arr Y).El⟩ : RelSet.{0})) fun ys => ∃ s, rep (outr D) s ys)
    (hUn : ∀ (xs : List Y.El) b bs, rep (uncons (ran (outr D)).val) xs (b, bs) ↔
      (∃ j, (ran (outr D)).val.row j = xs) ∧ xs = b :: bs)
    (hu : rep u = rep (outr D) ≫ rep (uncons (ran (outr D)).val))
    (hp : rep p = rpair (rep (outl D)) (rep (outl u))) (hQ : rep Q = rep p ≫ rep G)
    (hR : rep R = rpair (rep Q) (rep (outr u))) (hT : rep T = rep St ≫ rep R) (hN : rep (Rel.nub T) = rep T)
    (hdu : rep (dom u) = corefl (A := (⟨(Obj.prod X (.arr Y)).El⟩ : RelSet.{0})) fun s => ∃ b, rep u s b)
    (hA : rep A = rep D ≫ corefl (A := (⟨(Obj.prod X (.arr Y)).El⟩ : RelSet.{0})) fun s => ¬ ∃ y, rep (dom u) y s)
    (hO : rep O = rep St ≫ rep (outl A)) (hU : rep (out ∪ O) = rep out ∪ rep O) :
    (∀ k (c' : X.El) (ys : List Y.El), rep (Rel.nub T) k (c', ys) ↔
      ∃ c y, rep St k (c, y :: ys) ∧ rep G (c, y) c') ∧
    ∀ k (c : X.El), rep (out ∪ O) k c ↔ rep out k c ∨ rep St k (c, []) := by
  have eD : ∀ s s' : X.El × List Y.El, rep D s s' ↔ s = s' ∧ ∃ k, rep St k s := by
    intro s s'; rw [hD]; exact Iff.rfl
  have eOD : ∀ (s : X.El × List Y.El) ys, rep (outr D) s ys ↔ (∃ k, rep St k s) ∧ ys = s.2 := by
    intro s ys; rw [rep_outr, comp_apply]
    constructor
    · rintro ⟨s', h, e⟩; obtain ⟨rfl, hk⟩ := (eD s s').1 h; exact ⟨hk, e⟩
    · rintro ⟨hk, e⟩; exact ⟨s, (eD s s).2 ⟨rfl, hk⟩, e⟩
  have eu : ∀ (s : X.El × List Y.El) b bs, rep u s (b, bs) ↔ (∃ k, rep St k s) ∧ s.2 = b :: bs := by
    intro s b bs; rw [hu, comp_apply]
    constructor
    · rintro ⟨ys, h1, h2⟩; obtain ⟨hk, rfl⟩ := (eOD s ys).1 h1; exact ⟨hk, ((hUn _ b bs).1 h2).2⟩
    · rintro ⟨hk, e⟩
      have hw : rep (ran (outr D)) s.2 s.2 := by rw [hW]; exact ⟨rfl, s, (eOD s s.2).2 ⟨hk, rfl⟩⟩
      obtain ⟨j, -, hj⟩ := hw
      exact ⟨s.2, (eOD s s.2).2 ⟨hk, rfl⟩, (hUn _ b bs).2 ⟨⟨j, hj⟩, e⟩⟩
  have eLD : ∀ (s : X.El × List Y.El) c, rep (outl D) s c ↔ (∃ k, rep St k s) ∧ c = s.1 := by
    intro s c; rw [rep_outl, comp_apply]
    constructor
    · rintro ⟨s', h, e⟩; obtain ⟨rfl, hk⟩ := (eD s s').1 h; exact ⟨hk, e⟩
    · rintro ⟨hk, e⟩; exact ⟨s, (eD s s).2 ⟨rfl, hk⟩, e⟩
  have eLu : ∀ (s : X.El × List Y.El) y, rep (outl u) s y ↔ (∃ k, rep St k s) ∧ ∃ bs, s.2 = y :: bs := by
    intro s y; rw [rep_outl, comp_apply]
    constructor
    · rintro ⟨⟨b, bs⟩, h, e⟩; obtain ⟨hk, h2⟩ := (eu s b bs).1 h; exact ⟨hk, bs, (show y = b from e) ▸ h2⟩
    · rintro ⟨hk, bs, e⟩; exact ⟨(y, bs), (eu s y bs).2 ⟨hk, e⟩, rfl⟩
  have eRu : ∀ (s : X.El × List Y.El) bs, rep (outr u) s bs ↔ (∃ k, rep St k s) ∧ ∃ y, s.2 = y :: bs := by
    intro s bs; rw [rep_outr, comp_apply]
    constructor
    · rintro ⟨⟨b, bs'⟩, h, e⟩; obtain ⟨hk, h2⟩ := (eu s b bs').1 h; exact ⟨hk, b, (show bs = bs' from e) ▸ h2⟩
    · rintro ⟨hk, y, e⟩; exact ⟨(y, bs), (eu s y bs).2 ⟨hk, e⟩, rfl⟩
  refine ⟨fun k c' ys => ?_, fun k c => ?_⟩
  · rw [hN, hT, comp_apply]
    constructor
    · rintro ⟨s, hs, hr⟩
      rw [hR] at hr
      obtain ⟨hq, hru⟩ := hr
      rw [hQ, comp_apply] at hq
      obtain ⟨⟨c, y⟩, hpp, hg⟩ := hq
      rw [hp] at hpp
      obtain ⟨h1, h2⟩ := hpp
      obtain ⟨-, rfl⟩ := (eLD s _).1 h1
      obtain ⟨-, bs, e1⟩ := (eLu s _).1 h2
      obtain ⟨-, y', e2⟩ := (eRu s _).1 hru
      obtain ⟨rfl, rfl⟩ := List.cons.inj (e1.symm.trans e2)
      refine ⟨s.1, y, ?_, hg⟩
      rw [← e1]; exact hs
    · rintro ⟨c, y, hs, hg⟩
      have hk : ∃ k, rep St k (c, y :: ys) := ⟨k, hs⟩
      refine ⟨(c, y :: ys), hs, ?_⟩
      rw [hR]
      refine ⟨?_, (eRu _ _).2 ⟨hk, y, rfl⟩⟩
      rw [hQ, comp_apply]
      refine ⟨(c, y), ?_, hg⟩
      rw [hp]
      exact ⟨(eLD _ _).2 ⟨hk, rfl⟩, (eLu _ _).2 ⟨hk, ys, rfl⟩⟩
  · rw [hU, union_apply, hO, comp_apply]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨s, hs, ho⟩
      rw [rep_outl, comp_apply] at ho
      obtain ⟨s', ha, e⟩ := ho
      rw [hA, comp_apply] at ha
      obtain ⟨s'', hd, rfl, hn⟩ := ha
      obtain ⟨rfl, hk⟩ := (eD s s'').1 hd
      have h0 : s.2 = [] := by
        cases h : s.2 with
        | nil => rfl
        | cons b bs => exact absurd ⟨s, by rw [hdu]; exact ⟨rfl, (b, bs), (eu s b bs).2 ⟨hk, h⟩⟩⟩ hn
      have e' : c = s.1 := e
      rw [e', ← h0]; exact hs
    · intro hs
      have hk : ∃ k, rep St k (c, []) := ⟨k, hs⟩
      refine ⟨(c, []), hs, ?_⟩
      rw [rep_outl, comp_apply]
      refine ⟨(c, []), ?_, rfl⟩
      rw [hA, comp_apply]
      refine ⟨(c, []), (eD _ _).2 ⟨rfl, hk⟩, rfl, ?_⟩
      rintro ⟨y, hy⟩
      rw [hdu] at hy
      obtain ⟨rfl, ⟨b, bs⟩, hb⟩ := hy
      exact List.cons_ne_nil b bs ((eu _ b bs).1 hb).2.symm

end Round

end LeetQ.Rel.Rep
