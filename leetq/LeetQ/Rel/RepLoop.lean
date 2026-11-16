/-
  `loopOn` read back. `loopOn F P` runs rounds of `iter` on states `(c, ys)` per key: `(c, y :: ys)` to
  `(c', ys)` with `(c, y) F(D) c'`, `(c, [])` to `out`. Each round shortens every array by one and no array of
  `P` is longer than `P`'s payload, so the fuel `P`'s payload plus one always suffices: the result is the left
  fold of `F` along each array of `P`, from its seed.
-/
import LeetQ.Rel.RepFold
import LeetQ.Rel.RepList

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF
open QLean.Dep

open FoldN OpsN

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
    -- each round `iter` runs: below the fuel, `done` failing at every iterate up to it
    (hS : ∀ i, i ≤ (Rel.val P).2.1.toNat → (∀ i' ≤ i, ((f^[i'] (Alg.zero, P)).2.n == 0) = false) →
      ∀ k c' ys, rep (f^[i + 1] (Alg.zero, P)).2 k (c', ys) ↔
      ∃ c y, rep (f^[i] (Alg.zero, P)).2 k (c, y :: ys) ∧ Fr i (c, y) c')
    (hO : ∀ i, i ≤ (Rel.val P).2.1.toNat → (∀ i' ≤ i, ((f^[i'] (Alg.zero, P)).2.n == 0) = false) →
      ∀ k c, rep (f^[i + 1] (Alg.zero, P)).1 k c ↔
      rep (f^[i] (Alg.zero, P)).1 k c ∨ rep (f^[i] (Alg.zero, P)).2 k (c, [])) :
    ∀ k c, rep (loopOn F P) k c ↔ ∃ c₀ xs, rep P k (c₀, xs) ∧ ∃ g : Nat → X.El, g 0 = c₀ ∧
      (∀ t (ht : t < xs.length), Fr t (g t, xs[t]'ht) (g (t + 1))) ∧ c = g xs.length := by
  obtain ⟨j, hj, he, hs, hm⟩ := iter_stop (fun s : Rel K X × Rel K (.prod X (.arr Y)) => s.2.n == 0) f
    ((Rel.val P).2.1.toNat + 1) (Alg.zero, P)
  have hfe : f = fun st => (loopRound (fun D => (F D, true)) st).1 := funext fun ⟨o, S⟩ => by
    rw [hf o S _ _ _ rfl rfl rfl, ← nubC_fst]; rfl
  have hl : loopOn F P = (f^[j] (Alg.zero, P)).1 := by
    rw [← he, hfe]
    exact congrArg Prod.fst (iterC_fst _ _ (loopRound (fun D => (F D, true))) (Alg.zero, P))
  -- `out` after `j` rounds: the values of the empty states met before
  have hout : ∀ j', j' ≤ j → ∀ k c, rep (f^[j'] (Alg.zero, P)).1 k c ↔
      ∃ i < j', rep (f^[i] (Alg.zero, P)).2 k (c, []) := by
    intro j'
    induction j' with
    | zero => intro _ k c; exact ⟨fun ⟨i, _⟩ => i.elim0, fun ⟨_, hi, _⟩ => absurd hi (Nat.not_lt_zero _)⟩
    | succ j' ih =>
      intro hjN k c
      rw [show f^[j' + 1] (Alg.zero, P) = f (f^[j'] (Alg.zero, P)) from rfl] at *
      rw [show f (f^[j'] (Alg.zero, P)) = f^[j' + 1] (Alg.zero, P) from rfl,
        hO j' (by omega) (fun i' hi' => hm i' (by omega)), ih (by omega)]
      constructor
      · rintro (⟨i, hi, h⟩ | h)
        · exact ⟨i, by omega, h⟩
        · exact ⟨j', by omega, h⟩
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
  rw [hl, hout j (Nat.le_refl _)]
  exact loop_out Fr (fun i k s => rep (f^[i] (Alg.zero, P)).2 k s) j
    (fun i hi => hS i (by omega) (fun i' hi' => hm i' (by omega))) (Rel.val P).2.1.toNat j (Nat.le_refl _) hN
    hstop k c

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
    (hp : rep p = rpair (rep (outl D)) (rep (outl u)))
    (Gr : X.El × Y.El → X.El → Prop) (hG : ∀ cy c', (∃ s, rep p s cy) → (rep G cy c' ↔ Gr cy c'))
    (hQ : rep Q = rep p ≫ rep G)
    (hR : rep R = rpair (rep Q) (rep (outr u))) (hT : rep T = rep St ≫ rep R) (hN : rep (Rel.nub T) = rep T)
    (hdu : rep (dom u) = corefl (A := (⟨(Obj.prod X (.arr Y)).El⟩ : RelSet.{0})) fun s => ∃ b, rep u s b)
    (hA : rep A = rep D ≫ corefl (A := (⟨(Obj.prod X (.arr Y)).El⟩ : RelSet.{0})) fun s => ¬ ∃ y, rep (dom u) y s)
    (hO : rep O = rep St ≫ rep (outl A)) (hU : rep (out ∪ O) = rep out ∪ rep O) :
    (∀ k (c' : X.El) (ys : List Y.El), rep (Rel.nub T) k (c', ys) ↔
      ∃ c y, rep St k (c, y :: ys) ∧ Gr (c, y) c') ∧
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
      replace hg := (hG _ _ ⟨s, hpp⟩).1 hg
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
      have hpp : rep p (c, y :: ys) (c, y) := by rw [hp]; exact ⟨(eLD _ _).2 ⟨hk, rfl⟩, (eLu _ _).2 ⟨hk, ys, rfl⟩⟩
      refine ⟨(c, y :: ys), hs, ?_⟩
      rw [hR]
      refine ⟨?_, (eRu _ _).2 ⟨hk, y, rfl⟩⟩
      rw [hQ, comp_apply]
      exact ⟨(c, y), hpp, (hG _ _ ⟨_, hpp⟩).2 hg⟩
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

/-! ## The primitives' hypotheses at one round -/

/-! Each primitive's hypotheses as one bundle, over `FoldN`'s `mpairs` and `OpsN`'s `nubI`: `open FoldN OpsN Prim` in every
    file that reads back a composite of these primitives. -/
namespace Prim

-- `rep_comp`'s hypotheses at `R ≫ S`, `B` the middle object, the codes `jc` bound by their equation
set_option hygiene false in
scoped notation "cmpOK(" B ", " R ", " S ")" =>
  (Obj.CodesFit B (#v[⟨Rel.n R, Rel.val R⟩, ⟨Rel.n S, Rel.key S⟩] : Vector (Part B) 2) ∧
    ∀ jc : Vector Code 2, jc = Obj.codes B (#v[⟨Rel.n R, Rel.val R⟩, ⟨Rel.n S, Rel.key S⟩] : Vector (Part B) 2) →
      (Rel.n S).toNat < 2 ^ 63 ∧ (Rel.n R).toNat * (Rel.n S).toNat < min (2 ^ 63) USize.size ∧
      Vals.PickFits _ (Rel.key R) ((mpairs(jc, R, S)).map Prod.fst) ∧
      Vals.PickFits _ (Rel.val S) ((mpairs(jc, R, S)).map Prod.snd))
-- `rep_pair`'s hypotheses at `⟨R, S⟩`, `A` the keys' object, the codes `kc` bound by their equation
set_option hygiene false in
scoped notation "pairOK(" A ", " R ", " S ")" =>
  (Obj.CodesFit A (#v[⟨Rel.n R, Rel.key R⟩, ⟨Rel.n S, Rel.key S⟩] : Vector (Part A) 2) ∧
    ∀ kc : Vector Code 2, kc = Obj.codes A (#v[⟨Rel.n R, Rel.key R⟩, ⟨Rel.n S, Rel.key S⟩] : Vector (Part A) 2) →
      (Rel.n S).toNat < 2 ^ 63 ∧ (Rel.n R).toNat * (Rel.n S).toNat < min (2 ^ 63) USize.size ∧
      Vals.PickFits A (Rel.key R) ((mpairs(kc, R, S)).map Prod.fst) ∧
      Vals.PickFits _ (Rel.val R) ((mpairs(kc, R, S)).map Prod.fst) ∧
      Vals.PickFits _ (Rel.val S) ((mpairs(kc, R, S)).map Prod.snd))
-- `rep_ran`'s (`x` the values) or `rep_dom`'s (`x` the keys) hypotheses on the one-part code of `x`
set_option hygiene false in
scoped notation "oneFit(" B ", " n ", " x ")" =>
  (Obj.CodesFit B (#v[⟨n, x⟩] : Vector (Part B) 1) ∧ Vals.PickFits B x (List.range (n).toNat))
-- `rep_antiJoin`'s hypotheses at `antiJoin R C`
set_option hygiene false in
scoped notation "ajOK(" B ", " R ", " C ")" =>
  (Obj.CodesFit B (#v[⟨Rel.n R, Rel.val R⟩, ⟨Rel.n C, Rel.val C⟩] : Vector (Part B) 2) ∧
    (Vals.PickFits _ (Rel.key R) (List.range (Rel.n R).toNat) ∧ Vals.PickFits B (Rel.val R) (List.range (Rel.n R).toNat)))
-- `rep_uncons`'s hypotheses at the arrays `Rel.val W`, its intermediates `ib`, `lb`, `Tv` bound by their equations
set_option hygiene false in
scoped notation "uncOK(" Y ", " W ")" =>
  (∀ ib : ByteArray, ib = whereBits (Rel.n W) (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf (Rel.val W)).2 (one 0) (Rel.n W)) →
    ∀ lb : ByteArray, lb = gather 8 (slicesOf (Rel.val W)).1 ib →
    ∀ Tv : Vals (.arr Y) (len ib).toUSize, Tv = ⟨(Rel.val W).1, valCol Ew.add Ew.va lb (one 1),
        valCol Ew.add Ew.vv lb (gather 8 (slicesOf (Rel.val W)).2 ib), (Rel.val W).2.2.2⟩ →
      Vals.PickFits (.arr Y) (Rel.val W)
          ((List.range (len ib)).map fun q => (Column.bitsAt ib (q * 8) 8).toNat))
-- `rep_diff`'s hypotheses at `R \ S`, `A`, `B` the key and value objects, its codes `pc` bound
set_option hygiene false in
scoped notation "diffOK(" A ", " B ", " R ", " S ")" =>
  (∀ pc : Vector Code 2, pc = pairs #v[R, S] →
    codesOK(pc, (#v[⟨Rel.n R, (Rel.key R, Rel.val R)⟩, ⟨Rel.n S, (Rel.key S, Rel.val S)⟩] :
      Vector (Part (.prod A B)) 2)) ∧
    (Vals.PickFits A (Rel.key R) (List.range (Rel.n R).toNat) ∧ Vals.PickFits B (Rel.val R) (List.range (Rel.n R).toNat)))

end Prim

open Prim

open Freyd Freyd.Alg Freyd.Alg.RelSet

set_option hygiene false in
/-- `P`'s rows are pairwise distinct: two rows holding one pair are one row (`nub_rows_inj`'s conclusion). -/
scoped notation "rowsInj(" P ")" => ∀ {t t' : Fin (Rel.n P).toNat}, (Rel.key P).row t = (Rel.key P).row t' →
  (Rel.val P).row t = (Rel.val P).row t' → t = t'

/-- **Pigeonhole on `Nat`**: a list without repeats of numbers below `k` is at most `k` long, and when exactly `k`
    long it holds every number below `k` (`List.erase` of `k` at each step). -/
theorem nodup_below {k : Nat} : ∀ l : List Nat, l.Nodup → (∀ x ∈ l, x < k) →
    l.length ≤ k ∧ (l.length = k → ∀ y < k, y ∈ l) := by
  induction k with
  | zero =>
    intro l _ hl
    cases l with
    | nil => exact ⟨Nat.le_refl _, fun _ y hy => absurd hy (Nat.not_lt_zero _)⟩
    | cons x _ => exact absurd (hl x (by simp)) (Nat.not_lt_zero _)
  | succ k ih =>
    intro l hn hl
    obtain ⟨h1, h2⟩ := ih (l.erase k) (hn.erase k) fun x hx => by
      obtain ⟨hne, hx⟩ := hn.mem_erase_iff.1 hx; have := hl x hx; omega
    by_cases hk : k ∈ l
    · have e := List.length_erase_of_mem hk; have := List.length_pos_of_mem hk
      refine ⟨by omega, fun h y hy => ?_⟩
      rcases Nat.lt_or_ge y k with hy' | hy'
      · exact List.mem_of_mem_erase (h2 (by omega) y hy')
      · rw [show y = k by omega]; exact hk
    · rw [List.erase_of_not_mem hk] at h1; exact ⟨by omega, fun h => by omega⟩

/-- **Distinct rows count the pairs**: a relation `P` with distinct rows below `Q` has at most `Q`'s rows, and at
    least as many only when `Q` is below it too — each row of `P` sent to a row of `Q` holding its pair is a
    pigeonhole map (`nodup_below`). -/
theorem rows_le_of_inj (P Q : Rel A B) (hP : rowsInj(P)) (hle : rep P ⊑ rep Q) :
    P.n.toNat ≤ Q.n.toNat ∧ (Q.n.toNat ≤ P.n.toNat → rep Q ⊑ rep P) := by
  have hs : ∀ t : Fin P.n.toNat, ∃ s : Fin Q.n.toNat, Q.key.row s = P.key.row t ∧ Q.val.row s = P.val.row t :=
    fun t => le_iff.1 hle _ _ ⟨t, rfl, rfl⟩
  let σ : Nat → Nat := fun i => if h : i < P.n.toNat then (Classical.choose (hs ⟨i, h⟩)).1 else 0
  have hσ : ∀ i (h : i < P.n.toNat), ∃ s : Fin Q.n.toNat,
      σ i = s.1 ∧ Q.key.row s = P.key.row ⟨i, h⟩ ∧ Q.val.row s = P.val.row ⟨i, h⟩ :=
    fun i h => ⟨_, dif_pos h, Classical.choose_spec (hs ⟨i, h⟩)⟩
  have hn : ((List.range P.n.toNat).map σ).Nodup := by
    refine List.pairwise_map.2 (List.nodup_range.imp_of_mem fun ha hb hab e => hab ?_)
    obtain ⟨s, es, k1, v1⟩ := hσ _ (List.mem_range.1 ha)
    obtain ⟨s', es', k2, v2⟩ := hσ _ (List.mem_range.1 hb)
    have : s = s' := Fin.ext (es.symm.trans (e.trans es'))
    subst this
    exact congrArg Fin.val (hP (k1.symm.trans k2) (v1.symm.trans v2))
  obtain ⟨h1, h2⟩ := nodup_below (k := Q.n.toNat) _ hn fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    obtain ⟨s, e, -⟩ := hσ i (List.mem_range.1 hi); rw [e]; exact s.2
  simp only [List.length_map, List.length_range] at h1 h2
  refine ⟨h1, fun h => le_iff.2 fun a b ⟨s, ha, hb⟩ => ?_⟩
  obtain ⟨i, hi, e⟩ := List.mem_map.1 (h2 (by omega) s.1 s.2)
  obtain ⟨s', es', k1, v1⟩ := hσ i (List.mem_range.1 hi)
  have : s' = s := Fin.ext (es'.symm.trans e)
  subst this
  exact ⟨_, k1.symm.trans ha, v1.symm.trans hb⟩

/-- **`fixOn`'s state after round `i`**: the count of round `i - 1`'s relation, round `i`'s, and `i`. -/
theorem fixOn_iterate {A B : Obj} (φ : Rel A B → Rel A B) (X₀ : Rel A B) : ∀ i,
    (fun s : Nat × Rel A B × Nat => (s.2.1.n.toNat, (φ s.2.1).nub, s.2.2 + 1))^[i + 1] (X₀.nub.n.toNat + 1, X₀.nub, 0) =
      (((fun X => (φ X).nub)^[i] X₀.nub).n.toNat, (fun X => (φ X).nub)^[i + 1] X₀.nub, i + 1)
  | 0 => rfl
  | i + 1 => congrArg (fun s : Nat × Rel A B × Nat => (s.2.1.n.toNat, (φ s.2.1).nub, s.2.2 + 1)) (fixOn_iterate φ X₀ i)

/-- **`fixOn`, read back**: with `st i` the `i`-th round's state `nub(φ(…nub(X₀)))`, `fixOn n φ X₀` stops at a round
    `j ≤ n`, answers it, and denotes `Φ^[j](rep X₀)`, `Φ` what one round does to the denotation; below the fuel `j`
    is a fixed point of `Φ`; the answer is below every pre-fixed point `Y` of `Φ` above `rep X₀` (Kleene's
    iterates); and the loop stops below the fuel once `n` exceeds by two the rows of a relation `U` above every
    iterate. The iterates are a chain (`Φ` monotonic, `rep X₀` below or above `Φ(rep X₀)`), so an equal row count of
    two consecutive rounds, rows distinct (`hinj`), is an equal relation and a different one a strictly growing
    (shrinking) count (`rows_le_of_inj`). Kept: `h₀`, `hφ`, the step's spec with `rep_nub`'s premises at each round
    the loop ran (their codes grow with the rounds), and `hinj`, the distinct rows of each round's `nub`
    (`nub_rows_inj` under the same premises). -/
theorem rep_fixOn {A B : Obj} (n : Nat) (φ : Rel A B → Rel A B) (X₀ : Rel A B)
    (Φ : type_of% (rep X₀) → type_of% (rep X₀)) (h₀ : rep X₀.nub = rep X₀)
    (hφ : ∀ i < n, (∀ k < i, ((fun X => (φ X).nub)^[k] X₀.nub).n.toNat ≠
        ((fun X => (φ X).nub)^[k + 1] X₀.nub).n.toNat) →
      rep (φ ((fun X => (φ X).nub)^[i] X₀.nub)).nub = Φ (rep ((fun X => (φ X).nub)^[i] X₀.nub)))
    (hinj : ∀ i ≤ n, (∀ k, k + 1 < i → ((fun X => (φ X).nub)^[k] X₀.nub).n.toNat ≠
        ((fun X => (φ X).nub)^[k + 1] X₀.nub).n.toNat) → rowsInj((fun X => (φ X).nub)^[i] X₀.nub))
    (hm : ∀ x y : type_of% (rep X₀), x ⊑ y → Φ x ⊑ Φ y) (hch : rep X₀ ⊑ Φ (rep X₀) ∨ Φ (rep X₀) ⊑ rep X₀) :
    ∃ j ≤ n, (fixOn n φ X₀).2 = j ∧ rep (fixOn n φ X₀).1 = Φ^[j] (rep X₀) ∧
      (j < n → Φ (rep (fixOn n φ X₀).1) = rep (fixOn n φ X₀).1) ∧
      (∀ Y, rep X₀ ⊑ Y → Φ Y ⊑ Y → rep (fixOn n φ X₀).1 ⊑ Y) ∧
      (∀ U : Rel A B, (∀ i, Φ^[i] (rep X₀) ⊑ rep U) → U.n.toNat + 1 < n → j < n) := by
  let g : Rel A B → Rel A B := fun X => (φ X).nub
  let f : Nat × Rel A B × Nat → Nat × Rel A B × Nat := fun s => (s.2.1.n.toNat, (φ s.2.1).nub, s.2.2 + 1)
  let done : Nat × Rel A B × Nat → Bool := fun s => s.1 == s.2.1.n.toNat
  let s₀ : Nat × Rel A B × Nat := (X₀.nub.n.toNat + 1, X₀.nub, 0)
  have hs : ∀ i, f^[i + 1] s₀ = ((g^[i] X₀.nub).n.toNat, g^[i + 1] X₀.nub, i + 1) := fixOn_iterate φ X₀
  have hd : ∀ k, done (f^[k + 1] s₀) = ((g^[k] X₀.nub).n.toNat == (g^[k + 1] X₀.nub).n.toNat) := fun k => by
    rw [hs k]
  have hfix : fixOn n φ X₀ = ((iter n done f s₀).2.1, (iter n done f s₀).2.2) := rfl
  obtain ⟨j, hjn, he, hstop, hlt⟩ := iter_stop done f n s₀
  -- the rounds the loop ran changed the count, and are read back
  have hne : ∀ k, k + 1 < j → (g^[k] X₀.nub).n.toNat ≠ (g^[k + 1] X₀.nub).n.toNat := fun k hk h => by
    have := hlt (k + 1) hk
    rw [hd k] at this
    exact (by simpa using this : (g^[k] X₀.nub).n.toNat ≠ (g^[k + 1] X₀.nub).n.toNat) h
  have hg : ∀ i < j, rep (g^[i + 1] X₀.nub) = Φ (rep (g^[i] X₀.nub)) := fun i hi =>
    hφ i (by omega) fun k hk => hne k (by omega)
  have hr : ∀ i ≤ j, rep (g^[i] X₀.nub) = Φ^[i] (rep X₀) := by
    intro i
    induction i with
    | zero => intro _; exact h₀
    | succ i ih => intro hi; rw [hg i (by omega), ih (by omega)]; rfl
  have hu : ∀ i ≤ j, rowsInj(g^[i] X₀.nub) := fun i hi => hinj i (by omega) fun k hk => hne k (by omega)
  -- the denotations form a chain, up or down
  have hc : ∀ i, (rep X₀ ⊑ Φ (rep X₀) → Φ^[i] (rep X₀) ⊑ Φ^[i + 1] (rep X₀)) ∧
      (Φ (rep X₀) ⊑ rep X₀ → Φ^[i + 1] (rep X₀) ⊑ Φ^[i] (rep X₀)) := fun i => by
    induction i with
    | zero => exact ⟨id, id⟩
    | succ i ih => exact ⟨fun h => hm _ _ (ih.1 h), fun h => hm _ _ (ih.2 h)⟩
  have hup : ∀ k, k + 1 ≤ j → rep X₀ ⊑ Φ (rep X₀) → rep (g^[k] X₀.nub) ⊑ rep (g^[k + 1] X₀.nub) :=
    fun k hk h => by rw [hr k (by omega), hr (k + 1) hk]; exact (hc k).1 h
  have hdn : ∀ k, k + 1 ≤ j → Φ (rep X₀) ⊑ rep X₀ → rep (g^[k + 1] X₀.nub) ⊑ rep (g^[k] X₀.nub) :=
    fun k hk h => by rw [hr k (by omega), hr (k + 1) hk]; exact (hc k).2 h
  have hX : ∀ i, (f^[i] s₀).2.1 = g^[i] X₀.nub ∧ (f^[i] s₀).2.2 = i := fun
    | 0 => ⟨rfl, rfl⟩
    | i + 1 => by rw [hs i]; exact ⟨rfl, rfl⟩
  rw [hfix, he, (hX j).1, (hX j).2]
  refine ⟨j, hjn, rfl, hr j (Nat.le_refl _), fun h => ?_, fun Y h0 hY => ?_, fun U hU hUn => ?_⟩
  · cases j with
    | zero =>
      rcases hstop with e | e
      · omega
      · exact absurd (show (X₀.nub.n.toNat + 1 == X₀.nub.n.toNat) = true from e) (by simp)
    | succ i =>
      rcases hstop with e | e
      · omega
      rw [hd i] at e
      have hci : (g^[i] X₀.nub).n.toNat = (g^[i + 1] X₀.nub).n.toNat := by simpa using e
      -- an equal count of two comparable rounds with distinct rows is an equal relation
      have heq : rep (g^[i] X₀.nub) = rep (g^[i + 1] X₀.nub) := by
        rcases hch with hh | hh
        · have hl := hup i (Nat.le_refl _) hh
          exact Freyd.Alg.le_antisymm hl ((rows_le_of_inj _ _ (hu i (by omega)) hl).2 (by omega))
        · have hl := hdn i (Nat.le_refl _) hh
          exact (Freyd.Alg.le_antisymm hl ((rows_le_of_inj _ _ (hu (i + 1) (Nat.le_refl _)) hl).2 (by omega))).symm
      show Φ (rep (g^[i + 1] X₀.nub)) = rep (g^[i + 1] X₀.nub)
      rw [← heq]; exact (hg i (by omega)).symm.trans heq.symm
  · -- every iterate from below a pre-fixed point stays below it
    have hY' : ∀ i x, x ⊑ Y → Φ^[i] x ⊑ Y := fun i => by
      induction i with
      | zero => exact fun _ hx => hx
      | succ i ih => exact fun x hx => Freyd.Alg.le_trans (hm _ _ (ih x hx)) hY
    rw [hr j (Nat.le_refl _)]; exact hY' j _ h0
  · -- run out of fuel, the count moved by one each round and stayed within `U`'s rows
    refine Nat.lt_of_le_of_ne hjn fun hj => ?_
    have hUk : ∀ k ≤ j, (g^[k] X₀.nub).n.toNat ≤ U.n.toNat := fun k hk =>
      (rows_le_of_inj _ U (hu k hk) (by rw [hr k hk]; exact hU k)).1
    rcases hch with hh | hh
    · have hk : ∀ k, k + 1 ≤ j → k ≤ (g^[k] X₀.nub).n.toNat := fun k => by
        induction k with
        | zero => intro; exact Nat.zero_le _
        | succ k ih =>
          intro hk
          have := (rows_le_of_inj _ _ (hu k (by omega)) (hup k (by omega) hh)).1
          have := hne k (by omega); have := ih (by omega); omega
      have := hk (n - 1) (by omega); have := hUk (n - 1) (by omega); omega
    · have hk : ∀ k, k + 1 ≤ j → k + (g^[k] X₀.nub).n.toNat ≤ (g^[0] X₀.nub).n.toNat := fun k => by
        induction k with
        | zero => intro; exact Nat.le_of_eq (Nat.zero_add _)
        | succ k ih =>
          intro hk
          have := (rows_le_of_inj _ _ (hu (k + 1) (by omega)) (hdn k (by omega) hh)).1
          have := hne k (by omega); have := ih (by omega); omega
      have := hk (n - 1) (by omega); have := hUk 0 (by omega); omega

#print axioms nodup_below
#print axioms rows_le_of_inj
#print axioms rep_fixOn

end LeetQ.Rel.Rep
