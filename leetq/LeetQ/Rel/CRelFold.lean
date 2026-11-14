/-
  The runtime ok-bit on the fold: `foldRound` answers a round's new state and a bit, the `&&` of its step's and of
  its `nubC`/`antiJoinC`/`unionC`'s; `foldRowsC` carries the `&&` of the rounds run; `foldByC` `&&`s it with `numC`'s,
  `topC`'s and `compC`'s. Under that one bit every capacity premise of `rep_foldBy_keep` is decided; what stays is
  the step's own spec (`hS`, at the rounds whose step bit is set) and `unionC`'s `hat`, not a size bound.
-/
import LeetQ.Rel.CRelRel
import LeetQ.Rel.RepFold
import LeetQ.Rel.RepArith
import LeetQ.Rel.CRelArith
import LeetQ.Rel.CRelList

namespace LeetQ.Rel

namespace Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet
open OpsN FoldN

/-- **`rep (nub R) = rep R` under `nubC`'s bit**: the codes' bits give `rep_nub`'s `hK`, `hV` (`oneOK_of_codesC`),
    the `fitsN` bits its picks. -/
theorem rep_nubC {k v : Obj} (R : Rel k v) (hb : (nubC R).2 = true) : rep (nubC R).1 = rep R := by
  simp only [nubC, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨hK, hV⟩, hk⟩, hv⟩ := hb
  rw [nubC_fst]
  exact rep_nub R (oneOK_of_codesC k R.key hK) (oneOK_of_codesC v R.val hV) (pickFits_of_fitsN k R.key _ hk _ (by simp))
    (pickFits_of_fitsN v R.val _ hv _ (by simp))

/-- **A round's bit**: its step's, `nubC`'s on the step's relation, `antiJoinC`'s on the pending rows, `unionC`'s on
    the leftovers, at the round's element `el`. -/
theorem foldRound_snd {E V : Obj} (ids : Rel .long (.arr E)) (stepC : Rel .long E → Rel .long V → Rel .long V × Bool)
    (st : Rel .long V × Rel .long V × Nat) (el : Rel .long E) (hel : el = elR(ids, st.2.2)) :
    (foldRound ids stepC st).2 = ((stepC el st.1).2 && (nubC (stepC el st.1).1).2 &&
      (antiJoinC (st.1°) (idU (Rel.key el))).2 && (unionC st.2.1 (antiJoinC (st.1°) (idU (Rel.key el))).1°).2) := by
  subst hel; rfl

/-- **The rounds' bits**: where the carried bit is set after `j` rounds, each of the first `j` rounds' is. -/
theorem round_bits {E V : Obj} (ids : Rel .long (.arr E)) (stepC : Rel .long E → Rel .long V → Rel .long V × Bool)
    (G : (Rel .long V × Rel .long V × Nat) × Bool → (Rel .long V × Rel .long V × Nat) × Bool)
    (hG : ∀ y, G y = ((foldRound ids stepC y.1).1, y.2 && (foldRound ids stepC y.1).2)) (x) :
    ∀ j, (G^[j] x).2 = true → ∀ i < j, (foldRound ids stepC (G^[i] x).1).2 = true
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | j + 1, h, i, hi => by
    have h' : (G (G^[j] x)).2 = true := h
    rw [hG, Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact round_bits ids stepC G hG x j h'.1 i hi
    · exact h'.2

/-- **`foldBy` under `foldByC`'s bit**: `rep_foldBy_keep` with its capacity premises decided — `numC`'s bit gives
    `hn`, `hv`; `topC`'s `hN`, `h63`, `hB`; each round `iter` runs has its bit set (`round_bits`, the run before
    the stop), whose `nubC`/`antiJoinC`/`unionC` bits read the round back (`rep_nubC`, `rep_antiJoinC`,
    `rep_unionC`, `round_out`); `compC`'s gives `hC`. What stays: `step`'s spec `hS` at the rounds whose step bit
    is set, and `unionC`'s `hat`. `T`, `pend₀`, `step`, `elK`, `f` are bound by their equations. -/
theorem rep_foldByC {E V : Obj} {m n : USize} (e : Vals V m) (X : Vals (.arr E) n)
    (stepC : Rel .long E → Rel .long V → Rel .long V × Bool)
    -- not a size bound: `razeTo`'s read-back of two atom parts (`rep_unionC`)
    (hat : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
      (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
        USize.size), Vals.RazeFits (.atom t) x y →
      (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
    (hb : (foldByC X e stepC).2 = true)
    (T : Rel .long (.arr E)) (hT : T = num (idU X) 0)
    (pend₀ : Rel .long V) (hpend : pend₀ = top (A := .long) (Rel.key T) e)
    (step : Rel .long E → Rel .long V → Rel .long V) (hstep : ∀ el p, step el p = (stepC el p).1)
    (Sr : Nat → E.El × V.El → V.El → Prop)
    (elK : Nat → Rel .long E) (hE : ∀ k, elK k = elR(T, k))
    (f : Rel .long V × Rel .long V × Nat → Rel .long V × Rel .long V × Nat) (hf : ∀ st, f st = rnd(st))
    (keep : Prop)
    (hS : ∀ i, i ≤ (Rel.val T).1.toNat → ne(i + 1) → (stepC (elK i) (f^[i] (pend₀, Alg.zero, 0)).1).2 = true →
      ∀ r v, rep (step (elK i) (f^[i] (pend₀, Alg.zero, 0)).1) r v ↔
      (∃ e u, rep (elK i) r e ∧ rep (f^[i] (pend₀, Alg.zero, 0)).1 r u ∧ Sr i (e, u) v) ∨
        (keep ∧ (¬ ∃ e, rep (elK i) r e) ∧ rep (f^[i] (pend₀, Alg.zero, 0)).1 r v)) :
    ∀ (xs : List E.El) w, rep (foldByC X e stepC).1 xs w ↔ (∃ i, X.row i = xs) ∧
      ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
        (∃ p, e.row p = ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm)) ∧
        (∀ t (ht : t < xs.length), Sr (xs.length - 1 - t)
          (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm))
          (ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm))) ∧
        w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm) := by
  simp only [foldByC, numC, topC, Bool.and_eq_true, decide_eq_true_eq] at hb
  rw [← hT, ← hpend] at hb
  obtain ⟨⟨⟨⟨hnb, hvb⟩, ⟨⟨hN, h63⟩, -⟩, hBb⟩, hFb⟩, hcb⟩ := hb
  have hstep' : step = fun el p => (stepC el p).1 := funext fun el => funext (hstep el)
  -- the rounds `foldRowsC` runs: the state `f^[i]` beside the carried bit
  have hGf : ∀ y : (Rel .long V × Rel .long V × Nat) × Bool,
      ((let g := foldRound T stepC y.1; (g.1, y.2 && g.2)) : (Rel .long V × Rel .long V × Nat) × Bool).1 = f y.1 :=
    fun y => by dsimp only; exact foldRound_fst T stepC step hstep elK hE f hf y.1
  obtain ⟨j, hj, he, hs, -⟩ := iter_stop (fun st : (Rel .long V × Rel .long V × Nat) × Bool => st.1.1.n == 0)
    (fun st => let g := foldRound T stepC st.1; (g.1, st.2 && g.2)) ((Rel.val T).1.toNat + 1)
    ((pend₀, Alg.zero, 0), true)
  have hπ := repeat_map f Prod.fst _ hGf ((pend₀, Alg.zero, 0), true)
  have hbits := round_bits T stepC _ (fun _ => rfl) ((pend₀, Alg.zero, 0), true) j
    (by rw [← he]; exact hFb)
  -- every round before a stop has its bit set
  have hround : ∀ i, i ≤ (Rel.val T).1.toNat → ne(i + 1) →
      (foldRound T stepC (f^[i] (pend₀, Alg.zero, 0))).2 = true := by
    intro i hi hne
    have hij : i < j := by
      refine Nat.lt_of_not_le fun hji => ?_
      rcases hs with hs | hs
      · omega
      · have h0 := hne j (by omega)
        rw [← hπ j] at h0
        exact absurd hs (by simp only [h0, Bool.false_eq_true, not_false_eq_true])
    have h := hbits i hij
    rwa [hπ i] at h
  have hbit : ∀ i, i ≤ (Rel.val T).1.toNat → ne(i + 1) →
      (stepC (elK i) (f^[i] (pend₀, Alg.zero, 0)).1).2 = true ∧
        (nubC (stepC (elK i) (f^[i] (pend₀, Alg.zero, 0)).1).1).2 = true ∧
        (antiJoinC ((f^[i] (pend₀, Alg.zero, 0)).1°) (idU (Rel.key (elK i)))).2 = true ∧
        (unionC (f^[i] (pend₀, Alg.zero, 0)).2.1
          (antiJoinC ((f^[i] (pend₀, Alg.zero, 0)).1°) (idU (Rel.key (elK i)))).1°).2 = true := by
    intro i hi hne
    have h := hround i hi hne
    rw [foldRound_snd T stepC _ (elK i) (by rw [rounds_count pend₀ step elK f hf i]; exact hE i)] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  have hone : ∀ i, i ≤ (Rel.val T).1.toNat → ne(i + 1) → roundRB(i) := by
    intro i hi hne
    obtain ⟨-, hNb, hJb, hUb⟩ := hbit i hi hne
    refine ⟨by rw [hstep, ← nubC_fst]; exact rep_nubC _ hNb, fun r v => ?_⟩
    show rep (unionC _ (antiJoinC _ _).1°).1 r v ↔ _
    rw [rep_unionC hat _ _ hUb]
    show _ ∨ _ ↔ _
    exact or_congr Iff.rfl (round_out (elK i) _ (rep_antiJoinC _ _ hJb) r v)
  have hfb : (foldByC X e stepC).1 = foldBy X e step := by rw [foldByC_fst, hstep']
  rw [hfb]
  exact rep_foldBy_keep e X T hT (by simpa using hnb) (pickFits_of_fitsN (.arr E) X _ hvb _ (by simp [idU])) pend₀
    hpend hN h63 (pickFits_of_fitsN V e _ hBb _ (by simp)) step Sr elK hE f hf hone keep
    (fun i hi hne => hS i hi hne (hbit i hi hne).1) _ (by rw [foldRowsC_fst, hstep'])
    (rep_compC _ _ hcb)

#print axioms rep_foldByC

/-- **`foldOn` under `foldOnC`'s bit**: `rep_foldByC` at the step `demandStepC SC`, whose round `i` reads back,
    where its bit is set, by `step_rep_of` at `rep_pairC`, `rep_compC` (the step bit's) as `(SC (D i)).1` on the
    pairs (element, value) — `Sr i` there (`hSr`, at the rounds whose step bit is set, which holds `ranC`'s and
    `SC`'s bits at `D i`). What stays: `hat`, and `hSr`, the family's own spec. `T`, `pend₀`, `step`, `elK`, `f`,
    `D` are bound by their equations. -/
theorem rep_foldOnC {E V : Obj} {m n : USize} (e : Vals V m)
    (SC : Rel (.prod E V) (.prod E V) → Rel (.prod E V) V × Bool) (X : Vals (.arr E) n)
    -- not a size bound: `razeTo`'s read-back of two atom parts (`rep_unionC`)
    (hat : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
      (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
        USize.size), Vals.RazeFits (.atom t) x y →
      (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
    (hb : (foldOnC e SC X).2 = true)
    (T : Rel .long (.arr E)) (hT : T = num (idU X) 0)
    (pend₀ : Rel .long V) (hpend : pend₀ = top (A := .long) (Rel.key T) e)
    (step : Rel .long E → Rel .long V → Rel .long V) (hstep : ∀ el p, step el p = (demandStepC SC el p).1)
    (elK : Nat → Rel .long E) (hE : ∀ k, elK k = elR(T, k))
    (f : Rel .long V × Rel .long V × Nat → Rel .long V × Rel .long V × Nat) (hf : ∀ st, f st = rnd(st))
    (D : Nat → Rel (.prod E V) (.prod E V)) (hD : ∀ k, D k = ran (pair (elK k) (f^[k] (pend₀, Alg.zero, 0)).1))
    (Sr : Nat → E.El × V.El → V.El → Prop)
    (hSr : ∀ i, i ≤ (Rel.val T).1.toNat → ne(i + 1) →
      (demandStepC SC (elK i) (f^[i] (pend₀, Alg.zero, 0)).1).2 = true → ∀ p w, (∃ a, rep (D i) a p) →
        (∀ a b, rep (D i) a b → a = b) → (rep (SC (D i)).1 p w ↔ Sr i p w)) :
    ∀ (xs : List E.El) w, rep (foldOnC e SC X).1 xs w ↔ (∃ i, X.row i = xs) ∧
      ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
        (∃ p, e.row p = ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm)) ∧
        (∀ t (ht : t < xs.length), Sr (xs.length - 1 - t)
          (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm))
          (ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm))) ∧
        w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm) :=
  rep_foldByC e X (demandStepC SC) hat hb T hT pend₀ hpend step hstep Sr elK hE f hf False
    (fun i hi hne hbi r v => by
      have hbi' := hbi
      simp only [demandStepC, Bool.and_eq_true] at hbi'
      obtain ⟨⟨⟨hp, hd⟩, -⟩, hc⟩ := hbi'
      simp only [hstep, false_and, or_false]
      refine (step_rep_of (elK i) _ (fun D => (SC D).1) (rep_pairC _ _ hp) (rep_compC _ _ hc) r v).trans ?_
      -- the pair a row meets is in the round's `D i`: `ranC`'s and `pairC`'s bits read it back
      have hDi : rep (D i) = corefl (A := (⟨(Obj.prod E V).El⟩ : RelSet.{0}))
          fun b => ∃ a, rep (pairC (elK i) (f^[i] (pend₀, Alg.zero, 0)).1).1 a b := by
        rw [hD i, show ran (pair (elK i) (f^[i] (pend₀, Alg.zero, 0)).1) = (ranC (pairC (elK i)
          (f^[i] (pend₀, Alg.zero, 0)).1).1).1 from rfl, (rep_ranC _ hd).trans (dom_corefl _)]
        rfl
      have hS' : ∀ e u, rep (elK i) r e → rep (f^[i] (pend₀, Alg.zero, 0)).1 r u →
          (rep (SC (ran (pair (elK i) (f^[i] (pend₀, Alg.zero, 0)).1))).1 (e, u) v ↔ Sr i (e, u) v) := by
        intro e u he hu
        rw [← hD i]
        refine hSr i hi hne hbi _ _ ⟨(e, u), ?_⟩ (fun a b h => by rw [hDi] at h; exact h.1)
        rw [hDi]
        refine ⟨rfl, r, ?_⟩
        rw [rep_pairC _ _ hp]
        exact ⟨he, hu⟩
      exact exists_congr fun e => exists_congr fun u =>
        ⟨fun ⟨he, hu, h⟩ => ⟨he, hu, (hS' e u he hu).1 h⟩, fun ⟨he, hu, h⟩ => ⟨he, hu, (hS' e u he hu).2 h⟩⟩)

/-- **`fold` under `foldC`'s bit**: `rep_foldOnC` at the constant family `S`, read back as `rep S` outright. -/
theorem rep_foldC {E V : Obj} {m n : USize} (e : Vals V m) (S : Rel (.prod E V) V) (X : Vals (.arr E) n)
    (hat : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
      (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
        USize.size), Vals.RazeFits (.atom t) x y →
      (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
    (hb : (foldC e S X).2 = true) :
    ∀ (xs : List E.El) w, rep (foldC e S X).1 xs w ↔ (∃ i, X.row i = xs) ∧
      ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
        (∃ p, e.row p = ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm)) ∧
        (∀ t (ht : t < xs.length), rep S (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm))
          (ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm))) ∧
        w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm) :=
  rep_foldOnC e (fun _ => (S, true)) X hat hb _ rfl _ rfl _ (fun _ _ => rfl) _ (fun _ => rfl) _ (fun _ => rfl) _
    (fun _ => rfl) (fun _ => rep S) (fun _ _ _ _ _ _ _ _ => Iff.rfl)

/-- **`sum` under `sumC`'s bit**: `rep_foldOnC` at `plus` on the round's pairs, which reads back on a pair of `D k`
    with no premise (`rep_plus`), then `sum_chain`. What stays: `hat`. -/
theorem Arr.rep_sumC {n : USize} (X : Vals (.arr .long) n)
    (hat : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
      (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
        USize.size), Vals.RazeFits (.atom t) x y →
      (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
    (hb : (Alg.Arr.sumC X).2 = true) :
    ∀ (xs : List Int64) (w : Int64), rep (Alg.Arr.sumC X).1 xs w ↔ (∃ i, X.row i = xs) ∧
      (∀ t, t ≤ xs.length → -2 ^ 63 < List.sum (List.map Int64.toInt (List.drop t xs)) ∧
        List.sum (List.map Int64.toInt (List.drop t xs)) < 2 ^ 63) ∧ (∀ x ∈ xs, x ≠ nul) ∧
      w = xs.foldr (· + ·) 0 := by
  intro xs w; unfold Alg.Arr.sumC at hb ⊢
  exact (rep_foldOnC (E := .long) (V := .long) (m := ([0] : List Int64).length.toUSize) (col [0]) (fun D => (plus D.val, true)) X hat hb _ rfl _ rfl _ (fun _ _ => rfl) _ (fun _ => rfl) _ (fun _ => rfl) _
    (fun _ => rfl) (fun _ (p : Int64 × Int64) (w : Int64) =>
      w = Ew.intStep Ew.add nul p.1 p.2 ∧ w ≠ nul ∧ (0 ≤ p.2 ↔ p.1 ≤ w))
    (fun _ _ _ _ p w hp _ => by
      obtain ⟨a, b⟩ := p
      show rep (plus _) (a, b) w ↔ _
      rw [rep_plus]
      obtain ⟨_, i, -, h⟩ := hp
      exact and_iff_right ⟨i, h⟩) xs w).trans (and_congr Iff.rfl (sum_chain xs w))

/-- **`length` under `lengthC`'s bit**: `needSize`'s count fits (else the bit is `false`); `succC`'s bit reads `sc`
    back (`rep_succC`), the decided `2^63` keeps `m + 1` off the null; `rep_foldOnC` at `outr D ≫ sc`, each round's
    `compC` bit in its step's, `D k` coreflexive, then `length_chain`. What stays: `hat`. -/
theorem rep_lengthC {E : Obj} {n : USize} (X : Vals (.arr E) n)
    (hat : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
      (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
        USize.size), Vals.RazeFits (.atom t) x y →
      (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
    (hb : (lengthC X).2 = true) :
    ∀ (xs : List E.El) (w : Int64), rep (lengthC X).1 xs w ↔ (∃ i, X.row i = xs) ∧ w = Int64.ofNat xs.length := by
  intro xs w
  by_cases hX : X.1.toNat + 1 < USize.size
  case neg => simp only [lengthC, needSize, need, dif_neg hX] at hb; exact absurd hb Bool.false_ne_true
  simp only [lengthC, needSize, need, dif_pos hX, Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
  obtain ⟨⟨hsb, hfb⟩, h63X⟩ := hb
  have hcN : ((X.1.toNat + 1).toUSize).toNat = X.1.toNat + 1 := USize.toNat_ofNat_of_lt' hX
  have hsc' : ∀ m w, m < X.1.toNat →
      (rep (succC (tilCol (X.1.toNat + 1).toUSize)).1 (Int64.ofNat m) w ↔ w = Int64.ofNat (m + 1)) := by
    intro m w hm
    rw [rep_succC _ hsb, intStep_ofNat_succ m (by omega)]
    simp only [Vals.row_atom, tilCol_get]
    constructor
    · rintro ⟨-, h, -⟩; exact h
    · rintro rfl; exact ⟨⟨⟨m, by omega⟩, rfl⟩, rfl, ⟨m + 1, by omega⟩, rfl⟩
  have hL : (∃ i, X.row i = xs) → xs.length ≤ X.1.toNat := by
    rintro ⟨⟨i, hi⟩, rfl⟩
    obtain ⟨h1, h2, -⟩ := slicesOf_row X (by omega) hi
    omega
  refine (rep_foldOnC (E := E) (V := .long) (m := ([0] : List Int64).length.toUSize) (col [0]) (fun D => compC (outr D) (succC (tilCol (X.1.toNat + 1).toUSize)).1) X hat hfb _ rfl _ rfl _ (fun _ _ => rfl) _ (fun _ => rfl) _ (fun _ => rfl) _
    (fun _ => rfl) (fun _ (p : E.El × Int64) w => rep (succC (tilCol (X.1.toNat + 1).toUSize)).1 p.2 w)
    (fun _ _ _ hbk p w hp hcor => ?_) xs w).trans
    (and_congr_right fun hx => length_chain _ X.1.toNat hsc' xs (hL hx) w)
  show rep (compC (outr _) _).1 p w ↔ _
  rw [rep_compC, rep_outr]
  rotate_left; · simp only [demandStepC, Bool.and_eq_true] at hbk; exact hbk.1.2
  obtain ⟨a, ha⟩ := hp
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hy⟩
    obtain rfl := hcor _ _ hz
    exact hy
  · intro hy
    obtain rfl := hcor _ _ ha
    exact ⟨a.2, ⟨a, ha, rfl⟩, hy⟩

/-- **`map` under `mapC`'s bit**: `rep_foldByC` at the step `consC (pairC (compC el R) pend)`, each round's three
    bits read it back (`rep_consC`, `rep_pairC`, `rep_compC`), then `map_chain`. What stays: `hat`. -/
theorem rep_mapC {A B : Obj} {n : USize} (R : Rel A B) (X : Vals (.arr A) n)
    (hat : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
      (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
        USize.size), Vals.RazeFits (.atom t) x y →
      (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
    (hb : (mapC R X).2 = true) :
    ∀ (xs : List A.El) ys, rep (mapC R X).1 xs ys ↔ (∃ i, X.row i = xs) ∧ ys.length = xs.length ∧
      ∀ t (ht : t < xs.length) (ht' : t < ys.length), rep R (xs[t]'ht) (ys[t]'ht') := by
  intro xs ys; unfold mapC at hb ⊢
  refine (rep_foldByC (nilVal B) X _ hat hb _ rfl _ rfl _ (fun _ _ => rfl)
    (fun _ eu v => ∃ b, rep R eu.1 b ∧ v = b :: eu.2) _ (fun _ => rfl) _ (fun _ => rfl) False
    (fun i _ _ hbi r v => ?_) xs ys).trans ?_
  · simp only [Bool.and_eq_true] at hbi
    obtain ⟨⟨hq, hp⟩, hc⟩ := hbi
    simp only [false_and, or_false]
    refine (rep_consC _ hc r v).trans ?_
    rw [rep_pairC _ _ hp, rep_compC _ _ hq]
    constructor
    · rintro ⟨b, bs, ⟨⟨e, he, hR⟩, hu⟩, rfl⟩; exact ⟨e, bs, he, hu, b, hR, rfl⟩
    · rintro ⟨e, u, he, hu, b, hR, rfl⟩; exact ⟨b, u, ⟨⟨e, he, hR⟩, hu⟩, rfl⟩
  -- `nilVal B`'s one row is `[]`
  exact and_congr Iff.rfl ((exists_congr fun zs => exists_congr fun _ => and_congr
    ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨⟨0, by simp⟩, h.symm⟩⟩ Iff.rfl).trans (map_chain (rep R) xs ys))

#print axioms rep_foldOnC
#print axioms rep_foldC
#print axioms rep_mapC
#print axioms Arr.rep_sumC
#print axioms rep_lengthC

end Rep

namespace CRel

open QLean QLean.Kernel LeetQ.Rel.Alg Freyd Freyd.Alg Freyd.Alg.RelSet LeetQ.Rel.Rep FoldN

/-- `foldBy` on a step over `CRel`s, ok where every round's step was and `foldByC` ran within capacity. The
    step sees its inputs as ok: their bits are already in the fold's. -/
def foldBy {E V : Obj} {n m : USize} (X : Vals (.arr E) n) (e : Vals V m)
    (step : CRel .long E → CRel .long V → CRel .long V) : CRel (.arr E) V :=
  let r := foldByC X e fun el p => let s := step ⟨el, true⟩ ⟨p, true⟩; (s.rel, s.ok)
  ⟨r.1, r.2⟩

/-- **`CRel.foldBy` read back under its bit**: `rep_foldByC`. -/
theorem rep_foldBy {E V : Obj} {m n : USize} (e : Vals V m) (X : Vals (.arr E) n)
    (stepK : CRel .long E → CRel .long V → CRel .long V)
    (hat : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
      (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
        USize.size), Vals.RazeFits (.atom t) x y →
      (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
    (hb : (foldBy X e stepK).ok = true)
    (T : Rel .long (.arr E)) (hT : T = Alg.num (idU X) 0)
    (pend₀ : Rel .long V) (hpend : pend₀ = Alg.top (A := .long) (Rel.key T) e)
    (step : Rel .long E → Rel .long V → Rel .long V) (hstep : ∀ el p, step el p = (stepK ⟨el, true⟩ ⟨p, true⟩).rel)
    (Sr : Nat → E.El × V.El → V.El → Prop)
    (elK : Nat → Rel .long E) (hE : ∀ k, elK k = elR(T, k))
    (f : Rel .long V × Rel .long V × Nat → Rel .long V × Rel .long V × Nat) (hf : ∀ st, f st = rnd(st))
    (keep : Prop)
    (hS : ∀ i, i ≤ (Rel.val T).1.toNat → ne(i + 1) →
      (stepK ⟨elK i, true⟩ ⟨(f^[i] (pend₀, Alg.zero, 0)).1, true⟩).ok = true →
      ∀ r v, rep (step (elK i) (f^[i] (pend₀, Alg.zero, 0)).1) r v ↔
      (∃ e u, rep (elK i) r e ∧ rep (f^[i] (pend₀, Alg.zero, 0)).1 r u ∧ Sr i (e, u) v) ∨
        (keep ∧ (¬ ∃ e, rep (elK i) r e) ∧ rep (f^[i] (pend₀, Alg.zero, 0)).1 r v)) :
    ∀ (xs : List E.El) w, rep (foldBy X e stepK).rel xs w ↔ (∃ i, X.row i = xs) ∧
      ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
        (∃ p, e.row p = ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm)) ∧
        (∀ t (ht : t < xs.length), Sr (xs.length - 1 - t)
          (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm))
          (ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm))) ∧
        w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm) :=
  rep_foldByC e X _ hat hb T hT pend₀ hpend step hstep Sr elK hE f hf keep hS

/-- `foldOn` on a family over `CRel`s, ok where every round's family member was and `foldOnC` ran within
    capacity. The family sees the round's pairs as ok: their bits are already in the fold's. -/
def foldOn {E V : Obj} {m n : USize} (e : Vals V m) (S : CRel (.prod E V) (.prod E V) → CRel (.prod E V) V)
    (X : Vals (.arr E) n) : CRel (.arr E) V :=
  let r := foldOnC e (fun D => ((S ⟨D, true⟩).rel, (S ⟨D, true⟩).ok)) X
  ⟨r.1, r.2⟩

/-- **`CRel.foldOn` read back under its bit**: `rep_foldOnC`. -/
theorem rep_foldOn {E V : Obj} {m n : USize} (e : Vals V m) (S : CRel (.prod E V) (.prod E V) → CRel (.prod E V) V)
    (X : Vals (.arr E) n)
    (hat : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
      (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
        USize.size), Vals.RazeFits (.atom t) x y →
      (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
    (hb : (foldOn e S X).ok = true)
    (T : Rel .long (.arr E)) (hT : T = Alg.num (idU X) 0)
    (pend₀ : Rel .long V) (hpend : pend₀ = Alg.top (A := .long) (Rel.key T) e)
    (step : Rel .long E → Rel .long V → Rel .long V)
    (hstep : ∀ el p, step el p = (demandStepC (fun D => ((S ⟨D, true⟩).rel, (S ⟨D, true⟩).ok)) el p).1)
    (elK : Nat → Rel .long E) (hE : ∀ k, elK k = elR(T, k))
    (f : Rel .long V × Rel .long V × Nat → Rel .long V × Rel .long V × Nat) (hf : ∀ st, f st = rnd(st))
    (D : Nat → Rel (.prod E V) (.prod E V))
    (hD : ∀ k, D k = Alg.ran (Alg.pair (elK k) (f^[k] (pend₀, Alg.zero, 0)).1))
    (Sr : Nat → E.El × V.El → V.El → Prop)
    (hSr : ∀ i, i ≤ (Rel.val T).1.toNat → ne(i + 1) →
      (demandStepC (fun D => ((S ⟨D, true⟩).rel, (S ⟨D, true⟩).ok)) (elK i) (f^[i] (pend₀, Alg.zero, 0)).1).2 =
        true → ∀ p w, (∃ a, rep (D i) a p) → (∀ a b, rep (D i) a b → a = b) →
          (rep (S ⟨D i, true⟩).rel p w ↔ Sr i p w)) :
    ∀ (xs : List E.El) w, rep (foldOn e S X).rel xs w ↔ (∃ i, X.row i = xs) ∧
      ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
        (∃ p, e.row p = ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm)) ∧
        (∀ t (ht : t < xs.length), Sr (xs.length - 1 - t)
          (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm))
          (ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm))) ∧
        w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm) :=
  rep_foldOnC e _ X hat hb T hT pend₀ hpend step hstep elK hE f hf D hD Sr hSr

/-- `fold` of one `CRel` step, ok where `S` is and `foldC` ran within capacity. -/
def fold {E V : Obj} {m n : USize} (e : Vals V m) (S : CRel (.prod E V) V) (X : Vals (.arr E) n) : CRel (.arr E) V :=
  let r := foldC e S.rel X
  ⟨r.1, S.ok && r.2⟩

/-- **`CRel.fold` read back under its bit**: `rep_foldC`. -/
theorem rep_fold {E V : Obj} {m n : USize} (e : Vals V m) (S : CRel (.prod E V) V) (X : Vals (.arr E) n)
    (hat : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
      (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
        USize.size), Vals.RazeFits (.atom t) x y →
      (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
    (hb : (fold e S X).ok = true) :
    ∀ (xs : List E.El) w, rep (fold e S X).rel xs w ↔ (∃ i, X.row i = xs) ∧
      ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
        (∃ p, e.row p = ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm)) ∧
        (∀ t (ht : t < xs.length), rep S.rel (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm))
          (ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm))) ∧
        w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm) :=
  rep_foldC e S.rel X hat (by simp only [fold, Bool.and_eq_true] at hb; exact hb.2)

/-- `sum` as a `CRel`, ok where `sumC` ran within capacity. -/
def Arr.sum {n : USize} (X : Vals (.arr .long) n) : CRel (.arr .long) .long :=
  let r := Alg.Arr.sumC X
  ⟨r.1, r.2⟩

/-- **`CRel.Arr.sum` read back under its bit**: `Rep.Arr.rep_sumC`. -/
theorem Arr.rep_sum {n : USize} (X : Vals (.arr .long) n)
    (hat : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
      (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
        USize.size), Vals.RazeFits (.atom t) x y →
      (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
    (hb : (Arr.sum X).ok = true) :
    ∀ (xs : List Int64) (w : Int64), rep (Arr.sum X).rel xs w ↔ (∃ i, X.row i = xs) ∧
      (∀ t, t ≤ xs.length → -2 ^ 63 < List.sum (List.map Int64.toInt (List.drop t xs)) ∧
        List.sum (List.map Int64.toInt (List.drop t xs)) < 2 ^ 63) ∧ (∀ x ∈ xs, x ≠ nul) ∧
      w = xs.foldr (· + ·) 0 :=
  Rep.Arr.rep_sumC X hat hb

/-- `length` as a `CRel`, ok where `lengthC` ran within capacity. -/
def length {E : Obj} {n : USize} (X : Vals (.arr E) n) : CRel (.arr E) .long :=
  let r := lengthC X
  ⟨r.1, r.2⟩

/-- **`CRel.length` read back under its bit**: `rep_lengthC`. -/
theorem rep_length {E : Obj} {n : USize} (X : Vals (.arr E) n)
    (hat : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
      (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
        USize.size), Vals.RazeFits (.atom t) x y →
      (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
    (hb : (length X).ok = true) :
    ∀ (xs : List E.El) (w : Int64), rep (length X).rel xs w ↔ (∃ i, X.row i = xs) ∧ w = Int64.ofNat xs.length :=
  rep_lengthC X hat hb

/-- `map` as a `CRel`, ok where `R` is and `mapC` ran within capacity. -/
def map {A B : Obj} {n : USize} (R : CRel A B) (X : Vals (.arr A) n) : CRel (.arr A) (.arr B) :=
  let r := mapC R.rel X
  ⟨r.1, R.ok && r.2⟩

/-- **`CRel.map` read back under its bit**: `rep_mapC`. -/
theorem rep_map {A B : Obj} {n : USize} (R : CRel A B) (X : Vals (.arr A) n)
    (hat : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
      (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
        USize.size), Vals.RazeFits (.atom t) x y →
      (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
    (hb : (map R X).ok = true) :
    ∀ (xs : List A.El) ys, rep (map R X).rel xs ys ↔ (∃ i, X.row i = xs) ∧ ys.length = xs.length ∧
      ∀ t (ht : t < xs.length) (ht' : t < ys.length), rep R.rel (xs[t]'ht) (ys[t]'ht') :=
  rep_mapC R.rel X hat (by simp only [map, Bool.and_eq_true] at hb; exact hb.2)

#print axioms Arr.rep_sum
#print axioms rep_length
#print axioms rep_map

end CRel

end LeetQ.Rel
