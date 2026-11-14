/-
  The fold ops of `Alg` read back. `fold`, `foldOn`, `map`, … all run `foldRows`: rounds that pair each row still
  pending with its element `k` from the end, hand both to the step, `nub` the result, and move the rows that have
  no element `k` to `out`. This file reads one round in `Rel(Set)` and the rounds' `out` by induction.
-/
import LeetQ.Rel.RepDiv

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

-- `RepDiv`'s `c1`, `nubI`, `PQ` (local notations, so restated here)
set_option hygiene false in
local notation "c1(" X ", " n ", " x ")" => (Obj.codes X (#v[⟨n, x⟩] : Vector (Part X) 1))[0]
set_option hygiene false in
local notation "nubI(" X ", " Y ", " R ")" =>
  (tuples.tupleIds (c1(X, Rel.n R, Rel.key R)) #[c1(Y, Rel.n R, Rel.val R)]).2
set_option hygiene false in
local notation "PQ(" Y ", " Z ")" =>
  (⟨_, Obj.raze Y #[⟨Rel.n P, Rel.key P⟩, ⟨Rel.n Q, Rel.key Q⟩] hNk,
    Obj.raze Z #[⟨Rel.n P, Rel.val P⟩, ⟨Rel.n Q, Rel.val Q⟩] hNv⟩ : Rel Y Z)
-- the parts `antiJoin pend° (idU el.key)` codes: the rows of `pend`, the rows of `el`
set_option hygiene false in
local notation "jparts" => (#v[⟨Rel.n (pend°), Rel.val (pend°)⟩,
  ⟨Rel.n (idU (Rel.key el)), Rel.val (idU (Rel.key el))⟩] : Vector (Part .long) 2)

/-- **One round of `foldRows`, read back**: the new state `S.nub` (`S` the step's result) is `S`, and the new
    `out`, `P ∪ (antiJoin pend° (idU el.key))°`, adds to `P` the pairs of `pend` whose row has no element this
    round. `antiJoin`'s and `∪`'s intermediate values are bound by their defining equations (`hjc`, `hI`, `hQ`).
    Hypotheses: `Obj.CodesFit` of every coded part, `Vals.PickFits` where a part is picked, the counts fit. -/
theorem round_rep {E V : Obj} (el : Rel .long E) (pend P S : Rel .long V)
    (hSK : Obj.CodesFit .long (#v[⟨S.n, S.key⟩] : Vector (Part .long) 1))
    (hSV : V.CodesFit (#v[⟨S.n, S.val⟩] : Vector (Part V) 1))
    (hSk : Vals.PickFits .long S.key (ids nubI(.long, V, S)))
    (hSv : Vals.PickFits V S.val (ids nubI(.long, V, S)))
    (jc : Vector Code 2) (hjc : jc = Obj.codes .long jparts) (hjf : Obj.CodesFit .long jparts)
    (I : ByteArray) (hI : I = anti (jc[0]'(by decide)) (jc[1]'(by decide)))
    (hJk : Vals.PickFits V (Rel.key (pend°)) (ids I)) (hJv : Vals.PickFits .long (Rel.val (pend°)) (ids I))
    (Q : Rel .long V) (hQ : Q = (antiJoin (pend°) (idU (Rel.key el)))°)
    (hU : P.n.toNat + Q.n.toNat < USize.size)
    (hNk : ((#[⟨P.n, P.key⟩, ⟨Q.n, Q.key⟩] : Array (Part .long)).toList.map fun c : Part .long => c.1.toNat).sum <
      USize.size)
    (hNv : ((#[⟨P.n, P.val⟩, ⟨Q.n, Q.val⟩] : Array (Part V)).toList.map fun c : Part V => c.1.toNat).sum <
      USize.size)
    (hFk : Vals.RazeFits .long P.key Q.key) (hFv : Vals.RazeFits V P.val Q.val)
    (hUK : Obj.CodesFit .long (#v[⟨(PQ(.long, V)).n, (PQ(.long, V)).key⟩] : Vector (Part .long) 1))
    (hUV : V.CodesFit (#v[⟨(PQ(.long, V)).n, (PQ(.long, V)).val⟩] : Vector (Part V) 1))
    (hUk : Vals.PickFits .long (PQ(.long, V)).key (ids nubI(.long, V, PQ(.long, V))))
    (hUv : Vals.PickFits V (PQ(.long, V)).val (ids nubI(.long, V, PQ(.long, V)))) :
    rep (Rel.nub S) = rep S ∧
      ∀ r v, rep (P ∪ Q) r v ↔ rep P r v ∨ (rep pend r v ∧ ¬ ∃ e, rep el r e) := by
  refine ⟨rep_nub S (one_ok _ hSK) (one_ok _ hSV) hSk hSv, fun r v => ?_⟩
  rw [rep_union_full P Q hU hNk hNv hFk hFv (one_ok _ hUK) (one_ok _ hUV) hUk hUv]
  show rep P r v ∨ rep Q r v ↔ _
  subst hjc hI hQ
  have hA := congrFun (congrFun (rep_antiJoin (pend°) (idU (Rel.key el))
    (codes_faithful_wf .long _ hjf).1 hJk hJv) v) r
  rw [rep_conv]
  show _ ∨ rep (antiJoin (pend°) (idU (Rel.key el))) v r ↔ _
  rw [hA]
  show _ ∨ (∃ y, rep (pend°) v y ∧ y = r ∧ ¬ ∃ x, rep (idU (Rel.key el)) x y) ↔ _
  rw [rep_conv, rep_idU]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨y, hp, rfl, hn⟩
    exact ⟨hp, fun ⟨_, i, hi, _⟩ => hn ⟨_, rfl, i, hi⟩⟩
  · rintro ⟨hp, hn⟩
    exact ⟨r, hp, rfl, fun ⟨x, hx, i, hi⟩ => hn ⟨Vals.row (Rel.val el) i, i, hi.trans hx, rfl⟩⟩

/-! ## The rounds -/

open QLean.Dep

/-- `f^[j]`, `f` applied `j` times (core's `Nat.repeat`, outermost application last). -/
local notation:max f "^[" n "]" => Nat.repeat f n

/-- **`iter` stops at an iterate**: `iter n done f a` is `f^[j] a` for some `j ≤ n` where the rounds ran out
    (`j = n`) or `done` holds. -/
theorem iter_stop {α : Type} (done : α → Bool) (f : α → α) :
    ∀ (n : Nat) (a : α), ∃ j ≤ n, iter n done f a = f^[j] a ∧ (j = n ∨ done (f^[j] a) = true) := by
  have comm : ∀ j a, f^[j] (f a) = f (f^[j] a) := fun j => by
    induction j with
    | zero => intro; rfl
    | succ j ih => intro a; exact congrArg f (ih a)
  intro n
  induction n with
  | zero => intro a; exact ⟨0, Nat.le_refl _, by unfold iter; rw [hylo]; simp [Nat.repeat], Or.inl rfl⟩
  | succ m ih =>
    intro a
    cases hd : done a
    · obtain ⟨j, hj, he, hs⟩ := ih (f a)
      have e : iter (m + 1) done f a = iter m done f (f a) := by unfold iter; rw [hylo]; simp [hd]
      refine ⟨j + 1, by omega, by rw [e, he, comm]; rfl, ?_⟩
      rw [comm] at hs
      exact hs.imp (by omega) id
    · exact ⟨0, Nat.zero_le _, by unfold iter; rw [hylo]; simp [hd, Nat.repeat], Or.inr hd⟩

-- `foldRows`' element of round `k`: each row longer than `k` to its element `k` from the end
set_option hygiene false in
local notation "elR(" ids ", " k ")" =>
  (let s := slicesOf (Rel.val ids)
   let ends := add (Rel.n ids) s.1 s.2
   let a := whereBits (Rel.n ids) (Ew.cmp Ew.gt Ew.i64 Ew.va s.2 (one (k).toUInt64) (Rel.n ids))
   longCount "foldRows" a fun r hr =>
     let pos := Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul (gather 8 ends a) (one ((k) + 1).toUInt64) r
     (⟨r, Vals.pick .long (Rel.key ids) a r hr, Vals.pick _ (Rel.val ids).2.2.2 pos r (len_val ..)⟩ : Rel .long _))
-- `foldRows`' round, its element bound to `elK`: `round_rep`'s `S.nub` and `P ∪ Q`
set_option hygiene false in
local notation "rnd(" st ")" => ((step (elK (st).2.2) (st).1).nub,
  (st).2.1 ∪ (antiJoin ((st).1°) (idU (Rel.key (elK (st).2.2))))°, (st).2.2 + 1)

/-- **`foldRows` is the rounds' `out` at a stop**: the iterate `f^[j]` of the round `f` from `(pend, 𝟘, 0)` at
    the `j` where `iter` stops, the rounds' bound `X.1 + 1` reached or no row pending. `elK`, `f` are bound by
    their defining equations. -/
theorem foldRows_iter {E V : Obj} (ids : Rel .long (.arr E)) (pend : Rel .long V)
    (step : Rel .long E → Rel .long V → Rel .long V) (elK : Nat → Rel .long E) (hE : ∀ k, elK k = elR(ids, k))
    (f : Rel .long V × Rel .long V × Nat → Rel .long V × Rel .long V × Nat) (hf : ∀ st, f st = rnd(st)) :
    ∃ j ≤ (Rel.val ids).1.toNat + 1, foldRows ids pend step = (f^[j] (pend, Alg.zero, 0)).2.1 ∧
      (j = (Rel.val ids).1.toNat + 1 ∨ ((f^[j] (pend, Alg.zero, 0)).1.n == 0) = true) := by
  obtain ⟨j, hj, he, hs⟩ := iter_stop (fun st => st.1.n == 0) f ((Rel.val ids).1.toNat + 1) (pend, Alg.zero, 0)
  refine ⟨j, hj, ?_, hs⟩
  rw [← he]
  refine congrArg (fun g : Rel .long V × Rel .long V × Nat → Rel .long V × Rel .long V × Nat =>
    (iter ((Rel.val ids).1.toNat + 1) (fun st => st.1.n == 0) g (pend, Alg.zero, 0)).2.1) (funext fun st => ?_)
  obtain ⟨p, o, k⟩ := st
  rw [hf, hE]

-- `round_rep`'s hypotheses at `el`, `pend`, `P`, `S`, its bound values `jc`, `I`, `Q` quantified with their equations
set_option hygiene false in
local notation "roundOK" =>
  Obj.CodesFit .long (#v[⟨S.n, S.key⟩] : Vector (Part .long) 1) ∧
  V.CodesFit (#v[⟨S.n, S.val⟩] : Vector (Part V) 1) ∧
  Vals.PickFits .long S.key (ids nubI(.long, V, S)) ∧ Vals.PickFits V S.val (ids nubI(.long, V, S)) ∧
  Obj.CodesFit .long jparts ∧
  (∀ jc : Vector Code 2, jc = Obj.codes .long jparts → ∀ I : ByteArray, I = anti (jc[0]'(by decide)) (jc[1]'(by decide)) →
    Vals.PickFits V (Rel.key (pend°)) (ids I) ∧ Vals.PickFits .long (Rel.val (pend°)) (ids I)) ∧
  ∀ Q : Rel .long V, Q = (antiJoin (pend°) (idU (Rel.key el)))° →
    P.n.toNat + Q.n.toNat < USize.size ∧
    ∃ (hNk : ((#[⟨P.n, P.key⟩, ⟨Q.n, Q.key⟩] : Array (Part .long)).toList.map
        fun c : Part .long => c.1.toNat).sum < USize.size)
      (hNv : ((#[⟨P.n, P.val⟩, ⟨Q.n, Q.val⟩] : Array (Part V)).toList.map fun c : Part V => c.1.toNat).sum <
        USize.size),
      Vals.RazeFits .long P.key Q.key ∧ Vals.RazeFits V P.val Q.val ∧
      Obj.CodesFit .long (#v[⟨(PQ(.long, V)).n, (PQ(.long, V)).key⟩] : Vector (Part .long) 1) ∧
      V.CodesFit (#v[⟨(PQ(.long, V)).n, (PQ(.long, V)).val⟩] : Vector (Part V) 1) ∧
      Vals.PickFits .long (PQ(.long, V)).key (ids nubI(.long, V, PQ(.long, V))) ∧
      Vals.PickFits V (PQ(.long, V)).val (ids nubI(.long, V, PQ(.long, V)))

/-- **The rounds' invariant**: after `j` rounds from `(pend₀, 𝟘, 0)` the counter is `j`, `out` holds the pairs of
    the `i`-th state (`i < j`) whose row has no element in round `i`, and each state is the step on the one
    before, read in `Rel(Set)`. Hypotheses: `round_rep`'s at every round (`hR`), each round's values bound by
    their equations. -/
theorem rounds_rep {E V : Obj} (pend₀ : Rel .long V) (step : Rel .long E → Rel .long V → Rel .long V)
    (elK : Nat → Rel .long E)
    (f : Rel .long V × Rel .long V × Nat → Rel .long V × Rel .long V × Nat) (hf : ∀ st, f st = rnd(st))
    (hR : ∀ i (el : Rel .long E) (pend P S : Rel .long V), el = elK i → pend = (f^[i] (pend₀, Alg.zero, 0)).1 →
      P = (f^[i] (pend₀, Alg.zero, 0)).2.1 → S = step el pend → roundOK) :
    ∀ j, (f^[j] (pend₀, Alg.zero, 0)).2.2 = j ∧
      rep (f^[j + 1] (pend₀, Alg.zero, 0)).1 = rep (step (elK j) (f^[j] (pend₀, Alg.zero, 0)).1) ∧
      ∀ r v, rep (f^[j] (pend₀, Alg.zero, 0)).2.1 r v ↔
        ∃ i < j, rep (f^[i] (pend₀, Alg.zero, 0)).1 r v ∧ ¬ ∃ e, rep (elK i) r e := by
  -- round `j` read back, once the counter is `j`
  have one : ∀ j, (f^[j] (pend₀, Alg.zero, 0)).2.2 = j →
      rep (f^[j + 1] (pend₀, Alg.zero, 0)).1 = rep (step (elK j) (f^[j] (pend₀, Alg.zero, 0)).1) ∧
      ∀ r v, rep (f^[j + 1] (pend₀, Alg.zero, 0)).2.1 r v ↔ rep (f^[j] (pend₀, Alg.zero, 0)).2.1 r v ∨
        (rep (f^[j] (pend₀, Alg.zero, 0)).1 r v ∧ ¬ ∃ e, rep (elK j) r e) := by
    intro j hk
    obtain ⟨hSK, hSV, hSk, hSv, hjf, hJ, hQ⟩ := hR j _ _ _ _ rfl rfl rfl rfl
    obtain ⟨hJk, hJv⟩ := hJ _ rfl _ rfl
    obtain ⟨hU, hNk, hNv, hFk, hFv, hUK, hUV, hUk, hUv⟩ := hQ _ rfl
    have h := round_rep (elK j) _ _ _ hSK hSV hSk hSv _ rfl hjf _ rfl hJk hJv _ rfl hU hNk hNv hFk hFv hUK hUV
      hUk hUv
    have e : f^[j + 1] (pend₀, Alg.zero, 0) = rnd(f^[j] (pend₀, Alg.zero, 0)) := hf _
    rw [e, hk]
    exact h
  intro j
  induction j with
  | zero =>
    refine ⟨rfl, (one 0 rfl).1, fun r v => ⟨fun ⟨i, _⟩ => i.elim0, fun ⟨_, hi, _⟩ => absurd hi (Nat.not_lt_zero _)⟩⟩
  | succ j ih =>
    obtain ⟨hk, -, hout⟩ := ih
    have hk' : (f^[j + 1] (pend₀, Alg.zero, 0)).2.2 = j + 1 := by
      have e : f^[j + 1] (pend₀, Alg.zero, 0) = rnd(f^[j] (pend₀, Alg.zero, 0)) := hf _
      rw [e, hk]
    refine ⟨hk', (one (j + 1) hk').1, fun r v => ((one j hk).2 r v).trans ?_⟩
    rw [hout]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨j, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr h

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.Rep.round_rep
#print axioms LeetQ.Rel.Rep.iter_stop
#print axioms LeetQ.Rel.Rep.foldRows_iter
#print axioms LeetQ.Rel.Rep.rounds_rep
