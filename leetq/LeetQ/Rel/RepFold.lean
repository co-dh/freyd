/-
  The fold ops of `Alg` read back. `fold`, `foldOn`, `map`, … all run `foldRows`: rounds that pair each row still
  pending with its element `k` from the end, hand both to the step, `nub` the result, and move the rows that have
  no element `k` to `out`. This file reads one round in `Rel(Set)` and the rounds' `out` by induction.
-/
import LeetQ.Rel.RepDiv
import LeetQ.Rel.KernelWF.FoldSpec
import LeetQ.Rel.RepLambda
import LeetQ.Rel.RepMem

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF
-- `codesOK` is `RepOps`' (`OpsN`); the fold notations below use it
open OpsN

/-! The fold notations, one home: `open FoldN OpsN` in every file that states a fold read-back (they expand to
    `OpsN`'s `codesOK`, `c1`, `nubI`, `PQ`). Unhygienic: they
    capture `E`, `V`, `P`, `Q`, `S`, `el`, `pend`, `step`, `elK`, `Sf`, `hU` at the use site. -/
namespace FoldN

-- the parts `antiJoin pend° (idU el.key)` codes: the rows of `pend`, the rows of `el`
set_option hygiene false in
scoped notation "jparts" => (#v[⟨Rel.n (pend°), Rel.val (pend°)⟩,
  ⟨Rel.n (idU (Rel.key el)), Rel.val (idU (Rel.key el))⟩] : Vector (Part .long) 2)

/-- `f^[j]`, `f` applied `j` times (core's `Nat.repeat`, outermost application last). -/
scoped notation:max f "^[" n "]" => Nat.repeat f n

-- `foldRows`' element of round `k`: each row longer than `k` to its element `k` from the end
set_option hygiene false in
scoped notation "elR(" ids ", " k ")" =>
  (let s := slicesOf (Rel.val ids)
   let ends := add (Rel.n ids) s.1 s.2
   let a := whereBits (Rel.n ids) (Ew.cmp Ew.gt Ew.i64 Ew.va s.2 (one (k).toUInt64) (Rel.n ids))
   longCount "foldRows" a fun r hr =>
     let pos := Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul (gather 8 ends a) (one ((k) + 1).toUInt64) r
     (⟨r, Vals.pick .long (Rel.key ids) a r hr, Vals.pick _ (Rel.val ids).2.2.2 pos r (len_val ..)⟩ : Rel .long _))

-- `foldRows`' round, its element bound to `elK`: `round_rep`'s `S.nub` and `P ∪ Q`
set_option hygiene false in
scoped notation "rnd(" st ")" => ((step (elK (st).2.2) (st).1).nub,
  (st).2.1 ∪ (antiJoin ((st).1°) (idU (Rel.key (elK (st).2.2))))°, (st).2.2 + 1)

-- `round_rep`'s hypotheses at `el`, `pend`, `P`, `S`, its bound value `Q` quantified with its equation;
-- `roundAt(V)` names the value object, for a fold whose `V` is a composite such as `.arr B`
set_option hygiene false in
scoped notation "roundAt(" V ")" =>
  Obj.CodesFit V (#v[⟨S.n, S.val⟩] : Vector (Part V) 1) ∧ Vals.PickFits V S.val (List.range S.n.toNat) ∧
  ((jparts).toList.map (·.1.toNat)).sum < USize.size ∧
  Vals.PickFits V (Rel.key (pend°)) (List.range pend.n.toNat) ∧
  ∀ Q : Rel .long V, Q = (antiJoin (pend°) (idU (Rel.key el)))° →
    ∃ hU : P.n.toNat + Q.n.toNat < USize.size,
      Vals.RazeFits V P.val Q.val ∧
      Obj.CodesFit V (#v[⟨(PQ(.long, V)).n, (PQ(.long, V)).val⟩] : Vector (Part V) 1) ∧
      Vals.PickFits V (PQ(.long, V)).val (List.range (PQ(.long, V)).n.toNat)
set_option hygiene false in
scoped notation "roundOK" => roundAt(V)

-- the parts `pair R S` codes (both keys), and the parts `R ≫ S` codes (`R`'s values, `S`'s keys)
set_option hygiene false in
scoped notation "kp2(" R ", " S ")" => (#v[⟨Rel.n R, Rel.key R⟩, ⟨Rel.n S, Rel.key S⟩] : Vector (Part .long) 2)
set_option hygiene false in
scoped notation "vk2(" R ", " S ")" =>
  (#v[⟨Rel.n R, Rel.val R⟩, ⟨Rel.n S, Rel.key S⟩] : Vector (Part (.prod E V)) 2)
-- the parts `≫` codes when a relation into `.long` meets one out of it (`R`'s values, `S`'s keys)
set_option hygiene false in
scoped notation "ck2(" R ", " S ")" => (#v[⟨Rel.n R, Rel.val R⟩, ⟨Rel.n S, Rel.key S⟩] : Vector (Part .long) 2)
-- the row pairs `join` matches on the codes `cs` of rows of `R` and of `S`, and their count. The index proofs
-- are terms: a `by decide` here is elaborated against the whole context, so each hypothesis grew the next's cost
set_option hygiene false in
scoped notation "mpairs(" cs ", " R ", " S ")" => ((List.range (Rel.n R).toNat).flatMap fun i =>
  ((List.range (Rel.n S).toNat).filter fun j => Column.idAt (cs[1]'Nat.one_lt_two).b (cs[1]'Nat.one_lt_two).w j ==
    Column.idAt (cs[0]'Nat.zero_lt_two).b (cs[0]'Nat.zero_lt_two).w i).map (i, ·))

-- `step_rep`'s hypotheses at `el`, `pend`, its bound values `kc`, `P` quantified with their equations; `J` the
-- rest (`stepJ`), at the step relation `S`: one relation (`stepOK`), or `Sf` at the round's pairs (`stepOn`).
-- `el.n + pend.n` stays a hypothesis: `pend` is the step's output, which no input count bounds
-- (`codesOK_long2` derives the codes from it)
set_option hygiene false in
scoped notation "stepK(" J ")" =>
  ∀ kc : Vector Code 2, kc = Obj.codes .long kp2(el, pend) →
    (Rel.n el).toNat + (Rel.n pend).toNat < USize.size ∧ (Rel.n pend).toNat < 2 ^ 63 ∧
    (Rel.n el).toNat * (Rel.n pend).toNat < min (2 ^ 63) USize.size ∧ Vals.PickFits .long (Rel.key el) ((mpairs(kc, el, pend)).map Prod.fst) ∧
    Vals.PickFits E (Rel.val el) ((mpairs(kc, el, pend)).map Prod.fst) ∧
    Vals.PickFits V (Rel.val pend) ((mpairs(kc, el, pend)).map Prod.snd) ∧
    ∀ P : Rel .long (.prod E V), P = pair el pend → J
set_option hygiene false in
scoped notation "stepJ(" S ")" =>
  ∀ jc : Vector Code 2, jc = Obj.codes (.prod E V) vk2(P, S) →
    codesOK(jc, vk2(P, S)) ∧ (Rel.n S).toNat < 2 ^ 63 ∧ (Rel.n P).toNat * (Rel.n S).toNat < min (2 ^ 63) USize.size ∧
    Vals.PickFits .long (Rel.key P) ((mpairs(jc, P, S)).map Prod.fst) ∧
    Vals.PickFits V (Rel.val S) ((mpairs(jc, P, S)).map Prod.snd)
set_option hygiene false in
scoped notation "stepOK" => stepK(stepJ(S))
set_option hygiene false in
scoped notation "stepOn" => stepK(∀ S : Rel (.prod E V) V, S = Sf (ran P) → stepJ(S))

end FoldN

open FoldN

/-- **Two `.long` parts' codes are faithful and well formed on their summed count alone** (`codesFit_atom_count`):
    `rep_pair` and `rep_comp` on `.long` keys need of their codes only that the two counts added fit a `USize`. -/
theorem codesOK_long2 {n m : USize} (x : Vals .long n) (y : Vals .long m) (hN : n.toNat + m.toNat < USize.size) :
    codesOK(Obj.codes .long (#v[⟨n, x⟩, ⟨m, y⟩] : Vector (Part .long) 2),
      (#v[⟨n, x⟩, ⟨m, y⟩] : Vector (Part .long) 2)) :=
  (codes_faithful_wf .long _ (codesFit_atom_count _ (by simpa using hN) (.inr (.inl rfl)))).1

/-- **One round of `foldRows`, read back**: the new state `S.nub` (`S` the step's result) is `S`, and the new
    `out`, `P ∪ (antiJoin pend° (idU el.key))°`, adds to `P` the pairs of `pend` whose row has no element this
    round. `antiJoin`'s and `∪`'s intermediate values are bound by their defining equations (`hQ`).
    Hypotheses: `Obj.CodesFit` of every coded part, `Vals.PickFits` where a part is picked, the counts fit. -/
theorem round_rep {E V : Obj} (el : Rel .long E) (pend P S : Rel .long V)
    (hSV : V.CodesFit (#v[⟨S.n, S.val⟩] : Vector (Part V) 1))
    (hSv : Vals.PickFits V S.val (List.range S.n.toNat))
    (hjf : ((jparts).toList.map (·.1.toNat)).sum < USize.size)
    (hJk : Vals.PickFits V (Rel.key (pend°)) (List.range pend.n.toNat))
    (Q : Rel .long V) (hQ : Q = (antiJoin (pend°) (idU (Rel.key el)))°)
    (hU : P.n.toNat + Q.n.toNat < USize.size)
    (hFv : Vals.RazeFits V P.val Q.val)
    (hUV : V.CodesFit (#v[⟨(PQ(.long, V)).n, (PQ(.long, V)).val⟩] : Vector (Part V) 1))
    (hUv : Vals.PickFits V (PQ(.long, V)).val (List.range (PQ(.long, V)).n.toNat)) :
    rep (Rel.nub S) = rep S ∧
      ∀ r v, rep (P ∪ Q) r v ↔ rep P r v ∨ (rep pend r v ∧ ¬ ∃ e, rep el r e) := by
  -- a one-part `.long` side fits outright (`codesFit_atom_one`), and is picked outright at its rows (`pickFits_atom`)
  have hr : ∀ {n : USize} (x : Vals .long n), Vals.PickFits .long x (List.range n.toNat) :=
    fun x => pickFits_atom x fun _ h => List.mem_range.1 h
  refine ⟨rep_nub S (one_ok _ (codesFit_atom_one _ (.inl (Option.some_ne_none _)))) (one_ok _ hSV) (hr _) hSv,
    fun r v => ?_⟩
  rw [rep_union_full P Q hU (razeFits_atom_count _ _ hU (by decide) rfl) hFv (one_ok _ (codesFit_atom_one _ (.inl (Option.some_ne_none _))))
    (one_ok _ hUV) (hr _) hUv]
  show rep P r v ∨ rep Q r v ↔ _
  subst hQ
  have hA := congrFun (congrFun (rep_antiJoin (pend°) (idU (Rel.key el))
    (codes_faithful_wf .long _ (codesFit_atom_count _ hjf (.inr (.inl rfl)))).1 hJk (hr _)) v) r
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

/-- **Round `k`'s element, read back**: row `r` of `ids` to its array's element `k` from the end, at the rows
    whose array is longer than `k`. The rows longer than `k` (`a`) and their elements' payload positions (`pos`)
    are bound by their equations. Hypotheses: the payload count and `k` below `2^63`, `Vals.PickFits` where the
    key and the payload are picked. -/
theorem rep_elR {E : Obj} (ids : Rel .long (.arr E)) (k : Nat) (hk : k < 2 ^ 63)
    (hp : (Rel.val ids).1.toNat < 2 ^ 63) (a : ByteArray)
    (ha : a = whereBits (Rel.n ids)
      (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf (Rel.val ids)).2 (one k.toUInt64) (Rel.n ids)))
    (pos : ByteArray) (hpos : pos = Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul
      (gather 8 (add (Rel.n ids) (slicesOf (Rel.val ids)).1 (slicesOf (Rel.val ids)).2) a)
      (one (k + 1).toUInt64) (len a).toUSize)
    (hKf : Vals.PickFits .long (Rel.key ids)
      ((List.range (len a)).map fun q => (Column.bitsAt a (q * 8) 8).toNat))
    (hVf : Vals.PickFits E (Rel.val ids).2.2.2
      ((List.range (len a)).map fun q => (Column.bitsAt pos (q * 8) 8).toNat)) :
    ∀ r x, rep elR(ids, k) r x ↔ ∃ i, Vals.row (Rel.key ids) i = r ∧
      ∃ hl : k < (Vals.row (Rel.val ids) i).length,
        x = (Vals.row (Rel.val ids) i)[(Vals.row (Rel.val ids) i).length - 1 - k]'(by omega) := by
  intro r x
  have hlen : len a < USize.size := by
    rw [ha]; exact Nat.lt_of_le_of_lt (len_whereBits_le _ _) (Rel.n ids).toNat_lt_size
  have hm : ((len a).toUSize).toNat = len a := USize.toNat_ofNat_of_lt' hlen
  have hR := fun i (hi : i < (Rel.n ids).toNat) => slicesOf_row (Rel.val ids) hp hi
  have hA := whereGt_ids (Rel.n ids) (slicesOf (Rel.val ids)).2 hk fun i hi => by have := (hR i hi).1; omega
  rw [← ha] at hA
  have hmem : ∀ i, i ∈ QLean.Verify.ids a ↔
      i < (Rel.n ids).toNat ∧ k < (Column.bitsAt (slicesOf (Rel.val ids)).2 (i * 8) 8).toNat := fun i => by
    rw [hA, List.mem_filter, List.mem_range, decide_eq_true_iff]
  have hP2 : len pos = ((len a).toUSize).toNat := by rw [hpos]; exact len_val ..
  -- the `q`-th row of the round's element, at the row `a[q]` of `ids`
  have hq : ∀ (q : Nat) (hq : q < len a) (h1 : len a = ((len a).toUSize).toNat)
      (h2 : len pos = ((len a).toUSize).toNat),
      ∃ (hi : (Column.bitsAt a (q * 8) 8).toNat < (Rel.n ids).toNat),
        k < (Vals.row (Rel.val ids) ⟨_, hi⟩).length ∧
        Vals.row (Vals.pick .long (Rel.key ids) a _ h1) ⟨q, by omega⟩ = Vals.row (Rel.key ids) ⟨_, hi⟩ ∧
        ∀ hl : k < (Vals.row (Rel.val ids) ⟨_, hi⟩).length,
          Vals.row (Vals.pick E (Rel.val ids).2.2.2 pos _ h2) ⟨q, by omega⟩ =
            (Vals.row (Rel.val ids) ⟨_, hi⟩)[(Vals.row (Rel.val ids) ⟨_, hi⟩).length - 1 - k]'(by omega) := by
    intro q hq h1 h2
    have hin : (Column.bitsAt a (q * 8) 8).toNat ∈ QLean.Verify.ids a := by
      have hq' : q < (QLean.Verify.ids a).length := by rw [← len_eq_ids]; exact hq
      rw [← ids_getElem hq']; exact List.getElem_mem hq'
    obtain ⟨hi, hki⟩ := (hmem _).1 hin
    obtain ⟨hLC, hln, hget⟩ := hR _ hi
    refine ⟨hi, by rw [hln]; exact hki, ?_, fun hl => ?_⟩
    · rw [pick_row .long (Rel.key ids) a _ h1 (by rw [← h1]; exact hKf), dif_pos hi]
    · rw [pick_row E (Rel.val ids).2.2.2 pos _ h2 (by rw [← h1]; exact hVf)]
      have hend := add_get (n := Rel.n ids) (a := (slicesOf (Rel.val ids)).1) (b := (slicesOf (Rel.val ids)).2)
        hi (by omega)
      have hg : (Column.bitsAt (gather 8 (add (Rel.n ids) (slicesOf (Rel.val ids)).1 (slicesOf (Rel.val ids)).2) a)
          (q * 8) 8).toNat = (Column.bitsAt (slicesOf (Rel.val ids)).1 ((Column.bitsAt a (q * 8) 8).toNat * 8) 8).toNat +
            (Column.bitsAt (slicesOf (Rel.val ids)).2 ((Column.bitsAt a (q * 8) 8).toNat * 8) 8).toNat := by
        rw [gather8_get hq (by unfold add; rw [len_val]; exact hi)]; exact hend
      have hP : (Column.bitsAt pos (q * 8) 8).toNat =
          (Column.bitsAt (slicesOf (Rel.val ids)).1 ((Column.bitsAt a (q * 8) 8).toNat * 8) 8).toNat +
            (Column.bitsAt (slicesOf (Rel.val ids)).2 ((Column.bitsAt a (q * 8) 8).toNat * 8) 8).toNat - (k + 1) := by
        rw [hpos, subConst_get (by omega) (by rw [hg]; omega) (by rw [hg]; omega), hg]
      rw [dif_pos (by rw [hP]; omega), hget _ (by omega) (by rw [hln]; omega)]
      refine congrArg (Vals.row (Rel.val ids).2.2.2) (Fin.ext ?_)
      show (Column.bitsAt pos (q * 8) 8).toNat = _ + ((Vals.row (Rel.val ids) ⟨_, hi⟩).length - 1 - k)
      rw [hP, hln]; omega
  subst ha hpos
  dsimp only
  rw [longCount_eq _ _ _ hlen]
  show (∃ q, _ ∧ _) ↔ _
  constructor
  · rintro ⟨q, hr, hx⟩
    obtain ⟨hi, hki, hK, hV⟩ := hq q.1 (Nat.lt_of_lt_of_eq q.2 hm) hm.symm hP2
    exact ⟨⟨_, hi⟩, hK.symm.trans hr, hki, hx.symm.trans (hV hki)⟩
  · rintro ⟨⟨i, hi⟩, hr, hl, hx⟩
    have hin := (hmem i).2 ⟨hi, by rw [← (hR i hi).2.1]; exact hl⟩
    obtain ⟨q, hq', hqe⟩ := List.getElem_of_mem hin
    rw [ids_getElem hq'] at hqe
    have hq'' := Nat.lt_of_lt_of_eq hq' (len_eq_ids _).symm
    obtain ⟨hi', hki, hK, hV⟩ := hq q hq'' hm.symm hP2
    subst hqe
    exact ⟨⟨q, Nat.lt_of_lt_of_eq hq'' hm.symm⟩, hK.trans hr, (hV hl).trans hx.symm⟩

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
    obtain ⟨hSV, hSv, hjf, hJk, hQ⟩ := hR j _ _ _ _ rfl rfl rfl rfl
    obtain ⟨hU, hFv, hUV, hUv⟩ := hQ _ rfl
    have h := round_rep (elK j) _ _ _ hSV hSv hjf hJk _ rfl hU hFv hUV hUv
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


/-- **A fold step, read back**: `demandStep Sf` takes row `r`'s element `e` and value `u` to each `v` with
    `(e, u) S v`, `S = Sf (ran P)` the family at the pairs `P` the round meets. The codes `kc` of `pair`, the pair
    `P`, the step relation `S` and the codes `jc` of `P ≫ S` are bound by their equations. Hypotheses: `rep_pair`'s
    at `el`, `pend` (`hk…`) and `rep_comp`'s at `P`, `S` (`hj…`). -/
theorem step_rep {E V : Obj} (el : Rel .long E) (pend : Rel .long V)
    (Sf : Rel (.prod E V) (.prod E V) → Rel (.prod E V) V)
    (kc : Vector Code 2) (hkc : kc = Obj.codes .long kp2(el, pend))
    (hkO : (Rel.n el).toNat + (Rel.n pend).toNat < USize.size)
    (hkn : (Rel.n pend).toNat < 2 ^ 63) (hkM : (Rel.n el).toNat * (Rel.n pend).toNat < min (2 ^ 63) USize.size)
    (hkA : Vals.PickFits .long (Rel.key el) ((mpairs(kc, el, pend)).map Prod.fst))
    (hkB : Vals.PickFits E (Rel.val el) ((mpairs(kc, el, pend)).map Prod.fst))
    (hkC : Vals.PickFits V (Rel.val pend) ((mpairs(kc, el, pend)).map Prod.snd))
    (P : Rel .long (.prod E V)) (hP : P = pair el pend) (S : Rel (.prod E V) V) (hSP : S = Sf (ran P))
    (jc : Vector Code 2) (hjc : jc = Obj.codes (.prod E V) vk2(P, S)) (hjO : codesOK(jc, vk2(P, S)))
    (hjn : (Rel.n S).toNat < 2 ^ 63) (hjM : (Rel.n P).toNat * (Rel.n S).toNat < min (2 ^ 63) USize.size)
    (hjA : Vals.PickFits .long (Rel.key P) ((mpairs(jc, P, S)).map Prod.fst))
    (hjC : Vals.PickFits V (Rel.val S) ((mpairs(jc, P, S)).map Prod.snd)) :
    ∀ r v, rep (demandStep Sf el pend) r v ↔ ∃ e u, rep el r e ∧ rep pend r u ∧ rep S (e, u) v := by
  subst hkc hjc
  have h1 := rep_pair el pend (codesOK_long2 _ _ hkO) hkn hkM hkA hkB hkC
  subst hP
  have h2 := rep_comp (pair el pend) S hjO hjn hjM hjA hjC
  subst hSP
  intro r v
  show rep (pair el pend ≫ Sf (ran (pair el pend))) r v ↔ _
  rw [h2]
  constructor
  · rintro ⟨⟨e, u⟩, hp, hs⟩
    rw [h1] at hp
    exact ⟨e, u, hp.1, hp.2, hs⟩
  · rintro ⟨e, u, he, hu, hs⟩
    refine ⟨(e, u), ?_, hs⟩
    rw [h1]; exact ⟨he, hu⟩

/-- **The rounds' states and `out`, in `Set`**: `st i r` holds the values row `r` reaches after `i` rounds, each
    round taking `S` on the row's element `i` from the end of `xs r`, and past the row's length keeping the state
    when `keep` holds (`hst`, the states' defining recurrence: `keep` false for `demandStep`, true for a step
    `… ∪ pend`). Up to the row's length a state is a chain `ys` of `S`-steps from a seed in `st 0` along the last
    `i` elements; past the length it is the state at the length if `keep`, else empty; and `out` at a stop `j`
    past the length, or where the row's state `j` is empty, is the state at the length — the stop does not
    matter. -/
theorem rounds_closed_keep {K E V : Type} (xs : K → List E) (S : Nat → E × V → V → Prop)
    (st : Nat → K → V → Prop) (keep : Prop)
    (hst : ∀ i r v, st (i + 1) r v ↔
      (∃ e u, (∃ hl : i < (xs r).length, e = (xs r)[(xs r).length - 1 - i]'(by omega)) ∧ st i r u ∧
        S i (e, u) v) ∨ ((xs r).length ≤ i ∧ keep ∧ st i r v)) :
    (∀ i r v (hi : i ≤ (xs r).length), st i r v ↔ ∃ ys : List V, ∃ hy : ys.length = i + 1,
      st 0 r (ys[i]'(by omega)) ∧
      (∀ t (ht : t < i),
        S (i - 1 - t) ((xs r)[(xs r).length - i + t]'(by omega), ys[t + 1]'(by omega)) (ys[t]'(by omega))) ∧
      v = ys[0]'(by omega)) ∧
    (∀ i r v, (xs r).length < i → (st i r v ↔ keep ∧ st (xs r).length r v)) ∧
    (∀ j r v, ((xs r).length < j ∨ ∀ u, ¬ st j r u) →
      ((∃ i < j, st i r v ∧ ¬ ∃ e, ∃ hl : i < (xs r).length, e = (xs r)[(xs r).length - 1 - i]'(by omega)) ↔
        st (xs r).length r v)) := by
  have gi : ∀ (l : List E) a b (ha : a < l.length) (hb : b < l.length), a = b → l[a] = l[b] := by
    intro l a b ha hb h; subst h; rfl
  have gs : ∀ a b, a = b → ∀ p w, S a p w → S b p w := by intro a b h; subst h; exact fun _ _ x => x
  have pastS : ∀ i r v, (xs r).length ≤ i → (st (i + 1) r v ↔ keep ∧ st i r v) := by
    intro i r v hL
    rw [hst]
    constructor
    · rintro (⟨_, _, ⟨hl, _⟩, _⟩ | ⟨-, h⟩)
      · omega
      · exact h
    · intro h; exact Or.inr ⟨hL, h⟩
  have pastD : ∀ d r v, st ((xs r).length + 1 + d) r v ↔ keep ∧ st (xs r).length r v := by
    intro d
    induction d with
    | zero => intro r v; exact pastS _ r v (Nat.le_refl _)
    | succ d ih =>
      intro r v
      refine (pastS ((xs r).length + 1 + d) r v (by omega)).trans ?_
      rw [ih]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨h.1, h⟩⟩
  have past : ∀ i r v, (xs r).length < i → (st i r v ↔ keep ∧ st (xs r).length r v) := by
    intro i r v hi
    obtain ⟨d, hd⟩ : ∃ d, i = (xs r).length + 1 + d := ⟨i - (xs r).length - 1, by omega⟩
    rw [hd]; exact pastD d r v
  have down : ∀ j d r v, st (j + d) r v → ∃ u, st j r u := by
    intro j d
    induction d with
    | zero => intro r v h; exact ⟨v, h⟩
    | succ d ih =>
      intro r v h
      obtain ⟨_, u, _, hu, _⟩ | ⟨_, _, hu⟩ := (hst (j + d) r v).1 h
      · exact ih r u hu
      · exact ih r v hu
  have closed : ∀ i r v (hi : i ≤ (xs r).length), st i r v ↔ ∃ ys : List V, ∃ hy : ys.length = i + 1,
      st 0 r (ys[i]'(by omega)) ∧
      (∀ t (ht : t < i),
        S (i - 1 - t) ((xs r)[(xs r).length - i + t]'(by omega), ys[t + 1]'(by omega)) (ys[t]'(by omega))) ∧
      v = ys[0]'(by omega) := by
    intro i
    induction i with
    | zero =>
      intro r v _
      refine ⟨fun h => ⟨[v], rfl, h, fun t ht => absurd ht (Nat.not_lt_zero _), rfl⟩, ?_⟩
      rintro ⟨ys, hy, h0, -, rfl⟩; exact h0
    | succ i ih =>
      intro r v hi
      have hn : ¬ ((xs r).length ≤ i ∧ keep ∧ st i r v) := fun h => absurd h.1 (by omega)
      rw [hst, or_iff_left hn]
      constructor
      · rintro ⟨e, u, ⟨hl, rfl⟩, hu, hS⟩
        obtain ⟨ys, hy, h0, hstep, rfl⟩ := (ih r u (by omega)).1 hu
        refine ⟨v :: ys, by simp [hy], by simpa using h0, fun t ht => ?_, rfl⟩
        cases t with
        | zero =>
          simp only [List.getElem_cons_succ, List.getElem_cons_zero]
          refine gs i _ (by omega) _ _ ?_
          rw [gi (xs r) _ ((xs r).length - 1 - i) _ (by omega) (by omega)]; exact hS
        | succ t =>
          have h := hstep t (by omega)
          simp only [List.getElem_cons_succ]
          refine gs (i - 1 - t) _ (by omega) _ _ ?_
          rw [gi (xs r) _ ((xs r).length - i + t) _ (by omega) (by omega)]; exact h
      · rintro ⟨ys, hy, h0, hstep, hv⟩
        rcases ys with _ | ⟨w, ys⟩
        · simp at hy
        have hy' : ys.length = i + 1 := by simp at hy; omega
        subst hv
        refine ⟨(xs r)[(xs r).length - 1 - i]'(by omega), ys[0]'(by omega), ⟨by omega, rfl⟩,
          (ih r _ (by omega)).2 ⟨ys, hy', by simpa using h0, fun t ht => ?_, rfl⟩, ?_⟩
        · have h := hstep (t + 1) (by omega)
          simp only [List.getElem_cons_succ] at h
          refine gs (i + 1 - 1 - (t + 1)) _ (by omega) _ _ ?_
          rw [gi (xs r) _ ((xs r).length - (i + 1) + (t + 1)) _ (by omega) (by omega)]; exact h
        · have h := hstep 0 (by omega)
          simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
          refine gs (i + 1 - 1 - 0) _ (by omega) _ _ ?_
          rw [gi (xs r) _ ((xs r).length - (i + 1) + 0) _ (by omega) (by omega)]; exact h
  refine ⟨closed, past, fun j r v hj => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨i, hij, hs, hn⟩
    have hL : (xs r).length ≤ i := Nat.le_of_not_lt fun hl => hn ⟨_, hl, rfl⟩
    rcases Nat.lt_or_eq_of_le hL with hlt | heq
    · exact ((past i r v hlt).1 hs).2
    · rw [heq]; exact hs
  · have hLj : (xs r).length < j := by
      rcases hj with hj | hj
      · exact hj
      · refine Nat.lt_of_not_le fun hle => ?_
        obtain ⟨u, hu⟩ := down j ((xs r).length - j) r v (by rw [Nat.add_sub_of_le hle]; exact h)
        exact hj u hu
    exact ⟨_, hLj, h, fun ⟨_, hl, _⟩ => Nat.lt_irrefl _ hl⟩

/-- **`rounds_closed_keep` with no state kept past the length** (`demandStep`): the state there is empty. -/
theorem rounds_closed {K E V : Type} (xs : K → List E) (S : Nat → E × V → V → Prop) (st : Nat → K → V → Prop)
    (hst : ∀ i r v, st (i + 1) r v ↔
      ∃ e u, (∃ hl : i < (xs r).length, e = (xs r)[(xs r).length - 1 - i]'(by omega)) ∧ st i r u ∧ S i (e, u) v) :
    (∀ i r v (hi : i ≤ (xs r).length), st i r v ↔ ∃ ys : List V, ∃ hy : ys.length = i + 1,
      st 0 r (ys[i]'(by omega)) ∧
      (∀ t (ht : t < i),
        S (i - 1 - t) ((xs r)[(xs r).length - i + t]'(by omega), ys[t + 1]'(by omega)) (ys[t]'(by omega))) ∧
      v = ys[0]'(by omega)) ∧
    (∀ i r v, (xs r).length < i → ¬ st i r v) ∧
    (∀ j r v, ((xs r).length < j ∨ ∀ u, ¬ st j r u) →
      ((∃ i < j, st i r v ∧ ¬ ∃ e, ∃ hl : i < (xs r).length, e = (xs r)[(xs r).length - 1 - i]'(by omega)) ↔
        st (xs r).length r v)) := by
  obtain ⟨closed, past, outc⟩ := rounds_closed_keep xs S st False fun i r v =>
    (hst i r v).trans (or_iff_left fun h : (xs r).length ≤ i ∧ False ∧ st i r v => h.2.1).symm
  exact ⟨closed, fun i r v hi h => ((past i r v hi).1 h).1, outc⟩

/-- **`foldRows` of any step, read back**: row `r` goes to `v` when a chain `ys` of steps runs along the
    array `xs r` from a value of `pend₀` at `r` to `v`, the step on `(xs r)[t]` taken by `Sr k`, `k` the round
    that meets that element (`|xs r| - 1 - t`, rounds run from the end). Internal: `hel` characterises the
    rounds' elements by `xs` up to the rounds' bound (the payload count), `hlen` bounds every `xs r` by the
    payload, `hS` reads round `i`'s step back as `Sr i` on the row's element and value. `elK`, `f` are bound by
    their equations; `hR` is `round_rep`'s hypotheses at every round. `keep` says the step keeps the state of a
    row that has no element (`… ∪ pend`); `hS`'s second branch is that row's kept state. -/
theorem foldRows_rep_keep {E V : Obj} (X : Rel .long (.arr E)) (pend₀ : Rel .long V)
    (Sr : Nat → E.El × V.El → V.El → Prop)
    (xs : Obj.El .long → List E.El)
    (hel : ∀ k, k ≤ (Rel.val X).1.toNat → ∀ r x, rep elR(X, k) r x ↔
      ∃ hl : k < (xs r).length, x = (xs r)[(xs r).length - 1 - k]'(by omega))
    (hlen : ∀ r, (xs r).length ≤ (Rel.val X).1.toNat)
    (step : Rel .long E → Rel .long V → Rel .long V)
    (elK : Nat → Rel .long E) (hE : ∀ k, elK k = elR(X, k))
    (f : Rel .long V × Rel .long V × Nat → Rel .long V × Rel .long V × Nat) (hf : ∀ st, f st = rnd(st))
    (hR : ∀ i (el : Rel .long E) (pend P S : Rel .long V), el = elK i → pend = (f^[i] (pend₀, Alg.zero, 0)).1 →
      P = (f^[i] (pend₀, Alg.zero, 0)).2.1 → S = step el pend → roundOK)
    (keep : Prop)
    (hS : ∀ i, i ≤ (Rel.val X).1.toNat → ∀ r v, rep (step (elK i) (f^[i] (pend₀, Alg.zero, 0)).1) r v ↔
      (∃ e u, rep (elK i) r e ∧ rep (f^[i] (pend₀, Alg.zero, 0)).1 r u ∧ Sr i (e, u) v) ∨
        (keep ∧ (¬ ∃ e, rep (elK i) r e) ∧ rep (f^[i] (pend₀, Alg.zero, 0)).1 r v)) :
    ∀ r v, rep (foldRows X pend₀ step) r v ↔ ∃ ys : List V.El, ∃ hy : ys.length = (xs r).length + 1,
      rep pend₀ r (ys[(xs r).length]'(by omega)) ∧
      (∀ t (ht : t < (xs r).length),
        Sr ((xs r).length - 1 - t) ((xs r)[t], ys[t + 1]'(by omega)) (ys[t]'(by omega))) ∧
      v = ys[0]'(by omega) := by
  intro r v
  obtain ⟨j, hjN, hfo, hstop⟩ := foldRows_iter X pend₀ step elK hE f hf
  have hrr := rounds_rep pend₀ step elK f hf hR
  have hEl : ∀ i, i ≤ (Rel.val X).1.toNat → ∀ r e, rep (elK i) r e ↔
      ∃ hl : i < (xs r).length, e = (xs r)[(xs r).length - 1 - i]'(by omega) := fun i hi r e => by
    rw [hE]; exact hel i hi r e
  have hnone : ∀ i, i ≤ (Rel.val X).1.toNat → ∀ r, (¬ ∃ e, rep (elK i) r e) ↔ (xs r).length ≤ i :=
    fun i hi r => ⟨fun hn => Nat.le_of_not_lt fun hl => hn ⟨_, (hEl i hi r _).2 ⟨hl, rfl⟩⟩,
      fun hL ⟨e, he⟩ => by obtain ⟨hl, -⟩ := (hEl i hi r e).1 he; omega⟩
  -- the states held at the rounds' bound, where `hel` holds: past it no row has an element, and the state stays
  -- if `keep`, else it is empty
  have hst : ∀ i r v, (rep (f^[min (i + 1) ((Rel.val X).1.toNat + 1)] (pend₀, Alg.zero, 0)).1 r v ∧
      (i + 1 ≤ (Rel.val X).1.toNat + 1 ∨ keep)) ↔ (∃ e u,
      (∃ hl : i < (xs r).length, e = (xs r)[(xs r).length - 1 - i]'(by omega)) ∧
      (rep (f^[min i ((Rel.val X).1.toNat + 1)] (pend₀, Alg.zero, 0)).1 r u ∧
        (i ≤ (Rel.val X).1.toNat + 1 ∨ keep)) ∧ Sr i (e, u) v) ∨
      ((xs r).length ≤ i ∧ keep ∧ (rep (f^[min i ((Rel.val X).1.toNat + 1)] (pend₀, Alg.zero, 0)).1 r v ∧
        (i ≤ (Rel.val X).1.toNat + 1 ∨ keep))) := by
    intro i r v
    by_cases hi : i ≤ (Rel.val X).1.toNat
    · rw [Nat.min_eq_left (by omega : i + 1 ≤ (Rel.val X).1.toNat + 1),
        Nat.min_eq_left (by omega : i ≤ (Rel.val X).1.toNat + 1), (hrr i).2.1, hS i hi r v]
      constructor
      · rintro ⟨⟨e, u, he, hu, hs⟩ | ⟨hk, hn, hu⟩, -⟩
        · exact Or.inl ⟨e, u, (hEl i hi r e).1 he, ⟨hu, Or.inl (by omega)⟩, hs⟩
        · exact Or.inr ⟨(hnone i hi r).1 hn, hk, hu, Or.inl (by omega)⟩
      · rintro (⟨e, u, he, ⟨hu, -⟩, hs⟩ | ⟨hn, hk, hu, -⟩)
        · exact ⟨Or.inl ⟨e, u, (hEl i hi r e).2 he, hu, hs⟩, Or.inl (by omega)⟩
        · exact ⟨Or.inr ⟨hk, (hnone i hi r).2 hn, hu⟩, Or.inl (by omega)⟩
    · rw [Nat.min_eq_right (by omega : (Rel.val X).1.toNat + 1 ≤ i + 1),
        Nat.min_eq_right (by omega : (Rel.val X).1.toNat + 1 ≤ i)]
      constructor
      · rintro ⟨h, hk | hk⟩
        · omega
        · exact Or.inr ⟨by have := hlen r; omega, hk, h, Or.inr hk⟩
      · rintro (⟨_, _, ⟨hl, -⟩, -, -⟩ | ⟨-, hk, h, -⟩)
        · have := hlen r; omega
        · exact ⟨h, Or.inr hk⟩
  obtain ⟨closed, -, outc⟩ := rounds_closed_keep xs Sr
    (fun i r v => rep (f^[min i ((Rel.val X).1.toNat + 1)] (pend₀, Alg.zero, 0)).1 r v ∧
      (i ≤ (Rel.val X).1.toNat + 1 ∨ keep)) keep hst
  have hj : (xs r).length < j ∨ ∀ u, ¬ (rep (f^[min j ((Rel.val X).1.toNat + 1)] (pend₀, Alg.zero, 0)).1 r u ∧
      (j ≤ (Rel.val X).1.toNat + 1 ∨ keep)) := by
    rcases hstop with h | h
    · have := hlen r; omega
    · rw [Nat.min_eq_left hjN]
      refine Or.inr fun u ⟨⟨i, _, _⟩, _⟩ => ?_
      have h0 : (Rel.n (f^[j] (pend₀, Alg.zero, 0)).1).toNat = 0 := by simp [eq_of_beq h]
      exact absurd i.2 (by omega)
  rw [hfo, (hrr j).2.2 r v]
  refine (exists_congr fun i =>
    ⟨fun ⟨hi, h, hn⟩ => ⟨hi, ⟨by rw [Nat.min_eq_left (by omega)]; exact h, Or.inl (by omega)⟩,
        fun ⟨e, he⟩ => hn ⟨e, (hEl i (by omega) r e).2 he⟩⟩,
      fun ⟨hi, ⟨h, _⟩, hn⟩ => ⟨hi, by rw [Nat.min_eq_left (by omega)] at h; exact h,
        fun ⟨e, he⟩ => hn ⟨e, (hEl i (by omega) r e).1 he⟩⟩⟩).trans
    (((outc j r v hj).trans (closed _ r v (Nat.le_refl _))).trans ?_)
  refine exists_congr fun ys => exists_congr fun hy => and_congr
    ⟨fun h => by have h1 := h.1; rw [Nat.zero_min] at h1; exact h1,
      fun h => ⟨by rw [Nat.zero_min]; exact h, Or.inl (Nat.zero_le _)⟩⟩
    (and_congr (forall_congr' fun t => forall_congr' fun ht => ?_) Iff.rfl)
  simp only [Nat.sub_self, Nat.zero_add]

/-- **`foldRows_rep_keep` with no state kept** (`demandStep`, `map`): round `i`'s step meets only the rows that
    have an element. -/
theorem foldRows_rep {E V : Obj} (X : Rel .long (.arr E)) (pend₀ : Rel .long V)
    (Sr : Nat → E.El × V.El → V.El → Prop)
    (xs : Obj.El .long → List E.El)
    (hel : ∀ k, k ≤ (Rel.val X).1.toNat → ∀ r x, rep elR(X, k) r x ↔
      ∃ hl : k < (xs r).length, x = (xs r)[(xs r).length - 1 - k]'(by omega))
    (hlen : ∀ r, (xs r).length ≤ (Rel.val X).1.toNat)
    (step : Rel .long E → Rel .long V → Rel .long V)
    (elK : Nat → Rel .long E) (hE : ∀ k, elK k = elR(X, k))
    (f : Rel .long V × Rel .long V × Nat → Rel .long V × Rel .long V × Nat) (hf : ∀ st, f st = rnd(st))
    (hR : ∀ i (el : Rel .long E) (pend P S : Rel .long V), el = elK i → pend = (f^[i] (pend₀, Alg.zero, 0)).1 →
      P = (f^[i] (pend₀, Alg.zero, 0)).2.1 → S = step el pend → roundOK)
    (hS : ∀ i, i ≤ (Rel.val X).1.toNat → ∀ r v, rep (step (elK i) (f^[i] (pend₀, Alg.zero, 0)).1) r v ↔
      ∃ e u, rep (elK i) r e ∧ rep (f^[i] (pend₀, Alg.zero, 0)).1 r u ∧ Sr i (e, u) v) :
    ∀ r v, rep (foldRows X pend₀ step) r v ↔ ∃ ys : List V.El, ∃ hy : ys.length = (xs r).length + 1,
      rep pend₀ r (ys[(xs r).length]'(by omega)) ∧
      (∀ t (ht : t < (xs r).length),
        Sr ((xs r).length - 1 - t) ((xs r)[t], ys[t + 1]'(by omega)) (ys[t]'(by omega))) ∧
      v = ys[0]'(by omega) :=
  foldRows_rep_keep X pend₀ Sr xs hel hlen step elK hE f hf hR False fun i hi r v =>
    (hS i hi r v).trans (or_iff_left fun h : False ∧ _ => h.1).symm

/-- **`foldBy`, read back**: an array `xs` of `X` goes to `w` when a chain `ys` of steps runs along `xs` from
    a value of `e` (`ys[|xs|]`) to `w` (`ys[0]`), `ys[t+1]` to `ys[t]` on the element `xs[t]` by `Sr k`,
    `k = |xs| - 1 - t` the round that meets `xs[t]` (rounds run from the end). `foldBy` is `T° ≫ F`: `T`
    numbers the arrays of `X`, `F` the rounds from the seed `pend₀ = top T.key e`; `T`, `pend₀`, `elK`, `f`,
    `F`, `jc` are bound by their equations. Hypotheses: `rep_num`'s at `X` (`hn`, `hv`), the payload below
    `2^63` (`hp`), `rep_elR`'s at every round (`hel`), `rep_top`'s (`hN`, `h63`, `hA`, `hB`), `round_rep`'s at
    every round (`hR`), round `i`'s step read back as `Sr i` (`hS`, discharged by each fold's own step lemma),
    `rep_comp`'s at `T°`, `F` (`hj…`). `keep` and `hS`'s second branch as `foldRows_rep_keep`'s. -/
theorem rep_foldBy_keep {E V : Obj} {m n : USize} (e : Vals V m) (X : Vals (.arr E) n)
    (T : Rel .long (.arr E)) (hT : T = num (idU X) 0) (hn : n.toNat < 2 ^ 63)
    (hv : Vals.PickFits (.arr E) X (List.range n.toNat)) (hp : (Rel.val T).1.toNat < 2 ^ 63)
    (hel : ∀ k, k ≤ (Rel.val T).1.toNat → ∀ a : ByteArray, a = whereBits (Rel.n T)
        (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf (Rel.val T)).2 (one k.toUInt64) (Rel.n T)) →
      ∀ pos : ByteArray, pos = Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul
        (gather 8 (add (Rel.n T) (slicesOf (Rel.val T)).1 (slicesOf (Rel.val T)).2) a)
        (one (k + 1).toUInt64) (len a).toUSize →
      Vals.PickFits .long (Rel.key T) ((List.range (len a)).map fun q => (Column.bitsAt a (q * 8) 8).toNat) ∧
      Vals.PickFits E (Rel.val T).2.2.2 ((List.range (len a)).map fun q => (Column.bitsAt pos (q * 8) 8).toNat))
    (pend₀ : Rel .long V) (hpend : pend₀ = top (A := .long) (Rel.key T) e)
    (hN : (Rel.n T).toNat * m.toNat < USize.size) (h63 : (Rel.n T).toNat * m.toNat < 2 ^ 63)
    (hA : Vals.PickFits .long (Rel.key T) ((List.range ((Rel.n T).toNat * m.toNat)).map (· / m.toNat)))
    (hB : Vals.PickFits V e ((List.range ((Rel.n T).toNat * m.toNat)).map (· % m.toNat)))
    (step : Rel .long E → Rel .long V → Rel .long V) (Sr : Nat → E.El × V.El → V.El → Prop)
    (elK : Nat → Rel .long E) (hE : ∀ k, elK k = elR(T, k))
    (f : Rel .long V × Rel .long V × Nat → Rel .long V × Rel .long V × Nat) (hf : ∀ st, f st = rnd(st))
    (hR : ∀ i (el : Rel .long E) (pend P S : Rel .long V), el = elK i → pend = (f^[i] (pend₀, Alg.zero, 0)).1 →
      P = (f^[i] (pend₀, Alg.zero, 0)).2.1 → S = step el pend → roundOK) (keep : Prop)
    (hS : ∀ i, i ≤ (Rel.val T).1.toNat → ∀ r v, rep (step (elK i) (f^[i] (pend₀, Alg.zero, 0)).1) r v ↔
      (∃ e u, rep (elK i) r e ∧ rep (f^[i] (pend₀, Alg.zero, 0)).1 r u ∧ Sr i (e, u) v) ∨
        (keep ∧ (¬ ∃ e, rep (elK i) r e) ∧ rep (f^[i] (pend₀, Alg.zero, 0)).1 r v))
    (F : Rel .long V) (hF : F = foldRows T pend₀ step)
    (jc : Vector Code 2) (hjc : jc = Obj.codes .long ck2(T°, F)) (hjO : codesOK(jc, ck2(T°, F)))
    (hjn : (Rel.n F).toNat < 2 ^ 63) (hjM : (Rel.n (T°)).toNat * (Rel.n F).toNat < min (2 ^ 63) USize.size)
    (hjA : Vals.PickFits (.arr E) (Rel.key (T°)) ((mpairs(jc, T°, F)).map Prod.fst))
    (hjC : Vals.PickFits V (Rel.val F) ((mpairs(jc, T°, F)).map Prod.snd)) :
    ∀ (xs : List E.El) w, rep (foldBy X e step) xs w ↔ (∃ i, X.row i = xs) ∧
      ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
        (∃ p, e.row p = ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm)) ∧
        (∀ t (ht : t < xs.length), Sr (xs.length - 1 - t)
          (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm))
          (ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm))) ∧
        w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm) := by
  -- `T` keys row `i` of `X` by `i`, so it is a function on its keys
  have hnum : ∀ r y, rep T r y ↔ ∃ i : Fin n.toNat, r = Int64.ofNat i.1 ∧ X.row i = y := by
    intro r y; subst hT
    rw [rep_num (idU X) 0 (by simpa using hn) hv r y]
    simp only [USize.toNat_zero, Nat.zero_add]; exact Iff.rfl
  have hfun : ∀ r y y', rep T r y → rep T r y' → y = y' := by
    intro r y y' h h'
    obtain ⟨i, hr, rfl⟩ := (hnum r y).1 h
    obtain ⟨i', hr', rfl⟩ := (hnum r y').1 h'
    have h1 := i.2
    have h2 := i'.2
    have hi := congrArg Int64.toInt (hr.symm.trans hr')
    rw [Int64.toInt_ofNat_of_lt (by omega), Int64.toInt_ofNat_of_lt (by omega)] at hi
    rw [Fin.ext (Int.ofNat_inj.1 hi)]
  -- the array of each key, `[]` off the keys
  obtain ⟨as, has⟩ : ∃ as : Obj.El .long → List E.El,
      ∀ r, (∀ y, rep T r y → as r = y) ∧ ((∀ y, ¬ rep T r y) → as r = []) := by
    classical
    refine ⟨fun r => if h : ∃ y, rep T r y then Classical.choose h else [], fun r => ⟨fun y hy => ?_, fun hn => ?_⟩⟩
    · exact (dif_pos (⟨y, hy⟩ : ∃ y, rep T r y)).trans (hfun r _ _ (Classical.choose_spec _) hy)
    · exact dif_neg fun ⟨y, hy⟩ => hn y hy
  have hel' : ∀ k, k ≤ (Rel.val T).1.toNat → ∀ r x, rep elR(T, k) r x ↔
      ∃ hl : k < (as r).length, x = (as r)[(as r).length - 1 - k]'(by omega) := by
    intro k hk r x
    obtain ⟨hKf, hVf⟩ := hel k hk _ rfl _ rfl
    rw [rep_elR T k (by omega) hp _ rfl _ rfl hKf hVf]
    -- element `k` from the end, moved along an equation of lists
    have key : ∀ L L' : List E.El, L = L' → ((∃ hl : k < L.length, x = L[L.length - 1 - k]'(by omega)) ↔
        ∃ hl : k < L'.length, x = L'[L'.length - 1 - k]'(by omega)) := by
      intro L L' h; subst h; exact Iff.rfl
    constructor
    · rintro ⟨i, hi, hl, hx⟩
      exact (key _ _ ((has r).1 _ ⟨i, hi, rfl⟩)).2 ⟨hl, hx⟩
    · intro h
      by_cases hr : ∃ i, Vals.row (Rel.key T) i = r
      · obtain ⟨i, hi⟩ := hr
        obtain ⟨hl, hx⟩ := (key _ _ ((has r).1 _ ⟨i, hi, rfl⟩)).1 h
        exact ⟨i, hi, hl, hx⟩
      · obtain ⟨hl, -⟩ := (key _ _ ((has r).2 fun y ⟨i, hi, _⟩ => hr ⟨i, hi⟩)).1 h
        exact absurd hl (Nat.not_lt_zero _)
  have hlen : ∀ r, (as r).length ≤ (Rel.val T).1.toNat := by
    intro r
    by_cases hr : ∃ i, Vals.row (Rel.key T) i = r
    · obtain ⟨i, hi⟩ := hr
      rw [(has r).1 _ ⟨i, hi, rfl⟩]
      obtain ⟨h1, h2, -⟩ := slicesOf_row (Rel.val T) hp i.2
      exact Nat.le_trans (Nat.le_of_eq h2) (by omega)
    · rw [(has r).2 fun y ⟨i, hi, _⟩ => hr ⟨i, hi⟩]; exact Nat.zero_le _
  have hFr := foldRows_rep_keep T pend₀ Sr as hel' hlen step elK hE f hf hR keep hS
  have htop : ∀ r u, rep pend₀ r u ↔ (∃ i, Vals.row (Rel.key T) i = r) ∧ ∃ p, e.row p = u := by
    intro r u; subst hpend; rw [rep_top _ _ hN h63 hA hB]
    constructor
    · rintro ⟨_, ⟨rfl, hr⟩, _, -, rfl, hp⟩; exact ⟨hr, hp⟩
    · rintro ⟨hr, hp⟩; exact ⟨r, ⟨rfl, hr⟩, u, trivial, rfl, hp⟩
  have hfold : foldBy X e step = T° ≫ F := by subst hT hF hpend; rfl
  intro xs w
  subst hjc
  rw [hfold, rep_comp (T°) F hjO hjn hjM hjA hjC, rep_conv]
  subst hF
  constructor
  · rintro ⟨r, h1, h2⟩
    have hax := (has r).1 xs h1
    subst hax
    obtain ⟨i, -, hi⟩ := (hnum r _).1 h1
    obtain ⟨ys, hy, h0, hst, hw⟩ := (hFr r w).1 h2
    exact ⟨⟨i, hi⟩, ys, hy, ((htop r _).1 h0).2, hst, hw⟩
  · rintro ⟨⟨i, hi⟩, ys, hy, hp, hst, hw⟩
    have h1 : rep T (Int64.ofNat i.1) xs := (hnum _ _).2 ⟨i, rfl, hi⟩
    have hax := (has _).1 xs h1
    refine ⟨Int64.ofNat i.1, h1, (hFr _ w).2 ?_⟩
    obtain ⟨i', hk, -⟩ := h1
    subst hax
    exact ⟨ys, hy, (htop _ _).2 ⟨⟨i', hk⟩, hp⟩, hst, hw⟩

/-- **`rep_foldBy_keep` with no state kept** (`demandStep`, `map`): round `i`'s step read back as `Sr i` on the
    rows that have an element. -/
theorem rep_foldBy {E V : Obj} {m n : USize} (e : Vals V m) (X : Vals (.arr E) n)
    (T : Rel .long (.arr E)) (hT : T = num (idU X) 0) (hn : n.toNat < 2 ^ 63)
    (hv : Vals.PickFits (.arr E) X (List.range n.toNat)) (hp : (Rel.val T).1.toNat < 2 ^ 63)
    (hel : ∀ k, k ≤ (Rel.val T).1.toNat → ∀ a : ByteArray, a = whereBits (Rel.n T)
        (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf (Rel.val T)).2 (one k.toUInt64) (Rel.n T)) →
      ∀ pos : ByteArray, pos = Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul
        (gather 8 (add (Rel.n T) (slicesOf (Rel.val T)).1 (slicesOf (Rel.val T)).2) a)
        (one (k + 1).toUInt64) (len a).toUSize →
      Vals.PickFits .long (Rel.key T) ((List.range (len a)).map fun q => (Column.bitsAt a (q * 8) 8).toNat) ∧
      Vals.PickFits E (Rel.val T).2.2.2 ((List.range (len a)).map fun q => (Column.bitsAt pos (q * 8) 8).toNat))
    (pend₀ : Rel .long V) (hpend : pend₀ = top (A := .long) (Rel.key T) e)
    (hN : (Rel.n T).toNat * m.toNat < USize.size) (h63 : (Rel.n T).toNat * m.toNat < 2 ^ 63)
    (hA : Vals.PickFits .long (Rel.key T) ((List.range ((Rel.n T).toNat * m.toNat)).map (· / m.toNat)))
    (hB : Vals.PickFits V e ((List.range ((Rel.n T).toNat * m.toNat)).map (· % m.toNat)))
    (step : Rel .long E → Rel .long V → Rel .long V) (Sr : Nat → E.El × V.El → V.El → Prop)
    (elK : Nat → Rel .long E) (hE : ∀ k, elK k = elR(T, k))
    (f : Rel .long V × Rel .long V × Nat → Rel .long V × Rel .long V × Nat) (hf : ∀ st, f st = rnd(st))
    (hR : ∀ i (el : Rel .long E) (pend P S : Rel .long V), el = elK i → pend = (f^[i] (pend₀, Alg.zero, 0)).1 →
      P = (f^[i] (pend₀, Alg.zero, 0)).2.1 → S = step el pend → roundOK)
    (hS : ∀ i, i ≤ (Rel.val T).1.toNat → ∀ r v, rep (step (elK i) (f^[i] (pend₀, Alg.zero, 0)).1) r v ↔
      ∃ e u, rep (elK i) r e ∧ rep (f^[i] (pend₀, Alg.zero, 0)).1 r u ∧ Sr i (e, u) v)
    (F : Rel .long V) (hF : F = foldRows T pend₀ step)
    (jc : Vector Code 2) (hjc : jc = Obj.codes .long ck2(T°, F)) (hjO : codesOK(jc, ck2(T°, F)))
    (hjn : (Rel.n F).toNat < 2 ^ 63) (hjM : (Rel.n (T°)).toNat * (Rel.n F).toNat < min (2 ^ 63) USize.size)
    (hjA : Vals.PickFits (.arr E) (Rel.key (T°)) ((mpairs(jc, T°, F)).map Prod.fst))
    (hjC : Vals.PickFits V (Rel.val F) ((mpairs(jc, T°, F)).map Prod.snd)) :
    ∀ (xs : List E.El) w, rep (foldBy X e step) xs w ↔ (∃ i, X.row i = xs) ∧
      ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
        (∃ p, e.row p = ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm)) ∧
        (∀ t (ht : t < xs.length), Sr (xs.length - 1 - t)
          (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm))
          (ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm))) ∧
        w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm) :=
  rep_foldBy_keep e X T hT hn hv hp hel pend₀ hpend hN h63 hA hB step Sr elK hE f hf hR False
    (fun i hi r v => (hS i hi r v).trans (or_iff_left fun h : False ∧ _ => h.1).symm)
    F hF jc hjc hjO hjn hjM hjA hjC

/-- **`foldOn`, read back**: `rep_foldBy` at `demandStep Sf`, whose round `k` is read back by `step_rep` as
    `Sf (D k)`, `D k` the coreflexive on the (element, value) pairs round `k` meets over ALL arrays of `X`.
    `D` is bound by its equation; `hS` is `step_rep`'s hypotheses at every round, the rest as `rep_foldBy`'s. -/
theorem rep_foldOn {E V : Obj} {m n : USize} (e : Vals V m) (Sf : Rel (.prod E V) (.prod E V) → Rel (.prod E V) V)
    (X : Vals (.arr E) n)
    (T : Rel .long (.arr E)) (hT : T = num (idU X) 0) (hn : n.toNat < 2 ^ 63)
    (hv : Vals.PickFits (.arr E) X (List.range n.toNat)) (hp : (Rel.val T).1.toNat < 2 ^ 63)
    (hel : ∀ k, k ≤ (Rel.val T).1.toNat → ∀ a : ByteArray, a = whereBits (Rel.n T)
        (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf (Rel.val T)).2 (one k.toUInt64) (Rel.n T)) →
      ∀ pos : ByteArray, pos = Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul
        (gather 8 (add (Rel.n T) (slicesOf (Rel.val T)).1 (slicesOf (Rel.val T)).2) a)
        (one (k + 1).toUInt64) (len a).toUSize →
      Vals.PickFits .long (Rel.key T) ((List.range (len a)).map fun q => (Column.bitsAt a (q * 8) 8).toNat) ∧
      Vals.PickFits E (Rel.val T).2.2.2 ((List.range (len a)).map fun q => (Column.bitsAt pos (q * 8) 8).toNat))
    (pend₀ : Rel .long V) (hpend : pend₀ = top (A := .long) (Rel.key T) e)
    (hN : (Rel.n T).toNat * m.toNat < USize.size) (h63 : (Rel.n T).toNat * m.toNat < 2 ^ 63)
    (hA : Vals.PickFits .long (Rel.key T) ((List.range ((Rel.n T).toNat * m.toNat)).map (· / m.toNat)))
    (hB : Vals.PickFits V e ((List.range ((Rel.n T).toNat * m.toNat)).map (· % m.toNat)))
    (step : Rel .long E → Rel .long V → Rel .long V) (hstep : step = demandStep Sf)
    (elK : Nat → Rel .long E) (hE : ∀ k, elK k = elR(T, k))
    (f : Rel .long V × Rel .long V × Nat → Rel .long V × Rel .long V × Nat) (hf : ∀ st, f st = rnd(st))
    (D : Nat → Rel (.prod E V) (.prod E V)) (hD : ∀ k, D k = ran (pair (elK k) (f^[k] (pend₀, Alg.zero, 0)).1))
    (hR : ∀ i (el : Rel .long E) (pend P S : Rel .long V), el = elK i → pend = (f^[i] (pend₀, Alg.zero, 0)).1 →
      P = (f^[i] (pend₀, Alg.zero, 0)).2.1 → S = step el pend → roundOK)
    (hS : ∀ i (el : Rel .long E) (pend : Rel .long V), el = elK i → pend = (f^[i] (pend₀, Alg.zero, 0)).1 →
      stepOn)
    (F : Rel .long V) (hF : F = foldRows T pend₀ step)
    (jc : Vector Code 2) (hjc : jc = Obj.codes .long ck2(T°, F)) (hjO : codesOK(jc, ck2(T°, F)))
    (hjn : (Rel.n F).toNat < 2 ^ 63) (hjM : (Rel.n (T°)).toNat * (Rel.n F).toNat < min (2 ^ 63) USize.size)
    (hjA : Vals.PickFits (.arr E) (Rel.key (T°)) ((mpairs(jc, T°, F)).map Prod.fst))
    (hjC : Vals.PickFits V (Rel.val F) ((mpairs(jc, T°, F)).map Prod.snd)) :
    ∀ (xs : List E.El) w, rep (foldOn e Sf X) xs w ↔ (∃ i, X.row i = xs) ∧
      ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
        (∃ p, e.row p = ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm)) ∧
        (∀ t (ht : t < xs.length), rep (Sf (D (xs.length - 1 - t)))
          (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm))
          (ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm))) ∧
        w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm) := by
  subst hstep
  exact rep_foldBy e X T hT hn hv hp hel pend₀ hpend hN h63 hA hB _ (fun k p w => rep (Sf (D k)) p w) elK hE f hf
    hR (fun i _ r v => by
      obtain ⟨hkO, hkn, hkM, hkA, hkB, hkC, hJ⟩ := hS i _ _ rfl rfl _ rfl
      obtain ⟨hjO, hjn, hjM, hjA, hjC⟩ := hJ _ rfl _ (congrArg Sf (hD i)) _ rfl
      exact step_rep (elK i) _ Sf _ rfl hkO hkn hkM hkA hkB hkC _ rfl _ (congrArg Sf (hD i)) _ rfl
        hjO hjn hjM hjA hjC r v)
    F hF jc hjc hjO hjn hjM hjA hjC

/-- **`fold`, read back**: `rep_foldOn` at the family `fun _ => S`. An array `xs` of `X` goes to `w` when a chain
    `ys` of `S`-steps runs along `xs` from a value of `e` (`ys[|xs|]`) to `w` (`ys[0]`), `ys[t+1]` to `ys[t]` on
    the element `xs[t]`. Bound values and hypotheses as `rep_foldOn`'s. -/
theorem rep_fold {E V : Obj} {m n : USize} (e : Vals V m) (S : Rel (.prod E V) V) (X : Vals (.arr E) n)
    (T : Rel .long (.arr E)) (hT : T = num (idU X) 0) (hn : n.toNat < 2 ^ 63)
    (hv : Vals.PickFits (.arr E) X (List.range n.toNat)) (hp : (Rel.val T).1.toNat < 2 ^ 63)
    (hel : ∀ k, k ≤ (Rel.val T).1.toNat → ∀ a : ByteArray, a = whereBits (Rel.n T)
        (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf (Rel.val T)).2 (one k.toUInt64) (Rel.n T)) →
      ∀ pos : ByteArray, pos = Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul
        (gather 8 (add (Rel.n T) (slicesOf (Rel.val T)).1 (slicesOf (Rel.val T)).2) a)
        (one (k + 1).toUInt64) (len a).toUSize →
      Vals.PickFits .long (Rel.key T) ((List.range (len a)).map fun q => (Column.bitsAt a (q * 8) 8).toNat) ∧
      Vals.PickFits E (Rel.val T).2.2.2 ((List.range (len a)).map fun q => (Column.bitsAt pos (q * 8) 8).toNat))
    (pend₀ : Rel .long V) (hpend : pend₀ = top (A := .long) (Rel.key T) e)
    (hN : (Rel.n T).toNat * m.toNat < USize.size) (h63 : (Rel.n T).toNat * m.toNat < 2 ^ 63)
    (hA : Vals.PickFits .long (Rel.key T) ((List.range ((Rel.n T).toNat * m.toNat)).map (· / m.toNat)))
    (hB : Vals.PickFits V e ((List.range ((Rel.n T).toNat * m.toNat)).map (· % m.toNat)))
    (step : Rel .long E → Rel .long V → Rel .long V) (hstep : step = demandStep (fun _ => S))
    (elK : Nat → Rel .long E) (hE : ∀ k, elK k = elR(T, k))
    (f : Rel .long V × Rel .long V × Nat → Rel .long V × Rel .long V × Nat) (hf : ∀ st, f st = rnd(st))
    (hR : ∀ i (el : Rel .long E) (pend P S : Rel .long V), el = elK i → pend = (f^[i] (pend₀, Alg.zero, 0)).1 →
      P = (f^[i] (pend₀, Alg.zero, 0)).2.1 → S = step el pend → roundOK)
    (hS : ∀ i (el : Rel .long E) (pend : Rel .long V), el = elK i → pend = (f^[i] (pend₀, Alg.zero, 0)).1 →
      stepOK)
    (F : Rel .long V) (hF : F = foldRows T pend₀ step)
    (jc : Vector Code 2) (hjc : jc = Obj.codes .long ck2(T°, F)) (hjO : codesOK(jc, ck2(T°, F)))
    (hjn : (Rel.n F).toNat < 2 ^ 63) (hjM : (Rel.n (T°)).toNat * (Rel.n F).toNat < min (2 ^ 63) USize.size)
    (hjA : Vals.PickFits (.arr E) (Rel.key (T°)) ((mpairs(jc, T°, F)).map Prod.fst))
    (hjC : Vals.PickFits V (Rel.val F) ((mpairs(jc, T°, F)).map Prod.snd)) :
    ∀ (xs : List E.El) w, rep (fold e S X) xs w ↔ (∃ i, X.row i = xs) ∧
      ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
        (∃ p, e.row p = ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm)) ∧
        (∀ t (ht : t < xs.length), rep S (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm))
          (ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm))) ∧
        w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm) :=
  rep_foldOn e (fun _ => S) X T hT hn hv hp hel pend₀ hpend hN h63 hA hB step hstep elK hE f hf _ (fun _ => rfl) hR
    (fun i el pend he hq kc hkc => by
      obtain ⟨h1, h2, h3, h4, h5, h6, hJ⟩ := hS i el pend he hq kc hkc
      exact ⟨h1, h2, h3, h4, h5, h6, fun P hP S' hS' => by subst hS'; exact hJ P hP⟩)
    F hF jc hjc hjO hjn hjM hjA hjC

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.Rep.round_rep
#print axioms LeetQ.Rel.Rep.rep_elR
#print axioms LeetQ.Rel.Rep.iter_stop
#print axioms LeetQ.Rel.Rep.foldRows_iter
#print axioms LeetQ.Rel.Rep.rounds_rep
#print axioms LeetQ.Rel.Rep.rounds_closed_keep
#print axioms LeetQ.Rel.Rep.rounds_closed
#print axioms LeetQ.Rel.Rep.step_rep
#print axioms LeetQ.Rel.Rep.foldRows_rep_keep
#print axioms LeetQ.Rel.Rep.foldRows_rep
#print axioms LeetQ.Rel.Rep.rep_foldBy_keep
#print axioms LeetQ.Rel.Rep.rep_foldBy
#print axioms LeetQ.Rel.Rep.rep_foldOn
#print axioms LeetQ.Rel.Rep.rep_fold
