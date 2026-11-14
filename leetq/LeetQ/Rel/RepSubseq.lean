/-
  `subseq` read back: `foldBy` at the step `cons (pair el pend) ∪ pend`, whose `∪ pend` keeps a row's state alive
  past its array's end (`rep_foldBy_keep` at `keep := True`).
-/
import LeetQ.Rel.RepList

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

open FoldN OpsN

/-- **`subseq`'s step, read back**: `cons (pair el pend) ∪ pend` takes row `r`'s element `e` and list `u` to
    `e :: u`, and keeps every list `pend` holds at `r`, whether or not `r` has an element this round. The codes
    `kc`, the pair `W`, `cons`' pieces (as `rep_cons`'s), `P = cons W` and `Q = pend` are bound by their equations.
    Hypotheses: `rep_pair`'s at `el`, `pend` (`hk…`), `rep_cons`'s at `W`, `rep_union_full`'s at `P`, `Q`. -/
theorem subseq_step_rep {B : Obj} (el : Rel .long B) (pend : Rel .long (.arr B))
    (kc : Vector Code 2) (hkc : kc = Obj.codes .long kp2(el, pend)) (hkO : codesOK(kc, kp2(el, pend)))
    (hkn : (Rel.n pend).toNat < 2 ^ 63) (hkM : msum(kc, el, pend) < 2 ^ 63)
    (hkU : msum(kc, el, pend) < USize.size)
    (hkA : Vals.PickFits .long (Rel.key el) ((mpairs(kc, el, pend)).map Prod.fst))
    (hkB : Vals.PickFits B (Rel.val el) ((mpairs(kc, el, pend)).map Prod.fst))
    (hkC : Vals.PickFits (.arr B) (Rel.val pend) ((mpairs(kc, el, pend)).map Prod.snd))
    (W : Rel .long (.prod B (.arr B))) (hW : W = pair el pend)
    (hp : (Rel.val W).2.1.toNat < 2 ^ 63)
    (s : ByteArray × ByteArray) (hs : s = slicesOf (Rel.val W).2)
    (hcS : ((List.range (Rel.n W).toNat).map fun r => (Column.bitsAt s.2 (r * 8) 8).toNat).sum + (Rel.n W).toNat <
      2 ^ 63)
    (hcU : ((List.range (Rel.n W).toNat).map fun r => (Column.bitsAt s.2 (r * 8) 8).toNat).sum + (Rel.n W).toNat <
      USize.size)
    (xi : ByteArray) (hxi : xi = expandBytes 8 0 (tilLongs (Rel.n W)) s.2)
    (m : USize) (hm : m = (len xi).toUSize)
    (xr : ByteArray) (hxr : xr = sub m (tilLongs m) (gather 8 (sub (Rel.n W) (sums (Rel.n W) s.2) s.2) xi))
    (j : ByteArray) (hj : j = add m (gather 8 s.1 xi) xr)
    (tl : Vals B m) (htl : tl = Vals.pick B (Rel.val W).2.2.2.2 (add m (gather 8 s.1 xi) xr) m
      (len_val Ew.add Ew.vv (gather 8 s.1 xi) xr m))
    (c1 : ByteArray) (hc1 : c1 = addc (Rel.n W) s.2 1) (hi : ByteArray) (hhi : hi = sums (Rel.n W) c1)
    (lo : ByteArray) (hlo : lo = sub (Rel.n W) hi c1)
    (dst : ByteArray) (hdst : dst = addc m (add m (gather 8 lo xi) xr) 1)
    (g : ByteArray) (hg : g = (Code.ofLongs (concatBytes #[dst, lo])).grade)
    (hKf : Vals.PickFits .long (Rel.key W)
      ((List.range (Rel.n W).toNat).map fun q => (Column.bitsAt (tilLongs (Rel.n W)) (q * 8) 8).toNat))
    (hTf : Vals.PickFits B (Rel.val W).2.2.2.2 ((List.range m.toNat).map fun q => (Column.bitsAt j (q * 8) 8).toNat))
    (hRf : Vals.RazeFits B tl (Rel.val W).1)
    (hFf : ∀ hN, Vals.PickFits B (Obj.raze B #[⟨m, tl⟩, ⟨Rel.n W, (Rel.val W).1⟩] hN)
      ((List.range (len g)).map fun q => (Column.bitsAt g (q * 8) 8).toNat))
    (P : Rel .long (.arr B)) (hP : P = cons W) (Q : Rel .long (.arr B)) (hQ : Q = pend)
    (hU : P.n.toNat + Q.n.toNat < USize.size)
    (hNk : ((#[⟨P.n, P.key⟩, ⟨Q.n, Q.key⟩] : Array (Part .long)).toList.map fun c : Part .long => c.1.toNat).sum <
      USize.size)
    (hNv : ((#[⟨P.n, P.val⟩, ⟨Q.n, Q.val⟩] : Array (Part (.arr B))).toList.map
      fun c : Part (.arr B) => c.1.toNat).sum < USize.size)
    (hFk : Vals.RazeFits .long P.key Q.key) (hFv : Vals.RazeFits (.arr B) P.val Q.val)
    (hUV : Obj.CodesFit (.arr B)
      (#v[⟨(PQ(.long, (.arr B))).n, (PQ(.long, (.arr B))).val⟩] : Vector (Part (.arr B)) 1))
    (hUk : Vals.PickFits .long (PQ(.long, (.arr B))).key (List.range (PQ(.long, (.arr B))).n.toNat))
    (hUv : Vals.PickFits (.arr B) (PQ(.long, (.arr B))).val (List.range (PQ(.long, (.arr B))).n.toNat)) :
    ∀ r v, rep (cons (pair el pend) ∪ pend) r v ↔
      (∃ e u, rep el r e ∧ rep pend r u ∧ v = e :: u) ∨ rep pend r v := by
  subst hkc
  have h1 := rep_pair el pend hkO hkn hkM hkU hkA hkB hkC
  subst hW
  have h2 := rep_cons (pair el pend) hp s hs hcS hcU xi hxi m hm xr hxr j hj tl htl c1 hc1 hi hhi lo hlo
    dst hdst g hg hKf hTf hRf hFf
  subst P Q
  intro r v
  rw [rep_union_full (cons (pair el pend)) _ hU hNk hNv hFk hFv
    (one_ok _ (codesFit_atom_one _ (.inl (Option.some_ne_none _)))) (one_ok _ hUV) hUk hUv]
  show rep (cons (pair el pend)) r v ∨ rep _ r v ↔ _
  rw [h2]
  refine or_congr ⟨?_, ?_⟩ Iff.rfl
  · rintro ⟨b, bs, hb, rfl⟩
    rw [h1] at hb
    exact ⟨b, bs, hb.1, hb.2, rfl⟩
  · rintro ⟨e, u, he, hu, rfl⟩
    refine ⟨e, u, ?_, rfl⟩
    rw [h1]; exact ⟨he, hu⟩

/-- The chain `rep_foldBy_keep` leaves for `subseq`: rows `ys[t]` that are `xs[t] :: ys[t+1]` or `ys[t+1]`,
ending at `[]`, start at exactly the sublists of `xs`. -/
theorem subseq_chain {β : Type _} (xs w : List β) :
    (∃ ys : List (List β), ∃ hy : ys.length = xs.length + 1,
      ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm) = [] ∧
      (∀ t (ht : t < xs.length),
        ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) =
            xs[t]'ht :: ys[t+1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm) ∨
          ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) =
            ys[t+1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm)) ∧
      w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.succ_pos _) hy.symm)) ↔ w.Sublist xs := by
  induction xs generalizing w with
  | nil =>
    constructor
    · rintro ⟨ys, hy, hnil, -, rfl⟩
      exact List.sublist_nil.2 hnil
    · intro h
      obtain rfl := List.sublist_nil.1 h
      exact ⟨[[]], rfl, rfl, fun t ht => absurd ht (Nat.not_lt_zero _), rfl⟩
  | cons x xs ih =>
    constructor
    · rintro ⟨ys, hy, hnil, hstep, rfl⟩
      rcases ys with _ | ⟨y, ys⟩
      · simp at hy
      have hy' : ys.length = xs.length + 1 := by simp at hy; omega
      have h := (ih (ys[0]'(by omega))).1 ⟨ys, hy', hnil, fun t ht => hstep (t + 1) (by simp; omega), rfl⟩
      rcases hstep 0 (by simp) with h0 | h0
      · show y.Sublist (x :: xs)
        rw [show y = x :: ys[0]'(by omega) from h0]
        exact h.cons₂ x
      · show y.Sublist (x :: xs)
        rw [show y = ys[0]'(by omega) from h0]
        exact h.cons x
    · intro hs
      rcases List.sublist_cons_iff.1 hs with h | ⟨w', rfl, h⟩
      · obtain ⟨ys, hy, hnil, hstep, hw⟩ := (ih w).2 h
        refine ⟨ys[0]'(by omega) :: ys, by simp [hy], hnil, fun t ht => ?_, hw⟩
        cases t with
        | zero => exact Or.inr rfl
        | succ t => exact hstep t (by simp at ht; omega)
      · obtain ⟨ys, hy, hnil, hstep, hw⟩ := (ih w').2 h
        refine ⟨(x :: w') :: ys, by simp [hy], hnil, fun t ht => ?_, rfl⟩
        cases t with
        | zero => exact Or.inl (congrArg (x :: ·) hw)
        | succ t => exact hstep t (by simp at ht; omega)

section SubseqFold

open QLean.Dep

/-- **`subseq`, read back**: an array `xs` of `X` goes to exactly its sublists. `rep_foldBy_keep` at the step
    `cons (pair el pend) ∪ pend`, `keep := True`, and the seed `nilVal B`, its chain closed by `subseq_chain`.
    Bound values and hypotheses as `rep_foldBy`'s (`step` bound by `hstep`), and `subseq_step_rep`'s at every
    round (`hC`, a per-round bundle, each bound value with its equation). -/
theorem rep_subseq {B : Obj} {n : USize} (X : Vals (.arr B) n)
    (T : Rel .long (.arr B)) (hT : T = num (idU X) 0) (hn : n.toNat < 2 ^ 63)
    (hv : Vals.PickFits (.arr B) X (List.range n.toNat)) (hp : (Rel.val T).1.toNat < 2 ^ 63)
    (hel : ∀ k, k ≤ (Rel.val T).1.toNat → ∀ a : ByteArray, a = whereBits (Rel.n T)
        (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf (Rel.val T)).2 (one k.toUInt64) (Rel.n T)) →
      ∀ pos : ByteArray, pos = Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul
        (gather 8 (add (Rel.n T) (slicesOf (Rel.val T)).1 (slicesOf (Rel.val T)).2) a)
        (one (k + 1).toUInt64) (len a).toUSize →
      Vals.PickFits .long (Rel.key T) ((List.range (len a)).map fun q => (Column.bitsAt a (q * 8) 8).toNat) ∧
      Vals.PickFits B (Rel.val T).2.2.2 ((List.range (len a)).map fun q => (Column.bitsAt pos (q * 8) 8).toNat))
    (pend₀ : Rel .long (.arr B)) (hpend : pend₀ = top (A := .long) (Rel.key T) (nilVal B))
    (hN : (Rel.n T).toNat * (1 : USize).toNat < USize.size)
    (h63 : (Rel.n T).toNat * (1 : USize).toNat < 2 ^ 63)
    (hA : Vals.PickFits .long (Rel.key T)
      ((List.range ((Rel.n T).toNat * (1 : USize).toNat)).map (· / (1 : USize).toNat)))
    (hB : Vals.PickFits (.arr B) (nilVal B)
      ((List.range ((Rel.n T).toNat * (1 : USize).toNat)).map (· % (1 : USize).toNat)))
    (step : Rel .long B → Rel .long (.arr B) → Rel .long (.arr B))
    (hstep : step = fun el pend => cons (pair el pend) ∪ pend)
    (elK : Nat → Rel .long B) (hE : ∀ k, elK k = elR(T, k))
    (f : Rel .long (.arr B) × Rel .long (.arr B) × Nat → Rel .long (.arr B) × Rel .long (.arr B) × Nat)
    (hf : ∀ st, f st = rnd(st))
    (hR : ∀ i (el : Rel .long B) (pend P S : Rel .long (.arr B)), el = elK i →
      pend = (f^[i] (pend₀, Alg.zero, 0)).1 → P = (f^[i] (pend₀, Alg.zero, 0)).2.1 → S = step el pend →
      roundAt((.arr B)))
    (hC : ∀ i, i ≤ (Rel.val T).1.toNat → ∀ (el : Rel .long B) (pend : Rel .long (.arr B)), el = elK i →
      pend = (f^[i] (pend₀, Alg.zero, 0)).1 →
      ∀ kc : Vector Code 2, kc = Obj.codes .long kp2(el, pend) →
      codesOK(kc, kp2(el, pend)) ∧ (Rel.n pend).toNat < 2 ^ 63 ∧ msum(kc, el, pend) < 2 ^ 63 ∧
      msum(kc, el, pend) < USize.size ∧
      Vals.PickFits .long (Rel.key el) ((mpairs(kc, el, pend)).map Prod.fst) ∧
      Vals.PickFits B (Rel.val el) ((mpairs(kc, el, pend)).map Prod.fst) ∧
      Vals.PickFits (.arr B) (Rel.val pend) ((mpairs(kc, el, pend)).map Prod.snd) ∧
      ∀ W : Rel .long (.prod B (.arr B)), W = pair el pend →
      (Rel.val W).2.1.toNat < 2 ^ 63 ∧
      ∀ s : ByteArray × ByteArray, s = slicesOf (Rel.val W).2 →
      ((List.range (Rel.n W).toNat).map fun r => (Column.bitsAt s.2 (r * 8) 8).toNat).sum + (Rel.n W).toNat <
        2 ^ 63 ∧
      ((List.range (Rel.n W).toNat).map fun r => (Column.bitsAt s.2 (r * 8) 8).toNat).sum + (Rel.n W).toNat <
        USize.size ∧
      ∀ xi : ByteArray, xi = expandBytes 8 0 (tilLongs (Rel.n W)) s.2 →
      ∀ m : USize, m = (len xi).toUSize →
      ∀ xr : ByteArray, xr = sub m (tilLongs m) (gather 8 (sub (Rel.n W) (sums (Rel.n W) s.2) s.2) xi) →
      ∀ j : ByteArray, j = add m (gather 8 s.1 xi) xr →
      ∀ tl : Vals B m, tl = Vals.pick B (Rel.val W).2.2.2.2 (add m (gather 8 s.1 xi) xr) m
        (len_val Ew.add Ew.vv (gather 8 s.1 xi) xr m) →
      ∀ c1 : ByteArray, c1 = addc (Rel.n W) s.2 1 → ∀ hi : ByteArray, hi = sums (Rel.n W) c1 →
      ∀ lo : ByteArray, lo = sub (Rel.n W) hi c1 →
      ∀ dst : ByteArray, dst = addc m (add m (gather 8 lo xi) xr) 1 →
      ∀ g : ByteArray, g = (Code.ofLongs (concatBytes #[dst, lo])).grade →
      Vals.PickFits .long (Rel.key W)
        ((List.range (Rel.n W).toNat).map fun q => (Column.bitsAt (tilLongs (Rel.n W)) (q * 8) 8).toNat) ∧
      Vals.PickFits B (Rel.val W).2.2.2.2 ((List.range m.toNat).map fun q => (Column.bitsAt j (q * 8) 8).toNat) ∧
      Vals.RazeFits B tl (Rel.val W).1 ∧
      (∀ hN, Vals.PickFits B (Obj.raze B #[⟨m, tl⟩, ⟨Rel.n W, (Rel.val W).1⟩] hN)
        ((List.range (len g)).map fun q => (Column.bitsAt g (q * 8) 8).toNat)) ∧
      ∀ P : Rel .long (.arr B), P = cons W → ∀ Q : Rel .long (.arr B), Q = pend →
      P.n.toNat + Q.n.toNat < USize.size ∧
      ∃ (hNk : ((#[⟨P.n, P.key⟩, ⟨Q.n, Q.key⟩] : Array (Part .long)).toList.map
          fun c : Part .long => c.1.toNat).sum < USize.size)
        (hNv : ((#[⟨P.n, P.val⟩, ⟨Q.n, Q.val⟩] : Array (Part (.arr B))).toList.map
          fun c : Part (.arr B) => c.1.toNat).sum < USize.size),
        Vals.RazeFits .long P.key Q.key ∧ Vals.RazeFits (.arr B) P.val Q.val ∧
        Obj.CodesFit (.arr B)
          (#v[⟨(PQ(.long, (.arr B))).n, (PQ(.long, (.arr B))).val⟩] : Vector (Part (.arr B)) 1) ∧
        Vals.PickFits .long (PQ(.long, (.arr B))).key (List.range (PQ(.long, (.arr B))).n.toNat) ∧
        Vals.PickFits (.arr B) (PQ(.long, (.arr B))).val (List.range (PQ(.long, (.arr B))).n.toNat))
    (F : Rel .long (.arr B)) (hF : F = foldRows T pend₀ step)
    (jc : Vector Code 2) (hjc : jc = Obj.codes .long ck2(T°, F)) (hjO : codesOK(jc, ck2(T°, F)))
    (hjn : (Rel.n F).toNat < 2 ^ 63) (hjM : msum(jc, T°, F) < 2 ^ 63) (hjU : msum(jc, T°, F) < USize.size)
    (hjA : Vals.PickFits (.arr B) (Rel.key (T°)) ((mpairs(jc, T°, F)).map Prod.fst))
    (hjC : Vals.PickFits (.arr B) (Rel.val F) ((mpairs(jc, T°, F)).map Prod.snd)) :
    ∀ (xs : List B.El) ys, rep (Alg.subseq X) xs ys ↔ (∃ i, X.row i = xs) ∧ ys.Sublist xs := by
  subst hstep
  intro xs ys
  -- round `i`'s step read back: `subseq_step_rep` at the round's element and state, its kept branch split by
  -- whether the row has an element this round
  have hS : ∀ i, i ≤ (Rel.val T).1.toNat → ∀ r v,
      rep (cons (pair (elK i) (f^[i] (pend₀, Alg.zero, 0)).1) ∪ (f^[i] (pend₀, Alg.zero, 0)).1) r v ↔
      (∃ e u, rep (elK i) r e ∧ rep (f^[i] (pend₀, Alg.zero, 0)).1 r u ∧ (v = e :: u ∨ v = u)) ∨
        (True ∧ (¬ ∃ e, rep (elK i) r e) ∧ rep (f^[i] (pend₀, Alg.zero, 0)).1 r v) := by
    intro i hi r v
    obtain ⟨hkO, hkn, hkM, hkU, hkA, hkB, hkC, hW⟩ := hC i hi _ _ rfl rfl _ rfl
    obtain ⟨hp, hs⟩ := hW _ rfl
    obtain ⟨hcS, hcU, hx⟩ := hs _ rfl
    obtain ⟨hKf, hTf, hRf, hFf, hPQ⟩ := hx _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
    obtain ⟨hU, hNk, hNv, hFk, hFv, hUV, hUk, hUv⟩ := hPQ _ rfl _ rfl
    rw [subseq_step_rep _ _ _ rfl hkO hkn hkM hkU hkA hkB hkC _ rfl hp _ rfl hcS hcU _ rfl _ rfl _ rfl _ rfl
      _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl hKf hTf hRf hFf _ rfl _ rfl hU hNk hNv hFk hFv hUV hUk hUv r v]
    constructor
    · rintro (⟨e, u, he, hu, rfl⟩ | hu)
      · exact Or.inl ⟨e, u, he, hu, Or.inl rfl⟩
      · by_cases hx : ∃ e, rep (elK i) r e
        · obtain ⟨e, he⟩ := hx
          exact Or.inl ⟨e, v, he, hu, Or.inr rfl⟩
        · exact Or.inr ⟨trivial, hx, hu⟩
    · rintro (⟨e, u, he, hu, rfl | rfl⟩ | ⟨-, -, hu⟩)
      · exact Or.inl ⟨e, u, he, hu, rfl⟩
      · exact Or.inr hu
      · exact Or.inr hu
  refine (rep_foldBy_keep (nilVal B) X T hT hn hv hp hel pend₀ hpend hN h63 hA hB
    (fun el pend => cons (pair el pend) ∪ pend) (fun _ eu v => v = eu.1 :: eu.2 ∨ v = eu.2) elK hE f hf hR True hS
    F hF jc hjc hjO hjn hjM hjU hjA hjC xs ys).trans ?_
  -- `nilVal B`'s one row is `[]`
  exact and_congr Iff.rfl ((exists_congr fun zs => exists_congr fun _ => and_congr
    ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨⟨0, by simp⟩, h.symm⟩⟩ Iff.rfl).trans (subseq_chain xs ys))

end SubseqFold

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.Rep.subseq_step_rep
#print axioms LeetQ.Rel.Rep.subseq_chain
#print axioms LeetQ.Rel.Rep.rep_subseq
