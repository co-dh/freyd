/-
  `mergeOn` read back. `mergeOn q P` runs rounds of `iter` on states `((x, y), acc)` per key: with both arrays
  non-empty the head `a` of `x` goes to `acc` when `(a, b)` passes the test, else the head `b` of `y`; with either
  empty the state ends as `acc ++ x ++ y`. Each round shortens `x` or `y` by one and no array of `P` is longer
  than its side's payload, so the fuel (both payloads plus one) always suffices: the result is core's
  `List.merge` of each pair of `P`, at the test.
-/
import LeetQ.Rel.RepPerm
import LeetQ.Rel.RepLoop

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

open FoldN OpsN Prim ListN Pow

/-- **The states of a merge, in `Set`**: `st i k` holds the states key `k` reaches after `i` rounds, `out i k` the
    arrays flushed before round `i`. A round takes `((a :: x, b :: y), acc)` to `((x, b :: y), acc ++ [a])` when
    `le a b`, else to `((a :: x, y), acc ++ [b])` (`hst`), and flushes a state with an empty side as
    `acc ++ x ++ y` (`hout`); the seeds `st 0` are the pairs of `seed` with `acc = []`. At a stop `j` past every
    seed's total length (`N < j`), or with no state left, `out j` is exactly the merges of the seeds. -/
theorem merge_chain {K B : Type} (le : B → B → Bool) (seed : K → List B × List B → Prop)
    (st : Nat → K → (List B × List B) × List B → Prop) (out : Nat → K → List B → Prop) (M : Nat)
    (h0 : ∀ k x y acc, st 0 k ((x, y), acc) ↔ seed k (x, y) ∧ acc = [])
    (hst : ∀ i, i < M → ∀ k s', st (i + 1) k s' ↔ ∃ a x b y acc, st i k ((a :: x, b :: y), acc) ∧
      (le a b = true ∧ s' = ((x, b :: y), acc ++ [a]) ∨ le a b = false ∧ s' = ((a :: x, y), acc ++ [b])))
    (ho0 : ∀ k z, ¬ out 0 k z)
    (hout : ∀ i, i < M → ∀ k z, out (i + 1) k z ↔
      out i k z ∨ ∃ x y acc, st i k ((x, y), acc) ∧ (x = [] ∨ y = []) ∧ z = acc ++ x ++ y)
    (N j : Nat) (hjM : j ≤ M) (hN : ∀ k s, seed k s → s.1.length + s.2.length ≤ N)
    (hj : N < j ∨ ∀ k s, ¬ st j k s) :
    ∀ k z, out j k z ↔ ∃ xs ys, seed k (xs, ys) ∧ z = List.merge xs ys le := by
  -- a flushed state: one side empty, so `x ++ y` is their merge
  have flush : ∀ x y : List B, (x = [] ∨ y = []) → x ++ y = List.merge x y le := by
    rintro x y (rfl | rfl)
    · simp
    · simp
  -- every state after `i` rounds: `acc` then the merge of its sides is the merge of its seed, `i` cells moved
  have sound : ∀ i, i ≤ M → ∀ k x y acc, st i k ((x, y), acc) → ∃ xs ys, seed k (xs, ys) ∧
      acc ++ List.merge x y le = List.merge xs ys le ∧ x.length + y.length + i = xs.length + ys.length := by
    intro i
    induction i with
    | zero =>
      intro _ k x y acc h
      obtain ⟨hs, rfl⟩ := (h0 k x y acc).1 h
      exact ⟨x, y, hs, by simp, by simp⟩
    | succ i ih =>
      intro hi k x y acc h
      obtain ⟨a, x0, b, y0, acc0, hs, hc⟩ := (hst i (by omega) k _).1 h
      obtain ⟨xs, ys, hseed, he, hl⟩ := ih (by omega) k _ _ _ hs
      refine ⟨xs, ys, hseed, ?_⟩
      rcases hc with ⟨hab, e⟩ | ⟨hab, e⟩
      · simp only [Prod.mk.injEq] at e
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
        refine ⟨?_, ?_⟩
        · rw [← he, List.cons_merge_cons, if_pos hab]; simp
        · simp at hl ⊢; omega
      · simp only [Prod.mk.injEq] at e
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
        refine ⟨?_, ?_⟩
        · rw [← he, List.cons_merge_cons, if_neg (by simp [hab])]; simp
        · simp at hl ⊢; omega
  -- every seed has, after `i` rounds, its merge flushed or a state carrying it
  have complete : ∀ i, i ≤ M → ∀ k xs ys, seed k (xs, ys) → out i k (List.merge xs ys le) ∨
      ∃ x y acc, st i k ((x, y), acc) ∧ acc ++ List.merge x y le = List.merge xs ys le := by
    intro i
    induction i with
    | zero => intro _ k xs ys hs; exact Or.inr ⟨xs, ys, [], (h0 k xs ys []).2 ⟨hs, rfl⟩, by simp⟩
    | succ i ih =>
      intro hi k xs ys hs
      rcases ih (by omega) k xs ys hs with ho | ⟨x, y, acc, hst', he⟩
      · exact Or.inl ((hout i (by omega) k _).2 (Or.inl ho))
      · match x, y, hst', he with
        | [], y, hst', he =>
          exact Or.inl ((hout i (by omega) k _).2 (Or.inr ⟨[], y, acc, hst', Or.inl rfl, by rw [← he]; simp⟩))
        | a :: x, [], hst', he =>
          exact Or.inl ((hout i (by omega) k _).2 (Or.inr ⟨a :: x, [], acc, hst', Or.inr rfl, by rw [← he]; simp⟩))
        | a :: x, b :: y, hst', he =>
          refine Or.inr ?_
          cases hab : le a b
          · refine ⟨a :: x, y, acc ++ [b], (hst i (by omega) k _).2 ⟨a, x, b, y, acc, hst', Or.inr ⟨hab, rfl⟩⟩, ?_⟩
            rw [← he, List.cons_merge_cons, if_neg (by simp [hab])]; simp
          · refine ⟨x, b :: y, acc ++ [a], (hst i (by omega) k _).2 ⟨a, x, b, y, acc, hst', Or.inl ⟨hab, rfl⟩⟩, ?_⟩
            rw [← he, List.cons_merge_cons, if_pos hab]; simp
  have osound : ∀ i, i ≤ M → ∀ k z, out i k z → ∃ xs ys, seed k (xs, ys) ∧ z = List.merge xs ys le := by
    intro i
    induction i with
    | zero => intro _ k z h; exact absurd h (ho0 k z)
    | succ i ih =>
      intro hi k z h
      rcases (hout i (by omega) k z).1 h with h | ⟨x, y, acc, hs, he, rfl⟩
      · exact ih (by omega) k z h
      · obtain ⟨xs, ys, hseed, hm, -⟩ := sound i (by omega) k x y acc hs
        exact ⟨xs, ys, hseed, by rw [← hm, List.append_assoc, flush x y he]⟩
  intro k z
  refine ⟨osound j hjM k z, ?_⟩
  rintro ⟨xs, ys, hs, rfl⟩
  rcases complete j hjM k xs ys hs with ho | ⟨x, y, acc, hst', -⟩
  · exact ho
  · exfalso
    rcases hj with hj | hj
    · obtain ⟨xs', ys', hs', -, hl⟩ := sound j hjM k x y acc hst'
      have := hN k _ hs'
      simp at this
      omega
    · exact hj k _ hst'

#print axioms merge_chain

-- the states `((x, y), acc)` of `mergeOn`
set_option hygiene false in
local notation "SO" => Obj.prod (.prod (.arr B) (.arr B)) (.arr B)

section Round

open Freyd Freyd.Alg Freyd.Alg.RelSet

/-- **One round of `mergeOn`, read back from its primitives' read-backs**: the new states `mT` are the states
    with both sides non-empty, stepped by the test `le` on their heads, and `mU` adds to `out` the states with a
    side empty, flushed as `acc ++ x ++ y`. Each hypothesis is one primitive's read-back at this round's values
    (`rep_ran`, `rep_uncons`, `rep_comp`, `rep_pair`, `rep_dom`, `rep_snoc`, `rep_antiJoin`, `rep_union_full`,
    `rep_cat_ok`); `htest` reads the test `G` on the pairs of heads `mrh` the round meets. -/
theorem merge_round_set {K B : Obj} (le : B.El → B.El → Bool) (out : Rel K (.arr B)) (St : Rel K SO)
    (mD : Rel SO SO) (mx my macc : Rel SO (.arr B)) (mux muy : Rel SO (.prod B (.arr B)))
    (mpu : Rel SO (.prod (.prod B (.arr B)) (.prod B (.arr B)))) (mboth : Rel SO SO) (mh : Rel SO (.prod B B))
    (mrh G : Rel (.prod B B) (.prod B B)) (mhq : Rel SO (.prod B B)) (ml : Rel SO SO)
    (mA1 mA2 : Rel SO (.prod (.arr B) (.arr B))) (mS1 mS2 : Rel SO (.prod (.arr B) B)) (mN1 mN2 : Rel SO (.arr B))
    (mP1 mP2 mL1 mL2 mnb mtk mfl : Rel SO SO) (mT mSf : Rel K SO) (mc1 mc2 : Rel SO (.prod (.arr B) (.arr B)))
    (mC1 mC2 : Rel SO (.arr B)) (mO mU : Rel K (.arr B))
    (hD : rep mD = corefl (A := (⟨(SO).El⟩ : RelSet.{0})) fun s => ∃ k, rep St k s)
    (hx : mx = outl (outl mD)) (hy : my = outr (outl mD)) (hacc : macc = outr mD)
    (hUx : ∀ (xs : List B.El) b bs, rep (uncons (Rel.val mx)) xs (b, bs) ↔
      (∃ j, (Rel.val mx).row j = xs) ∧ xs = b :: bs)
    (hux : rep mux = rep mx ≫ rep (uncons (Rel.val mx)))
    (hUy : ∀ (xs : List B.El) b bs, rep (uncons (Rel.val my)) xs (b, bs) ↔
      (∃ j, (Rel.val my).row j = xs) ∧ xs = b :: bs)
    (huy : rep muy = rep my ≫ rep (uncons (Rel.val my)))
    (hpu : rep mpu = rpair (rep mux) (rep muy))
    (hboth : rep mboth = corefl (A := (⟨(SO).El⟩ : RelSet.{0})) fun s => ∃ p, rep mpu s p)
    (hh : rep mh = rpair (rep (outl mux)) (rep (outl muy)))
    (hrh : rep mrh = corefl (A := (⟨(Obj.prod B B).El⟩ : RelSet.{0})) fun ab => ∃ s, rep mh s ab)
    (htest : ∀ a b, rep mrh (a, b) (a, b) → ((∃ c, rep G (a, b) c) ↔ le a b = true))
    (hhq : rep mhq = rep mh ≫ rep G)
    (hl : rep ml = corefl (A := (⟨(SO).El⟩ : RelSet.{0})) fun s => ∃ c, rep mhq s c)
    (hA1 : rep mA1 = rpair (rep (outr mux)) (rep my)) (hS1 : rep mS1 = rpair (rep macc) (rep (outl mux)))
    (hN1 : ∀ s z, rep mN1 s z ↔ ∃ bs b, rep mS1 s (bs, b) ∧ z = bs ++ [b])
    (hP1 : rep mP1 = rpair (rep mA1) (rep mN1)) (hL1 : rep mL1 = rep ml ≫ rep mP1)
    (hnb : rep mnb = rep mboth ≫ corefl (A := (⟨(SO).El⟩ : RelSet.{0})) fun s => ¬ ∃ y, rep ml y s)
    (hA2 : rep mA2 = rpair (rep mx) (rep (outr muy))) (hS2 : rep mS2 = rpair (rep macc) (rep (outl muy)))
    (hN2 : ∀ s z, rep mN2 s z ↔ ∃ bs b, rep mS2 s (bs, b) ∧ z = bs ++ [b])
    (hP2 : rep mP2 = rpair (rep mA2) (rep mN2)) (hL2 : rep mL2 = rep mnb ≫ rep mP2)
    (htk : rep mtk = rep mL1 ∪ rep mL2) (hT : rep mT = rep St ≫ rep mtk)
    (hfl : rep mfl = rep mD ≫ corefl (A := (⟨(SO).El⟩ : RelSet.{0})) fun s => ¬ ∃ y, rep mboth y s)
    (hSf : rep mSf = rep St ≫ rep mfl)
    (hc1 : rep mc1 = rpair (rep macc) (rep mx))
    (hC1 : ∀ s z, rep mC1 s z ↔ ∃ xs ys, rep mc1 s (xs, ys) ∧ z = xs ++ ys)
    (hc2 : rep mc2 = rpair (rep mC1) (rep my))
    (hC2 : ∀ s z, rep mC2 s z ↔ ∃ xs ys, rep mc2 s (xs, ys) ∧ z = xs ++ ys)
    (hO : rep mO = rep mSf ≫ rep mC2) (hU : rep mU = rep out ∪ rep mO) :
    (∀ k s', rep mT k s' ↔ ∃ a x b y acc, rep St k ((a :: x, b :: y), acc) ∧
      (le a b = true ∧ s' = ((x, b :: y), acc ++ [a]) ∨ le a b = false ∧ s' = ((a :: x, y), acc ++ [b]))) ∧
    ∀ k z, rep mU k z ↔
      rep out k z ∨ ∃ x y acc, rep St k ((x, y), acc) ∧ (x = [] ∨ y = []) ∧ z = acc ++ x ++ y := by
  have eD : ∀ s s', rep mD s s' ↔ s = s' ∧ ∃ k, rep St k s := fun s s' => by rw [hD]; exact Iff.rfl
  -- the three parts of a state, each read off `D`
  have eLD : ∀ s v, rep (outl mD) s v ↔ (∃ k, rep St k s) ∧ v = s.1 := by
    intro s v
    refine (outl_holds mD s v).trans ⟨?_, ?_⟩
    · rintro ⟨w, h⟩; obtain ⟨rfl, hk⟩ := (eD _ _).1 h; exact ⟨hk, rfl⟩
    · rintro ⟨hk, rfl⟩; exact ⟨s.2, (eD _ _).2 ⟨rfl, hk⟩⟩
  have eX : ∀ s v, rep mx s v ↔ (∃ k, rep St k s) ∧ v = s.1.1 := by
    intro s v; rw [hx]
    refine (outl_holds _ s v).trans ⟨?_, ?_⟩
    · rintro ⟨w, h⟩; obtain ⟨hk, e⟩ := (eLD _ _).1 h; exact ⟨hk, by rw [← e]⟩
    · rintro ⟨hk, rfl⟩; exact ⟨s.1.2, (eLD _ _).2 ⟨hk, rfl⟩⟩
  have eY : ∀ s v, rep my s v ↔ (∃ k, rep St k s) ∧ v = s.1.2 := by
    intro s v; rw [hy]
    refine (outr_holds _ s v).trans ⟨?_, ?_⟩
    · rintro ⟨w, h⟩; obtain ⟨hk, e⟩ := (eLD _ _).1 h; exact ⟨hk, by rw [← e]⟩
    · rintro ⟨hk, rfl⟩; exact ⟨s.1.1, (eLD _ _).2 ⟨hk, rfl⟩⟩
  have eA : ∀ s v, rep macc s v ↔ (∃ k, rep St k s) ∧ v = s.2 := by
    intro s v; rw [hacc]
    refine (outr_holds _ s v).trans ⟨?_, ?_⟩
    · rintro ⟨w, h⟩; obtain ⟨rfl, hk⟩ := (eD _ _).1 h; exact ⟨hk, rfl⟩
    · rintro ⟨hk, rfl⟩; exact ⟨s.1, (eD _ _).2 ⟨rfl, hk⟩⟩
  -- `uncons` of each side
  have eUx : ∀ s a t, rep mux s (a, t) ↔ (∃ k, rep St k s) ∧ s.1.1 = a :: t := by
    intro s a t; rw [hux, comp_apply]
    constructor
    · rintro ⟨v, h1, h2⟩; obtain ⟨hk, rfl⟩ := (eX _ _).1 h1; exact ⟨hk, ((hUx _ a t).1 h2).2⟩
    · rintro ⟨hk, e⟩
      have h1 := (eX s s.1.1).2 ⟨hk, rfl⟩
      obtain ⟨j, -, hj⟩ := id h1
      exact ⟨s.1.1, h1, (hUx _ a t).2 ⟨⟨j, hj⟩, e⟩⟩
  have eUy : ∀ s b t, rep muy s (b, t) ↔ (∃ k, rep St k s) ∧ s.1.2 = b :: t := by
    intro s b t; rw [huy, comp_apply]
    constructor
    · rintro ⟨v, h1, h2⟩; obtain ⟨hk, rfl⟩ := (eY _ _).1 h1; exact ⟨hk, ((hUy _ b t).1 h2).2⟩
    · rintro ⟨hk, e⟩
      have h1 := (eY s s.1.2).2 ⟨hk, rfl⟩
      obtain ⟨j, -, hj⟩ := id h1
      exact ⟨s.1.2, h1, (hUy _ b t).2 ⟨⟨j, hj⟩, e⟩⟩
  have eLx : ∀ s a, rep (outl mux) s a ↔ (∃ k, rep St k s) ∧ ∃ t, s.1.1 = a :: t :=
    fun s a => (outl_holds _ s a).trans ⟨fun ⟨t, h⟩ => ((eUx _ _ _).1 h).imp_right fun e => ⟨t, e⟩,
      fun ⟨hk, t, e⟩ => ⟨t, (eUx _ _ _).2 ⟨hk, e⟩⟩⟩
  have eRx : ∀ s t, rep (outr mux) s t ↔ (∃ k, rep St k s) ∧ ∃ a, s.1.1 = a :: t :=
    fun s t => (outr_holds _ s t).trans ⟨fun ⟨a, h⟩ => ((eUx _ _ _).1 h).imp_right fun e => ⟨a, e⟩,
      fun ⟨hk, a, e⟩ => ⟨a, (eUx _ _ _).2 ⟨hk, e⟩⟩⟩
  have eLy : ∀ s b, rep (outl muy) s b ↔ (∃ k, rep St k s) ∧ ∃ t, s.1.2 = b :: t :=
    fun s b => (outl_holds _ s b).trans ⟨fun ⟨t, h⟩ => ((eUy _ _ _).1 h).imp_right fun e => ⟨t, e⟩,
      fun ⟨hk, t, e⟩ => ⟨t, (eUy _ _ _).2 ⟨hk, e⟩⟩⟩
  have eRy : ∀ s t, rep (outr muy) s t ↔ (∃ k, rep St k s) ∧ ∃ b, s.1.2 = b :: t :=
    fun s t => (outr_holds _ s t).trans ⟨fun ⟨b, h⟩ => ((eUy _ _ _).1 h).imp_right fun e => ⟨b, e⟩,
      fun ⟨hk, b, e⟩ => ⟨b, (eUy _ _ _).2 ⟨hk, e⟩⟩⟩
  -- `both`: the states with both sides non-empty
  have eB : ∀ s s', rep mboth s s' ↔ s = s' ∧ (∃ k, rep St k s) ∧ (∃ a x, s.1.1 = a :: x) ∧
      ∃ b y, s.1.2 = b :: y := by
    intro s s'; rw [hboth]
    show s = s' ∧ (∃ p, rep mpu s p) ↔ _
    refine and_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨⟨⟨a, x⟩, ⟨b, y⟩⟩, hp⟩
      rw [hpu] at hp
      obtain ⟨h1, h2⟩ := hp
      obtain ⟨hk, e1⟩ := (eUx _ _ _).1 h1
      exact ⟨hk, ⟨a, x, e1⟩, b, y, ((eUy _ _ _).1 h2).2⟩
    · rintro ⟨hk, ⟨a, x, e1⟩, b, y, e2⟩
      refine ⟨((a, x), (b, y)), ?_⟩
      rw [hpu]
      exact ⟨(eUx _ _ _).2 ⟨hk, e1⟩, (eUy _ _ _).2 ⟨hk, e2⟩⟩
  have eH : ∀ s a b, rep mh s (a, b) ↔ (∃ k, rep St k s) ∧ (∃ x, s.1.1 = a :: x) ∧ ∃ y, s.1.2 = b :: y := by
    intro s a b; rw [hh]
    show rep (outl mux) s a ∧ rep (outl muy) s b ↔ _
    rw [eLx, eLy]
    exact ⟨fun ⟨⟨hk, h1⟩, ⟨_, h2⟩⟩ => ⟨hk, h1, h2⟩, fun ⟨hk, h1, h2⟩ => ⟨⟨hk, h1⟩, ⟨hk, h2⟩⟩⟩
  -- `l`: the states with both sides non-empty whose heads pass the test
  have eL : ∀ s s', rep ml s s' ↔ s = s' ∧ (∃ k, rep St k s) ∧
      ∃ a x b y, s.1 = (a :: x, b :: y) ∧ le a b = true := by
    intro s s'; rw [hl]
    show s = s' ∧ (∃ c, rep mhq s c) ↔ _
    refine and_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨c, hc⟩
      rw [hhq, comp_apply] at hc
      obtain ⟨⟨a, b⟩, h1, h2⟩ := hc
      obtain ⟨hk, ⟨x, ex⟩, y, ey⟩ := (eH _ _ _).1 h1
      have hr : rep mrh (a, b) (a, b) := by rw [hrh]; exact ⟨rfl, s, h1⟩
      exact ⟨hk, a, x, b, y, Prod.ext ex ey, (htest a b hr).1 ⟨c, h2⟩⟩
    · rintro ⟨hk, a, x, b, y, e, hab⟩
      have h1 : rep mh s (a, b) := (eH _ _ _).2 ⟨hk, ⟨x, by rw [e]⟩, y, by rw [e]⟩
      have hr : rep mrh (a, b) (a, b) := by rw [hrh]; exact ⟨rfl, s, h1⟩
      obtain ⟨c, hc⟩ := (htest a b hr).2 hab
      refine ⟨c, ?_⟩
      rw [hhq, comp_apply]
      exact ⟨(a, b), h1, hc⟩
  have eL1 : ∀ s s', rep mL1 s s' ↔ (∃ k, rep St k s) ∧ ∃ a x b y, s.1 = (a :: x, b :: y) ∧
      le a b = true ∧ s' = ((x, b :: y), s.2 ++ [a]) := by
    intro s s'; rw [hL1, comp_apply]
    constructor
    · rintro ⟨s'', h1, h2⟩
      obtain ⟨rfl, hk, a, x, b, y, e, hab⟩ := (eL _ _).1 h1
      rw [hP1] at h2
      obtain ⟨h3, h4⟩ := h2
      rw [hA1] at h3
      obtain ⟨h5, h6⟩ := h3
      obtain ⟨-, a', e5⟩ := (eRx _ _).1 h5
      obtain ⟨-, e6⟩ := (eY _ _).1 h6
      obtain ⟨bs, b', h7, e7⟩ := (hN1 _ _).1 h4
      rw [hS1] at h7
      obtain ⟨h8, h9⟩ := h7
      obtain ⟨-, e8⟩ := (eA _ _).1 h8
      obtain ⟨-, t, e9⟩ := (eLx _ _).1 h9
      refine ⟨hk, a, x, b, y, e, hab, ?_⟩
      obtain ⟨⟨s11, s12⟩, s2⟩ := s'
      simp only [e, List.cons.injEq] at e5 e6 e7 e8 e9
      obtain ⟨-, rfl⟩ := e5
      subst e6 e7 e8
      obtain ⟨rfl, -⟩ := e9
      rfl
    · rintro ⟨hk, a, x, b, y, e, hab, rfl⟩
      refine ⟨s, (eL _ _).2 ⟨rfl, hk, a, x, b, y, e, hab⟩, ?_⟩
      rw [hP1]
      refine ⟨?_, (hN1 _ _).2 ⟨s.2, a, ?_, rfl⟩⟩
      · rw [hA1]
        exact ⟨(eRx _ _).2 ⟨hk, a, by rw [e]⟩, (eY _ _).2 ⟨hk, by rw [e]⟩⟩
      · rw [hS1]
        exact ⟨(eA _ _).2 ⟨hk, rfl⟩, (eLx _ _).2 ⟨hk, x, by rw [e]⟩⟩
  have eL2 : ∀ s s', rep mL2 s s' ↔ (∃ k, rep St k s) ∧ ∃ a x b y, s.1 = (a :: x, b :: y) ∧
      le a b = false ∧ s' = ((a :: x, y), s.2 ++ [b]) := by
    -- a state of `both` is outside `l` exactly when its heads fail the test
    have enl : ∀ s a x b y, (∃ k, rep St k s) → s.1 = (a :: x, b :: y) →
        ((¬ ∃ s'', rep ml s'' s) ↔ le a b = false) := by
      intro s a x b y hk e
      constructor
      · intro hn
        cases hab : le a b
        · rfl
        · exact absurd ⟨s, (eL _ _).2 ⟨rfl, hk, a, x, b, y, e, hab⟩⟩ hn
      · rintro hab ⟨s'', h⟩
        obtain ⟨rfl, -, a', x', b', y', e', hab'⟩ := (eL _ _).1 h
        rw [e] at e'
        simp only [Prod.mk.injEq, List.cons.injEq] at e'
        obtain ⟨⟨rfl, -⟩, rfl, -⟩ := e'
        rw [hab] at hab'; exact Bool.false_ne_true hab'
    intro s s'; rw [hL2, comp_apply]
    constructor
    · rintro ⟨s'', h1, h2⟩
      rw [hnb, comp_apply] at h1
      obtain ⟨s3, h3, rfl, hn⟩ := h1
      obtain ⟨rfl, hk, ⟨a, x, ex⟩, b, y, ey⟩ := (eB _ _).1 h3
      have e : s.1 = (a :: x, b :: y) := Prod.ext ex ey
      rw [hP2] at h2
      obtain ⟨h3, h4⟩ := h2
      rw [hA2] at h3
      obtain ⟨h5, h6⟩ := h3
      obtain ⟨-, e5⟩ := (eX _ _).1 h5
      obtain ⟨-, b', e6⟩ := (eRy _ _).1 h6
      obtain ⟨bs, b'', h7, e7⟩ := (hN2 _ _).1 h4
      rw [hS2] at h7
      obtain ⟨h8, h9⟩ := h7
      obtain ⟨-, e8⟩ := (eA _ _).1 h8
      obtain ⟨-, t, e9⟩ := (eLy _ _).1 h9
      refine ⟨hk, a, x, b, y, e, (enl s a x b y hk e).1 hn, ?_⟩
      obtain ⟨⟨s11, s12⟩, s2⟩ := s'
      simp only [e, List.cons.injEq] at e5 e6 e7 e8 e9
      subst e5
      obtain ⟨-, rfl⟩ := e6
      subst e7 e8
      obtain ⟨rfl, -⟩ := e9
      rfl
    · rintro ⟨hk, a, x, b, y, e, hab, rfl⟩
      refine ⟨s, ?_, ?_⟩
      · rw [hnb, comp_apply]
        exact ⟨s, (eB _ _).2 ⟨rfl, hk, ⟨a, x, by rw [e]⟩, b, y, by rw [e]⟩, rfl, (enl s a x b y hk e).2 hab⟩
      · rw [hP2]
        refine ⟨?_, (hN2 _ _).2 ⟨s.2, b, ?_, rfl⟩⟩
        · rw [hA2]
          exact ⟨(eX _ _).2 ⟨hk, by rw [e]⟩, (eRy _ _).2 ⟨hk, b, by rw [e]⟩⟩
        · rw [hS2]
          exact ⟨(eA _ _).2 ⟨hk, rfl⟩, (eLy _ _).2 ⟨hk, y, by rw [e]⟩⟩
  -- the flushed arrays: `acc ++ x ++ y` of a state with a side empty
  have eC2 : ∀ s z, rep mC2 s z ↔ (∃ k, rep St k s) ∧ z = s.2 ++ s.1.1 ++ s.1.2 := by
    intro s z
    rw [hC2]
    constructor
    · rintro ⟨u, v, h1, rfl⟩
      rw [hc2] at h1
      obtain ⟨h2, h3⟩ := h1
      obtain ⟨p, q, h4, rfl⟩ := (hC1 _ _).1 h2
      rw [hc1] at h4
      obtain ⟨h5, h6⟩ := h4
      obtain ⟨hk, rfl⟩ := (eA _ _).1 h5
      obtain ⟨-, rfl⟩ := (eX _ _).1 h6
      obtain ⟨-, rfl⟩ := (eY _ _).1 h3
      exact ⟨hk, rfl⟩
    · rintro ⟨hk, rfl⟩
      refine ⟨s.2 ++ s.1.1, s.1.2, ?_, rfl⟩
      rw [hc2]
      refine ⟨(hC1 _ _).2 ⟨s.2, s.1.1, ?_, rfl⟩, (eY _ _).2 ⟨hk, rfl⟩⟩
      rw [hc1]
      exact ⟨(eA _ _).2 ⟨hk, rfl⟩, (eX _ _).2 ⟨hk, rfl⟩⟩
  have eFl : ∀ s s', rep mfl s s' ↔ s = s' ∧ (∃ k, rep St k s) ∧ (s.1.1 = [] ∨ s.1.2 = []) := by
    intro s s'; rw [hfl, comp_apply]
    constructor
    · rintro ⟨s'', h1, rfl, hn⟩
      obtain ⟨rfl, hk⟩ := (eD _ _).1 h1
      refine ⟨rfl, hk, ?_⟩
      cases ex : s.1.1 with
      | nil => exact Or.inl rfl
      | cons a x =>
        cases ey : s.1.2 with
        | nil => exact Or.inr rfl
        | cons b y => exact absurd ⟨s, (eB _ _).2 ⟨rfl, hk, ⟨a, x, ex⟩, b, y, ey⟩⟩ hn
    · rintro ⟨rfl, hk, he⟩
      refine ⟨s, (eD _ _).2 ⟨rfl, hk⟩, rfl, ?_⟩
      rintro ⟨s'', h⟩
      obtain ⟨rfl, -, ⟨a, x, ex⟩, b, y, ey⟩ := (eB _ _).1 h
      rcases he with he | he
      · rw [he] at ex; exact List.cons_ne_nil a x ex.symm
      · rw [he] at ey; exact List.cons_ne_nil b y ey.symm
  refine ⟨fun k s' => ?_, fun k z => ?_⟩
  · rw [hT, comp_apply]
    constructor
    · rintro ⟨s, hs, h⟩
      rw [htk, union_apply] at h
      rcases h with h | h
      · obtain ⟨-, a, x, b, y, e, hab, rfl⟩ := (eL1 _ _).1 h
        refine ⟨a, x, b, y, s.2, ?_, Or.inl ⟨hab, rfl⟩⟩
        rw [← e]; exact hs
      · obtain ⟨-, a, x, b, y, e, hab, rfl⟩ := (eL2 _ _).1 h
        refine ⟨a, x, b, y, s.2, ?_, Or.inr ⟨hab, rfl⟩⟩
        rw [← e]; exact hs
    · rintro ⟨a, x, b, y, acc, hs, h⟩
      refine ⟨_, hs, ?_⟩
      rw [htk, union_apply]
      rcases h with ⟨hab, rfl⟩ | ⟨hab, rfl⟩
      · exact Or.inl ((eL1 _ _).2 ⟨⟨k, hs⟩, a, x, b, y, rfl, hab, rfl⟩)
      · exact Or.inr ((eL2 _ _).2 ⟨⟨k, hs⟩, a, x, b, y, rfl, hab, rfl⟩)
  · rw [hU, union_apply, hO, comp_apply]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨⟨⟨x, y⟩, acc⟩, h1, h2⟩
      rw [hSf, comp_apply] at h1
      obtain ⟨s', hs, h3⟩ := h1
      obtain ⟨rfl, -, he⟩ := (eFl _ _).1 h3
      exact ⟨x, y, acc, hs, he, ((eC2 _ _).1 h2).2⟩
    · rintro ⟨x, y, acc, hs, he, rfl⟩
      refine ⟨((x, y), acc), ?_, (eC2 _ _).2 ⟨⟨k, hs⟩, rfl⟩⟩
      rw [hSf, comp_apply]
      exact ⟨_, hs, (eFl _ _).2 ⟨rfl, ⟨k, hs⟩, he⟩⟩

end Round

#print axioms merge_round_set

/-! ## The primitives' hypotheses at one round -/


-- every primitive's hypotheses at one round's values, named as `merge_round_set` names them
set_option hygiene false in
local notation "mergeOK" =>
  (oneFit(SO, Rel.n St, Rel.val St) ∧ uncOK(B, mx) ∧ cmpOK(.arr B, mx, uncons (Rel.val mx)) ∧
    uncOK(B, my) ∧ cmpOK(.arr B, my, uncons (Rel.val my)) ∧ pairOK(SO, mux, muy) ∧
    oneFit(SO, Rel.n mpu, Rel.key mpu) ∧ pairOK(SO, outl mux, outl muy) ∧
    oneFit(.prod B B, Rel.n mh, Rel.val mh) ∧ cmpOK(.prod B B, mh, G) ∧ oneFit(SO, Rel.n mhq, Rel.key mhq) ∧
    pairOK(SO, outr mux, my) ∧ pairOK(SO, macc, outl mux) ∧ snocOK(SO, B, mS1) ∧ pairOK(SO, mA1, mN1) ∧
    cmpOK(SO, ml, mP1) ∧ ajOK(SO, mboth, ml) ∧
    pairOK(SO, mx, outr muy) ∧ pairOK(SO, macc, outl muy) ∧ snocOK(SO, B, mS2) ∧ pairOK(SO, mA2, mN2) ∧
    cmpOK(SO, mnb, mP2) ∧ uniOK(SO, SO, mL1, mL2) ∧ cmpOK(SO, St, mtk) ∧
    ajOK(SO, mD, mboth) ∧ cmpOK(SO, St, mfl) ∧ pairOK(SO, macc, mx) ∧ catOK(SO, B, mc1) ∧
    pairOK(SO, mC1, my) ∧ catOK(SO, B, mc2) ∧ cmpOK(SO, mSf, mC2) ∧ uniOK(K, .arr B, out, mO))

/-- **One round of `mergeOn`, read back**: `merge_round_set` with each primitive's read-back discharged by its
    lemma. The round's values are bound by their equations, the test `G` any relation (`mergeOn`'s is
    `q(ran h)`); `h` is every primitive's hypotheses at them (`mergeOK`), `hW` `rep_snoc`'s universal one. -/
theorem merge_round_rep {K B : Obj} (le : B.El → B.El → Bool) (out : Rel K (.arr B)) (St : Rel K SO)
    (mD : Rel SO SO) (hD : mD = ran St) (mx : Rel SO (.arr B)) (hx : mx = outl (outl mD))
    (my : Rel SO (.arr B)) (hy : my = outr (outl mD)) (macc : Rel SO (.arr B)) (hacc : macc = outr mD)
    (mux : Rel SO (.prod B (.arr B))) (hux : mux = mx ≫ uncons (Rel.val mx))
    (muy : Rel SO (.prod B (.arr B))) (huy : muy = my ≫ uncons (Rel.val my))
    (mpu : Rel SO (.prod (.prod B (.arr B)) (.prod B (.arr B)))) (hpu : mpu = pair mux muy)
    (mboth : Rel SO SO) (hboth : mboth = dom mpu)
    (mh : Rel SO (.prod B B)) (hh : mh = pair (outl mux) (outl muy))
    (mrh : Rel (.prod B B) (.prod B B)) (hrh : mrh = ran mh) (G : Rel (.prod B B) (.prod B B))
    (mhq : Rel SO (.prod B B)) (hhq : mhq = mh ≫ G) (ml : Rel SO SO) (hl : ml = dom mhq)
    (mA1 : Rel SO (.prod (.arr B) (.arr B))) (hA1 : mA1 = pair (outr mux) my)
    (mS1 : Rel SO (.prod (.arr B) B)) (hS1 : mS1 = pair macc (outl mux))
    (mN1 : Rel SO (.arr B)) (hN1 : mN1 = snoc mS1) (mP1 : Rel SO SO) (hP1 : mP1 = pair mA1 mN1)
    (mL1 : Rel SO SO) (hL1 : mL1 = ml ≫ mP1) (mnb : Rel SO SO) (hnb : mnb = antiJoin mboth ml)
    (mA2 : Rel SO (.prod (.arr B) (.arr B))) (hA2 : mA2 = pair mx (outr muy))
    (mS2 : Rel SO (.prod (.arr B) B)) (hS2 : mS2 = pair macc (outl muy))
    (mN2 : Rel SO (.arr B)) (hN2 : mN2 = snoc mS2) (mP2 : Rel SO SO) (hP2 : mP2 = pair mA2 mN2)
    (mL2 : Rel SO SO) (hL2 : mL2 = mnb ≫ mP2) (mtk : Rel SO SO) (htk : mtk = mL1 ∪ mL2)
    (mT : Rel K SO) (hT : mT = St ≫ mtk) (mfl : Rel SO SO) (hfl : mfl = antiJoin mD mboth)
    (mSf : Rel K SO) (hSf : mSf = St ≫ mfl)
    (mc1 : Rel SO (.prod (.arr B) (.arr B))) (hc1 : mc1 = pair macc mx) (mC1 : Rel SO (.arr B)) (hC1 : mC1 = cat mc1)
    (mc2 : Rel SO (.prod (.arr B) (.arr B))) (hc2 : mc2 = pair mC1 my) (mC2 : Rel SO (.arr B)) (hC2 : mC2 = cat mc2)
    (mO : Rel K (.arr B)) (hO : mO = mSf ≫ mC2) (mU : Rel K (.arr B)) (hU : mU = out ∪ mO)
    (htest : ∀ a b, rep mrh (a, b) (a, b) → ((∃ c, rep G (a, b) c) ↔ le a b = true))
    (hW : codesWF) (h : mergeOK) :
    (∀ k s', rep mT k s' ↔ ∃ a x b y acc, rep St k ((a :: x, b :: y), acc) ∧
      (le a b = true ∧ s' = ((x, b :: y), acc ++ [a]) ∨ le a b = false ∧ s' = ((a :: x, y), acc ++ [b]))) ∧
    ∀ k z, rep mU k z ↔
      rep out k z ∨ ∃ x y acc, rep St k ((x, y), acc) ∧ (x = [] ∨ y = []) ∧ z = acc ++ x ++ y := by
  obtain ⟨⟨Df, Dp⟩, ⟨x63, xU⟩, ⟨xcf, xc⟩, ⟨y63, yU⟩, ⟨ycf, yc⟩, ⟨puf, pup⟩, ⟨bf, bp⟩, ⟨hhf, hhp⟩, ⟨rf, rp⟩,
    ⟨qf, qc⟩, ⟨lf, lp⟩, ⟨a1f, a1p⟩, ⟨s1f, s1p⟩, sn1, ⟨p1f, p1p⟩, ⟨l1f, l1c⟩, ⟨nbf, nbp⟩, ⟨a2f, a2p⟩,
    ⟨s2f, s2p⟩, sn2, ⟨p2f, p2p⟩, ⟨l2f, l2c⟩, ⟨tN, tNk, tNv, tFk, tFv, tK, tV, tk, tv⟩, ⟨Tf, Tc⟩, ⟨flf, flp⟩,
    ⟨sff, sfc⟩, ⟨c1f, c1p⟩, ct1, ⟨c2f, c2p⟩, ct2, ⟨Of, Oc⟩, ⟨uN, uNk, uNv, uFk, uFv, uK, uV, uk, uv⟩⟩ := h
  obtain ⟨xk, xh, xt⟩ := xU _ rfl _ rfl _ rfl
  obtain ⟨yk, yh, yt⟩ := yU _ rfl _ rfl _ rfl
  obtain ⟨xc1, xc2, xc3, xc4, xc5⟩ := xc _ rfl
  obtain ⟨yc1, yc2, yc3, yc4, yc5⟩ := yc _ rfl
  obtain ⟨pu1, pu2, pu3, pu4, pu5, pu6⟩ := pup _ rfl
  obtain ⟨hh1, hh2, hh3, hh4, hh5, hh6⟩ := hhp _ rfl
  obtain ⟨q1, q2, q3, q4, q5⟩ := qc _ rfl
  obtain ⟨a11, a12, a13, a14, a15, a16⟩ := a1p _ rfl
  obtain ⟨s11, s12, s13, s14, s15, s16⟩ := s1p _ rfl
  obtain ⟨p11, p12, p13, p14, p15, p16⟩ := p1p _ rfl
  obtain ⟨l11, l12, l13, l14, l15⟩ := l1c _ rfl
  obtain ⟨nb1, nb2⟩ := nbp _ rfl _ rfl
  obtain ⟨a21, a22, a23, a24, a25, a26⟩ := a2p _ rfl
  obtain ⟨s21, s22, s23, s24, s25, s26⟩ := s2p _ rfl
  obtain ⟨p21, p22, p23, p24, p25, p26⟩ := p2p _ rfl
  obtain ⟨l21, l22, l23, l24, l25⟩ := l2c _ rfl
  obtain ⟨T1, T2, T3, T4, T5⟩ := Tc _ rfl
  obtain ⟨fl1, fl2⟩ := flp _ rfl _ rfl
  obtain ⟨sf1, sf2, sf3, sf4, sf5⟩ := sfc _ rfl
  obtain ⟨c11, c12, c13, c14, c15, c16⟩ := c1p _ rfl
  obtain ⟨c21, c22, c23, c24, c25, c26⟩ := c2p _ rfl
  obtain ⟨O1, O2, O3, O4, O5⟩ := Oc _ rfl
  refine merge_round_set le out St mD mx my macc mux muy mpu mboth mh mrh G mhq ml mA1 mA2 mS1 mS2 mN1 mN2
    mP1 mP2 mL1 mL2 mnb mtk mfl mT mSf mc1 mc2 mC1 mC2 mO mU
    (by rw [hD]; exact rep_ran_corefl St (one_ok _ Df) (Dp _ rfl)) hx hy hacc
    (rep_uncons (Rel.val mx) x63 _ rfl _ rfl _ rfl xk xh xt)
    (by rw [hux]; exact rep_comp _ _ (codes_faithful_wf _ _ xcf).1 xc1 xc2 xc3 xc4 xc5)
    (rep_uncons (Rel.val my) y63 _ rfl _ rfl _ rfl yk yh yt)
    (by rw [huy]; exact rep_comp _ _ (codes_faithful_wf _ _ ycf).1 yc1 yc2 yc3 yc4 yc5)
    (by rw [hpu]; exact rep_pair _ _ (codes_faithful_wf _ _ puf).1 pu1 pu2 pu3 pu4 pu5 pu6)
    (by rw [hboth]; exact rep_dom_corefl mpu (one_ok _ bf) (bp _ rfl))
    (by rw [hh]; exact rep_pair _ _ (codes_faithful_wf _ _ hhf).1 hh1 hh2 hh3 hh4 hh5 hh6)
    (by rw [hrh]; exact rep_ran_corefl mh (one_ok _ rf) (rp _ rfl)) htest
    (by rw [hhq]; exact rep_comp _ _ (codes_faithful_wf _ _ qf).1 q1 q2 q3 q4 q5)
    (by rw [hl]; exact rep_dom_corefl mhq (one_ok _ lf) (lp _ rfl))
    (by rw [hA1]; exact rep_pair _ _ (codes_faithful_wf _ _ a1f).1 a11 a12 a13 a14 a15 a16)
    (by rw [hS1]; exact rep_pair _ _ (codes_faithful_wf _ _ s1f).1 s11 s12 s13 s14 s15 s16)
    (by rw [hN1]; exact rep_snoc mS1 hW sn1)
    (by rw [hP1]; exact rep_pair _ _ (codes_faithful_wf _ _ p1f).1 p11 p12 p13 p14 p15 p16)
    (by rw [hL1]; exact rep_comp _ _ (codes_faithful_wf _ _ l1f).1 l11 l12 l13 l14 l15)
    (by rw [hnb]; exact rep_antiJoin mboth ml (codes_faithful_wf _ _ nbf).1 nb1 nb2)
    (by rw [hA2]; exact rep_pair _ _ (codes_faithful_wf _ _ a2f).1 a21 a22 a23 a24 a25 a26)
    (by rw [hS2]; exact rep_pair _ _ (codes_faithful_wf _ _ s2f).1 s21 s22 s23 s24 s25 s26)
    (by rw [hN2]; exact rep_snoc mS2 hW sn2)
    (by rw [hP2]; exact rep_pair _ _ (codes_faithful_wf _ _ p2f).1 p21 p22 p23 p24 p25 p26)
    (by rw [hL2]; exact rep_comp _ _ (codes_faithful_wf _ _ l2f).1 l21 l22 l23 l24 l25)
    (by rw [htk]; exact rep_union_full mL1 mL2 tN tNk tNv tFk tFv (one_ok _ tK) (one_ok _ tV) tk tv)
    (by rw [hT]; exact rep_comp _ _ (codes_faithful_wf _ _ Tf).1 T1 T2 T3 T4 T5)
    (by rw [hfl]; exact rep_antiJoin mD mboth (codes_faithful_wf _ _ flf).1 fl1 fl2)
    (by rw [hSf]; exact rep_comp _ _ (codes_faithful_wf _ _ sff).1 sf1 sf2 sf3 sf4 sf5)
    (by rw [hc1]; exact rep_pair _ _ (codes_faithful_wf _ _ c1f).1 c11 c12 c13 c14 c15 c16)
    (by rw [hC1]; exact rep_cat_ok mc1 ct1)
    (by rw [hc2]; exact rep_pair _ _ (codes_faithful_wf _ _ c2f).1 c21 c22 c23 c24 c25 c26)
    (by rw [hC2]; exact rep_cat_ok mc2 ct2)
    (by rw [hO]; exact rep_comp _ _ (codes_faithful_wf _ _ Of).1 O1 O2 O3 O4 O5)
    (by rw [hU]; exact rep_union_full out mO uN uNk uNv uFk uFv (one_ok _ uK) (one_ok _ uV) uk uv)

#print axioms merge_round_rep

/-! ## `mergeOn` and `merge` -/

-- the fuel of `mergeOn q P`: both sides' payloads plus one
set_option hygiene false in
local notation "fuelP" => (Rel.val P).1.1.toNat + (Rel.val P).2.1.toNat + 1
-- the first state of `mergeOn q P`: nothing out, each pair of `P` with the empty `acc`
set_option hygiene false in
local notation "initP" => (Alg.zero, P ≫ pair (idU (ran P).val) (Alg.top (ran P).val (nilVal B)))
-- `mergeOn q`'s round `f`, bound by its defining equation, its values bound by theirs as `mergeOn` binds them
set_option hygiene false in
local notation "mergeF(" q ")" =>
  ∀ out St D, D = ran St → ∀ x, x = outl (outl D) → ∀ y, y = outr (outl D) → ∀ acc, acc = outr D →
    ∀ ux, ux = x ≫ uncons (Rel.val x) → ∀ uy, uy = y ≫ uncons (Rel.val y) → ∀ both, both = dom (pair ux uy) →
    ∀ h, h = pair (outl ux) (outl uy) → ∀ l, l = dom (h ≫ q (ran h)) →
    f (out, St) = (out ∪ St ≫ antiJoin D both ≫ cat (pair (cat (pair acc x)) y),
      St ≫ (l ≫ pair (pair (outr ux) y) (snoc (pair acc (outl ux))) ∪
        antiJoin both l ≫ pair (pair x (outr uy)) (snoc (pair acc (outl uy)))))
-- a round's values from its state `St` and `out`, each bound by its equation, the test `G` by `Gq`, then `J`
set_option hygiene false in
local notation "mergeVals(" Gq ", " J ")" =>
  ∀ mD, mD = ran St → ∀ mx, mx = outl (outl mD) → ∀ my, my = outr (outl mD) → ∀ macc, macc = outr mD →
  ∀ mux, mux = mx ≫ uncons (Rel.val mx) → ∀ muy, muy = my ≫ uncons (Rel.val my) → ∀ mpu, mpu = pair mux muy →
  ∀ mboth, mboth = dom mpu → ∀ mh, mh = pair (outl mux) (outl muy) → ∀ mrh, mrh = ran mh → ∀ G, G = Gq →
  ∀ mhq, mhq = mh ≫ G → ∀ ml, ml = dom mhq → ∀ mA1, mA1 = pair (outr mux) my →
  ∀ mS1, mS1 = pair macc (outl mux) → ∀ mN1, mN1 = snoc mS1 → ∀ mP1, mP1 = pair mA1 mN1 →
  ∀ mL1, mL1 = ml ≫ mP1 → ∀ mnb, mnb = antiJoin mboth ml → ∀ mA2, mA2 = pair mx (outr muy) →
  ∀ mS2, mS2 = pair macc (outl muy) → ∀ mN2, mN2 = snoc mS2 → ∀ mP2, mP2 = pair mA2 mN2 →
  ∀ mL2, mL2 = mnb ≫ mP2 → ∀ mtk, mtk = mL1 ∪ mL2 → ∀ mT, mT = St ≫ mtk → ∀ mfl, mfl = antiJoin mD mboth →
  ∀ mSf, mSf = St ≫ mfl → ∀ mc1, mc1 = pair macc mx → ∀ mC1, mC1 = cat mc1 → ∀ mc2, mc2 = pair mC1 my →
  ∀ mC2, mC2 = cat mc2 → ∀ mO, mO = mSf ≫ mC2 → ∀ mU, mU = out ∪ mO → J
-- the hypotheses of `mergeOn`'s first state: `rep_ran`'s at `P`, `rep_top`'s at `ran P` and `nilVal`, `rep_pair`'s
-- and `rep_comp`'s at `P ≫ ⟨idU, top⟩`
set_option hygiene false in
local notation "initOK" =>
  (oneFit(.prod (.arr B) (.arr B), Rel.n P, Rel.val P) ∧
    (Rel.n (ran P)).toNat * (1 : USize).toNat < USize.size ∧ (Rel.n (ran P)).toNat * (1 : USize).toNat < 2 ^ 63 ∧
    Vals.PickFits (.prod (.arr B) (.arr B)) (Rel.val (ran P))
      ((List.range ((Rel.n (ran P)).toNat * (1 : USize).toNat)).map (· / (1 : USize).toNat)) ∧
    Vals.PickFits (.arr B) (nilVal B)
      ((List.range ((Rel.n (ran P)).toNat * (1 : USize).toNat)).map (· % (1 : USize).toNat)) ∧
    pairOK(.prod (.arr B) (.arr B), idU (Rel.val (ran P)), Alg.top (Rel.val (ran P)) (nilVal B)) ∧
    cmpOK(.prod (.arr B) (.arr B), P, pair (idU (Rel.val (ran P))) (Alg.top (Rel.val (ran P)) (nilVal B))))

section Headline

open Freyd Freyd.Alg Freyd.Alg.RelSet

/-- **`mergeOn`, read back from its rounds**: with the first state `I` read back (`h0`) and each round's states and
    `out` read back (`hS`, `hO`, internal: `rep_mergeOn` discharges them from the primitives), `mergeOn q P` takes
    `k` to the merges, at `le`, of `k`'s pairs in `P`. The round `f` is bound by its defining equation (`hf`). -/
theorem mergeOn_rounds {K B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B))
    (P : Rel K (.prod (.arr B) (.arr B))) (le : B.El → B.El → Bool)
    (f : Rel K (.arr B) × Rel K SO → Rel K (.arr B) × Rel K SO) (hf : mergeF(q))
    (I : Rel K SO) (hI : I = P ≫ pair (idU (ran P).val) (Alg.top (ran P).val (nilVal B)))
    (h0 : ∀ k x y acc, rep I k ((x, y), acc) ↔ rep P k (x, y) ∧ acc = [])
    (hS : ∀ i, i < fuelP → ∀ k s', rep (f^[i + 1] (Alg.zero, I)).2 k s' ↔
      ∃ a x b y acc, rep (f^[i] (Alg.zero, I)).2 k ((a :: x, b :: y), acc) ∧
        (le a b = true ∧ s' = ((x, b :: y), acc ++ [a]) ∨ le a b = false ∧ s' = ((a :: x, y), acc ++ [b])))
    (hO : ∀ i, i < fuelP → ∀ k z, rep (f^[i + 1] (Alg.zero, I)).1 k z ↔ rep (f^[i] (Alg.zero, I)).1 k z ∨
      ∃ x y acc, rep (f^[i] (Alg.zero, I)).2 k ((x, y), acc) ∧ (x = [] ∨ y = []) ∧ z = acc ++ x ++ y) :
    ∀ k zs, rep (mergeOn q P) k zs ↔ ∃ xs ys, rep P k (xs, ys) ∧ zs = List.merge xs ys le := by
  obtain ⟨j, hj, he, hs⟩ := iter_stop (fun s : Rel K (.arr B) × Rel K SO => s.2.n == 0) f fuelP (Alg.zero, I)
  have hl : mergeOn q P = (f^[j] (Alg.zero, I)).1 := by
    rw [← he, hI]
    refine congrArg (fun g : Rel K (.arr B) × Rel K SO → Rel K (.arr B) × Rel K SO =>
      (iter fuelP (fun s => s.2.n == 0) g initP).1) (funext fun st => ?_)
    obtain ⟨o, S⟩ := st
    rw [hf o S _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl]
  have hN : ∀ k (s : List B.El × List B.El), rep P k s →
      s.1.length + s.2.length ≤ (Rel.val P).1.1.toNat + (Rel.val P).2.1.toNat := by
    rintro k s ⟨i, -, hi⟩
    rw [← hi]
    exact Nat.add_le_add (arr_row_length (Rel.val P).1 i) (arr_row_length (Rel.val P).2 i)
  have hstop : (Rel.val P).1.1.toNat + (Rel.val P).2.1.toNat < j ∨
      ∀ k (s : (List B.El × List B.El) × List B.El), ¬ rep (f^[j] (Alg.zero, I)).2 k s := by
    rcases hs with hs | hs
    · exact Or.inl (by omega)
    · refine Or.inr fun k s h => ?_
      obtain ⟨i, -⟩ := h
      have h0 : (f^[j] (Alg.zero, I)).2.n = 0 := beq_iff_eq.1 hs
      have h1 : (f^[j] (Alg.zero, I)).2.n.toNat = 0 := by rw [h0]; rfl
      exact Nat.not_lt_zero _ (Nat.lt_of_lt_of_eq i.2 h1)
  intro k zs
  rw [hl]
  exact merge_chain le (fun k s => rep P k s) (fun i k s => rep (f^[i] (Alg.zero, I)).2 k s)
    (fun i k z => rep (f^[i] (Alg.zero, I)).1 k z) fuelP h0 hS (fun _ _ ⟨i, _⟩ => i.elim0) hO
    ((Rel.val P).1.1.toNat + (Rel.val P).2.1.toNat) j hj hN hstop k zs

/-- **`mergeOn`, read back**: key `k` goes to `zs` exactly when `zs` is core's `List.merge xs ys le` of one of its
    pairs `(xs, ys)` in `P`, `le a b` the test on the heads `(a, b)` (`a` first when it passes). The fuel always
    suffices, so the stop is not in the conclusion. The round `f` is bound by its defining equation (`hf`); `h0` is
    the first state's hypotheses, `hW` `rep_snoc`'s universal one, and `hR` is, at every round up to the fuel, the
    test read back on the pairs of heads `mrh` the round meets and every primitive's hypotheses (`mergeOK`). -/
theorem rep_mergeOn {K B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B))
    (P : Rel K (.prod (.arr B) (.arr B))) (le : B.El → B.El → Bool)
    (f : Rel K (.arr B) × Rel K SO → Rel K (.arr B) × Rel K SO) (hf : mergeF(q)) (hW : codesWF) (h0 : initOK)
    (hR : ∀ i, i < fuelP → ∀ out St, out = (f^[i] initP).1 → St = (f^[i] initP).2 →
      mergeVals(q mrh, (∀ a b, rep mrh (a, b) (a, b) → ((∃ c, rep G (a, b) c) ↔ le a b = true)) ∧ mergeOK)) :
    ∀ k zs, rep (mergeOn q P) k zs ↔ ∃ xs ys, rep P k (xs, ys) ∧ zs = List.merge xs ys le := by
  obtain ⟨⟨Pf, Pp⟩, t1, t2, t3, t4, ⟨qf, qp⟩, ⟨mf, mp⟩⟩ := h0
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := qp _ rfl
  obtain ⟨m1, m2, m3, m4, m5⟩ := mp _ rfl
  have eR := rep_ran_corefl P (one_ok _ Pf) (Pp _ rfl)
  have eT := rep_top (Rel.val (ran P)) (nilVal B) t1 t2 t3 t4
  have eQ := rep_pair _ _ (codes_faithful_wf _ _ qf).1 q1 q2 q3 q4 q5 q6
  have eM := rep_comp _ _ (codes_faithful_wf _ _ mf).1 m1 m2 m3 m4 m5
  -- a pair of `P` is a row of `ran P`'s values
  have hrow : ∀ k p, rep P k p → ∃ i, (Rel.val (ran P)).row i = p := by
    intro k p hp
    have h : rep (ran P) p p := by rw [eR]; exact ⟨rfl, k, hp⟩
    obtain ⟨i, -, hi⟩ := h
    exact ⟨i, hi⟩
  have eTop : ∀ p acc, rep (Alg.top (Rel.val (ran P)) (nilVal B)) p acc ↔
      (∃ i, (Rel.val (ran P)).row i = p) ∧ acc = [] := by
    intro p acc
    rw [eT, comp_apply]
    constructor
    · rintro ⟨y, ⟨rfl, hp⟩, h⟩
      rw [comp_apply] at h
      obtain ⟨z, -, rfl, j, hj⟩ := h
      exact ⟨hp, by rw [← hj]; exact nilVal_row B j⟩
    · rintro ⟨hp, rfl⟩
      refine ⟨p, ⟨rfl, hp⟩, ?_⟩
      rw [comp_apply]
      exact ⟨[], trivial, rfl, ⟨0, by simp⟩, nilVal_row B _⟩
  have h0' : ∀ k x y acc, rep (P ≫ pair (idU (ran P).val) (Alg.top (ran P).val (nilVal B))) k ((x, y), acc) ↔
      rep P k (x, y) ∧ acc = [] := by
    intro k x y acc
    rw [eM, comp_apply]
    constructor
    · rintro ⟨p, hp, hq⟩
      rw [eQ] at hq
      obtain ⟨h1, h2⟩ := hq
      obtain ⟨rfl, -⟩ := (idU_holds _ _ _).1 h1
      exact ⟨hp, ((eTop _ _).1 h2).2⟩
    · rintro ⟨hp, rfl⟩
      refine ⟨(x, y), hp, ?_⟩
      rw [eQ]
      exact ⟨(idU_holds _ _ _).2 ⟨rfl, hrow k _ hp⟩, (eTop _ _).2 ⟨hrow k _ hp, rfl⟩⟩
  have one : ∀ i, i < fuelP →
      (∀ k s', rep (f^[i + 1] initP).2 k s' ↔ ∃ a x b y acc, rep (f^[i] initP).2 k ((a :: x, b :: y), acc) ∧
        (le a b = true ∧ s' = ((x, b :: y), acc ++ [a]) ∨ le a b = false ∧ s' = ((a :: x, y), acc ++ [b]))) ∧
      ∀ k z, rep (f^[i + 1] initP).1 k z ↔ rep (f^[i] initP).1 k z ∨
        ∃ x y acc, rep (f^[i] initP).2 k ((x, y), acc) ∧ (x = [] ∨ y = []) ∧ z = acc ++ x ++ y := by
    intro i hi
    obtain ⟨htest, hok⟩ := hR i hi _ _ rfl rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
      _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
      _ rfl _ rfl _ rfl _ rfl _ rfl
    have hr := merge_round_rep le _ _ _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ _ rfl _ rfl
      _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
      _ rfl _ rfl _ rfl htest hW hok
    have e : f^[i + 1] initP = _ :=
      hf (f^[i] initP).1 (f^[i] initP).2 _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
    rw [e]
    exact hr
  exact mergeOn_rounds q P le f hf _ rfl h0' (fun i hi => (one i hi).1) (fun i hi => (one i hi).2)

/-- **`merge`, read back**: `rep_mergeOn` at `q = pairsIn Q`, the test read back by `rep_pairsIn`: `le a b` is any
    Boolean test with `le a b = true` exactly when `a Q b` (`hle`). Hypotheses as `rep_mergeOn`'s, with
    `rep_pairsIn`'s `cmpOK` at each round's pairs of heads `mrh` in place of the test's read-back. -/
theorem rep_merge {K B : Obj} (Q : Rel B B) (P : Rel K (.prod (.arr B) (.arr B))) (le : B.El → B.El → Bool)
    (hle : ∀ a b, le a b = true ↔ rep Q a b)
    (f : Rel K (.arr B) × Rel K SO → Rel K (.arr B) × Rel K SO) (hf : mergeF(pairsIn Q)) (hW : codesWF)
    (h0 : initOK)
    (hR : ∀ i, i < fuelP → ∀ out St, out = (f^[i] initP).1 → St = (f^[i] initP).2 →
      mergeVals(pairsIn Q mrh, cmpOK(.prod B B, mrh, idU (t := .prod B B) (m := Rel.n Q) (Rel.key Q, Rel.val Q)) ∧
        mergeOK)) :
    ∀ k zs, rep (merge Q P) k zs ↔ ∃ xs ys, rep P k (xs, ys) ∧ zs = List.merge xs ys le := by
  refine rep_mergeOn (pairsIn Q) P le f hf hW h0 fun i hi out St ho hS => ?_
  intro mD hD mx hx my hy macc hacc mux hux muy huy mpu hpu mboth hboth mh hh mrh hrh G hG mhq hhq ml hl mA1 hA1
    mS1 hS1 mN1 hN1 mP1 hP1 mL1 hL1 mnb hnb mA2 hA2 mS2 hS2 mN2 hN2 mP2 hP2 mL2 hL2 mtk htk mT hT mfl hfl mSf hSf
    mc1 hc1 mC1 hC1 mc2 hc2 mC2 hC2 mO hO mU hU
  obtain ⟨hc, hok⟩ := hR i hi out St ho hS mD hD mx hx my hy macc hacc mux hux muy huy mpu hpu mboth hboth mh hh
    mrh hrh G hG mhq hhq ml hl mA1 hA1 mS1 hS1 mN1 hN1 mP1 hP1 mL1 hL1 mnb hnb mA2 hA2 mS2 hS2 mN2 hN2 mP2 hP2
    mL2 hL2 mtk htk mT hT mfl hfl mSf hSf mc1 hc1 mC1 hC1 mc2 hc2 mC2 hC2 mO hO mU hU
  refine ⟨fun a b hab => ?_, hok⟩
  obtain ⟨-, -, -, -, -, -, -, -, ⟨rf, rp⟩, -⟩ := hok
  have eRh : ∀ ab ab', rep mrh ab ab' ↔ ab = ab' ∧ ∃ s, rep mh s ab := fun ab ab' => by
    rw [hrh, rep_ran_corefl mh (one_ok _ rf) (rp _ rfl)]; exact Iff.rfl
  have eP := rep_pairsIn Q mrh hc
  rw [hG]
  constructor
  · rintro ⟨c, h⟩
    obtain ⟨h1, h2⟩ := (eP _ _).1 h
    obtain ⟨rfl, -⟩ := (eRh _ _).1 h1
    exact (hle a b).2 h2
  · intro h
    exact ⟨(a, b), (eP _ _).2 ⟨hab, (hle a b).1 h⟩⟩

end Headline

#print axioms mergeOn_rounds
#print axioms rep_mergeOn
#print axioms rep_merge

end LeetQ.Rel.Rep
