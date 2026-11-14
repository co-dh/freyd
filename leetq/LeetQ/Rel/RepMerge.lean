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

open FoldN Prim

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

end LeetQ.Rel.Rep
