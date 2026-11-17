/-
  Order on arrays read back: `orderedOn`/`ordered` (`suffix`, `uncons`, `mem`, `pair`, `antiJoin`, `dom`),
  `sortSet` (`setify°` then `ordered`), each from its primitives' read-backs. `thinL` is read back under its bit
  (`rep_thinLC`).
-/
import LeetQ.Rel.RepPerm
import LeetQ.Rel.RepSubseq

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

open FoldN OpsN Prim ListN

/-- Every element `Q`-below every later one, said on the suffixes: `y` heads a suffix `y :: zs` of `xs` and `z` is
    in `zs` exactly when `y` comes before `z` in `xs`. -/
theorem suffix_pairwise {β : Type _} (R : β → β → Prop) (xs : List β) :
    (∀ y zs, (y :: zs) <:+ xs → ∀ z ∈ zs, R y z) ↔ xs.Pairwise R := by
  induction xs with
  | nil => exact ⟨fun _ => List.Pairwise.nil, fun _ y zs h => absurd (List.suffix_nil.1 h) (List.cons_ne_nil _ _)⟩
  | cons a l ih =>
    rw [List.pairwise_cons, ← ih]
    constructor
    · intro h
      exact ⟨h a l (List.suffix_refl _), fun y zs hs => h y zs (hs.trans (List.suffix_cons a l))⟩
    · rintro ⟨h1, h2⟩ y zs hs
      rcases List.suffix_cons_iff.1 hs with e | hs
      · obtain ⟨rfl, rfl⟩ := List.cons.inj e
        exact h1
      · exact h2 y zs hs

-- every primitive's hypotheses in `orderedOn q X` past `suffix`, at the pieces bound by their equations
set_option hygiene false in
local notation "ordOK" =>
  (oneFit(.arr B, Rel.n Su, Rel.val Su) ∧ uncOK(B, Wu) ∧ cmpOK(.arr B, Su, uncons (Rel.val Wu)) ∧
    oneFit(.prod B (.arr B), Rel.n T, Rel.val T) ∧ oneFit(.arr B, Rel.n O, Rel.val O) ∧
    Vals.PickFits (.arr B) (Rel.val V) (List.range (Rel.n V).toNat) ∧
    Vals.PickFits (.arr B) (Rel.val V) ((List.range (Rel.n V).toNat).flatMap fun r =>
      if h : r < (Rel.n V).toNat then List.replicate ((Rel.val V).row ⟨r, h⟩).length r else []) ∧
    cmpOK(.arr B, O, mem (Rel.val V)) ∧ pairOK(.prod B (.arr B), outl D, M) ∧
    oneFit(.prod B B, Rel.n yz, Rel.val yz) ∧ ajOK(.prod B B, yz, q E) ∧
    oneFit(.prod B (.arr B), Rel.n bad, Rel.key bad) ∧ cmpOK(.prod B (.arr B), T, dom bad) ∧
    oneFit(.arr B, Rel.n C, Rel.key C) ∧ ajOK(.arr B, idU X, dom C))

/-- **`orderedOn`, read back**: an array `xs` of `X` goes to itself exactly when, for every suffix `y :: zs` of `xs`
    and every `z` of `zs`, the test `q E` reaches `(y, z)`; and the test sees every such `(y, z)` (`E` holds it).
    The pieces are bound as `orderedOn` builds them: `Su` the suffixes, `T` their `uncons`, `D = ran T`,
    `yz` the pairs `(y, z)`, `bad` those the test misses, `C` the arrays with a bad suffix. Hypotheses:
    `hS`, `suffix X` read back (`rep_suffixC`), and every primitive's at the pieces (`ordOK`). -/
theorem rep_orderedOn {B : Obj} {n : USize} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B))
    (X : Vals (.arr B) n) (hS : ∀ xs ys, rep (suffix X) xs ys ↔ (∃ j, X.row j = xs) ∧ ys <:+ xs)
    (Su : Rel (.arr B) (.arr B)) (hSu : Su = suffix X) (Wu : Rel (.arr B) (.arr B)) (hWu : Wu = ran Su)
    (T : Rel (.arr B) (.prod B (.arr B))) (hT : T = Su ≫ uncons (Rel.val Wu))
    (D : Rel (.prod B (.arr B)) (.prod B (.arr B))) (hD : D = ran T)
    (O : Rel (.prod B (.arr B)) (.arr B)) (hO : O = outr D) (V : Rel (.arr B) (.arr B)) (hV : V = ran O)
    (M : Rel (.prod B (.arr B)) B) (hM : M = O ≫ mem (Rel.val V))
    (yz : Rel (.prod B (.arr B)) (.prod B B)) (hyz : yz = pair (outl D) M)
    (E : Rel (.prod B B) (.prod B B)) (hE : E = ran yz)
    (bad : Rel (.prod B (.arr B)) (.prod B B)) (hbad : bad = antiJoin yz (q E))
    (C : Rel (.arr B) (.prod B (.arr B))) (hC : C = T ≫ dom bad)
    -- kept: fits and codes of the suffix pieces `Su`, `Wu`, `V`, `O`, `bad`, `C`, kernel intermediates
    (h : ordOK) :
    (∀ xs y zs z, (∃ i, X.row i = xs) → (y :: zs) <:+ xs → z ∈ zs → rep E (y, z) (y, z)) ∧
    ∀ xs ys, rep (orderedOn q X) xs ys ↔ (∃ i, X.row i = xs) ∧ ys = xs ∧
      ∀ y zs, (y :: zs) <:+ xs → ∀ z ∈ zs, ∃ w, rep (q E) w (y, z) := by
  obtain ⟨⟨hSf, hSp⟩, hUn, ⟨hcf, hc'⟩, ⟨hTf, hTp⟩, ⟨hOf, hOp⟩, hVv, hVk, ⟨hmf, hm'⟩, ⟨hpf, hp'⟩,
    ⟨hyf, hyp⟩, ⟨hbf, hb'⟩, ⟨hdf, hdp⟩, ⟨hCf, hC'⟩, ⟨hDf, hDp⟩, ⟨hAf, hA'⟩⟩ := h
  have u1 := hUn _ rfl _ rfl _ rfl
  obtain ⟨c1, c2, c3, c4⟩ := hc' _ rfl
  obtain ⟨m1, m2, m3, m4⟩ := hm' _ rfl
  obtain ⟨p1, p2, p3, p4, p5⟩ := hp' _ rfl
  obtain ⟨b1, b2⟩ := hb'
  obtain ⟨k1, k2, k3, k4⟩ := hC' _ rfl
  obtain ⟨a1, a2⟩ := hA'
  have eS : ∀ xs ys, rep Su xs ys ↔ (∃ j, X.row j = xs) ∧ ys <:+ xs := by
    rw [hSu]; exact hS
  have eW : ∀ a a', rep Wu a a' ↔ a = a' ∧ ∃ k, rep Su k a := fun a a' => by
    rw [hWu, rep_ran_corefl Su (one_ok _ hSf) (hSp)]; exact Iff.rfl
  have eU := rep_uncons (Rel.val Wu) _ rfl _ rfl _ rfl u1
  -- `T`: an array to the head and tail of each of its non-empty suffixes
  have eT : ∀ xs (p : (Obj.prod B (.arr B)).El), rep T xs p ↔ rep Su xs (p.1 :: p.2) := fun xs p => by
    rw [hT, rep_comp _ _ (codes_faithful_wf _ _ hcf).1 c1 c2 c3 c4, Core.Rel.comp_apply]
    constructor
    · rintro ⟨a, ha, hu⟩
      obtain ⟨-, rfl⟩ := (eU a p.1 p.2).1 hu
      exact ha
    · intro hs
      obtain ⟨j, -, hj⟩ := (eW _ _).2 ⟨rfl, xs, hs⟩
      exact ⟨_, hs, (eU _ p.1 p.2).2 ⟨⟨j, hj⟩, rfl⟩⟩
  have eD : ∀ p p', rep D p p' ↔ p = p' ∧ ∃ xs, rep T xs p := fun p p' => by
    rw [hD, rep_ran_corefl T (one_ok _ hTf) (hTp)]; exact Iff.rfl
  have eO : ∀ p a, rep O p a ↔ (∃ xs, rep T xs p) ∧ a = p.2 := fun p a => by
    rw [hO, rep_apply, outr_holds]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨rfl, hx⟩ := (eD _ _).1 hy
      exact ⟨hx, rfl⟩
    · rintro ⟨hx, rfl⟩
      exact ⟨p.1, (eD _ _).2 ⟨rfl, hx⟩⟩
  have eV : ∀ a a', rep V a a' ↔ a = a' ∧ ∃ p, rep O p a := fun a a' => by
    rw [hV, rep_ran_corefl O (one_ok _ hOf) (hOp)]; exact Iff.rfl
  have eMem := rep_mem (Rel.val V) hVv hVk
  have eM : ∀ p z, rep M p z ↔ (∃ xs, rep T xs p) ∧ z ∈ p.2 := fun p z => by
    rw [hM, rep_comp _ _ (codes_faithful_wf _ _ hmf).1 m1 m2 m3 m4, Core.Rel.comp_apply]
    constructor
    · rintro ⟨a, ho, hm⟩
      obtain ⟨hx, rfl⟩ := (eO p a).1 ho
      exact ⟨hx, ((eMem _ _).1 hm).2⟩
    · rintro ⟨hx, hz⟩
      have ho := (eO p p.2).2 ⟨hx, rfl⟩
      obtain ⟨i, -, hi⟩ := (eV _ _).2 ⟨rfl, p, ho⟩
      exact ⟨p.2, ho, (eMem _ _).2 ⟨⟨i, hi⟩, hz⟩⟩
  have eL : ∀ p y, rep (outl D) p y ↔ (∃ xs, rep T xs p) ∧ y = p.1 := fun p y => by
    rw [rep_apply, outl_holds]
    constructor
    · rintro ⟨zs, hy⟩
      obtain ⟨rfl, hx⟩ := (eD _ _).1 hy
      exact ⟨hx, rfl⟩
    · rintro ⟨hx, rfl⟩
      exact ⟨p.2, (eD _ _).2 ⟨rfl, hx⟩⟩
  have eP := rep_pair _ _ (codes_faithful_wf _ _ hpf).1 p1 p2 p3 p4 p5
  have eyz : ∀ p y z, rep yz p (y, z) ↔ (∃ xs, rep T xs p) ∧ y = p.1 ∧ z ∈ p.2 := fun p y z => by
    rw [hyz]
    refine (Iff.of_eq (congrFun (congrFun eP p) (y, z))).trans ((and_congr (eL p y) (eM p z)).trans ?_)
    exact ⟨fun ⟨⟨h1, h2⟩, _, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h1, h3⟩⟩
  have eE : ∀ w w', rep E w w' ↔ w = w' ∧ ∃ p, rep yz p w := fun w w' => by
    rw [hE, rep_ran_corefl yz (one_ok _ hyf) (hyp)]; exact Iff.rfl
  have ebad : ∀ p v, rep bad p v ↔ rep yz p v ∧ ¬ ∃ w, rep (q E) w v := fun p v => by
    rw [hbad, rep_antiJoin yz (q E) (codes_faithful_wf _ _ hbf).1 b1 b2, Core.Rel.comp_apply]
    exact ⟨fun ⟨_, h1, rfl, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨v, h1, rfl, h2⟩⟩
  have edb : ∀ p p', rep (dom bad) p p' ↔ p = p' ∧ ∃ v, rep bad p v := fun p p' => by
    rw [rep_dom_corefl bad (one_ok _ hdf) (hdp)]; exact Iff.rfl
  have eC : ∀ xs p, rep C xs p ↔ rep T xs p ∧ ∃ v, rep bad p v := fun xs p => by
    rw [hC, rep_comp _ _ (codes_faithful_wf _ _ hCf).1 k1 k2 k3 k4, Core.Rel.comp_apply]
    constructor
    · rintro ⟨p', ht, hd⟩
      obtain ⟨rfl, hv⟩ := (edb _ _).1 hd
      exact ⟨ht, hv⟩
    · rintro ⟨ht, hv⟩
      exact ⟨p, ht, (edb _ _).2 ⟨rfl, hv⟩⟩
  have edC : ∀ xs xs', rep (dom C) xs xs' ↔ xs = xs' ∧ ∃ p, rep C xs p := fun xs xs' => by
    rw [rep_dom_corefl C (one_ok _ hDf) (hDp)]; exact Iff.rfl
  have eA : ∀ xs ys, rep (antiJoin (idU X) (dom C)) xs ys ↔
      rep (idU X) xs ys ∧ ¬ ∃ w, rep (dom C) w ys := fun xs ys => by
    rw [rep_antiJoin (idU X) (dom C) (codes_faithful_wf _ _ hAf).1 a1 a2, Core.Rel.comp_apply]
    exact ⟨fun ⟨_, h1, rfl, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨ys, h1, rfl, h2⟩⟩
  -- the suffix `y :: zs` of a row `xs` and `z` of `zs` give the pair `(y, z)` of `yz`
  have hyz' : ∀ xs y zs z, (∃ i, X.row i = xs) → (y :: zs) <:+ xs → z ∈ zs → rep yz (y, zs) (y, z) :=
    fun xs y zs z hx hs hz => (eyz _ _ _).2 ⟨⟨xs, (eT _ _).2 ((eS _ _).2 ⟨hx, hs⟩)⟩, rfl, hz⟩
  -- a row has a bad suffix exactly when `dom C` holds it
  have key : ∀ xs, (∃ i, X.row i = xs) → ((∃ w, rep (dom C) w xs) ↔
      ∃ y zs, (y :: zs) <:+ xs ∧ ∃ z ∈ zs, ¬ ∃ w, rep (q E) w (y, z)) := by
    intro xs hx
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨rfl, p, hp⟩ := (edC _ _).1 hw
      obtain ⟨ht, ⟨y', z⟩, hv⟩ := (eC _ _).1 hp
      obtain ⟨hy, hn⟩ := (ebad _ _).1 hv
      obtain ⟨-, rfl, hz⟩ := (eyz _ _ _).1 hy
      exact ⟨p.1, p.2, ((eS _ _).1 ((eT _ _).1 ht)).2, z, hz, hn⟩
    · rintro ⟨y, zs, hs, z, hz, hn⟩
      have ht : rep T xs (y, zs) := (eT _ _).2 ((eS _ _).2 ⟨hx, hs⟩)
      exact ⟨xs, (edC _ _).2 ⟨rfl, (y, zs), (eC _ _).2 ⟨ht, (y, z), (ebad _ _).2 ⟨hyz' xs y zs z hx hs hz, hn⟩⟩⟩⟩
  refine ⟨fun xs y zs z hx hs hz => (eE _ _).2 ⟨rfl, (y, zs), hyz' xs y zs z hx hs hz⟩, fun xs ys => ?_⟩
  have e : orderedOn q X = antiJoin (idU X) (dom C) := by subst hC hbad hE hyz hM hV hO hD hT hWu hSu; rfl
  rw [e, eA, rep_apply, idU_holds]
  constructor
  · rintro ⟨⟨rfl, hx⟩, hn⟩
    exact ⟨hx, rfl, fun y zs hs z hz => Classical.byContradiction fun hq => hn ((key xs hx).2 ⟨y, zs, hs, z, hz, hq⟩)⟩
  · rintro ⟨hx, rfl, hall⟩
    refine ⟨⟨rfl, hx⟩, fun hw => ?_⟩
    obtain ⟨y, zs, hs, z, hz, hq⟩ := (key ys hx).1 hw
    exact hq (hall y zs hs z hz)

/-- **`orderedOn`'s read-back at `q := pairsIn Q` in `Pairwise` form**, for any relation `O` read back as it: the test
    read back by `rep_pairsIn` (`hq`), the suffix form turned into `Pairwise` (`suffix_pairwise`). -/
theorem pairwise_of_orderedOn {B : Obj} {n : USize} (Q : Rel B B) (X : Vals (.arr B) n) (O : Rel (.arr B) (.arr B))
    (E : Rel (.prod B B) (.prod B B))
    (hq : cmpOK(.prod B B, E, idU (t := .prod B B) (m := Rel.n Q) (Rel.key Q, Rel.val Q)))
    (h1 : ∀ xs y zs z, (∃ i, X.row i = xs) → (y :: zs) <:+ xs → z ∈ zs → rep E (y, z) (y, z))
    (h2 : ∀ xs ys, rep O xs ys ↔ (∃ i, X.row i = xs) ∧ ys = xs ∧
      ∀ y zs, (y :: zs) <:+ xs → ∀ z ∈ zs, ∃ w, rep (pairsIn Q E) w (y, z)) :
    ∀ xs ys, rep O xs ys ↔ (∃ i, X.row i = xs) ∧ ys = xs ∧ xs.Pairwise (fun y z => rep Q y z) := by
  intro xs ys
  rw [h2]
  refine and_congr_right fun hx => and_congr_right fun _ => Iff.trans ?_ (suffix_pairwise _ xs)
  exact ⟨fun hall y zs hs z hz => by
      obtain ⟨w, hw⟩ := hall y zs hs z hz
      exact ((rep_pairsIn Q E hq w (y, z)).1 hw).2,
    fun hall y zs hs z hz => ⟨(y, z), (rep_pairsIn Q E hq _ _).2 ⟨h1 xs y zs z hx hs hz, hall y zs hs z hz⟩⟩⟩

/-- **`sortSet(Q)`, read back**: `s` goes to `ys` exactly when `setify` takes the array `ys` of `Y` to `s` and `ys`
    is `Q`-ordered. `sortSet Q Y` is `(setify Y)° ≫ ordered Q Y` (`rep_comp`, `rep_conv`, `rep_orderedC`).
    Hypotheses: `ordered Q Y` read back (`eO`: `rep_orderedC`), `rep_comp`'s at the composite. -/
theorem rep_sortSet {B : Obj} {n : USize} (Q : Rel B B) (Y : Vals (.arr B) n)
    (eO : ∀ xs ys, rep (ordered Q Y) xs ys ↔ (∃ i, Y.row i = xs) ∧ ys = xs ∧ xs.Pairwise (fun y z => rep Q y z))
    (hc : cmpOK(.arr B, (setify Y)°, ordered Q Y)) :
    ∀ s ys, rep (sortSet Q Y) s ys ↔
      rep (setify Y) ys s ∧ (∃ i, Y.row i = ys) ∧ ys.Pairwise (fun y z => rep Q y z) := by
  obtain ⟨hf, h'⟩ := hc
  obtain ⟨c1, c2, c3, c4⟩ := h' _ rfl
  intro s ys
  rw [show sortSet Q Y = (setify Y)° ≫ ordered Q Y from rfl,
    rep_comp _ _ (codes_faithful_wf _ _ hf).1 c1 c2 c3 c4, Core.Rel.comp_apply]
  constructor
  · rintro ⟨m, hm, ho⟩
    obtain ⟨hx, rfl, hp⟩ := (eO m ys).1 ho
    rw [rep_conv] at hm
    exact ⟨hm, hx, hp⟩
  · rintro ⟨hs, hx, hp⟩
    exact ⟨ys, by rw [rep_conv]; exact hs, (eO ys ys).2 ⟨hx, rfl, hp⟩⟩

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.Rep.suffix_pairwise
#print axioms LeetQ.Rel.Rep.rep_orderedOn
#print axioms LeetQ.Rel.Rep.rep_sortSet
