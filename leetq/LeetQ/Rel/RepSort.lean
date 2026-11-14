/-
  Order on arrays read back: `orderedOn`/`ordered` (`suffix`, `uncons`, `mem`, `pair`, `antiJoin`, `dom`),
  `sortSet` (`setify°` then `ordered`), `thinL` (`setify`, the divisions, `subseq`), each from its primitives'
  read-backs.
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
    `rep_suffix`'s (`g`, `hg`, `hR`) and every primitive's at the pieces (`ordOK`). -/
theorem rep_orderedOn {B : Obj} {n : USize} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B))
    (X : Vals (.arr B) n)
    (g : Rel (.arr B) (.arr B) × Rel (.arr B) (.arr B) → Rel (.arr B) (.arr B) × Rel (.arr B) (.arr B))
    (hg : ∀ S F, g (S, F) = (S ∪ F ≫ tail (ran F).val, F ≫ tail (ran F).val))
    (hR : ∀ i, i ≤ X.1.toNat → ∀ S F, S = (g^[i] (idU X, idU X)).1 → F = (g^[i] (idU X, idU X)).2 → sufOK)
    (Su : Rel (.arr B) (.arr B)) (hSu : Su = suffix X) (Wu : Rel (.arr B) (.arr B)) (hWu : Wu = ran Su)
    (T : Rel (.arr B) (.prod B (.arr B))) (hT : T = Su ≫ uncons (Rel.val Wu))
    (D : Rel (.prod B (.arr B)) (.prod B (.arr B))) (hD : D = ran T)
    (O : Rel (.prod B (.arr B)) (.arr B)) (hO : O = outr D) (V : Rel (.arr B) (.arr B)) (hV : V = ran O)
    (M : Rel (.prod B (.arr B)) B) (hM : M = O ≫ mem (Rel.val V))
    (yz : Rel (.prod B (.arr B)) (.prod B B)) (hyz : yz = pair (outl D) M)
    (E : Rel (.prod B B) (.prod B B)) (hE : E = ran yz)
    (bad : Rel (.prod B (.arr B)) (.prod B B)) (hbad : bad = antiJoin yz (q E))
    (C : Rel (.arr B) (.prod B (.arr B))) (hC : C = T ≫ dom bad)
    (h : ordOK) :
    (∀ xs y zs z, (∃ i, X.row i = xs) → (y :: zs) <:+ xs → z ∈ zs → rep E (y, z) (y, z)) ∧
    ∀ xs ys, rep (orderedOn q X) xs ys ↔ (∃ i, X.row i = xs) ∧ ys = xs ∧
      ∀ y zs, (y :: zs) <:+ xs → ∀ z ∈ zs, ∃ w, rep (q E) w (y, z) := by
  obtain ⟨⟨hSf, hSp⟩, ⟨h63, hUn⟩, ⟨hcf, hc'⟩, ⟨hTf, hTp⟩, ⟨hOf, hOp⟩, hVv, hVk, ⟨hmf, hm'⟩, ⟨hpf, hp'⟩,
    ⟨hyf, hyp⟩, ⟨hbf, hb'⟩, ⟨hdf, hdp⟩, ⟨hCf, hC'⟩, ⟨hDf, hDp⟩, ⟨hAf, hA'⟩⟩ := h
  obtain ⟨u1, u2, u3⟩ := hUn _ rfl _ rfl _ rfl
  obtain ⟨c1, c2, c3, c4⟩ := hc' _ rfl
  obtain ⟨m1, m2, m3, m4⟩ := hm' _ rfl
  obtain ⟨p1, p2, p3, p4, p5⟩ := hp' _ rfl
  obtain ⟨b1, b2⟩ := hb'
  obtain ⟨k1, k2, k3, k4⟩ := hC' _ rfl
  obtain ⟨a1, a2⟩ := hA'
  have eS : ∀ xs ys, rep Su xs ys ↔ (∃ j, X.row j = xs) ∧ ys <:+ xs := by
    rw [hSu]; exact rep_suffix X g hg hR
  have eW : ∀ a a', rep Wu a a' ↔ a = a' ∧ ∃ k, rep Su k a := fun a a' => by
    rw [hWu, rep_ran_corefl Su (one_ok _ hSf) (hSp)]; exact Iff.rfl
  have eU := rep_uncons (Rel.val Wu) h63 _ rfl _ rfl _ rfl u1 u2 u3
  -- `T`: an array to the head and tail of each of its non-empty suffixes
  have eT : ∀ xs (p : (Obj.prod B (.arr B)).El), rep T xs p ↔ rep Su xs (p.1 :: p.2) := fun xs p => by
    rw [hT, rep_comp _ _ (codes_faithful_wf _ _ hcf).1 c1 c2 c3 c4, Freyd.Alg.RelSet.comp_apply]
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
    rw [hM, rep_comp _ _ (codes_faithful_wf _ _ hmf).1 m1 m2 m3 m4, Freyd.Alg.RelSet.comp_apply]
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
    rw [hbad, rep_antiJoin yz (q E) (codes_faithful_wf _ _ hbf).1 b1 b2, Freyd.Alg.RelSet.comp_apply]
    exact ⟨fun ⟨_, h1, rfl, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨v, h1, rfl, h2⟩⟩
  have edb : ∀ p p', rep (dom bad) p p' ↔ p = p' ∧ ∃ v, rep bad p v := fun p p' => by
    rw [rep_dom_corefl bad (one_ok _ hdf) (hdp)]; exact Iff.rfl
  have eC : ∀ xs p, rep C xs p ↔ rep T xs p ∧ ∃ v, rep bad p v := fun xs p => by
    rw [hC, rep_comp _ _ (codes_faithful_wf _ _ hCf).1 k1 k2 k3 k4, Freyd.Alg.RelSet.comp_apply]
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
    rw [rep_antiJoin (idU X) (dom C) (codes_faithful_wf _ _ hAf).1 a1 a2, Freyd.Alg.RelSet.comp_apply]
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

/-- **`ordered(Q)`, read back**: an array `xs` of `X` goes to itself exactly when each element is `Q`-below every
    later one. `rep_orderedOn` at `q := pairsIn Q` (`rep_pairsIn`), the suffix form turned into `Pairwise`
    (`suffix_pairwise`). Hypotheses: `rep_orderedOn`'s, then `rep_pairsIn`'s at `E`. -/
theorem rep_ordered {B : Obj} {n : USize} (Q : Rel B B) (X : Vals (.arr B) n)
    (g : Rel (.arr B) (.arr B) × Rel (.arr B) (.arr B) → Rel (.arr B) (.arr B) × Rel (.arr B) (.arr B))
    (hg : ∀ S F, g (S, F) = (S ∪ F ≫ tail (ran F).val, F ≫ tail (ran F).val))
    (hR : ∀ i, i ≤ X.1.toNat → ∀ S F, S = (g^[i] (idU X, idU X)).1 → F = (g^[i] (idU X, idU X)).2 → sufOK)
    (Su : Rel (.arr B) (.arr B)) (hSu : Su = suffix X) (Wu : Rel (.arr B) (.arr B)) (hWu : Wu = ran Su)
    (T : Rel (.arr B) (.prod B (.arr B))) (hT : T = Su ≫ uncons (Rel.val Wu))
    (D : Rel (.prod B (.arr B)) (.prod B (.arr B))) (hD : D = ran T)
    (O : Rel (.prod B (.arr B)) (.arr B)) (hO : O = outr D) (V : Rel (.arr B) (.arr B)) (hV : V = ran O)
    (M : Rel (.prod B (.arr B)) B) (hM : M = O ≫ mem (Rel.val V))
    (yz : Rel (.prod B (.arr B)) (.prod B B)) (hyz : yz = pair (outl D) M)
    (E : Rel (.prod B B) (.prod B B)) (hE : E = ran yz)
    (bad : Rel (.prod B (.arr B)) (.prod B B)) (hbad : bad = antiJoin yz (pairsIn Q E))
    (C : Rel (.arr B) (.prod B (.arr B))) (hC : C = T ≫ dom bad)
    (h : ∀ q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B), q = pairsIn Q → ordOK)
    (hq : cmpOK(.prod B B, E, idU (t := .prod B B) (m := Rel.n Q) (Rel.key Q, Rel.val Q))) :
    ∀ xs ys, rep (ordered Q X) xs ys ↔ (∃ i, X.row i = xs) ∧ ys = xs ∧ xs.Pairwise (fun y z => rep Q y z) := by
  obtain ⟨h1, h2⟩ := rep_orderedOn (pairsIn Q) X g hg hR Su hSu Wu hWu T hT D hD O hO V hV M hM yz hyz E hE bad hbad
    C hC (h _ rfl)
  intro xs ys
  rw [show ordered Q X = orderedOn (pairsIn Q) X from rfl, h2]
  refine and_congr_right fun hx => and_congr_right fun _ => Iff.trans ?_ (suffix_pairwise _ xs)
  exact ⟨fun hall y zs hs z hz => by
      obtain ⟨w, hw⟩ := hall y zs hs z hz
      exact ((rep_pairsIn Q E hq w (y, z)).1 hw).2,
    fun hall y zs hs z hz => ⟨(y, z), (rep_pairsIn Q E hq _ _).2 ⟨h1 xs y zs z hx hs hz, hall y zs hs z hz⟩⟩⟩

/-- **`sortSet(Q)`, read back**: `s` goes to `ys` exactly when `setify` takes the array `ys` of `Y` to `s` and `ys`
    is `Q`-ordered. `sortSet Q Y` is `(setify Y)° ≫ ordered Q Y` (`rep_comp`, `rep_conv`, `rep_ordered`).
    Hypotheses: `rep_ordered`'s at `Y`, `rep_comp`'s at the composite. -/
theorem rep_sortSet {B : Obj} {n : USize} (Q : Rel B B) (Y : Vals (.arr B) n)
    (g : Rel (.arr B) (.arr B) × Rel (.arr B) (.arr B) → Rel (.arr B) (.arr B) × Rel (.arr B) (.arr B))
    (hg : ∀ S F, g (S, F) = (S ∪ F ≫ tail (ran F).val, F ≫ tail (ran F).val))
    (hR : ∀ i, i ≤ Y.1.toNat → ∀ S F, S = (g^[i] (idU Y, idU Y)).1 → F = (g^[i] (idU Y, idU Y)).2 → sufOK)
    (Su : Rel (.arr B) (.arr B)) (hSu : Su = suffix Y) (Wu : Rel (.arr B) (.arr B)) (hWu : Wu = ran Su)
    (T : Rel (.arr B) (.prod B (.arr B))) (hT : T = Su ≫ uncons (Rel.val Wu))
    (D : Rel (.prod B (.arr B)) (.prod B (.arr B))) (hD : D = ran T)
    (O : Rel (.prod B (.arr B)) (.arr B)) (hO : O = outr D) (V : Rel (.arr B) (.arr B)) (hV : V = ran O)
    (M : Rel (.prod B (.arr B)) B) (hM : M = O ≫ mem (Rel.val V))
    (yz : Rel (.prod B (.arr B)) (.prod B B)) (hyz : yz = pair (outl D) M)
    (E : Rel (.prod B B) (.prod B B)) (hE : E = ran yz)
    (bad : Rel (.prod B (.arr B)) (.prod B B)) (hbad : bad = antiJoin yz (pairsIn Q E))
    (C : Rel (.arr B) (.prod B (.arr B))) (hC : C = T ≫ dom bad)
    (h : ∀ q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B), q = pairsIn Q → ∀ X, X = Y → ordOK)
    (hq : cmpOK(.prod B B, E, idU (t := .prod B B) (m := Rel.n Q) (Rel.key Q, Rel.val Q)))
    (hc : cmpOK(.arr B, (setify Y)°, ordered Q Y)) :
    ∀ s ys, rep (sortSet Q Y) s ys ↔
      rep (setify Y) ys s ∧ (∃ i, Y.row i = ys) ∧ ys.Pairwise (fun y z => rep Q y z) := by
  obtain ⟨hf, h'⟩ := hc
  obtain ⟨c1, c2, c3, c4⟩ := h' _ rfl
  have eO := rep_ordered Q Y g hg hR Su hSu Wu hWu T hT D hD O hO V hV M hM yz hyz E hE bad hbad C hC
    (fun q hq' => h q hq' Y rfl) hq
  intro s ys
  rw [show sortSet Q Y = (setify Y)° ≫ ordered Q Y from rfl,
    rep_comp _ _ (codes_faithful_wf _ _ hf).1 c1 c2 c3 c4, Freyd.Alg.RelSet.comp_apply]
  constructor
  · rintro ⟨m, hm, ho⟩
    obtain ⟨hx, rfl, hp⟩ := (eO m ys).1 ho
    rw [rep_conv] at hm
    exact ⟨hm, hx, hp⟩
  · rintro ⟨hs, hx, hp⟩
    exact ⟨ys, by rw [rep_conv]; exact hs, (eO ys ys).2 ⟨hx, rfl, hp⟩⟩

open DivN

-- `rep_inter`'s hypotheses at `L ∩ R` (`K` the keys' object, `V` the values'), its codes `pc` bound
set_option hygiene false in
local notation "interOK(" K ", " V ", " L ", " R ")" =>
  (∀ pc : Vector Code 2, pc = pairs #v[L, R] →
    codesOK(pc, (#v[⟨Rel.n L, (Rel.key L, Rel.val L)⟩, ⟨Rel.n R, (Rel.key R, Rel.val R)⟩] :
      Vector (Part (.prod K V)) 2)) ∧
    (Vals.PickFits K (Rel.key L) (List.range (Rel.n L).toNat) ∧ Vals.PickFits V (Rel.val L) (List.range (Rel.n L).toNat)))

/-- **`thinL(Q)`, read back over `subseq` and `setify`**: `xs` goes to `ys` exactly when `subseq` does and `setify`
    takes `xs` to `s` and `ys` to `t` with `t ⊆ s` and every element of `s` `Q`-above some element of `t`.
    `thinL Q X` is `(St ≫ (Rd ∩ Ld)) ≫ St° ∩ U`, `St = setify (ran U).val`, `Rd = ∋ / ∋` (`⊇`), `Ld = ∈ \ Q°∈`, the
    pieces bound by their equations. Hypotheses: `rep_mem`'s at `St.val`; `rep_comp`'s at `QS`, `H`, `G`;
    `rep_rightDiv`'s at `Rd` and `rep_leftDiv`'s at `Ld` (`divOK`); `rep_inter`'s at `Rd ∩ Ld` and at `G ∩ U`. -/
theorem rep_thinL_sets {B : Obj} {n : USize} (Q : Rel B B) (X : Vals (.arr B) n)
    (U : Rel (.arr B) (.arr B)) (hU : U = subseq X) (Wy : Rel (.arr B) (.arr B)) (hWy : Wy = ran U)
    (St : Rel (.arr B) (.arr B)) (hSt : St = setify (Rel.val Wy))
    (mS : Rel (.arr B) B) (hmS : mS = mem (Rel.val St)) (QS : Rel B (.arr B)) (hQS : QS = Q° ≫ mS°)
    (Rd : Rel (.arr B) (.arr B)) (hRd : Rd = rightDiv mS mS (Rel.val St) (Rel.val St))
    (Ld : Rel (.arr B) (.arr B)) (hLd : Ld = leftDiv (mS°) QS (Rel.val St) (Rel.val St))
    (Tt : Rel (.arr B) (.arr B)) (hTt : Tt = Rd ∩ Ld) (H : Rel (.arr B) (.arr B)) (hH : H = St ≫ Tt)
    (G : Rel (.arr B) (.arr B)) (hG : G = H ≫ St°)
    (hSv : Vals.PickFits (.arr B) (Rel.val St) (List.range (Rel.n St).toNat))
    (hSk : Vals.PickFits (.arr B) (Rel.val St) ((List.range (Rel.n St).toNat).flatMap fun r =>
      if h : r < (Rel.n St).toNat then List.replicate ((Rel.val St).row ⟨r, h⟩).length r else []))
    (hcQ : cmpOK(B, Q°, mS°)) (hcH : cmpOK(.arr B, St, Tt)) (hcG : cmpOK(.arr B, H, St°))
    (hdR : divOK(B, .arr B, .arr B, mS°, mS°, Rel.n St, Rel.val St, Rel.n St, Rel.val St))
    (hdL : divOK(B, .arr B, .arr B, mS°, QS, Rel.n St, Rel.val St, Rel.n St, Rel.val St))
    (hiT : interOK(.arr B, .arr B, Rd, Ld)) (hiG : interOK(.arr B, .arr B, G, U)) :
    ∀ xs ys, rep (thinL Q X) xs ys ↔ rep U xs ys ∧ ∃ s t, rep St xs s ∧ rep St ys t ∧
      (∀ c ∈ t, c ∈ s) ∧ ∀ a ∈ s, ∃ y ∈ t, rep Q y a := by
  have eM : ∀ t c, rep mS t c ↔ (∃ i, (Rel.val St).row i = t) ∧ c ∈ t := fun t c => by
    rw [hmS]; exact rep_mem _ hSv hSk t c
  have eX : ∀ a s, rep (mS°) a s ↔ (∃ i, (Rel.val St).row i = s) ∧ a ∈ s := fun a s => by
    rw [rep_conv]; exact eM s a
  obtain ⟨hf1, h1'⟩ := hcQ
  obtain ⟨c1, c2, c3, c4⟩ := h1' _ rfl
  obtain ⟨hf2, h2'⟩ := hcH
  obtain ⟨d1, d2, d3, d4⟩ := h2' _ rfl
  obtain ⟨hf3, h3'⟩ := hcG
  obtain ⟨g1, g2, g3, g4⟩ := h3' _ rfl
  have eQS : ∀ a t, rep QS a t ↔ ∃ y, rep Q y a ∧ (∃ j, (Rel.val St).row j = t) ∧ y ∈ t := fun a t => by
    rw [hQS, rep_comp _ _ (codes_faithful_wf _ _ hf1).1 c1 c2 c3 c4, Freyd.Alg.RelSet.comp_apply]
    exact exists_congr fun y => and_congr (by rw [rep_conv]; exact Iff.rfl) (eX y t)
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, lk⟩ := hdL
  obtain ⟨l11, l12, l13, ly⟩ := lk _ rfl
  obtain ⟨l15, l16, lc⟩ := ly _ rfl
  obtain ⟨l17, l18, l19, l20, l21, lI⟩ := lc _ rfl _ rfl
  obtain ⟨l22, l23, lP⟩ := lI _ rfl
  obtain ⟨l24, l25, l26, l27, l28, l29, l30⟩ := lP _ rfl _ rfl
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, rk⟩ := hdR
  obtain ⟨r11, r12, r13, ry⟩ := rk _ rfl
  obtain ⟨r15, r16, rc⟩ := ry _ rfl
  obtain ⟨r17, r18, r19, r20, r21, rI⟩ := rc _ rfl _ rfl
  obtain ⟨r22, r23, rP⟩ := rI _ rfl
  obtain ⟨r24, r25, r26, r27, r28, r29, r30⟩ := rP _ rfl _ rfl
  obtain ⟨hic, hiI⟩ := hiT _ rfl
  obtain ⟨hik, hiv⟩ := hiI
  -- `Rd ∩ Ld` on two arrays of `St.val`: the second a subset of the first, each element of the first above one of it
  have eT : ∀ s t, (∃ i, (Rel.val St).row i = s) → (∃ j, (Rel.val St).row j = t) →
      (rep Tt s t ↔ (∀ c ∈ t, c ∈ s) ∧ ∀ a ∈ s, ∃ y ∈ t, rep Q y a) := by
    intro s t hs ht
    rw [hTt, rep_inter Rd Ld hic hik hiv]
    show rep Rd s t ∧ rep Ld s t ↔ _
    rw [hRd, rep_rightDiv mS mS (Rel.val St) (Rel.val St) r1 r2 r3 r4 r5 r6 r7 r8 _ rfl r9 r10 r11 r12 r13
        _ rfl _ rfl r15 _ rfl r16 _ rfl r22 r23 r17 r18 r19 r20 r21 _ _ rfl rfl r24 r25 r26 r27 r28 r29 r30 s t,
      hLd, rep_leftDiv (mS°) QS (Rel.val St) (Rel.val St) l1 l2 l3 l4 l5 l6 l7 l8 _ rfl l9 l10 l11 l12 l13
        _ rfl _ rfl l15 _ rfl l16 _ rfl l22 l23 l17 l18 l19 l20 l21 _ _ rfl rfl l24 l25 l26 l27 l28 l29 l30 s t]
    simp only [eM, eX, eQS]
    constructor
    · rintro ⟨⟨hr, -⟩, ⟨hl, -⟩⟩
      refine ⟨fun c hc => (hr c ⟨ht, hc⟩).2, fun a ha => ?_⟩
      obtain ⟨y, hq, -, hy⟩ := hl a ⟨hs, ha⟩
      exact ⟨y, hy, hq⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨fun c ⟨_, hc⟩ => ⟨hs, h1 c hc⟩, Or.inr ⟨hs, ht⟩⟩, ⟨fun a ⟨_, ha⟩ => ?_, Or.inr ⟨hs, ht⟩⟩⟩
      obtain ⟨y, hy, hq⟩ := h2 a ha
      exact ⟨y, hq, ht, hy⟩
  have eH : ∀ xs t, rep H xs t ↔ ∃ s, rep St xs s ∧ rep Tt s t := fun xs t => by
    rw [hH, rep_comp _ _ (codes_faithful_wf _ _ hf2).1 d1 d2 d3 d4, Freyd.Alg.RelSet.comp_apply]
  have eG : ∀ xs ys, rep G xs ys ↔ ∃ t, rep H xs t ∧ rep St ys t := fun xs ys => by
    rw [hG, rep_comp _ _ (codes_faithful_wf _ _ hf3).1 g1 g2 g3 g4, Freyd.Alg.RelSet.comp_apply]
    exact exists_congr fun t => and_congr Iff.rfl (by rw [rep_conv]; exact Iff.rfl)
  obtain ⟨hjc, hjI⟩ := hiG _ rfl
  obtain ⟨hjk, hjv⟩ := hjI
  have e : thinL Q X = G ∩ U := by subst hG hH hTt hLd hRd hQS hmS hSt hWy hU; rfl
  intro xs ys
  rw [e, rep_inter G U hjc hjk hjv]
  show rep G xs ys ∧ rep U xs ys ↔ _
  rw [and_comm, eG]
  refine and_congr_right fun _ => ⟨fun ⟨t, hh, ht⟩ => ?_, fun ⟨s, t, hs, ht, hst⟩ => ?_⟩
  · obtain ⟨s, hs, hT⟩ := (eH _ _).1 hh
    obtain ⟨i, -, hi⟩ := id hs
    obtain ⟨j, -, hj⟩ := id ht
    exact ⟨s, t, hs, ht, (eT s t ⟨i, hi⟩ ⟨j, hj⟩).1 hT⟩
  · obtain ⟨i, -, hi⟩ := id hs
    obtain ⟨j, -, hj⟩ := id ht
    exact ⟨t, (eH _ _).2 ⟨s, hs, (eT s t ⟨i, hi⟩ ⟨j, hj⟩).2 hst⟩, ht⟩

-- `rep_thinL_sets`'s hypotheses at its pieces, as one bundle: stated here, where `Pow`'s `/` is not open
set_option hygiene false in
local notation "thinOK" =>
  (Vals.PickFits (.arr B) (Rel.val St) (List.range (Rel.n St).toNat) ∧
    Vals.PickFits (.arr B) (Rel.val St) ((List.range (Rel.n St).toNat).flatMap fun r =>
      if h : r < (Rel.n St).toNat then List.replicate ((Rel.val St).row ⟨r, h⟩).length r else []) ∧
    cmpOK(B, Q°, mS°) ∧ cmpOK(.arr B, St, Tt) ∧ cmpOK(.arr B, H, St°) ∧
    divOK(B, .arr B, .arr B, mS°, mS°, Rel.n St, Rel.val St, Rel.n St, Rel.val St) ∧
    divOK(B, .arr B, .arr B, mS°, QS, Rel.n St, Rel.val St, Rel.n St, Rel.val St) ∧
    interOK(.arr B, .arr B, Rd, Ld) ∧ interOK(.arr B, .arr B, G, U))

open QLean.Dep

-- `rep_subseq`'s hypotheses at `X`, as one bundle
set_option hygiene false in
local notation "subOK" =>
  (T = num (idU X) 0 ∧ n.toNat < 2 ^ 63 ∧ Vals.PickFits (.arr B) X (List.range n.toNat) ∧
    (Rel.val T).1.toNat < 2 ^ 63 ∧
    (∀ k, k ≤ (Rel.val T).1.toNat → ∀ a : ByteArray, a = whereBits (Rel.n T)
        (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf (Rel.val T)).2 (one k.toUInt64) (Rel.n T)) →
      ∀ pos : ByteArray, pos = Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul
        (gather 8 (add (Rel.n T) (slicesOf (Rel.val T)).1 (slicesOf (Rel.val T)).2) a)
        (one (k + 1).toUInt64) (len a).toUSize →
      Vals.PickFits .long (Rel.key T) ((List.range (len a)).map fun q => (Column.bitsAt a (q * 8) 8).toNat) ∧
      Vals.PickFits B (Rel.val T).2.2.2 ((List.range (len a)).map fun q => (Column.bitsAt pos (q * 8) 8).toNat)) ∧
    pend₀ = top (A := .long) (Rel.key T) (nilVal B) ∧
    (Rel.n T).toNat * (1 : USize).toNat < USize.size ∧ (Rel.n T).toNat * (1 : USize).toNat < 2 ^ 63 ∧
    Vals.PickFits .long (Rel.key T)
      ((List.range ((Rel.n T).toNat * (1 : USize).toNat)).map (· / (1 : USize).toNat)) ∧
    Vals.PickFits (.arr B) (nilVal B)
      ((List.range ((Rel.n T).toNat * (1 : USize).toNat)).map (· % (1 : USize).toNat)) ∧
    step = (fun el pend => cons (pair el pend) ∪ pend) ∧ (∀ k, elK k = elR(T, k)) ∧ (∀ st, f st = rnd(st)) ∧
    (∀ i (el : Rel .long B) (pend P S : Rel .long (.arr B)), el = elK i →
      pend = (f^[i] (pend₀, Alg.zero, 0)).1 → P = (f^[i] (pend₀, Alg.zero, 0)).2.1 → S = step el pend →
      roundAt(.arr B)) ∧
    (∀ i, i ≤ (Rel.val T).1.toNat → ∀ (el : Rel .long B) (pend : Rel .long (.arr B)), el = elK i →
      pend = (f^[i] (pend₀, Alg.zero, 0)).1 →
      ∀ kc : Vector Code 2, kc = Obj.codes .long kp2(el, pend) →
      (Rel.n el).toNat + (Rel.n pend).toNat < USize.size ∧ (Rel.n pend).toNat < 2 ^ 63 ∧
      (Rel.n el).toNat * (Rel.n pend).toNat < min (2 ^ 63) USize.size ∧
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
      ∃ hU : P.n.toNat + Q.n.toNat < USize.size,
        Vals.RazeFits (.arr B) P.val Q.val ∧
        Obj.CodesFit (.arr B)
          (#v[⟨(PQ(.long, (.arr B))).n, (PQ(.long, (.arr B))).val⟩] : Vector (Part (.arr B)) 1) ∧
        Vals.PickFits .long (PQ(.long, (.arr B))).key (List.range (PQ(.long, (.arr B))).n.toNat) ∧
        Vals.PickFits (.arr B) (PQ(.long, (.arr B))).val (List.range (PQ(.long, (.arr B))).n.toNat)) ∧
    F = foldRows T pend₀ step ∧ jc = Obj.codes .long ck2(T°, F) ∧ codesOK(jc, ck2(T°, F)) ∧
    (Rel.n F).toNat < 2 ^ 63 ∧ (Rel.n (T°)).toNat * (Rel.n F).toNat < min (2 ^ 63) USize.size ∧
    Vals.PickFits (.arr B) (Rel.key (T°)) ((mpairs(jc, T°, F)).map Prod.fst) ∧
    Vals.PickFits (.arr B) (Rel.val F) ((mpairs(jc, T°, F)).map Prod.snd))

/-- **`thinL(Q)`, `subseq` read back**: an array `xs` of `X` goes to `ys` exactly when `ys` is a sublist of `xs`
    and the `setify` images `s` of `xs` and `t` of `ys` satisfy the thin condition. `rep_thinL_sets` with
    `rep_subseq`. The elementwise form is `rep_thinL`. -/
theorem rep_thinL_sublist {B : Obj} {n : USize} (Q : Rel B B) (X : Vals (.arr B) n)
    -- `rep_subseq` at `X`
    (T : Rel .long (.arr B)) (pend₀ : Rel .long (.arr B))
    (step : Rel .long B → Rel .long (.arr B) → Rel .long (.arr B)) (elK : Nat → Rel .long B)
    (f : Rel .long (.arr B) × Rel .long (.arr B) × Nat → Rel .long (.arr B) × Rel .long (.arr B) × Nat)
    (F : Rel .long (.arr B)) (jc : Vector Code 2) (hsub : subOK)
    (U : Rel (.arr B) (.arr B)) (hU : U = subseq X) (Wy : Rel (.arr B) (.arr B)) (hWy : Wy = ran U)
    (St : Rel (.arr B) (.arr B)) (hSt : St = setify (Rel.val Wy))
    (mS : Rel (.arr B) B) (hmS : mS = mem (Rel.val St)) (QS : Rel B (.arr B)) (hQS : QS = Q° ≫ mS°)
    (Rd : Rel (.arr B) (.arr B)) (hRd : Rd = rightDiv mS mS (Rel.val St) (Rel.val St))
    (Ld : Rel (.arr B) (.arr B)) (hLd : Ld = leftDiv (mS°) QS (Rel.val St) (Rel.val St))
    (Tt : Rel (.arr B) (.arr B)) (hTt : Tt = Rd ∩ Ld) (H : Rel (.arr B) (.arr B)) (hH : H = St ≫ Tt)
    (G : Rel (.arr B) (.arr B)) (hG : G = H ≫ St°) (hth : thinOK) :
    ∀ xs ys, rep (thinL Q X) xs ys ↔ (∃ i, X.row i = xs) ∧ ys.Sublist xs ∧
      ∃ s t, rep St xs s ∧ rep St ys t ∧ (∀ c ∈ t, c ∈ s) ∧ ∀ a ∈ s, ∃ y ∈ t, rep Q y a := by
  obtain ⟨hT, hn, hv, hp, hel, hpend, hN, h63, hA, hB, hstep, hE, hf, hR, hC, hF, hjc, hjO, hjn, hjM, hjA,
    hjC⟩ := hsub
  obtain ⟨hSv, hSk, hcQ, hcH, hcG, hdR, hdL, hiT, hiG⟩ := hth
  intro xs ys
  rw [rep_thinL_sets Q X U hU Wy hWy St hSt mS hmS QS hQS Rd hRd Ld hLd Tt hTt H hH G hG hSv hSk hcQ hcH hcG hdR hdL
    hiT hiG xs ys, hU, rep_subseq X T hT hn hv hp hel pend₀ hpend hN h63 hA hB step hstep elK hE f hf hR hC F hF jc
    hjc hjO hjn hjM hjA hjC, and_assoc]

section
open Pow UnionN

-- `rep_setify_list`'s hypotheses at `Rel.val Wy`, `Ms` its `∋`, each bound value quantified with its equation
set_option hygiene false in
local notation "setOK" =>
  (Vals.PickFits (.arr B) (Rel.val Wy) (List.range (Rel.n Wy).toNat) ∧
    Vals.PickFits (.arr B) (Rel.val Wy) ((List.range (Rel.n Wy).toNat).flatMap fun r =>
      if h : r < (Rel.n Wy).toNat then List.replicate ((Rel.val Wy).row ⟨r, h⟩).length r else []) ∧
    ∀ kc vc : Code, kc = kcR(Ms) → vc = vcR(Ms) →
    cOK(kc, Rel.n Ms, Rel.key Ms) ∧ cOK(vc, Rel.n Ms, Rel.val Ms) ∧
    Vals.PickFits (.arr B) (Rel.key Ms) (List.range (Rel.n Ms).toNat) ∧
    Vals.PickFits B (Rel.val Ms) (List.range (Rel.n Ms).toNat) ∧
    ∀ kt : Code, kt = kcT(Ms) →
    (∀ {i j : Nat} (hi : i < (Rel.nub Ms).n.toNat) (hj : j < (Rel.nub Ms).n.toNat),
      Column.idAt kt.b kt.w i = Column.idAt kt.b kt.w j ↔
        Vals.row (Rel.nub Ms).key ⟨i, hi⟩ = Vals.row (Rel.nub Ms).key ⟨j, hj⟩) ∧
    laneOK(kt.w) ∧
    kt.n = (Rel.nub Ms).n ∧ kt.b.size = (kt.n.toNat * kt.w + 7) / 8 ∧
    B.CodesFit (#v[⟨(Rel.nub Ms).n, (Rel.nub Ms).val⟩] : Vector (Part B) 1) ∧
    (Rel.nub Ms).n.toNat < 2 ^ 63 ∧
    ∀ p lo : ByteArray, p = pT(Ms) → lo = loT(Ms) →
    Vals.PickFits (.arr B) (Rel.nub Ms).key (ids p) ∧ Vals.PickFits B (Rel.nub Ms).val (ids p) ∧
    Vals.PickFits (.arr B) (Vals.pickPart (.arr B) (Rel.nub Ms).key p).2 (ids lo) ∧
    ∀ pc : Vector Code 2, pc = pairs #v[idU (Rel.val Wy), dom Ms] →
    codesOK(pc, (#v[⟨Rel.n (idU (Rel.val Wy)), (Rel.key (idU (Rel.val Wy)), Rel.val (idU (Rel.val Wy)))⟩,
      ⟨Rel.n (dom Ms), (Rel.key (dom Ms), Rel.val (dom Ms))⟩] : Vector (Part (.prod (.arr B) (.arr B))) 2)) ∧
    ∀ D : Rel (.arr B) (.arr B), D = lD(Ms, Rel.val Wy) →
    (Rel.n D).toNat * USize.toNat 1 < USize.size ∧ (Rel.n D).toNat * USize.toNat 1 < 2 ^ 63 ∧
    Vals.PickFits (.arr B) (Rel.key D) ((List.range ((Rel.n D).toNat * USize.toNat 1)).map (· / USize.toNat 1)) ∧
    Vals.PickFits (.arr B) (nilVal B) ((List.range ((Rel.n D).toNat * USize.toNat 1)).map (· % USize.toNat 1)) ∧
    ∀ T N : Rel (.arr B) (.arr B), T = lT(Ms) → N = top (Rel.key D) (nilVal B) →
    ∃ hN : (Rel.n T).toNat + (Rel.n N).toNat < USize.size,
    Vals.RazeFits (.arr B) (Rel.key T) (Rel.key N) ∧ Vals.RazeFits (.arr B) (Rel.val T) (Rel.val N) ∧
    ∀ L : Rel (.arr B) (.arr B), L = Uc(T, N, hN) → ∀ ku vu : Code, ku = kcR(L) → vu = vcR(L) →
    cOK(ku, Rel.n L, Rel.key L) ∧ cOK(vu, Rel.n L, Rel.val L) ∧
    Vals.PickFits (.arr B) (Rel.key L) (List.range (Rel.n L).toNat) ∧
    Vals.PickFits (.arr B) (Rel.val L) (List.range (Rel.n L).toNat))

/-- **`thinL(Q)`, elementwise**: an array `xs` of `X` goes to `ys` exactly when `ys` is a sublist of `xs` and each
    element of `xs` is `Q`-above some element of `ys`. `rep_thinL_sublist`, with the `setify` images replaced by
    `xs`, `ys` through `rep_setify_list` (they hold the same elements), and the images found through `rep_ran`
    at `U` (every sublist of `xs` is in the range of `subseq X`). -/
theorem rep_thinL {B : Obj} {n : USize} (Q : Rel B B) (X : Vals (.arr B) n)
    -- `rep_subseq` at `X`
    (T : Rel .long (.arr B)) (pend₀ : Rel .long (.arr B))
    (step : Rel .long B → Rel .long (.arr B) → Rel .long (.arr B)) (elK : Nat → Rel .long B)
    (f : Rel .long (.arr B) × Rel .long (.arr B) × Nat → Rel .long (.arr B) × Rel .long (.arr B) × Nat)
    (F : Rel .long (.arr B)) (jc : Vector Code 2) (hsub : subOK)
    (U : Rel (.arr B) (.arr B)) (hU : U = subseq X) (Wy : Rel (.arr B) (.arr B)) (hWy : Wy = ran U)
    (St : Rel (.arr B) (.arr B)) (hSt : St = setify (Rel.val Wy))
    (mS : Rel (.arr B) B) (hmS : mS = mem (Rel.val St)) (QS : Rel B (.arr B)) (hQS : QS = Q° ≫ mS°)
    (Rd : Rel (.arr B) (.arr B)) (hRd : Rd = rightDiv mS mS (Rel.val St) (Rel.val St))
    (Ld : Rel (.arr B) (.arr B)) (hLd : Ld = leftDiv (mS°) QS (Rel.val St) (Rel.val St))
    (Tt : Rel (.arr B) (.arr B)) (hTt : Tt = Rd ∩ Ld) (H : Rel (.arr B) (.arr B)) (hH : H = St ≫ Tt)
    (G : Rel (.arr B) (.arr B)) (hG : G = H ≫ St°) (hth : thinOK)
    -- `rep_ran` at `U`
    (hWf : oneFit(.arr B, Rel.n U, Rel.val U))
    -- `rep_setify_list` at `Rel.val Wy`
    (Ms : Rel (.arr B) B) (hMs : Ms = mem (Rel.val Wy)) (hset : setOK) :
    ∀ xs ys, rep (thinL Q X) xs ys ↔ (∃ i, X.row i = xs) ∧ ys.Sublist xs ∧ ∀ a ∈ xs, ∃ y ∈ ys, rep Q y a := by
  have eL := rep_thinL_sublist Q X T pend₀ step elK f F jc hsub U hU Wy hWy St hSt mS hmS QS hQS Rd hRd Ld hLd Tt
    hTt H hH G hG hth
  obtain ⟨hT, hn, hv, hp, hel, hpend, hN, h63, hA, hB, hstep, hE, hf, hR, hC, hF, hjc, hjO, hjn, hjM, hjA,
    hjC⟩ := hsub
  have eU : ∀ xs ys, rep U xs ys ↔ (∃ i, X.row i = xs) ∧ ys.Sublist xs := by
    rw [hU]; exact rep_subseq X T hT hn hv hp hel pend₀ hpend hN h63 hA hB step hstep elK hE f hf hR hC F hF jc
      hjc hjO hjn hjM hjA hjC
  have eW : ∀ a b, rep Wy a b ↔ a = b ∧ ∃ x, rep U x a := fun a b => by
    rw [hWy, rep_ran_corefl U (one_ok _ hWf.1) hWf.2]; exact Iff.rfl
  subst hMs
  obtain ⟨hmv, hmk, k1⟩ := hset
  obtain ⟨hK, hV, hk, hv', k2⟩ := k1 _ _ rfl rfl
  obtain ⟨hF', hw, hn', hs, hW, h63', k3⟩ := k2 _ rfl
  obtain ⟨hpk, hpv, hlo, k4⟩ := k3 _ _ rfl rfl
  obtain ⟨hc, k6⟩ := k4 _ rfl
  obtain ⟨htN, ht63, htA, htB, k7⟩ := k6 _ rfl
  obtain ⟨hN', hFk, hFv, k8⟩ := k7 _ _ rfl rfl
  obtain ⟨huK, huV, huk, huv⟩ := k8 _ rfl _ _ rfl rfl
  have hS := rep_setify_list (Rel.val Wy) hmv hmk _ _ rfl rfl hK hV hk hv' _ rfl hF' hw hn' hs hW h63' _ _ rfl rfl
    hpk hpv _ rfl hc _ rfl htN ht63 htA htB _ _ rfl rfl hN' hFk hFv _ rfl _ _ rfl rfl
    huK huV huk huv
  rw [← hSt] at hS
  intro xs ys
  rw [eL xs ys]
  refine and_congr_right fun hx => and_congr_right fun hsl => ⟨?_, fun hq => ?_⟩
  · rintro ⟨s, t, hs, ht, -, hq⟩ a ha
    obtain ⟨y, hy, hQ⟩ := hq a (((hS.1 xs s hs).2.2 a).2 ha)
    exact ⟨y, ((hS.1 ys t ht).2.2 y).1 hy, hQ⟩
  · obtain ⟨i, -, hi⟩ := id ((eW ys ys).2 ⟨rfl, xs, (eU xs ys).2 ⟨hx, hsl⟩⟩)
    obtain ⟨j, -, hj⟩ := id ((eW xs xs).2 ⟨rfl, xs, (eU xs xs).2 ⟨hx, List.Sublist.refl xs⟩⟩)
    obtain ⟨s, hs⟩ := (hS.2 xs).2 ⟨j, hj⟩
    obtain ⟨t, ht⟩ := (hS.2 ys).2 ⟨i, hi⟩
    refine ⟨s, t, hs, ht, fun c hc => ((hS.1 xs s hs).2.2 c).2 (hsl.subset (((hS.1 ys t ht).2.2 c).1 hc)),
      fun a ha => ?_⟩
    obtain ⟨y, hy, hQ⟩ := hq a (((hS.1 xs s hs).2.2 a).1 ha)
    exact ⟨y, ((hS.1 ys t ht).2.2 y).2 hy, hQ⟩

end

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.Rep.suffix_pairwise
#print axioms LeetQ.Rel.Rep.rep_orderedOn
#print axioms LeetQ.Rel.Rep.rep_ordered
#print axioms LeetQ.Rel.Rep.rep_sortSet
#print axioms LeetQ.Rel.Rep.rep_thinL_sets
#print axioms LeetQ.Rel.Rep.rep_thinL_sublist
#print axioms LeetQ.Rel.Rep.rep_thinL
