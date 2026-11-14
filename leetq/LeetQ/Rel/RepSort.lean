/-
  Order on arrays read back: `orderedOn`/`ordered` (`suffix`, `uncons`, `mem`, `pair`, `antiJoin`, `dom`),
  `sortSet` (`setify°` then `ordered`), `thinL` (`setify`, the divisions, `subseq`), each from its primitives'
  read-backs.
-/
import LeetQ.Rel.RepPerm
import LeetQ.Rel.RepSubseq

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

open FoldN Prim

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

-- `rep_suffix`'s round hypotheses at the union so far `S` and last arrays `F` (`RepPerm`'s local `sufOK`)
set_option hygiene false in
local notation "sufOK" =>
  (∀ Dr : Rel (.arr B) (.arr B), Dr = ran F →
    oneFit(.arr B, Rel.n F, Rel.val F) ∧ uncOK(B, Dr) ∧ cmpOK(.arr B, F, tail (Rel.val Dr)) ∧
    ∀ P : Rel (.arr B) (.arr B), P = S → ∀ Q : Rel (.arr B) (.arr B), Q = F ≫ tail (Rel.val Dr) →
    P.n.toNat + Q.n.toNat < USize.size ∧
    ∃ (hNk : ((#[⟨P.n, P.key⟩, ⟨Q.n, Q.key⟩] : Array (Part (.arr B))).toList.map
        fun c : Part (.arr B) => c.1.toNat).sum < USize.size)
      (hNv : ((#[⟨P.n, P.val⟩, ⟨Q.n, Q.val⟩] : Array (Part (.arr B))).toList.map
        fun c : Part (.arr B) => c.1.toNat).sum < USize.size),
      Vals.RazeFits (.arr B) P.key Q.key ∧ Vals.RazeFits (.arr B) P.val Q.val ∧
      Obj.CodesFit (.arr B) (#v[⟨(PQ(.arr B, .arr B)).n, (PQ(.arr B, .arr B)).key⟩] : Vector (Part (.arr B)) 1) ∧
      Obj.CodesFit (.arr B) (#v[⟨(PQ(.arr B, .arr B)).n, (PQ(.arr B, .arr B)).val⟩] : Vector (Part (.arr B)) 1) ∧
      Vals.PickFits (.arr B) (PQ(.arr B, .arr B)).key (ids nubI(.arr B, .arr B, PQ(.arr B, .arr B))) ∧
      Vals.PickFits (.arr B) (PQ(.arr B, .arr B)).val (ids nubI(.arr B, .arr B, PQ(.arr B, .arr B))))

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
  obtain ⟨c1, c2, c3, c4, c5⟩ := hc' _ rfl
  obtain ⟨m1, m2, m3, m4, m5⟩ := hm' _ rfl
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp' _ rfl
  obtain ⟨b1, b2⟩ := hb' _ rfl _ rfl
  obtain ⟨k1, k2, k3, k4, k5⟩ := hC' _ rfl
  obtain ⟨a1, a2⟩ := hA' _ rfl _ rfl
  have eS : ∀ xs ys, rep Su xs ys ↔ (∃ j, X.row j = xs) ∧ ys <:+ xs := by
    rw [hSu]; exact rep_suffix X g hg hR
  have eW : ∀ a a', rep Wu a a' ↔ a = a' ∧ ∃ k, rep Su k a := fun a a' => by
    rw [hWu, rep_ran Su (one_ok _ hSf) (hSp _ rfl)]; exact Iff.rfl
  have eU := rep_uncons (Rel.val Wu) h63 _ rfl _ rfl _ rfl u1 u2 u3
  -- `T`: an array to the head and tail of each of its non-empty suffixes
  have eT : ∀ xs (p : (Obj.prod B (.arr B)).El), rep T xs p ↔ rep Su xs (p.1 :: p.2) := fun xs p => by
    rw [hT, rep_comp _ _ (codes_faithful_wf _ _ hcf).1 c1 c2 c3 c4 c5, Freyd.Alg.RelSet.comp_apply]
    constructor
    · rintro ⟨a, ha, hu⟩
      obtain ⟨-, rfl⟩ := (eU a p.1 p.2).1 hu
      exact ha
    · intro hs
      obtain ⟨j, -, hj⟩ := (eW _ _).2 ⟨rfl, xs, hs⟩
      exact ⟨_, hs, (eU _ p.1 p.2).2 ⟨⟨j, hj⟩, rfl⟩⟩
  have eD : ∀ p p', rep D p p' ↔ p = p' ∧ ∃ xs, rep T xs p := fun p p' => by
    rw [hD, rep_ran T (one_ok _ hTf) (hTp _ rfl)]; exact Iff.rfl
  have eO : ∀ p a, rep O p a ↔ (∃ xs, rep T xs p) ∧ a = p.2 := fun p a => by
    rw [hO, rep_apply, outr_holds]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨rfl, hx⟩ := (eD _ _).1 hy
      exact ⟨hx, rfl⟩
    · rintro ⟨hx, rfl⟩
      exact ⟨p.1, (eD _ _).2 ⟨rfl, hx⟩⟩
  have eV : ∀ a a', rep V a a' ↔ a = a' ∧ ∃ p, rep O p a := fun a a' => by
    rw [hV, rep_ran O (one_ok _ hOf) (hOp _ rfl)]; exact Iff.rfl
  have eMem := rep_mem (Rel.val V) hVv hVk
  have eM : ∀ p z, rep M p z ↔ (∃ xs, rep T xs p) ∧ z ∈ p.2 := fun p z => by
    rw [hM, rep_comp _ _ (codes_faithful_wf _ _ hmf).1 m1 m2 m3 m4 m5, Freyd.Alg.RelSet.comp_apply]
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
  have eP := rep_pair _ _ (codes_faithful_wf _ _ hpf).1 p1 p2 p3 p4 p5 p6
  have eyz : ∀ p y z, rep yz p (y, z) ↔ (∃ xs, rep T xs p) ∧ y = p.1 ∧ z ∈ p.2 := fun p y z => by
    rw [hyz]
    refine (Iff.of_eq (congrFun (congrFun eP p) (y, z))).trans ((and_congr (eL p y) (eM p z)).trans ?_)
    exact ⟨fun ⟨⟨h1, h2⟩, _, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h1, h3⟩⟩
  have eE : ∀ w w', rep E w w' ↔ w = w' ∧ ∃ p, rep yz p w := fun w w' => by
    rw [hE, rep_ran yz (one_ok _ hyf) (hyp _ rfl)]; exact Iff.rfl
  have ebad : ∀ p v, rep bad p v ↔ rep yz p v ∧ ¬ ∃ w, rep (q E) w v := fun p v => by
    rw [hbad, rep_antiJoin yz (q E) (codes_faithful_wf _ _ hbf).1 b1 b2, Freyd.Alg.RelSet.comp_apply]
    exact ⟨fun ⟨_, h1, rfl, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨v, h1, rfl, h2⟩⟩
  have edb : ∀ p p', rep (dom bad) p p' ↔ p = p' ∧ ∃ v, rep bad p v := fun p p' => by
    rw [rep_dom bad (one_ok _ hdf) (hdp _ rfl)]; exact Iff.rfl
  have eC : ∀ xs p, rep C xs p ↔ rep T xs p ∧ ∃ v, rep bad p v := fun xs p => by
    rw [hC, rep_comp _ _ (codes_faithful_wf _ _ hCf).1 k1 k2 k3 k4 k5, Freyd.Alg.RelSet.comp_apply]
    constructor
    · rintro ⟨p', ht, hd⟩
      obtain ⟨rfl, hv⟩ := (edb _ _).1 hd
      exact ⟨ht, hv⟩
    · rintro ⟨ht, hv⟩
      exact ⟨p, ht, (edb _ _).2 ⟨rfl, hv⟩⟩
  have edC : ∀ xs xs', rep (dom C) xs xs' ↔ xs = xs' ∧ ∃ p, rep C xs p := fun xs xs' => by
    rw [rep_dom C (one_ok _ hDf) (hDp _ rfl)]; exact Iff.rfl
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
  obtain ⟨c1, c2, c3, c4, c5⟩ := h' _ rfl
  have eO := rep_ordered Q Y g hg hR Su hSu Wu hWu T hT D hD O hO V hV M hM yz hyz E hE bad hbad C hC
    (fun q hq' => h q hq' Y rfl) hq
  intro s ys
  rw [show sortSet Q Y = (setify Y)° ≫ ordered Q Y from rfl,
    rep_comp _ _ (codes_faithful_wf _ _ hf).1 c1 c2 c3 c4 c5, Freyd.Alg.RelSet.comp_apply]
  constructor
  · rintro ⟨m, hm, ho⟩
    obtain ⟨hx, rfl, hp⟩ := (eO m ys).1 ho
    rw [rep_conv] at hm
    exact ⟨hm, hx, hp⟩
  · rintro ⟨hs, hx, hp⟩
    exact ⟨ys, by rw [rep_conv]; exact hs, (eO ys ys).2 ⟨hx, rfl, hp⟩⟩

section ThinL

open DivN

-- `rep_inter`'s hypotheses at `L ∩ R` (`K` the keys' object, `V` the values'), its codes `pc` and hits `I` bound
set_option hygiene false in
local notation "interOK(" K ", " V ", " L ", " R ")" =>
  (∀ pc : Vector Code 2, pc = pairs #v[L, R] →
    codesOK(pc, (#v[⟨Rel.n L, (Rel.key L, Rel.val L)⟩, ⟨Rel.n R, (Rel.key R, Rel.val R)⟩] :
      Vector (Part (.prod K V)) 2)) ∧
    ∀ I : ByteArray, I = whereBits (Rel.n L) ((pc[0]'Nat.zero_lt_two).member (pc[1]'Nat.one_lt_two)) →
      Vals.PickFits K (Rel.key L) (ids I) ∧ Vals.PickFits V (Rel.val L) (ids I))

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
  obtain ⟨c1, c2, c3, c4, c5⟩ := h1' _ rfl
  obtain ⟨hf2, h2'⟩ := hcH
  obtain ⟨d1, d2, d3, d4, d5⟩ := h2' _ rfl
  obtain ⟨hf3, h3'⟩ := hcG
  obtain ⟨g1, g2, g3, g4, g5⟩ := h3' _ rfl
  have eQS : ∀ a t, rep QS a t ↔ ∃ y, rep Q y a ∧ (∃ j, (Rel.val St).row j = t) ∧ y ∈ t := fun a t => by
    rw [hQS, rep_comp _ _ (codes_faithful_wf _ _ hf1).1 c1 c2 c3 c4 c5, Freyd.Alg.RelSet.comp_apply]
    exact exists_congr fun y => and_congr (by rw [rep_conv]; exact Iff.rfl) (eX y t)
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, lk⟩ := hdL
  obtain ⟨l11, l12, l13, l14, ly⟩ := lk _ rfl
  obtain ⟨l15, l16, lc⟩ := ly _ rfl
  obtain ⟨l17, l18, l19, l20, l21, lI⟩ := lc _ rfl _ rfl
  obtain ⟨l22, l23, lP⟩ := lI _ rfl
  obtain ⟨l24, lN, lV, l25, l26, l27, l28, l29, l30⟩ := lP _ rfl _ rfl
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, rk⟩ := hdR
  obtain ⟨r11, r12, r13, r14, ry⟩ := rk _ rfl
  obtain ⟨r15, r16, rc⟩ := ry _ rfl
  obtain ⟨r17, r18, r19, r20, r21, rI⟩ := rc _ rfl _ rfl
  obtain ⟨r22, r23, rP⟩ := rI _ rfl
  obtain ⟨r24, rN, rV, r25, r26, r27, r28, r29, r30⟩ := rP _ rfl _ rfl
  obtain ⟨hic, hiI⟩ := hiT _ rfl
  obtain ⟨hik, hiv⟩ := hiI _ rfl
  -- `Rd ∩ Ld` on two arrays of `St.val`: the second a subset of the first, each element of the first above one of it
  have eT : ∀ s t, (∃ i, (Rel.val St).row i = s) → (∃ j, (Rel.val St).row j = t) →
      (rep Tt s t ↔ (∀ c ∈ t, c ∈ s) ∧ ∀ a ∈ s, ∃ y ∈ t, rep Q y a) := by
    intro s t hs ht
    rw [hTt, rep_inter Rd Ld hic hik hiv]
    show rep Rd s t ∧ rep Ld s t ↔ _
    rw [hRd, rep_rightDiv mS mS (Rel.val St) (Rel.val St) r1 r2 r3 r4 r5 r6 r7 r8 _ rfl r9 r10 r11 r12 r13 r14
        _ rfl _ rfl r15 _ rfl r16 _ rfl r22 r23 r17 r18 r19 r20 r21 _ _ rfl rfl r24 rN rV r25 r26 r27 r28 r29 r30 s t,
      hLd, rep_leftDiv (mS°) QS (Rel.val St) (Rel.val St) l1 l2 l3 l4 l5 l6 l7 l8 _ rfl l9 l10 l11 l12 l13 l14
        _ rfl _ rfl l15 _ rfl l16 _ rfl l22 l23 l17 l18 l19 l20 l21 _ _ rfl rfl l24 lN lV l25 l26 l27 l28 l29 l30 s t]
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
    rw [hH, rep_comp _ _ (codes_faithful_wf _ _ hf2).1 d1 d2 d3 d4 d5, Freyd.Alg.RelSet.comp_apply]
  have eG : ∀ xs ys, rep G xs ys ↔ ∃ t, rep H xs t ∧ rep St ys t := fun xs ys => by
    rw [hG, rep_comp _ _ (codes_faithful_wf _ _ hf3).1 g1 g2 g3 g4 g5, Freyd.Alg.RelSet.comp_apply]
    exact exists_congr fun t => and_congr Iff.rfl (by rw [rep_conv]; exact Iff.rfl)
  obtain ⟨hjc, hjI⟩ := hiG _ rfl
  obtain ⟨hjk, hjv⟩ := hjI _ rfl
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

end ThinL

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.Rep.suffix_pairwise
#print axioms LeetQ.Rel.Rep.rep_orderedOn
#print axioms LeetQ.Rel.Rep.rep_ordered
#print axioms LeetQ.Rel.Rep.rep_sortSet
#print axioms LeetQ.Rel.Rep.rep_thinL_sets
