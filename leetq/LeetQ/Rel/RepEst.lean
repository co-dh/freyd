/-
  The composites of `Alg` built only from ops already read back: `tail`, `Arr.union`, `pairsIn`, `swapIn`,
  `estOn`/`est`, `thinOn`/`thin`. Each headline chains its primitives' read-backs; the intermediates are bound by
  their defining equations and the primitives' hypotheses are `Prim`'s bundles at them.
-/
import LeetQ.Rel.RepLoop
import LeetQ.Rel.RepE

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

/-! ## `Arr.union` -/

section ArrUnion

open Pow OpsN UnionN

/-- Every element of a cell of `X` is a row of its payload: a cell's window ends inside the payload. -/
theorem row_mem_payload {A : Obj} {n : USize} (X : Vals (.arr A) n) :
    ∀ xs x, (∃ i, Vals.row X i = xs) → x ∈ xs → ∃ i, Vals.row X.2.2.2 i = x := by
  rintro xs x ⟨q, rfl⟩ hx
  rw [arr_row] at hx
  obtain ⟨j, hj, hjx⟩ := List.mem_map.1 hx
  rw [List.mem_range] at hj
  rw [dif_pos (by omega)] at hjx
  exact ⟨_, hjx⟩

end ArrUnion

/-! ## `tail`, `pairsIn`, `swapIn`, `estOn`, `est`, `thinOn`, `thin` -/

section Est

open FoldN OpsN Prim

/-- **`rep (tail X)`: an array of `X` to its tail**: `tail X` is `outr (uncons X)` (`outr_holds`, `rep_uncons`).
    Hypotheses: `rep_uncons`'s. -/
theorem rep_tail {B : Obj} {n : USize} (X : Vals (.arr B) n)
    (i : ByteArray) (hi : i = whereBits n (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf X).2 (one 0) n))
    (l : ByteArray) (hl : l = gather 8 (slicesOf X).1 i)
    (T : Vals (.arr B) (len i).toUSize)
    (hT : T = ⟨X.1, valCol Ew.add Ew.va l (one 1), valCol Ew.add Ew.vv l (gather 8 (slicesOf X).2 i), X.2.2.2⟩)
    (hKf : Vals.PickFits (.arr B) X ((List.range (len i)).map fun q => (Column.bitsAt i (q * 8) 8).toNat)) :
    ∀ (xs bs : List B.El), rep (tail X) xs bs ↔ (∃ j, X.row j = xs) ∧ ∃ b, xs = b :: bs := by
  intro xs bs
  have hu := rep_uncons X i hi l hl T hT hKf xs
  rw [rep_apply, show tail X = outr (uncons X) from rfl, outr_holds]
  exact ⟨fun ⟨b, h⟩ => ((hu b bs).1 h).imp_right fun e => ⟨b, e⟩,
    fun ⟨hj, b, e⟩ => ⟨b, (hu b bs).2 ⟨hj, e⟩⟩⟩

/-- **`rep (pairsIn Q D)`: the pairs of `D` that are pairs of `Q`**: `pairsIn Q D` is `D ≫ idU (Q.key, Q.val)`
    (`rep_comp`, `rep_idU`). Hypotheses: `rep_comp`'s. -/
theorem rep_pairsIn {B : Obj} (Q : Rel B B) (D : Rel (.prod B B) (.prod B B))
    (h : cmpOK(.prod B B, D, idU (t := .prod B B) (m := Rel.n Q) (Rel.key Q, Rel.val Q))) :
    ∀ p p', rep (pairsIn Q D) p p' ↔ rep D p p' ∧ rep Q p'.1 p'.2 := by
  obtain ⟨hf, h'⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := h' _ rfl
  have e := rep_comp _ _ (codes_faithful_wf _ _ hf).1 h1 h2 h3 h4
  intro p p'
  rw [show pairsIn Q D = D ≫ idU (t := .prod B B) (m := Rel.n Q) (Rel.key Q, Rel.val Q) from rfl, e,
    Freyd.Alg.RelSet.comp_apply]
  constructor
  · rintro ⟨w, hw, hu⟩
    obtain ⟨rfl, i, hi⟩ := (idU_holds _ w p').1 hu
    exact ⟨hw, i, congrArg Prod.fst hi, congrArg Prod.snd hi⟩
  · rintro ⟨hw, i, h1, h2⟩
    exact ⟨p', hw, (idU_holds _ p' p').2 ⟨rfl, i, Prod.ext h1 h2⟩⟩

/-- **`rep (swapIn q D)`, the coreflexive on the `p` whose swap passes the test**: `p` is kept when, with `u` a
    second component and `v` a first component of a pair `D` gives `p`, the test `q E` relates `(u, v)` to
    something; `s`, `E`, `M` bound by their equations as `swapIn` builds them. Hypotheses: `rep_pair`'s at `s`,
    `rep_comp`'s at `M`, `rep_dom`'s at `M`. -/
theorem rep_swapIn {B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B))
    (D : Rel (.prod B B) (.prod B B)) (s : Rel (.prod B B) (.prod B B)) (hs : s = pair (outr D) (outl D))
    (E : Rel (.prod B B) (.prod B B)) (hE : E = ran s) (M : Rel (.prod B B) (.prod B B)) (hM : M = s ≫ q E)
    (h : pairOK(.prod B B, outr D, outl D) ∧ cmpOK(.prod B B, s, q E) ∧ oneFit(.prod B B, Rel.n M, Rel.key M)) :
    ∀ p p', rep (swapIn q D) p p' ↔
      p = p' ∧ ∃ u v w, ((∃ y, rep D p (y, u)) ∧ ∃ z, rep D p (v, z)) ∧ rep (q E) (u, v) w := by
  obtain ⟨⟨hpf, hp'⟩, ⟨hcf, hc'⟩, hdf, hdp⟩ := h
  obtain ⟨p1, p2, p3, p4, p5⟩ := hp' _ rfl
  obtain ⟨c1, c2, c3, c4⟩ := hc' _ rfl
  have es : ∀ x u v, rep s x (u, v) ↔ (∃ y, rep D x (y, u)) ∧ ∃ z, rep D x (v, z) := fun x u v => by
    rw [hs, rep_pair _ _ (codes_faithful_wf _ _ hpf).1 p1 p2 p3 p4 p5]
    exact and_congr (outr_holds D x u) (outl_holds D x v)
  have eM : ∀ x w, rep M x w ↔ ∃ m, rep s x m ∧ rep (q E) m w := fun x w => by
    rw [hM, rep_comp _ _ (codes_faithful_wf _ _ hcf).1 c1 c2 c3 c4, Freyd.Alg.RelSet.comp_apply]
  intro p p'
  rw [show swapIn q D = dom M by rw [hM, hE, hs]; rfl, rep_dom_corefl M (one_ok _ hdf) (hdp)]
  show (p = p' ∧ ∃ w, rep M p w) ↔ _
  refine and_congr Iff.rfl ⟨fun ⟨w, hw⟩ => ?_, fun ⟨u, v, w, huv, hq⟩ => ⟨w, (eM p w).2 ⟨(u, v), (es p u v).2 huv, hq⟩⟩⟩
  obtain ⟨⟨u, v⟩, hm, hq⟩ := (eM p w).1 hw
  exact ⟨u, v, w, (es p u v).1 hm, hq⟩

/-- **`rep (estOn q G)`**: `(a, b)` of `G` is kept unless some value `c ≠ b` of `a` has `(b, c)` failing the test
    `q D` at itself, `D` the coreflexive on the pairs of values of one key. The intermediates are bound as
    `estOn` builds them. Hypotheses: `rep_pair`'s at `P`, `W`; `rep_ran`'s at `D`, `V`, `N`; `rep_diff`'s at
    `Y`, `Z` and the result; `rep_comp`'s at `M`. -/
theorem rep_estOn {A B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B)) (G : Rel A B)
    (P : Rel A (.prod B B)) (hP : P = pair G G) (D : Rel (.prod B B) (.prod B B)) (hD : D = ran P)
    (V : Rel B B) (hV : V = ran G) (W : Rel B (.prod B B)) (hW : W = pair V V)
    (N : Rel (.prod B B) (.prod B B)) (hN : N = ran W) (Y : Rel (.prod B B) (.prod B B)) (hY : Y = D \ q D)
    (Z : Rel (.prod B B) (.prod B B)) (hZ : Z = Y \ N) (M : Rel A B) (hM : M = P ≫ outl Z)
    (h : pairOK(A, G, G) ∧ oneFit(.prod B B, Rel.n P, Rel.val P) ∧ oneFit(B, Rel.n G, Rel.val G) ∧
      pairOK(B, V, V) ∧ oneFit(.prod B B, Rel.n W, Rel.val W) ∧ diffOK(.prod B B, .prod B B, D, q D) ∧
      diffOK(.prod B B, .prod B B, Y, N) ∧ cmpOK(.prod B B, P, outl Z) ∧ diffOK(A, B, G, M)) :
    ∀ a b, rep (estOn q G) a b ↔ rep G a b ∧ ¬ ∃ c, rep G a c ∧ c ≠ b ∧ ¬ rep (q D) (b, c) (b, c) := by
  obtain ⟨⟨hPf, hP'⟩, ⟨hDf, hDp⟩, ⟨hVf, hVp⟩, ⟨hWf, hW'⟩, ⟨hNf, hNp⟩, hY', hZ', ⟨hMf, hM'⟩, hE'⟩ := h
  obtain ⟨p1, p2, p3, p4, p5⟩ := hP' _ rfl
  obtain ⟨w1, w2, w3, w4, w5⟩ := hW' _ rfl
  obtain ⟨m1, m2, m3, m4⟩ := hM' _ rfl
  obtain ⟨y1, y2⟩ := hY' _ rfl
  obtain ⟨y3, y4⟩ := y2
  obtain ⟨z1, z2⟩ := hZ' _ rfl
  obtain ⟨z3, z4⟩ := z2
  obtain ⟨e1, e2⟩ := hE' _ rfl
  obtain ⟨e3, e4⟩ := e2
  have eP : ∀ a b c, rep P a (b, c) ↔ rep G a b ∧ rep G a c := fun a b c => by
    rw [hP, rep_pair _ _ (codes_faithful_wf _ _ hPf).1 p1 p2 p3 p4 p5]; exact Iff.rfl
  have eD : ∀ x x', rep D x x' ↔ x = x' ∧ ∃ a, rep P a x := fun x x' => by
    rw [hD, rep_ran_corefl P (one_ok _ hDf) (hDp)]; exact Iff.rfl
  have eV : ∀ b b', rep V b b' ↔ b = b' ∧ ∃ a, rep G a b := fun b b' => by
    rw [hV, rep_ran_corefl G (one_ok _ hVf) (hVp)]; exact Iff.rfl
  have eW : ∀ b u v, rep W b (u, v) ↔ rep V b u ∧ rep V b v := fun b u v => by
    rw [hW, rep_pair _ _ (codes_faithful_wf _ _ hWf).1 w1 w2 w3 w4 w5]; exact Iff.rfl
  have eN : ∀ x x', rep N x x' ↔ x = x' ∧ ∃ b, rep W b x := fun x x' => by
    rw [hN, rep_ran_corefl W (one_ok _ hNf) (hNp)]; exact Iff.rfl
  have eY : ∀ x x', rep Y x x' ↔ rep D x x' ∧ ¬ rep (q D) x x' := fun x x' => by
    rw [hY]; exact rep_diff D (q D) y1 y3 y4 x x'
  have eZ : ∀ x x', rep Z x x' ↔ rep Y x x' ∧ ¬ rep N x x' := fun x x' => by
    rw [hZ]; exact rep_diff Y N z1 z3 z4 x x'
  have eM : ∀ a b, rep M a b ↔ ∃ x, rep P a x ∧ ∃ z, rep Z x (b, z) := fun a b => by
    rw [hM, rep_comp _ _ (codes_faithful_wf _ _ hMf).1 m1 m2 m3 m4, Freyd.Alg.RelSet.comp_apply]
    exact exists_congr fun x => and_congr Iff.rfl (outl_holds Z x b)
  have eE : ∀ a b, rep (estOn q G) a b ↔ rep G a b ∧ ¬ rep M a b := fun a b => by
    rw [show estOn q G = G \ M by rw [hM, hZ, hY, hN, hW, hV, hD, hP]; rfl]
    exact rep_diff G M e1 e3 e4 a b
  intro a b
  rw [eE]
  refine and_congr_right fun hab => not_congr ?_
  rw [eM]
  constructor
  · rintro ⟨x, hx, z, hz⟩
    obtain ⟨hy, hnN⟩ := (eZ x (b, z)).1 hz
    obtain ⟨hd, hnq⟩ := (eY x (b, z)).1 hy
    obtain ⟨rfl, -⟩ := (eD x (b, z)).1 hd
    obtain ⟨-, hz'⟩ := (eP a b z).1 hx
    refine ⟨z, hz', fun e => hnN ?_, hnq⟩
    subst e
    exact (eN _ _).2 ⟨rfl, z, (eW z z z).2 ⟨(eV z z).2 ⟨rfl, a, hz'⟩, (eV z z).2 ⟨rfl, a, hz'⟩⟩⟩
  · rintro ⟨c, hc, hne, hnq⟩
    have hP' : rep P a (b, c) := (eP a b c).2 ⟨hab, hc⟩
    have hd : rep D (b, c) (b, c) := (eD _ _).2 ⟨rfl, a, hP'⟩
    refine ⟨(b, c), hP', c, (eZ _ _).2 ⟨(eY _ _).2 ⟨hd, hnq⟩, fun hn => hne ?_⟩⟩
    obtain ⟨-, b', hw⟩ := (eN _ _).1 hn
    obtain ⟨h1, h2⟩ := (eW b' b c).1 hw
    obtain ⟨e1, -⟩ := (eV _ _).1 h1
    obtain ⟨e2, -⟩ := (eV _ _).1 h2
    exact e2.symm.trans e1

/-- **`rep (est Q G)`: the values `b` of `a` with `b Q c` for every other value `c` of `a`**: `rep_estOn` at
    `q := pairsIn Q` (`rep_pairsIn`). Hypotheses: `rep_estOn`'s, then `rep_pairsIn`'s at `D`. -/
theorem rep_est {A B : Obj} (Q : Rel B B) (G : Rel A B)
    (P : Rel A (.prod B B)) (hP : P = pair G G) (D : Rel (.prod B B) (.prod B B)) (hD : D = ran P)
    (V : Rel B B) (hV : V = ran G) (W : Rel B (.prod B B)) (hW : W = pair V V)
    (N : Rel (.prod B B) (.prod B B)) (hN : N = ran W) (Y : Rel (.prod B B) (.prod B B))
    (hY : Y = D \ pairsIn Q D) (Z : Rel (.prod B B) (.prod B B)) (hZ : Z = Y \ N) (M : Rel A B)
    (hM : M = P ≫ outl Z)
    (h : pairOK(A, G, G) ∧ oneFit(.prod B B, Rel.n P, Rel.val P) ∧ oneFit(B, Rel.n G, Rel.val G) ∧
      pairOK(B, V, V) ∧ oneFit(.prod B B, Rel.n W, Rel.val W) ∧ diffOK(.prod B B, .prod B B, D, pairsIn Q D) ∧
      diffOK(.prod B B, .prod B B, Y, N) ∧ cmpOK(.prod B B, P, outl Z) ∧ diffOK(A, B, G, M))
    (hq : cmpOK(.prod B B, D, idU (t := .prod B B) (m := Rel.n Q) (Rel.key Q, Rel.val Q))) :
    ∀ a b, rep (est Q G) a b ↔ rep G a b ∧ ∀ c, rep G a c → c ≠ b → rep Q b c := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := h.1.2 _ rfl
  have hd : ∀ a b c, rep G a b → rep G a c → rep D (b, c) (b, c) := fun a b c hb hc => by
    rw [hD, rep_ran_corefl P (one_ok _ h.2.1.1) h.2.1.2]
    refine ⟨rfl, a, ?_⟩
    rw [hP, rep_pair _ _ (codes_faithful_wf _ _ h.1.1).1 p1 p2 p3 p4 p5]
    exact ⟨hb, hc⟩
  intro a b
  rw [show est Q G = estOn (pairsIn Q) G from rfl, rep_estOn (pairsIn Q) G P hP D hD V hV W hW N hN Y hY Z hZ M hM h]
  refine and_congr_right fun hab => ⟨fun hn c hc hne => Classical.byContradiction fun hq' =>
    hn ⟨c, hc, hne, fun h' => hq' ((rep_pairsIn Q D hq _ _).1 h').2⟩,
    fun hall ⟨c, hc, hne, hn⟩ => hn ((rep_pairsIn Q D hq _ _).2 ⟨hd a b c hab hc, hall c hc hne⟩)⟩

/-- **`rep (thinOn q G)`**: `(a, c)` of `G` is kept unless some pair `(b, b')` of values of `a` passes the test
    `q D` to `(y, c)` and not `swapIn q D`. The intermediates are bound as `thinOn` builds them; `S`'s read-back
    is `rep_swapIn`. Hypotheses: `rep_pair`'s at `P`; `rep_diff`'s at `Y` and the result; `rep_comp`'s at `M`. -/
theorem rep_thinOn {A B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B)) (G : Rel A B)
    (P : Rel A (.prod B B)) (hP : P = pair G G) (D : Rel (.prod B B) (.prod B B)) (hD : D = ran P)
    (S : Rel (.prod B B) (.prod B B)) (hS : S = swapIn q D) (Y : Rel (.prod B B) (.prod B B)) (hY : Y = q D \ S)
    (M : Rel A B) (hM : M = P ≫ outr Y)
    (h : pairOK(A, G, G) ∧ diffOK(.prod B B, .prod B B, q D, S) ∧ cmpOK(.prod B B, P, outr Y) ∧
      diffOK(A, B, G, M)) :
    ∀ a c, rep (thinOn q G) a c ↔ rep G a c ∧
      ¬ ∃ b b' y, rep G a b ∧ rep G a b' ∧ rep (q D) (b, b') (y, c) ∧ ¬ rep S (b, b') (y, c) := by
  obtain ⟨⟨hPf, hP'⟩, hY', ⟨hMf, hM'⟩, hE'⟩ := h
  obtain ⟨p1, p2, p3, p4, p5⟩ := hP' _ rfl
  obtain ⟨m1, m2, m3, m4⟩ := hM' _ rfl
  obtain ⟨y1, y2⟩ := hY' _ rfl
  obtain ⟨y3, y4⟩ := y2
  obtain ⟨e1, e2⟩ := hE' _ rfl
  obtain ⟨e3, e4⟩ := e2
  have eP : ∀ a b c, rep P a (b, c) ↔ rep G a b ∧ rep G a c := fun a b c => by
    rw [hP, rep_pair _ _ (codes_faithful_wf _ _ hPf).1 p1 p2 p3 p4 p5]; exact Iff.rfl
  have eY : ∀ x x', rep Y x x' ↔ rep (q D) x x' ∧ ¬ rep S x x' := fun x x' => by
    rw [hY]; exact rep_diff (q D) S y1 y3 y4 x x'
  have eM : ∀ a c, rep M a c ↔ ∃ x, rep P a x ∧ ∃ y, rep Y x (y, c) := fun a c => by
    rw [hM, rep_comp _ _ (codes_faithful_wf _ _ hMf).1 m1 m2 m3 m4, Freyd.Alg.RelSet.comp_apply]
    exact exists_congr fun x => and_congr Iff.rfl (outr_holds Y x c)
  have eE : ∀ a c, rep (thinOn q G) a c ↔ rep G a c ∧ ¬ rep M a c := fun a c => by
    rw [show thinOn q G = G \ M by rw [hM, hY, hS, hD, hP]; rfl]
    exact rep_diff G M e1 e3 e4 a c
  intro a c
  rw [eE]
  refine and_congr_right fun _ => not_congr ?_
  rw [eM]
  constructor
  · rintro ⟨⟨b, b'⟩, hx, y, hy⟩
    obtain ⟨hb, hb'⟩ := (eP a b b').1 hx
    exact ⟨b, b', y, hb, hb', (eY _ _).1 hy⟩
  · rintro ⟨b, b', y, hb, hb', hy⟩
    exact ⟨(b, b'), (eP a b b').2 ⟨hb, hb'⟩, y, (eY _ _).2 hy⟩

/-- **`rep (thin Q G)`: the values `c` of `a` with no value `b` of `a` strictly `Q`-below**: `(a, c)` of `G` is
    dropped when some value `b` of `a` has `b Q c` and not `c Q b`. `rep_thinOn` at `q := pairsIn Q`, `rep_swapIn`
    there, `rep_pairsIn` at `D` and at `E`. Hypotheses: `rep_thinOn`'s, `rep_swapIn`'s, `rep_ran`'s at `D` and
    `E`, `rep_pairsIn`'s at `D` and `E`. -/
theorem rep_thin {A B : Obj} (Q : Rel B B) (G : Rel A B)
    (P : Rel A (.prod B B)) (hP : P = pair G G) (D : Rel (.prod B B) (.prod B B)) (hD : D = ran P)
    (s : Rel (.prod B B) (.prod B B)) (hs : s = pair (outr D) (outl D))
    (E : Rel (.prod B B) (.prod B B)) (hE : E = ran s) (Ms : Rel (.prod B B) (.prod B B))
    (hMs : Ms = s ≫ pairsIn Q E)
    (S : Rel (.prod B B) (.prod B B)) (hS : S = swapIn (pairsIn Q) D) (Y : Rel (.prod B B) (.prod B B))
    (hY : Y = pairsIn Q D \ S) (M : Rel A B) (hM : M = P ≫ outr Y)
    (h : pairOK(A, G, G) ∧ diffOK(.prod B B, .prod B B, pairsIn Q D, S) ∧ cmpOK(.prod B B, P, outr Y) ∧
      diffOK(A, B, G, M))
    (hsw : pairOK(.prod B B, outr D, outl D) ∧ cmpOK(.prod B B, s, pairsIn Q E) ∧
      oneFit(.prod B B, Rel.n Ms, Rel.key Ms))
    (hDf : oneFit(.prod B B, Rel.n P, Rel.val P)) (hEf : oneFit(.prod B B, Rel.n s, Rel.val s))
    (hqD : cmpOK(.prod B B, D, idU (t := .prod B B) (m := Rel.n Q) (Rel.key Q, Rel.val Q)))
    (hqE : cmpOK(.prod B B, E, idU (t := .prod B B) (m := Rel.n Q) (Rel.key Q, Rel.val Q))) :
    ∀ a c, rep (thin Q G) a c ↔ rep G a c ∧ ¬ ∃ b, rep G a b ∧ rep Q b c ∧ ¬ rep Q c b := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := h.1.2 _ rfl
  obtain ⟨s1, s2, s3, s4, s5⟩ := hsw.1.2 _ rfl
  have eP : ∀ a b c, rep P a (b, c) ↔ rep G a b ∧ rep G a c := fun a b c => by
    rw [hP, rep_pair _ _ (codes_faithful_wf _ _ h.1.1).1 p1 p2 p3 p4 p5]; exact Iff.rfl
  have eD : ∀ x x', rep D x x' ↔ x = x' ∧ ∃ a, rep P a x := fun x x' => by
    rw [hD, rep_ran_corefl P (one_ok _ hDf.1) hDf.2]; exact Iff.rfl
  have es : ∀ x u v, rep s x (u, v) ↔ (∃ y, rep D x (y, u)) ∧ ∃ z, rep D x (v, z) := fun x u v => by
    rw [hs, rep_pair _ _ (codes_faithful_wf _ _ hsw.1.1).1 s1 s2 s3 s4 s5]
    exact and_congr (outr_holds D x u) (outl_holds D x v)
  have eE : ∀ x x', rep E x x' ↔ x = x' ∧ ∃ y, rep s y x := fun x x' => by
    rw [hE, rep_ran_corefl s (one_ok _ hEf.1) hEf.2]; exact Iff.rfl
  have eS : ∀ p p', rep S p p' ↔
      p = p' ∧ ∃ u v w, ((∃ y, rep D p (y, u)) ∧ ∃ z, rep D p (v, z)) ∧ rep (pairsIn Q E) (u, v) w := by
    rw [hS]; exact rep_swapIn (pairsIn Q) D s hs E hE Ms hMs hsw
  have eqD := rep_pairsIn Q D hqD
  have eqE := rep_pairsIn Q E hqE
  intro a c
  rw [show thin Q G = thinOn (pairsIn Q) G from rfl, rep_thinOn (pairsIn Q) G P hP D hD S hS Y hY M hM h a c]
  refine and_congr_right fun hac => not_congr ⟨?_, ?_⟩
  · rintro ⟨b, b', y, hb, hb', hq, hnS⟩
    obtain ⟨hd, hQ⟩ := (eqD _ _).1 hq
    obtain ⟨e, -⟩ := (eD _ _).1 hd
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    subst e1
    subst b'
    have hbc : rep D (b, c) (b, c) := (eD _ _).2 ⟨rfl, a, (eP a b c).2 ⟨hb, hac⟩⟩
    refine ⟨b, hb, hQ, fun hcb => hnS ((eS _ _).2 ⟨rfl, c, b, (c, b), ⟨⟨b, hbc⟩, c, hbc⟩,
      (eqE _ _).2 ⟨(eE _ _).2 ⟨rfl, (b, c), (es _ _ _).2 ⟨⟨b, hbc⟩, c, hbc⟩⟩, hcb⟩⟩)⟩
  · rintro ⟨b, hb, hQ, hncb⟩
    have hbc : rep D (b, c) (b, c) := (eD _ _).2 ⟨rfl, a, (eP a b c).2 ⟨hb, hac⟩⟩
    refine ⟨b, c, b, hb, hac, (eqD _ _).2 ⟨hbc, hQ⟩, fun hS' => hncb ?_⟩
    obtain ⟨-, u, v, w, ⟨⟨y, hy⟩, z, hz⟩, hw⟩ := (eS _ _).1 hS'
    obtain ⟨e1, -⟩ := (eD _ _).1 hy
    obtain ⟨e2, -⟩ := (eD _ _).1 hz
    obtain ⟨hE', hQw⟩ := (eqE _ _).1 hw
    obtain ⟨e3, -⟩ := (eE _ _).1 hE'
    subst e3
    have hu : c = u := (Prod.mk.inj e1).2
    have hv : b = v := (Prod.mk.inj e2).1
    subst hu hv
    exact hQw

end Est

/-! ## `P` -/

section PowerRel

open FoldN OpsN Prim

namespace DivN

-- `rep_leftDiv`'s hypotheses at `leftDiv R S Ub Uc` (`R : Rel K B`, `S : Rel K C`; `Ub`, `Uc` of sizes `mb`, `mc`),
-- its codes `kc`, `ycs`, `zc`, rows `y`, kept rows `I` and sides `P`, `Q` bound by their equations
set_option hygiene false in
scoped notation "divOK(" K ", " B ", " C ", " R ", " S ", " mb ", " Ub ", " mc ", " Uc ")" =>
  (Obj.CodesFit K (#v[⟨Rel.n R, Rel.key R⟩] : Vector (Part K) 1) ∧
    Obj.CodesFit B (#v[⟨Rel.n R, Rel.val R⟩] : Vector (Part B) 1) ∧
    Vals.PickFits K (Rel.key R) (List.range (Rel.n R).toNat) ∧ Vals.PickFits B (Rel.val R) (List.range (Rel.n R).toNat) ∧
    Obj.CodesFit K (#v[⟨Rel.n S, Rel.key S⟩] : Vector (Part K) 1) ∧
    Obj.CodesFit C (#v[⟨Rel.n S, Rel.val S⟩] : Vector (Part C) 1) ∧
    Vals.PickFits K (Rel.key S) (List.range (Rel.n S).toNat) ∧ Vals.PickFits C (Rel.val S) (List.range (Rel.n S).toNat) ∧
    Obj.CodesFit K (#v[⟨Rel.n (Rel.nub R), Rel.key (Rel.nub R)⟩, ⟨Rel.n (Rel.nub S), Rel.key (Rel.nub S)⟩] :
      Vector (Part K) 2) ∧
    (Rel.n S).toNat < 2 ^ 63 ∧ (Rel.n R).toNat * (Rel.n S).toNat < min (2 ^ 63) USize.size ∧
    ∀ kc : Vector Code 2, kc = Obj.codes K (#v[⟨Rel.n (Rel.nub R), Rel.key (Rel.nub R)⟩,
        ⟨Rel.n (Rel.nub S), Rel.key (Rel.nub S)⟩] : Vector (Part K) 2) →
      Vals.PickFits B (Rel.val (Rel.nub R)) ((jp(kc[0]'Nat.zero_lt_two, kc[1]'Nat.one_lt_two)).map Prod.fst) ∧
      Vals.PickFits C (Rel.val (Rel.nub S)) ((jp(kc[0]'Nat.zero_lt_two, kc[1]'Nat.one_lt_two)).map Prod.snd) ∧
      ∀ y : Rel B C, y = yJ(B, C, Rel.nub R, Rel.nub S, kc[0]'Nat.zero_lt_two, kc[1]'Nat.one_lt_two) →
      Obj.CodesFit B (#v[⟨Rel.n y, Rel.key y⟩, ⟨Rel.n (Rel.nub R), Rel.val (Rel.nub R)⟩, ⟨mb, Ub⟩] :
        Vector (Part B) 3) ∧
      Obj.CodesFit C (#v[⟨Rel.n y, Rel.val y⟩] : Vector (Part C) 1) ∧
      ∀ ycs : Vector Code 3, ycs = Obj.codes B (#v[⟨Rel.n y, Rel.key y⟩, ⟨Rel.n (Rel.nub R), Rel.val (Rel.nub R)⟩,
          ⟨mb, Ub⟩] : Vector (Part B) 3) →
      ∀ zc : Vector Code 1, zc = Obj.codes C (#v[⟨Rel.n y, Rel.val y⟩] : Vector (Part C) 1) →
      Vals.PickFits B Ub (List.range (USize.toNat mb)) ∧
      USize.toNat mb * USize.toNat mc < min (2 ^ 63) USize.size ∧
      Vals.PickFits B (vacY(B, Ub, ycs)).2
        ((List.range ((vacY(B, Ub, ycs)).1.toNat * USize.toNat mc)).map (· / USize.toNat mc)) ∧
      Vals.PickFits C Uc ((List.range ((vacY(B, Ub, ycs)).1.toNat * USize.toNat mc)).map (· % USize.toNat mc)) ∧
      ∀ I : ByteArray, I = (longCount "\\" (tuples.tupleIds (ycs[0]'(Nat.zero_lt_succ 2)) #[zc[0]'Nat.zero_lt_one]).2
          fun g _ => gather 8 (tuples.tupleIds (ycs[0]'(Nat.zero_lt_succ 2)) #[zc[0]'Nat.zero_lt_one]).2
            (whereEqV g (classSizes (ycs[0]'(Nat.zero_lt_succ 2)).n
                (tuples.tupleIds (ycs[0]'(Nat.zero_lt_succ 2)) #[zc[0]'Nat.zero_lt_one]))
              (atCnt (cnt (ycs[1]'(Nat.succ_lt_succ (Nat.zero_lt_succ 1))))
                ((ycs[0]'(Nat.zero_lt_succ 2)).gather
                  (tuples.tupleIds (ycs[0]'(Nat.zero_lt_succ 2)) #[zc[0]'Nat.zero_lt_one]).2)))) →
      ∀ P : Rel B C, P = Rel.rows y I → ∀ Q : Rel B C, Q = top (vacY(B, Ub, ycs)).2 Uc →
        ∃ hU : (Rel.n P).toNat + (Rel.n Q).toNat < USize.size,
          Vals.RazeFits B (Rel.key P) (Rel.key Q) ∧ Vals.RazeFits C (Rel.val P) (Rel.val Q) ∧
          Obj.CodesFit B (#v[⟨(PQ(B, C)).n, (PQ(B, C)).key⟩] : Vector (Part B) 1) ∧
          Obj.CodesFit C (#v[⟨(PQ(B, C)).n, (PQ(B, C)).val⟩] : Vector (Part C) 1) ∧
          Vals.PickFits B (PQ(B, C)).key (List.range (PQ(B, C)).n.toNat) ∧
          Vals.PickFits C (PQ(B, C)).val (List.range (PQ(B, C)).n.toNat))

end DivN

open DivN

end PowerRel


#print axioms rep_tail
#print axioms rep_pairsIn
#print axioms rep_swapIn
#print axioms rep_estOn
#print axioms rep_est
#print axioms rep_thinOn
#print axioms rep_thin

end LeetQ.Rel.Rep
