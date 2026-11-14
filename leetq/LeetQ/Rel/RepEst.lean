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

open Pow

/-- **`rep (Arr.union X)`: each array of arrays to the array of the elements of its members**: an array
    `Arr.union X` gives `xss` holds exactly the elements of the members of `xss`, and `Arr.union X` has a row at
    `xss` exactly when `X` lists `xss`. `Arr.union X` is `E(∋)` on `X` (`rep_E` at `R := Rm`, `∋` on the payload
    of `X`), then `rep_mem` at that payload. Hypotheses: `rep_E`'s at `Rm`, `X`, then `rep_mem`'s at `X.2.2.2`. -/
theorem rep_arrUnion {A : Obj} {n : USize} (X : Vals (.arr (.arr A)) n) (Rm : Rel (.arr A) A)
    (hRm : Rm = mem X.2.2.2) (M : Rel (.arr (.arr A)) A)
    -- `rep_E` at `Rm`, `X`
    (kc vc : Code) (hkc : kc = kcR(M)) (hvc : vc = vcR(M))
    (hK : cOK(kc, Rel.n M, Rel.key M)) (hV : cOK(vc, Rel.n M, Rel.val M))
    (hk : Vals.PickFits (.arr (.arr A)) (Rel.key M) (ids (tuples.tupleIds kc #[vc]).2))
    (hv : Vals.PickFits A (Rel.val M) (ids (tuples.tupleIds kc #[vc]).2))
    (kt : Code) (hkt : kt = kcT(M))
    (hF : ∀ {i j : Nat} (hi : i < (Rel.nub M).n.toNat) (hj : j < (Rel.nub M).n.toNat),
      Column.idAt kt.b kt.w i = Column.idAt kt.b kt.w j ↔
        Vals.row (Rel.nub M).key ⟨i, hi⟩ = Vals.row (Rel.nub M).key ⟨j, hj⟩)
    (hw : kt.w = 1 ∨ kt.w = 2 ∨ kt.w = 4 ∨ kt.w = 8 ∨ kt.w = 16 ∨ kt.w = 32 ∨ kt.w = 64)
    (hn : kt.n = (Rel.nub M).n)
    (hs : kt.b.size = (kt.n.toNat * kt.w + 7) / 8)
    (hW : ∀ (B : Obj) (x : Part B), (((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 1 ∨
      ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 2 ∨ ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 4 ∨
      ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 8 ∨ ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 16 ∨
      ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 32 ∨ ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 64) ∧
      ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).b.size =
        (((Obj.codes B #v[x])[0]'Nat.zero_lt_one).n.toNat * ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w + 7) / 8 ∧
      ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).n = x.1)
    (h63 : (Rel.nub M).n.toNat < 2 ^ 63)
    (p lo : ByteArray) (hpT : p = pT(M)) (hloT : lo = loT(M))
    (hpk : Vals.PickFits (.arr (.arr A)) (Rel.nub M).key (ids p))
    (hpv : Vals.PickFits A (Rel.nub M).val (ids p))
    (hlo : Vals.PickFits (.arr (.arr A)) (Vals.pickPart (.arr (.arr A)) (Rel.nub M).key p).2 (ids lo))
    (hp : Vals.PickFits (.arr (.arr A)) (Rel.key M) (ids kc.groupIds.2))
    (pc : Vector Code 2) (hpc : pc = pairs #v[LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom M])
    (hc : codesOK(pc, pcs(LeetQ.Rel.Alg.idU X, LeetQ.Rel.Alg.dom M)))
    (I : ByteArray) (hI : I = anti (pc[0]'Nat.zero_lt_two) (pc[1]'Nat.one_lt_two))
    (hdk : Vals.PickFits (.arr (.arr A)) X (ids I))
    (hdv : Vals.PickFits (.arr (.arr A)) X (ids I))
    (D : Rel (.arr (.arr A)) (.arr (.arr A))) (hD : D = lD(M, X))
    (htN : (Rel.n D).toNat * USize.toNat 1 < USize.size)
    (ht63 : (Rel.n D).toNat * USize.toNat 1 < 2 ^ 63)
    (htA : Vals.PickFits (.arr (.arr A)) (Rel.key D)
      ((List.range ((Rel.n D).toNat * USize.toNat 1)).map (· / USize.toNat 1)))
    (htB : Vals.PickFits (.arr A) (LeetQ.Rel.Alg.nilVal A)
      ((List.range ((Rel.n D).toNat * USize.toNat 1)).map (· % USize.toNat 1)))
    (T N : Rel (.arr (.arr A)) (.arr A)) (hT : T = lT(M))
    (hN0 : N = LeetQ.Rel.Alg.top (Rel.key D) (LeetQ.Rel.Alg.nilVal A))
    (hN : (Rel.n T).toNat + (Rel.n N).toNat < USize.size)
    (hNk : ((pk(T, N)).toList.map fun c : Part (.arr (.arr A)) => c.1.toNat).sum < USize.size)
    (hNv : ((pv(T, N)).toList.map fun c : Part (.arr A) => c.1.toNat).sum < USize.size)
    (hFk : Vals.RazeFits (.arr (.arr A)) (Rel.key T) (Rel.key N))
    (hFv : Vals.RazeFits (.arr A) (Rel.val T) (Rel.val N))
    (L : Rel (.arr (.arr A)) (.arr A)) (hL : L = Uc(T, N))
    (ku vu : Code) (hku : ku = kcR(L)) (hvu : vu = vcR(L))
    (huK : cOK(ku, Rel.n L, Rel.key L)) (huV : cOK(vu, Rel.n L, Rel.val L))
    (huk : Vals.PickFits (.arr (.arr A)) (Rel.key L) (ids (tuples.tupleIds ku #[vu]).2))
    (huv : Vals.PickFits (.arr A) (Rel.val L) (ids (tuples.tupleIds ku #[vu]).2))
    (hM : M = LeetQ.Rel.Alg.mem X ≫ Rm)
    (hmv : Vals.PickFits (.arr (.arr A)) X (List.range n.toNat))
    (hmk : Vals.PickFits (.arr (.arr A)) X ((List.range n.toNat).flatMap fun r =>
      if h : r < n.toNat then List.replicate (X.row ⟨r, h⟩).length r else []))
    (hcc : codesOK(jc(mS(X), Rm), jcs(mS(X), Rm)))
    (hcrn : (Rel.n Rm).toNat < 2 ^ 63) (hcM : jcount(mS(X), Rm) < 2 ^ 63) (hcMU : jcount(mS(X), Rm) < USize.size)
    (hcA : Vals.PickFits (.arr (.arr A)) (Rel.key mS(X)) ((jpairs(mS(X), Rm)).map Prod.fst))
    (hcC : Vals.PickFits A (Rel.val Rm) ((jpairs(mS(X), Rm)).map Prod.snd))
    -- `rep_mem` at the payload `X.2.2.2`
    (hv2 : Vals.PickFits (.arr A) X.2.2.2 (List.range X.1.toNat))
    (hk2 : Vals.PickFits (.arr A) X.2.2.2 ((List.range X.1.toNat).flatMap fun r =>
      if h : r < X.1.toNat then List.replicate (X.2.2.2.row ⟨r, h⟩).length r else [])) :
    (∀ xss Y, rep (Arr.union X) xss Y → (∃ i, Vals.row X i = xss) ∧ ∀ y, y ∈ Y ↔ ∃ xs ∈ xss, y ∈ xs) ∧
      (∀ xss, (∃ Y, rep (Arr.union X) xss Y) ↔ ∃ i, Vals.row X i = xss) := by
  subst hRm
  obtain ⟨h1, h2⟩ := rep_E (mem X.2.2.2) X M kc vc hkc hvc hK hV hk hv kt hkt hF hw hn hs hW h63 p lo hpT hloT hpk
    hpv hlo hp pc hpc hc I hI hdk hdv D hD htN ht63 htA htB T N hT hN0 hN hNk hNv hFk hFv L hL ku vu hku hvu huK
    huV huk huv hM hmv hmk hcc hcrn hcM hcMU hcA hcC
  -- every element of a cell of `X` is a row of its payload: a cell's window ends inside the payload
  have hpay : ∀ xss xs, (∃ i, Vals.row X i = xss) → xs ∈ xss → ∃ i, Vals.row X.2.2.2 i = xs := by
    rintro xss xs ⟨q, rfl⟩ hx
    rw [arr_row] at hx
    obtain ⟨j, hj, hjx⟩ := List.mem_map.1 hx
    rw [List.mem_range] at hj
    rw [dif_pos (by omega)] at hjx
    exact ⟨_, hjx⟩
  refine ⟨fun xss Y h => ⟨(h1 xss Y h).1, fun y => ((h1 xss Y h).2 y).trans ?_⟩, h2⟩
  exact ⟨fun ⟨xs, hxs, hm⟩ => ⟨xs, hxs, ((rep_mem X.2.2.2 hv2 hk2 xs y).1 hm).2⟩,
    fun ⟨xs, hxs, hy⟩ => ⟨xs, hxs, (rep_mem X.2.2.2 hv2 hk2 xs y).2 ⟨hpay xss xs (h1 xss Y h).1 hxs, hy⟩⟩⟩

#print axioms rep_arrUnion

end ArrUnion

/-! ## `tail`, `pairsIn`, `swapIn`, `estOn`, `est`, `thinOn`, `thin` -/

section Est

open FoldN Prim

/-- **`rep (tail X)`: an array of `X` to its tail**: `tail X` is `outr (uncons X)` (`outr_holds`, `rep_uncons`).
    Hypotheses: `rep_uncons`'s. -/
theorem rep_tail {B : Obj} {n : USize} (X : Vals (.arr B) n) (hp : X.1.toNat < 2 ^ 63)
    (i : ByteArray) (hi : i = whereBits n (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf X).2 (one 0) n))
    (l : ByteArray) (hl : l = gather 8 (slicesOf X).1 i)
    (T : Vals (.arr B) (len i).toUSize)
    (hT : T = ⟨X.1, valCol Ew.add Ew.va l (one 1), valCol Ew.add Ew.vv l (gather 8 (slicesOf X).2 i), X.2.2.2⟩)
    (hKf : Vals.PickFits (.arr B) X ((List.range (len i)).map fun q => (Column.bitsAt i (q * 8) 8).toNat))
    (hHf : Vals.PickFits B X.2.2.2 ((List.range (len i)).map fun q => (Column.bitsAt l (q * 8) 8).toNat))
    (hTf : Vals.PickFits (.arr B) T
      ((List.range (len i)).map fun q => (Column.bitsAt (tilLongs (len i).toUSize) (q * 8) 8).toNat)) :
    ∀ (xs bs : List B.El), rep (tail X) xs bs ↔ (∃ j, X.row j = xs) ∧ ∃ b, xs = b :: bs := by
  intro xs bs
  have hu := rep_uncons X hp i hi l hl T hT hKf hHf hTf xs
  rw [rep_apply, show tail X = outr (uncons X) from rfl, outr_holds]
  exact ⟨fun ⟨b, h⟩ => ((hu b bs).1 h).imp_right fun e => ⟨b, e⟩,
    fun ⟨hj, b, e⟩ => ⟨b, (hu b bs).2 ⟨hj, e⟩⟩⟩

/-- **`rep (pairsIn Q D)`: the pairs of `D` that are pairs of `Q`**: `pairsIn Q D` is `D ≫ idU (Q.key, Q.val)`
    (`rep_comp`, `rep_idU`). Hypotheses: `rep_comp`'s. -/
theorem rep_pairsIn {B : Obj} (Q : Rel B B) (D : Rel (.prod B B) (.prod B B))
    (h : cmpOK(.prod B B, D, idU (t := .prod B B) (m := Rel.n Q) (Rel.key Q, Rel.val Q))) :
    ∀ p p', rep (pairsIn Q D) p p' ↔ rep D p p' ∧ rep Q p'.1 p'.2 := by
  obtain ⟨hf, h'⟩ := h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h' _ rfl
  have e := rep_comp _ _ (codes_faithful_wf _ _ hf).1 h1 h2 h3 h4 h5
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
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp' _ rfl
  obtain ⟨c1, c2, c3, c4, c5⟩ := hc' _ rfl
  have es : ∀ x u v, rep s x (u, v) ↔ (∃ y, rep D x (y, u)) ∧ ∃ z, rep D x (v, z) := fun x u v => by
    rw [hs, rep_pair _ _ (codes_faithful_wf _ _ hpf).1 p1 p2 p3 p4 p5 p6]
    exact and_congr (outr_holds D x u) (outl_holds D x v)
  have eM : ∀ x w, rep M x w ↔ ∃ m, rep s x m ∧ rep (q E) m w := fun x w => by
    rw [hM, rep_comp _ _ (codes_faithful_wf _ _ hcf).1 c1 c2 c3 c4 c5, Freyd.Alg.RelSet.comp_apply]
  intro p p'
  rw [show swapIn q D = dom M by rw [hM, hE, hs]; rfl, rep_dom M (one_ok _ hdf) (hdp _ rfl)]
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
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hP' _ rfl
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := hW' _ rfl
  obtain ⟨m1, m2, m3, m4, m5⟩ := hM' _ rfl
  obtain ⟨y1, y2⟩ := hY' _ rfl
  obtain ⟨y3, y4⟩ := y2 _ rfl
  obtain ⟨z1, z2⟩ := hZ' _ rfl
  obtain ⟨z3, z4⟩ := z2 _ rfl
  obtain ⟨e1, e2⟩ := hE' _ rfl
  obtain ⟨e3, e4⟩ := e2 _ rfl
  have eP : ∀ a b c, rep P a (b, c) ↔ rep G a b ∧ rep G a c := fun a b c => by
    rw [hP, rep_pair _ _ (codes_faithful_wf _ _ hPf).1 p1 p2 p3 p4 p5 p6]; exact Iff.rfl
  have eD : ∀ x x', rep D x x' ↔ x = x' ∧ ∃ a, rep P a x := fun x x' => by
    rw [hD, rep_ran P (one_ok _ hDf) (hDp _ rfl)]; exact Iff.rfl
  have eV : ∀ b b', rep V b b' ↔ b = b' ∧ ∃ a, rep G a b := fun b b' => by
    rw [hV, rep_ran G (one_ok _ hVf) (hVp _ rfl)]; exact Iff.rfl
  have eW : ∀ b u v, rep W b (u, v) ↔ rep V b u ∧ rep V b v := fun b u v => by
    rw [hW, rep_pair _ _ (codes_faithful_wf _ _ hWf).1 w1 w2 w3 w4 w5 w6]; exact Iff.rfl
  have eN : ∀ x x', rep N x x' ↔ x = x' ∧ ∃ b, rep W b x := fun x x' => by
    rw [hN, rep_ran W (one_ok _ hNf) (hNp _ rfl)]; exact Iff.rfl
  have eY : ∀ x x', rep Y x x' ↔ rep D x x' ∧ ¬ rep (q D) x x' := fun x x' => by
    rw [hY]; exact rep_diff D (q D) y1 y3 y4 x x'
  have eZ : ∀ x x', rep Z x x' ↔ rep Y x x' ∧ ¬ rep N x x' := fun x x' => by
    rw [hZ]; exact rep_diff Y N z1 z3 z4 x x'
  have eM : ∀ a b, rep M a b ↔ ∃ x, rep P a x ∧ ∃ z, rep Z x (b, z) := fun a b => by
    rw [hM, rep_comp _ _ (codes_faithful_wf _ _ hMf).1 m1 m2 m3 m4 m5, Freyd.Alg.RelSet.comp_apply]
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
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := h.1.2 _ rfl
  have hd : ∀ a b c, rep G a b → rep G a c → rep D (b, c) (b, c) := fun a b c hb hc => by
    rw [hD, rep_ran P (one_ok _ h.2.1.1) (h.2.1.2 _ rfl)]
    refine ⟨rfl, a, ?_⟩
    rw [hP, rep_pair _ _ (codes_faithful_wf _ _ h.1.1).1 p1 p2 p3 p4 p5 p6]
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
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hP' _ rfl
  obtain ⟨m1, m2, m3, m4, m5⟩ := hM' _ rfl
  obtain ⟨y1, y2⟩ := hY' _ rfl
  obtain ⟨y3, y4⟩ := y2 _ rfl
  obtain ⟨e1, e2⟩ := hE' _ rfl
  obtain ⟨e3, e4⟩ := e2 _ rfl
  have eP : ∀ a b c, rep P a (b, c) ↔ rep G a b ∧ rep G a c := fun a b c => by
    rw [hP, rep_pair _ _ (codes_faithful_wf _ _ hPf).1 p1 p2 p3 p4 p5 p6]; exact Iff.rfl
  have eY : ∀ x x', rep Y x x' ↔ rep (q D) x x' ∧ ¬ rep S x x' := fun x x' => by
    rw [hY]; exact rep_diff (q D) S y1 y3 y4 x x'
  have eM : ∀ a c, rep M a c ↔ ∃ x, rep P a x ∧ ∃ y, rep Y x (y, c) := fun a c => by
    rw [hM, rep_comp _ _ (codes_faithful_wf _ _ hMf).1 m1 m2 m3 m4 m5, Freyd.Alg.RelSet.comp_apply]
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
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := h.1.2 _ rfl
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hsw.1.2 _ rfl
  have eP : ∀ a b c, rep P a (b, c) ↔ rep G a b ∧ rep G a c := fun a b c => by
    rw [hP, rep_pair _ _ (codes_faithful_wf _ _ h.1.1).1 p1 p2 p3 p4 p5 p6]; exact Iff.rfl
  have eD : ∀ x x', rep D x x' ↔ x = x' ∧ ∃ a, rep P a x := fun x x' => by
    rw [hD, rep_ran P (one_ok _ hDf.1) (hDf.2 _ rfl)]; exact Iff.rfl
  have es : ∀ x u v, rep s x (u, v) ↔ (∃ y, rep D x (y, u)) ∧ ∃ z, rep D x (v, z) := fun x u v => by
    rw [hs, rep_pair _ _ (codes_faithful_wf _ _ hsw.1.1).1 s1 s2 s3 s4 s5 s6]
    exact and_congr (outr_holds D x u) (outl_holds D x v)
  have eE : ∀ x x', rep E x x' ↔ x = x' ∧ ∃ y, rep s y x := fun x x' => by
    rw [hE, rep_ran s (one_ok _ hEf.1) (hEf.2 _ rfl)]; exact Iff.rfl
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

#print axioms rep_tail
#print axioms rep_pairsIn
#print axioms rep_swapIn
#print axioms rep_estOn
#print axioms rep_est
#print axioms rep_thinOn
#print axioms rep_thin

end LeetQ.Rel.Rep
