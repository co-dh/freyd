/-
  The list primitives' twins read back: each `rep_<op>C` is `rep_<op>` under the twin's one bit, the bit deciding
  every size premise `rep_<op>` takes. `CRel` carries the bit along a program, as `CRel.lean` does for `≫`, `∩`, `∪`.
  The composites `uncat`, `snoc` are twinned by composing the twins of their pieces: their bit is the `&&` of the
  pieces' bits, each piece's `_ok` lemma reading it as that piece's premises.
-/
import LeetQ.Rel.CRelRel
import LeetQ.Rel.RepPerm

namespace LeetQ.Rel

namespace Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF
open FoldN OpsN Prim Pow ListN

/-- **`expand`'s copies' count is the counts summed**, each count below `2^63` (`expand_idx`): the `O(1)` length a
    twin decides a count bound on, in place of folding the counts. -/
theorem len_expand_sum {n : USize} {cnt : ByteArray} (hl : len cnt = n.toNat)
    (hc : ∀ t < n.toNat, (Column.bitsAt cnt (t * 8) 8).toNat < 2 ^ 63) :
    len (expandBytes 8 0 (tilLongs n) cnt) =
      ((List.range n.toNat).map fun r => (Column.bitsAt cnt (r * 8) 8).toNat).sum := by
  rw [len_eq_ids, expand_idx (Nat.le_of_eq hl) (fun t ht => hc t (hl ▸ ht)), List.length_flatMap, hl]
  simp only [List.length_replicate]

/-- `expand` of an array side's counts copies their sum, the payload count below `2^63` (`slicesOf_row`). -/
theorem len_expand_slicesOf {B : Obj} {n : USize} (X : Vals (.arr B) n) (hp : X.1.toNat < 2 ^ 63) :
    len (expandBytes 8 0 (tilLongs n) (slicesOf X).2) =
      ((List.range n.toNat).map fun r => (Column.bitsAt (slicesOf X).2 (r * 8) 8).toNat).sum :=
  len_expand_sum (len_slices _ _ _ _).2 fun t ht => by have := (slicesOf_row X hp ht).1; omega

/-- Counts each one more than `g`'s sum to `g`'s sum plus their number. -/
theorem sum_range_add_one {f g : Nat → Nat} {N : Nat} (h : ∀ r < N, f r = g r + 1) :
    ((List.range N).map f).sum = ((List.range N).map g).sum + N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [List.range_succ, List.map_append, List.sum_append_nat, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, ih fun r hr => h r (by omega), h N (by omega)]
    omega

/-- **`unconsC`'s bit is `rep_uncons`'s fit**: the pick of `X` at its non-empty rows (`pickC_fits`). -/
theorem unconsC_fits {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (unconsC X).2 = true) :
    Vals.PickFits (.arr B) X
      ((List.range (len (whereBits n (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf X).2 (one 0) n)))).map fun q =>
        (Column.bitsAt (whereBits n (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf X).2 (one 0) n)) (q * 8) 8).toNat) := by
  simp only [unconsC, longCount, need] at hb
  split at hb
  · rename_i hlt
    have hf := Vals.pickC_fits (.arr B) X _ _ _ hb
    rwa [USize.toNat_ofNat_of_lt' hlt] at hf
  · exact absurd hb Bool.false_ne_true

theorem rep_unconsC {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (unconsC X).2 = true) :
    ∀ (xs : List B.El) b bs, rep (unconsC X).1 xs (b, bs) ↔ (∃ j, X.row j = xs) ∧ xs = b :: bs := by
  rw [unconsC_fst]; exact rep_uncons X _ rfl _ rfl _ rfl (unconsC_fits X hb)

theorem rep_tailC {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (tailC X).2 = true) :
    ∀ (xs bs : List B.El), rep (tailC X).1 xs bs ↔ (∃ j, X.row j = xs) ∧ ∃ b, xs = b :: bs := by
  rw [tailC_fst]; exact rep_tail X _ rfl _ rfl _ rfl (unconsC_fits X hb)

theorem rep_atPosC {B : Obj} {n : USize} (k : Nat) (X : Vals (.arr B) n) (hb : (atPosC k X).2 = true) :
    ∀ (xs : List B.El) x, rep (atPosC k X).1 xs x ↔ (∃ j, X.row j = xs) ∧ ∃ h : k < xs.length, x = xs[k]'h := by
  simp only [atPosC, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact rep_atPos k X hb.1 _ rfl _ rfl (pickFits_of_fitsN _ X _ hb.2 _ (by simp))

theorem rep_unsnocC {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (unsnocC X).2 = true) :
    ∀ (xs : List B.El) bs b, rep (unsnocC X).1 xs (bs, b) ↔ (∃ j, X.row j = xs) ∧ xs = bs ++ [b] :=
  rep_unsnoc X _ rfl _ rfl _ rfl (pickFits_of_fitsN _ X _ hb _ (by simp))

/-- **`zipC`'s bit is `rep_zip`'s premises**: the `fitsN` bits its `hPa`, `hPb`, `hKf`; the copies' count decided
    inside `expand` its `hS`, `expand`'s guard its `hU`, both through `len_expand_sum` (each lesser count below a
    side's payload, `lesser_get`). -/
theorem zipC_ok {K A B : Obj} (P : Rel K (.prod (.arr A) (.arr B))) (hb : (zipC P).2 = true) :
    Vals.PickFits (.arr A) P.val.1 (List.range P.n.toNat) ∧ Vals.PickFits (.arr B) P.val.2 (List.range P.n.toNat) ∧
    ((List.range P.n.toNat).map fun r => (Column.bitsAt (Kernel.Ew.val Ew.lesser Ew.i64 Ew.vv nul
      (slicesOf P.val.1).2 (slicesOf P.val.2).2 P.n) (r * 8) 8).toNat).sum < 2 ^ 63 ∧
    ((List.range P.n.toNat).map fun r => (Column.bitsAt (Kernel.Ew.val Ew.lesser Ew.i64 Ew.vv nul
      (slicesOf P.val.1).2 (slicesOf P.val.2).2 P.n) (r * 8) 8).toNat).sum < USize.size ∧
    Vals.PickFits K P.key ((List.range P.n.toNat).map fun q => (Column.bitsAt (tilLongs P.n) (q * 8) 8).toNat) := by
  simp only [zipC, expand, need, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨ha, hb'⟩, hk⟩, hb⟩ := hb
  have hPa := pickFits_of_fitsN _ _ _ ha (List.range P.n.toNat) (by simp)
  have hPb := pickFits_of_fitsN _ _ _ hb' (List.range P.n.toNat) (by simp)
  have hpa := (pickFits_payload _ hPa).1
  have hpb := (pickFits_payload _ hPb).1
  have hsum := len_expand_sum (n := P.n)
    (cnt := Kernel.Ew.val Ew.lesser Ew.i64 Ew.vv nul (slicesOf P.val.1).2 (slicesOf P.val.2).2 P.n) (len_val ..)
    fun t ht => by
      have := (slicesOf_row P.val.1 hpa ht).1; have := (slicesOf_row P.val.2 hpb ht).1
      rw [lesser_get ht (by omega) (by omega)]; omega
  split at hb
  · rename_i hx
    simp only [decide_eq_true_eq] at hb
    rw [USize.toNat_ofNat_of_lt' hx, hsum] at hb
    rw [hsum] at hx
    exact ⟨hPa, hPb, hb, hx, pickFits_of_fitsN _ _ _ hk _ (by simp)⟩
  · exact absurd hb Bool.false_ne_true

theorem rep_zipC {K A B : Obj} (P : Rel K (.prod (.arr A) (.arr B))) (hb : (zipC P).2 = true) :
    ∀ k zs, rep (zipC P).1 k zs ↔ ∃ xs ys, rep P k (xs, ys) ∧ zs = List.zip xs ys := by
  rw [zipC_fst]
  obtain ⟨hPa, hPb, hS, hU, hk⟩ := zipC_ok P hb
  exact rep_zip P hPa hPb _ rfl hS hU _ rfl _ rfl _ rfl _ rfl _ rfl hk

/-- **`consC`'s bit is `rep_cons`'s premises** (`consOK`): the `fitsN` bits its `hV`, `hKf`; inside `expand`, the
    copies' count `k` plus the rows decided its `hS`, `need`'s guard its `hU` (`len_expand_slicesOf`), the raze's
    bit its `hRf` (`razeC_fits`), the last pick's its `hFf` (`pickC_fits`). -/
theorem consC_ok {K B : Obj} (P : Rel K (.prod B (.arr B))) (hb : (consC P).2 = true) : consOK(K, B, P) := by
  simp only [consC, expand, longCount, need, Bool.and_eq_true] at hb
  obtain ⟨⟨hV, hK⟩, hb⟩ := hb
  have hVf := pickFits_of_fitsN _ _ _ hV (List.range P.n.toNat) (by simp)
  refine ⟨hVf, ?_⟩
  rintro s rfl
  split at hb
  · rename_i hx
    split at hb
    · rename_i hN
      split at hb
      · rename_i hp
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        obtain ⟨⟨h63, hR⟩, hF⟩ := hb
        rw [USize.toNat_ofNat_of_lt' hx, len_expand_slicesOf _ (pickFits_payload _ hVf).1] at h63 hN
        refine ⟨h63, hN, ?_⟩
        rintro xi rfl m rfl xr rfl j rfl tl rfl c1 rfl hi rfl lo rfl dst rfl g rfl
        have hFf := Vals.pickC_fits B _ _ _ _ hF
        rw [razeC_fst, USize.toNat_ofNat_of_lt' hp] at hFf
        exact ⟨pickFits_of_fitsN _ _ _ hK _ (by simp), Obj.razeC_fits B _ _ _ (by rfl) _ hR, fun _ => hFf⟩
      · exact absurd hb Bool.false_ne_true
    · exact absurd hb Bool.false_ne_true
  · exact absurd hb Bool.false_ne_true

theorem rep_consC {K B : Obj} (P : Rel K (.prod B (.arr B))) (hb : (consC P).2 = true) :
    ∀ k ys, rep (consC P).1 k ys ↔ ∃ b bs, rep P k (b, bs) ∧ ys = b :: bs := by
  rw [consC_fst]; exact rep_cons_ok P (consC_ok P hb)

open Freyd Freyd.Alg Freyd.Alg.RelSet in
/-- **`rep (α)` under `alphaC`'s bit**: `need`'s guard is `rep_alpha`'s `hN`, the decided bound its `h63`, the
    raze's bit its `hF` (`razeC_fits`), `consC`'s bit its `hc` (`consC_ok`). -/
theorem rep_alphaC {K B : Obj} {n : USize} (I : Vals K 1) (P : Vals (.prod B (.arr B)) n)
    (hb : (alphaC I P).2 = true) :
    rep (alphaC I P).1 = Freyd.Alg.junc (sumCop (⟨K.El⟩ : RelSet.{0}) ⟨B.El × List B.El⟩)
      (corefl (A := (⟨K.El⟩ : RelSet.{0})) (fun u => ∃ i, I.row i = u) ≫
        (graph (fun _ => []) :(⟨K.El⟩ : RelSet.{0}) ⟶ ⟨List B.El⟩))
      (corefl (A := (⟨B.El × List B.El⟩ : RelSet.{0})) (fun p => ∃ i, P.row i = p) ≫
        (graph (fun p => p.1 :: p.2) :(⟨B.El × List B.El⟩ : RelSet.{0}) ⟶ ⟨List B.El⟩)) := by
  rw [alphaC_fst]
  unfold alphaC at hb
  generalize hc : consC (idU P) = c at hb
  obtain ⟨S, cb⟩ := c
  have hS : S = cons (idU P) := (congrArg Prod.fst hc).symm.trans (consC_fst _)
  subst hS
  simp only [need] at hb
  split at hb
  · rename_i hN
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨h63, hv⟩, hcb⟩ := hb
    exact rep_alpha I P hN h63 (Obj.razeC_fits (.arr B) _ _ _ (by rfl) _ hv) (consC_ok _ (by rw [hc]; exact hcb))
  · exact absurd hb Bool.false_ne_true

/-- **`catC`'s bit is `rep_cat`'s premises** (`catOK`), as `consC_ok`: the two copies' counts `ka + kb` decided its
    `hS`, `need`'s guard its `hU`, each a side's counts summed (`len_expand_slicesOf`). -/
theorem catC_ok {K B : Obj} (P : Rel K (.prod (.arr B) (.arr B))) (hb : (catC P).2 = true) : catOK(K, B, P) := by
  simp only [catC, expand, longCount, need, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨ha, hb'⟩, hK⟩, hb⟩ := hb
  have hPa := pickFits_of_fitsN _ _ _ ha (List.range P.n.toNat) (by simp)
  have hPb := pickFits_of_fitsN _ _ _ hb' (List.range P.n.toNat) (by simp)
  refine ⟨hPa, hPb, ?_⟩
  rintro sa rfl sb rfl
  split at hb
  · rename_i hxa
    split at hb
    · rename_i hxb
      split at hb
      · rename_i hN
        split at hb
        · rename_i hp
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
          obtain ⟨⟨h63, hR⟩, hF⟩ := hb
          rw [USize.toNat_ofNat_of_lt' hxa, USize.toNat_ofNat_of_lt' hxb,
            len_expand_slicesOf _ (pickFits_payload _ hPa).1, len_expand_slicesOf _ (pickFits_payload _ hPb).1]
            at h63 hN
          refine ⟨h63, hN, ?_⟩
          rintro xa rfl ma rfl ra rfl xb rfl mb rfl rb rfl ja rfl jb rfl ta rfl tb rfl c rfl hi rfl lo rfl da rfl
            db rfl g rfl
          have hFf := Vals.pickC_fits B _ _ _ _ hF
          rw [razeC_fst, USize.toNat_ofNat_of_lt' hp] at hFf
          exact ⟨pickFits_of_fitsN _ _ _ hK _ (by simp), Obj.razeC_fits B _ _ _ (by rfl) _ hR, fun _ => hFf⟩
        · exact absurd hb Bool.false_ne_true
      · exact absurd hb Bool.false_ne_true
    · exact absurd hb Bool.false_ne_true
  · exact absurd hb Bool.false_ne_true

/-- **`rep (cat P)` under `catC`'s bit**: `rep_cat` at `catC_ok`'s premises. -/
theorem rep_catC {K B : Obj} (P : Rel K (.prod (.arr B) (.arr B))) (hb : (catC P).2 = true) :
    ∀ k zs, rep (catC P).1 k zs ↔ ∃ xs ys, rep P k (xs, ys) ∧ zs = xs ++ ys := by
  rw [catC_fst]; exact rep_cat_ok P (catC_ok P hb)

/-- **`nestC`'s bit, read as `rep_inits`'s and `rep_tails`'s premises**: `X` fitting at all its rows; inside
    `expand`, the copies' count decided below `2^63` and `need`'s guard, each the counts plus one summed
    (`len_expand_sum`, every count plus one below `2^63` by the payload bound), and the slices' compacting pick
    fitting at the `m` copies `expand` makes (`pickC_fits`). -/
theorem nestC_bits {B : Obj} {n : USize} (X : Vals (.arr B) n)
    (f : (m : USize) → ByteArray × ByteArray → (i r : ByteArray) → len i = m.toNat → Arr .long m × Arr .long m)
    (hb : (nestC X f).2 = true) :
    ((List.range n.toNat).map fun u => (Column.bitsAt (slicesOf X).2 (u * 8) 8).toNat).sum + n.toNat < 2 ^ 63 ∧
    ((List.range n.toNat).map fun u => (Column.bitsAt (slicesOf X).2 (u * 8) 8).toNat).sum + n.toNat < USize.size ∧
    Vals.PickFits (.arr B) X ((List.range n.toNat).map fun q => (Column.bitsAt (tilLongs n) (q * 8) 8).toNat) ∧
    ∀ h : len (expandBytes 8 0 (tilLongs n) (addc n (slicesOf X).2 1)) =
        (len (expandBytes 8 0 (tilLongs n) (addc n (slicesOf X).2 1))).toUSize.toNat,
      Vals.PickFits (.arr B)
        (⟨X.1, (f _ (slicesOf X) (expandBytes 8 0 (tilLongs n) (addc n (slicesOf X).2 1))
          (sub (len (expandBytes 8 0 (tilLongs n) (addc n (slicesOf X).2 1))).toUSize
            (tilLongs (len (expandBytes 8 0 (tilLongs n) (addc n (slicesOf X).2 1))).toUSize)
            (gather 8 (sub n (sums n (addc n (slicesOf X).2 1)) (addc n (slicesOf X).2 1))
              (expandBytes 8 0 (tilLongs n) (addc n (slicesOf X).2 1)))) h).1,
          (f _ (slicesOf X) (expandBytes 8 0 (tilLongs n) (addc n (slicesOf X).2 1))
          (sub (len (expandBytes 8 0 (tilLongs n) (addc n (slicesOf X).2 1))).toUSize
            (tilLongs (len (expandBytes 8 0 (tilLongs n) (addc n (slicesOf X).2 1))).toUSize)
            (gather 8 (sub n (sums n (addc n (slicesOf X).2 1)) (addc n (slicesOf X).2 1))
              (expandBytes 8 0 (tilLongs n) (addc n (slicesOf X).2 1)))) h).2, X.2.2.2⟩ :
          Vals (.arr B) (len (expandBytes 8 0 (tilLongs n) (addc n (slicesOf X).2 1))).toUSize)
        ((List.range (len (expandBytes 8 0 (tilLongs n) (addc n (slicesOf X).2 1))).toUSize.toNat).map fun q =>
          (Column.bitsAt (tilLongs (len (expandBytes 8 0 (tilLongs n) (addc n (slicesOf X).2 1))).toUSize)
            (q * 8) 8).toNat) := by
  simp only [nestC, expand, need, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨hp1, hK⟩, hb⟩ := hb
  split at hb
  · rename_i hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨h63, hv⟩ := hb
    have hc : ∀ r < n.toNat, (Column.bitsAt (addc n (slicesOf X).2 1) (r * 8) 8).toNat =
        (Column.bitsAt (slicesOf X).2 (r * 8) 8).toNat + 1 := fun r hr => by
      have := (slicesOf_row X (by omega) hr).1
      rw [addc, val_va_get _ _ _ _ hr, bitsAt_one, addOne_toNat (by omega)]
    have hsum : len (expandBytes 8 0 (tilLongs n) (addc n (slicesOf X).2 1)) =
        ((List.range n.toNat).map fun u => (Column.bitsAt (slicesOf X).2 (u * 8) 8).toNat).sum + n.toNat := by
      rw [len_expand_sum (by rw [addc, len_val]) fun t ht => by
        rw [hc t ht]; have := (slicesOf_row X (by omega) ht).1; omega]
      exact sum_range_add_one hc
    rw [USize.toNat_ofNat_of_lt' hx, hsum] at h63
    rw [hsum] at hx
    exact ⟨h63, hx, pickFits_of_fitsN _ X _ hK _ (by simp), fun _ => Vals.pickC_fits (.arr B) _ _ _ _ hv⟩
  · exact absurd hb Bool.false_ne_true

theorem rep_initsC {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (initsC X).2 = true) :
    ∀ xs yss, rep (initsC X).1 xs yss ↔ (∃ j, X.row j = xs) ∧
      yss = (List.range (xs.length + 1)).map fun k => xs.take k := by
  obtain ⟨hS, hU, hK, hV⟩ := nestC_bits X _ hb
  rw [initsC_fst]; exact rep_inits X _ rfl hS hU _ rfl _ rfl _ rfl hK hV

theorem rep_tailsC {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (tailsC X).2 = true) :
    ∀ xs yss, rep (tailsC X).1 xs yss ↔ (∃ j, X.row j = xs) ∧
      yss = (List.range (xs.length + 1)).map fun k => xs.drop k := by
  obtain ⟨hS, hU, hK, hV⟩ := nestC_bits X _ hb
  rw [tailsC_fst]; exact rep_tails X _ rfl hS hU _ rfl _ rfl _ rfl hK hV

/-- **`memC`'s bit is `rep_mem`'s premises**: the `fitsN` bit its `hv`, and with it `expand`'s guard
    (`slicesOf_copies`); the keys' pick bit, at the copies `expand` makes, its `hk` (`pickC_fits`, `copies_rows`). -/
theorem memC_ok {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (memC X).2 = true) :
    Vals.PickFits (.arr B) X (List.range n.toNat) ∧
    Vals.PickFits (.arr B) X ((List.range n.toNat).flatMap fun r =>
      if h : r < n.toNat then List.replicate (X.row ⟨r, h⟩).length r else []) := by
  simp only [memC, Bool.and_eq_true] at hb
  obtain ⟨hk, hv⟩ := hb
  have hv' : Vals.PickFits (.arr B) X (List.range n.toNat) := pickFits_of_fitsN (.arr B) X _ hv _ (by simp)
  refine ⟨hv', ?_⟩
  unfold expand need at hk
  dsimp only at hk
  rw [dif_pos (slicesOf_copies X hv').1] at hk
  rw [← copies_rows X hv']
  exact Vals.pickC_fits (.arr B) X _ _ _ hk

/-- **`pairC`'s bit is `rep_pair`'s premises** (`pairOK`), as `compC_ok`: the keys' codes fitting, the decided
    bounds, and the three picks' bits read at the join's rows (`join_rows`, `pickC_fits`). -/
theorem pairC_ok {A B C : Obj} (R : Rel A B) (S : Rel A C) (hb : (pairC R S).2 = true) : pairOK(A, R, S) := by
  simp only [pairC, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hcb, hrn⟩, hM⟩, hp⟩ := hb
  have hcf := Obj.codesC_fits A _ hcb
  refine ⟨hcf, ?_⟩
  rintro kc rfl
  have hc := (codes_faithful_wf A _ hcf).1
  obtain ⟨hlw, hln, hls, -⟩ := hc.2 (k := 0) (by decide)
  obtain ⟨hrw, hrn', hrs, hrc⟩ := hc.2 (k := 1) (by decide)
  replace hln : ((A.codes (#v[⟨R.n, R.key⟩, ⟨S.n, S.key⟩] : Vector (Part A) 2))[0]'Nat.zero_lt_two).n = R.n := hln
  replace hrn' : ((A.codes (#v[⟨R.n, R.key⟩, ⟨S.n, S.key⟩] : Vector (Part A) 2))[1]'Nat.one_lt_two).n = S.n := hrn'
  have hcf' := Obj.codesC_fst A (#v[⟨R.n, R.key⟩, ⟨S.n, S.key⟩] : Vector (Part A) 2)
  rw [← hcf'] at hlw hls hrw hrs hrc hln hrn'
  obtain ⟨-, hZ⟩ := join_rows _ _ hlw hls hrw hrs hrc (by rw [hrn']; exact hrn) (by rw [hln, hrn']; exact hM)
  unfold longCount need at hp
  split at hp
  · rename_i hlt
    simp only [Bool.and_eq_true] at hp
    have e := hZ _ (USize.toNat_ofNat_of_lt' hlt).symm
    have hfA := Vals.pickC_fits A R.key _ _ _ hp.1.1
    have hfB := Vals.pickC_fits B R.val _ _ _ hp.1.2
    have hfC := Vals.pickC_fits C S.val _ _ _ hp.2
    rw [hln, hrn'] at e
    rw [hcf'] at e hfA hfB hfC
    exact ⟨hrn, hM, by rw [e, List.map_map]; exact hfA, by rw [e, List.map_map]; exact hfB,
      by rw [e, List.map_map]; exact hfC⟩
  · exact absurd hp Bool.false_ne_true

/-- `compC_ok` in `cmpOK`'s form, the codes bound by their equation. -/
theorem compC_cmpOK {A B C : Obj} (R : Rel A B) (S : Rel B C) (hb : (compC R S).2 = true) : cmpOK(B, R, S) := by
  obtain ⟨hcf, h⟩ := compC_ok R S hb
  exact ⟨hcf, fun _ e => by subst e; exact h⟩

/-- **`rep (uncat X)` under `uncatC`'s bit**: `rep_uncat` at its pieces' premises, each read off that piece's bit —
    `nestC_bits` at `inits`, `tails`, `pairC_ok`, `zipC_ok`, `memC_ok`, `compC_ok`. -/
theorem rep_uncatC {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (uncatC X).2 = true) :
    ∀ xs ys zs, rep (uncatC X).1 xs (ys, zs) ↔ (∃ j, X.row j = xs) ∧ xs = ys ++ zs := by
  rw [uncatC_fst]
  simp only [uncatC, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨hi, ht⟩, hp⟩, hz⟩, hv⟩, hc⟩ := hb
  obtain ⟨hS, hU, hK, hVi⟩ := nestC_bits X _ hi
  obtain ⟨-, -, -, hVt⟩ := nestC_bits X _ ht
  rw [initsC_fst, tailsC_fst] at hp hz hv hc
  obtain ⟨hkf, hk1⟩ := pairC_ok _ _ hp
  obtain ⟨hkn, hkM, hkA, hkB, hkC⟩ := hk1 _ rfl
  rw [pairC_fst] at hz hv hc
  obtain ⟨-, -, hS', hU', -⟩ := zipC_ok _ hz
  rw [zipC_fst] at hv hc
  obtain ⟨hmv, hmk⟩ := memC_ok _ hv
  rw [memC_fst] at hc
  obtain ⟨hjf, hjn, hjM, hjA, hjC⟩ := compC_ok _ _ hc
  exact rep_uncat X _ rfl hS hU _ rfl _ rfl _ rfl hK hVi hVt _ rfl (codes_faithful_wf _ _ hkf).1 hkn hkM hkA hkB
    hkC _ rfl _ rfl hS' hU' _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl (codes_faithful_wf _ _ hjf).1 hjn hjM hjA hjC
    hmv hmk

/-- **`rep (snoc P)` under `snocC`'s bit**: `rep_snoc` at `snocOK`, each piece's premises read off its bit —
    `ranC`'s codes and `fitsN` bits (`oneFit`), `transposeC`'s at `idU` (`tauOK`), `compC_cmpOK`, `pairC_ok`,
    `catC_ok`. -/
theorem rep_snocC {K B : Obj} (P : Rel K (.prod (.arr B) B)) (hb : (snocC P).2 = true) :
    ∀ k ys, rep (snocC P).1 k ys ↔ ∃ bs b, rep P k (bs, b) ∧ ys = bs ++ [b] := by
  rw [snocC_fst]
  simp only [snocC, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨hD, ht⟩, hT⟩, hQ⟩, hM⟩, hr⟩ := hb
  have eD : (ranC P).1 = ran P := distinctCoreflC_fst _ _
  rw [eD] at ht hT hQ hM hr
  simp only [ranC, distinctCoreflC, Bool.and_eq_true] at hD
  simp only [transposeC, Bool.and_eq_true, decide_eq_true_eq] at ht
  obtain ⟨⟨⟨⟨⟨⟨hK1, -⟩, hk1⟩, -⟩, hWk⟩, hW⟩, h63⟩ := ht
  apply rep_snoc P
  refine ⟨⟨Obj.codesC_fits _ _ hD.1, pickFits_of_fitsN _ _ _ hD.2 _ (by simp)⟩, ?_⟩
  rintro D rfl X rfl
  -- `idU X` has `X`'s row count by its definition, which `simp` leaves unfolded
  refine ⟨⟨oneOK_of_codesC B _ hK1, pickFits_of_fitsN _ _ _ hk1 _ (by simp; exact Nat.le_of_eq rfl), Obj.codesC_fits _ _ hWk,
    Obj.codesC_fits _ _ hW, h63⟩, compC_cmpOK _ _ hT, ?_⟩
  rintro T rfl
  rw [compC_fst] at hQ
  refine ⟨pairC_ok _ _ hQ, ?_⟩
  rintro Q rfl
  rw [compC_fst, pairC_fst] at hM
  refine ⟨compC_cmpOK _ _ hM, ?_⟩
  rintro M rfl
  rw [compC_fst, pairC_fst, compC_fst] at hr
  exact catC_ok _ hr

#print axioms rep_consC
#print axioms rep_catC
#print axioms rep_zipC
#print axioms rep_initsC
#print axioms rep_uncatC
#print axioms rep_snocC

end Rep

namespace CRel

open QLean QLean.Kernel LeetQ.Rel.Alg LeetQ.Rel.Rep

variable {K A B : Obj} {n : USize}

/-- `cons°` on the arrays `X`, ok where `unconsC` ran within capacity. -/
def uncons (X : Vals (.arr B) n) : CRel (.arr B) (.prod B (.arr B)) := let r := unconsC X; ⟨r.1, r.2⟩

/-- `tail` on the arrays `X`, ok where `tailC` ran within capacity. -/
def tail (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := let r := tailC X; ⟨r.1, r.2⟩

/-- `at(k)` on the arrays `X`, ok where `atPosC` ran within capacity. -/
def atPos (k : Nat) (X : Vals (.arr B) n) : CRel (.arr B) B := let r := atPosC k X; ⟨r.1, r.2⟩

/-- `snoc°` on the arrays `X`, ok where `unsnocC` ran within capacity. -/
def unsnoc (X : Vals (.arr B) n) : CRel (.arr B) (.prod (.arr B) B) := let r := unsnocC X; ⟨r.1, r.2⟩

/-- `inits` on the arrays `X`, ok where `initsC` ran within capacity. -/
def inits (X : Vals (.arr B) n) : CRel (.arr B) (.arr (.arr B)) := let r := initsC X; ⟨r.1, r.2⟩

/-- `tails` on the arrays `X`, ok where `tailsC` ran within capacity. -/
def tails (X : Vals (.arr B) n) : CRel (.arr B) (.arr (.arr B)) := let r := tailsC X; ⟨r.1, r.2⟩

/-- `cat°` on the arrays `X`, ok where `uncatC` ran within capacity. -/
def uncat (X : Vals (.arr B) n) : CRel (.arr B) (.prod (.arr B) (.arr B)) := let r := uncatC X; ⟨r.1, r.2⟩

/-- `cons`, ok where `P` is and `consC` ran within capacity. -/
def cons (P : CRel K (.prod B (.arr B))) : CRel K (.arr B) := let r := consC P.rel; ⟨r.1, P.ok && r.2⟩

/-- `cat`, ok where `P` is and `catC` ran within capacity. -/
def cat (P : CRel K (.prod (.arr B) (.arr B))) : CRel K (.arr B) := let r := catC P.rel; ⟨r.1, P.ok && r.2⟩

/-- `snoc`, ok where `P` is and `snocC` ran within capacity. -/
def snoc (P : CRel K (.prod (.arr B) B)) : CRel K (.arr B) := let r := snocC P.rel; ⟨r.1, P.ok && r.2⟩

/-- `zip`, ok where `P` is and `zipC` ran within capacity. -/
def zip (P : CRel K (.prod (.arr A) (.arr B))) : CRel K (.arr (.prod A B)) := let r := zipC P.rel; ⟨r.1, P.ok && r.2⟩

/-- `α ≜ [nil, cons]` on `I` and `P`, ok where `alphaC` ran within capacity. -/
def alpha (I : Vals K 1) (P : Vals (.prod B (.arr B)) n) : CRel (.sum K (.prod B (.arr B))) (.arr B) :=
  let r := alphaC I P; ⟨r.1, r.2⟩

theorem rep_uncons (X : Vals (.arr B) n) (hb : (uncons X).ok = true) :
    ∀ (xs : List B.El) b bs, rep (uncons X).rel xs (b, bs) ↔ (∃ j, X.row j = xs) ∧ xs = b :: bs :=
  rep_unconsC X hb

theorem rep_tail (X : Vals (.arr B) n) (hb : (tail X).ok = true) :
    ∀ (xs bs : List B.El), rep (tail X).rel xs bs ↔ (∃ j, X.row j = xs) ∧ ∃ b, xs = b :: bs :=
  rep_tailC X hb

theorem rep_atPos (k : Nat) (X : Vals (.arr B) n) (hb : (atPos k X).ok = true) :
    ∀ (xs : List B.El) x, rep (atPos k X).rel xs x ↔ (∃ j, X.row j = xs) ∧ ∃ h : k < xs.length, x = xs[k]'h :=
  rep_atPosC k X hb

theorem rep_unsnoc (X : Vals (.arr B) n) (hb : (unsnoc X).ok = true) :
    ∀ (xs : List B.El) bs b, rep (unsnoc X).rel xs (bs, b) ↔ (∃ j, X.row j = xs) ∧ xs = bs ++ [b] :=
  rep_unsnocC X hb

theorem rep_inits (X : Vals (.arr B) n) (hb : (inits X).ok = true) :
    ∀ xs yss, rep (inits X).rel xs yss ↔ (∃ j, X.row j = xs) ∧
      yss = (List.range (xs.length + 1)).map fun k => xs.take k :=
  rep_initsC X hb

theorem rep_tails (X : Vals (.arr B) n) (hb : (tails X).ok = true) :
    ∀ xs yss, rep (tails X).rel xs yss ↔ (∃ j, X.row j = xs) ∧
      yss = (List.range (xs.length + 1)).map fun k => xs.drop k :=
  rep_tailsC X hb

theorem rep_uncat (X : Vals (.arr B) n) (hb : (uncat X).ok = true) :
    ∀ xs ys zs, rep (uncat X).rel xs (ys, zs) ↔ (∃ j, X.row j = xs) ∧ xs = ys ++ zs :=
  rep_uncatC X hb

theorem rep_cons (P : CRel K (.prod B (.arr B))) (hb : (cons P).ok = true) :
    ∀ k ys, rep (cons P).rel k ys ↔ ∃ b bs, rep P.rel k (b, bs) ∧ ys = b :: bs :=
  rep_consC P.rel (by simp only [cons, Bool.and_eq_true] at hb; exact hb.2)

theorem rep_cat (P : CRel K (.prod (.arr B) (.arr B))) (hb : (cat P).ok = true) :
    ∀ k zs, rep (cat P).rel k zs ↔ ∃ xs ys, rep P.rel k (xs, ys) ∧ zs = xs ++ ys :=
  rep_catC P.rel (by simp only [cat, Bool.and_eq_true] at hb; exact hb.2)

theorem rep_snoc (P : CRel K (.prod (.arr B) B)) (hb : (snoc P).ok = true) :
    ∀ k ys, rep (snoc P).rel k ys ↔ ∃ bs b, rep P.rel k (bs, b) ∧ ys = bs ++ [b] :=
  rep_snocC P.rel (by simp only [snoc, Bool.and_eq_true] at hb; exact hb.2)

theorem rep_zip (P : CRel K (.prod (.arr A) (.arr B))) (hb : (zip P).ok = true) :
    ∀ k zs, rep (zip P).rel k zs ↔ ∃ xs ys, rep P.rel k (xs, ys) ∧ zs = List.zip xs ys :=
  rep_zipC P.rel (by simp only [zip, Bool.and_eq_true] at hb; exact hb.2)

open Freyd Freyd.Alg Freyd.Alg.RelSet in
theorem rep_alpha (I : Vals K 1) (P : Vals (.prod B (.arr B)) n) (hb : (alpha I P).ok = true) :
    rep (alpha I P).rel = Freyd.Alg.junc (sumCop (⟨K.El⟩ : RelSet.{0}) ⟨B.El × List B.El⟩)
      (corefl (A := (⟨K.El⟩ : RelSet.{0})) (fun u => ∃ i, I.row i = u) ≫
        (graph (fun _ => []) :(⟨K.El⟩ : RelSet.{0}) ⟶ ⟨List B.El⟩))
      (corefl (A := (⟨B.El × List B.El⟩ : RelSet.{0})) (fun p => ∃ i, P.row i = p) ≫
        (graph (fun p => p.1 :: p.2) :(⟨B.El × List B.El⟩ : RelSet.{0}) ⟶ ⟨List B.El⟩)) :=
  rep_alphaC I P hb

end CRel

end LeetQ.Rel
