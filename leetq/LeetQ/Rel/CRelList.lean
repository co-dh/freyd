/-
  The list primitives' twins read back: each `rep_<op>C` is `rep_<op>` under the twin's one bit, the bit deciding
  every size premise `rep_<op>` takes. `CRel` carries the bit along a program, as `CRel.lean` does for `≫`, `∩`, `∪`.
  The composites `uncat`, `snoc` are twinned by composing the twins of their pieces: their bit is the `&&` of the
  pieces' bits, each piece's `_ok` lemma reading it as that piece's premises.
-/
import LeetQ.Rel.CRelRel
import LeetQ.Run.CRelRelDef
import LeetQ.Rel.CRelArith
import LeetQ.Run.CRelArithDef
import LeetQ.Rel.RepPerm
import LeetQ.Run.CRelListDef

namespace LeetQ.Rel

namespace Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF
open FoldN OpsN Prim Pow ListN

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
  exact rep_uncons X _ rfl _ rfl _ rfl (unconsC_fits X hb)

theorem rep_tailC {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (tailC X).2 = true) :
    ∀ (xs bs : List B.El), rep (tailC X).1 xs bs ↔ (∃ j, X.row j = xs) ∧ ∃ b, xs = b :: bs := by
  exact rep_tail X _ rfl _ rfl _ rfl (unconsC_fits X hb)

theorem rep_atPosC {B : Obj} {n : USize} (k : Nat) (X : Vals (.arr B) n) (hb : (atPosC k X).2 = true) :
    ∀ (xs : List B.El) x, rep (atPosC k X).1 xs x ↔ (∃ j, X.row j = xs) ∧ ∃ h : k < xs.length, x = xs[k]'h := by
  simp only [atPosC, okbit] at hb; exact rep_atPos k X hb.1 _ rfl _ rfl (pickFits_range _ X hb.2)

theorem rep_unsnocC {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (unsnocC X).2 = true) :
    ∀ (xs : List B.El) bs b, rep (unsnocC X).1 xs (bs, b) ↔ (∃ j, X.row j = xs) ∧ xs = bs ++ [b] :=
  rep_unsnoc X _ rfl _ rfl _ rfl (pickFits_range _ X hb)

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
  simp only [zipC, expand, need, okbit] at hb
  obtain ⟨⟨⟨ha, hb'⟩, hk⟩, hb⟩ := hb
  have hPa := pickFits_range _ _ ha; have hPb := pickFits_range _ _ hb'
  have hpa := (pickFits_payload _ hPa).1
  have hpb := (pickFits_payload _ hPb).1
  have hsum := len_expand_sum (n := P.n)
    (cnt := Kernel.Ew.val Ew.lesser Ew.i64 Ew.vv nul (slicesOf P.val.1).2 (slicesOf P.val.2).2 P.n) (len_val ..)
    fun t ht => by
      have := (slicesOf_row P.val.1 hpa ht).1; have := (slicesOf_row P.val.2 hpb ht).1
      rw [lesser_get ht (by omega) (by omega)]; omega
  split at hb
  · rename_i hx
    simp only [okbit] at hb
    rw [USize.toNat_ofNat_of_lt' hx, hsum] at hb
    rw [hsum] at hx
    exact ⟨hPa, hPb, hb, hx, pickFits_map_range _ _ _ hk⟩
  · exact absurd hb Bool.false_ne_true

theorem rep_zipC {K A B : Obj} (P : Rel K (.prod (.arr A) (.arr B))) (hb : (zipC P).2 = true) :
    ∀ k zs, rep (zipC P).1 k zs ↔ ∃ xs ys, rep P k (xs, ys) ∧ zs = List.zip xs ys := by
  obtain ⟨hPa, hPb, hS, hU, hk⟩ := zipC_ok P hb
  exact rep_zip P hPa hPb _ rfl hS hU _ rfl _ rfl _ rfl _ rfl _ rfl hk

/-- **`consC`'s bit is `rep_cons`'s premises** (`consOK`): the `fitsN` bits its `hV`, `hKf`; inside `expand`, the
    copies' count `k` plus the rows decided its `hS`, `need`'s guard its `hU` (`len_expand_slicesOf`), the raze's
    bit its `hRf` (`razeC_fits`), the last pick's its `hFf` (`pickC_fits`). -/
theorem consC_ok {K B : Obj} (P : Rel K (.prod B (.arr B))) (hb : (consC P).2 = true) : consOK(K, B, P) := by
  simp only [consC, expand, longCount, need, okbit] at hb
  obtain ⟨⟨hV, hK⟩, hb⟩ := hb
  have hVf := pickFits_range _ _ hV
  refine ⟨hVf, ?_⟩
  rintro s rfl
  split at hb
  · rename_i hx
    split at hb
    · rename_i hN
      split at hb
      · rename_i hp
        simp only [okbit] at hb
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
  exact rep_cons_ok P (consC_ok P hb)

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
  simp only [alphaC, okbit] at hb
  obtain ⟨hj, hcb⟩ := hb
  simp only [juncC, need] at hj
  split at hj
  · rename_i hN
    simp only [okbit] at hj
    exact rep_alpha I P hN hj.1 (Obj.razeC_fits (.arr B) _ _ _ (by rfl) _ hj.2) (consC_ok _ hcb)
  · exact absurd hj Bool.false_ne_true

/-- **`catC`'s bit is `rep_cat`'s premises** (`catOK`), as `consC_ok`: the two copies' counts `ka + kb` decided its
    `hS`, `need`'s guard its `hU`, each a side's counts summed (`len_expand_slicesOf`). -/
theorem catC_ok {K B : Obj} (P : Rel K (.prod (.arr B) (.arr B))) (hb : (catC P).2 = true) : catOK(K, B, P) := by
  simp only [catC, expand, longCount, need, okbit] at hb
  obtain ⟨⟨⟨ha, hb'⟩, hK⟩, hb⟩ := hb
  have hPa := pickFits_range _ _ ha; have hPb := pickFits_range _ _ hb'
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
          simp only [okbit] at hb
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
  exact rep_cat_ok P (catC_ok P hb)

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
  simp only [nestC, expand, need, okbit] at hb
  obtain ⟨⟨hp1, hK⟩, hb⟩ := hb
  split at hb
  · rename_i hx
    simp only [okbit] at hb
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
    exact ⟨h63, hx, pickFits_map_range _ X _ hK, fun _ => Vals.pickC_fits (.arr B) _ _ _ _ hv⟩
  · exact absurd hb Bool.false_ne_true

theorem rep_initsC {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (initsC X).2 = true) :
    ∀ xs yss, rep (initsC X).1 xs yss ↔ (∃ j, X.row j = xs) ∧
      yss = (List.range (xs.length + 1)).map fun k => xs.take k := by
  obtain ⟨hS, hU, hK, hV⟩ := nestC_bits X _ hb
  exact rep_inits X _ rfl hS hU _ rfl _ rfl _ rfl hK hV

theorem rep_tailsC {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (tailsC X).2 = true) :
    ∀ xs yss, rep (tailsC X).1 xs yss ↔ (∃ j, X.row j = xs) ∧
      yss = (List.range (xs.length + 1)).map fun k => xs.drop k := by
  obtain ⟨hS, hU, hK, hV⟩ := nestC_bits X _ hb
  exact rep_tails X _ rfl hS hU _ rfl _ rfl _ rfl hK hV

/-- **`nestMemC`'s bit is `nestC`'s, and the keys' pick fitting**: the two run the one `expand` with the one
    slice pick; `nestMemC` adds the keys' pick at the copies (`pickC_fits`). -/
theorem nestMemC_bits {B : Obj} {n : USize} (X : Vals (.arr B) n)
    (f : (m : USize) → ByteArray × ByteArray → (i r : ByteArray) → len i = m.toNat → Arr .long m × Arr .long m)
    (hb : (nestMemC X f).2 = true) :
    (nestC X f).2 = true ∧ Vals.PickFits (.arr B) X
      ((List.range (len (expandBytes 8 0 (tilLongs n) (addc n (slicesOf X).2 1))).toUSize.toNat).map fun q =>
        (Column.bitsAt (expandBytes 8 0 (tilLongs n) (addc n (slicesOf X).2 1)) (q * 8) 8).toNat) := by
  simp only [nestMemC, expand, need, okbit] at hb
  obtain ⟨⟨hp1, hK⟩, hb⟩ := hb
  split at hb
  · rename_i hx
    simp only [okbit] at hb
    obtain ⟨⟨h63, hv⟩, hk⟩ := hb
    refine ⟨?_, Vals.pickC_fits (.arr B) X _ _ _ hk⟩
    simp only [nestC, expand, need, okbit, hp1, hK, hx, h63, hv, dite_true, Bool.and_self, decide_true]
  · exact absurd hb Bool.false_ne_true

/-- **`prefix` under `prefixC`'s bit**: an array `xs` of `X` goes to exactly its prefixes, B&dM's
    `prefix = ⦇[nil, nil ∪ cons]⦈` (p.126): `rep_prefix` at `nestMemC_bits`' and `nestC_bits`' premises. -/
theorem rep_prefixC {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (prefixC X).2 = true) :
    ∀ xs ys, rep (prefixC X).1 xs ys ↔ (∃ j, X.row j = xs) ∧ ys <+: xs := by
  obtain ⟨hn, hk⟩ := nestMemC_bits X _ hb
  obtain ⟨hS, hU, hK, hV⟩ := nestC_bits X _ hn
  exact rep_prefix X _ rfl hS hU _ rfl _ rfl _ rfl hK hV hk

/-- **`suffix` under `suffixC`'s bit**: an array `xs` of `X` goes to exactly its suffixes (B&dM p.127):
    `rep_suffix` at `nestMemC_bits`' and `nestC_bits`' premises. -/
theorem rep_suffixC {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (suffixC X).2 = true) :
    ∀ xs ys, rep (suffixC X).1 xs ys ↔ (∃ j, X.row j = xs) ∧ ys <:+ xs := by
  obtain ⟨hn, hk⟩ := nestMemC_bits X _ hb
  obtain ⟨hS, hU, hK, hV⟩ := nestC_bits X _ hn
  exact rep_suffix X _ rfl hS hU _ rfl _ rfl _ rfl hK hV hk

/-- `compC_ok` in `cmpOK`'s form, the codes bound by their equation. -/
theorem compC_cmpOK {A B C : Obj} (R : Rel A B) (S : Rel B C) (hb : (compC R S).2 = true) : cmpOK(B, R, S) := by
  obtain ⟨hcf, h⟩ := compC_ok R S hb
  exact ⟨hcf, fun _ e => by subst e; exact h⟩

/-- **`rep (uncat X)` under `uncatC`'s bit**: `rep_uncat` at its pieces' premises, each read off that piece's bit —
    `nestC_bits` at `inits`, `tails`, `pairC_ok`, `zipC_ok`, `memC_ok`, `compC_ok`. -/
theorem rep_uncatC {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (uncatC X).2 = true) :
    ∀ xs ys zs, rep (uncatC X).1 xs (ys, zs) ↔ (∃ j, X.row j = xs) ∧ xs = ys ++ zs := by
  simp only [uncatC, okbit] at hb
  obtain ⟨⟨⟨⟨⟨hi, ht⟩, hp⟩, hz⟩, hv⟩, hc⟩ := hb
  obtain ⟨hS, hU, hK, hVi⟩ := nestC_bits X _ hi
  obtain ⟨-, -, -, hVt⟩ := nestC_bits X _ ht
  obtain ⟨hkf, hk1⟩ := pairC_ok _ _ hp
  obtain ⟨hkn, hkM, hkA, hkB, hkC⟩ := hk1 _ rfl
  obtain ⟨-, -, hS', hU', -⟩ := zipC_ok _ hz
  obtain ⟨hmv, hmk⟩ := memC_ok _ hv
  obtain ⟨hjf, hjn, hjM, hjA, hjC⟩ := compC_ok _ _ hc
  exact rep_uncat X _ rfl hS hU _ rfl _ rfl _ rfl hK hVi hVt _ rfl (codes_faithful_wf _ _ hkf).1 hkn hkM hkA hkB
    hkC _ rfl _ rfl hS' hU' _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl (codes_faithful_wf _ _ hjf).1 hjn hjM hjA hjC
    hmv hmk

/-- **`rep (snoc P)` under `snocC`'s bit**: `rep_snoc` at `snocOK`, each piece's premises read off its bit —
    `ranC`'s codes and `fitsN` bits (`oneFit`), `transposeC`'s at `idU` (`tauOK`), `compC_cmpOK`, `pairC_ok`,
    `catC_ok`. -/
theorem rep_snocC {K B : Obj} (P : Rel K (.prod (.arr B) B)) (hb : (snocC P).2 = true) :
    ∀ k ys, rep (snocC P).1 k ys ↔ ∃ bs b, rep P k (bs, b) ∧ ys = bs ++ [b] := by
  simp only [snocC, okbit] at hb
  obtain ⟨⟨⟨⟨⟨hD, ht⟩, hT⟩, hQ⟩, hM⟩, hr⟩ := hb
  have eD : (ranC P).1 = ran P := rfl
  rw [eD] at ht hT hQ hM hr
  simp only [ranC, distinctCoreflC, okbit] at hD
  obtain ⟨hK1, -, hk1, -, hWk, hW, h63⟩ := transposeC_ok _ ht
  apply rep_snoc P
  refine ⟨⟨Obj.codesC_fits _ _ hD.1, pickFits_range _ _ hD.2⟩, ?_⟩
  rintro D rfl X rfl
  refine ⟨⟨hK1, hk1, hWk, hW, h63⟩, compC_cmpOK _ _ hT, ?_⟩
  rintro T rfl
  refine ⟨pairC_ok _ _ hQ, ?_⟩
  rintro Q rfl
  refine ⟨compC_cmpOK _ _ hM, ?_⟩
  rintro M rfl
  exact catC_ok _ hr

/-- **`gather 8 src idx` misses**: long `j` reads `0` where its index is past `src`'s count. -/
theorem gather8_miss {src idx : ByteArray} {j : Nat} (hj : j < len idx)
    (hs : len src ≤ (Column.bitsAt idx (j * 8) 8).toNat) : Column.bitsAt (gather 8 src idx) (j * 8) 8 = 0 := by
  have h8 : (Nat.toUSize 8).toNat = 8 := KernelWF.toNat_small 8 (by decide)
  have h := (gatherBytes_spec (Nat.toUSize 8) (by rw [h8]; decide) 0 src idx).2 j (by simpa [len] using hj)
  rw [h8] at h
  unfold gather; rw [h, if_neg (by simp only [len] at hs; omega)]; rfl

/-- **Windows laid end to end flatten to one**: the window of `t` is `[S t, S (t + 1))`, `S` rising over
    `[a, a + c]`. -/
theorem flatten_windows {α : Type} (S : Nat → Nat) (g : Nat → α) (a : Nat) : ∀ c,
    (∀ t, a ≤ t → t < a + c → S t ≤ S (t + 1)) → S a ≤ S (a + c) ∧
      ((List.range c).map fun j => (List.range (S (a + j + 1) - S (a + j))).map fun k => g (S (a + j) + k)).flatten =
        (List.range (S (a + c) - S a)).map fun k => g (S a + k)
  | 0, _ => ⟨Nat.le_refl _, by simp⟩
  | c + 1, h => by
    obtain ⟨hle, ih⟩ := flatten_windows S g a c fun t h1 h2 => h t h1 (by omega)
    have hs := h (a + c) (by omega) (by omega)
    rw [show a + (c + 1) = a + c + 1 from rfl]
    refine ⟨Nat.le_trans hle hs, ?_⟩
    rw [List.range_succ, List.map_append, List.flatten_append, ih, List.map_singleton, List.flatten_singleton,
      show S (a + c + 1) - S a = (S (a + c) - S a) + (S (a + c + 1) - S (a + c)) by omega, List.range_add,
      List.map_append, List.map_map]
    congr 1
    apply List.map_congr_left; intro k _; simp only [Function.comp_apply]; congr 1; omega

/-- **`concat` under `concatC`'s bit**: an array of arrays `xss` of `X` goes to `xss.flatten`, B&dM's
    `concat = ⦇[nil, cat]⦈` (p.129), the prelude's `⦇ran(nil), cat⦈`. The compacted inner arrays lie end to end
    (`pick_row_arr`'s `S`), so outer row `i`, inner arrays `[a, a + c)` (`slicesOf_row`), is `[S a, S (a + c))`
    (`flatten_windows`), each end gathered at the index one before (`gather8_get`, `gather8_miss` at `-1`). -/
theorem rep_concatC {B : Obj} {n : USize} (X : Vals (.arr (.arr B)) n) (hb : (concatC X).2 = true) :
    ∀ xss ys, rep (concatC X).1 xss ys ↔ (∃ j, X.row j = xss) ∧ ys = xss.flatten := by
  obtain ⟨m, lo, hi, Y⟩ := X
  simp only [concatC, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨hp, hz⟩ := hb
  have hf := Vals.pickC_fits (.arr B) Y (tilLongs m) m (len_tilLongs m) hz
  obtain ⟨⟨S, hS0, hSm, hS63, hSq⟩, hrow⟩ :=
    pick_row_arr Y (fun i m h hf q => pick_row B Y.2.2.2 i m h hf q) (tilLongs m) m (len_tilLongs m) hf
  have ez : (Vals.pickC (.arr B) Y (tilLongs m) m (len_tilLongs m)).1 =
    Vals.pick (.arr B) Y (tilLongs m) m (len_tilLongs m) := rfl
  generalize Vals.pick (.arr B) Y (tilLongs m) m (len_tilLongs m) = Z at hrow hSm hSq ez
  have mono : ∀ t ≤ m.toNat, S t ≤ S m.toNat := fun t ht => by
    have := (flatten_windows S (fun _ => ()) t (m.toNat - t) fun u _ h2 => (hSq ⟨u, by omega⟩).1).1
    rwa [Nat.add_sub_cancel' ht] at this
  have cl : ∀ x, x ≤ Z.1.toNat → min (max (x : Int) 0).toNat Z.1.toNat = x := fun x hx => by omega
  let g : Nat → B.El := fun k => if h : k < Z.1.toNat then Z.2.2.2.row ⟨k, h⟩ else B.dflt
  have hZrow : ∀ q : Fin m.toNat, Z.row q = (List.range (S (q + 1) - S q)).map fun k => g (S q + k) := fun q => by
    obtain ⟨-, hl, hh⟩ := hSq q
    rw [arr_row, hl, hh, cl _ (hSm ▸ mono _ (by omega)), cl _ (hSm ▸ mono _ q.2)]
  have hYZ : ∀ q : Fin m.toNat, Y.row q = Z.row q := fun q => by
    rw [hrow, dif_pos (by rw [tilLongs_get q.2]; exact q.2)]
    exact congrArg Y.row (Fin.ext (tilLongs_get q.2)).symm
  -- an end: the long `k[i]` (at most `m`) less one, gathered from `Z`'s `hi`, is `S k[i]`
  have hE : ∀ (k : ByteArray) (i : Fin n.toNat), (Column.bitsAt k (i.1 * 8) 8).toNat ≤ m.toNat →
      (Column.bitsAt (gather 8 (longsOf Z.2.2.1) (Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul k (one 1) n)) (i.1 * 8) 8
        ).toInt64.toInt = S (Column.bitsAt k (i.1 * 8) 8).toNat := fun k i hk => by
    have hm63 : m.toNat < 2 ^ 63 := hp
    have hv := val_va_get Ew.sub k (one 1) n i.2
    rw [bitsAt_one] at hv
    have hx := toInt64_toInt (x := Column.bitsAt k (i.1 * 8) 8) (by omega)
    have h1 := (valStep_int (x := Column.bitsAt k (i.1 * 8) 8) (y := 1) (by omega) (by decide)).2.1
      (by rw [hx]; decide) (by rw [hx]; omega)
    rw [← hv, hx, show (1 : UInt64).toInt64.toInt = 1 from rfl] at h1
    have hlen : i.1 < len (Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul k (one 1) n) := by rw [len_val]; exact i.2
    rcases Nat.eq_zero_or_pos (Column.bitsAt k (i.1 * 8) 8).toNat with h0 | hpos
    · rw [h0] at h1 ⊢
      have hu := u64_ext (v := UInt64.ofNat (2 ^ 64 - 1)) (h1.trans (by decide))
      rw [gather8_miss hlen (by rw [hu, len_longsOf]; have := hSm ▸ hS63; simp; omega), hS0]; rfl
    · have hu := u64_ext (v := UInt64.ofNat ((Column.bitsAt k (i.1 * 8) 8).toNat - 1))
        (h1.trans (by rw [toInt64_toInt (by rw [UInt64.toNat_ofNat_of_lt' (by omega)]; omega),
          UInt64.toNat_ofNat_of_lt' (by omega)]; omega))
      have hlt : (Column.bitsAt k (i.1 * 8) 8).toNat - 1 < m.toNat := by omega
      rw [gather8_get hlen (by rw [hu, len_longsOf, UInt64.toNat_ofNat_of_lt' (by omega)]; exact hlt), hu,
        UInt64.toNat_ofNat_of_lt' (by omega), longsOf_get _ hlt, Int64.toInt64_toUInt64,
        (hSq ⟨_, hlt⟩).2.1]
      congr 1; simp only; omega
  have key : ∀ i : Fin n.toNat, Vals.row (concatC ⟨m, lo, hi, Y⟩).1.val i =
      (Vals.row (A := .arr (.arr B)) ⟨m, lo, hi, Y⟩ i).flatten := fun i => by
    obtain ⟨hac, hlen, hel⟩ := slicesOf_row (⟨m, lo, hi, Y⟩ : Vals (.arr (.arr B)) n) hp i.2
    have hsum := add_get (n := n) (a := (slicesOf (⟨m, lo, hi, Y⟩ : Vals (.arr (.arr B)) n)).1)
      (b := (slicesOf (⟨m, lo, hi, Y⟩ : Vals (.arr (.arr B)) n)).2) i.2 (by have : m.toNat < 2 ^ 63 := hp; omega)
    have e1 := hE _ i (by omega)
    have e2 := hE _ i (by rw [hsum]; exact hac)
    rw [hsum] at e2
    generalize (Column.bitsAt (slicesOf (⟨m, lo, hi, Y⟩ : Vals (.arr (.arr B)) n)).1 (i.1 * 8) 8).toNat = a
      at hac hlen hel e1 e2
    generalize (Column.bitsAt (slicesOf (⟨m, lo, hi, Y⟩ : Vals (.arr (.arr B)) n)).2 (i.1 * 8) 8).toNat = c
      at hac hlen hel e1 e2
    have hX : Vals.row (A := .arr (.arr B)) ⟨m, lo, hi, Y⟩ i =
        (List.range c).map fun j => (List.range (S (a + j + 1) - S (a + j))).map fun k => g (S (a + j) + k) := by
      apply List.ext_getElem (by rw [hlen]; simp)
      intro j h1 h2
      rw [hel j h1 (by omega), List.getElem_map, List.getElem_range]
      exact (hYZ _).trans (hZrow _)
    rw [hX, (flatten_windows S g a c fun t h1 h2 => (hSq ⟨t, by omega⟩).1).2]
    simp only [concatC]
    rw [ez, arr_row, longsN_get, longsN_get, e1, e2, cl _ (hSm ▸ mono _ (by omega)), cl _ (hSm ▸ mono _ hac)]
  intro xss ys
  rw [rep_apply]
  constructor
  · rintro ⟨i, h1, h2⟩
    exact ⟨⟨i, h1⟩, h2 ▸ h1 ▸ key i⟩
  · rintro ⟨⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl, key i⟩

#print axioms rep_concatC
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

theorem rep_prefix (X : Vals (.arr B) n) (hb : («prefix» X).ok = true) :
    ∀ xs ys, rep («prefix» X).rel xs ys ↔ (∃ j, X.row j = xs) ∧ ys <+: xs :=
  rep_prefixC X hb

theorem rep_suffix (X : Vals (.arr B) n) (hb : (suffix X).ok = true) :
    ∀ xs ys, rep (suffix X).rel xs ys ↔ (∃ j, X.row j = xs) ∧ ys <:+ xs :=
  rep_suffixC X hb

theorem rep_concat (X : Vals (.arr (.arr B)) n) (hb : (concat X).ok = true) :
    ∀ xss ys, rep (concat X).rel xss ys ↔ (∃ j, X.row j = xss) ∧ ys = xss.flatten :=
  rep_concatC X hb

theorem rep_uncat (X : Vals (.arr B) n) (hb : (uncat X).ok = true) :
    ∀ xs ys zs, rep (uncat X).rel xs (ys, zs) ↔ (∃ j, X.row j = xs) ∧ xs = ys ++ zs :=
  rep_uncatC X hb

theorem rep_cons (P : CRel K (.prod B (.arr B))) (hb : (cons P).ok = true) :
    ∀ k ys, rep (cons P).rel k ys ↔ ∃ b bs, rep P.rel k (b, bs) ∧ ys = b :: bs := by
  have e : cons P = _ := guard_eq ok hb; rw [e] at hb ⊢; exact rep_consC P.rel hb

theorem rep_cat (P : CRel K (.prod (.arr B) (.arr B))) (hb : (cat P).ok = true) :
    ∀ k zs, rep (cat P).rel k zs ↔ ∃ xs ys, rep P.rel k (xs, ys) ∧ zs = xs ++ ys := by
  have e : cat P = _ := guard_eq ok hb; rw [e] at hb ⊢; exact rep_catC P.rel hb

theorem rep_snoc (P : CRel K (.prod (.arr B) B)) (hb : (snoc P).ok = true) :
    ∀ k ys, rep (snoc P).rel k ys ↔ ∃ bs b, rep P.rel k (bs, b) ∧ ys = bs ++ [b] := by
  have e : snoc P = _ := guard_eq ok hb; rw [e] at hb ⊢; exact rep_snocC P.rel hb

theorem rep_zip (P : CRel K (.prod (.arr A) (.arr B))) (hb : (zip P).ok = true) :
    ∀ k zs, rep (zip P).rel k zs ↔ ∃ xs ys, rep P.rel k (xs, ys) ∧ zs = List.zip xs ys := by
  have e : zip P = _ := guard_eq ok hb; rw [e] at hb ⊢; exact rep_zipC P.rel hb

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
