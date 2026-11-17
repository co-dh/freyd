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

open LeetQ.Core.Rel hiding id comp recip inter union zero le inl inr junc in
/-- **`rep (α)` under `alphaC`'s bit**: `need`'s guard is `rep_alpha`'s `hN`, the decided bound its `h63`, the
    raze's bit its `hF` (`razeC_fits`), `consC`'s bit its `hc` (`consC_ok`). -/
theorem rep_alphaC {K B : Obj} {n : USize} (I : Vals K 1) (P : Vals (.prod B (.arr B)) n)
    (hb : (alphaC I P).2 = true) :
    rep (alphaC I P).1 = Core.Rel.junc
      (corefl (α := K.El) (fun u => ∃ i, I.row i = u) ≫
        (graph (fun _ => []) :Core.Rel (K.El) (List B.El)))
      (corefl (α := B.El × List B.El) (fun p => ∃ i, P.row i = p) ≫
        (graph (fun p => p.1 :: p.2) :Core.Rel (B.El × List B.El) (List B.El))) := by
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
    `concat = ⦇[nil, cat]⦈` (p.129). The compacted inner arrays lie end to end
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
    congr 1; exact Fin.ext (tilLongs_get q.2).symm
  -- an end: the long `k[i]` (at most `m`) less one, gathered from `Z`'s `hi`, is `S k[i]`
  have hE : ∀ (k : ByteArray) (i : Fin n.toNat), (Column.bitsAt k (i.1 * 8) 8).toNat ≤ m.toNat →
      (Column.bitsAt (gather 8 (longsOf Z.2.2.1) (Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul k (one 1) n)) (i.1 * 8) 8
        ).toInt64.toInt = S (Column.bitsAt k (i.1 * 8) 8).toNat := fun k i hk => by
    have hm63 : m.toNat < 2 ^ 63 := hp
    have hsz : UInt64.size = 2 ^ 64 := rfl
    have h1' : (1 : UInt64).toInt64.toInt = 1 := rfl
    have hv := val_va_get Ew.sub k (one 1) n i.2
    rw [bitsAt_one] at hv
    have hx := toInt64_toInt (x := Column.bitsAt k (i.1 * 8) 8) (by omega)
    have h1 := (valStep_int (x := Column.bitsAt k (i.1 * 8) 8) (y := 1) (by rw [hx]; omega) (by rw [h1']; decide)).2.1
      (by rw [hx, h1']; omega) (by rw [hx, h1']; omega)
    rw [← hv, hx, h1'] at h1
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
        (hSq ⟨_, hlt⟩).2.2]
      simp only [Nat.sub_add_cancel hpos]
  have key : ∀ i : Fin n.toNat, Vals.row (concatC ⟨m, lo, hi, Y⟩).1.val i =
      (Vals.row (A := .arr (.arr B)) ⟨m, lo, hi, Y⟩ i).flatten := fun i => by
    obtain ⟨hac, hlen, hel⟩ := slicesOf_row (⟨m, lo, hi, Y⟩ : Vals (.arr (.arr B)) n) hp i.2
    change _ + _ ≤ m.toNat at hac
    have hsum := add_get (n := n) (a := (slicesOf (⟨m, lo, hi, Y⟩ : Vals (.arr (.arr B)) n)).1)
      (b := (slicesOf (⟨m, lo, hi, Y⟩ : Vals (.arr (.arr B)) n)).2) i.2 (by have : m.toNat < 2 ^ 63 := hp; omega)
    have e1 := hE (slicesOf (⟨m, lo, hi, Y⟩ : Vals (.arr (.arr B)) n)).1 i (by omega)
    have e2 := hE (add n (slicesOf (⟨m, lo, hi, Y⟩ : Vals (.arr (.arr B)) n)).1
      (slicesOf (⟨m, lo, hi, Y⟩ : Vals (.arr (.arr B)) n)).2) i (by rw [hsum]; exact hac)
    rw [hsum] at e2
    generalize (Column.bitsAt (slicesOf (⟨m, lo, hi, Y⟩ : Vals (.arr (.arr B)) n)).1 (i.1 * 8) 8).toNat = a
      at hac hlen hel e1 e2
    generalize (Column.bitsAt (slicesOf (⟨m, lo, hi, Y⟩ : Vals (.arr (.arr B)) n)).2 (i.1 * 8) 8).toNat = c
      at hac hlen hel e1 e2
    have hX : Vals.row (A := .arr (.arr B)) ⟨m, lo, hi, Y⟩ i =
        (List.range c).map fun j => (List.range (S (a + j + 1) - S (a + j))).map fun k => g (S (a + j) + k) := by
      apply List.ext_getElem (by rw [hlen]; simp)
      intro j h1 h2
      have hjc : j < c := by rw [← hlen]; exact h1
      rw [hel j h1 (by show a + j < m.toNat; omega), List.getElem_map, List.getElem_range]
      exact (hYZ _).trans (hZrow _)
    rw [hX, (flatten_windows S g a c fun t h1 h2 => (hSq ⟨t, by omega⟩).1).2]
    simp only [concatC]
    rw [arr_row]; dsimp only
    rw [longsN_get, longsN_get, ez, e1, e2, cl _ (hSm ▸ mono _ (by omega)), cl _ (hSm ▸ mono _ hac)]
  intro xss ys
  rw [rep_apply]
  constructor
  · rintro ⟨i, h1, h2⟩
    exact ⟨⟨i, h1⟩, h2 ▸ h1 ▸ key i⟩
  · rintro ⟨⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl, key i⟩

/-! ### `filter(p)`, `takewhile(p)`: masks on the payload -/

/-- **`gatherT t src idx`'s long `j`**: `src`'s long `idx[j]` where that is below `src`'s count, else `t`. -/
theorem gatherT_get {t : Nat} (ht : t < 2 ^ 64) {src idx : ByteArray} {j : Nat} (hj : j < len idx) :
    (Column.bitsAt (gatherT t src idx) (j * 8) 8).toNat =
      if (Column.bitsAt idx (j * 8) 8).toNat < len src then
        (Column.bitsAt src ((Column.bitsAt idx (j * 8) 8).toNat * 8) 8).toNat else t := by
  have h8 : (Nat.toUSize 8).toNat = 8 := KernelWF.toNat_small 8 (by decide)
  have h := (gatherBytes_spec (Nat.toUSize 8) (by rw [h8]; decide) t.toUInt64 src idx).2 j (by simpa [len] using hj)
  rw [h8] at h
  unfold gatherT; rw [h]
  by_cases h1 : (Column.bitsAt idx (j * 8) 8).toNat < len src
  · rw [if_pos (by simpa [len] using h1), if_pos h1]
  · rw [if_neg (by simpa [len] using h1), if_neg h1]
    simp [Nat.mod_eq_of_lt ht]

/-- **`countBefore` read back**: at a position `p` up to the cell count `M`, the set bits of `b` below `p` — the
    position `M` misses the gather and reads the total `t`. -/
theorem countBefore_get {M : USize} (hM : M.toNat < 2 ^ 63) (b idx : ByteArray) {t : Nat}
    (ht : t = ((List.range M.toNat).filter (Column.bitAt b)).length) {j : Nat} (hj : j < len idx)
    (hp : (Column.bitsAt idx (j * 8) 8).toNat ≤ M.toNat) :
    (Column.bitsAt (countBefore M b t idx) (j * 8) 8).toNat =
      ((List.range (Column.bitsAt idx (j * 8) 8).toNat).filter (Column.bitAt b)).length := by
  have hl : len (sub M (sums M (Kernel.Ew.widen Ew.bits Ew.i64 nul nul b M))
      (Kernel.Ew.widen Ew.bits Ew.i64 nul nul b M)) = M.toNat := len_val ..
  have hf : t ≤ M.toNat := ht ▸ Nat.le_trans (List.length_filter_le _ _) (by simp)
  unfold countBefore; dsimp only
  rw [gatherT_get (by omega) hj, hl]
  split
  · exact rank_get b M hM ‹_›
  · rw [ht, show (Column.bitsAt idx (j * 8) 8).toNat = M.toNat by omega]

/-- **`keyBitsC`'s bit `k`**: set exactly when cell `k` of the payload is a key of `P`, the joint codes faithful
    (`codes_faithful_wf`, `member_bit`). -/
theorem keyBitsC_bit {B : Obj} {M : USize} (F : Vals B M) (P : Rel B B) (hb : (keyBitsC F P).2 = true) {k : Nat}
    (hk : k < M.toNat) : Column.bitAt (keyBitsC F P).1 k = true ↔ ∃ y, rep P (F.row ⟨k, hk⟩) y := by
  have hc := codes_faithful_wf B _ (Obj.codesC_fits B _ hb)
  obtain ⟨hw0, hn0, hs0, -⟩ := hc.1.2 (k := 0) (by decide)
  obtain ⟨hw1, hn1, hs1, -⟩ := hc.1.2 (k := 1) (by decide)
  simp only [keyBitsC]; rw [Obj.codesC_fst]
  rw [member_bit _ _ hw0 hw1 hs0 hs1 (by rw [hn0]; exact hk)]
  simp only [rep_apply, Rel.Holds]
  constructor
  · rintro ⟨j, hj, he⟩
    have hj' : j < P.n.toNat := by rw [hn1] at hj; exact hj
    exact ⟨P.val.row ⟨j, hj'⟩, ⟨j, hj'⟩, (hc.1.1 (k := 1) (l := 0) (by decide) (by decide) hj' hk).1 he, rfl⟩
  · rintro ⟨y, j, hj, -⟩
    exact ⟨j.1, by rw [hn1]; exact j.2, (hc.1.1 (k := 1) (l := 0) (by decide) (by decide) j.2 hk).2 hj⟩

/-- **A window's kept positions are a slice of all kept positions**: with `L` the positions below `M` that `m`
    keeps, those in `[a, a + c)` are `L`'s entries from the count kept below `a` to the count kept below `a + c`. -/
theorem filter_window (m : Nat → Bool) {a c M : Nat} (h : a + c ≤ M) :
    ((List.range c).map (a + ·)).filter m =
      (List.range (((List.range (a + c)).filter m).length - ((List.range a).filter m).length)).map fun j =>
        ((List.range M).filter m).getD (((List.range a).filter m).length + j) 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, M = a + c + r := ⟨M - a - c, by omega⟩
  have e1 : (List.range (a + c)).filter m = (List.range a).filter m ++ ((List.range c).map (a + ·)).filter m := by
    rw [List.range_add, List.filter_append]
  have e2 : (List.range (a + c + r)).filter m =
      ((List.range a).filter m ++ ((List.range c).map (a + ·)).filter m) ++
        ((List.range r).map (a + c + ·)).filter m := by
    rw [List.range_add, List.filter_append, e1]
  rw [e1, e2, List.length_append, Nat.add_sub_cancel_left]
  apply List.ext_getElem (by simp) fun j h1 h2 => ?_
  rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_append_left h1,
    List.getElem?_eq_getElem h1, Option.getD_some]

/-- The window `[a, a + c + 1)` is `a` before the window `[a + 1, a + 1 + c)`. -/
theorem range_succ_map (a c : Nat) : (List.range (c + 1)).map (a + ·) = a :: (List.range c).map (a + 1 + ·) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]; congr 1
  apply List.map_congr_left; intro k _; simp only [Function.comp_apply]; omega

/-- **The first position from `a` in `[a, a + r)` that `d` sets**, `a + r` if none: every position before it
    unset. -/
theorem first_set (d : Nat → Bool) : ∀ (r a : Nat),
    a ≤ (((List.range r).map (a + ·)).filter d).getD 0 (a + r) ∧
    (((List.range r).map (a + ·)).filter d).getD 0 (a + r) ≤ a + r ∧
    (∀ k, a ≤ k → k < (((List.range r).map (a + ·)).filter d).getD 0 (a + r) → d k = false) ∧
    ((((List.range r).map (a + ·)).filter d).getD 0 (a + r) < a + r →
      d ((((List.range r).map (a + ·)).filter d).getD 0 (a + r)) = true)
  | 0, a => by simp; intro k h1 h2; omega
  | r + 1, a => by
    rw [range_succ_map]
    cases hd : d a
    · rw [List.filter_cons_of_neg (by simp [hd])]
      obtain ⟨h1, h2, h3, h4⟩ := first_set d r (a + 1)
      rw [show a + 1 + r = a + (r + 1) by omega] at h1 h2 h3 h4
      refine ⟨by omega, h2, fun k hk hk' => ?_, h4⟩
      rcases Nat.eq_or_lt_of_le hk with rfl | hk
      · exact hd
      · exact h3 k hk hk'
    · rw [List.filter_cons_of_pos (by simp [hd])]
      simp only [List.getD_cons_zero]
      exact ⟨Nat.le_refl _, by omega, fun k h1 h2 => absurd h2 (by omega), fun _ => hd⟩

/-- **`takeWhile` on a window**: the positions from `a` before `e`, where every one in `[a, e)` passes `m` and `e`,
    inside the window, fails it. -/
theorem takeWhile_window (m : Nat → Bool) : ∀ (c : Nat) {a e : Nat}, a ≤ e → (∀ k, a ≤ k → k < e → m k = true) →
    (e < a + c → m e = false) →
    ((List.range c).map (a + ·)).takeWhile m = (List.range (min (a + c) e - a)).map (a + ·)
  | 0, a, e, hae, _, _ => by simp [show min a e - a = 0 by omega]
  | c + 1, a, e, hae, hk, he => by
    rw [range_succ_map]
    rcases Nat.eq_or_lt_of_le hae with rfl | hlt
    · rw [List.takeWhile_cons_of_neg (by simp [he (by omega)])]
      simp [show min (a + (c + 1)) a - a = 0 by omega]
    · rw [List.takeWhile_cons_of_pos (by simp [hk a (Nat.le_refl _) hlt]),
        takeWhile_window m c (a := a + 1) hlt (fun k h1 h2 => hk k (by omega) h2) (fun h => he (by omega)),
        show min (a + (c + 1)) e - a = (min (a + 1 + c) e - (a + 1)) + 1 by omega, range_succ_map]

/-- The positions below `a` that `m` keeps are no more than those below `b ≥ a`. -/
theorem filter_range_le (m : Nat → Bool) {a b : Nat} (h : a ≤ b) :
    ((List.range a).filter m).length ≤ ((List.range b).filter m).length :=
  ((List.range_sublist.2 h).filter m).length_le

/-- An array row read at its slice `[a, a + c)`: the payload's cells there, a cell past the payload `dflt`. -/
theorem row_window {B : Obj} {n : USize} (X : Vals (.arr B) n) (hp : X.1.toNat < 2 ^ 63) {i : Nat}
    (hi : i < n.toNat) :
    Vals.row X ⟨i, hi⟩ = (List.range (Column.bitsAt (slicesOf X).2 (i * 8) 8).toNat).map fun j =>
      if h : (Column.bitsAt (slicesOf X).1 (i * 8) 8).toNat + j < X.1.toNat then
        Vals.row X.2.2.2 ⟨_, h⟩ else B.dflt := by
  obtain ⟨hac, hlen, hel⟩ := slicesOf_row X hp hi
  apply List.ext_getElem (by rw [hlen]; simp)
  intro j h1 h2
  rw [hel j h1 (by omega), List.getElem_map, List.getElem_range, dif_pos (by omega)]

/-- A relation keyed by the arrays `X`, row `i` valued `φ` of array `i`: each array of `X` goes to its `φ`. -/
theorem rep_rowwise {B C : Obj} {n : USize} (X : Vals (.arr B) n) (V : Vals C n) (φ : List B.El → C.El)
    (h : ∀ i, V.row i = φ (X.row i)) :
    ∀ xs ys, rep (⟨n, X, V⟩ : Rel (.arr B) C) xs ys ↔ (∃ j, X.row j = xs) ∧ ys = φ xs := by
  intro xs ys; rw [rep_apply]
  constructor
  · rintro ⟨i, h1, h2⟩; exact ⟨⟨i, h1⟩, h2 ▸ h1 ▸ h i⟩
  · rintro ⟨⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl, h i⟩

open Classical in
/-- **`filter(p)` under `filterC`'s bit**: an array `xs` of `X` goes to its cells that are keys of `P`, in order
    (B&dM p.66, `filter p = ⦇[nil, p outl → cons, outr]⦈`). The mask is `keyBitsC_bit`, the kept cells `L`
    (`whereBits_ids`); a row `[a, a + c)` is `L` between the counts kept below `a` and below `a + c`
    (`countBefore_get`, `filter_window`), each picked from the payload (`pick_row`). -/
theorem rep_filterC {B : Obj} {n : USize} (P : Rel B B) (X : Vals (.arr B) n) (hb : (filterC P X).2 = true) :
    ∀ xs ys, rep (filterC P X).1 xs ys ↔ (∃ j, X.row j = xs) ∧ ys = xs.filter fun x => decide (∃ y, rep P x y) := by
  obtain ⟨M, lo, hi, F⟩ := X
  have hb' := hb
  simp only [filterC, need] at hb'
  split at hb'
  case isFalse => exact absurd hb' Bool.false_ne_true
  rename_i hK
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb'
  obtain ⟨⟨⟨hk, hp⟩, -⟩, hv⟩ := hb'
  have hbit : ∀ k (h : k < M.toNat), Column.bitAt (keyBitsC F P).1 k = decide (∃ y, rep P (F.row ⟨k, h⟩) y) :=
    fun k h => by rw [Bool.eq_iff_iff, decide_eq_true_iff]; exact keyBitsC_bit F P hk h
  obtain ⟨hids, -, -⟩ := whereBits_ids M (keyBitsC F P).1
  have hlenK : len (whereBits M (keyBitsC F P).1) =
      ((List.range M.toNat).filter (Column.bitAt (keyBitsC F P).1)).length := by
    rw [← hids]; simp [ids, len]
  have hKs : (len (whereBits M (keyBitsC F P).1)).toUSize.toNat = len (whereBits M (keyBitsC F P).1) :=
    USize.toNat_ofNat_of_lt' hK
  have hpick := pick_row B F _ (len (whereBits M (keyBitsC F P).1)).toUSize hKs.symm (Vals.pickC_fits B F _ _ _ hv)
  simp only [filterC, need]; rw [dif_pos hK]
  dsimp only; intro xs ys
  refine rep_rowwise (C := .arr B) _ _ (fun xs => xs.filter fun x => decide (∃ y, rep P x y)) ?_ xs ys
  · intro i
    have hac := (slicesOf_row (⟨M, lo, hi, F⟩ : Vals (.arr B) n) hp i.2).1
    have hsum := add_get (n := n) (a := (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).1)
      (b := (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).2) i.2 (by change _ ≤ M.toNat at hac; omega)
    have hlo := countBefore_get hp (keyBitsC F P).1 (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).1 hlenK
      (Nat.lt_of_lt_of_le i.2 (Nat.le_of_eq (len_slices ..).1.symm)) (by change _ ≤ M.toNat at hac; omega)
    have hhi := countBefore_get hp (keyBitsC F P).1 (add n (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).1
      (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).2) hlenK
      (Nat.lt_of_lt_of_le i.2 (Nat.le_of_eq (len_val ..).symm)) (by rw [hsum]; exact hac)
    rw [hsum] at hhi
    rw [row_window (⟨M, lo, hi, F⟩ : Vals (.arr B) n) hp i.2, arr_row]; dsimp only
    rw [longsN_get, longsN_get]
    generalize (Column.bitsAt (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).1 (i.1 * 8) 8).toNat = a at hac hlo hhi ⊢
    generalize (Column.bitsAt (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).2 (i.1 * 8) 8).toNat = c at hac hhi ⊢
    change a + c ≤ M.toNat at hac
    have hA : ((List.range a).filter (Column.bitAt (keyBitsC F P).1)).length ≤ a :=
      Nat.le_trans (List.length_filter_le _ _) (by simp)
    have hAC := filter_range_le (Column.bitAt (keyBitsC F P).1) (Nat.le_add_right a c)
    have hCL := filter_range_le (Column.bitAt (keyBitsC F P).1) hac
    have hC : ((List.range (a + c)).filter (Column.bitAt (keyBitsC F P).1)).length ≤ a + c :=
      Nat.le_trans (List.length_filter_le _ _) (by simp)
    rw [toInt64_toInt (by rw [hlo]; omega), toInt64_toInt (by rw [hhi]; omega), hlo, hhi,
      show min (max (((List.range a).filter (Column.bitAt (keyBitsC F P).1)).length : Int) 0).toNat
        (len (whereBits M (keyBitsC F P).1)).toUSize.toNat =
        ((List.range a).filter (Column.bitAt (keyBitsC F P).1)).length by rw [hKs]; omega,
      show min (max (((List.range (a + c)).filter (Column.bitAt (keyBitsC F P).1)).length : Int) 0).toNat
        (len (whereBits M (keyBitsC F P).1)).toUSize.toNat =
        ((List.range (a + c)).filter (Column.bitAt (keyBitsC F P).1)).length by rw [hKs]; omega]
    rw [show ((List.range c).map fun j => if h : a + j < M.toNat then F.row ⟨a + j, h⟩ else B.dflt) =
        ((List.range c).map (a + ·)).map fun k => if h : k < M.toNat then F.row ⟨k, h⟩ else B.dflt by
          rw [List.map_map]; rfl,
      List.filter_map, show ((List.range c).map (a + ·)).filter ((fun x => decide (∃ y, rep P x y)) ∘
          fun k => if h : k < M.toNat then F.row ⟨k, h⟩ else B.dflt) =
          ((List.range c).map (a + ·)).filter (Column.bitAt (keyBitsC F P).1) from List.filter_congr fun k hk => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hk
        have h : a + j < M.toNat := by rw [List.mem_range] at hj; omega
        simp only [Function.comp_apply, dif_pos h]; exact (hbit _ h).symm,
      filter_window _ hac, List.map_map]
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    have hj' : ((List.range a).filter (Column.bitAt (keyBitsC F P).1)).length + j < ((List.range M.toNat).filter (Column.bitAt (keyBitsC F P).1)).length := by omega
    rw [dif_pos (by rw [hKs, hlenK]; exact hj'), pickC_fst]
    rw [hpick, dif_pos (by rw [ids_get hids hj']; exact
      (List.mem_range.1 (List.mem_filter.1 (List.getElem_mem hj')).1))]
    simp only [Function.comp_apply, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
    rw [dif_pos (List.mem_range.1 (List.mem_filter.1 (List.getElem_mem hj')).1)]
    exact congrArg F.row (Fin.ext (ids_get hids hj'))

open Classical in
/-- **`takewhile(p)` under `takewhileC`'s bit**: an array `xs` of `X` goes to its longest prefix of keys of `P`
    (B&dM p.174, `takewhile p = ⦇[nil, p outl → cons, nil]⦈`). The failing cells `L` (`notBits`, `whereBits_ids`)
    read at the count failing below a row's start `a` give the first failing cell `e` from `a` (`first_set`), the
    row's end the lesser of `e` and its own (`lesser_get`, `takeWhile_window`). -/
theorem rep_takewhileC {B : Obj} {n : USize} (P : Rel B B) (X : Vals (.arr B) n) (hb : (takewhileC P X).2 = true) :
    ∀ xs ys, rep (takewhileC P X).1 xs ys ↔
      (∃ j, X.row j = xs) ∧ ys = xs.takeWhile fun x => decide (∃ y, rep P x y) := by
  obtain ⟨M, lo, hi, F⟩ := X
  have hb' := hb
  simp only [takewhileC, Bool.and_eq_true, decide_eq_true_eq] at hb'
  obtain ⟨⟨hk, hp⟩, -⟩ := hb'
  have hbit : ∀ k (h : k < M.toNat), Column.bitAt (keyBitsC F P).1 k = decide (∃ y, rep P (F.row ⟨k, h⟩) y) :=
    fun k h => by rw [Bool.eq_iff_iff, decide_eq_true_iff]; exact keyBitsC_bit F P hk h
  have hfb : ∀ k < M.toNat, Column.bitAt (Ew.notBits M (keyBitsC F P).1) k = !Column.bitAt (keyBitsC F P).1 k :=
    fun k h => notBits_bitAt _ _ h
  obtain ⟨hids, -, -⟩ := whereBits_ids M (Ew.notBits M (keyBitsC F P).1)
  have hlenF : len (whereBits M (Ew.notBits M (keyBitsC F P).1)) =
      ((List.range M.toNat).filter (Column.bitAt (Ew.notBits M (keyBitsC F P).1))).length := by
    rw [← hids]; simp [ids, len]
  simp only [takewhileC]
  intro xs ys
  refine rep_rowwise (C := .arr B) _ _ (fun xs => xs.takeWhile fun x => decide (∃ y, rep P x y)) ?_ xs ys
  · intro i
    have hac := (slicesOf_row (⟨M, lo, hi, F⟩ : Vals (.arr B) n) hp i.2).1
    have hsum := add_get (n := n) (a := (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).1)
      (b := (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).2) i.2 (by change _ ≤ M.toNat at hac; omega)
    have hs1 : i.1 < len (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).1 :=
      Nat.lt_of_lt_of_le i.2 (Nat.le_of_eq (len_slices ..).1.symm)
    have hlo := countBefore_get hp (Ew.notBits M (keyBitsC F P).1) _ hlenF hs1 (by change _ ≤ M.toNat at hac; omega)
    have hcb : i.1 < len (countBefore M (Ew.notBits M (keyBitsC F P).1)
        (len (whereBits M (Ew.notBits M (keyBitsC F P).1))) (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).1) := by
      unfold countBefore; dsimp only; rw [len_gatherT]; exact hs1
    have he := gatherT_get (t := M.toNat) (src := whereBits M (Ew.notBits M (keyBitsC F P).1)) (by omega) hcb
    rw [hlo] at he
    rw [row_window (⟨M, lo, hi, F⟩ : Vals (.arr B) n) hp i.2, arr_row]; dsimp only
    rw [longsN_get, longsN_get, toInt64_toInt (x := Column.bitsAt (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).1
      (i.1 * 8) 8) (by change _ ≤ M.toNat at hac; omega)]
    generalize (Column.bitsAt (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).1 (i.1 * 8) 8).toNat = a at hac hlo he hsum ⊢
    generalize (Column.bitsAt (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).2 (i.1 * 8) 8).toNat = c at hac hsum ⊢
    change a + c ≤ M.toNat at hac
    -- the first failing cell from `a`
    obtain ⟨r, hr⟩ : ∃ r, M.toNat = a + r := ⟨M.toNat - a, by omega⟩
    obtain ⟨e1, e2, e3, e4⟩ := first_set (Column.bitAt (Ew.notBits M (keyBitsC F P).1)) r a
    have hL : (List.range M.toNat).filter (Column.bitAt (Ew.notBits M (keyBitsC F P).1)) =
        (List.range a).filter (Column.bitAt (Ew.notBits M (keyBitsC F P).1)) ++
          ((List.range r).map (a + ·)).filter (Column.bitAt (Ew.notBits M (keyBitsC F P).1)) := by
      rw [hr, List.range_add, List.filter_append]
    have hE : (Column.bitsAt (gatherT M.toNat (whereBits M (Ew.notBits M (keyBitsC F P).1))
        (countBefore M (Ew.notBits M (keyBitsC F P).1) (len (whereBits M (Ew.notBits M (keyBitsC F P).1)))
          (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).1)) (i.1 * 8) 8).toNat =
        (((List.range r).map (a + ·)).filter (Column.bitAt (Ew.notBits M (keyBitsC F P).1))).getD 0 (a + r) := by
      rw [he, hlenF, hL, List.length_append]
      split
      · rename_i h
        rw [ids_get hids (by rw [hL, List.length_append]; exact h)]
        simp only [hL, List.getElem_append_right (Nat.le_refl _), Nat.sub_self]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none, hr]
    generalize (((List.range r).map (a + ·)).filter (Column.bitAt (Ew.notBits M (keyBitsC F P).1))).getD 0
      (a + r) = e at e1 e2 e3 e4 hE
    rw [← hr] at e2 e4
    have hmin := lesser_get (n := n) (a := add n (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).1
      (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).2) (b := gatherT M.toNat
        (whereBits M (Ew.notBits M (keyBitsC F P).1)) (countBefore M (Ew.notBits M (keyBitsC F P).1)
          (len (whereBits M (Ew.notBits M (keyBitsC F P).1))) (slicesOf (⟨M, lo, hi, F⟩ : Vals (.arr B) n)).1))
      i.2 (by rw [hsum]; omega) (by rw [hE]; omega)
    rw [hsum, hE] at hmin
    rw [toInt64_toInt (by rw [hmin]; omega), hmin,
      show min (max ((a : Nat) : Int) 0).toNat M.toNat = a by omega,
      show min (max ((min (a + c) e : Nat) : Int) 0).toNat M.toNat = min (a + c) e by omega]
    rw [show ((List.range c).map fun j => if h : a + j < M.toNat then F.row ⟨a + j, h⟩ else B.dflt) =
        ((List.range c).map (a + ·)).map fun k => if h : k < M.toNat then F.row ⟨k, h⟩ else B.dflt by
          rw [List.map_map]; rfl,
      List.takeWhile_map,
      takeWhile_window _ c e1 (fun k h1 h2 => by
          have h : k < M.toNat := by omega
          simp only [Function.comp_apply, dif_pos h, ← hbit k h]
          have := e3 k h1 h2; rw [hfb k h] at this; simpa using this)
        (fun h => by
          have h' : e < M.toNat := by omega
          simp only [Function.comp_apply, dif_pos h', ← hbit e h']
          have := e4 h'; rw [hfb e h'] at this; simpa using this),
      List.map_map]
    rfl

#print axioms rep_filterC
#print axioms rep_takewhileC
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
  by unfold CRel.uncons at hb ⊢; rw [rep_ofC hb]; exact rep_unconsC X (ofC_ok hb).1

theorem rep_tail (X : Vals (.arr B) n) (hb : (tail X).ok = true) :
    ∀ (xs bs : List B.El), rep (tail X).rel xs bs ↔ (∃ j, X.row j = xs) ∧ ∃ b, xs = b :: bs :=
  by unfold CRel.tail at hb ⊢; rw [rep_ofC hb]; exact rep_tailC X (ofC_ok hb).1

theorem rep_atPos (k : Nat) (X : Vals (.arr B) n) (hb : (atPos k X).ok = true) :
    ∀ (xs : List B.El) x, rep (atPos k X).rel xs x ↔ (∃ j, X.row j = xs) ∧ ∃ h : k < xs.length, x = xs[k]'h :=
  by unfold CRel.atPos at hb ⊢; rw [rep_ofC hb]; exact rep_atPosC k X (ofC_ok hb).1

theorem rep_unsnoc (X : Vals (.arr B) n) (hb : (unsnoc X).ok = true) :
    ∀ (xs : List B.El) bs b, rep (unsnoc X).rel xs (bs, b) ↔ (∃ j, X.row j = xs) ∧ xs = bs ++ [b] :=
  by unfold CRel.unsnoc at hb ⊢; rw [rep_ofC hb]; exact rep_unsnocC X (ofC_ok hb).1

theorem rep_inits (X : Vals (.arr B) n) (hb : (inits X).ok = true) :
    ∀ xs yss, rep (inits X).rel xs yss ↔ (∃ j, X.row j = xs) ∧
      yss = (List.range (xs.length + 1)).map fun k => xs.take k :=
  by unfold CRel.inits at hb ⊢; rw [rep_ofC hb]; exact rep_initsC X (ofC_ok hb).1

theorem rep_tails (X : Vals (.arr B) n) (hb : (tails X).ok = true) :
    ∀ xs yss, rep (tails X).rel xs yss ↔ (∃ j, X.row j = xs) ∧
      yss = (List.range (xs.length + 1)).map fun k => xs.drop k :=
  by unfold CRel.tails at hb ⊢; rw [rep_ofC hb]; exact rep_tailsC X (ofC_ok hb).1

theorem rep_prefix (X : Vals (.arr B) n) (hb : («prefix» X).ok = true) :
    ∀ xs ys, rep («prefix» X).rel xs ys ↔ (∃ j, X.row j = xs) ∧ ys <+: xs :=
  by unfold CRel.prefix at hb ⊢; rw [rep_ofC hb]; exact rep_prefixC X (ofC_ok hb).1

theorem rep_suffix (X : Vals (.arr B) n) (hb : (suffix X).ok = true) :
    ∀ xs ys, rep (suffix X).rel xs ys ↔ (∃ j, X.row j = xs) ∧ ys <:+ xs :=
  by unfold CRel.suffix at hb ⊢; rw [rep_ofC hb]; exact rep_suffixC X (ofC_ok hb).1

theorem rep_concat (X : Vals (.arr (.arr B)) n) (hb : (concat X).ok = true) :
    ∀ xss ys, rep (concat X).rel xss ys ↔ (∃ j, X.row j = xss) ∧ ys = xss.flatten :=
  by unfold CRel.concat at hb ⊢; rw [rep_ofC hb]; exact rep_concatC X (ofC_ok hb).1

theorem rep_uncat (X : Vals (.arr B) n) (hb : (uncat X).ok = true) :
    ∀ xs ys zs, rep (uncat X).rel xs (ys, zs) ↔ (∃ j, X.row j = xs) ∧ xs = ys ++ zs :=
  by unfold CRel.uncat at hb ⊢; rw [rep_ofC hb]; exact rep_uncatC X (ofC_ok hb).1

theorem rep_cons (P : CRel K (.prod B (.arr B))) (hb : (cons P).ok = true) :
    ∀ k ys, rep (cons P).rel k ys ↔ ∃ b bs, rep P.rel k (b, bs) ∧ ys = b :: bs := by
  have e : cons P = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_consC P.rel hb

theorem rep_cat (P : CRel K (.prod (.arr B) (.arr B))) (hb : (cat P).ok = true) :
    ∀ k zs, rep (cat P).rel k zs ↔ ∃ xs ys, rep P.rel k (xs, ys) ∧ zs = xs ++ ys := by
  have e : cat P = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_catC P.rel hb

theorem rep_snoc (P : CRel K (.prod (.arr B) B)) (hb : (snoc P).ok = true) :
    ∀ k ys, rep (snoc P).rel k ys ↔ ∃ bs b, rep P.rel k (bs, b) ∧ ys = bs ++ [b] := by
  have e : snoc P = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_snocC P.rel hb

theorem rep_zip (P : CRel K (.prod (.arr A) (.arr B))) (hb : (zip P).ok = true) :
    ∀ k zs, rep (zip P).rel k zs ↔ ∃ xs ys, rep P.rel k (xs, ys) ∧ zs = List.zip xs ys := by
  have e : zip P = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_zipC P.rel hb

open Classical in
theorem rep_filter (P : CRel B B) (X : Vals (.arr B) n) (hb : (filter P X).ok = true) :
    ∀ xs ys, rep (filter P X).rel xs ys ↔ (∃ j, X.row j = xs) ∧ ys = xs.filter fun x => decide (∃ y, rep P.rel x y) := by
  have e : filter P X = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_filterC P.rel X hb

open Classical in
theorem rep_takewhile (P : CRel B B) (X : Vals (.arr B) n) (hb : (takewhile P X).ok = true) :
    ∀ xs ys, rep (takewhile P X).rel xs ys ↔
      (∃ j, X.row j = xs) ∧ ys = xs.takeWhile fun x => decide (∃ y, rep P.rel x y) := by
  have e : takewhile P X = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_takewhileC P.rel X hb

open LeetQ.Core.Rel hiding id comp recip inter union zero le inl inr junc in
theorem rep_alpha (I : Vals K 1) (P : Vals (.prod B (.arr B)) n) (hb : (alpha I P).ok = true) :
    rep (alpha I P).rel = Core.Rel.junc
      (corefl (α := K.El) (fun u => ∃ i, I.row i = u) ≫
        (graph (fun _ => []) :Core.Rel (K.El) (List B.El)))
      (corefl (α := B.El × List B.El) (fun p => ∃ i, P.row i = p) ≫
        (graph (fun p => p.1 :: p.2) :Core.Rel (B.El × List B.El) (List B.El))) :=
  by unfold CRel.alpha at hb ⊢; rw [rep_ofC hb]; exact rep_alphaC I P (ofC_ok hb).1

end CRel

end LeetQ.Rel
