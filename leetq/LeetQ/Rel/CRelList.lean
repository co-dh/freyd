/-
  The list primitives' twins read back: each `rep_<op>C` is `rep_<op>` under the twin's one bit, the bit deciding
  every size premise `rep_<op>` takes. `CRel` carries the bit along a program, as `CRel.lean` does for `≫`, `∩`, `∪`.
-/
import LeetQ.Rel.CRel
import LeetQ.Rel.RepPerm

namespace LeetQ.Rel

namespace Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

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

theorem rep_zipC {K A B : Obj} (P : Rel K (.prod (.arr A) (.arr B))) (hb : (zipC P).2 = true) :
    ∀ k zs, rep (zipC P).1 k zs ↔ ∃ xs ys, rep P k (xs, ys) ∧ zs = List.zip xs ys := by
  simp only [zipC, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨ha, hb⟩, hS⟩, hU⟩, hk⟩ := hb
  exact rep_zip P (pickFits_of_fitsN _ _ _ ha _ (by simp)) (pickFits_of_fitsN _ _ _ hb _ (by simp)) _ rfl hS hU
    _ rfl _ rfl _ rfl _ rfl _ rfl (pickFits_of_fitsN _ _ _ hk _ (by simp))

open ListN in
/-- **`consC`'s bit is `rep_cons`'s premises** (`consOK`): the decided bounds its `hS`, `hU`, the `fitsN` bits its
    `hV`, `hKf`; inside `expand`, the raze's bit its `hRf` (`razeC_fits`), the last pick's its `hFf` (`pickC_fits`). -/
theorem consC_ok {K B : Obj} (P : Rel K (.prod B (.arr B))) (hb : (consC P).2 = true) : consOK(K, B, P) := by
  simp only [consC, expand, longCount, need, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨hV, hS⟩, hU⟩, hK⟩, hb⟩ := hb
  refine ⟨pickFits_of_fitsN _ _ _ hV _ (by simp), ?_⟩
  rintro s rfl
  refine ⟨hS, hU, ?_⟩
  rintro xi rfl m rfl xr rfl j rfl tl rfl c1 rfl hi rfl lo rfl dst rfl g rfl
  refine ⟨pickFits_of_fitsN _ _ _ hK _ (by simp), ?_⟩
  split at hb
  · split at hb
    · split at hb
      · rename_i hp
        simp only [Bool.and_eq_true] at hb
        have hFf := Vals.pickC_fits B _ _ _ _ hb.2
        rw [razeC_fst, USize.toNat_ofNat_of_lt' hp] at hFf
        exact ⟨Obj.razeC_fits B _ _ _ (by rfl) _ hb.1, fun _ => hFf⟩
      · exact absurd hb Bool.false_ne_true
    · exact absurd hb Bool.false_ne_true
  · exact absurd hb Bool.false_ne_true

theorem rep_consC {K B : Obj} (P : Rel K (.prod B (.arr B))) (hb : (consC P).2 = true) :
    ∀ k ys, rep (consC P).1 k ys ↔ ∃ b bs, rep P k (b, bs) ∧ ys = b :: bs := by
  rw [consC_fst]
  obtain ⟨hV, h⟩ := consC_ok P hb
  obtain ⟨hS, hU, h⟩ := h _ rfl
  obtain ⟨hK, hR, hF⟩ := h _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
  exact rep_cons P hV _ rfl hS hU _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl hK hR hF

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

/-- **`rep (cat P)` under `catC`'s bit**: as `rep_consC`, the two sides' `fitsN` bits `rep_cat`'s `hVa`, `hVb`. -/
theorem rep_catC {K B : Obj} (P : Rel K (.prod (.arr B) (.arr B))) (hb : (catC P).2 = true) :
    ∀ k zs, rep (catC P).1 k zs ↔ ∃ xs ys, rep P k (xs, ys) ∧ zs = xs ++ ys := by
  rw [catC_fst]
  simp only [catC, expand, longCount, need, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨ha, hb'⟩, hS⟩, hU⟩, hK⟩, hb⟩ := hb
  split at hb
  · split at hb
    · split at hb
      · split at hb
        · rename_i hp
          simp only [Bool.and_eq_true] at hb
          have hRf := Obj.razeC_fits B _ _ _ (by rfl) _ hb.1
          have hFf := Vals.pickC_fits B _ _ _ _ hb.2
          rw [razeC_fst, USize.toNat_ofNat_of_lt' hp] at hFf
          exact rep_cat P (pickFits_of_fitsN _ _ _ ha _ (by simp)) (pickFits_of_fitsN _ _ _ hb' _ (by simp))
            _ rfl _ rfl hS hU _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
            _ rfl _ rfl (pickFits_of_fitsN _ _ _ hK _ (by simp)) hRf (fun _ => hFf)
        · exact absurd hb Bool.false_ne_true
      · exact absurd hb Bool.false_ne_true
    · exact absurd hb Bool.false_ne_true
  · exact absurd hb Bool.false_ne_true

/-- **`nestC`'s bit, read as `rep_inits`'s and `rep_tails`'s premises**: the decided bounds, `X` fitting at all its
    rows, and the slices' compacting pick fitting at the `m` copies `expand` makes (`pickC_fits`). -/
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
  obtain ⟨⟨⟨hS, hU⟩, hK⟩, hb⟩ := hb
  refine ⟨hS, hU, pickFits_of_fitsN _ X _ hK _ (by simp), fun _ => ?_⟩
  split at hb
  · exact Vals.pickC_fits (.arr B) _ _ _ _ hb
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

#print axioms rep_consC
#print axioms rep_catC
#print axioms rep_initsC

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

/-- `cons`, ok where `P` is and `consC` ran within capacity. -/
def cons (P : CRel K (.prod B (.arr B))) : CRel K (.arr B) := let r := consC P.rel; ⟨r.1, P.ok && r.2⟩

/-- `cat`, ok where `P` is and `catC` ran within capacity. -/
def cat (P : CRel K (.prod (.arr B) (.arr B))) : CRel K (.arr B) := let r := catC P.rel; ⟨r.1, P.ok && r.2⟩

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

theorem rep_cons (P : CRel K (.prod B (.arr B))) (hb : (cons P).ok = true) :
    ∀ k ys, rep (cons P).rel k ys ↔ ∃ b bs, rep P.rel k (b, bs) ∧ ys = b :: bs :=
  rep_consC P.rel (by simp only [cons, Bool.and_eq_true] at hb; exact hb.2)

theorem rep_cat (P : CRel K (.prod (.arr B) (.arr B))) (hb : (cat P).ok = true) :
    ∀ k zs, rep (cat P).rel k zs ↔ ∃ xs ys, rep P.rel k (xs, ys) ∧ zs = xs ++ ys :=
  rep_catC P.rel (by simp only [cat, Bool.and_eq_true] at hb; exact hb.2)

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
