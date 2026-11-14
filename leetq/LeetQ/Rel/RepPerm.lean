/-
  List composites read back: `tic` (`cons`, `inits`, `tail`) and `perm` (`foldBy` at a step built from `uncat`,
  `cat`, `cons`, `pair`), each from its primitives' read-backs.
-/
import LeetQ.Rel.RepEst
import LeetQ.Rel.RepUncat

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

open FoldN OpsN Prim

/-! `cons`'s, `cat`'s and `snoc`'s bundles, one home: `open ListN` in every file that reads back a composite of
    them (`snocOK` also needs `Pow`, `FoldN` and `Prim` open). -/
namespace ListN
-- `rep_cons`'s hypotheses at `P`, its pieces bound by their equations
set_option hygiene false in
scoped notation "consOK(" K ", " B ", " P ")" =>
  ((Rel.val P).2.1.toNat < 2 ^ 63 ∧
    ∀ s : ByteArray × ByteArray, s = slicesOf (Rel.val P).2 →
    ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt s.2 (r * 8) 8).toNat).sum + (Rel.n P).toNat <
      2 ^ 63 ∧
    ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt s.2 (r * 8) 8).toNat).sum + (Rel.n P).toNat <
      USize.size ∧
    ∀ xi : ByteArray, xi = expandBytes 8 0 (tilLongs (Rel.n P)) s.2 →
    ∀ m : USize, m = (len xi).toUSize →
    ∀ xr : ByteArray, xr = sub m (tilLongs m) (gather 8 (sub (Rel.n P) (sums (Rel.n P) s.2) s.2) xi) →
    ∀ j : ByteArray, j = add m (gather 8 s.1 xi) xr →
    ∀ tl : Vals B m, tl = Vals.pick B (Rel.val P).2.2.2.2 (add m (gather 8 s.1 xi) xr) m
      (len_val Ew.add Ew.vv (gather 8 s.1 xi) xr m) →
    ∀ c1 : ByteArray, c1 = addc (Rel.n P) s.2 1 → ∀ hi : ByteArray, hi = sums (Rel.n P) c1 →
    ∀ lo : ByteArray, lo = sub (Rel.n P) hi c1 →
    ∀ dst : ByteArray, dst = addc m (add m (gather 8 lo xi) xr) 1 →
    ∀ g : ByteArray, g = (Code.ofLongs (concatBytes #[dst, lo])).grade →
    Vals.PickFits K (Rel.key P)
      ((List.range (Rel.n P).toNat).map fun q => (Column.bitsAt (tilLongs (Rel.n P)) (q * 8) 8).toNat) ∧
    Vals.PickFits B (Rel.val P).2.2.2.2 ((List.range m.toNat).map fun q => (Column.bitsAt j (q * 8) 8).toNat) ∧
    Vals.RazeFits B tl (Rel.val P).1 ∧
    ∀ hN, Vals.PickFits B (Obj.raze B #[⟨m, tl⟩, ⟨Rel.n P, (Rel.val P).1⟩] hN)
      ((List.range (len g)).map fun q => (Column.bitsAt g (q * 8) 8).toNat))
-- `rep_cat`'s hypotheses at `P`, its pieces bound by their equations
set_option hygiene false in
scoped notation "catOK(" K ", " B ", " P ")" =>
  ((Rel.val P).1.1.toNat < 2 ^ 63 ∧ (Rel.val P).2.1.toNat < 2 ^ 63 ∧
    ∀ sa : ByteArray × ByteArray, sa = slicesOf (Rel.val P).1 →
    ∀ sb : ByteArray × ByteArray, sb = slicesOf (Rel.val P).2 →
    ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt sa.2 (r * 8) 8).toNat).sum +
      ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt sb.2 (r * 8) 8).toNat).sum < 2 ^ 63 ∧
    ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt sa.2 (r * 8) 8).toNat).sum +
      ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt sb.2 (r * 8) 8).toNat).sum < USize.size ∧
    ∀ xa : ByteArray, xa = expandBytes 8 0 (tilLongs (Rel.n P)) sa.2 →
    ∀ ma : USize, ma = (len xa).toUSize →
    ∀ ra : ByteArray, ra = sub ma (tilLongs ma) (gather 8 (sub (Rel.n P) (sums (Rel.n P) sa.2) sa.2) xa) →
    ∀ xb : ByteArray, xb = expandBytes 8 0 (tilLongs (Rel.n P)) sb.2 →
    ∀ mb : USize, mb = (len xb).toUSize →
    ∀ rb : ByteArray, rb = sub mb (tilLongs mb) (gather 8 (sub (Rel.n P) (sums (Rel.n P) sb.2) sb.2) xb) →
    ∀ ja : ByteArray, ja = add ma (gather 8 sa.1 xa) ra →
    ∀ jb : ByteArray, jb = add mb (gather 8 sb.1 xb) rb →
    ∀ ta : Vals B ma, ta = Vals.pick B (Rel.val P).1.2.2.2 (add ma (gather 8 sa.1 xa) ra) ma
      (len_val Ew.add Ew.vv (gather 8 sa.1 xa) ra ma) →
    ∀ tb : Vals B mb, tb = Vals.pick B (Rel.val P).2.2.2.2 (add mb (gather 8 sb.1 xb) rb) mb
      (len_val Ew.add Ew.vv (gather 8 sb.1 xb) rb mb) →
    ∀ c : ByteArray, c = add (Rel.n P) sa.2 sb.2 → ∀ hi : ByteArray, hi = sums (Rel.n P) c →
    ∀ lo : ByteArray, lo = sub (Rel.n P) hi c →
    ∀ da : ByteArray, da = add ma (gather 8 lo xa) ra →
    ∀ db : ByteArray, db = add mb (add mb (gather 8 lo xb) (gather 8 sa.2 xb)) rb →
    ∀ g : ByteArray, g = (Code.ofLongs (concatBytes #[da, db])).grade →
    Vals.PickFits K (Rel.key P)
      ((List.range (Rel.n P).toNat).map fun q => (Column.bitsAt (tilLongs (Rel.n P)) (q * 8) 8).toNat) ∧
    Vals.PickFits B (Rel.val P).1.2.2.2 ((List.range ma.toNat).map fun q => (Column.bitsAt ja (q * 8) 8).toNat) ∧
    Vals.PickFits B (Rel.val P).2.2.2.2 ((List.range mb.toNat).map fun q => (Column.bitsAt jb (q * 8) 8).toNat) ∧
    Vals.RazeFits B ta tb ∧
    ∀ hN, Vals.PickFits B (Obj.raze B #[⟨ma, ta⟩, ⟨mb, tb⟩] hN)
      ((List.range (len g)).map fun q => (Column.bitsAt g (q * 8) 8).toNat))
end ListN
open ListN

-- `rep_inits`'s hypotheses at the arrays `X` (`n` rows), its pieces bound by their equations
set_option hygiene false in
local notation "initsOK(" B ", " n ", " X ")" =>
  ((X).1.toNat < 2 ^ 63 ∧ ∀ c : ByteArray, c = addc n (slicesOf X).2 1 →
    ((List.range (n).toNat).map fun u => (Column.bitsAt (slicesOf X).2 (u * 8) 8).toNat).sum + (n).toNat < 2 ^ 63 ∧
    ((List.range (n).toNat).map fun u => (Column.bitsAt (slicesOf X).2 (u * 8) 8).toNat).sum + (n).toNat <
      USize.size ∧
    ∀ xi : ByteArray, xi = expandBytes 8 0 (tilLongs n) c → ∀ m : USize, m = (len xi).toUSize →
    ∀ xr : ByteArray, xr = sub m (tilLongs m) (gather 8 (sub n (sums n c) c) xi) →
    Vals.PickFits (.arr B) X ((List.range (n).toNat).map fun q => (Column.bitsAt (tilLongs n) (q * 8) 8).toNat) ∧
    ∀ h : len xi = m.toNat, Vals.PickFits (.arr B)
      (⟨(X).1, longsN m (gather 8 (slicesOf X).1 xi) (Nat.le_of_eq ((gather_len _ _).trans h).symm),
        valCol Ew.add Ew.vv (gather 8 (slicesOf X).1 xi) xr, (X).2.2.2⟩ : Vals (.arr B) m)
      ((List.range m.toNat).map fun q => (Column.bitsAt (tilLongs m) (q * 8) 8).toNat))

-- `rep_uncat`'s hypotheses at the arrays `X` (`n` rows), its pieces bound by their equations
set_option hygiene false in
local notation "uncatOK(" B ", " n ", " X ")" =>
  ((X).1.toNat < 2 ^ 63 ∧ ∀ c : ByteArray, c = addc n (slicesOf X).2 1 →
    ((List.range (n).toNat).map fun u => (Column.bitsAt (slicesOf X).2 (u * 8) 8).toNat).sum + (n).toNat < 2 ^ 63 ∧
    ((List.range (n).toNat).map fun u => (Column.bitsAt (slicesOf X).2 (u * 8) 8).toNat).sum + (n).toNat <
      USize.size ∧
    ∀ xi : ByteArray, xi = expandBytes 8 0 (tilLongs n) c → ∀ m : USize, m = (len xi).toUSize →
    ∀ xr : ByteArray, xr = sub m (tilLongs m) (gather 8 (sub n (sums n c) c) xi) →
    Vals.PickFits (.arr B) X ((List.range (n).toNat).map fun q => (Column.bitsAt (tilLongs n) (q * 8) 8).toNat) ∧
    (∀ h : len xi = m.toNat, Vals.PickFits (.arr B)
      (⟨(X).1, longsN m (gather 8 (slicesOf X).1 xi) (Nat.le_of_eq ((gather_len _ _).trans h).symm),
        valCol Ew.add Ew.vv (gather 8 (slicesOf X).1 xi) xr, (X).2.2.2⟩ : Vals (.arr B) m)
      ((List.range m.toNat).map fun q => (Column.bitsAt (tilLongs m) (q * 8) 8).toNat)) ∧
    (∀ h : len xi = m.toNat, Vals.PickFits (.arr B)
      (⟨(X).1, valCol Ew.add Ew.vv (gather 8 (slicesOf X).1 xi) xr,
        longsN m (gather 8 (add n (slicesOf X).1 (slicesOf X).2) xi) (Nat.le_of_eq ((gather_len _ _).trans h).symm),
        (X).2.2.2⟩ : Vals (.arr B) m)
      ((List.range m.toNat).map fun q => (Column.bitsAt (tilLongs m) (q * 8) 8).toNat)) ∧
    ∀ kc : Vector Code 2, kc = Obj.codes (.arr B)
      (#v[⟨Rel.n (inits X), Rel.key (inits X)⟩, ⟨Rel.n (tails X), Rel.key (tails X)⟩] : Vector (Part (.arr B)) 2) →
    codesOK(kc,
      (#v[⟨Rel.n (inits X), Rel.key (inits X)⟩, ⟨Rel.n (tails X), Rel.key (tails X)⟩] : Vector (Part (.arr B)) 2)) ∧
    (Rel.n (tails X)).toNat < 2 ^ 63 ∧ msum(kc, inits X, tails X) < 2 ^ 63 ∧
    msum(kc, inits X, tails X) < USize.size ∧
    Vals.PickFits (.arr B) (Rel.key (inits X)) ((mpairs(kc, inits X, tails X)).map Prod.fst) ∧
    Vals.PickFits (.arr (.arr B)) (Rel.val (inits X)) ((mpairs(kc, inits X, tails X)).map Prod.fst) ∧
    Vals.PickFits (.arr (.arr B)) (Rel.val (tails X)) ((mpairs(kc, inits X, tails X)).map Prod.snd) ∧
    ∀ P : Rel (.arr B) (.prod (.arr (.arr B)) (.arr (.arr B))), P = pair (inits X) (tails X) →
    (Rel.val P).1.1.toNat < 2 ^ 63 ∧ (Rel.val P).2.1.toNat < 2 ^ 63 ∧
    ∀ c' : ByteArray, c' = Kernel.Ew.val Ew.lesser Ew.i64 Ew.vv nul (slicesOf (Rel.val P).1).2
      (slicesOf (Rel.val P).2).2 (Rel.n P) →
    ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt c' (r * 8) 8).toNat).sum < 2 ^ 63 ∧
    ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt c' (r * 8) 8).toNat).sum < USize.size ∧
    ∀ xi' : ByteArray, xi' = expandBytes 8 0 (tilLongs (Rel.n P)) c' →
    ∀ m' : USize, m' = (len xi').toUSize →
    ∀ xr' : ByteArray, xr' = sub m' (tilLongs m') (gather 8 (sub (Rel.n P) (sums (Rel.n P) c') c') xi') →
    ∀ ja : ByteArray, ja = add m' (gather 8 (slicesOf (Rel.val P).1).1 xi') xr' →
    ∀ jb : ByteArray, jb = add m' (gather 8 (slicesOf (Rel.val P).2).1 xi') xr' →
    Vals.PickFits (.arr B) (Rel.key P)
      ((List.range (Rel.n P).toNat).map fun q => (Column.bitsAt (tilLongs (Rel.n P)) (q * 8) 8).toNat) ∧
    Vals.PickFits (.arr B) (Rel.val P).1.2.2.2
      ((List.range m'.toNat).map fun q => (Column.bitsAt ja (q * 8) 8).toNat) ∧
    Vals.PickFits (.arr B) (Rel.val P).2.2.2.2
      ((List.range m'.toNat).map fun q => (Column.bitsAt jb (q * 8) 8).toNat) ∧
    ∀ Z : Rel (.arr B) (.arr (.prod (.arr B) (.arr B))), Z = zip P →
    ∀ jc : Vector Code 2, jc = Obj.codes (.arr (.prod (.arr B) (.arr B)))
      (#v[⟨Rel.n Z, Rel.val Z⟩, ⟨Rel.n (mem Z.val), Rel.key (mem Z.val)⟩] :
        Vector (Part (.arr (.prod (.arr B) (.arr B)))) 2) →
    codesOK(jc, (#v[⟨Rel.n Z, Rel.val Z⟩, ⟨Rel.n (mem Z.val), Rel.key (mem Z.val)⟩] :
        Vector (Part (.arr (.prod (.arr B) (.arr B)))) 2)) ∧
    (Rel.n (mem Z.val)).toNat < 2 ^ 63 ∧ msum(jc, Z, mem Z.val) < 2 ^ 63 ∧ msum(jc, Z, mem Z.val) < USize.size ∧
    Vals.PickFits (.arr B) (Rel.key Z) ((mpairs(jc, Z, mem Z.val)).map Prod.fst) ∧
    Vals.PickFits (.prod (.arr B) (.arr B)) (Rel.val (mem Z.val)) ((mpairs(jc, Z, mem Z.val)).map Prod.snd) ∧
    Vals.PickFits (.arr (.prod (.arr B) (.arr B))) Z.val (List.range Z.n.toNat) ∧
    Vals.PickFits (.arr (.prod (.arr B) (.arr B))) Z.val ((List.range Z.n.toNat).flatMap fun r =>
      if h : r < Z.n.toNat then List.replicate (Z.val.row ⟨r, h⟩).length r else []))

/-- `rep_cons` with its hypotheses as the bundle `consOK`. -/
theorem rep_cons_ok {K B : Obj} (P : Rel K (.prod B (.arr B))) (h : consOK(K, B, P)) :
    ∀ k ys, rep (cons P) k ys ↔ ∃ b bs, rep P k (b, bs) ∧ ys = b :: bs := by
  obtain ⟨hp, hs⟩ := h
  obtain ⟨hS, hU, hx⟩ := hs _ rfl
  obtain ⟨hKf, hTf, hRf, hFf⟩ := hx _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
  exact rep_cons P hp _ rfl hS hU _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl hKf hTf hRf hFf

/-- `rep_cat` with its hypotheses as the bundle `catOK`. -/
theorem rep_cat_ok {K B : Obj} (P : Rel K (.prod (.arr B) (.arr B))) (h : catOK(K, B, P)) :
    ∀ k zs, rep (cat P) k zs ↔ ∃ xs ys, rep P k (xs, ys) ∧ zs = xs ++ ys := by
  obtain ⟨hpa, hpb, h1⟩ := h
  obtain ⟨hS, hU, h2⟩ := h1 _ rfl _ rfl
  obtain ⟨hKf, hTa, hTb, hRf, hFf⟩ :=
    h2 _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
  exact rep_cat P hpa hpb _ rfl _ rfl hS hU _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
    _ rfl _ rfl _ rfl _ rfl hKf hTa hTb hRf hFf

/-- `rep_uncat` with its hypotheses as the bundle `uncatOK`. -/
theorem rep_uncat_ok {B : Obj} {n : USize} (X : Vals (.arr B) n) (h : uncatOK(B, n, X)) :
    ∀ xs ys zs, rep (uncat X) xs (ys, zs) ↔ (∃ j, X.row j = xs) ∧ xs = ys ++ zs := by
  obtain ⟨hp, h1⟩ := h
  obtain ⟨hS, hU, h2⟩ := h1 _ rfl
  obtain ⟨hK, hVi, hVt, h3⟩ := h2 _ rfl _ rfl _ rfl
  obtain ⟨hkO, hkn, hkM, hkU, hkA, hkB, hkC, h4⟩ := h3 _ rfl
  obtain ⟨hpa, hpb, h5⟩ := h4 _ rfl
  obtain ⟨hS', hU', h6⟩ := h5 _ rfl
  obtain ⟨hKf, hAf, hBf, h7⟩ := h6 _ rfl _ rfl _ rfl _ rfl _ rfl
  obtain ⟨hjO, hjn, hjM, hjU, hjA, hjC, hv, hk⟩ := h7 _ rfl _ rfl
  exact rep_uncat X hp _ rfl hS hU _ rfl _ rfl _ rfl hK hVi hVt _ rfl hkO hkn hkM hkU hkA hkB hkC _ rfl hpa hpb
    _ rfl hS' hU' _ rfl _ rfl _ rfl _ rfl _ rfl hKf hAf hBf _ rfl _ rfl hjO hjn hjM hjU hjA hjC hv hk

open Freyd Freyd.Alg Freyd.Alg.RelSet in
/-- **`α ≜ [nil, cons]`, read back**: the copairing, out of the sum, of `nil` on the elements `I` lists (each to
    the empty array) and `cons` on the pairs `P` lists (`(b, bs)` to `b :: bs`). Hypotheses: `rep_junc_full`'s at
    `nil I`, `cons (idU P)` (`hN`, `h63`, `hF`), `rep_cons`'s at `idU P` (`hc`). -/
theorem rep_alpha {K B : Obj} {n : USize} (I : Vals K 1) (P : Vals (.prod B (.arr B)) n)
    (hN : (Alg.nil (B := B) I).n.toNat + (cons (idU P)).n.toNat < USize.size)
    (h63 : (Alg.nil (B := B) I).n.toNat + (cons (idU P)).n.toNat ≤ 2 ^ 63)
    (hF : Vals.RazeFits (.arr B) (Alg.nil (B := B) I).val (cons (idU P)).val)
    (hc : consOK(.prod B (.arr B), B, idU P)) :
    rep (alpha I P) = Freyd.Alg.junc (sumCop (⟨K.El⟩ : RelSet.{0}) ⟨B.El × List B.El⟩)
      (corefl (A := (⟨K.El⟩ : RelSet.{0})) (fun u => ∃ i, I.row i = u) ≫
        (graph (fun _ => []) :(⟨K.El⟩ : RelSet.{0}) ⟶ ⟨List B.El⟩))
      (corefl (A := (⟨B.El × List B.El⟩ : RelSet.{0})) (fun p => ∃ i, P.row i = p) ≫
        (graph (fun p => p.1 :: p.2) :(⟨B.El × List B.El⟩ : RelSet.{0}) ⟶ ⟨List B.El⟩)) := by
  rw [alpha, rep_junc_full _ _ hN h63 hF, ← rep_idU P]
  congr 1
  · refine hom_ext fun u xs => (rep_nil I u xs).trans ⟨?_, ?_⟩
    · rintro ⟨h, rfl⟩; exact ⟨u, ⟨rfl, h⟩, rfl⟩
    · rintro ⟨v, ⟨rfl, h⟩, rfl⟩; exact ⟨h, rfl⟩
  · refine hom_ext fun p ys => (rep_cons_ok _ hc p ys).trans ⟨?_, ?_⟩
    · rintro ⟨b, bs, h, rfl⟩; exact ⟨(b, bs), h, rfl⟩
    · rintro ⟨⟨b, bs⟩, h, rfl⟩; exact ⟨b, bs, h, rfl⟩

/-! ## `tic` -/

/-- **`tic`, read back**: a row `(b, bs)` of `P` goes to the non-empty prefixes of `b :: bs`, shortest first.
    `tic P` is `I ≫ tail I.val`, `I = C ≫ inits C.val`, `C = cons P` (bound by `hC`, `hI`). Hypotheses:
    `rep_cons`'s at `P` (`hc`), `rep_comp`'s at `I` (`h1`) and at the result (`h2`), `rep_inits`'s at `C.val`
    (`hi`), `rep_tail`'s at `I.val` (`ht`). -/
theorem rep_tic {K B : Obj} (P : Rel K (.prod B (.arr B))) (C : Rel K (.arr B)) (hC : C = cons P)
    (I : Rel K (.arr (.arr B))) (hI : I = C ≫ inits (Rel.val C))
    (hc : consOK(K, B, P)) (h1 : cmpOK(.arr B, C, inits (Rel.val C))) (hi : initsOK(B, Rel.n C, Rel.val C))
    (h2 : cmpOK(.arr (.arr B), I, tail (Rel.val I))) (ht : uncOK(.arr B, I)) :
    ∀ k zss, rep (tic P) k zss ↔ ∃ b bs, rep P k (b, bs) ∧
      zss = (List.range (bs.length + 1)).map fun j => (b :: bs).take (j + 1) := by
  have eC := rep_cons_ok P hc
  obtain ⟨h1f, h1'⟩ := h1
  obtain ⟨c1, c2, c3, c4, c5⟩ := h1' _ rfl
  have e1 := rep_comp _ _ (codes_faithful_wf _ _ h1f).1 c1 c2 c3 c4 c5
  obtain ⟨i63, hi'⟩ := hi
  obtain ⟨iS, iU, hx⟩ := hi' _ rfl
  obtain ⟨iK, iV⟩ := hx _ rfl _ rfl _ rfl
  have eN := rep_inits (Rel.val C) i63 _ rfl iS iU _ rfl _ rfl _ rfl iK iV
  obtain ⟨h2f, h2'⟩ := h2
  obtain ⟨d1, d2, d3, d4, d5⟩ := h2' _ rfl
  have e2 := rep_comp _ _ (codes_faithful_wf _ _ h2f).1 d1 d2 d3 d4 d5
  obtain ⟨t63, ht'⟩ := ht
  obtain ⟨tK, tH, tT⟩ := ht' _ rfl _ rfl _ rfl
  have eT := rep_tail (Rel.val I) t63 _ rfl _ rfl _ rfl tK tH tT
  -- `I`: a row `(b, bs)` to every prefix of `b :: bs`
  have eI : ∀ k yss, rep I k yss ↔ ∃ b bs, rep P k (b, bs) ∧
      yss = (List.range ((b :: bs).length + 1)).map fun j => (b :: bs).take j := by
    intro k yss
    rw [hI, e1, Freyd.Alg.RelSet.comp_apply]
    constructor
    · rintro ⟨ys, hy, hn⟩
      obtain ⟨-, rfl⟩ := (eN ys yss).1 hn
      rw [hC] at hy
      obtain ⟨b, bs, hb, rfl⟩ := (eC k ys).1 hy
      exact ⟨b, bs, hb, rfl⟩
    · rintro ⟨b, bs, hb, rfl⟩
      have hy : rep C k (b :: bs) := by rw [hC]; exact (eC k _).2 ⟨b, bs, hb, rfl⟩
      obtain ⟨q, -, hq⟩ := id hy
      exact ⟨b :: bs, hy, (eN _ _).2 ⟨⟨q, hq⟩, rfl⟩⟩
  have hl : ∀ (b : B.El) (bs : List B.El), (List.range ((b :: bs).length + 1)).map (fun j => (b :: bs).take j) =
      [] :: (List.range (bs.length + 1)).map fun j => (b :: bs).take (j + 1) := by
    intro b bs
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    rfl
  intro k zss
  rw [show tic P = I ≫ tail (Rel.val I) by rw [hI, hC]; rfl, e2, Freyd.Alg.RelSet.comp_apply]
  constructor
  · rintro ⟨yss, hy, ht⟩
    obtain ⟨-, y, e⟩ := (eT yss zss).1 ht
    obtain ⟨b, bs, hb, rfl⟩ := (eI k yss).1 hy
    exact ⟨b, bs, hb, (List.cons.inj ((hl b bs).symm.trans e)).2.symm⟩
  · rintro ⟨b, bs, hb, rfl⟩
    have hy := (eI k _).2 ⟨b, bs, hb, rfl⟩
    obtain ⟨q, -, hq⟩ := id hy
    exact ⟨_, hy, (eT _ _).2 ⟨⟨q, hq⟩, [], hl b bs⟩⟩

/-! ## `perm` -/

/-- `perm`'s step on relations: given what each piece relates, `q ≫ cat V` takes row `r`'s element `e` and list
    `u = ys ++ zs` to `ys ++ e :: zs`. The pieces are as `perm` builds them: `U = pend ≫ uncat`, `q = ⟨el, U⟩`,
    `D = ran q`, `W = ⟨π₁ D, π₂ π₂ D⟩`, `Cn = cons W`, `V = ⟨π₁ π₂ D, Cn⟩`, `Ct = cat V`, `R = q ≫ Ct`. -/
theorem perm_step_set {B : Obj} (el : Rel .long B) (pend : Rel .long (.arr B))
    (U : Rel .long (.prod (.arr B) (.arr B))) (q : Rel .long (.prod B (.prod (.arr B) (.arr B))))
    (D : Rel (.prod B (.prod (.arr B) (.arr B))) (.prod B (.prod (.arr B) (.arr B))))
    (W : Rel (.prod B (.prod (.arr B) (.arr B))) (.prod B (.arr B)))
    (Cn : Rel (.prod B (.prod (.arr B) (.arr B))) (.arr B))
    (V : Rel (.prod B (.prod (.arr B) (.arr B))) (.prod (.arr B) (.arr B)))
    (Ct : Rel (.prod B (.prod (.arr B) (.arr B))) (.arr B)) (R : Rel .long (.arr B))
    (hU : ∀ r ys zs, rep U r (ys, zs) ↔ ∃ u, rep pend r u ∧ u = ys ++ zs)
    (hq : ∀ r e p, rep q r (e, p) ↔ rep el r e ∧ rep U r p)
    (hD : ∀ t t', rep D t t' ↔ t = t' ∧ ∃ r, rep q r t)
    (hW : ∀ t a b, rep W t (a, b) ↔ rep (outl D) t a ∧ rep (outr (outr D)) t b)
    (hCn : ∀ t ys, rep Cn t ys ↔ ∃ a b, rep W t (a, b) ∧ ys = a :: b)
    (hV : ∀ t xs ys, rep V t (xs, ys) ↔ rep (outl (outr D)) t xs ∧ rep Cn t ys)
    (hCt : ∀ t zs, rep Ct t zs ↔ ∃ xs ys, rep V t (xs, ys) ∧ zs = xs ++ ys)
    (hR : ∀ r v, rep R r v ↔ ∃ t, rep q r t ∧ rep Ct t v) :
    ∀ r v, rep R r v ↔ ∃ e u, rep el r e ∧ rep pend r u ∧ ∃ ys zs, u = ys ++ zs ∧ v = ys ++ e :: zs := by
  -- the components `D` reads off a tuple `q` reaches
  have hl : ∀ t a, rep (outl D) t a ↔ a = t.1 ∧ ∃ r, rep q r t := by
    intro t a
    refine (outl_holds D t a).trans ⟨fun ⟨z, h⟩ => ?_, fun ⟨e, h'⟩ => ⟨t.2, (hD _ _).2 ⟨by subst e; rfl, h'⟩⟩⟩
    obtain ⟨rfl, h'⟩ := (hD _ _).1 h
    exact ⟨rfl, h'⟩
  have hrr : ∀ t b, rep (outr (outr D)) t b ↔ b = t.2.2 ∧ ∃ r, rep q r t := by
    intro t b
    refine (outr_holds (outr D) t b).trans ⟨fun ⟨y, h⟩ => ?_,
      fun ⟨e, h'⟩ => ⟨t.2.1, (outr_holds D t _).2 ⟨t.1, (hD _ _).2 ⟨by subst e; rfl, h'⟩⟩⟩⟩
    obtain ⟨x, h⟩ := (outr_holds D t (y, b)).1 h
    obtain ⟨rfl, h'⟩ := (hD _ _).1 h
    exact ⟨rfl, h'⟩
  have hlr : ∀ t xs, rep (outl (outr D)) t xs ↔ xs = t.2.1 ∧ ∃ r, rep q r t := by
    intro t xs
    refine (outl_holds (outr D) t xs).trans ⟨fun ⟨z, h⟩ => ?_,
      fun ⟨e, h'⟩ => ⟨t.2.2, (outr_holds D t _).2 ⟨t.1, (hD _ _).2 ⟨by subst e; rfl, h'⟩⟩⟩⟩
    obtain ⟨x, h⟩ := (outr_holds D t (xs, z)).1 h
    obtain ⟨rfl, h'⟩ := (hD _ _).1 h
    exact ⟨rfl, h'⟩
  have hCt' : ∀ t v, (∃ r, rep q r t) → (rep Ct t v ↔ v = t.2.1 ++ t.1 :: t.2.2) := by
    intro t v ht
    rw [hCt]
    constructor
    · rintro ⟨xs, ys, hv, rfl⟩
      obtain ⟨hx, hy⟩ := (hV _ _ _).1 hv
      obtain ⟨rfl, -⟩ := (hlr _ _).1 hx
      obtain ⟨a, b, hw, rfl⟩ := (hCn _ _).1 hy
      obtain ⟨ha, hb⟩ := (hW _ _ _).1 hw
      obtain ⟨rfl, -⟩ := (hl _ _).1 ha
      obtain ⟨rfl, -⟩ := (hrr _ _).1 hb
      rfl
    · rintro rfl
      exact ⟨_, _, (hV _ _ _).2 ⟨(hlr _ _).2 ⟨rfl, ht⟩, (hCn _ _).2
        ⟨_, _, (hW _ _ _).2 ⟨(hl _ _).2 ⟨rfl, ht⟩, (hrr _ _).2 ⟨rfl, ht⟩⟩, rfl⟩⟩, rfl⟩
  intro r v
  rw [hR]
  constructor
  · rintro ⟨⟨e, ys, zs⟩, ht, hv⟩
    rw [hCt' _ _ ⟨r, ht⟩] at hv
    obtain ⟨he, hu⟩ := (hq _ _ _).1 ht
    obtain ⟨u, hu, rfl⟩ := (hU _ _ _).1 hu
    exact ⟨e, _, he, hu, ys, zs, rfl, hv⟩
  · rintro ⟨e, u, he, hu, ys, zs, rfl, rfl⟩
    have ht : rep q r (e, ys, zs) := (hq _ _ _).2 ⟨he, (hU _ _ _).2 ⟨_, hu, rfl⟩⟩
    exact ⟨_, ht, (hCt' _ _ ⟨r, ht⟩).2 rfl⟩

-- every primitive's hypotheses at one round of `perm`, at the round's element `el` and state `pend`, each piece
-- bound by its equation as `perm`'s step builds it
set_option hygiene false in
local notation "permOK" =>
  (oneFit(.arr B, Rel.n pend, Rel.val pend) ∧
    ∀ Dp : Rel (.arr B) (.arr B), Dp = ran pend →
    uncatOK(B, Rel.n Dp, Rel.val Dp) ∧ cmpOK(.arr B, pend, uncat (Rel.val Dp)) ∧
    ∀ U : Rel .long (.prod (.arr B) (.arr B)), U = pend ≫ uncat (Rel.val Dp) →
    pairOK(.long, el, U) ∧
    ∀ q : Rel .long (.prod B (.prod (.arr B) (.arr B))), q = pair el U →
    oneFit(.prod B (.prod (.arr B) (.arr B)), Rel.n q, Rel.val q) ∧
    ∀ D : Rel (.prod B (.prod (.arr B) (.arr B))) (.prod B (.prod (.arr B) (.arr B))), D = ran q →
    pairOK(.prod B (.prod (.arr B) (.arr B)), outl D, outr (outr D)) ∧
    ∀ W : Rel (.prod B (.prod (.arr B) (.arr B))) (.prod B (.arr B)), W = pair (outl D) (outr (outr D)) →
    consOK(.prod B (.prod (.arr B) (.arr B)), B, W) ∧
    ∀ Cn : Rel (.prod B (.prod (.arr B) (.arr B))) (.arr B), Cn = cons W →
    pairOK(.prod B (.prod (.arr B) (.arr B)), outl (outr D), Cn) ∧
    ∀ V : Rel (.prod B (.prod (.arr B) (.arr B))) (.prod (.arr B) (.arr B)), V = pair (outl (outr D)) Cn →
    catOK(.prod B (.prod (.arr B) (.arr B)), B, V) ∧ cmpOK(.prod B (.prod (.arr B) (.arr B)), q, cat V))

/-- **`perm`'s step, read back**: row `r`'s element `e` and list `u` go to `e` inserted at any cut of `u`.
    Hypotheses: every primitive's at the round's pieces (`permOK`): `rep_ran`'s at `pend` and `q`, `rep_uncat`'s,
    `rep_comp`'s at `U` and at the result, `rep_pair`'s at `q`, `W`, `V`, `rep_cons`'s at `W`, `rep_cat`'s at
    `V`. -/
theorem perm_step_rep {B : Obj} (el : Rel .long B) (pend : Rel .long (.arr B)) (h : permOK) :
    ∀ r v, rep (let q := pair el (pend ≫ uncat (ran pend).val); let D := ran q;
        q ≫ cat (pair (outl (outr D)) (cons (pair (outl D) (outr (outr D)))))) r v ↔
      ∃ e u, rep el r e ∧ rep pend r u ∧ ∃ ys zs, u = ys ++ zs ∧ v = ys ++ e :: zs := by
  obtain ⟨⟨hDf, hDp⟩, h1⟩ := h
  obtain ⟨hUn, ⟨huf, hu'⟩, h2⟩ := h1 _ rfl
  obtain ⟨⟨hqf, hq'⟩, h3⟩ := h2 _ rfl
  obtain ⟨⟨hdf, hdp⟩, h4⟩ := h3 _ rfl
  obtain ⟨⟨hwf, hw'⟩, h5⟩ := h4 _ rfl
  obtain ⟨hCn, h6⟩ := h5 _ rfl
  obtain ⟨⟨hvf, hv'⟩, h7⟩ := h6 _ rfl
  obtain ⟨hCt, hrf, hr'⟩ := h7 _ rfl
  obtain ⟨u1, u2, u3, u4, u5⟩ := hu' _ rfl
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hq' _ rfl
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := hw' _ rfl
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hv' _ rfl
  obtain ⟨r1, r2, r3, r4, r5⟩ := hr' _ rfl
  have eDp := rep_ran_corefl pend (one_ok _ hDf) (hDp)
  have eUn := rep_uncat_ok (Rel.val (ran pend)) hUn
  have eU := rep_comp _ _ (codes_faithful_wf _ _ huf).1 u1 u2 u3 u4 u5
  have eq := rep_pair _ _ (codes_faithful_wf _ _ hqf).1 p1 p2 p3 p4 p5 p6
  have eD := rep_ran_corefl _ (one_ok _ hdf) (hdp)
  have eW := rep_pair _ _ (codes_faithful_wf _ _ hwf).1 w1 w2 w3 w4 w5 w6
  have eCn := rep_cons_ok _ hCn
  have eV := rep_pair _ _ (codes_faithful_wf _ _ hvf).1 v1 v2 v3 v4 v5 v6
  have eCt := rep_cat_ok _ hCt
  have eR := rep_comp _ _ (codes_faithful_wf _ _ hrf).1 r1 r2 r3 r4 r5
  refine perm_step_set el pend (pend ≫ uncat (Rel.val (ran pend))) (pair el (pend ≫ uncat (Rel.val (ran pend))))
    (ran (pair el (pend ≫ uncat (Rel.val (ran pend))))) _ _ _ _ _ (fun r ys zs => ?_)
    (fun r e p => Iff.of_eq (congrFun (congrFun eq r) (e, p))) (fun t t' => Iff.of_eq (congrFun (congrFun eD t) t'))
    (fun t a b => Iff.of_eq (congrFun (congrFun eW t) (a, b))) eCn
    (fun t xs ys => Iff.of_eq (congrFun (congrFun eV t) (xs, ys))) eCt
    (fun r v => Iff.of_eq (congrFun (congrFun eR r) v))
  rw [eU, Freyd.Alg.RelSet.comp_apply]
  refine ⟨fun ⟨u, hu, hx⟩ => ⟨u, hu, ((eUn u ys zs).1 hx).2⟩, fun ⟨u, hu, e⟩ => ⟨u, hu, (eUn u ys zs).2 ⟨?_, e⟩⟩⟩
  have hr : rep (ran pend) u u := by rw [eDp]; exact ⟨rfl, r, hu⟩
  obtain ⟨j, -, hj⟩ := hr
  exact ⟨j, hj⟩

/-- The chain `rep_foldBy` leaves for `perm`: rows `ys[t]` that are `ys[t+1]` with `xs[t]` inserted at some cut,
ending at `[]`, start at exactly the permutations of `xs`. -/
theorem perm_chain {β : Type _} (xs w : List β) :
    (∃ ys : List (List β), ∃ hy : ys.length = xs.length + 1,
      ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm) = [] ∧
      (∀ t (ht : t < xs.length), ∃ a b,
        ys[t+1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm) = a ++ b ∧
        ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) = a ++ xs[t]'ht :: b) ∧
      w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.succ_pos _) hy.symm)) ↔ w.Perm xs := by
  induction xs generalizing w with
  | nil =>
    constructor
    · rintro ⟨ys, hy, hnil, -, rfl⟩
      exact List.Perm.of_eq hnil
    · intro h
      obtain rfl := List.Perm.eq_nil h
      exact ⟨[[]], rfl, rfl, fun t ht => absurd ht (Nat.not_lt_zero _), rfl⟩
  | cons x xs ih =>
    constructor
    · rintro ⟨ys, hy, hnil, hstep, rfl⟩
      rcases ys with _ | ⟨y, ys⟩
      · simp at hy
      have hy' : ys.length = xs.length + 1 := by simp at hy; omega
      have h := (ih (ys[0]'(by omega))).1 ⟨ys, hy', hnil, fun t ht => hstep (t + 1) (by simp; omega), rfl⟩
      obtain ⟨a, b, h1, h0⟩ := hstep 0 (by simp)
      show y.Perm (x :: xs)
      rw [show y = a ++ x :: b from h0]
      exact List.perm_middle.trans (((List.Perm.of_eq h1.symm).trans h).cons x)
    · intro hp
      obtain ⟨a, b, rfl⟩ := List.append_of_mem (hp.mem_iff.2 (List.mem_cons_self (a := x) (l := xs)))
      obtain ⟨ys, hy, hnil, hstep, hw⟩ := (ih (a ++ b)).2 (List.perm_middle.symm.trans hp).cons_inv
      refine ⟨(a ++ x :: b) :: ys, by simp [hy], hnil, fun t ht => ?_, rfl⟩
      cases t with
      | zero => exact ⟨a, b, hw.symm, rfl⟩
      | succ t => exact hstep t (by simp at ht; omega)

section PermFold

open QLean.Dep

/-- **`perm`, read back**: an array `xs` of `X` goes to exactly its permutations. `rep_foldBy` at `perm`'s step
    and the seed `nilVal B`, its chain closed by `perm_chain`. Bound values and hypotheses as `rep_foldBy`'s
    (`step` bound by `hstep`), and `perm_step_rep`'s at every round (`hC`, a per-round bundle `permOK`, each bound
    value with its equation). -/
theorem rep_perm {B : Obj} {n : USize} (X : Vals (.arr B) n)
    (T : Rel .long (.arr B)) (hT : T = num (idU X) 0) (hn : n.toNat < 2 ^ 63)
    (hv : Vals.PickFits (.arr B) X (List.range n.toNat)) (hp : (Rel.val T).1.toNat < 2 ^ 63)
    (hel : ∀ k, k ≤ (Rel.val T).1.toNat → ∀ a : ByteArray, a = whereBits (Rel.n T)
        (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf (Rel.val T)).2 (one k.toUInt64) (Rel.n T)) →
      ∀ pos : ByteArray, pos = Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul
        (gather 8 (add (Rel.n T) (slicesOf (Rel.val T)).1 (slicesOf (Rel.val T)).2) a)
        (one (k + 1).toUInt64) (len a).toUSize →
      Vals.PickFits .long (Rel.key T) ((List.range (len a)).map fun q => (Column.bitsAt a (q * 8) 8).toNat) ∧
      Vals.PickFits B (Rel.val T).2.2.2 ((List.range (len a)).map fun q => (Column.bitsAt pos (q * 8) 8).toNat))
    (pend₀ : Rel .long (.arr B)) (hpend : pend₀ = top (A := .long) (Rel.key T) (nilVal B))
    (hN : (Rel.n T).toNat * (1 : USize).toNat < USize.size)
    (h63 : (Rel.n T).toNat * (1 : USize).toNat < 2 ^ 63)
    (hA : Vals.PickFits .long (Rel.key T)
      ((List.range ((Rel.n T).toNat * (1 : USize).toNat)).map (· / (1 : USize).toNat)))
    (hB : Vals.PickFits (.arr B) (nilVal B)
      ((List.range ((Rel.n T).toNat * (1 : USize).toNat)).map (· % (1 : USize).toNat)))
    (step : Rel .long B → Rel .long (.arr B) → Rel .long (.arr B))
    (hstep : step = fun el pend => let q := pair el (pend ≫ uncat (ran pend).val); let D := ran q;
      q ≫ cat (pair (outl (outr D)) (cons (pair (outl D) (outr (outr D))))))
    (elK : Nat → Rel .long B) (hE : ∀ k, elK k = elR(T, k))
    (f : Rel .long (.arr B) × Rel .long (.arr B) × Nat → Rel .long (.arr B) × Rel .long (.arr B) × Nat)
    (hf : ∀ st, f st = rnd(st))
    (hR : ∀ i (el : Rel .long B) (pend P S : Rel .long (.arr B)), el = elK i →
      pend = (f^[i] (pend₀, Alg.zero, 0)).1 → P = (f^[i] (pend₀, Alg.zero, 0)).2.1 → S = step el pend →
      roundAt((.arr B)))
    (hC : ∀ i, i ≤ (Rel.val T).1.toNat → ∀ (el : Rel .long B) (pend : Rel .long (.arr B)), el = elK i →
      pend = (f^[i] (pend₀, Alg.zero, 0)).1 → permOK)
    (F : Rel .long (.arr B)) (hF : F = foldRows T pend₀ step)
    (jc : Vector Code 2) (hjc : jc = Obj.codes .long ck2(T°, F)) (hjO : codesOK(jc, ck2(T°, F)))
    (hjn : (Rel.n F).toNat < 2 ^ 63) (hjM : msum(jc, T°, F) < 2 ^ 63) (hjU : msum(jc, T°, F) < USize.size)
    (hjA : Vals.PickFits (.arr B) (Rel.key (T°)) ((mpairs(jc, T°, F)).map Prod.fst))
    (hjC : Vals.PickFits (.arr B) (Rel.val F) ((mpairs(jc, T°, F)).map Prod.snd)) :
    ∀ (xs : List B.El) ys, rep (Alg.perm X) xs ys ↔ (∃ i, X.row i = xs) ∧ ys.Perm xs := by
  subst hstep
  intro xs ys
  refine (rep_foldBy (nilVal B) X T hT hn hv hp hel pend₀ hpend hN h63 hA hB
    (fun el pend => let q := pair el (pend ≫ uncat (ran pend).val); let D := ran q;
      q ≫ cat (pair (outl (outr D)) (cons (pair (outl D) (outr (outr D))))))
    (fun _ eu v => ∃ ys zs, eu.2 = ys ++ zs ∧ v = ys ++ eu.1 :: zs) elK hE f hf hR
    (fun i hi => perm_step_rep _ _ (hC i hi _ _ rfl rfl)) F hF jc hjc hjO hjn hjM hjU hjA hjC xs ys).trans ?_
  -- `nilVal B`'s one row is `[]`
  exact and_congr Iff.rfl ((exists_congr fun zs => exists_congr fun _ => and_congr
    ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨⟨0, by simp⟩, h.symm⟩⟩ Iff.rfl).trans (perm_chain xs ys))

end PermFold

/-! ## `suffix` -/

-- every primitive's hypotheses at one round of `suffix`, at its union so far `S` and last arrays `F`: `rep_ran`'s
-- at `F`, `rep_tail`'s at `Dr = ran F`, `rep_comp`'s at `F ≫ tail`, `rep_union_full`'s at `P = S`, `Q = F ≫ tail`
namespace ListN
set_option hygiene false in
scoped notation "sufOK" =>
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
      Vals.PickFits (.arr B) (PQ(.arr B, .arr B)).key (List.range (PQ(.arr B, .arr B)).n.toNat) ∧
      Vals.PickFits (.arr B) (PQ(.arr B, .arr B)).val (List.range (PQ(.arr B, .arr B)).n.toNat))
end ListN
open ListN

/-- **One round of `suffix`, read back**: `F ≫ tail` takes an array to the tail of each array `F` gives it, and the
    union adds those to `S`. Hypotheses: `sufOK`. -/
theorem suffix_round {B : Obj} (S F : Rel (.arr B) (.arr B)) (h : sufOK) :
    (∀ xs ys, rep (F ≫ tail (ran F).val) xs ys ↔ ∃ c, rep F xs (c :: ys)) ∧
    ∀ xs ys, rep (S ∪ F ≫ tail (ran F).val) xs ys ↔ rep S xs ys ∨ ∃ c, rep F xs (c :: ys) := by
  obtain ⟨⟨hDf, hDp⟩, ⟨t63, ht⟩, ⟨hcf, hc⟩, hU⟩ := h _ rfl
  obtain ⟨tK, tH, tT⟩ := ht _ rfl _ rfl _ rfl
  have eT := rep_tail (Rel.val (ran F)) t63 _ rfl _ rfl _ rfl tK tH tT
  obtain ⟨c1, c2, c3, c4, c5⟩ := hc _ rfl
  have eC := rep_comp _ _ (codes_faithful_wf _ _ hcf).1 c1 c2 c3 c4 c5
  have eD := rep_ran_corefl F (one_ok _ hDf) (hDp)
  have e1 : ∀ xs ys, rep (F ≫ tail (ran F).val) xs ys ↔ ∃ c, rep F xs (c :: ys) := by
    intro xs ys
    rw [eC, Freyd.Alg.RelSet.comp_apply]
    constructor
    · rintro ⟨a, ha, ht⟩
      obtain ⟨-, c, rfl⟩ := (eT a ys).1 ht
      exact ⟨c, ha⟩
    · rintro ⟨c, hc⟩
      have hr : rep (ran F) (c :: ys) (c :: ys) := by rw [eD]; exact ⟨rfl, xs, hc⟩
      obtain ⟨j, -, hj⟩ := hr
      exact ⟨c :: ys, hc, (eT _ _).2 ⟨⟨j, hj⟩, c, rfl⟩⟩
  obtain ⟨hN, hNk, hNv, hFk, hFv, hUK, hUV, hUk, hUv⟩ := hU _ rfl _ rfl
  refine ⟨e1, fun xs ys => ?_⟩
  rw [rep_union_full S _ hN hNk hNv hFk hFv (one_ok _ hUK) (one_ok _ hUV) hUk hUv]
  show rep S xs ys ∨ rep _ xs ys ↔ _
  exact or_congr Iff.rfl (e1 xs ys)

/-- **`suffix`, read back**: an array `xs` of `X` goes to exactly its suffixes. Round `i` holds in `F` the arrays
    `drop i xs` (for `i ≤ |xs|`) and in `S` every `drop t xs`, `t ≤ i`; the fuel `X.1 + 1` passes every array's
    length (`arr_row_length`), and a stop at an empty `F` means every array is shorter. The round `g` is bound by
    its defining equation (`hg`); `hR` is `sufOK` at every round up to the payload count. -/
theorem rep_suffix {B : Obj} {n : USize} (X : Vals (.arr B) n)
    (g : Rel (.arr B) (.arr B) × Rel (.arr B) (.arr B) → Rel (.arr B) (.arr B) × Rel (.arr B) (.arr B))
    (hg : ∀ S F, g (S, F) = (S ∪ F ≫ tail (ran F).val, F ≫ tail (ran F).val))
    (hR : ∀ i, i ≤ X.1.toNat → ∀ S F, S = (g^[i] (idU X, idU X)).1 → F = (g^[i] (idU X, idU X)).2 → sufOK) :
    ∀ xs ys, rep (suffix X) xs ys ↔ (∃ j, X.row j = xs) ∧ ys <:+ xs := by
  have hd : ∀ (i : Nat) (xs : List B.El) ys, (∃ c, c :: ys = xs.drop i) ↔ i < xs.length ∧ ys = xs.drop (i + 1) := by
    intro i xs ys
    constructor
    · rintro ⟨c, h⟩
      refine ⟨?_, (congrArg List.tail h).trans (by rw [List.tail_drop])⟩
      have := congrArg List.length h
      simp at this
      omega
    · rintro ⟨hi, rfl⟩
      exact ⟨xs[i], (List.drop_eq_getElem_cons hi).symm⟩
  -- after `i` rounds: `F` is `drop i`, `S` every `drop t`, `t ≤ i`
  have inv : ∀ i, i ≤ X.1.toNat + 1 →
      (∀ xs ys, rep (g^[i] (idU X, idU X)).2 xs ys ↔ (∃ j, X.row j = xs) ∧ i ≤ xs.length ∧ ys = xs.drop i) ∧
      (∀ xs ys, rep (g^[i] (idU X, idU X)).1 xs ys ↔
        (∃ j, X.row j = xs) ∧ ∃ t ≤ i, t ≤ xs.length ∧ ys = xs.drop t) := by
    intro i
    induction i with
    | zero =>
      intro _
      have e : ∀ xs ys, rep (idU X) xs ys ↔ (∃ j, X.row j = xs) ∧ 0 ≤ xs.length ∧ ys = xs.drop 0 :=
        fun xs ys => (idU_holds X xs ys).trans
          ⟨fun ⟨h, hj⟩ => ⟨hj, Nat.zero_le _, h.symm⟩, fun ⟨hj, _, h⟩ => ⟨h.symm, hj⟩⟩
      refine ⟨e, fun xs ys => (e xs ys).trans (and_congr Iff.rfl
        ⟨fun h => ⟨0, Nat.le_refl _, h⟩, fun ⟨t, ht, _, h⟩ => ?_⟩)⟩
      obtain rfl : t = 0 := by omega
      exact ⟨Nat.zero_le _, h⟩
    | succ i ih =>
      intro hi
      obtain ⟨hF, hS⟩ := ih (by omega)
      have hr := suffix_round _ _ (hR i (by omega) _ _ rfl rfl)
      have e : g^[i + 1] (idU X, idU X) = _ := hg (g^[i] (idU X, idU X)).1 (g^[i] (idU X, idU X)).2
      have hF' : ∀ xs ys, (∃ c, rep (g^[i] (idU X, idU X)).2 xs (c :: ys)) ↔
          (∃ j, X.row j = xs) ∧ i + 1 ≤ xs.length ∧ ys = xs.drop (i + 1) := by
        intro xs ys
        constructor
        · rintro ⟨c, h⟩
          obtain ⟨hj, -, h⟩ := (hF _ _).1 h
          obtain ⟨hl, e⟩ := (hd i xs ys).1 ⟨c, h⟩
          exact ⟨hj, hl, e⟩
        · rintro ⟨hj, hl, e⟩
          obtain ⟨c, hc⟩ := (hd i xs ys).2 ⟨hl, e⟩
          exact ⟨c, (hF _ _).2 ⟨hj, by omega, hc⟩⟩
      rw [e]
      refine ⟨fun xs ys => (hr.1 xs ys).trans (hF' xs ys), fun xs ys => (hr.2 xs ys).trans
        ((or_congr (hS xs ys) (hF' xs ys)).trans ?_)⟩
      constructor
      · rintro (⟨hj, t, ht, hl, e⟩ | ⟨hj, hl, e⟩)
        · exact ⟨hj, t, by omega, hl, e⟩
        · exact ⟨hj, i + 1, Nat.le_refl _, hl, e⟩
      · rintro ⟨hj, t, ht, hl, e⟩
        rcases Nat.lt_or_ge t (i + 1) with h | h
        · exact Or.inl ⟨hj, t, by omega, hl, e⟩
        · obtain rfl : t = i + 1 := by omega
          exact Or.inr ⟨hj, hl, e⟩
  obtain ⟨j, hj, he, hs⟩ := iter_stop (fun s : Rel (.arr B) (.arr B) × Rel (.arr B) (.arr B) => s.2.n == 0) g
    (X.1.toNat + 1) (idU X, idU X)
  have hl : suffix X = (g^[j] (idU X, idU X)).1 := by
    rw [← he]
    refine congrArg (fun g' : Rel (.arr B) (.arr B) × Rel (.arr B) (.arr B) →
        Rel (.arr B) (.arr B) × Rel (.arr B) (.arr B) =>
      (iter (X.1.toNat + 1) (fun s => s.2.n == 0) g' (idU X, idU X)).1) (funext fun st => ?_)
    obtain ⟨S, F⟩ := st
    rw [hg S F]
  have hstop : X.1.toNat + 1 ≤ j ∨ ∀ xs ys, ¬ rep (g^[j] (idU X, idU X)).2 xs ys := by
    rcases hs with hs | hs
    · exact Or.inl (by omega)
    · refine Or.inr fun xs ys h => ?_
      obtain ⟨i, -⟩ := h
      have h0 : (g^[j] (idU X, idU X)).2.n = 0 := beq_iff_eq.1 hs
      have h1 : (g^[j] (idU X, idU X)).2.n.toNat = 0 := by rw [h0]; rfl
      exact Nat.not_lt_zero _ (Nat.lt_of_lt_of_eq i.2 h1)
  obtain ⟨hFj, hSj⟩ := inv j hj
  intro xs ys
  rw [hl]
  refine (hSj xs ys).trans (and_congr_right fun ⟨r, hr⟩ => ⟨fun ⟨t, _, _, e⟩ => by
    rw [e]; exact List.drop_suffix .., fun h => ⟨xs.length - ys.length, ?_, by omega, List.suffix_iff_eq_drop.1 h⟩⟩)
  have hx : xs.length ≤ X.1.toNat := by rw [← hr]; exact arr_row_length X r
  rcases hstop with h' | h'
  · omega
  · have : xs.length < j := Nat.lt_of_not_le fun hc => h' xs _ ((hFj xs _).2 ⟨⟨r, hr⟩, hc, rfl⟩)
    omega

/-! ## `snoc` -/

section Snoc
open Pow

namespace ListN
-- `rep_tau_list`'s hypotheses at the side `X` (`n` rows of `A`)
set_option hygiene false in
scoped notation "tauOK(" A ", " cnt ", " X ")" =>
  (((∀ {i j : Nat} (hi : i < (cnt).toNat) (hj : j < (cnt).toNat),
      Column.idAt (kcX(X)).b (kcX(X)).w i = Column.idAt (kcX(X)).b (kcX(X)).w j ↔
        Vals.row X ⟨i, hi⟩ = Vals.row X ⟨j, hj⟩) ∧
    laneOK((kcX(X)).w) ∧
      (kcX(X)).n = cnt ∧ (kcX(X)).b.size = ((kcX(X)).n.toNat * (kcX(X)).w + 7) / 8 ∧
      ((kcX(X)).w < 8 → (kcX(X)).card < USize.size ∧
        ∀ i < (kcX(X)).n.toNat, Column.idAt (kcX(X)).b (kcX(X)).w i < (kcX(X)).card)) ∧
  Vals.PickFits A X (List.range (cnt).toNat) ∧
  (∀ {i j : Nat} (hi : i < (Rel.nub (idU X)).n.toNat) (hj : j < (Rel.nub (idU X)).n.toNat),
    Column.idAt (kcT(idU X)).b (kcT(idU X)).w i = Column.idAt (kcT(idU X)).b (kcT(idU X)).w j ↔
      Vals.row (Rel.nub (idU X)).key ⟨i, hi⟩ = Vals.row (Rel.nub (idU X)).key ⟨j, hj⟩) ∧
  laneOK((kcT(idU X)).w) ∧
  (kcT(idU X)).n = (Rel.nub (idU X)).n ∧
  (kcT(idU X)).b.size = ((kcT(idU X)).n.toNat * (kcT(idU X)).w + 7) / 8 ∧
  A.CodesFit (#v[⟨(Rel.nub (idU X)).n, (Rel.nub (idU X)).val⟩] : Vector (Part A) 1) ∧
  (Rel.nub (idU X)).n.toNat < 2 ^ 63 ∧
  Vals.PickFits A (Rel.nub (idU X)).key (ids (pT(idU X))) ∧
  Vals.PickFits A (Rel.nub (idU X)).val (ids (pT(idU X))) ∧
  Vals.PickFits A (Vals.pickPart A (Rel.nub (idU X)).key (pT(idU X))).2 (ids (loT(idU X))))

-- every primitive's hypotheses in `snoc P`, `P : Rel K (B* × B)`, each piece bound by its equation as `snoc`
-- builds it
set_option hygiene false in
scoped notation "snocOK(" K ", " B ", " P ")" =>
  (oneFit(.prod (.arr B) B, Rel.n P, Rel.val P) ∧
    ∀ D : Rel (.prod (.arr B) B) (.prod (.arr B) B), D = ran P →
    ∀ X : Vals B (Rel.n (outr D)), X = Rel.val (outr D) →
    tauOK(B, Rel.n (outr D), X) ∧ cmpOK(B, outr D, τ X) ∧
    ∀ T : Rel (.prod (.arr B) B) (.arr B), T = outr D ≫ τ X →
    pairOK(.prod (.arr B) B, outl D, T) ∧
    ∀ Q : Rel (.prod (.arr B) B) (.prod (.arr B) (.arr B)), Q = pair (outl D) T →
    cmpOK(.prod (.arr B) B, P, Q) ∧
    ∀ M : Rel K (.prod (.arr B) (.arr B)), M = P ≫ Q → catOK(K, B, M))
end ListN
open ListN

/-- **`snoc`, read back**: a row `(bs, b)` of `P` goes to `bs ++ [b]` and nothing else. `snoc P` is
    `cat (P ≫ ⟨outl D, outr D ≫ τ⟩)`, `D = ran P`; `τ` gives `b` the array `[b]` exactly (`rep_tau_list`).
    Hypotheses: every primitive's at the pieces (`snocOK`): `rep_ran`'s at
    `P`, `rep_tau_list`'s at `(outr D).val`, `rep_comp`'s at `outr D ≫ τ` and at `P ≫ Q`, `rep_pair`'s at `Q`,
    `rep_cat`'s at the result. -/
theorem rep_snoc {K B : Obj} (P : Rel K (.prod (.arr B) B))
    (h : snocOK(K, B, P)) :
    ∀ k ys, rep (snoc P) k ys ↔ ∃ bs b, rep P k (bs, b) ∧ ys = bs ++ [b] := by
  obtain ⟨⟨hPf, hPp⟩, h1⟩ := h
  obtain ⟨ht, ⟨hcf, hc'⟩, h2⟩ := h1 _ rfl _ rfl
  obtain ⟨⟨hqf, hq'⟩, h3⟩ := h2 _ rfl
  obtain ⟨⟨hmf, hm'⟩, h4⟩ := h3 _ rfl
  have hCt := h4 _ rfl
  obtain ⟨c1, c2, c3, c4, c5⟩ := hc' _ rfl
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq' _ rfl
  obtain ⟨m1, m2, m3, m4, m5⟩ := hm' _ rfl
  obtain ⟨hX, hx, hF, hw, hn, hs, hW, h63, hpk, hpv, hlo⟩ := ht
  have eD := rep_ran_corefl P (one_ok _ hPf) (hPp)
  have eτ := rep_tau_list _ hX hx hF hw hn hs hW h63 hpk hpv hlo
  have eT := rep_comp _ _ (codes_faithful_wf _ _ hcf).1 c1 c2 c3 c4 c5
  have eQ := rep_pair _ _ (codes_faithful_wf _ _ hqf).1 q1 q2 q3 q4 q5 q6
  have eM := rep_comp _ _ (codes_faithful_wf _ _ hmf).1 m1 m2 m3 m4 m5
  have eC := rep_cat_ok _ hCt
  -- `D = ran P`: the pairs `P` gives, each to itself
  have hD : ∀ p p', rep (ran P) p p' ↔ p = p' ∧ ∃ k, rep P k p := fun p p' => by rw [eD]; exact Iff.rfl
  -- `outr D ≫ τ`: a pair of `P` to the array of its second part alone
  have hT : ∀ p Y, rep (outr (ran P) ≫ τ (outr (ran P)).val) p Y ↔ (∃ k, rep P k p) ∧ Y = [p.2] := by
    intro p Y
    rw [eT, Freyd.Alg.RelSet.comp_apply]
    constructor
    · rintro ⟨b, hb, hτ⟩
      obtain ⟨y, hy⟩ := (outr_holds (ran P) p b).1 hb
      obtain ⟨rfl, hk⟩ := (hD _ _).1 hy
      exact ⟨hk, ((eτ b Y).1 hτ).2⟩
    · rintro ⟨hk, rfl⟩
      have hb : rep (outr (ran P)) p p.2 := (outr_holds (ran P) p p.2).2 ⟨p.1, (hD _ _).2 ⟨rfl, hk⟩⟩
      obtain ⟨i, -, hi⟩ := id hb
      exact ⟨p.2, hb, (eτ _ _).2 ⟨⟨i, hi⟩, rfl⟩⟩
  intro k ys
  rw [show snoc P = cat (P ≫ pair (outl (ran P)) (outr (ran P) ≫ τ (outr (ran P)).val)) from rfl, eC]
  constructor
  · rintro ⟨xs, Y, hM, rfl⟩
    rw [eM, Freyd.Alg.RelSet.comp_apply] at hM
    obtain ⟨p, hp, hq⟩ := hM
    have hq' : rep (outl (ran P)) p xs ∧ rep (outr (ran P) ≫ τ (outr (ran P)).val) p Y :=
      (Iff.of_eq (congrFun (congrFun eQ p) (xs, Y))).1 hq
    obtain ⟨z, hz⟩ := (outl_holds (ran P) p xs).1 hq'.1
    obtain ⟨rfl, -⟩ := (hD _ _).1 hz
    obtain ⟨-, rfl⟩ := (hT _ _).1 hq'.2
    exact ⟨xs, z, hp, rfl⟩
  · rintro ⟨bs, b, hp, rfl⟩
    refine ⟨bs, [b], ?_, rfl⟩
    rw [eM, Freyd.Alg.RelSet.comp_apply]
    refine ⟨(bs, b), hp, (Iff.of_eq (congrFun (congrFun eQ (bs, b)) (bs, [b]))).2 ⟨?_, (hT _ _).2 ⟨⟨k, hp⟩, rfl⟩⟩⟩
    exact (outl_holds (ran P) (bs, b) bs).2 ⟨b, (hD _ _).2 ⟨rfl, k, hp⟩⟩

#print axioms rep_snoc

end Snoc

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.Rep.rep_cons_ok
#print axioms LeetQ.Rel.Rep.rep_cat_ok
#print axioms LeetQ.Rel.Rep.rep_uncat_ok
#print axioms LeetQ.Rel.Rep.rep_alpha
#print axioms LeetQ.Rel.Rep.rep_tic
#print axioms LeetQ.Rel.Rep.perm_step_set
#print axioms LeetQ.Rel.Rep.perm_step_rep
#print axioms LeetQ.Rel.Rep.perm_chain
#print axioms LeetQ.Rel.Rep.rep_perm
#print axioms LeetQ.Rel.Rep.suffix_round
#print axioms LeetQ.Rel.Rep.rep_suffix
