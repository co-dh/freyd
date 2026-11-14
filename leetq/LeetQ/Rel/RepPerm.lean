/-
  List composites read back: `tic` (`cons`, `inits`, `tail`) and `perm` (`foldBy` at a step built from `uncat`,
  `cat`, `cons`, `pair`), each from its primitives' read-backs.
-/
import LeetQ.Rel.RepEst
import LeetQ.Rel.RepUncat

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

open FoldN Prim

-- `rep_cons`'s hypotheses at `P`, its pieces bound by their equations
set_option hygiene false in
local notation "consOK(" K ", " B ", " P ")" =>
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
local notation "catOK(" K ", " B ", " P ")" =>
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
  have eDp := rep_ran pend (one_ok _ hDf) (hDp _ rfl)
  have eUn := rep_uncat_ok (Rel.val (ran pend)) hUn
  have eU := rep_comp _ _ (codes_faithful_wf _ _ huf).1 u1 u2 u3 u4 u5
  have eq := rep_pair _ _ (codes_faithful_wf _ _ hqf).1 p1 p2 p3 p4 p5 p6
  have eD := rep_ran _ (one_ok _ hdf) (hdp _ rfl)
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

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.Rep.rep_cons_ok
#print axioms LeetQ.Rel.Rep.rep_cat_ok
#print axioms LeetQ.Rel.Rep.rep_uncat_ok
#print axioms LeetQ.Rel.Rep.rep_tic
#print axioms LeetQ.Rel.Rep.perm_step_set
#print axioms LeetQ.Rel.Rep.perm_step_rep
#print axioms LeetQ.Rel.Rep.perm_chain
#print axioms LeetQ.Rel.Rep.rep_perm
