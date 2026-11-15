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
  (Vals.PickFits (.arr B) (Rel.val P).2 (List.range (Rel.n P).toNat) ∧
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
    Vals.RazeFits B tl (Rel.val P).1 ∧
    ∀ hN, Vals.PickFits B (Obj.raze B #[⟨m, tl⟩, ⟨Rel.n P, (Rel.val P).1⟩] hN)
      ((List.range (len g)).map fun q => (Column.bitsAt g (q * 8) 8).toNat))
-- `rep_cat`'s hypotheses at `P`, its pieces bound by their equations
set_option hygiene false in
scoped notation "catOK(" K ", " B ", " P ")" =>
  (Vals.PickFits (.arr B) (Rel.val P).1 (List.range (Rel.n P).toNat) ∧
    Vals.PickFits (.arr B) (Rel.val P).2 (List.range (Rel.n P).toNat) ∧
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
    Vals.RazeFits B ta tb ∧
    ∀ hN, Vals.PickFits B (Obj.raze B #[⟨ma, ta⟩, ⟨mb, tb⟩] hN)
      ((List.range (len g)).map fun q => (Column.bitsAt g (q * 8) 8).toNat))
end ListN
open ListN

/-- `rep_cons` with its hypotheses as the bundle `consOK`. -/
theorem rep_cons_ok {K B : Obj} (P : Rel K (.prod B (.arr B))) (h : consOK(K, B, P)) :
    ∀ k ys, rep (cons P) k ys ↔ ∃ b bs, rep P k (b, bs) ∧ ys = b :: bs := by
  obtain ⟨hV, hs⟩ := h
  obtain ⟨hS, hU, hx⟩ := hs _ rfl
  obtain ⟨hKf, hRf, hFf⟩ := hx _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
  exact rep_cons P hV _ rfl hS hU _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl hKf hRf hFf

/-- `rep_cat` with its hypotheses as the bundle `catOK`. -/
theorem rep_cat_ok {K B : Obj} (P : Rel K (.prod (.arr B) (.arr B))) (h : catOK(K, B, P)) :
    ∀ k zs, rep (cat P) k zs ↔ ∃ xs ys, rep P k (xs, ys) ∧ zs = xs ++ ys := by
  obtain ⟨hVa, hVb, h1⟩ := h
  obtain ⟨hS, hU, h2⟩ := h1 _ rfl _ rfl
  obtain ⟨hKf, hRf, hFf⟩ :=
    h2 _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
  exact rep_cat P hVa hVb _ rfl _ rfl hS hU _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
    _ rfl _ rfl _ rfl _ rfl hKf hRf hFf

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
  rw [show alpha I P = junc (nil I) (cons (idU P)) from rfl, rep_junc_full _ _ hN h63 hF, ← rep_idU P]
  congr 1
  · refine hom_ext fun u xs => (rep_nil I u xs).trans ⟨?_, ?_⟩
    · rintro ⟨h, rfl⟩; exact ⟨u, ⟨rfl, h⟩, rfl⟩
    · rintro ⟨v, ⟨rfl, h⟩, rfl⟩; exact ⟨h, rfl⟩
  · refine hom_ext fun p ys => (rep_cons_ok _ hc p ys).trans ⟨?_, ?_⟩
    · rintro ⟨b, bs, h, rfl⟩; exact ⟨(b, bs), h, rfl⟩
    · rintro ⟨⟨b, bs⟩, h, rfl⟩; exact ⟨b, bs, h, rfl⟩

/-! ## `tic` -/

open Freyd Freyd.Alg Freyd.Alg.RelSet in
/-- **`tic`, read back**: a row `(b, bs)` of `P` goes to the non-empty prefixes of `b :: bs`, shortest first.
    `tic P` is `I ≫ tail I.val`, `I = C ≫ inits C.val`, `C = cons P` (bound by `hC`, `hI`). Hypotheses:
    `rep_cons`'s at `P` (`hc`), `rep_comp`'s at `I` (`h1`) and at the result (`h2`), `rep_inits`'s at `C.val`
    (`hi`), `rep_tail`'s at `I.val` (`ht`). -/
theorem tic_of {K B : Obj} (P : Rel K (.prod B (.arr B))) (C : Rel K (.arr B)) (hC : C = cons P)
    (I : Rel K (.arr (.arr B))) (hI : I = C ≫ inits (Rel.val C))
    (eC : ∀ k ys, rep (cons P) k ys ↔ ∃ b bs, rep P k (b, bs) ∧ ys = b :: bs)
    (e1 : rep (C ≫ inits (Rel.val C)) = rep C ≫ rep (inits (Rel.val C)))
    (eN : ∀ xs yss, rep (inits (Rel.val C)) xs yss ↔ (∃ j, (Rel.val C).row j = xs) ∧
      yss = (List.range (xs.length + 1)).map fun k => xs.take k)
    (e2 : rep (I ≫ tail (Rel.val I)) = rep I ≫ rep (tail (Rel.val I)))
    (eT : ∀ xs bs, rep (tail (Rel.val I)) xs bs ↔ (∃ j, (Rel.val I).row j = xs) ∧ ∃ b, xs = b :: bs) :
    ∀ k zss, rep (tic P) k zss ↔ ∃ b bs, rep P k (b, bs) ∧
      zss = (List.range (bs.length + 1)).map fun j => (b :: bs).take (j + 1) := by
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
  -- generic `A`: the nub copies `X`'s cells, whose dictionaries, general cells, nested payloads no `X` fact bounds
  Obj.CodesFit A (#v[⟨(Rel.nub (idU X)).n, (Rel.nub (idU X)).key⟩] : Vector (Part A) 1) ∧
  Obj.CodesFit A (#v[⟨(Rel.nub (idU X)).n, (Rel.nub (idU X)).val⟩] : Vector (Part A) 1) ∧
  (cnt).toNat < 2 ^ 63)

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
  obtain ⟨c1, c2, c3, c4⟩ := hc' _ rfl
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq' _ rfl
  obtain ⟨m1, m2, m3, m4⟩ := hm' _ rfl
  obtain ⟨hX, hx, hWk, hW, h63⟩ := ht
  have eD := rep_ran_corefl P (one_ok _ hPf) (hPp)
  have eτ := rep_tau_list _ hX hx hWk hW h63
  have eT := rep_comp _ _ (codes_faithful_wf _ _ hcf).1 c1 c2 c3 c4
  have eQ := rep_pair _ _ (codes_faithful_wf _ _ hqf).1 q1 q2 q3 q4 q5
  have eM := rep_comp _ _ (codes_faithful_wf _ _ hmf).1 m1 m2 m3 m4
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
  -- `transposeC`'s `.1` named, so the goal closes syntactically: a defeq check through it evaluates `cat`
  have ht : ∀ R : Rel B B, (transposeC R).1 = transpose R := fun _ => rfl
  rw [show snoc P = cat (P ≫ pair (outl (ran P)) (outr (ran P) ≫ τ (outr (ran P)).val)) by
    unfold snoc snocC ranC ran τ cat; dsimp only; rw [ht]; rfl, eC]
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
#print axioms LeetQ.Rel.Rep.rep_alpha
#print axioms LeetQ.Rel.Rep.perm_step_set
#print axioms LeetQ.Rel.Rep.perm_chain
