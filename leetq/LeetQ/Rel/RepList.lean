/-
  The array ops of `Alg` read back: `cons°` (`uncons`), `cons`, and the folds over arrays built from them.
-/
import LeetQ.Rel.RepFold
import LeetQ.Rel.KernelWF.PlaceSpec

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

/-- A `valCol` long is its `Ew.val` payload's long. -/
theorem valCol_get {m : USize} (op sh : UInt8) (a b : ByteArray) (q : Fin m.toNat) :
    (valCol (n := m) op sh a b).get q = (Column.bitsAt (Kernel.Ew.val op Ew.i64 sh nul a b m) (q.1 * 8) 8).toInt64 := by
  rw [Arr.get_long_bytes _ rfl]

/-- `Ew.val add` of two longs read as an `Int`: their natural sum, both and the sum below `2^63`. -/
theorem addStep_toInt {x y : UInt64} (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63) (h : x.toNat + y.toNat < 2 ^ 63) :
    (Ew.valStep Ew.add Ew.i64 nul.toUInt64 x y).toInt64.toInt = ((x.toNat + y.toNat : Nat) : Int) := by
  rw [(valStep_add_sub hx hy).1 h]; exact Int64.toInt_ofNat_of_lt h

-- row `q`'s start and count in `X`, at its row `i[q]`
set_option hygiene false in
local notation "Lq" => (Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat
set_option hygiene false in
local notation "Cq" => (Column.bitsAt (slicesOf X).2 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat

/-- **`cons°`, read back**: an array of `X` goes to `(b, bs)` exactly when it is `b :: bs`. The non-empty rows
    (`i`), their starts (`l`) and the tails before `Vals.compact` (`T`) are bound by their equations.
    Hypotheses: the payload count below `2^63`, `Vals.PickFits` where `X`, its payload and `T` are picked. -/
theorem rep_uncons {B : Obj} {n : USize} (X : Vals (.arr B) n) (hp : X.1.toNat < 2 ^ 63)
    (i : ByteArray) (hi : i = whereBits n (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf X).2 (one 0) n))
    (l : ByteArray) (hl : l = gather 8 (slicesOf X).1 i)
    (T : Vals (.arr B) (len i).toUSize)
    (hT : T = ⟨X.1, valCol Ew.add Ew.va l (one 1), valCol Ew.add Ew.vv l (gather 8 (slicesOf X).2 i), X.2.2.2⟩)
    (hKf : Vals.PickFits (.arr B) X ((List.range (len i)).map fun q => (Column.bitsAt i (q * 8) 8).toNat))
    (hHf : Vals.PickFits B X.2.2.2 ((List.range (len i)).map fun q => (Column.bitsAt l (q * 8) 8).toNat))
    (hTf : Vals.PickFits (.arr B) T
      ((List.range (len i)).map fun q => (Column.bitsAt (tilLongs (len i).toUSize) (q * 8) 8).toNat)) :
    ∀ (xs : List B.El) b bs, rep (uncons X) xs (b, bs) ↔ (∃ j, X.row j = xs) ∧ xs = b :: bs := by
  intro xs b bs
  have hlen : len i < USize.size := by
    rw [hi]; exact Nat.lt_of_le_of_lt (len_whereBits_le _ _) n.toNat_lt_size
  have hm : ((len i).toUSize).toNat = len i := USize.toNat_ofNat_of_lt' hlen
  have hR := fun j (hj : j < n.toNat) => slicesOf_row X hp hj
  have hA := whereGt_ids n (slicesOf X).2 (k := 0) (by decide) fun j hj => by have := (hR j hj).1; omega
  rw [show Nat.toUInt64 0 = 0 from rfl, ← hi] at hA
  have hmem : ∀ j, j ∈ QLean.Verify.ids i ↔
      j < n.toNat ∧ 0 < (Column.bitsAt (slicesOf X).2 (j * 8) 8).toNat := fun j => by
    rw [hA, List.mem_filter, List.mem_range, decide_eq_true_iff]
  have hs1 : len (slicesOf X).1 = n.toNat := (len_slices _ _ _ _).1
  have hs2 : len (slicesOf X).2 = n.toNat := (len_slices _ _ _ _).2
  -- row `q` of the result: the array `X.row i[q]`, its head and its compacted tail
  have hq : ∀ (q : Nat) (hq : q < len i) (h1 : len i = ((len i).toUSize).toNat)
      (h2 : len l = ((len i).toUSize).toNat),
      ∃ hj : (Column.bitsAt i (q * 8) 8).toNat < n.toNat,
        Vals.row (Vals.pick (.arr B) X i _ h1) ⟨q, by omega⟩ = X.row ⟨_, hj⟩ ∧
        X.row ⟨_, hj⟩ = Vals.row (Vals.pick B X.2.2.2 l _ h2) ⟨q, by omega⟩ ::
          Vals.row (Vals.compact (.arr B) T) ⟨q, by omega⟩ := by
    intro q hq h1 h2
    have qb : q < ((len i).toUSize).toNat := by omega
    have hin : (Column.bitsAt i (q * 8) 8).toNat ∈ QLean.Verify.ids i := by
      have hq' : q < (QLean.Verify.ids i).length := by rw [← len_eq_ids]; exact hq
      rw [← ids_getElem hq']; exact List.getElem_mem hq'
    obtain ⟨hj, hc⟩ := (hmem _).1 hin
    obtain ⟨hLC, hln, hget⟩ := hR _ hj
    have hlq : Column.bitsAt l (q * 8) 8 =
        Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8 := by
      rw [hl]; exact gather8_get hq (by rw [hs1]; exact hj)
    have hcq : Column.bitsAt (gather 8 (slicesOf X).2 i) (q * 8) 8 =
        Column.bitsAt (slicesOf X).2 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8 :=
      gather8_get hq (by rw [hs2]; exact hj)
    have hlqN := congrArg UInt64.toNat hlq
    refine ⟨hj, by rw [pick_row (.arr B) X i _ h1 (by rw [← h1]; exact hKf), dif_pos hj], ?_⟩
    have eT : ∀ (a : Nat) (ha : a < ((len i).toUSize).toNat), a = q → T.row ⟨a, ha⟩ = T.row ⟨q, qb⟩ := by
      intro a ha e; subst e; rfl
    rw [pick_row B X.2.2.2 l _ h2 (by rw [← h1]; exact hHf),
      dif_pos (show (Column.bitsAt l (q * 8) 8).toNat < X.1.toNat by omega),
      show Vals.compact (.arr B) T = Vals.pick (.arr B) T (tilLongs _) _ (len_tilLongs _) from rfl,
      pick_row (.arr B) T (tilLongs _) _ (len_tilLongs _) (by rw [← h1]; exact hTf),
      dif_pos (show (Column.bitsAt (tilLongs (len i).toUSize) (q * 8) 8).toNat < ((len i).toUSize).toNat by
        rw [tilLongs_get qb]; exact qb),
      eT _ _ (tilLongs_get qb)]
    subst hT
    have hlo : ((valCol (n := (len i).toUSize) Ew.add Ew.va l (one 1)).get ⟨q, qb⟩).toInt =
        (((Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat + 1 : Nat) : Int) := by
      rw [valCol_get, val_va_get _ _ _ _ qb, bitsAt_one, hlq]
      exact addStep_toInt (by omega) (by decide) (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)
    have hhi : ((valCol (n := (len i).toUSize) Ew.add Ew.vv l (gather 8 (slicesOf X).2 i)).get ⟨q, qb⟩).toInt =
        (((Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat +
          (Column.bitsAt (slicesOf X).2 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat : Nat) : Int) := by
      rw [valCol_get, val_vv_get _ _ _ _ qb, hlq, hcq]
      exact addStep_toInt (by omega) (by omega) (by omega)
    have hrow := arr_row (b := B) (⟨X.1, valCol (n := (len i).toUSize) Ew.add Ew.va l (one 1),
      valCol Ew.add Ew.vv l (gather 8 (slicesOf X).2 i), X.2.2.2⟩ : Vals (.arr B) (len i).toUSize) ⟨q, qb⟩
    dsimp only at hrow
    rw [hlo, hhi] at hrow
    have e1 : min (max ((Lq + 1 : Nat) : Int) 0).toNat X.1.toNat = Lq + 1 := by omega
    have e2 : min (max ((Lq + Cq : Nat) : Int) 0).toNat X.1.toNat = Lq + Cq := by omega
    rw [e1, e2] at hrow
    rw [hrow]
    apply List.ext_getElem
    · rw [hln, List.length_cons, List.length_map, List.length_range]; omega
    · intro t h1' h2'
      cases t with
      | zero =>
        rw [hget 0 h1' (by omega), List.getElem_cons_zero]
        exact congrArg (Vals.row X.2.2.2) (Fin.ext (show Lq + 0 = (Column.bitsAt l (q * 8) 8).toNat by omega))
      | succ t =>
        rw [hget (t + 1) h1' (by omega), List.getElem_cons_succ, List.getElem_map, List.getElem_range,
          dif_pos (show Lq + 1 + t < X.1.toNat by omega)]
        exact congrArg (Vals.row X.2.2.2) (Fin.ext (show Lq + (t + 1) = Lq + 1 + t by omega))
  subst hi hl
  unfold uncons
  dsimp only
  rw [longCount_eq _ _ _ hlen]
  show (∃ q, _ ∧ _) ↔ _
  constructor
  · rintro ⟨⟨q, hq'⟩, hr, hv⟩
    obtain ⟨hj, hK, hV⟩ := hq q (Nat.lt_of_lt_of_eq hq' hm) hm.symm (by rw [gather_len]; exact hm.symm)
    subst hT
    refine ⟨⟨_, hK.symm.trans hr⟩, ?_⟩
    rw [← hr, hK, hV]
    exact congr (congrArg List.cons (congrArg Prod.fst hv)) (congrArg Prod.snd hv)
  · rintro ⟨⟨⟨j, hj⟩, hx⟩, rfl⟩
    have hc : 0 < (Column.bitsAt (slicesOf X).2 (j * 8) 8).toNat := by
      rw [← (hR j hj).2.1, hx]; exact Nat.zero_lt_succ _
    obtain ⟨q, hq', hqe⟩ := List.getElem_of_mem ((hmem j).2 ⟨hj, hc⟩)
    rw [ids_getElem hq'] at hqe
    have hq'' := Nat.lt_of_lt_of_eq hq' (len_eq_ids _).symm
    obtain ⟨hj', hK, hV⟩ := hq q hq'' hm.symm (by rw [gather_len]; exact hm.symm)
    subst hqe hT
    refine ⟨⟨q, Nat.lt_of_lt_of_eq hq'' hm.symm⟩, hK.trans hx, ?_⟩
    have e := hV.symm.trans hx
    exact Prod.ext (List.cons.inj e).1 (List.cons.inj e).2

/-- An `Ew.val` payload on longs holds exactly its longs (`val_spec`). -/
theorem val_size_len (op sh : UInt8) (a b : ByteArray) (n : USize) :
    (Kernel.Ew.val op Ew.i64 sh nul a b n).size = len (Kernel.Ew.val op Ew.i64 sh nul a b n) * 8 := by
  have h := (val_spec op Ew.i64 sh nul a b n).1
  have hw : Kernel.Ew.width Ew.i64 = 8 := by decide
  rw [hw] at h; rw [len_val, h]; omega

/-- `valStep` adding the long `1` to a long whose successor is below `2^63`: its successor. -/
theorem addOne_toNat {x : UInt64} (hx : x.toNat + 1 < 2 ^ 63) :
    (Ew.valStep Ew.add Ew.i64 nul.toUInt64 x (Nat.toUInt64 1)).toNat = x.toNat + 1 := by
  have h1 : (Nat.toUInt64 1).toNat = 1 := rfl
  have hy : (Nat.toUInt64 1).toNat < 2 ^ 63 := by rw [h1]; decide
  rw [(valStep_add_sub (by omega) hy).1 (by omega), UInt64.toNat_ofNat_of_lt'
    (Nat.lt_of_lt_of_le (show x.toNat + (Nat.toUInt64 1).toNat < 2 ^ 63 by omega) (by decide)), h1]

-- row `r`'s count and start in `P`'s arrays, the counts before row `r`, and `P`'s row count
set_option hygiene false in
local notation "cnt(" r ")" => (Column.bitsAt (slicesOf (Rel.val P).2).2 (r * 8) 8).toNat
set_option hygiene false in
local notation "st(" r ")" => (Column.bitsAt (slicesOf (Rel.val P).2).1 (r * 8) 8).toNat
set_option hygiene false in
local notation "pre(" r ")" => ((List.range r).map fun u => (Column.bitsAt (slicesOf (Rel.val P).2).2 (u * 8) 8).toNat).sum
set_option hygiene false in
local notation "nN" => (Rel.n P).toNat

/-- **`cons`, read back**: a row `(b, bs)` of `P` goes to the array `b :: bs`, under its key. The pieces `cons`
    computes are bound by their equations: the slices `s` of `P`'s arrays, `expand`'s index and rank columns
    `xi`, `xr` (at `m` copies), the tails' payload rows `j` and the tails `tl`, the counts plus one `c1`, their
    running ends `hi` and starts `lo`, the tails' places `dst` and the grade `g` that lays the cells out.
    Hypotheses: the payload count below `2^63`; the counts plus one per row summed below `2^63` and a `USize`;
    `Vals.PickFits` where the key, the payload and the razed cells are picked, `Vals.RazeFits` of the tails and
    the heads. -/
theorem rep_cons {K B : Obj} (P : Rel K (.prod B (.arr B))) (hp : (Rel.val P).2.1.toNat < 2 ^ 63)
    (s : ByteArray × ByteArray) (hs : s = slicesOf (Rel.val P).2)
    (hS : ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt s.2 (r * 8) 8).toNat).sum + (Rel.n P).toNat <
      2 ^ 63)
    (hU : ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt s.2 (r * 8) 8).toNat).sum + (Rel.n P).toNat <
      USize.size)
    (xi : ByteArray) (hxi : xi = expandBytes 8 0 (tilLongs (Rel.n P)) s.2)
    (m : USize) (hm : m = (len xi).toUSize)
    (xr : ByteArray) (hxr : xr = sub m (tilLongs m) (gather 8 (sub (Rel.n P) (sums (Rel.n P) s.2) s.2) xi))
    (j : ByteArray) (hj : j = add m (gather 8 s.1 xi) xr)
    (hjl : len j = m.toNat) (tl : Vals B m) (htl : tl = Vals.pick B (Rel.val P).2.2.2.2 j m hjl)
    (c1 : ByteArray) (hc1 : c1 = addc (Rel.n P) s.2 1) (hi : ByteArray) (hhi : hi = sums (Rel.n P) c1)
    (lo : ByteArray) (hlo : lo = sub (Rel.n P) hi c1)
    (dst : ByteArray) (hdst : dst = addc m (add m (gather 8 lo xi) xr) 1)
    (g : ByteArray) (hg : g = (Code.ofLongs (concatBytes #[dst, lo])).grade)
    (hKf : Vals.PickFits K (Rel.key P)
      ((List.range (Rel.n P).toNat).map fun q => (Column.bitsAt (tilLongs (Rel.n P)) (q * 8) 8).toNat))
    (hTf : Vals.PickFits B (Rel.val P).2.2.2.2 ((List.range m.toNat).map fun q => (Column.bitsAt j (q * 8) 8).toNat))
    (hRf : Vals.RazeFits B tl (Rel.val P).1)
    (hFf : ∀ hN, Vals.PickFits B (Obj.raze B #[⟨m, tl⟩, ⟨Rel.n P, (Rel.val P).1⟩] hN)
      ((List.range (len g)).map fun q => (Column.bitsAt g (q * 8) 8).toNat)) :
    ∀ k ys, rep (cons P) k ys ↔ ∃ b bs, rep P k (b, bs) ∧ ys = b :: bs := by
  subst hs
  have hs1 : len (slicesOf (Rel.val P).2).1 = nN := (len_slices _ _ _ _).1
  have hs2 : len (slicesOf (Rel.val P).2).2 = nN := (len_slices _ _ _ _).2
  have hR := fun r (hr : r < nN) => slicesOf_row (Rel.val P).2 hp hr
  have hpre_le : ∀ a b, a ≤ b → pre(a) ≤ pre(b) := fun a b h => sum_range_le _ h
  have hpre_succ : ∀ r, pre(r + 1) = pre(r) + cnt(r) := fun r => sum_range_succ' _ r
  have hcl : ∀ r, r < nN → cnt(r) + 1 < 2 ^ 63 := fun r hr => by
    have := hpre_le (r + 1) nN (by omega); rw [hpre_succ] at this; omega
  -- the counts plus one, their running ends and starts: row `r`'s new array is `[pre(r) + r, pre(r+1) + r + 1)`
  have hc1g : ∀ r, r < nN → (Column.bitsAt c1 (r * 8) 8).toNat = cnt(r) + 1 := fun r hr => by
    rw [hc1, addc, val_va_get _ _ _ _ hr, bitsAt_one, addOne_toNat (hcl r hr)]
  have hc1l : len c1 = nN := by rw [hc1, addc, len_val]
  have hc1sum : ∀ r, r ≤ nN →
      ((List.range r).map fun u => (Column.bitsAt c1 (u * 8) 8).toNat).sum = pre(r) + r := by
    intro r
    induction r with
    | zero => intro _; simp
    | succ r ih => intro hr; simp only [sum_range_succ']; rw [ih (by omega), hc1g r (by omega)]; omega
  have hhig : ∀ r, r < nN → (Column.bitsAt hi (r * 8) 8).toNat = pre(r + 1) + (r + 1) := fun r hr => by
    have e := hc1sum (r + 1) (by omega)
    have hb := hpre_le (r + 1) nN (by omega)
    rw [hhi, sums_get (b := c1) hr (by rw [hc1l]; exact hr) (by rw [e]; omega), e]
  have hlog : ∀ r, r < nN → (Column.bitsAt lo (r * 8) 8).toNat = pre(r) + r := fun r hr => by
    have := hhig r hr; have := hc1g r hr; have := hpre_succ r; have := hpre_le (r + 1) nN (by omega)
    rw [hlo, sub_get (a := hi) (b := c1) hr (by omega) (by omega)]; omega
  have hlol : len lo = nN := by rw [hlo, sub, len_val]
  -- `expand`: copy `d` is cell `d - pre(r)` of row `r = xi[d]`
  have hI := expand_idx (n := Rel.n P) (cnt := (slicesOf (Rel.val P).2).2) (by omega)
    (fun t ht => by have := hcl t (by omega); omega)
  rw [← hxi, hs2] at hI
  have hxl : len xi = pre(nN) := by
    rw [len_eq_ids, hI, List.length_flatMap]; simp only [List.length_replicate]
  have hxU : len xi < USize.size := by omega
  have hmN : m.toNat = len xi := by rw [hm]; exact USize.toNat_ofNat_of_lt' hxU
  have hxi_at : ∀ d, d < len xi → ∃ r, r < nN ∧ (Column.bitsAt xi (d * 8) 8).toNat = r ∧ pre(r) ≤ d ∧
      d < pre(r) + cnt(r) := by
    intro d hd
    obtain ⟨t, ht, h1, h2, h3⟩ := flatMap_get (fun t => List.replicate cnt(t) t) nN d
      (by simp only [List.length_replicate]; omega)
    simp only [List.length_replicate] at h1 h2 h3
    rw [List.getElem?_replicate, if_pos (by omega)] at h3
    have hpl : d < ((List.range nN).flatMap fun t => List.replicate cnt(t) t).length := by
      rw [← hI, ← len_eq_ids]; exact hd
    refine ⟨t, ht, ?_, h1, h2⟩
    rw [ids_get hI hpl]; rw [List.getElem?_eq_getElem hpl] at h3; exact Option.some.inj h3
  have hxi_in : ∀ r t, r < nN → t < cnt(r) → (Column.bitsAt xi ((pre(r) + t) * 8) 8).toNat = r := by
    intro r t hr ht
    have h := flatMap_get_at (fun t => List.replicate cnt(t) t) hr (q := t)
      (by simp only [List.length_replicate]; exact ht)
    simp only [List.length_replicate, List.getElem?_replicate, ht, ↓reduceIte] at h
    have hpl : pre(r) + t < ((List.range nN).flatMap fun t => List.replicate cnt(t) t).length := by
      rw [← hI, ← len_eq_ids, hxl]; have := hpre_le (r + 1) nN (by omega); rw [hpre_succ] at this; omega
    rw [ids_get hI hpl]; rw [List.getElem?_eq_getElem hpl] at h; exact Option.some.inj h
  have hxrg : ∀ d, d < len xi → (Column.bitsAt xr (d * 8) 8).toNat = d - pre((Column.bitsAt xi (d * 8) 8).toNat) := by
    intro d hd
    have := expand_rank (n := Rel.n P) (cnt := (slicesOf (Rel.val P).2).2) (by omega) (by rw [hs2]; omega)
      (by rw [← hxi]; exact hxU) (p := d) (by rw [← hxi]; exact hd)
    rw [← hxi, ← hm, ← hxr] at this
    exact this
  -- copy `d` of row `r`: its tail cell in `P`'s payload (`j`) and its place in the new payload (`dst`)
  have hD : ∀ d, d < len xi → ∃ r, r < nN ∧ pre(r) ≤ d ∧ d < pre(r) + cnt(r) ∧
      (Column.bitsAt xi (d * 8) 8).toNat = r ∧ (Column.bitsAt j (d * 8) 8).toNat = st(r) + (d - pre(r)) ∧
      (Column.bitsAt dst (d * 8) 8).toNat = pre(r) + r + 1 + (d - pre(r)) := by
    intro d hd
    obtain ⟨r, hr, hxe, h1, h2⟩ := hxi_at d hd
    have hrk := hxrg d hd; rw [hxe] at hrk
    have hdm : d < m.toNat := by omega
    obtain ⟨hLC, -, -⟩ := hR r hr
    have hgs : Column.bitsAt (gather 8 (slicesOf (Rel.val P).2).1 xi) (d * 8) 8 =
        Column.bitsAt (slicesOf (Rel.val P).2).1 (r * 8) 8 := by
      rw [gather8_get (src := (slicesOf (Rel.val P).2).1) hd (by rw [hxe, hs1]; exact hr), hxe]
    have hgl : Column.bitsAt (gather 8 lo xi) (d * 8) 8 = Column.bitsAt lo (r * 8) 8 := by
      rw [gather8_get (src := lo) hd (by rw [hxe, hlol]; exact hr), hxe]
    have hl := hlog r hr
    have hpN := hpre_le (r + 1) nN (by omega); rw [hpre_succ] at hpN
    have hjd : (Column.bitsAt j (d * 8) 8).toNat = st(r) + (d - pre(r)) := by
      rw [hj, add_get (a := gather 8 (slicesOf (Rel.val P).2).1 xi) (b := xr) hdm (by rw [hgs, hrk]; omega), hgs, hrk]
    refine ⟨r, hr, h1, h2, hxe, hjd, ?_⟩
    have hsum := add_get (n := m) (a := gather 8 lo xi) (b := xr) hdm (by rw [hgl, hrk]; omega)
    rw [hgl, hrk, hl] at hsum
    rw [hdst, addc, val_va_get _ _ _ _ hdm, bitsAt_one,
      addOne_toNat (x := Column.bitsAt (add m (gather 8 lo xi) xr) (d * 8) 8) (by rw [hsum]; omega), hsum]
    omega
  -- the destinations then the starts: `cons`' grade lays the cells out by them
  have hdl : len dst = len xi := by rw [hdst, addc, len_val, hmN]
  have hd8 : dst.size = len dst * 8 := by rw [hdst, addc]; exact val_size_len ..
  have hl8 : lo.size = len lo * 8 := by rw [hlo, sub]; exact val_size_len ..
  have hbl : len (concatBytes #[dst, lo]) = len xi + nN := by
    have e : concatBytes #[dst, lo] = dst ++ lo := by simp [concatBytes]
    rw [e]; simp only [len, ByteArray.size_append] at hd8 hl8 hdl hlol ⊢; omega
  have hbg : ∀ d, (Column.bitsAt (concatBytes #[dst, lo]) (d * 8) 8).toNat =
      if d < len xi then (Column.bitsAt dst (d * 8) 8).toNat else (Column.bitsAt lo ((d - len xi) * 8) 8).toNat := by
    intro d; rw [concat2_get hd8, hdl]; split <;> rfl
  -- every value: a start `pre(r) + r` (`d ≥ len xi`) or a tail place `pre(r) + r + 1 + t`, `t < cnt(r)`
  have hval : ∀ d, d < len xi + nN → ∃ r t, r < nN ∧ t ≤ cnt(r) ∧
      (Column.bitsAt (concatBytes #[dst, lo]) (d * 8) 8).toNat = pre(r) + r + t ∧
      (d < len xi ↔ 0 < t) ∧ (d < len xi → t = 1 + (d - pre(r)) ∧ pre(r) ≤ d) ∧ (len xi ≤ d → d = len xi + r) := by
    intro d hd
    by_cases h : d < len xi
    · obtain ⟨r, hr, h1, h2, -, -, hdd⟩ := hD d h
      exact ⟨r, 1 + (d - pre(r)), hr, by omega, by rw [hbg, if_pos h, hdd]; omega, iff_of_true h (by omega),
        fun _ => ⟨rfl, h1⟩, fun h' => absurd h (by omega)⟩
    · have hl := hlog (d - len xi) (by omega)
      exact ⟨d - len xi, 0, by omega, by omega, by rw [hbg, if_neg h, hl]; omega, iff_of_false h (by omega),
        fun h' => absurd h' h, fun _ => by omega⟩
  have hblk : ∀ r, r < nN → pre(r) + r < pre(r + 1) + (r + 1) := fun r _ => by rw [hpre_succ]; omega
  have hinj : ∀ a b, a < len (concatBytes #[dst, lo]) → b < len (concatBytes #[dst, lo]) →
      Column.bitsAt (concatBytes #[dst, lo]) (a * 8) 8 = Column.bitsAt (concatBytes #[dst, lo]) (b * 8) 8 →
      a = b := by
    intro a b ha hb e
    rw [hbl] at ha hb
    obtain ⟨r, t, hr, ht, ea, ia, ta, da⟩ := hval a ha
    obtain ⟨r', t', hr', ht', eb, ib, tb, db⟩ := hval b hb
    have e' := congrArg UInt64.toNat e
    rw [ea, eb] at e'
    obtain ⟨rfl, rfl⟩ := block_inj (P := fun r => pre(r) + r) hblk r t r' t' hr hr'
      (by have := hpre_succ r; dsimp only; omega) (by have := hpre_succ r'; dsimp only; omega) e'
    by_cases h : a < len xi
    · have h' := ia.1 h; obtain ⟨t1, t2⟩ := ta h
      obtain ⟨t3, t4⟩ := tb (ib.2 h'); omega
    · have h' : ¬ b < len xi := fun hb' => h (ia.2 (ib.1 hb'))
      rw [da (by omega), db (by omega)]
  have hpN : pre(nN) + nN = len (concatBytes #[dst, lo]) := by rw [hbl, hxl]
  obtain ⟨hgl, hgk, hglt⟩ : ∃ hgl : (ids g).length = len (concatBytes #[dst, lo]),
      (∀ d (hd : d < len (concatBytes #[dst, lo])), (Column.bitsAt (concatBytes #[dst, lo])
        ((ids g)[d]'(Nat.lt_of_lt_of_eq hd hgl.symm) * 8) 8).toNat = d) ∧
      ∀ d (hd : d < len (concatBytes #[dst, lo])),
        (ids g)[d]'(Nat.lt_of_lt_of_eq hd hgl.symm) < len (concatBytes #[dst, lo]) := by
    subst hg
    exact grade_ofLongs_inv (concatBytes #[dst, lo]) (by omega) (by omega)
      (fun d hd => by
        rw [hbl] at hd
        obtain ⟨r, t, hr, ht, ea, -, -, -⟩ := hval d hd
        have := hpre_le (r + 1) nN (by omega); rw [hpre_succ] at this
        rw [ea, ← hpN]; omega) hinj
  -- the grade at a start is that row's head, at a tail place that tail cell
  have hgx : ∀ x d (hx : x < len (concatBytes #[dst, lo])), d < len (concatBytes #[dst, lo]) →
      (Column.bitsAt (concatBytes #[dst, lo]) (d * 8) 8).toNat = x →
      (ids g)[x]'(Nat.lt_of_lt_of_eq hx hgl.symm) = d := by
    intro x d hx hd e
    refine hinj _ _ (hglt x hx) hd (UInt64.toNat_inj.1 ?_)
    rw [hgk x hx, e]
  have hgh : ∀ r (hr : r < nN), (ids g)[pre(r) + r]'(by
      have := hpre_le (r + 1) nN (by omega); rw [hpre_succ] at this; rw [hgl]; omega) = len xi + r := by
    intro r hr
    have := hpre_le (r + 1) nN (by omega); rw [hpre_succ] at this
    refine hgx (pre(r) + r) (len xi + r) (by omega) (by omega) ?_
    rw [hbg, if_neg (show ¬ len xi + r < len xi by omega), Nat.add_sub_cancel_left, hlog r hr]
  have hgt : ∀ r t (hr : r < nN) (ht : t < cnt(r)), (ids g)[pre(r) + r + 1 + t]'(by
      have := hpre_le (r + 1) nN (by omega); rw [hpre_succ] at this; rw [hgl]; omega) = pre(r) + t := by
    intro r t hr ht
    have := hpre_le (r + 1) nN (by omega); rw [hpre_succ] at this
    refine hgx (pre(r) + r + 1 + t) (pre(r) + t) (by omega) (by omega) ?_
    rw [hbg, if_pos (show pre(r) + t < len xi by omega)]
    obtain ⟨r', hr', h1, h2, hx, -, hdd⟩ := hD (pre(r) + t) (by omega)
    rw [hxi_in r t hr ht] at hx; rw [← hx] at hdd
    rw [hdd]; omega
  -- the key: `Vals.compact` reads back every row
  have hkey : ∀ q : Fin nN, (Vals.compact K (Rel.key P)).row q = (Rel.key P).row q := fun q => by
    rw [show Vals.compact K (Rel.key P) = Vals.pick K (Rel.key P) (tilLongs _) _ (len_tilLongs _) from rfl,
      pick_row K (Rel.key P) (tilLongs (Rel.n P)) (Rel.n P) (len_tilLongs _) hKf,
      dif_pos (show (Column.bitsAt (tilLongs (Rel.n P)) (q.1 * 8) 8).toNat < (Rel.n P).toNat by
        rw [tilLongs_get q.2]; exact q.2)]
    exact congrArg (Vals.row (Rel.key P)) (Fin.ext (tilLongs_get q.2))
  have hgU : len g < USize.size := by rw [len_eq_ids, hgl]; omega
  have hgN : ((len g).toUSize).toNat = pre(nN) + nN := by
    rw [USize.toNat_ofNat_of_lt' hgU, len_eq_ids, hgl, hpN]
  -- row `r` of the result: the head, then the tail cells in order
  have hrow : ∀ (hpg : len g = ((len g).toUSize).toNat) hN (hh : (Rel.n P).toNat ≤ len hi) (r : Nat) (hr : r < nN),
      Vals.row (A := .arr B) (⟨(len g).toUSize, valCol Ew.sub Ew.vv hi c1, longsN (Rel.n P) hi hh,
        Vals.pick B (Obj.raze B #[⟨m, tl⟩, ⟨Rel.n P, (Rel.val P).1⟩] hN) g (len g).toUSize hpg⟩ :
          Vals (.arr B) (Rel.n P)) ⟨r, hr⟩ =
        Vals.row (Rel.val P).1 ⟨r, hr⟩ :: Vals.row (Rel.val P).2 ⟨r, hr⟩ := by
    intro hpg hN hh r hr
    have hFf' := hFf hN
    rw [hpg] at hFf'
    have hpk : ∀ {N : USize} (F : Vals B N)
        (hF : Vals.PickFits B F ((List.range ((len g).toUSize).toNat).map fun q => (Column.bitsAt g (q * 8) 8).toNat))
        (q : Fin ((len g).toUSize).toNat) (d : Fin N.toNat), (Column.bitsAt g (q.1 * 8) 8).toNat = d.1 →
        (Vals.pick B F g _ hpg).row q = F.row d := by
      intro N F hF q d e
      rw [pick_row B F g _ hpg hF q, dif_pos (show (Column.bitsAt g (q.1 * 8) 8).toNat < N.toNat by
        rw [e]; exact d.2)]
      exact congrArg _ (Fin.ext e)
    have hcN := raze2_cnt tl (Rel.val P).1 hN
    have e1 := hhig r hr; have e2 := hc1g r hr; have e3 := hpre_succ r; have e4 := hpre_le (r + 1) nN (by omega)
    have hsub : (Column.bitsAt (sub (Rel.n P) hi c1) (r * 8) 8).toNat = pre(r) + r := by
      rw [sub_get (a := hi) (b := c1) hr (by omega) (by omega)]; omega
    have hlo' : ((valCol (n := Rel.n P) Ew.sub Ew.vv hi c1).get ⟨r, hr⟩).toInt = ((pre(r) + r : Nat) : Int) := by
      rw [valCol_get]; dsimp only
      rw [show Kernel.Ew.val Ew.sub Ew.i64 Ew.vv nul hi c1 (Rel.n P) = sub (Rel.n P) hi c1 from rfl,
        toInt64_toInt (x := Column.bitsAt (sub (Rel.n P) hi c1) (r * 8) 8) (by omega), hsub]
    have hhi' : ((longsN (Rel.n P) hi hh).get ⟨r, hr⟩).toInt = ((pre(r + 1) + (r + 1) : Nat) : Int) := by
      rw [longsN_get]; dsimp only
      rw [toInt64_toInt (x := Column.bitsAt hi (r * 8) 8) (by omega), e1]
    have hrow := arr_row (b := B) (⟨(len g).toUSize, valCol (n := Rel.n P) Ew.sub Ew.vv hi c1,
      longsN (Rel.n P) hi hh, Vals.pick B (Obj.raze B #[⟨m, tl⟩, ⟨Rel.n P, (Rel.val P).1⟩] hN) g (len g).toUSize hpg⟩ :
        Vals (.arr B) (Rel.n P)) ⟨r, hr⟩
    dsimp only at hrow
    rw [hlo', hhi'] at hrow
    have f1 : min (max ((pre(r) + r : Nat) : Int) 0).toNat ((len g).toUSize).toNat = pre(r) + r := by omega
    have f2 : min (max ((pre(r + 1) + (r + 1) : Nat) : Int) 0).toNat ((len g).toUSize).toNat =
        pre(r + 1) + (r + 1) := by omega
    rw [f1, f2] at hrow
    rw [hrow]
    obtain ⟨hLC, hln, hget⟩ := hR r hr
    apply List.ext_getElem
    · rw [List.length_cons, hln, List.length_map, List.length_range]; omega
    · intro t h1 h2
      have hb : pre(r) + r + t < ((len g).toUSize).toNat := by
        simp only [List.length_map, List.length_range] at h1; omega
      rw [List.getElem_map, List.getElem_range, dif_pos hb]
      cases t with
      | zero =>
        rw [List.getElem_cons_zero, hpk _ hFf' ⟨_, hb⟩ ⟨len xi + r, by rw [hcN, hmN]; omega⟩ (by
            dsimp only
            rw [← ids_getElem (b := g) (j := pre(r) + r + 0) (by rw [hgl]; omega)]; exact hgh r hr),
          raze_row_full B tl (Rel.val P).1 hRf hN, dif_neg (show ¬ len xi + r < m.toNat by omega)]
        exact congrArg _ (Fin.ext (show len xi + r - m.toNat = r by omega))
      | succ t =>
        have ht : t < cnt(r) := by simp only [List.length_cons] at h2; omega
        rw [List.getElem_cons_succ, hpk _ hFf' ⟨_, hb⟩ ⟨pre(r) + t, by rw [hcN, hmN, hxl]; omega⟩ (by
            dsimp only
            rw [show pre(r) + r + (t + 1) = pre(r) + r + 1 + t by omega,
              ← ids_getElem (b := g) (j := pre(r) + r + 1 + t) (by rw [hgl]; omega)]
            exact hgt r t hr ht),
          raze_row_full B tl (Rel.val P).1 hRf hN, dif_pos (show pre(r) + t < m.toNat by omega)]
        have hdl' : pre(r) + t < len xi := by rw [hxl]; omega
        obtain ⟨r', hr', -, -, hx, hjd, -⟩ := hD (pre(r) + t) hdl'
        rw [hxi_in r t hr ht] at hx; rw [← hx] at hjd
        rw [htl, pick_row B _ j m hjl hTf, dif_pos (show (Column.bitsAt j ((pre(r) + t) * 8) 8).toNat <
          (Rel.val P).2.1.toNat by rw [hjd]; omega), hget t (by rw [hln]; exact ht) (by omega)]
        exact congrArg _ (Fin.ext (show (Column.bitsAt j ((pre(r) + t) * 8) 8).toNat = st(r) + t by rw [hjd]; omega))
  -- `cons` unfolded at its pieces
  intro k ys
  have hkN : m.toNat + nN < USize.size := by omega
  subst hm
  subst htl hj hg hdst hlo hhi hc1 hxr hxi
  unfold cons expand need
  dsimp only
  rw [dif_pos hxU]
  try dsimp only
  rw [dif_pos hkN]
  try dsimp only
  rw [longCount_eq _ _ _ hgU]
  show (∃ q, _ ∧ _) ↔ _
  constructor
  · rintro ⟨⟨r, hr⟩, hk, hv⟩
    refine ⟨Vals.row (Rel.val P).1 ⟨r, hr⟩, Vals.row (Rel.val P).2 ⟨r, hr⟩, ?_, ?_⟩
    · show ∃ q, _ ∧ _
      exact ⟨⟨r, hr⟩, (hkey _).symm.trans hk, rfl⟩
    · rw [← hv]
      exact hrow _ _ _ r hr
  · rintro ⟨b, bs, ⟨⟨r, hr⟩, hk, hv⟩, rfl⟩
    refine ⟨⟨r, hr⟩, (hkey _).trans hk, ?_⟩
    rw [hrow _ _ _ r hr]
    exact congr (congrArg List.cons (congrArg Prod.fst hv)) (congrArg Prod.snd hv)

/-- The chain `rep_foldBy` leaves for `map`: rows `ys[t] = b :: ys[t+1]` ending at `[]` read back as one list
whose cell `t` is related to `xs[t]`. -/
theorem map_chain {α β : Type _} (R : α → β → Prop) (xs : List α) (w : List β) :
    (∃ ys : List (List β), ∃ hy : ys.length = xs.length + 1,
      ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm) = [] ∧
      (∀ t (ht : t < xs.length), ∃ b, R (xs[t]'ht) b ∧
        ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) =
          b :: ys[t+1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm)) ∧
      w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.succ_pos _) hy.symm)) ↔
    w.length = xs.length ∧ ∀ t (ht : t < xs.length) (ht' : t < w.length), R (xs[t]'ht) (w[t]'ht') := by
  constructor
  · rintro ⟨ys, hy, hnil, hstep, rfl⟩
    have hdrop : ∀ t (ht : t ≤ xs.length), ys[t]'(by omega) = (ys[0]'(by omega)).drop t := by
      intro t
      induction t with
      | zero => intro _; rfl
      | succ t ih =>
        intro ht
        obtain ⟨b, -, hb⟩ := hstep t (by omega)
        have h := ih (by omega)
        rw [hb] at h
        rw [← List.tail_drop, ← h]
        rfl
    have hlen : ∀ k t (ht : t ≤ xs.length), t + k = xs.length → (ys[t]'(by omega)).length = k := by
      intro k
      induction k with
      | zero =>
        intro t ht h
        obtain rfl : t = xs.length := by omega
        rw [hnil]
        rfl
      | succ k ih =>
        intro t ht h
        obtain ⟨b, -, hb⟩ := hstep t (by omega)
        rw [hb, List.length_cons, ih (t+1) (by omega) (by omega)]
    refine ⟨hlen xs.length 0 (by omega) (by omega), fun t ht ht' => ?_⟩
    obtain ⟨b, hR, hb⟩ := hstep t ht
    have h := hdrop t (by omega)
    rw [hb, List.drop_eq_getElem_cons ht'] at h
    injection h with h1
    rw [← h1]
    exact hR
  · rintro ⟨hl, hR⟩
    refine ⟨(List.range (xs.length + 1)).map fun t => w.drop t, by simp, ?_,
      fun t ht => ⟨w[t]'(by omega), hR t ht (by omega), ?_⟩, ?_⟩
    · simp [hl]
    · simp only [List.getElem_map, List.getElem_range]
      exact List.drop_eq_getElem_cons _
    · simp

-- `RepFold`'s `codesOK`, `kp2`, `mpairs`, `msum` (local notations, so restated here)
set_option hygiene false in
local notation "codesOK(" cs ", " ps ")" => ((∀ {k l : Nat} (hk : k < 2) (hl : l < 2) {i j : Nat}
    (hi : i < (ps[k]'hk).1.toNat) (hj : j < (ps[l]'hl).1.toNat),
    Column.idAt (cs[k]'hk).b (cs[k]'hk).w i = Column.idAt (cs[l]'hl).b (cs[l]'hl).w j ↔
      Vals.row (ps[k]'hk).2 ⟨i, hi⟩ = Vals.row (ps[l]'hl).2 ⟨j, hj⟩) ∧
  ∀ {k : Nat} (hk : k < 2),
    ((cs[k]'hk).w = 1 ∨ (cs[k]'hk).w = 2 ∨ (cs[k]'hk).w = 4 ∨ (cs[k]'hk).w = 8 ∨ (cs[k]'hk).w = 16 ∨
      (cs[k]'hk).w = 32 ∨ (cs[k]'hk).w = 64) ∧
    (cs[k]'hk).n = (ps[k]'hk).1 ∧ (cs[k]'hk).b.size = ((cs[k]'hk).n.toNat * (cs[k]'hk).w + 7) / 8 ∧
    ((cs[k]'hk).w < 8 → (cs[k]'hk).card < USize.size ∧
      ∀ i < (cs[k]'hk).n.toNat, Column.idAt (cs[k]'hk).b (cs[k]'hk).w i < (cs[k]'hk).card))
set_option hygiene false in
local notation "kp2(" R ", " S ")" => (#v[⟨Rel.n R, Rel.key R⟩, ⟨Rel.n S, Rel.key S⟩] : Vector (Part .long) 2)
set_option hygiene false in
local notation "mpairs(" cs ", " R ", " S ")" => ((List.range (Rel.n R).toNat).flatMap fun i =>
  ((List.range (Rel.n S).toNat).filter fun j => Column.idAt (cs[1]'Nat.one_lt_two).b (cs[1]'Nat.one_lt_two).w j ==
    Column.idAt (cs[0]'Nat.zero_lt_two).b (cs[0]'Nat.zero_lt_two).w i).map (i, ·))
set_option hygiene false in
local notation "msum(" cs ", " R ", " S ")" => ((List.range (Rel.n R).toNat).map fun i =>
  ((List.range (Rel.n S).toNat).filter fun j => Column.idAt (cs[1]'Nat.one_lt_two).b (cs[1]'Nat.one_lt_two).w j ==
    Column.idAt (cs[0]'Nat.zero_lt_two).b (cs[0]'Nat.zero_lt_two).w i).length).sum

/-- **`map`'s step, read back**: `cons (pair (el ≫ R) pend)` takes row `r`'s element `e` and list `u` to
    `b :: u` for each `b` with `e R b`. `Q = el ≫ R`, `P = pair Q pend` and the codes `jc`, `kc` are bound by
    their equations. Hypotheses: `rep_comp`'s at `el`, `R` (`hj…`), `rep_pair`'s at `Q`, `pend` (`hk…`),
    `rep_cons`'s at `P`. -/
theorem map_step_rep {E B : Obj} (el : Rel .long E) (R : Rel E B) (pend : Rel .long (.arr B))
    (jc : Vector Code 2)
    (hjc : jc = Obj.codes E (#v[⟨Rel.n el, Rel.val el⟩, ⟨Rel.n R, Rel.key R⟩] : Vector (Part E) 2))
    (hjO : codesOK(jc, (#v[⟨Rel.n el, Rel.val el⟩, ⟨Rel.n R, Rel.key R⟩] : Vector (Part E) 2)))
    (hjn : (Rel.n R).toNat < 2 ^ 63) (hjM : msum(jc, el, R) < 2 ^ 63) (hjU : msum(jc, el, R) < USize.size)
    (hjA : Vals.PickFits .long (Rel.key el) ((mpairs(jc, el, R)).map Prod.fst))
    (hjC : Vals.PickFits B (Rel.val R) ((mpairs(jc, el, R)).map Prod.snd))
    (Q : Rel .long B) (hQ : Q = el ≫ R)
    (kc : Vector Code 2) (hkc : kc = Obj.codes .long kp2(Q, pend)) (hkO : codesOK(kc, kp2(Q, pend)))
    (hkn : (Rel.n pend).toNat < 2 ^ 63) (hkM : msum(kc, Q, pend) < 2 ^ 63)
    (hkU : msum(kc, Q, pend) < USize.size)
    (hkA : Vals.PickFits .long (Rel.key Q) ((mpairs(kc, Q, pend)).map Prod.fst))
    (hkB : Vals.PickFits B (Rel.val Q) ((mpairs(kc, Q, pend)).map Prod.fst))
    (hkC : Vals.PickFits (.arr B) (Rel.val pend) ((mpairs(kc, Q, pend)).map Prod.snd))
    (P : Rel .long (.prod B (.arr B))) (hP : P = pair Q pend)
    (hp : (Rel.val P).2.1.toNat < 2 ^ 63)
    (s : ByteArray × ByteArray) (hs : s = slicesOf (Rel.val P).2)
    (hS : ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt s.2 (r * 8) 8).toNat).sum + (Rel.n P).toNat < 2 ^ 63)
    (hU : ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt s.2 (r * 8) 8).toNat).sum + (Rel.n P).toNat < USize.size)
    (xi : ByteArray) (hxi : xi = expandBytes 8 0 (tilLongs (Rel.n P)) s.2)
    (m : USize) (hm : m = (len xi).toUSize)
    (xr : ByteArray) (hxr : xr = sub m (tilLongs m) (gather 8 (sub (Rel.n P) (sums (Rel.n P) s.2) s.2) xi))
    (j : ByteArray) (hj : j = add m (gather 8 s.1 xi) xr)
    (hjl : len j = m.toNat) (tl : Vals B m) (htl : tl = Vals.pick B (Rel.val P).2.2.2.2 j m hjl)
    (c1 : ByteArray) (hc1 : c1 = addc (Rel.n P) s.2 1) (hi : ByteArray) (hhi : hi = sums (Rel.n P) c1)
    (lo : ByteArray) (hlo : lo = sub (Rel.n P) hi c1)
    (dst : ByteArray) (hdst : dst = addc m (add m (gather 8 lo xi) xr) 1)
    (g : ByteArray) (hg : g = (Code.ofLongs (concatBytes #[dst, lo])).grade)
    (hKf : Vals.PickFits .long (Rel.key P) ((List.range (Rel.n P).toNat).map fun q => (Column.bitsAt (tilLongs (Rel.n P)) (q * 8) 8).toNat))
    (hTf : Vals.PickFits B (Rel.val P).2.2.2.2 ((List.range m.toNat).map fun q => (Column.bitsAt j (q * 8) 8).toNat))
    (hRf : Vals.RazeFits B tl (Rel.val P).1)
    (hFf : ∀ hN, Vals.PickFits B (Obj.raze B #[⟨m, tl⟩, ⟨Rel.n P, (Rel.val P).1⟩] hN)
      ((List.range (len g)).map fun q => (Column.bitsAt g (q * 8) 8).toNat)) :
    ∀ r v, rep (cons (pair (el ≫ R) pend)) r v ↔
      ∃ e u, rep el r e ∧ rep pend r u ∧ ∃ b, rep R e b ∧ v = b :: u := by
  subst hjc hkc
  have h2 := rep_comp el R hjO hjn hjM hjU hjA hjC
  subst hQ
  have h1 := rep_pair (el ≫ R) pend hkO hkn hkM hkU hkA hkB hkC
  subst hP
  intro r v
  rw [rep_cons (pair (el ≫ R) pend) hp s hs hS hU xi hxi m hm xr hxr j hj hjl tl htl c1 hc1 hi hhi lo hlo
    dst hdst g hg hKf hTf hRf hFf, h1]
  constructor
  · rintro ⟨b, bs, hb, rfl⟩
    obtain ⟨hq, hu⟩ := hb
    rw [h2] at hq
    obtain ⟨e, he, hR⟩ := hq
    exact ⟨e, bs, he, hu, b, hR, rfl⟩
  · rintro ⟨e, u, he, hu, b, hR, rfl⟩
    refine ⟨b, u, ⟨?_, hu⟩, rfl⟩
    rw [h2]
    exact ⟨e, he, hR⟩

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.Rep.rep_uncons
#print axioms LeetQ.Rel.Rep.rep_cons
#print axioms LeetQ.Rel.Rep.map_chain
#print axioms LeetQ.Rel.Rep.map_step_rep
