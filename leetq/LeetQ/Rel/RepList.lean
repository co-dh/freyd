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

/-- **An atom side fits at the rows `tilLongs n` reads**: they are `0, …, n-1`, so no row misses. -/
theorem pickFits_tilLongs {t : QAtomicType} {n : USize} (x : Vals (.atom t) n) :
    Vals.PickFits (.atom t) x ((List.range n.toNat).map fun q => (Column.bitsAt (tilLongs n) (q * 8) 8).toNat) :=
  pickFits_atom x fun k hk => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hk
    rw [tilLongs_get (List.mem_range.1 hq)]
    exact List.mem_range.1 hq

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
    (tl : Vals B m) (htl : tl = Vals.pick B (Rel.val P).2.2.2.2 (add m (gather 8 s.1 xi) xr) m
      (len_val Ew.add Ew.vv (gather 8 s.1 xi) xr m))
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
  -- the tails' rows `j` are `m` longs: `tl` picks at `j` itself
  have hjl : len j = m.toNat := by rw [hj]; exact len_val ..
  replace htl : tl = Vals.pick B (Rel.val P).2.2.2.2 j m hjl := by subst hj; exact htl
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
  have hblk : ∀ r, r < nN → pre(r) + r ≤ pre(r + 1) + (r + 1) := fun r _ => by rw [hpre_succ]; omega
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

-- the counts `cn` an `expand` reads: count `r` and the counts before row `r`
set_option hygiene false in
local notation "cc(" r ")" => (Column.bitsAt cn (r * 8) 8).toNat
set_option hygiene false in
local notation "pc(" r ")" => ((List.range r).map fun u => (Column.bitsAt cn (u * 8) 8).toNat).sum

/-- **`expand`, read back by place**: of the counts `cn`, copy `pc(r) + t` (`t < cc(r)`) is row `r` (`xi`) at rank
    `t` (`xr`), and every copy is one of these. Hypotheses: the counts' sum below `2^63` and a `USize`. -/
theorem expand_at {n : USize} (cn : ByteArray) (hl : len cn = n.toNat) (hS : pc(n.toNat) < 2 ^ 63)
    (hU : pc(n.toNat) < USize.size) (xi : ByteArray) (hxi : xi = expandBytes 8 0 (tilLongs n) cn)
    (xr : ByteArray)
    (hxr : xr = sub (len xi).toUSize (tilLongs (len xi).toUSize) (gather 8 (sub n (sums n cn) cn) xi)) :
    len xi = pc(n.toNat) ∧
      (∀ r t, r < n.toNat → t < cc(r) → (Column.bitsAt xi ((pc(r) + t) * 8) 8).toNat = r ∧
        (Column.bitsAt xr ((pc(r) + t) * 8) 8).toNat = t) ∧
      ∀ d, d < len xi → ∃ r t, r < n.toNat ∧ t < cc(r) ∧ d = pc(r) + t := by
  have hpre_le : ∀ a b, a ≤ b → pc(a) ≤ pc(b) := fun a b h => sum_range_le _ h
  have hpre_succ : ∀ r, pc(r + 1) = pc(r) + cc(r) := fun r => sum_range_succ' _ r
  have hI := expand_idx (n := n) (cnt := cn) (by omega)
    (fun t ht => by have := hpre_le (t + 1) n.toNat (by omega); rw [hpre_succ] at this; omega)
  rw [← hxi, hl] at hI
  have hxl : len xi = pc(n.toNat) := by
    rw [len_eq_ids, hI, List.length_flatMap]; simp only [List.length_replicate]
  have hxU : len xi < USize.size := by omega
  have hxi_in : ∀ r t, r < n.toNat → t < cc(r) → (Column.bitsAt xi ((pc(r) + t) * 8) 8).toNat = r := by
    intro r t hr ht
    have h := flatMap_get_at (fun t => List.replicate cc(t) t) hr (q := t)
      (by simp only [List.length_replicate]; exact ht)
    simp only [List.length_replicate, List.getElem?_replicate, ht, ↓reduceIte] at h
    have hpl : pc(r) + t < ((List.range n.toNat).flatMap fun t => List.replicate cc(t) t).length := by
      rw [← hI, ← len_eq_ids, hxl]; have := hpre_le (r + 1) n.toNat (by omega); rw [hpre_succ] at this; omega
    rw [ids_get hI hpl]; rw [List.getElem?_eq_getElem hpl] at h; exact Option.some.inj h
  have hxrg : ∀ d, d < len xi → (Column.bitsAt xr (d * 8) 8).toNat = d - pc((Column.bitsAt xi (d * 8) 8).toNat) := by
    intro d hd
    have := expand_rank (n := n) (cnt := cn) (by omega) (by rw [hl]; exact hS)
      (by rw [← hxi]; exact hxU) (p := d) (by rw [← hxi]; exact hd)
    rw [← hxi, ← hxr] at this
    exact this
  refine ⟨hxl, fun r t hr ht => ⟨hxi_in r t hr ht, ?_⟩, fun d hd => ?_⟩
  · have hpl : pc(r) + t < len xi := by
      rw [hxl]; have := hpre_le (r + 1) n.toNat (by omega); rw [hpre_succ] at this; omega
    rw [hxrg _ hpl, hxi_in r t hr ht]; omega
  · obtain ⟨t, ht, h1, h2, -⟩ := flatMap_get (fun t => List.replicate cc(t) t) n.toNat d
      (by simp only [List.length_replicate]; omega)
    simp only [List.length_replicate] at h1 h2
    exact ⟨t, d - pc(t), ht, by omega, by omega⟩

-- `P`'s two sides: row `r`'s count and start, and the counts before row `r`
set_option hygiene false in
local notation "ca(" r ")" => (Column.bitsAt (slicesOf (Rel.val P).1).2 (r * 8) 8).toNat
set_option hygiene false in
local notation "cb(" r ")" => (Column.bitsAt (slicesOf (Rel.val P).2).2 (r * 8) 8).toNat
set_option hygiene false in
local notation "sa(" r ")" => (Column.bitsAt (slicesOf (Rel.val P).1).1 (r * 8) 8).toNat
set_option hygiene false in
local notation "sb(" r ")" => (Column.bitsAt (slicesOf (Rel.val P).2).1 (r * 8) 8).toNat
set_option hygiene false in
local notation "pa(" r ")" => ((List.range r).map fun u => (Column.bitsAt (slicesOf (Rel.val P).1).2 (u * 8) 8).toNat).sum
set_option hygiene false in
local notation "pb(" r ")" => ((List.range r).map fun u => (Column.bitsAt (slicesOf (Rel.val P).2).2 (u * 8) 8).toNat).sum

/-- **`cat`'s places, read back**: under `rep_cat`'s bound pieces and size bounds, each side's copies fit a `USize`,
    and of row `r` the first side's copy `pa(r) + t` is its cell `sa(r) + t` (`ja`), graded to place
    `pa(r) + pb(r) + t`; the second side's copy `pb(r) + t` is its cell `sb(r) + t` (`jb`), graded to place
    `pa(r) + pb(r) + ca(r) + t`. -/
theorem cat_places {K B : Obj} (P : Rel K (.prod (.arr B) (.arr B)))
    (hpa : (Rel.val P).1.1.toNat < 2 ^ 63) (hpb : (Rel.val P).2.1.toNat < 2 ^ 63)
    (sa : ByteArray × ByteArray) (hsa : sa = slicesOf (Rel.val P).1)
    (sb : ByteArray × ByteArray) (hsb : sb = slicesOf (Rel.val P).2)
    (hS : ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt sa.2 (r * 8) 8).toNat).sum +
      ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt sb.2 (r * 8) 8).toNat).sum < 2 ^ 63)
    (hU : ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt sa.2 (r * 8) 8).toNat).sum +
      ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt sb.2 (r * 8) 8).toNat).sum < USize.size)
    (xa : ByteArray) (hxa : xa = expandBytes 8 0 (tilLongs (Rel.n P)) sa.2)
    (ma : USize) (hma : ma = (len xa).toUSize)
    (ra : ByteArray) (hra : ra = sub ma (tilLongs ma) (gather 8 (sub (Rel.n P) (sums (Rel.n P) sa.2) sa.2) xa))
    (xb : ByteArray) (hxb : xb = expandBytes 8 0 (tilLongs (Rel.n P)) sb.2)
    (mb : USize) (hmb : mb = (len xb).toUSize)
    (rb : ByteArray) (hrb : rb = sub mb (tilLongs mb) (gather 8 (sub (Rel.n P) (sums (Rel.n P) sb.2) sb.2) xb))
    (ja : ByteArray) (hja : ja = add ma (gather 8 sa.1 xa) ra)
    (jb : ByteArray) (hjb : jb = add mb (gather 8 sb.1 xb) rb)
    (c : ByteArray) (hcs : c = add (Rel.n P) sa.2 sb.2) (hi : ByteArray) (hhi : hi = sums (Rel.n P) c)
    (lo : ByteArray) (hlo : lo = sub (Rel.n P) hi c)
    (da : ByteArray) (hda : da = add ma (gather 8 lo xa) ra)
    (db : ByteArray) (hdb : db = add mb (add mb (gather 8 lo xb) (gather 8 sa.2 xb)) rb)
    (g : ByteArray) (hg : g = (Code.ofLongs (concatBytes #[da, db])).grade) :
    len xa < USize.size ∧ len xb < USize.size ∧ ma.toNat = len xa ∧ mb.toNat = len xb ∧
      len xa = pa((Rel.n P).toNat) ∧ len xb = pb((Rel.n P).toNat) ∧ len g = len xa + len xb ∧
      (∀ r, r < (Rel.n P).toNat → (Column.bitsAt hi (r * 8) 8).toNat = pa(r + 1) + pb(r + 1) ∧
        (Column.bitsAt c (r * 8) 8).toNat = ca(r) + cb(r)) ∧
      (∀ r t, r < (Rel.n P).toNat → t < ca(r) → (Column.bitsAt ja ((pa(r) + t) * 8) 8).toNat = sa(r) + t ∧
        (ids g)[pa(r) + pb(r) + t]? = some (pa(r) + t)) ∧
      ∀ r t, r < (Rel.n P).toNat → t < cb(r) → (Column.bitsAt jb ((pb(r) + t) * 8) 8).toNat = sb(r) + t ∧
        (ids g)[pa(r) + pb(r) + ca(r) + t]? = some (len xa + (pb(r) + t)) := by
  subst hsa hsb
  have hsa1 : len (slicesOf (Rel.val P).1).1 = nN := (len_slices _ _ _ _).1
  have hsa2 : len (slicesOf (Rel.val P).1).2 = nN := (len_slices _ _ _ _).2
  have hsb1 : len (slicesOf (Rel.val P).2).1 = nN := (len_slices _ _ _ _).1
  have hsb2 : len (slicesOf (Rel.val P).2).2 = nN := (len_slices _ _ _ _).2
  have hRa := fun r (hr : r < nN) => slicesOf_row (Rel.val P).1 hpa hr
  have hRb := fun r (hr : r < nN) => slicesOf_row (Rel.val P).2 hpb hr
  have hpa_le : ∀ a b, a ≤ b → pa(a) ≤ pa(b) := fun a b h => sum_range_le _ h
  have hpb_le : ∀ a b, a ≤ b → pb(a) ≤ pb(b) := fun a b h => sum_range_le _ h
  have hpa_succ : ∀ r, pa(r + 1) = pa(r) + ca(r) := fun r => sum_range_succ' _ r
  have hpb_succ : ∀ r, pb(r + 1) = pb(r) + cb(r) := fun r => sum_range_succ' _ r
  have hcl : ∀ r, r < nN → pa(r) + ca(r) ≤ pa(nN) ∧ pb(r) + cb(r) ≤ pb(nN) := fun r hr => by
    have h1 := hpa_le (r + 1) nN (by omega); have h2 := hpb_le (r + 1) nN (by omega)
    rw [hpa_succ] at h1; rw [hpb_succ] at h2; exact ⟨h1, h2⟩
  -- the summed counts, their running ends and starts: row `r`'s new array is `[pa(r) + pb(r), pa(r+1) + pb(r+1))`
  have hcg : ∀ r, r < nN → (Column.bitsAt c (r * 8) 8).toNat = ca(r) + cb(r) := fun r hr => by
    obtain ⟨cl1, cl2⟩ := hcl r hr
    rw [hcs, add_get (a := (slicesOf (Rel.val P).1).2) (b := (slicesOf (Rel.val P).2).2) hr (by omega)]
  have hcl' : len c = nN := by rw [hcs, add, len_val]
  have hcsum : ∀ r, r ≤ nN →
      ((List.range r).map fun u => (Column.bitsAt c (u * 8) 8).toNat).sum = pa(r) + pb(r) := by
    intro r
    induction r with
    | zero => intro _; simp
    | succ r ih => intro hr; simp only [sum_range_succ']; rw [ih (by omega), hcg r (by omega)]; omega
  have hhig : ∀ r, r < nN → (Column.bitsAt hi (r * 8) 8).toNat = pa(r + 1) + pb(r + 1) := fun r hr => by
    have e := hcsum (r + 1) (by omega)
    have h1 := hpa_le (r + 1) nN (by omega); have h2 := hpb_le (r + 1) nN (by omega)
    rw [hhi, sums_get (b := c) hr (by rw [hcl']; exact hr) (by rw [e]; omega), e]
  have hlog : ∀ r, r < nN → (Column.bitsAt lo (r * 8) 8).toNat = pa(r) + pb(r) := fun r hr => by
    have := hhig r hr; have := hcg r hr; have := hpa_succ r; have := hpb_succ r
    have := hpa_le (r + 1) nN (by omega); have := hpb_le (r + 1) nN (by omega)
    rw [hlo, sub_get (a := hi) (b := c) hr (by omega) (by omega)]; omega
  have hlol : len lo = nN := by rw [hlo, sub, len_val]
  -- each side's `expand`: copy `pa(r) + t` (`pb(r) + t`) is row `r` at rank `t`
  obtain ⟨hxal, hxa_in, hxa_at⟩ := expand_at (n := Rel.n P) (slicesOf (Rel.val P).1).2 hsa2 (by omega) (by omega)
    xa hxa ra (by rw [hra, hma])
  obtain ⟨hxbl, hxb_in, hxb_at⟩ := expand_at (n := Rel.n P) (slicesOf (Rel.val P).2).2 hsb2 (by omega) (by omega)
    xb hxb rb (by rw [hrb, hmb])
  have hxaU : len xa < USize.size := by omega
  have hxbU : len xb < USize.size := by omega
  have hmaN : ma.toNat = len xa := by rw [hma]; exact USize.toNat_ofNat_of_lt' hxaU
  have hmbN : mb.toNat = len xb := by rw [hmb]; exact USize.toNat_ofNat_of_lt' hxbU
  -- copy `pa(r) + t` of the first side: its cell in that payload (`ja`) and its place `pa(r) + pb(r) + t` (`da`)
  have hA : ∀ r t, r < nN → t < ca(r) →
      (Column.bitsAt ja ((pa(r) + t) * 8) 8).toNat = sa(r) + t ∧
      (Column.bitsAt da ((pa(r) + t) * 8) 8).toNat = pa(r) + pb(r) + t := by
    intro r t hr ht
    obtain ⟨hx, hrk⟩ := hxa_in r t hr ht
    obtain ⟨cl1, cl2⟩ := hcl r hr
    have hd : pa(r) + t < len xa := by rw [hxal]; omega
    have hdm : pa(r) + t < ma.toNat := by omega
    obtain ⟨hLC, -, -⟩ := hRa r hr
    have hgs : Column.bitsAt (gather 8 (slicesOf (Rel.val P).1).1 xa) ((pa(r) + t) * 8) 8 =
        Column.bitsAt (slicesOf (Rel.val P).1).1 (r * 8) 8 := by
      rw [gather8_get (src := (slicesOf (Rel.val P).1).1) hd (by rw [hx, hsa1]; exact hr), hx]
    have hgl : Column.bitsAt (gather 8 lo xa) ((pa(r) + t) * 8) 8 = Column.bitsAt lo (r * 8) 8 := by
      rw [gather8_get (src := lo) hd (by rw [hx, hlol]; exact hr), hx]
    have hl := hlog r hr
    constructor
    · rw [hja, add_get (a := gather 8 (slicesOf (Rel.val P).1).1 xa) (b := ra) hdm (by rw [hgs, hrk]; omega), hgs, hrk]
    · rw [hda, add_get (a := gather 8 lo xa) (b := ra) hdm (by rw [hgl, hrk, hl]; omega), hgl, hrk, hl]
  -- copy `pb(r) + t` of the second side: its cell (`jb`) and its place `pa(r) + pb(r) + ca(r) + t` (`db`)
  have hB : ∀ r t, r < nN → t < cb(r) →
      (Column.bitsAt jb ((pb(r) + t) * 8) 8).toNat = sb(r) + t ∧
      (Column.bitsAt db ((pb(r) + t) * 8) 8).toNat = pa(r) + pb(r) + ca(r) + t := by
    intro r t hr ht
    obtain ⟨hx, hrk⟩ := hxb_in r t hr ht
    obtain ⟨cl1, cl2⟩ := hcl r hr
    have hd : pb(r) + t < len xb := by rw [hxbl]; omega
    have hdm : pb(r) + t < mb.toNat := by omega
    obtain ⟨hLC, -, -⟩ := hRb r hr
    have hgs : Column.bitsAt (gather 8 (slicesOf (Rel.val P).2).1 xb) ((pb(r) + t) * 8) 8 =
        Column.bitsAt (slicesOf (Rel.val P).2).1 (r * 8) 8 := by
      rw [gather8_get (src := (slicesOf (Rel.val P).2).1) hd (by rw [hx, hsb1]; exact hr), hx]
    have hgl : Column.bitsAt (gather 8 lo xb) ((pb(r) + t) * 8) 8 = Column.bitsAt lo (r * 8) 8 := by
      rw [gather8_get (src := lo) hd (by rw [hx, hlol]; exact hr), hx]
    have hga : Column.bitsAt (gather 8 (slicesOf (Rel.val P).1).2 xb) ((pb(r) + t) * 8) 8 =
        Column.bitsAt (slicesOf (Rel.val P).1).2 (r * 8) 8 := by
      rw [gather8_get (src := (slicesOf (Rel.val P).1).2) hd (by rw [hx, hsa2]; exact hr), hx]
    have hl := hlog r hr
    have hs1 := add_get (n := mb) (a := gather 8 lo xb) (b := gather 8 (slicesOf (Rel.val P).1).2 xb) hdm
      (by rw [hgl, hga, hl]; omega)
    rw [hgl, hga, hl] at hs1
    constructor
    · rw [hjb, add_get (a := gather 8 (slicesOf (Rel.val P).2).1 xb) (b := rb) hdm (by rw [hgs, hrk]; omega), hgs, hrk]
    · rw [hdb, add_get (a := add mb (gather 8 lo xb) (gather 8 (slicesOf (Rel.val P).1).2 xb)) (b := rb) hdm
        (by rw [hs1, hrk]; omega), hs1, hrk]
  -- the first side's places then the second's: `cat`'s grade lays the cells out by them
  have hdal : len da = len xa := by rw [hda, add, len_val, hmaN]
  have hda8 : da.size = len da * 8 := by rw [hda, add]; exact val_size_len ..
  have hdbl : len db = len xb := by rw [hdb, add, len_val, hmbN]
  have hdb8 : db.size = len db * 8 := by rw [hdb, add]; exact val_size_len ..
  have hbl : len (concatBytes #[da, db]) = len xa + len xb := by
    have e : concatBytes #[da, db] = da ++ db := by simp [concatBytes]
    rw [e]; simp only [len, ByteArray.size_append] at hda8 hdb8 hdal hdbl ⊢; omega
  have hbg : ∀ d, (Column.bitsAt (concatBytes #[da, db]) (d * 8) 8).toNat =
      if d < len xa then (Column.bitsAt da (d * 8) 8).toNat else (Column.bitsAt db ((d - len xa) * 8) 8).toNat := by
    intro d; rw [concat2_get hda8, hdal]; split <;> rfl
  -- every place: `pa(r) + pb(r) + u`, `u < ca(r)` from the first side, `ca(r) ≤ u < ca(r) + cb(r)` from the second
  have hval : ∀ d, d < len xa + len xb → ∃ r u, r < nN ∧ u < ca(r) + cb(r) ∧
      (Column.bitsAt (concatBytes #[da, db]) (d * 8) 8).toNat = pa(r) + pb(r) + u ∧
      (d < len xa ↔ u < ca(r)) ∧ (d < len xa → d = pa(r) + u) ∧
      (len xa ≤ d → d = len xa + pb(r) + (u - ca(r))) := by
    intro d hd
    by_cases h : d < len xa
    · obtain ⟨r, t, hr, ht, e⟩ := hxa_at d h
      have hp := (hA r t hr ht).2
      rw [← e] at hp
      exact ⟨r, t, hr, by omega, by rw [hbg, if_pos h, hp], iff_of_true h ht, fun _ => e,
        fun h' => absurd h (by omega)⟩
    · obtain ⟨r, t, hr, ht, e⟩ := hxb_at (d - len xa) (by omega)
      have hp := (hB r t hr ht).2
      refine ⟨r, ca(r) + t, hr, by omega, ?_, iff_of_false h (by omega), fun h' => absurd h' h, fun _ => by omega⟩
      rw [hbg, if_neg h, e, hp]; omega
  have hblk : ∀ r, r < nN → pa(r) + pb(r) ≤ pa(r + 1) + pb(r + 1) := fun r _ => by
    rw [hpa_succ, hpb_succ]; omega
  have hinj : ∀ a b, a < len (concatBytes #[da, db]) → b < len (concatBytes #[da, db]) →
      Column.bitsAt (concatBytes #[da, db]) (a * 8) 8 = Column.bitsAt (concatBytes #[da, db]) (b * 8) 8 →
      a = b := by
    intro a b ha hb e
    rw [hbl] at ha hb
    obtain ⟨r, t, hr, ht, ea, ia1, ta1, la1⟩ := hval a ha
    obtain ⟨r', t', hr', ht', eb, ib1, tb1, lb1⟩ := hval b hb
    have e' := congrArg UInt64.toNat e
    rw [ea, eb] at e'
    obtain ⟨rfl, rfl⟩ := block_inj (P := fun r => pa(r) + pb(r)) hblk r t r' t' hr hr'
      (by have := hpa_succ r; have := hpb_succ r; dsimp only; omega)
      (by have := hpa_succ r'; have := hpb_succ r'; dsimp only; omega) e'
    by_cases h : a < len xa
    · have h' := ia1.1 h; rw [ta1 h, tb1 (ib1.2 h')]
    · have h' : ¬ b < len xa := fun hb' => h (ia1.2 (ib1.1 hb'))
      rw [la1 (by omega), lb1 (by omega)]
  have hpN : pa(nN) + pb(nN) = len (concatBytes #[da, db]) := by rw [hbl, hxal, hxbl]
  obtain ⟨hgl, hgk, hglt⟩ : ∃ hgl : (ids g).length = len (concatBytes #[da, db]),
      (∀ d (hd : d < len (concatBytes #[da, db])), (Column.bitsAt (concatBytes #[da, db])
        ((ids g)[d]'(Nat.lt_of_lt_of_eq hd hgl.symm) * 8) 8).toNat = d) ∧
      ∀ d (hd : d < len (concatBytes #[da, db])),
        (ids g)[d]'(Nat.lt_of_lt_of_eq hd hgl.symm) < len (concatBytes #[da, db]) := by
    subst hg
    exact grade_ofLongs_inv (concatBytes #[da, db]) (by omega) (by omega)
      (fun d hd => by
        rw [hbl] at hd
        obtain ⟨r, t, hr, ht, ea, -, -, -⟩ := hval d hd
        obtain ⟨cl1, cl2⟩ := hcl r hr
        rw [ea, ← hpN]; omega) hinj
  -- the grade at row `r`'s place `u`: the first side's copy below `ca(r)`, the second's past it
  have hgx : ∀ x d (hx : x < len (concatBytes #[da, db])), d < len (concatBytes #[da, db]) →
      (Column.bitsAt (concatBytes #[da, db]) (d * 8) 8).toNat = x →
      (ids g)[x]'(Nat.lt_of_lt_of_eq hx hgl.symm) = d := by
    intro x d hx hd e
    refine hinj _ _ (hglt x hx) hd (UInt64.toNat_inj.1 ?_)
    rw [hgk x hx, e]
  have hga : ∀ r t (hr : r < nN) (ht : t < ca(r)), (ids g)[pa(r) + pb(r) + t]'(by
      obtain ⟨cl1, cl2⟩ := hcl r hr; rw [hgl, ← hpN]; omega) = pa(r) + t := by
    intro r t hr ht
    obtain ⟨cl1, cl2⟩ := hcl r hr
    refine hgx _ _ (by rw [← hpN]; omega) (by rw [hbl, hxal]; omega) ?_
    rw [hbg, if_pos (show pa(r) + t < len xa by rw [hxal]; omega), (hA r t hr ht).2]
  have hgb : ∀ r t (hr : r < nN) (ht : t < cb(r)), (ids g)[pa(r) + pb(r) + ca(r) + t]'(by
      obtain ⟨cl1, cl2⟩ := hcl r hr; rw [hgl, ← hpN]; omega) = len xa + (pb(r) + t) := by
    intro r t hr ht
    obtain ⟨cl1, cl2⟩ := hcl r hr
    refine hgx _ _ (by rw [← hpN]; omega) (by rw [hbl, hxbl]; omega) ?_
    rw [hbg, if_neg (show ¬ len xa + (pb(r) + t) < len xa by omega), Nat.add_sub_cancel_left, (hB r t hr ht).2]
  refine ⟨hxaU, hxbU, hmaN, hmbN, hxal, hxbl, by rw [len_eq_ids, hgl, hbl], fun r hr => ⟨hhig r hr, hcg r hr⟩,
    fun r t hr ht => ⟨(hA r t hr ht).1, ?_⟩, fun r t hr ht => ⟨(hB r t hr ht).1, ?_⟩⟩
  · obtain ⟨cl1, cl2⟩ := hcl r hr
    rw [List.getElem?_eq_getElem (by rw [hgl, ← hpN]; omega), hga r t hr ht]
  · obtain ⟨cl1, cl2⟩ := hcl r hr
    rw [List.getElem?_eq_getElem (by rw [hgl, ← hpN]; omega), hgb r t hr ht]

/-- **`cat`'s row `r`, read back**: under `rep_cat`'s bound pieces and hypotheses, the result's row `r` is row `r`
    of the first side then row `r` of the second; the copies fit a `USize` (from `cat_places`). -/
theorem cat_row {K B : Obj} (P : Rel K (.prod (.arr B) (.arr B)))
    (hpa : (Rel.val P).1.1.toNat < 2 ^ 63) (hpb : (Rel.val P).2.1.toNat < 2 ^ 63)
    (sa : ByteArray × ByteArray) (hsa : sa = slicesOf (Rel.val P).1)
    (sb : ByteArray × ByteArray) (hsb : sb = slicesOf (Rel.val P).2)
    (hS : ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt sa.2 (r * 8) 8).toNat).sum +
      ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt sb.2 (r * 8) 8).toNat).sum < 2 ^ 63)
    (hU : ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt sa.2 (r * 8) 8).toNat).sum +
      ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt sb.2 (r * 8) 8).toNat).sum < USize.size)
    (xa : ByteArray) (hxa : xa = expandBytes 8 0 (tilLongs (Rel.n P)) sa.2)
    (ma : USize) (hma : ma = (len xa).toUSize)
    (ra : ByteArray) (hra : ra = sub ma (tilLongs ma) (gather 8 (sub (Rel.n P) (sums (Rel.n P) sa.2) sa.2) xa))
    (xb : ByteArray) (hxb : xb = expandBytes 8 0 (tilLongs (Rel.n P)) sb.2)
    (mb : USize) (hmb : mb = (len xb).toUSize)
    (rb : ByteArray) (hrb : rb = sub mb (tilLongs mb) (gather 8 (sub (Rel.n P) (sums (Rel.n P) sb.2) sb.2) xb))
    (ja : ByteArray) (hja : ja = add ma (gather 8 sa.1 xa) ra)
    (jb : ByteArray) (hjb : jb = add mb (gather 8 sb.1 xb) rb)
    (ta : Vals B ma) (hta : ta = Vals.pick B (Rel.val P).1.2.2.2 (add ma (gather 8 sa.1 xa) ra) ma
      (len_val Ew.add Ew.vv (gather 8 sa.1 xa) ra ma))
    (tb : Vals B mb) (htb : tb = Vals.pick B (Rel.val P).2.2.2.2 (add mb (gather 8 sb.1 xb) rb) mb
      (len_val Ew.add Ew.vv (gather 8 sb.1 xb) rb mb))
    (c : ByteArray) (hcs : c = add (Rel.n P) sa.2 sb.2) (hi : ByteArray) (hhi : hi = sums (Rel.n P) c)
    (lo : ByteArray) (hlo : lo = sub (Rel.n P) hi c)
    (da : ByteArray) (hda : da = add ma (gather 8 lo xa) ra)
    (db : ByteArray) (hdb : db = add mb (add mb (gather 8 lo xb) (gather 8 sa.2 xb)) rb)
    (g : ByteArray) (hg : g = (Code.ofLongs (concatBytes #[da, db])).grade)
    (hTa : Vals.PickFits B (Rel.val P).1.2.2.2 ((List.range ma.toNat).map fun q => (Column.bitsAt ja (q * 8) 8).toNat))
    (hTb : Vals.PickFits B (Rel.val P).2.2.2.2 ((List.range mb.toNat).map fun q => (Column.bitsAt jb (q * 8) 8).toNat))
    (hRf : Vals.RazeFits B ta tb)
    (hFf : ∀ hN, Vals.PickFits B (Obj.raze B #[⟨ma, ta⟩, ⟨mb, tb⟩] hN)
      ((List.range (len g)).map fun q => (Column.bitsAt g (q * 8) 8).toNat)) :
    len xa < USize.size ∧ len xb < USize.size ∧ ma.toNat + mb.toNat < USize.size ∧ len g < USize.size ∧
      ∀ (hpg : len g = ((len g).toUSize).toNat) hN (hh : (Rel.n P).toNat ≤ len hi) (r : Nat)
        (hr : r < (Rel.n P).toNat),
        Vals.row (A := .arr B) (⟨(len g).toUSize, valCol Ew.sub Ew.vv hi c, longsN (Rel.n P) hi hh,
          Vals.pick B (Obj.raze B #[⟨ma, ta⟩, ⟨mb, tb⟩] hN) g (len g).toUSize hpg⟩ :
            Vals (.arr B) (Rel.n P)) ⟨r, hr⟩ =
          Vals.row (Rel.val P).1 ⟨r, hr⟩ ++ Vals.row (Rel.val P).2 ⟨r, hr⟩ := by
  -- each side's payload rows are `ma`/`mb` longs: `ta`, `tb` pick at `ja`, `jb` themselves
  have hjal : len ja = ma.toNat := by rw [hja]; exact len_val ..
  replace hta : ta = Vals.pick B (Rel.val P).1.2.2.2 ja ma hjal := by subst hja; exact hta
  have hjbl : len jb = mb.toNat := by rw [hjb]; exact len_val ..
  replace htb : tb = Vals.pick B (Rel.val P).2.2.2.2 jb mb hjbl := by subst hjb; exact htb
  obtain ⟨hxaU, hxbU, hmaN, hmbN, hxal, hxbl, hglen, hHC, hA, hB⟩ := cat_places P hpa hpb sa hsa sb hsb hS hU
    xa hxa ma hma ra hra xb hxb mb hmb rb hrb ja hja jb hjb c hcs hi hhi lo hlo da hda db hdb g hg
  subst hsa hsb
  have hRa := fun r (hr : r < nN) => slicesOf_row (Rel.val P).1 hpa hr
  have hRb := fun r (hr : r < nN) => slicesOf_row (Rel.val P).2 hpb hr
  have hpa_le : ∀ a b, a ≤ b → pa(a) ≤ pa(b) := fun a b h => sum_range_le _ h
  have hpb_le : ∀ a b, a ≤ b → pb(a) ≤ pb(b) := fun a b h => sum_range_le _ h
  have hpa_succ : ∀ r, pa(r + 1) = pa(r) + ca(r) := fun r => sum_range_succ' _ r
  have hpb_succ : ∀ r, pb(r + 1) = pb(r) + cb(r) := fun r => sum_range_succ' _ r
  have hcl : ∀ r, r < nN → pa(r) + ca(r) ≤ pa(nN) ∧ pb(r) + cb(r) ≤ pb(nN) := fun r hr => by
    have h1 := hpa_le (r + 1) nN (by omega); have h2 := hpb_le (r + 1) nN (by omega)
    rw [hpa_succ] at h1; rw [hpb_succ] at h2; exact ⟨h1, h2⟩
  have hhig := fun r (hr : r < nN) => (hHC r hr).1
  have hcg := fun r (hr : r < nN) => (hHC r hr).2
  -- each side's cells read back: copy `pa(r) + t` is cell `t` of row `r`'s first array, likewise the second
  have hta_row : ∀ r t (hr : r < nN) (ht : t < (Vals.row (Rel.val P).1 ⟨r, hr⟩).length) a (ha : a < ma.toNat),
      a = pa(r) + t → ta.row ⟨a, ha⟩ = (Vals.row (Rel.val P).1 ⟨r, hr⟩)[t] := by
    intro r t hr ht a ha e
    subst e
    obtain ⟨hLa, hlna, hgeta⟩ := hRa r hr
    have hj := (hA r t hr (by omega)).1
    rw [hta, pick_row B _ ja ma hjal hTa, dif_pos (show (Column.bitsAt ja ((pa(r) + t) * 8) 8).toNat <
      (Rel.val P).1.1.toNat by rw [hj]; omega), hgeta t ht (by omega)]
    exact congrArg _ (Fin.ext hj)
  have htb_row : ∀ r t (hr : r < nN) (ht : t < (Vals.row (Rel.val P).2 ⟨r, hr⟩).length) a (ha : a < mb.toNat),
      a = pb(r) + t → tb.row ⟨a, ha⟩ = (Vals.row (Rel.val P).2 ⟨r, hr⟩)[t] := by
    intro r t hr ht a ha e
    subst e
    obtain ⟨hLb, hlnb, hgetb⟩ := hRb r hr
    have hj := (hB r t hr (by omega)).1
    rw [htb, pick_row B _ jb mb hjbl hTb, dif_pos (show (Column.bitsAt jb ((pb(r) + t) * 8) 8).toNat <
      (Rel.val P).2.1.toNat by rw [hj]; omega), hgetb t ht (by omega)]
    exact congrArg _ (Fin.ext hj)
  have hgU : len g < USize.size := by rw [hglen]; omega
  have hgN : ((len g).toUSize).toNat = pa(nN) + pb(nN) := by
    rw [USize.toNat_ofNat_of_lt' hgU, hglen, hxal, hxbl]
  -- row `r` of the result: the first array's cells, then the second's
  have hrow : ∀ (hpg : len g = ((len g).toUSize).toNat) hN (hh : (Rel.n P).toNat ≤ len hi) (r : Nat) (hr : r < nN),
      Vals.row (A := .arr B) (⟨(len g).toUSize, valCol Ew.sub Ew.vv hi c, longsN (Rel.n P) hi hh,
        Vals.pick B (Obj.raze B #[⟨ma, ta⟩, ⟨mb, tb⟩] hN) g (len g).toUSize hpg⟩ :
          Vals (.arr B) (Rel.n P)) ⟨r, hr⟩ =
        Vals.row (Rel.val P).1 ⟨r, hr⟩ ++ Vals.row (Rel.val P).2 ⟨r, hr⟩ := by
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
    have hcN := raze2_cnt ta tb hN
    obtain ⟨cl1, cl2⟩ := hcl r hr
    have e1 := hhig r hr; have e2 := hcg r hr; have e3 := hpa_succ r; have e4 := hpb_succ r
    have hsub : (Column.bitsAt (sub (Rel.n P) hi c) (r * 8) 8).toNat = pa(r) + pb(r) := by
      rw [sub_get (a := hi) (b := c) hr (by omega) (by omega)]; omega
    have hlo' : ((valCol (n := Rel.n P) Ew.sub Ew.vv hi c).get ⟨r, hr⟩).toInt = ((pa(r) + pb(r) : Nat) : Int) := by
      rw [valCol_get]; dsimp only
      rw [show Kernel.Ew.val Ew.sub Ew.i64 Ew.vv nul hi c (Rel.n P) = sub (Rel.n P) hi c from rfl,
        toInt64_toInt (x := Column.bitsAt (sub (Rel.n P) hi c) (r * 8) 8) (by omega), hsub]
    have hhi' : ((longsN (Rel.n P) hi hh).get ⟨r, hr⟩).toInt = ((pa(r + 1) + pb(r + 1) : Nat) : Int) := by
      rw [longsN_get]; dsimp only
      rw [toInt64_toInt (x := Column.bitsAt hi (r * 8) 8) (by omega), e1]
    have hrow := arr_row (b := B) (⟨(len g).toUSize, valCol (n := Rel.n P) Ew.sub Ew.vv hi c,
      longsN (Rel.n P) hi hh, Vals.pick B (Obj.raze B #[⟨ma, ta⟩, ⟨mb, tb⟩] hN) g (len g).toUSize hpg⟩ :
        Vals (.arr B) (Rel.n P)) ⟨r, hr⟩
    dsimp only at hrow
    rw [hlo', hhi'] at hrow
    have f1 : min (max ((pa(r) + pb(r) : Nat) : Int) 0).toNat ((len g).toUSize).toNat = pa(r) + pb(r) := by omega
    have f2 : min (max ((pa(r + 1) + pb(r + 1) : Nat) : Int) 0).toNat ((len g).toUSize).toNat =
        pa(r + 1) + pb(r + 1) := by omega
    rw [f1, f2] at hrow
    rw [hrow]
    obtain ⟨hLa, hlna, -⟩ := hRa r hr
    obtain ⟨hLb, hlnb, -⟩ := hRb r hr
    apply List.ext_getElem
    · rw [List.length_append, hlna, hlnb, List.length_map, List.length_range]; omega
    · intro u h1 h2
      have hb : pa(r) + pb(r) + u < ((len g).toUSize).toNat := by
        simp only [List.length_map, List.length_range] at h1; omega
      have hu2 : u < ca(r) + cb(r) := by simp only [List.length_map, List.length_range] at h1; omega
      rw [List.getElem_map, List.getElem_range, dif_pos hb]
      by_cases hu : u < ca(r)
      · rw [List.getElem_append_left (by omega), hpk _ hFf' ⟨_, hb⟩ ⟨pa(r) + u, by rw [hcN, hmaN]; omega⟩ (by
            dsimp only
            have hJ : pa(r) + pb(r) + u < (ids g).length := by rw [← len_eq_ids, hglen]; omega
            rw [← ids_getElem (b := g) (j := pa(r) + pb(r) + u) hJ]
            exact Option.some.inj ((List.getElem?_eq_getElem hJ).symm.trans (hA r u hr hu).2)),
          raze_row_full B ta tb hRf hN, dif_pos (show pa(r) + u < ma.toNat by omega)]
        exact hta_row r u hr (by omega) _ _ rfl
      · rw [List.getElem_append_right (by omega), hpk _ hFf' ⟨_, hb⟩
            ⟨len xa + (pb(r) + (u - ca(r))), by rw [hcN, hmaN, hmbN]; omega⟩ (by
            dsimp only
            have hJ : pa(r) + pb(r) + ca(r) + (u - ca(r)) < (ids g).length := by rw [← len_eq_ids, hglen]; omega
            rw [show pa(r) + pb(r) + u = pa(r) + pb(r) + ca(r) + (u - ca(r)) by omega,
              ← ids_getElem (b := g) (j := pa(r) + pb(r) + ca(r) + (u - ca(r))) hJ]
            exact Option.some.inj ((List.getElem?_eq_getElem hJ).symm.trans (hB r (u - ca(r)) hr (by omega)).2)),
          raze_row_full B ta tb hRf hN, dif_neg (show ¬ len xa + (pb(r) + (u - ca(r))) < ma.toNat by omega)]
        have hl1 : (Vals.row (Rel.val P).1 ⟨r, hr⟩).length = ca(r) := hlna
        have ht2 : u - (Vals.row (Rel.val P).1 ⟨r, hr⟩).length < (Vals.row (Rel.val P).2 ⟨r, hr⟩).length := by
          omega
        have ha2 : len xa + (pb(r) + (u - ca(r))) - ma.toNat < mb.toNat := by
          rw [hmaN, hmbN, hxbl, Nat.add_sub_cancel_left]; omega
        have ea2 : len xa + (pb(r) + (u - ca(r))) - ma.toNat = pb(r) + (u - (Vals.row (Rel.val P).1 ⟨r, hr⟩).length) := by
          rw [hmaN, Nat.add_sub_cancel_left, hl1]
        exact htb_row r _ hr ht2 _ ha2 ea2
  exact ⟨hxaU, hxbU, by omega, hgU, hrow⟩

/-- **`cat`, read back**: a row `(xs, ys)` of `P` goes to the array `xs ++ ys`, under its key. The pieces `cat`
    computes are bound by their equations: the slices `sa`, `sb` of `P`'s two sides, each side's `expand` index and
    rank columns (`xa`, `ra` at `ma` copies; `xb`, `rb` at `mb`), its payload rows `ja`, `jb` and cells `ta`, `tb`,
    the summed counts `c`, their running ends `hi` and starts `lo`, each side's places `da`, `db` and the grade `g`.
    Hypotheses: both payload counts below `2^63`; both sides' counts summed below `2^63` and a `USize`;
    `Vals.PickFits` where the key, the two payloads and the razed cells are picked, `Vals.RazeFits` of the cells.
    The rows are `cat_row`'s; this unfolds `cat` at its pieces. -/
theorem rep_cat {K B : Obj} (P : Rel K (.prod (.arr B) (.arr B)))
    (hpa : (Rel.val P).1.1.toNat < 2 ^ 63) (hpb : (Rel.val P).2.1.toNat < 2 ^ 63)
    (sa : ByteArray × ByteArray) (hsa : sa = slicesOf (Rel.val P).1)
    (sb : ByteArray × ByteArray) (hsb : sb = slicesOf (Rel.val P).2)
    (hS : ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt sa.2 (r * 8) 8).toNat).sum +
      ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt sb.2 (r * 8) 8).toNat).sum < 2 ^ 63)
    (hU : ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt sa.2 (r * 8) 8).toNat).sum +
      ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt sb.2 (r * 8) 8).toNat).sum < USize.size)
    (xa : ByteArray) (hxa : xa = expandBytes 8 0 (tilLongs (Rel.n P)) sa.2)
    (ma : USize) (hma : ma = (len xa).toUSize)
    (ra : ByteArray) (hra : ra = sub ma (tilLongs ma) (gather 8 (sub (Rel.n P) (sums (Rel.n P) sa.2) sa.2) xa))
    (xb : ByteArray) (hxb : xb = expandBytes 8 0 (tilLongs (Rel.n P)) sb.2)
    (mb : USize) (hmb : mb = (len xb).toUSize)
    (rb : ByteArray) (hrb : rb = sub mb (tilLongs mb) (gather 8 (sub (Rel.n P) (sums (Rel.n P) sb.2) sb.2) xb))
    (ja : ByteArray) (hja : ja = add ma (gather 8 sa.1 xa) ra)
    (jb : ByteArray) (hjb : jb = add mb (gather 8 sb.1 xb) rb)
    (ta : Vals B ma) (hta : ta = Vals.pick B (Rel.val P).1.2.2.2 (add ma (gather 8 sa.1 xa) ra) ma
      (len_val Ew.add Ew.vv (gather 8 sa.1 xa) ra ma))
    (tb : Vals B mb) (htb : tb = Vals.pick B (Rel.val P).2.2.2.2 (add mb (gather 8 sb.1 xb) rb) mb
      (len_val Ew.add Ew.vv (gather 8 sb.1 xb) rb mb))
    (c : ByteArray) (hcs : c = add (Rel.n P) sa.2 sb.2) (hi : ByteArray) (hhi : hi = sums (Rel.n P) c)
    (lo : ByteArray) (hlo : lo = sub (Rel.n P) hi c)
    (da : ByteArray) (hda : da = add ma (gather 8 lo xa) ra)
    (db : ByteArray) (hdb : db = add mb (add mb (gather 8 lo xb) (gather 8 sa.2 xb)) rb)
    (g : ByteArray) (hg : g = (Code.ofLongs (concatBytes #[da, db])).grade)
    (hKf : Vals.PickFits K (Rel.key P)
      ((List.range (Rel.n P).toNat).map fun q => (Column.bitsAt (tilLongs (Rel.n P)) (q * 8) 8).toNat))
    (hTa : Vals.PickFits B (Rel.val P).1.2.2.2 ((List.range ma.toNat).map fun q => (Column.bitsAt ja (q * 8) 8).toNat))
    (hTb : Vals.PickFits B (Rel.val P).2.2.2.2 ((List.range mb.toNat).map fun q => (Column.bitsAt jb (q * 8) 8).toNat))
    (hRf : Vals.RazeFits B ta tb)
    (hFf : ∀ hN, Vals.PickFits B (Obj.raze B #[⟨ma, ta⟩, ⟨mb, tb⟩] hN)
      ((List.range (len g)).map fun q => (Column.bitsAt g (q * 8) 8).toNat)) :
    ∀ k zs, rep (cat P) k zs ↔ ∃ xs ys, rep P k (xs, ys) ∧ zs = xs ++ ys := by
  obtain ⟨hxaU, hxbU, hkN, hgU, hrow⟩ := cat_row P hpa hpb sa hsa sb hsb hS hU xa hxa ma hma ra hra xb hxb mb hmb
    rb hrb ja hja jb hjb ta hta tb htb c hcs hi hhi lo hlo da hda db hdb g hg hTa hTb hRf hFf
  -- the key: `Vals.compact` reads back every row
  have hkey : ∀ q : Fin nN, (Vals.compact K (Rel.key P)).row q = (Rel.key P).row q := fun q => by
    rw [show Vals.compact K (Rel.key P) = Vals.pick K (Rel.key P) (tilLongs _) _ (len_tilLongs _) from rfl,
      pick_row K (Rel.key P) (tilLongs (Rel.n P)) (Rel.n P) (len_tilLongs _) hKf,
      dif_pos (show (Column.bitsAt (tilLongs (Rel.n P)) (q.1 * 8) 8).toNat < (Rel.n P).toNat by
        rw [tilLongs_get q.2]; exact q.2)]
    exact congrArg (Vals.row (Rel.key P)) (Fin.ext (tilLongs_get q.2))
  -- `cat` unfolded at its pieces
  intro k zs
  subst hma hmb
  subst hta htb hja hjb hg hda hdb hlo hhi hcs hra hrb hxa hxb hsa hsb
  unfold cat expand need
  dsimp only
  rw [dif_pos hxaU]
  try dsimp only
  rw [dif_pos hxbU]
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
  · rintro ⟨xs, ys, ⟨⟨r, hr⟩, hk, hv⟩, e⟩
    refine ⟨⟨r, hr⟩, (hkey _).trans hk, ?_⟩
    rw [hrow _ _ _ r hr, e, show xs = Vals.row (Rel.val P).1 ⟨r, hr⟩ from (congrArg Prod.fst hv).symm,
      show ys = Vals.row (Rel.val P).2 ⟨r, hr⟩ from (congrArg Prod.snd hv).symm]

open FoldN OpsN

/-- **`map`'s step, read back**: `cons (pair (el ≫ R) pend)` takes row `r`'s element `e` and list `u` to
    `b :: u` for each `b` with `e R b`. `Q = el ≫ R`, `P = pair Q pend` and the codes `jc`, `kc` are bound by
    their equations. Hypotheses: `rep_comp`'s at `el`, `R` (`hj…`), `rep_pair`'s at `Q`, `pend` (`hk…`),
    `rep_cons`'s at `P`. -/
theorem map_step_rep {E B : Obj} (el : Rel .long E) (R : Rel E B) (pend : Rel .long (.arr B))
    (jc : Vector Code 2)
    (hjc : jc = Obj.codes E (#v[⟨Rel.n el, Rel.val el⟩, ⟨Rel.n R, Rel.key R⟩] : Vector (Part E) 2))
    (hjO : codesOK(jc, (#v[⟨Rel.n el, Rel.val el⟩, ⟨Rel.n R, Rel.key R⟩] : Vector (Part E) 2)))
    (hjn : (Rel.n R).toNat < 2 ^ 63) (hjM : (Rel.n el).toNat * (Rel.n R).toNat < min (2 ^ 63) USize.size)
    (hjC : Vals.PickFits B (Rel.val R) ((mpairs(jc, el, R)).map Prod.snd))
    (Q : Rel .long B) (hQ : Q = el ≫ R)
    (kc : Vector Code 2) (hkc : kc = Obj.codes .long kp2(Q, pend))
    (hkO : (Rel.n Q).toNat + (Rel.n pend).toNat < USize.size)
    (hkn : (Rel.n pend).toNat < 2 ^ 63) (hkM : (Rel.n Q).toNat * (Rel.n pend).toNat < min (2 ^ 63) USize.size)
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
    (tl : Vals B m) (htl : tl = Vals.pick B (Rel.val P).2.2.2.2 (add m (gather 8 s.1 xi) xr) m
      (len_val Ew.add Ew.vv (gather 8 s.1 xi) xr m))
    (c1 : ByteArray) (hc1 : c1 = addc (Rel.n P) s.2 1) (hi : ByteArray) (hhi : hi = sums (Rel.n P) c1)
    (lo : ByteArray) (hlo : lo = sub (Rel.n P) hi c1)
    (dst : ByteArray) (hdst : dst = addc m (add m (gather 8 lo xi) xr) 1)
    (g : ByteArray) (hg : g = (Code.ofLongs (concatBytes #[dst, lo])).grade)
    (hTf : Vals.PickFits B (Rel.val P).2.2.2.2 ((List.range m.toNat).map fun q => (Column.bitsAt j (q * 8) 8).toNat))
    (hRf : Vals.RazeFits B tl (Rel.val P).1)
    (hFf : ∀ hN, Vals.PickFits B (Obj.raze B #[⟨m, tl⟩, ⟨Rel.n P, (Rel.val P).1⟩] hN)
      ((List.range (len g)).map fun q => (Column.bitsAt g (q * 8) 8).toNat)) :
    ∀ r v, rep (cons (pair (el ≫ R) pend)) r v ↔
      ∃ e u, rep el r e ∧ rep pend r u ∧ ∃ b, rep R e b ∧ v = b :: u := by
  subst hjc hkc
  have h2 := rep_comp el R hjO hjn hjM (pickFits_atom_fst _) hjC
  subst hQ
  have h1 := rep_pair (el ≫ R) pend (codesOK_long2 _ _ hkO) hkn hkM (pickFits_atom_fst _) hkB hkC
  subst hP
  intro r v
  rw [rep_cons (pair (el ≫ R) pend) hp s hs hS hU xi hxi m hm xr hxr j hj tl htl c1 hc1 hi hhi lo hlo
    dst hdst g hg (pickFits_tilLongs _) hTf hRf hFf, h1]
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

section MapFold

open QLean.Dep

/-- **`map`, read back**: `F(R)` takes an array `xs` of `X` to every `ys` of its length with `xs[t] R ys[t]` at each
    `t`. `rep_foldBy` at the step `cons (pair (el ≫ R) pend)` and the seed `nilVal B`, its chain closed by
    `map_chain`. Bound values and hypotheses as `rep_foldBy`'s (`step` bound by `hstep`), and `map_step_rep`'s at
    every round (`hC`, a per-round bundle, each bound value with its equation). -/
theorem rep_map {A B : Obj} {n : USize} (R : Rel A B) (X : Vals (.arr A) n)
    (T : Rel .long (.arr A)) (hT : T = num (idU X) 0) (hn : n.toNat < 2 ^ 63)
    (hv : Vals.PickFits (.arr A) X (List.range n.toNat))
    (pend₀ : Rel .long (.arr B)) (hpend : pend₀ = top (A := .long) (Rel.key T) (nilVal B))
    (hN : (Rel.n T).toNat * (1 : USize).toNat < USize.size)
    (h63 : (Rel.n T).toNat * (1 : USize).toNat < 2 ^ 63)
    (step : Rel .long A → Rel .long (.arr B) → Rel .long (.arr B))
    (hstep : step = fun el pend => cons (pair (el ≫ R) pend))
    (elK : Nat → Rel .long A) (hE : ∀ k, elK k = elR(T, k))
    (f : Rel .long (.arr B) × Rel .long (.arr B) × Nat → Rel .long (.arr B) × Rel .long (.arr B) × Nat)
    (hf : ∀ st, f st = rnd(st))
    (hR : ∀ i (el : Rel .long A) (pend P S : Rel .long (.arr B)), el = elK i →
      pend = (f^[i] (pend₀, Alg.zero, 0)).1 → P = (f^[i] (pend₀, Alg.zero, 0)).2.1 → S = step el pend →
      roundAt((.arr B)))
    (hC : ∀ i, i ≤ (Rel.val T).1.toNat → ∀ (el : Rel .long A) (pend : Rel .long (.arr B)), el = elK i →
      pend = (f^[i] (pend₀, Alg.zero, 0)).1 →
      ∀ jc : Vector Code 2, jc = Obj.codes A (#v[⟨Rel.n el, Rel.val el⟩, ⟨Rel.n R, Rel.key R⟩] : Vector (Part A) 2) →
      codesOK(jc, (#v[⟨Rel.n el, Rel.val el⟩, ⟨Rel.n R, Rel.key R⟩] : Vector (Part A) 2)) ∧
      (Rel.n R).toNat < 2 ^ 63 ∧ (Rel.n el).toNat * (Rel.n R).toNat < min (2 ^ 63) USize.size ∧
      Vals.PickFits B (Rel.val R) ((mpairs(jc, el, R)).map Prod.snd) ∧
      ∀ Q : Rel .long B, Q = el ≫ R →
      ∀ kc : Vector Code 2, kc = Obj.codes .long kp2(Q, pend) →
      (Rel.n Q).toNat + (Rel.n pend).toNat < USize.size ∧ (Rel.n pend).toNat < 2 ^ 63 ∧
      (Rel.n Q).toNat * (Rel.n pend).toNat < min (2 ^ 63) USize.size ∧
      Vals.PickFits B (Rel.val Q) ((mpairs(kc, Q, pend)).map Prod.fst) ∧
      Vals.PickFits (.arr B) (Rel.val pend) ((mpairs(kc, Q, pend)).map Prod.snd) ∧
      ∀ P : Rel .long (.prod B (.arr B)), P = pair Q pend →
      (Rel.val P).2.1.toNat < 2 ^ 63 ∧
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
      Vals.PickFits B (Rel.val P).2.2.2.2 ((List.range m.toNat).map fun q => (Column.bitsAt j (q * 8) 8).toNat) ∧
      Vals.RazeFits B tl (Rel.val P).1 ∧
      ∀ hN, Vals.PickFits B (Obj.raze B #[⟨m, tl⟩, ⟨Rel.n P, (Rel.val P).1⟩] hN)
        ((List.range (len g)).map fun q => (Column.bitsAt g (q * 8) 8).toNat))
    (F : Rel .long (.arr B)) (hF : F = foldRows T pend₀ step)
    (jc : Vector Code 2) (hjc : jc = Obj.codes .long ck2(T°, F)) (hjO : codesOK(jc, ck2(T°, F)))
    (hjn : (Rel.n F).toNat < 2 ^ 63) (hjM : (Rel.n (T°)).toNat * (Rel.n F).toNat < min (2 ^ 63) USize.size)
    (hjA : Vals.PickFits (.arr A) (Rel.key (T°)) ((mpairs(jc, T°, F)).map Prod.fst))
    (hjC : Vals.PickFits (.arr B) (Rel.val F) ((mpairs(jc, T°, F)).map Prod.snd)) :
    ∀ (xs : List A.El) ys, rep (Alg.map R X) xs ys ↔ (∃ i, X.row i = xs) ∧ ys.length = xs.length ∧
      ∀ t (ht : t < xs.length) (ht' : t < ys.length), rep R (xs[t]'ht) (ys[t]'ht') := by
  subst hstep
  intro xs ys
  -- round `i`'s step read back: `map_step_rep` at the round's element and state
  have hS : ∀ i, i ≤ (Rel.val T).1.toNat → ∀ r v,
      rep (cons (pair (elK i ≫ R) (f^[i] (pend₀, Alg.zero, 0)).1)) r v ↔
      ∃ e u, rep (elK i) r e ∧ rep (f^[i] (pend₀, Alg.zero, 0)).1 r u ∧ ∃ b, rep R e b ∧ v = b :: u := by
    intro i hi r v
    obtain ⟨hjO, hjn, hjM, hjC, hQ⟩ := hC i hi _ _ rfl rfl _ rfl
    obtain ⟨hkO, hkn, hkM, hkB, hkC, hP⟩ := hQ _ rfl _ rfl
    obtain ⟨hp, hs⟩ := hP _ rfl
    obtain ⟨hS, hU, hx⟩ := hs _ rfl
    obtain ⟨hTf, hRf, hFf⟩ := hx _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
    exact map_step_rep _ R _ _ rfl hjO hjn hjM hjC _ rfl _ rfl hkO hkn hkM hkB hkC _ rfl hp _ rfl
      hS hU _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl hTf hRf hFf r v
  refine (rep_foldBy (nilVal B) X T hT hn hv pend₀ hpend hN h63 (pickFits_nilVal B _)
    (fun el pend => cons (pair (el ≫ R) pend)) (fun _ eu v => ∃ b, rep R eu.1 b ∧ v = b :: eu.2) elK hE f hf hR hS
    F hF jc hjc hjO hjn hjM hjA hjC xs ys).trans ?_
  -- `nilVal B`'s one row is `[]`
  exact and_congr Iff.rfl ((exists_congr fun zs => exists_congr fun _ => and_congr
    ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨⟨0, by simp⟩, h.symm⟩⟩ Iff.rfl).trans (map_chain (rep R) xs ys))

end MapFold

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.Rep.rep_uncons
#print axioms LeetQ.Rel.Rep.rep_cons
#print axioms LeetQ.Rel.Rep.map_chain
#print axioms LeetQ.Rel.Rep.expand_at
#print axioms LeetQ.Rel.Rep.cat_places
#print axioms LeetQ.Rel.Rep.cat_row
#print axioms LeetQ.Rel.Rep.rep_cat
#print axioms LeetQ.Rel.Rep.map_step_rep
#print axioms LeetQ.Rel.Rep.rep_map
