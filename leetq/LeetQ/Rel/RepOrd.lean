/-
  `rep` of the order relations `lt` and `leq` at `long`, read in `Rel(Set)`: the pairs of elements of `U` in
  `Int64` order. `lt` compares q's ordinal ranks (`rank_long`) of every pair of positions (`cross`) and drops the
  pairs of one value, which the ranks put apart by position.
-/
import LeetQ.Rel.RepArith
import LeetQ.Rel.KernelWF.RankSpec
import LeetQ.Rel.KernelWF.RazeFoR
import LeetQ.Rel.RepList

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

/-- `Ew.cmp lt` at `long` on two longs below `2^63`: their order as numbers. -/
theorem cmp_lt_small {v w : UInt64} (hv : v.toNat < 2 ^ 63) (hw : w.toNat < 2 ^ 63) :
    Ew.cmpStep Ew.lt Ew.i64 v w = true ↔ v.toNat < w.toNat := by
  have e : ∀ u : UInt64, u.toNat < 2 ^ 63 → u.toInt64.toInt = u.toNat := fun u hu => by
    have : u.toInt64.toInt = if 2 * u.toNat < 2 ^ 64 then (u.toNat : Int) else (u.toNat : Int) - 2 ^ 64 := by
      rw [Int64.toInt, BitVec.toInt_eq_toNat_cond]; rfl
    rw [this, if_pos (by omega)]
  show Ew.cmpStep Ew.lt Ew.i64 v.toInt64.toUInt64 w.toInt64.toUInt64 = true ↔ _
  rw [cmpStep_i64]
  simp only [show (Ew.lt == Ew.eq) = false by decide, show (Ew.lt == Ew.ne) = false by decide,
    show (Ew.lt == Ew.lt) = true by decide, Bool.false_eq_true, if_false, if_true, beq_iff_eq, compare_lt_iff,
    Int64.lt_iff_toInt_lt, e v hv, e w hw]
  omega

/-- A column of `n` rows picked at `c@w`, `c` holding `f t` at each of its `N` rows: row `q` is row `f w[q]`. -/
theorem pick_gather_at {n : USize} (U : Vals (.atom .long) n) (c : ByteArray) (N : Nat) (f : Nat → Nat)
    (hc : len c = N) (hg : ∀ t, t < N → (Column.bitsAt c (t * 8) 8).toNat = f t) (hf : ∀ t, t < N → f t < n.toNat)
    (w : ByteArray) (r : USize) (hr : len (gather 8 c w) = r.toNat) (q : Fin r.toNat)
    (hin : (Column.bitsAt w (q.1 * 8) 8).toNat < N) :
    (Vals.pick _ U (gather 8 c w) r hr).row q =
      if ht : f (Column.bitsAt w (q.1 * 8) 8).toNat < n.toNat then U.row ⟨_, ht⟩ else default := by
  have hq : q.1 < len w := by rw [← gather_len c w, hr]; exact q.2
  have e : (Column.bitsAt (gather 8 c w) (q.1 * 8) 8).toNat = f (Column.bitsAt w (q.1 * 8) 8).toNat := by
    rw [gather8_get hq (by rw [hc]; exact hin), hg _ hin]
  rw [dif_pos (hf _ hin), pick_row_atom _ _ _ _ q (by rw [e]; exact hf _ hin)]
  exact congrArg U.row (Fin.ext e)

section
attribute [local irreducible] whereBits gather cross Ew.cmp longsOf Ops.rank

/-- The rows `lt` builds before it drops the pairs of one value: `(U[p], U[q])` for every pair of positions whose
    ranks ascend — by value, ties by position (`rank_long`). Hypotheses: the pair count fits a `USize` and is
    below `2^63` (`cross_ids`'s). -/
theorem lt_rows_holds {n : USize} (U : Vals (.atom .long) n) (h : QAtomicType.long ≠ .general)
    (hN : n.toNat * n.toNat < USize.size) (h63 : n.toNat * n.toNat < 2 ^ 63) (L : Rel (.atom .long) (.atom .long))
    (hL : L = longCount "<" (cross n n).1 fun nn _ =>
      longCount "<" (whereBits nn (Ew.cmp Ew.lt Ew.i64 Ew.vv (gather 8 (longsOf (Ops.rank U h)) (cross n n).1)
          (gather 8 (longsOf (Ops.rank U h)) (cross n n).2) nn)) fun k hk =>
        ⟨k, Vals.pick _ U (gather 8 (cross n n).1 (whereBits nn (Ew.cmp Ew.lt Ew.i64 Ew.vv
            (gather 8 (longsOf (Ops.rank U h)) (cross n n).1) (gather 8 (longsOf (Ops.rank U h)) (cross n n).2) nn)))
            k ((gather_len _ _).trans hk),
          Vals.pick _ U (gather 8 (cross n n).2 (whereBits nn (Ew.cmp Ew.lt Ew.i64 Ew.vv
            (gather 8 (longsOf (Ops.rank U h)) (cross n n).1) (gather 8 (longsOf (Ops.rank U h)) (cross n n).2) nn)))
            k ((gather_len _ _).trans hk)⟩)
    (a b : Int64) :
    L.Holds a b ↔ ∃ p q, ∃ (hp : p < n.toNat) (hq : q < n.toNat),
      U.row ⟨p, hp⟩ = a ∧ U.row ⟨q, hq⟩ = b ∧ (a < b ∨ (a = b ∧ p < q)) := by
  subst hL
  have hc1 : len (cross n n).1 = n.toNat * n.toNat := by
    rw [len_eq_ids, (cross_ids hN h63).1, List.length_map, List.length_range]
  have hc2 : len (cross n n).2 = n.toNat * n.toNat := by
    rw [len_eq_ids, (cross_ids hN h63).2, List.length_map, List.length_range]
  have g1 : ∀ t, t < n.toNat * n.toNat → (Column.bitsAt (cross n n).1 (t * 8) 8).toNat = t / n.toNat :=
    fun t ht => by rw [ids_get (cross_ids hN h63).1 (by simpa using ht)]; simp
  have g2 : ∀ t, t < n.toNat * n.toNat → (Column.bitsAt (cross n n).2 (t * 8) 8).toNat = t % n.toNat :=
    fun t ht => by rw [ids_get (cross_ids hN h63).2 (by simpa using ht)]; simp
  have hdm : ∀ t, t < n.toNat * n.toNat → t / n.toNat < n.toNat ∧ t % n.toNat < n.toNat := fun t ht =>
    ⟨Nat.div_lt_of_lt_mul ht, Nat.mod_lt _ (Nat.pos_of_ne_zero fun e => by rw [e, Nat.zero_mul] at ht; omega)⟩
  have hnn : ((len (cross n n).1).toUSize).toNat = n.toNat * n.toNat := by
    rw [USize.toNat_ofNat_of_lt' (by rw [hc1]; exact hN), hc1]
  rw [longCount_eq _ _ _ (by rw [hc1]; exact hN)]
  generalize hR : longsOf (Ops.rank U h) = r
  have hrl : len r = n.toNat := by rw [← hR]; exact len_longsOf _
  have hbit : ∀ t, t < n.toNat * n.toNat →
      (Column.bitAt (Ew.cmp Ew.lt Ew.i64 Ew.vv (gather 8 r (cross n n).1) (gather 8 r (cross n n).2)
        ((len (cross n n).1).toUSize)) t = true ↔
        (Column.bitsAt r (t / n.toNat * 8) 8).toNat < (Column.bitsAt r (t % n.toNat * 8) 8).toNat) := fun t ht => by
    obtain ⟨hd, hm⟩ := hdm t ht
    have hn63 : n.toNat < 2 ^ 63 := Nat.lt_of_le_of_lt (Nat.le_mul_self _) h63
    have b1 := (rank_long U h hd hd).1
    have b2 := (rank_long U h hm hm).1
    rw [hR] at b1 b2
    rw [(cmp_bitAt _ _ _ _ _ _).2 t (by rw [hnn]; omega)]
    simp only [Ew.shapeIdx, show (Ew.vv == Ew.vv) = true by decide, ↓reduceIte, elem_i64]
    rw [gather8_get (by rw [hc1]; exact ht) (by rw [g1 t ht, hrl]; exact hd),
      gather8_get (by rw [hc2]; exact ht) (by rw [g2 t ht, hrl]; exact hm), g1 t ht, g2 t ht,
      Bool.and_eq_true, decide_eq_true_eq, cmp_lt_small (by omega) (by omega)]
    exact ⟨fun h => h.2, fun h => ⟨by rw [hnn]; exact ht, h⟩⟩
  refine (holds_where (K := .atom .long) (V := .atom .long) "<" ((len (cross n n).1).toUSize)
      (Ew.cmp Ew.lt Ew.i64 Ew.vv (gather 8 r (cross n n).1) (gather 8 r (cross n n).2) ((len (cross n n).1).toUSize))
      (fun r' hr' => Vals.pick _ U (gather 8 (cross n n).1 (whereBits ((len (cross n n).1).toUSize)
        (Ew.cmp Ew.lt Ew.i64 Ew.vv (gather 8 r (cross n n).1) (gather 8 r (cross n n).2)
          ((len (cross n n).1).toUSize)))) r' ((gather_len _ _).trans hr'))
      (fun r' hr' => Vals.pick _ U (gather 8 (cross n n).2 (whereBits ((len (cross n n).1).toUSize)
        (Ew.cmp Ew.lt Ew.i64 Ew.vv (gather 8 r (cross n n).1) (gather 8 r (cross n n).2)
          ((len (cross n n).1).toUSize)))) r' ((gather_len _ _).trans hr'))
      (fun t => if ht : t / n.toNat < n.toNat then U.row ⟨_, ht⟩ else default)
      (fun t => if ht : t % n.toNat < n.toNat then U.row ⟨_, ht⟩ else default) ?_ ?_ a b).trans ?_
  · intro r' hr' q hin
    rw [hnn] at hin
    exact pick_gather_at U _ _ (· / n.toNat) hc1 g1 (fun t ht => (hdm t ht).1) _ r' _ q hin
  · intro r' hr' q hin
    rw [hnn] at hin
    exact pick_gather_at U _ _ (· % n.toNat) hc2 g2 (fun t ht => (hdm t ht).2) _ r' _ q hin
  · rw [hnn]
    constructor
    · rintro ⟨t, ht, hb, hg, hh⟩
      obtain ⟨hd, hm⟩ := hdm t ht
      rw [dif_pos hd] at hg; rw [dif_pos hm] at hh
      have hk := (rank_long U h hd hm).2
      rw [hR] at hk
      refine ⟨_, _, hd, hm, hg, hh, ?_⟩
      rw [← hg, ← hh]; exact hk.1 ((hbit t ht).1 hb)
    · rintro ⟨p, q, hp, hq, hg, hh, hlt⟩
      obtain ⟨ht, hd, hm⟩ := cross_at (ma := n) (mb := n) hp hq
      refine ⟨p * n.toNat + q, ht, ?_, ?_, ?_⟩
      · rw [hbit _ ht]
        have hk := (rank_long U h (hdm _ ht).1 (hdm _ ht).2).2
        rw [hR] at hk
        refine hk.2 ?_
        simp only [hd, hm]
        show U.row ⟨p, hp⟩ < U.row ⟨q, hq⟩ ∨ (U.row ⟨p, hp⟩ = U.row ⟨q, hq⟩ ∧ p < q)
        rw [hg, hh]; exact hlt
      · simp only [hd, dif_pos hp]; exact hg
      · simp only [hm, dif_pos hq]; exact hh

end

open OpsN UnionN

/-- **`rep (lt U)` at `long`**: the pairs of elements of `U` in `Int64` order, q's null `0N` the least. The rows
    of every pair of positions whose ranks ascend (`lt_rows_holds`), less the pairs of one value (`rep_diff`).
    Hypotheses: the pair count fits a `USize` and is below `2^63`; `L` names the rows before the diff;
    `rep_diff`'s, at `L` and `idU U`. -/
theorem rep_lt {n : USize} (U : Vals (.atom .long) n) (h : QAtomicType.long ≠ .general)
    (hN : n.toNat * n.toNat < USize.size) (h63 : n.toNat * n.toNat < 2 ^ 63) (L : Rel (.atom .long) (.atom .long))
    (hL : L = longCount "<" (cross n n).1 fun nn _ =>
      longCount "<" (whereBits nn (Ew.cmp Ew.lt Ew.i64 Ew.vv (gather 8 (longsOf (Ops.rank U h)) (cross n n).1)
          (gather 8 (longsOf (Ops.rank U h)) (cross n n).2) nn)) fun k hk =>
        ⟨k, Vals.pick _ U (gather 8 (cross n n).1 (whereBits nn (Ew.cmp Ew.lt Ew.i64 Ew.vv
            (gather 8 (longsOf (Ops.rank U h)) (cross n n).1) (gather 8 (longsOf (Ops.rank U h)) (cross n n).2) nn)))
            k ((gather_len _ _).trans hk),
          Vals.pick _ U (gather 8 (cross n n).2 (whereBits nn (Ew.cmp Ew.lt Ew.i64 Ew.vv
            (gather 8 (longsOf (Ops.rank U h)) (cross n n).1) (gather 8 (longsOf (Ops.rank U h)) (cross n n).2) nn)))
            k ((gather_len _ _).trans hk)⟩)
    (hc : pairsOK(L, idU U)) (hk : Vals.PickFits (.atom .long) L.key (List.range L.n.toNat))
    (hv : Vals.PickFits (.atom .long) L.val (List.range L.n.toNat)) (a b : Int64) :
    rep (lt U h) a b ↔ (∃ i, U.row i = a) ∧ (∃ j, U.row j = b) ∧ a < b := by
  have e : lt U h = L \ idU U := by subst hL; rfl
  rw [e, rep_diff L (idU U) hc hk hv, rep_apply, rep_apply, lt_rows_holds U h hN h63 L hL, idU_holds]
  constructor
  · rintro ⟨⟨p, q, hp, hq, hg, hh, hlt⟩, hne⟩
    exact ⟨⟨_, hg⟩, ⟨_, hh⟩, hlt.resolve_right fun ⟨e, _⟩ => hne ⟨e, _, hg⟩⟩
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩, hlt⟩
    exact ⟨⟨i.1, j.1, i.2, j.2, hi, hj, .inl hlt⟩, fun ⟨e, _⟩ => by subst e; exact Int64.lt_irrefl hlt⟩

/-- **`rep (leq U)` at `long`**: the pairs of elements of `U` in `Int64` order or equal. `leq U = lt U ∪ 𝟙`:
    `rep_union_full`, then `rep_lt` and `idU_holds`. Hypotheses: `rep_lt`'s; `rep_union_full`'s at `lt U h`,
    `idU U`, with `V` naming the razed union. -/
theorem rep_leq {n : USize} (U : Vals (.atom .long) n) (h : QAtomicType.long ≠ .general)
    (hN : n.toNat * n.toNat < USize.size) (h63 : n.toNat * n.toNat < 2 ^ 63) (L : Rel (.atom .long) (.atom .long))
    (hL : L = longCount "<" (cross n n).1 fun nn _ =>
      longCount "<" (whereBits nn (Ew.cmp Ew.lt Ew.i64 Ew.vv (gather 8 (longsOf (Ops.rank U h)) (cross n n).1)
          (gather 8 (longsOf (Ops.rank U h)) (cross n n).2) nn)) fun k hk =>
        ⟨k, Vals.pick _ U (gather 8 (cross n n).1 (whereBits nn (Ew.cmp Ew.lt Ew.i64 Ew.vv
            (gather 8 (longsOf (Ops.rank U h)) (cross n n).1) (gather 8 (longsOf (Ops.rank U h)) (cross n n).2) nn)))
            k ((gather_len _ _).trans hk),
          Vals.pick _ U (gather 8 (cross n n).2 (whereBits nn (Ew.cmp Ew.lt Ew.i64 Ew.vv
            (gather 8 (longsOf (Ops.rank U h)) (cross n n).1) (gather 8 (longsOf (Ops.rank U h)) (cross n n).2) nn)))
            k ((gather_len _ _).trans hk)⟩)
    (hc : pairsOK(L, idU U)) (hk : Vals.PickFits (.atom .long) L.key (List.range L.n.toNat))
    (hv : Vals.PickFits (.atom .long) L.val (List.range L.n.toNat))
    (hNU : (Rel.n (lt U h)).toNat + (Rel.n (idU U)).toNat < USize.size)
    (hNk : ((pk(lt U h, idU U)).toList.map fun c : Part (.atom .long) => c.1.toNat).sum < USize.size)
    (hNv : ((pv(lt U h, idU U)).toList.map fun c : Part (.atom .long) => c.1.toNat).sum < USize.size)
    (hFk : Vals.RazeFits (.atom .long) (Rel.key (lt U h)) (Rel.key (idU U)))
    (hFv : Vals.RazeFits (.atom .long) (Rel.val (lt U h)) (Rel.val (idU U)))
    (V : Rel (.atom .long) (.atom .long)) (hV : V = Uc(lt U h, idU U, hNk, hNv))
    (huK : cOK(kcR(V), Rel.n V, Rel.key V)) (huV : cOK(vcR(V), Rel.n V, Rel.val V))
    (huk : Vals.PickFits (.atom .long) (Rel.key V) (List.range (Rel.n V).toNat))
    (huv : Vals.PickFits (.atom .long) (Rel.val V) (List.range (Rel.n V).toNat)) (a b : Int64) :
    rep (leq U h) a b ↔ (∃ i, U.row i = a) ∧ (∃ j, U.row j = b) ∧ a ≤ b := by
  subst hV
  have e : leq U h = lt U h ∪ idU U := rfl
  rw [e, rep_union_full (lt U h) (idU U) hNU hNk hNv hFk hFv huK huV huk huv, Freyd.Alg.RelSet.union_apply,
    rep_lt U h hN h63 L hL hc hk hv, rep_apply, idU_holds, Int64.le_iff_lt_or_eq]
  constructor
  · rintro (⟨ha, hb, hlt⟩ | ⟨e, ha⟩)
    · exact ⟨ha, hb, .inl hlt⟩
    · exact ⟨ha, e ▸ ha, .inr e⟩
  · rintro ⟨ha, hb, hlt | e⟩
    · exact .inl ⟨ha, hb, hlt⟩
    · exact .inr ⟨e, ha⟩

-- row `r`'s count in `X` and the counts before it
set_option hygiene false in
local notation "cc(" r ")" => (Column.bitsAt (slicesOf X).2 (r * 8) 8).toNat
set_option hygiene false in
local notation "pc(" r ")" => ((List.range r).map fun u => (Column.bitsAt (slicesOf X).2 (u * 8) 8).toNat).sum

/-- **`bagify`'s row `r`, read back**: under `rep_bagify`'s bound pieces and hypotheses, the result's row `r` is a
    permutation of row `r` of `X`, ascending; the copies fit a `USize` (`expand_at`). The pieces: `expand`'s
    index and rank columns `xi`, `xr` at `m` copies, the cells `cells`, the regrouped grade `p`. -/
theorem bag_row {n : USize} (X : Vals (.arr (.atom .long)) n) (hp : X.1.toNat < 2 ^ 63) (hn : n.toNat < 2 ^ 63)
    (hS : pc(n.toNat) < 2 ^ 63) (hU : pc(n.toNat) < USize.size)
    (xi : ByteArray) (hxi : xi = expandBytes 8 0 (tilLongs n) (slicesOf X).2)
    (m : USize) (hm : m = (len xi).toUSize)
    (xr : ByteArray) (hxr : xr = sub m (tilLongs m) (gather 8 (sub n (sums n (slicesOf X).2) (slicesOf X).2) xi))
    (cells : Vals (.atom .long) m) (hc : cells = Vals.pick (.atom .long) X.2.2.2
      (add m (gather 8 (slicesOf X).1 xi) xr) m (len_val Ew.add Ew.vv (gather 8 (slicesOf X).1 xi) xr m))
    (p : ByteArray) (hpg : p = gather 8 (Obj.sortBy (.atom .long) cells (tilLongs m))
      (Code.ofLongs (gather 8 xi (Obj.sortBy (.atom .long) cells (tilLongs m)))).grade) :
    len xi < USize.size ∧ len p = m.toNat ∧
      ∀ (q : USize) (hq : len p = q.toNat) (hh : n.toNat ≤ len (sums n (slicesOf X).2)) (r : Nat)
        (hr : r < n.toNat) (ys : List Int64), ys = Vals.row (A := .arr (.atom .long))
          (⟨q, valCol Ew.sub Ew.vv (sums n (slicesOf X).2) (slicesOf X).2, longsN n (sums n (slicesOf X).2) hh,
            Vals.pick (.atom .long) cells p q hq⟩ : Vals (.arr (.atom .long)) n) ⟨r, hr⟩ →
        ys.Perm (X.row ⟨r, hr⟩) ∧ ys.Pairwise (· ≤ ·) := by
  have hs1 : len (slicesOf X).1 = n.toNat := (len_slices _ _ _ _).1
  have hs2 : len (slicesOf X).2 = n.toNat := (len_slices _ _ _ _).2
  have hR := fun r (hr : r < n.toNat) => slicesOf_row X hp hr
  have hpc_le : ∀ a b, a ≤ b → pc(a) ≤ pc(b) := fun a b h => sum_range_le _ h
  have hpc_succ : ∀ r, pc(r + 1) = pc(r) + cc(r) := fun r => sum_range_succ' _ r
  have hcl : ∀ r, r < n.toNat → pc(r) + cc(r) ≤ pc(n.toNat) := fun r hr => by
    have h := hpc_le (r + 1) n.toNat (by omega); rw [hpc_succ] at h; exact h
  obtain ⟨hxl, hx_in, hx_at⟩ := expand_at (n := n) (slicesOf X).2 hs2 hS hU xi hxi xr (by rw [hxr, hm])
  have hxU : len xi < USize.size := by omega
  have hmN : m.toNat = len xi := by rw [hm]; exact USize.toNat_ofNat_of_lt' hxU
  -- copy `pc(r) + t` is cell `t` of row `r`
  have hcell : ∀ r t (hr : r < n.toNat) (ht : t < (X.row ⟨r, hr⟩).length) (hd : pc(r) + t < m.toNat),
      cells.row ⟨pc(r) + t, hd⟩ = (X.row ⟨r, hr⟩)[t] := by
    intro r t hr ht hd
    obtain ⟨hLC, hln, hget⟩ := hR r hr
    have htc : t < cc(r) := by omega
    obtain ⟨hx, hrk⟩ := hx_in r t hr htc
    have hdx : pc(r) + t < len xi := by omega
    have hgs : Column.bitsAt (gather 8 (slicesOf X).1 xi) ((pc(r) + t) * 8) 8 =
        Column.bitsAt (slicesOf X).1 (r * 8) 8 := by
      rw [gather8_get hdx (by rw [hx, hs1]; exact hr), hx]
    have hj : (Column.bitsAt (add m (gather 8 (slicesOf X).1 xi) xr) ((pc(r) + t) * 8) 8).toNat =
        (Column.bitsAt (slicesOf X).1 (r * 8) 8).toNat + t := by
      rw [add_get hd (by rw [hgs, hrk]; omega), hgs, hrk]
    subst hc
    rw [pick_row_atom _ _ _ _ ⟨pc(r) + t, hd⟩ (by rw [hj]; omega), hget t ht (by omega)]
    exact congrArg _ (Fin.ext hj)
  -- every copy is of row `xi[c]`, in that row's block
  have hkey : ∀ c, c < len xi → (Column.bitsAt xi (c * 8) 8).toNat < n.toNat ∧
      pc((Column.bitsAt xi (c * 8) 8).toNat) ≤ c ∧ c < pc((Column.bitsAt xi (c * 8) 8).toNat + 1) := by
    intro c hc
    obtain ⟨r, t, hr, ht, rfl⟩ := hx_at c hc
    rw [(hx_in r t hr ht).1, hpc_succ]; omega
  -- the cells sorted by value, then regrouped stably by row
  generalize hv : Obj.sortBy (.atom .long) cells (tilLongs m) = v at hpg
  obtain ⟨hvp, hvs⟩ := sortBy_long cells
  rw [hv, hmN] at hvp; rw [hv] at hvs
  obtain ⟨hpp, hps⟩ := grade_group xi v hvp _ hvs hxU (fun c hc => by have := (hkey c hc).1; omega)
  rw [← hpg] at hpp hps
  have hlp : len p = m.toNat := by rw [len_eq_ids, hpp.length_eq, List.length_range, hmN]
  have hpm : ∀ a, a ∈ ids p → a < m.toNat := fun a ha => by rw [hmN]; exact List.mem_range.1 (hpp.mem_iff.1 ha)
  refine ⟨hxU, hlp, fun q hq hh r hr ys hys => ?_⟩
  have hqN : q.toNat = pc(n.toNat) := by rw [← hq, hlp, hmN, hxl]
  have hcr := hcl r hr
  have e1 := hpc_succ r
  have hsum : (Column.bitsAt (sums n (slicesOf X).2) (r * 8) 8).toNat = pc(r + 1) := by
    rw [sums_get hr (by rw [hs2]; exact hr) (by omega)]
  have hsub : (Column.bitsAt (sub n (sums n (slicesOf X).2) (slicesOf X).2) (r * 8) 8).toNat = pc(r) := by
    rw [sub_get hr (by rw [hsum]; omega) (by rw [hsum]; omega), hsum]; omega
  have hlo : ((valCol (n := n) Ew.sub Ew.vv (sums n (slicesOf X).2) (slicesOf X).2).get ⟨r, hr⟩).toInt =
      ((pc(r) : Nat) : Int) := by
    rw [valCol_get]; dsimp only
    rw [show Kernel.Ew.val Ew.sub Ew.i64 Ew.vv nul (sums n (slicesOf X).2) (slicesOf X).2 n =
        sub n (sums n (slicesOf X).2) (slicesOf X).2 from rfl,
      toInt64_toInt (x := Column.bitsAt (sub n (sums n (slicesOf X).2) (slicesOf X).2) (r * 8) 8) (by omega), hsub]
  have hhi : ((longsN n (sums n (slicesOf X).2) hh).get ⟨r, hr⟩).toInt = ((pc(r + 1) : Nat) : Int) := by
    rw [longsN_get]; dsimp only
    rw [toInt64_toInt (x := Column.bitsAt (sums n (slicesOf X).2) (r * 8) 8) (by omega), hsum]
  have hrow := arr_row (b := .atom .long) (⟨q, valCol (n := n) Ew.sub Ew.vv (sums n (slicesOf X).2) (slicesOf X).2,
    longsN n (sums n (slicesOf X).2) hh, Vals.pick (.atom .long) cells p q hq⟩ : Vals (.arr (.atom .long)) n) ⟨r, hr⟩
  dsimp only at hrow
  rw [hlo, hhi] at hrow
  have f1 : min (max ((pc(r) : Nat) : Int) 0).toNat q.toNat = pc(r) := by omega
  have f2 : min (max ((pc(r + 1) : Nat) : Int) 0).toNat q.toNat = pc(r + 1) := by omega
  rw [f1, f2] at hrow
  -- the row is the block `[pc(r), pc(r+1))` of the grade, each copy read as its cell
  let F : Nat → Int64 := fun c => if h : c < m.toNat then cells.row ⟨c, h⟩ else default
  have hlen : ((ids p).drop pc(r)).length ≥ cc(r) := by
    rw [List.length_drop, ← len_eq_ids, hlp, hmN, hxl]; omega
  have hys : ys = (((ids p).drop pc(r)).take cc(r)).map F := by
    rw [hys, hrow]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, List.length_take]; omega
    · intro u h1 h2
      simp only [List.length_map, List.length_range] at h1
      have hb : pc(r) + u < q.toNat := by omega
      have hJ : pc(r) + u < (ids p).length := by rw [← len_eq_ids, hlp, hmN, hxl]; omega
      have hin : (ids p)[pc(r) + u] < m.toNat := hpm _ (List.getElem_mem hJ)
      rw [List.getElem_map, List.getElem_range, dif_pos hb, List.getElem_map, List.getElem_take, List.getElem_drop]
      dsimp only [F]
      rw [dif_pos hin, pick_row_atom _ _ _ _ ⟨pc(r) + u, hb⟩ (by rw [← ids_getElem hJ]; exact hin)]
      exact congrArg _ (Fin.ext (ids_getElem hJ).symm)
  have hX : X.row ⟨r, hr⟩ = (List.range' pc(r) cc(r)).map F := by
    obtain ⟨-, hln, -⟩ := hR r hr
    apply List.ext_getElem
    · rw [hln, List.length_map, List.length_range']
    · intro t h1 h2
      have hd : pc(r) + t < m.toNat := by rw [hmN, hxl]; omega
      rw [List.getElem_map, List.getElem_range']
      dsimp only [F]
      rw [Nat.one_mul, dif_pos hd, hcell r t hr h1 hd]
  have hblk := sorted_block_perm (ids p) (fun c => (Column.bitsAt xi (c * 8) 8).toNat) (fun r => pc(r)) hpp
    (hps.imp fun h => h.elim Nat.le_of_lt fun h => Nat.le_of_eq h.1) (fun r _ => hpc_le r (r + 1) (by omega))
    hxl.symm (fun c hc => hkey c hc) r hr
  have e2 : pc(r + 1) - pc(r) = cc(r) := by omega
  simp only [e2] at hblk
  refine ⟨by rw [hys, hX]; exact hblk.map F, ?_⟩
  rw [hys, List.pairwise_map]
  -- inside the block every copy is of row `r`, so the stable regroup keeps the value order
  have hkr : ∀ a, a ∈ ((ids p).drop pc(r)).take cc(r) → (Column.bitsAt xi (a * 8) 8).toNat = r := by
    intro a ha
    obtain ⟨h1, h2⟩ := List.mem_range'_1.1 (hblk.mem_iff.1 ha)
    have ha' : a < len xi := by omega
    obtain ⟨hk, k1, k2⟩ := hkey a ha'
    rcases Nat.lt_trichotomy (Column.bitsAt xi (a * 8) 8).toNat r with h | h | h
    · have := hpc_le ((Column.bitsAt xi (a * 8) 8).toNat + 1) r h; omega
    · exact h
    · have := hpc_le (r + 1) (Column.bitsAt xi (a * 8) 8).toNat h; omega
  refine (hps.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))).imp_of_mem fun {a b} ha hb h => ?_
  have ham := hpm a (((List.take_sublist _ _).trans (List.drop_sublist _ _)).subset ha)
  have hbm := hpm b (((List.take_sublist _ _).trans (List.drop_sublist _ _)).subset hb)
  rw [hkr a ha, hkr b hb] at h
  rcases h with h | ⟨-, h⟩
  · exact absurd h (Nat.lt_irrefl _)
  · dsimp only [F]
    rw [dif_pos ham, dif_pos hbm, Vals.row_atom, Vals.row_atom, Int64.le_iff_lt_or_eq]
    rcases h ham hbm with h | ⟨h, -⟩
    · exact .inl h
    · exact .inr h

/-- **`rep (bagify X)` at `long`**: an array of `X` goes to `ys` exactly when `ys` is a permutation of it,
    ascending — the one sorted member of its `perm` class. Hypotheses: the payload count, the row count and the
    summed counts below `2^63` (`xi`'s rows are graded as longs), the summed counts a `USize` (`expand`'s copies),
    `Vals.PickFits` where `Vals.compact` picks `X`. -/
theorem rep_bagify {n : USize} (X : Vals (.arr (.atom .long)) n) (hp : X.1.toNat < 2 ^ 63)
    (hn : n.toNat < 2 ^ 63) (hS : pc(n.toNat) < 2 ^ 63) (hU : pc(n.toNat) < USize.size)
    (hKf : Vals.PickFits (.arr (.atom .long)) X
      ((List.range n.toNat).map fun q => (Column.bitsAt (tilLongs n) (q * 8) 8).toNat)) :
    ∀ xs ys, rep (bagify X) xs ys ↔ (∃ j, X.row j = xs) ∧ ys.Perm xs ∧ ys.Pairwise (· ≤ ·) := by
  have hkey : ∀ q : Fin n.toNat, (Vals.compact _ X).row q = X.row q := fun q => by
    rw [show Vals.compact _ X = Vals.pick _ X (tilLongs _) _ (len_tilLongs _) from rfl,
      pick_row _ X (tilLongs n) n (len_tilLongs _) hKf,
      dif_pos (show (Column.bitsAt (tilLongs n) (q.1 * 8) 8).toNat < n.toNat by rw [tilLongs_get q.2]; exact q.2)]
    exact congrArg (Vals.row X) (Fin.ext (tilLongs_get q.2))
  obtain ⟨hxU, hlp, hrow⟩ := bag_row X hp hn hS hU _ rfl _ rfl _ rfl _ rfl _ rfl
  intro xs ys
  unfold bagify expand need
  dsimp only
  rw [dif_pos hxU]
  try dsimp only
  rw [longCount_eq _ _ _ (by rw [hlp]; exact USize.toNat_lt_size _)]
  show (∃ q, _ ∧ _) ↔ _
  constructor
  · rintro ⟨⟨r, hr⟩, hk, hv⟩
    exact ⟨⟨⟨r, hr⟩, (hkey _).symm.trans hk⟩, hk ▸ (hkey _).symm ▸ hrow _ _ _ r hr ys hv.symm⟩
  · rintro ⟨⟨⟨j, hj⟩, hx⟩, hpe, hs⟩
    refine ⟨⟨j, hj⟩, (hkey _).trans hx, ?_⟩
    obtain ⟨hpe', hs'⟩ := hrow _ _ (sums_le (len_slices ..).2) j hj _ rfl
    rw [hx] at hpe'
    exact (List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => Int64.le_antisymm h1 h2) hs' hs
      (hpe'.trans hpe.symm))

#print axioms bag_row
#print axioms rep_bagify
#print axioms cmp_lt_small
#print axioms lt_rows_holds
#print axioms rep_lt
#print axioms rep_leq

end LeetQ.Rel.Rep
