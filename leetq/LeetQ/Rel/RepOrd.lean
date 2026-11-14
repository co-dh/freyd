/-
  `rep` of the order relations `lt` and `leq` at `long`, read in `Rel(Set)`: the pairs of elements of `U` in
  `Int64` order. `lt` compares q's ordinal ranks (`rank_long`) of every pair of positions (`cross`) and drops the
  pairs of one value, which the ranks put apart by position.
-/
import LeetQ.Rel.RepArith
import LeetQ.Rel.KernelWF.RankSpec
import LeetQ.Rel.KernelWF.RazeFoR

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
    (hc : pairsOK(L, idU U)) (hk : Vals.PickFits (.atom .long) L.key (ids (misses(L, idU U))))
    (hv : Vals.PickFits (.atom .long) L.val (ids (misses(L, idU U)))) (a b : Int64) :
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
    (hc : pairsOK(L, idU U)) (hk : Vals.PickFits (.atom .long) L.key (ids (misses(L, idU U))))
    (hv : Vals.PickFits (.atom .long) L.val (ids (misses(L, idU U))))
    (hNU : (Rel.n (lt U h)).toNat + (Rel.n (idU U)).toNat < USize.size)
    (hNk : ((pk(lt U h, idU U)).toList.map fun c : Part (.atom .long) => c.1.toNat).sum < USize.size)
    (hNv : ((pv(lt U h, idU U)).toList.map fun c : Part (.atom .long) => c.1.toNat).sum < USize.size)
    (hFk : Vals.RazeFits (.atom .long) (Rel.key (lt U h)) (Rel.key (idU U)))
    (hFv : Vals.RazeFits (.atom .long) (Rel.val (lt U h)) (Rel.val (idU U)))
    (V : Rel (.atom .long) (.atom .long)) (hV : V = Uc(lt U h, idU U, hNk, hNv))
    (huK : cOK(kcR(V), Rel.n V, Rel.key V)) (huV : cOK(vcR(V), Rel.n V, Rel.val V))
    (huk : Vals.PickFits (.atom .long) (Rel.key V) (ids nubR(V)))
    (huv : Vals.PickFits (.atom .long) (Rel.val V) (ids nubR(V))) (a b : Int64) :
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

#print axioms cmp_lt_small
#print axioms lt_rows_holds
#print axioms rep_lt
#print axioms rep_leq

end LeetQ.Rel.Rep
