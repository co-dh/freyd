/-
  The divisions of `Rel`, read back. `leftDiv R S Ub Uc` joins `R.nub` and `S.nub` on the shared key into rows
  `(y, z)` (the `y` part, as `≫` joins), keeps the first row of each pair whose count equals the count of `y`
  among `R.nub`'s values (`leftDiv_keep`), and adds `⊤` on the values of `Ub` that are no value of `R` and `Uc`.
-/
import LeetQ.Rel.RepOps
import LeetQ.Rel.KernelWF.DivSpec
import LeetQ.Rel.KernelWF.CountSpec
import LeetQ.Rel.KernelWF.CodesAll
import LeetQ.Rel.KernelWF.RazeFoR
import LeetQ.Rel.RepOps2

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg

variable {A B C : Obj}

/-! The notations `rep_leftDiv`/`rep_rightDiv` state their hypotheses with: `open DivN` to state them elsewhere
    (`c1`, `nubI`, `PQ` are `FoldN`'s, downstream). Every name they use is an argument. -/
namespace DivN

-- the pairs `(i, j)` `join l r` answers, as `join_rows` lists them: row `i` of `l`, row `j` of `r`, equal codes
set_option quotPrecheck false in
scoped notation "jp(" l ", " r ")" => ((List.range (Code.n l).toNat).flatMap fun i =>
  ((List.range (Code.n r).toNat).filter fun j =>
    Column.idAt (Code.b r) (Code.w r) j == Column.idAt (Code.b l) (Code.w l) i).map (i, ·))
-- `leftDiv`'s `y` over the key codes `l`, `k`: the joined rows `(r`'s value, `s`'s value`)`, as `leftDiv` builds it.
-- The objects are arguments, not captured, so a notation that expands to this one passes its own
set_option quotPrecheck false in
scoped notation "yJ(" B ", " C ", " r ", " s ", " l ", " k ")" => (longCount "\\" (join l k).2 fun m h =>
  (⟨m, Vals.pickN B (Rel.val r) (join l k).1 m (h ▸ join_len l k), Vals.pick C (Rel.val s) (join l k).2 m h⟩ :
    Rel B C))
-- `leftDiv`'s vacuous side at its joint codes `ycs`, the universe `Ub`
set_option quotPrecheck false in
scoped notation "vacY(" B ", " Ub ", " ycs ")" =>
  Vals.pickPart B Ub (anti (ycs[2]'(Nat.lt_add_one 2)) (ycs[1]'(Nat.succ_lt_succ (Nat.zero_lt_succ 1))))

end DivN

open DivN OpsN

/-- **`leftDiv`'s joined rows, read back**: one row per pair `(i, j)` of `join l r`, in its order, `x`'s row `i`
    beside `z`'s row `j`. Stated over any two codes, not `leftDiv`'s, so the statement holds no `Obj.codes`.
    Hypotheses: `join_rows`', and each side picks back at its rows of the pairs. -/
theorem div_y_rows {n₁ n₂ : USize} (l r : Code) (x : Vals B n₁) (z : Vals C n₂) (hln : l.n = n₁) (hrn' : r.n = n₂)
    (hlw : laneOK(l.w))
    (hls : l.b.size = (l.n.toNat * l.w + 7) / 8)
    (hrw : laneOK(r.w))
    (hrs : r.b.size = (r.n.toNat * r.w + 7) / 8)
    (hrc : r.w < 8 → r.card < USize.size ∧ ∀ i < r.n.toNat, Column.idAt r.b r.w i < r.card)
    (hrn : r.n.toNat < 2 ^ 63)
    (hM : ((List.range l.n.toNat).map fun i => ((List.range r.n.toNat).filter fun j =>
      Column.idAt r.b r.w j == Column.idAt l.b l.w i).length).sum < 2 ^ 63)
    (hMU : ((List.range l.n.toNat).map fun i => ((List.range r.n.toNat).filter fun j =>
      Column.idAt r.b r.w j == Column.idAt l.b l.w i).length).sum < USize.size)
    (hB : Vals.PickFits B x ((jp(l, r)).map Prod.fst)) (hC : Vals.PickFits C z ((jp(l, r)).map Prod.snd))
    (m : USize) (hmJ : len (join l r).2 = m.toNat) (hle : m.toNat ≤ len (join l r).1) :
    m.toNat = (jp(l, r)).length ∧
      ∀ (q : Nat) (hq : q < m.toNat), ∃ (hJ : q < (jp(l, r)).length)
        (hi : ((jp(l, r))[q]'hJ).1 < n₁.toNat) (hj : ((jp(l, r))[q]'hJ).2 < n₂.toNat),
        (Vals.pickN B x (join l r).1 m hle).row ⟨q, hq⟩ = x.row ⟨_, hi⟩ ∧
        (Vals.pick C z (join l r).2 m hmJ).row ⟨q, hq⟩ = z.row ⟨_, hj⟩ := by
  subst hln hrn'
  obtain ⟨-, hZ⟩ := join_rows l r hlw hls hrw hrs hrc hrn hM hMU
  have e := hZ m hmJ
  have hfB : Vals.PickFits B x
      ((List.range m.toNat).map fun q => (Column.bitsAt (fit m.toNat (join l r).1) (q * 8) 8).toNat) := by
    rw [show ((List.range m.toNat).map fun q => (Column.bitsAt (fit m.toNat (join l r).1) (q * 8) 8).toNat) =
      (jp(l, r)).map Prod.fst by rw [e, List.map_map]; rfl]; exact hB
  have hfC : Vals.PickFits C z ((List.range m.toNat).map fun q => (Column.bitsAt (join l r).2 (q * 8) 8).toNat) := by
    rw [show ((List.range m.toNat).map fun q => (Column.bitsAt (join l r).2 (q * 8) 8).toNat) =
      (jp(l, r)).map Prod.snd by rw [e, List.map_map]; rfl]; exact hC
  have hlen : m.toNat = (jp(l, r)).length := by rw [e, List.length_map, List.length_range]
  refine ⟨hlen, fun q hq => ?_⟩
  have hJ : q < (jp(l, r)).length := by rw [← hlen]; exact hq
  have hq' : (jp(l, r))[q]'hJ = ((Column.bitsAt (fit m.toNat (join l r).1) (q * 8) 8).toNat,
      (Column.bitsAt (join l r).2 (q * 8) 8).toNat) := by
    rw [List.getElem_of_eq e hJ]; simp only [List.getElem_map, List.getElem_range]
  have hmem := List.getElem_mem hJ
  rw [hq'] at hmem
  obtain ⟨hi, hj, -⟩ := (mem_joinPairs l r _ _).1 hmem
  refine ⟨hJ, by rw [hq']; exact hi, by rw [hq']; exact hj, ?_, ?_⟩
  · unfold Vals.pickN
    rw [pick_row B x _ m _ hfB ⟨q, hq⟩, dif_pos hi]
    exact congrArg x.row (Fin.ext (congrArg Prod.fst hq').symm)
  · rw [pick_row C z _ m hmJ hfC ⟨q, hq⟩, dif_pos hj]
    exact congrArg z.row (Fin.ext (congrArg Prod.snd hq').symm)

/-- **`leftDiv`'s `y`, read back**: `div_y_rows` at the count `longCount` enters with, which `join_rows` bounds. -/
theorem div_y_holds (r : Rel A B) (s : Rel A C) (l k : Code) (hln : l.n = r.n) (hkn : k.n = s.n)
    (hlw : laneOK(l.w))
    (hls : l.b.size = (l.n.toNat * l.w + 7) / 8)
    (hrw : laneOK(k.w))
    (hrs : k.b.size = (k.n.toNat * k.w + 7) / 8)
    (hrc : k.w < 8 → k.card < USize.size ∧ ∀ i < k.n.toNat, Column.idAt k.b k.w i < k.card)
    (hrn : k.n.toNat < 2 ^ 63)
    (hM : ((List.range l.n.toNat).map fun i => ((List.range k.n.toNat).filter fun j =>
      Column.idAt k.b k.w j == Column.idAt l.b l.w i).length).sum < 2 ^ 63)
    (hMU : ((List.range l.n.toNat).map fun i => ((List.range k.n.toNat).filter fun j =>
      Column.idAt k.b k.w j == Column.idAt l.b l.w i).length).sum < USize.size)
    (hB : Vals.PickFits B r.val ((jp(l, k)).map Prod.fst)) (hC : Vals.PickFits C s.val ((jp(l, k)).map Prod.snd)) :
    (yJ(B, C, r, s, l, k)).n.toNat = (jp(l, k)).length ∧
      ∀ (q : Nat) (hq : q < (yJ(B, C, r, s, l, k)).n.toNat), ∃ (hJ : q < (jp(l, k)).length)
        (hi : ((jp(l, k))[q]'hJ).1 < r.n.toNat) (hj : ((jp(l, k))[q]'hJ).2 < s.n.toNat),
        (yJ(B, C, r, s, l, k)).key.row ⟨q, hq⟩ = r.val.row ⟨_, hi⟩ ∧ (yJ(B, C, r, s, l, k)).val.row ⟨q, hq⟩ = s.val.row ⟨_, hj⟩ := by
  obtain ⟨hlt, -⟩ := join_rows l k hlw hls hrw hrs hrc hrn hM hMU
  unfold longCount need
  rw [dif_pos hlt]
  dsimp only
  have hm : len (join l k).2 = ((len (join l k).2).toUSize).toNat := (USize.toNat_ofNat_of_lt' hlt).symm
  exact div_y_rows l k r.val s.val hln hkn hlw hls hrw hrs hrc hrn hM hMU hB hC _ hm (hm ▸ join_len l k)

-- a pair of code columns read as one key per row, the key `tupleIds` groups by (as `DivSpec`'s)
local notation "key2(" a ", " b ")" => fun i => (Column.idAt (Code.b a) (Code.w a) i, Column.idAt (Code.b b) (Code.w b) i)

/-- **`leftDiv`'s counted part, read back**: `y`, the rows of `join l k` (`div_y_rows`) as `(r`'s value, `s`'s
    value`)`, kept at `leftDiv_keep`'s rows, holds `(b, c)` exactly when every `a` that `r` takes to `b` `s` takes to
    `c`, and some `a` is taken to `b`. Hypotheses: `l`, `k` code `r.key`, `s.key` jointly; `yc`, `zc` code `y`'s
    sides, `rv` codes `r.val` jointly with `yc`; `s`'s rows are distinct; `y` picks back at the kept rows. -/
theorem div_keep_holds (r : Rel A B) (s : Rel A C) (y : Rel B C) (l k yc zc rv : Code) (I : ByteArray)
    (hy : y.n.toNat = (jp(l, k)).length ∧ ∀ (q : Nat) (hq : q < y.n.toNat), ∃ (hJ : q < (jp(l, k)).length)
      (hi : ((jp(l, k))[q]'hJ).1 < r.n.toNat) (hj : ((jp(l, k))[q]'hJ).2 < s.n.toNat),
      y.key.row ⟨q, hq⟩ = r.val.row ⟨_, hi⟩ ∧ y.val.row ⟨q, hq⟩ = s.val.row ⟨_, hj⟩)
    (hln : l.n = r.n) (hkn : k.n = s.n)
    (hlk : ∀ {i j : Nat} (hi : i < r.n.toNat) (hj : j < s.n.toNat),
      Column.idAt k.b k.w j = Column.idAt l.b l.w i ↔ r.key.row ⟨i, hi⟩ = s.key.row ⟨j, hj⟩)
    (hs : ∀ j j' : Fin s.n.toNat, s.key.row j = s.key.row j' → s.val.row j = s.val.row j' → j = j')
    (hyn : yc.n = y.n)
    (hyc : ∀ {q q' : Nat} (hq : q < y.n.toNat) (hq' : q' < y.n.toNat),
      Column.idAt yc.b yc.w q = Column.idAt yc.b yc.w q' ↔ y.key.row ⟨q, hq⟩ = y.key.row ⟨q', hq'⟩)
    (hzc : ∀ {q q' : Nat} (hq : q < y.n.toNat) (hq' : q' < y.n.toNat),
      Column.idAt zc.b zc.w q = Column.idAt zc.b zc.w q' ↔ y.val.row ⟨q, hq⟩ = y.val.row ⟨q', hq'⟩)
    (hrn : rv.n = r.n)
    (hrv : ∀ {j q : Nat} (hj : j < r.n.toNat) (hq : q < y.n.toNat),
      Column.idAt rv.b rv.w j = Column.idAt yc.b yc.w q ↔ r.val.row ⟨j, hj⟩ = y.key.row ⟨q, hq⟩)
    (hI : ids I = ((List.range (firstsOf key2(yc, zc) yc.n.toNat).length).filter fun t =>
      decide (((List.range yc.n.toNat).filter fun q =>
          decide (key2(yc, zc) q = key2(yc, zc) ((firstsOf key2(yc, zc) yc.n.toNat).getD t 0))).length =
        ((List.range rv.n.toNat).filter fun j =>
          Column.idAt rv.b rv.w j == Column.idAt yc.b yc.w ((firstsOf key2(yc, zc) yc.n.toNat).getD t 0)).length)).map
      fun t => (firstsOf key2(yc, zc) yc.n.toNat).getD t 0)
    (hk : Vals.PickFits B y.key (ids I)) (hv : Vals.PickFits C y.val (ids I)) (b : B.El) (c : C.El) :
    (y.rows I).Holds b c ↔ (∀ a, r.Holds a b → s.Holds a c) ∧ ∃ a, r.Holds a b := by
  classical
  obtain ⟨hyl, hyr⟩ := hy
  -- the kept rows: first rows `p` whose pair's count equals `r`'s count of `p`'s value
  have hI' : ids I = (List.range y.n.toNat).filter fun p =>
      decide (p ∈ firstsOf key2(yc, zc) y.n.toNat) && decide (((List.range y.n.toNat).filter fun q =>
          decide (key2(yc, zc) q = key2(yc, zc) p)).length =
        ((List.range r.n.toNat).filter fun j => Column.idAt rv.b rv.w j == Column.idAt yc.b yc.w p).length) := by
    rw [hI, hyn, hrn]
    refine (filter_getD_map _ 0 (fun p => decide (((List.range y.n.toNat).filter fun q =>
          decide (key2(yc, zc) q = key2(yc, zc) p)).length =
        ((List.range r.n.toNat).filter fun j => Column.idAt rv.b rv.w j == Column.idAt yc.b yc.w p).length))).trans ?_
    unfold firstsOf
    rw [List.filter_filter]
    refine List.filter_congr fun p hp => ?_
    rw [Bool.and_comm]; congr 1
    rw [Bool.eq_iff_iff, decide_eq_true_iff, List.mem_filter]; exact ⟨fun h => ⟨hp, h⟩, fun h => h.2⟩
  rw [rows_keep y I _ hI' hk hv b c]
  -- the count at a row `p` holding `(b, c)`, against the rows of `join l k`
  have hcount : ∀ p (hp : p < y.n.toNat), y.key.row ⟨p, hp⟩ = b → y.val.row ⟨p, hp⟩ = c →
      ((((List.range y.n.toNat).filter fun q => decide (key2(yc, zc) q = key2(yc, zc) p)).length =
        ((List.range r.n.toNat).filter fun j => Column.idAt rv.b rv.w j == Column.idAt yc.b yc.w p).length) ↔
        ∀ a, r.Holds a b → s.Holds a c) := by
    intro p hp hb hc
    let qf : Nat → Bool := fun j => decide (∃ hj : j < s.n.toNat, s.val.row ⟨j, hj⟩ = c)
    let pf : Nat → Bool := fun i => Column.idAt rv.b rv.w i == Column.idAt yc.b yc.w p
    have h1 : ((List.range y.n.toNat).filter fun q => decide (key2(yc, zc) q = key2(yc, zc) p)).length =
        ((jp(l, k)).filter fun ij => pf ij.1 && qf ij.2).length := by
      rw [← filter_getD_map (jp(l, k)) (0, 0), List.length_map, ← hyl]
      congr 1
      refine List.filter_congr fun q hq => ?_
      have hq := List.mem_range.1 hq
      obtain ⟨hJ, hi, hj, e1, e2⟩ := hyr q hq
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJ, Option.getD_some]
      have hi' : ((jp(l, k))[q]'hJ).1 < r.n.toNat := hi
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff, Prod.mk.injEq,
        hyc hq hp, hzc hq hp, hrv hi' hp, e1, e2, hb, hc]
      exact ⟨fun ⟨u, v⟩ => ⟨u, hj, v⟩, fun ⟨u, _, v⟩ => ⟨u, v⟩⟩
    have hinj : ∀ i < l.n.toNat, ∀ j j', j < k.n.toNat → j' < k.n.toNat →
        (Column.idAt k.b k.w j == Column.idAt l.b l.w i) = true → qf j = true →
        (Column.idAt k.b k.w j' == Column.idAt l.b l.w i) = true → qf j' = true → j = j' := by
      intro i hi j j' hj hj' e q e' q'
      rw [hln] at hi; rw [hkn] at hj hj'
      obtain ⟨_, hc1⟩ := decide_eq_true_iff.1 q
      obtain ⟨_, hc2⟩ := decide_eq_true_iff.1 q'
      have k1 := (hlk hi hj).1 (beq_iff_eq.1 e)
      have k2 := (hlk hi hj').1 (beq_iff_eq.1 e')
      exact congrArg Fin.val (hs ⟨j, hj⟩ ⟨j', hj'⟩ (k1.symm.trans k2) (hc1.trans hc2.symm))
    rw [h1, ← hln, count_pairs l.n.toNat k.n.toNat _ pf qf hinj]
    constructor
    · rintro h a ⟨⟨i, hi⟩, ha, hib⟩
      have hi' : i < l.n.toNat := by rw [hln]; exact hi
      have hp' : pf i = true := by
        show (Column.idAt rv.b rv.w i == Column.idAt yc.b yc.w p) = true
        rw [beq_iff_eq, hrv hi hp, hb]; exact hib
      obtain ⟨j, hj, e, q⟩ := h i hi' hp'
      obtain ⟨hj', hc'⟩ := decide_eq_true_iff.1 q
      exact ⟨⟨j, hj'⟩, ((hlk hi hj').1 (beq_iff_eq.1 e)).symm.trans ha, hc'⟩
    · intro h i hi hp'
      rw [hln] at hi
      have hib : r.val.row ⟨i, hi⟩ = b := by rw [← hb]; exact (hrv hi hp).1 (beq_iff_eq.1 hp')
      obtain ⟨⟨j, hj⟩, hja, hjc⟩ := h _ ⟨⟨i, hi⟩, rfl, hib⟩
      refine ⟨j, by rw [hkn]; exact hj, beq_iff_eq.2 ((hlk hi hj).2 hja.symm), decide_eq_true_iff.2 ⟨hj, hjc⟩⟩
  constructor
  · rintro ⟨⟨p, hp⟩, hb, hc, hf⟩
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at hf
    obtain ⟨hJ, hi, hj, e1, e2⟩ := hyr p hp
    exact ⟨(hcount p hp hb hc).1 hf.2, _, ⟨_, hi⟩, rfl, e1.symm.trans hb⟩
  · rintro ⟨h, a, ⟨i, ha, hib⟩⟩
    obtain ⟨⟨j, hj⟩, hja, hjc⟩ := h a ⟨i, ha, hib⟩
    have hmem : (i.1, j) ∈ jp(l, k) := (mem_joinPairs l k _ _).2
      ⟨by rw [hln]; exact i.2, by rw [hkn]; exact hj, (hlk i.2 hj).2 (ha.trans hja.symm)⟩
    obtain ⟨q, hJ, hq⟩ := List.getElem_of_mem hmem
    have hq' : q < y.n.toNat := by rw [hyl]; exact hJ
    obtain ⟨hJ', hi', hj', e1, e2⟩ := hyr q hq'
    have eb : y.key.row ⟨q, hq'⟩ = b := by rw [e1, ← hib]; congr 2; rw [hq]
    have ec : y.val.row ⟨q, hq'⟩ = c := by rw [e2, ← hjc]; congr 2; rw [hq]
    obtain ⟨p, hpf, hpq⟩ := exists_first (g := key2(yc, zc)) (m := y.n.toNat) hq'
    have hp := firsts_lt _ _ hpf
    have hpb : y.key.row ⟨p, hp⟩ = b := by
      rw [← eb, ← hyc hp hq']; exact congrArg Prod.fst hpq
    have hpc : y.val.row ⟨p, hp⟩ = c := by
      rw [← ec, ← hzc hp hq']; exact congrArg Prod.snd hpq
    refine ⟨⟨p, hp⟩, hpb, hpc, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    exact ⟨hpf, (hcount p hp hpb hpc).2 h⟩

/-- **`Vals.pickPart` read back**: an element is a row of `x` picked at `I` exactly when it is `x`'s row at a
    position `I` lists. Hypotheses: `I`'s count fits a `USize`, its positions are rows of `x`, `x` picks back there. -/
theorem pickPart_rows {n : USize} (x : Vals B n) (I : ByteArray) (hL : len I < USize.size)
    (hlt : ∀ t ∈ ids I, t < n.toNat) (hP : Vals.PickFits B x (ids I)) (u : B.El) :
    (∃ i, (Vals.pickPart B x I).2.row i = u) ↔ ∃ t ∈ ids I, ∃ ht : t < n.toNat, x.row ⟨t, ht⟩ = u := by
  have hpd : Vals.pickPart B x I = ⟨(len I).toUSize, Vals.pick B x I _ (USize.toNat_ofNat_of_lt' hL).symm⟩ := by
    unfold Vals.pickPart need; rw [dif_pos hL]
  have hLn : ((len I).toUSize).toNat = len I := USize.toNat_ofNat_of_lt' hL
  rw [hpd]; dsimp only
  have hfit : Vals.PickFits B x
      ((List.range ((len I).toUSize).toNat).map fun q => (Column.bitsAt I (q * 8) 8).toNat) := by
    rw [hLn]; exact hP
  constructor
  · rintro ⟨⟨q, hq⟩, e⟩
    have hq' : q < (ids I).length := by rw [← len_eq_ids, ← hLn]; exact hq
    have ht := hlt _ (List.getElem_mem hq')
    rw [ids_getElem hq'] at ht
    rw [pick_row B x I _ _ hfit ⟨q, hq⟩, dif_pos ht] at e
    exact ⟨_, by rw [← ids_getElem hq']; exact List.getElem_mem hq', ht, e⟩
  · rintro ⟨t, hti, ht, e⟩
    obtain ⟨q, hq, hqt⟩ := List.getElem_of_mem hti
    have hq' : q < ((len I).toUSize).toNat := by rw [hLn, len_eq_ids]; exact hq
    have ht' : (Column.bitsAt I (q * 8) 8).toNat < n.toNat := by rw [← ids_getElem hq, hqt]; exact ht
    refine ⟨⟨q, hq'⟩, ?_⟩
    rw [pick_row B x I _ _ hfit ⟨q, hq'⟩, dif_pos ht', ← e]
    exact congrArg x.row (Fin.ext ((ids_getElem hq).symm.trans hqt))

-- `leftDiv`'s vacuous side: the values of `Ub` coded as no value of `r`
set_option hygiene false in
local notation "vac" => Vals.pickPart B Ub (anti ubc rvc)

/-- **`leftDiv`'s vacuous part, read back**: `⊤` on the values of `Ub` that are no value of `r`, and `Uc`.
    Hypotheses: `ubc`, `rvc` code `Ub`, `r.val` jointly and well formed (`anti_ids`); `Ub` picks back at the kept
    positions; `rep_top`'s. -/
theorem div_vac_holds (r : Rel A B) {mb mc : USize} (Ub : Vals B mb) (Uc : Vals C mc) (ubc rvc : Code)
    (hxw : laneOK(ubc.w))
    (hyw : laneOK(rvc.w))
    (hxs : ubc.b.size = (ubc.n.toNat * ubc.w + 7) / 8) (hys : rvc.b.size = (rvc.n.toNat * rvc.w + 7) / 8)
    (hun : ubc.n = mb) (hrn : rvc.n = r.n)
    (hj : ∀ {j p : Nat} (hj : j < r.n.toNat) (hp : p < mb.toNat),
      Column.idAt rvc.b rvc.w j = Column.idAt ubc.b ubc.w p ↔ r.val.row ⟨j, hj⟩ = Ub.row ⟨p, hp⟩)
    (hP : Vals.PickFits B Ub (ids (anti ubc rvc)))
    (hN : (vac).1.toNat * mc.toNat < USize.size) (h63 : (vac).1.toNat * mc.toNat < 2 ^ 63)
    (hA : Vals.PickFits B (vac).2 ((List.range ((vac).1.toNat * mc.toNat)).map (· / mc.toNat)))
    (hB : Vals.PickFits C Uc ((List.range ((vac).1.toNat * mc.toNat)).map (· % mc.toNat))) (b : B.El) (c : C.El) :
    (top (vac).2 Uc).Holds b c ↔ ((∃ p, Ub.row p = b) ∧ ¬∃ a, r.Holds a b) ∧ ∃ j, Uc.row j = c := by
  have h := congrFun (congrFun (rep_top _ Uc hN h63 hA hB) b) c
  refine (Iff.of_eq h).trans ?_
  have hm := anti_ids ubc rvc hxw hyw hxs hys
  have hL : len (anti ubc rvc) < USize.size := by
    rw [len_eq_ids, hm.1]
    exact Nat.lt_of_le_of_lt (Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq (List.length_range ..)))
      ubc.n.toNat_lt_size
  have hlt : ∀ t ∈ ids (anti ubc rvc), t < mb.toNat := fun t ht => by rw [← hun]; exact ((hm.2.2 t).1 ht).1
  show (∃ a', (b = a' ∧ ∃ i, (vac).2.row i = b) ∧ ∃ b', True ∧ (b' = c ∧ ∃ j, Uc.row j = b')) ↔ _
  rw [pickPart_rows Ub _ hL hlt hP b]
  constructor
  · rintro ⟨_, ⟨rfl, t, hti, ht, e⟩, _, -, rfl, hc⟩
    obtain ⟨-, hno⟩ := (hm.2.2 t).1 hti
    refine ⟨⟨⟨⟨t, ht⟩, e⟩, ?_⟩, hc⟩
    rintro ⟨a, ⟨j, -, hjb⟩⟩
    exact hno ⟨j.1, by rw [hrn]; exact j.2, (hj j.2 ht).2 (hjb.trans e.symm)⟩
  · rintro ⟨⟨⟨⟨p, hp⟩, e⟩, hno⟩, hc⟩
    refine ⟨b, ⟨rfl, p, (hm.2.2 p).2 ⟨by rw [hun]; exact hp, ?_⟩, hp, e⟩, c, trivial, rfl, hc⟩
    rintro ⟨j, hjn, hje⟩
    rw [hrn] at hjn
    exact hno ⟨r.key.row ⟨j, hjn⟩, ⟨j, hjn⟩, rfl, ((hj hjn hp).1 hje).trans e⟩

/-- One part's code is faithful and well formed under `Obj.CodesFit` (`codes_faithful_wf` at the one part). -/
theorem one_ok {X : Obj} {n : USize} (x : Vals X n) (h : X.CodesFit (#v[⟨n, x⟩] : Vector (Part X) 1)) :
    oneOK(X, n, x) := by
  obtain ⟨⟨hF, hW⟩, -⟩ := codes_faithful_wf X _ h
  exact ⟨fun hi hj => hF (k := 0) (l := 0) (by decide) (by decide) hi hj, hW (k := 0) (by decide)⟩

/-- **`rep (R \ S)`**: `b` to `c` exactly when every `a` that `R` takes to `b` `S` takes to `c`, and either some
    `a` is taken to `b`, or `b` and `c` are elements of the universes `Ub`, `Uc`. `leftDiv`'s intermediate values
    are bound to variables by their defining equations (`hkc`, `hy`, `hycs`, `hzc`, `hI`, `hPe`, `hQe`).
    Hypotheses: `Obj.CodesFit` of every coded part; the counts fit; `Vals.PickFits` where a part is picked. -/
theorem rep_leftDiv {mb mc : USize} (R : Rel A B) (S : Rel A C) (Ub : Vals B mb) (Uc : Vals C mc)
    (hRK : A.CodesFit (#v[⟨R.n, R.key⟩] : Vector (Part A) 1)) (hRV : B.CodesFit (#v[⟨R.n, R.val⟩] : Vector (Part B) 1))
    (hRk : Vals.PickFits A R.key (ids nubI(A, B, R))) (hRv : Vals.PickFits B R.val (ids nubI(A, B, R)))
    (hSK : A.CodesFit (#v[⟨S.n, S.key⟩] : Vector (Part A) 1)) (hSV : C.CodesFit (#v[⟨S.n, S.val⟩] : Vector (Part C) 1))
    (hSk : Vals.PickFits A S.key (ids nubI(A, C, S))) (hSv : Vals.PickFits C S.val (ids nubI(A, C, S)))
    (kc : Vector Code 2)
    (hkc : kc = A.codes #v[⟨(Rel.nub R).n, (Rel.nub R).key⟩, ⟨(Rel.nub S).n, (Rel.nub S).key⟩])
    (hfk : A.CodesFit #v[⟨(Rel.nub R).n, (Rel.nub R).key⟩, ⟨(Rel.nub S).n, (Rel.nub S).key⟩])
    (hrn : (Rel.nub S).n.toNat < 2 ^ 63)
    (hM : ((List.range (kc[0]'Nat.zero_lt_two).n.toNat).map fun i => ((List.range (kc[1]'Nat.one_lt_two).n.toNat).filter
      fun j => Column.idAt (kc[1]'Nat.one_lt_two).b (kc[1]'Nat.one_lt_two).w j ==
        Column.idAt (kc[0]'Nat.zero_lt_two).b (kc[0]'Nat.zero_lt_two).w i).length).sum < 2 ^ 63)
    (hMU : ((List.range (kc[0]'Nat.zero_lt_two).n.toNat).map fun i => ((List.range (kc[1]'Nat.one_lt_two).n.toNat).filter
      fun j => Column.idAt (kc[1]'Nat.one_lt_two).b (kc[1]'Nat.one_lt_two).w j ==
        Column.idAt (kc[0]'Nat.zero_lt_two).b (kc[0]'Nat.zero_lt_two).w i).length).sum < USize.size)
    (hB : Vals.PickFits B (Rel.nub R).val ((jp(kc[0]'Nat.zero_lt_two, kc[1]'Nat.one_lt_two)).map Prod.fst))
    (hC : Vals.PickFits C (Rel.nub S).val ((jp(kc[0]'Nat.zero_lt_two, kc[1]'Nat.one_lt_two)).map Prod.snd))
    (y : Rel B C) (hy : y = yJ(B, C, Rel.nub R,Rel.nub S, kc[0]'Nat.zero_lt_two, kc[1]'Nat.one_lt_two))
    (ycs : Vector Code 3) (hycs : ycs = B.codes #v[⟨y.n, y.key⟩, ⟨(Rel.nub R).n, (Rel.nub R).val⟩, ⟨mb, Ub⟩])
    (hfy : B.CodesFit #v[⟨y.n, y.key⟩, ⟨(Rel.nub R).n, (Rel.nub R).val⟩, ⟨mb, Ub⟩])
    (zc : Vector Code 1) (hzc : zc = C.codes #v[⟨y.n, y.val⟩]) (hfz : C.CodesFit #v[⟨y.n, y.val⟩])
    (I : ByteArray)
    (hI : I = longCount "\\" (tuples.tupleIds (ycs[0]'(Nat.zero_lt_succ 2)) #[zc[0]'Nat.zero_lt_one]).2 fun g _ =>
      gather 8 (tuples.tupleIds (ycs[0]'(Nat.zero_lt_succ 2)) #[zc[0]'Nat.zero_lt_one]).2
        (whereEqV g (classSizes (ycs[0]'(Nat.zero_lt_succ 2)).n (tuples.tupleIds (ycs[0]'(Nat.zero_lt_succ 2)) #[zc[0]'Nat.zero_lt_one]))
          (atCnt (cnt (ycs[1]'(Nat.succ_lt_succ (Nat.zero_lt_succ 1))))
            ((ycs[0]'(Nat.zero_lt_succ 2)).gather (tuples.tupleIds (ycs[0]'(Nat.zero_lt_succ 2)) #[zc[0]'Nat.zero_lt_one]).2))))
    (hk : Vals.PickFits B y.key (ids I)) (hv : Vals.PickFits C y.val (ids I))
    (hP : Vals.PickFits B Ub (ids (anti (ycs[2]'(Nat.lt_add_one 2)) (ycs[1]'(Nat.succ_lt_succ (Nat.zero_lt_succ 1))))))
    (hN : (vacY(B, Ub, ycs)).1.toNat * mc.toNat < USize.size) (h63 : (vacY(B, Ub, ycs)).1.toNat * mc.toNat < 2 ^ 63)
    (hA : Vals.PickFits B (vacY(B, Ub, ycs)).2 ((List.range ((vacY(B, Ub, ycs)).1.toNat * mc.toNat)).map (· / mc.toNat)))
    (hBc : Vals.PickFits C Uc ((List.range ((vacY(B, Ub, ycs)).1.toNat * mc.toNat)).map (· % mc.toNat)))
    (P Q : Rel B C) (hPe : P = y.rows I) (hQe : Q = top (vacY(B, Ub, ycs)).2 Uc)
    (hU : P.n.toNat + Q.n.toNat < USize.size)
    (hNk : ((#[⟨P.n, P.key⟩, ⟨Q.n, Q.key⟩] : Array (Part B)).toList.map fun c : Part B => c.1.toNat).sum <
      USize.size)
    (hNv : ((#[⟨P.n, P.val⟩, ⟨Q.n, Q.val⟩] : Array (Part C)).toList.map fun c : Part C => c.1.toNat).sum <
      USize.size)
    (hFk : Vals.RazeFits B P.key Q.key) (hFv : Vals.RazeFits C P.val Q.val)
    (hUK : B.CodesFit (#v[⟨(PQ(B, C)).n, (PQ(B, C)).key⟩] : Vector (Part B) 1))
    (hUV : C.CodesFit (#v[⟨(PQ(B, C)).n, (PQ(B, C)).val⟩] : Vector (Part C) 1))
    (hUk : Vals.PickFits B (PQ(B, C)).key (ids nubI(B, C, PQ(B, C))))
    (hUv : Vals.PickFits C (PQ(B, C)).val (ids nubI(B, C, PQ(B, C)))) (b : B.El) (c : C.El) :
    rep (leftDiv R S Ub Uc) b c ↔
      (∀ a, rep R a b → rep S a c) ∧ ((∃ a, rep R a b) ∨ ((∃ p, Ub.row p = b) ∧ ∃ j, Uc.row j = c)) := by
  classical
  have e : leftDiv R S Ub Uc = P ∪ Q := by subst hPe hQe hI hzc hycs hy hkc; rfl
  rw [e, rep_union_full P Q hU hNk hNv hFk hFv (one_ok _ hUK) (one_ok _ hUV) hUk hUv]
  show P.Holds b c ∨ Q.Holds b c ↔ _
  subst hPe hQe
  -- the joint codes, faithful and well formed
  have hK' := codes_faithful_wf A _ hfk; rw [← hkc] at hK'
  obtain ⟨⟨kF, kW⟩, -⟩ := hK'
  have hY' := codes_faithful_wf B _ hfy; rw [← hycs] at hY'
  obtain ⟨⟨yF, yW⟩, -⟩ := hY'
  have hZ' := codes_faithful_wf C _ hfz; rw [← hzc] at hZ'
  obtain ⟨⟨zF, zW⟩, -⟩ := hZ'
  obtain ⟨hlw, hln, hls, -⟩ := kW (k := 0) (by decide)
  obtain ⟨hrw, hkn, hrs, hrc⟩ := kW (k := 1) (by decide)
  obtain ⟨y0w, y0n, y0s, y0c⟩ := yW (k := 0) (by decide)
  obtain ⟨y1w, y1n, y1s, y1c⟩ := yW (k := 1) (by decide)
  obtain ⟨y2w, y2n, y2s, -⟩ := yW (k := 2) (by decide)
  obtain ⟨z0w, z0n, z0s, z0c⟩ := zW (k := 0) (by decide)
  -- the counted part
  have hy' := div_y_holds (Rel.nub R) (Rel.nub S) (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two) hln hkn hlw hls hrw hrs
    hrc (by rw [hkn]; exact hrn) hM hMU hB hC
  rw [← hy] at hy'
  have hI' := leftDiv_keep (ycs[0]'(Nat.zero_lt_succ 2)) (zc[0]'Nat.zero_lt_one) (ycs[1]'(Nat.succ_lt_succ (Nat.zero_lt_succ 1))) (z0n.trans y0n.symm)
    ⟨y0w, y0s, fun h i hi => Nat.lt_of_lt_of_le ((y0c h).2 i hi) (Nat.le_max_left _ _)⟩
    ⟨z0w, z0s, fun h i hi => Nat.lt_of_lt_of_le ((z0c h).2 i hi) (Nat.le_max_left _ _)⟩ y1w y1s y1c
  rw [← hI] at hI'
  have hdk := div_keep_holds (Rel.nub R) (Rel.nub S) y (kc[0]'Nat.zero_lt_two) (kc[1]'Nat.one_lt_two)
    (ycs[0]'(Nat.zero_lt_succ 2)) (zc[0]'Nat.zero_lt_one) (ycs[1]'(Nat.succ_lt_succ (Nat.zero_lt_succ 1))) I hy' hln hkn
    (fun hi hj => eq_comm.trans (kF (k := 0) (l := 1) (by decide) (by decide) hi hj))
    (fun j j' h1 h2 => nub_rows_inj S (one_ok _ hSK) (one_ok _ hSV) hSk hSv h1 h2) y0n
    (fun hq hq' => yF (k := 0) (l := 0) (by decide) (by decide) hq hq')
    (fun hq hq' => zF (k := 0) (l := 0) (by decide) (by decide) hq hq') y1n
    (fun hj hq => yF (k := 1) (l := 0) (by decide) (by decide) hj hq) hI' hk hv b c
  -- the vacuous part
  have hdv := div_vac_holds (Rel.nub R) Ub Uc (ycs[2]'(Nat.lt_add_one 2)) (ycs[1]'(Nat.succ_lt_succ (Nat.zero_lt_succ 1))) y2w y1w y2s y1s y2n y1n
    (fun hj hp => yF (k := 1) (l := 2) (by decide) (by decide) hj hp) hP hN h63 hA hBc b c
  refine (or_congr hdk hdv).trans ?_
  have eR : ∀ a, (Rel.nub R).Holds a b ↔ rep R a b := fun a =>
    Iff.of_eq (congrFun (congrFun (rep_nub R (one_ok _ hRK) (one_ok _ hRV) hRk hRv) a) b)
  have eS : ∀ a, (Rel.nub S).Holds a c ↔ rep S a c := fun a =>
    Iff.of_eq (congrFun (congrFun (rep_nub S (one_ok _ hSK) (one_ok _ hSV) hSk hSv) a) c)
  simp only [eR, eS]
  constructor
  · rintro (⟨h, ha⟩ | ⟨⟨hb, hno⟩, hc⟩)
    · exact ⟨h, Or.inl ha⟩
    · exact ⟨fun a ha => absurd ⟨a, ha⟩ hno, Or.inr ⟨hb, hc⟩⟩
  · rintro ⟨h, ha | ⟨hb, hc⟩⟩
    · exact Or.inl ⟨h, ha⟩
    · by_cases hx : ∃ a, rep R a b
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr ⟨⟨hb, hx⟩, hc⟩

#print axioms rep_leftDiv

/-- **`rep (R / S)`**: `x` to `y` exactly when `R` takes `x` to every `c` that `S` takes `y` to, and either `S`
    takes `y` somewhere, or `x` and `y` are elements of the universes `Ua`, `Ub`. `rightDiv R S Ua Ub` is
    `(S° \ R°)°` on `Ub`, `Ua`, so this is `rep_leftDiv` there, its hypotheses at `S°`, `R°`, read through
    `rep_conv`. The objects are named as `leftDiv`'s there: `R : Rel C A`, `S : Rel B A`. -/
theorem rep_rightDiv {ma mb : USize} (R : Rel C A) (S : Rel B A) (Ua : Vals C ma) (Ub : Vals B mb)
    (hRK : A.CodesFit (#v[⟨(S°).n, (S°).key⟩] : Vector (Part A) 1))
    (hRV : B.CodesFit (#v[⟨(S°).n, (S°).val⟩] : Vector (Part B) 1))
    (hRk : Vals.PickFits A (S°).key (ids nubI(A, B, S°))) (hRv : Vals.PickFits B (S°).val (ids nubI(A, B, S°)))
    (hSK : A.CodesFit (#v[⟨(R°).n, (R°).key⟩] : Vector (Part A) 1))
    (hSV : C.CodesFit (#v[⟨(R°).n, (R°).val⟩] : Vector (Part C) 1))
    (hSk : Vals.PickFits A (R°).key (ids nubI(A, C, R°))) (hSv : Vals.PickFits C (R°).val (ids nubI(A, C, R°)))
    (kc : Vector Code 2)
    (hkc : kc = A.codes #v[⟨(Rel.nub (S°)).n, (Rel.nub (S°)).key⟩, ⟨(Rel.nub (R°)).n, (Rel.nub (R°)).key⟩])
    (hfk : A.CodesFit #v[⟨(Rel.nub (S°)).n, (Rel.nub (S°)).key⟩, ⟨(Rel.nub (R°)).n, (Rel.nub (R°)).key⟩])
    (hrn : (Rel.nub (R°)).n.toNat < 2 ^ 63)
    (hM : ((List.range (kc[0]'Nat.zero_lt_two).n.toNat).map fun i => ((List.range (kc[1]'Nat.one_lt_two).n.toNat).filter
      fun j => Column.idAt (kc[1]'Nat.one_lt_two).b (kc[1]'Nat.one_lt_two).w j ==
        Column.idAt (kc[0]'Nat.zero_lt_two).b (kc[0]'Nat.zero_lt_two).w i).length).sum < 2 ^ 63)
    (hMU : ((List.range (kc[0]'Nat.zero_lt_two).n.toNat).map fun i => ((List.range (kc[1]'Nat.one_lt_two).n.toNat).filter
      fun j => Column.idAt (kc[1]'Nat.one_lt_two).b (kc[1]'Nat.one_lt_two).w j ==
        Column.idAt (kc[0]'Nat.zero_lt_two).b (kc[0]'Nat.zero_lt_two).w i).length).sum < USize.size)
    (hB : Vals.PickFits B (Rel.nub (S°)).val ((jp(kc[0]'Nat.zero_lt_two, kc[1]'Nat.one_lt_two)).map Prod.fst))
    (hC : Vals.PickFits C (Rel.nub (R°)).val ((jp(kc[0]'Nat.zero_lt_two, kc[1]'Nat.one_lt_two)).map Prod.snd))
    (yd : Rel B C) (hy : yd = yJ(B, C, Rel.nub (S°),Rel.nub (R°), kc[0]'Nat.zero_lt_two, kc[1]'Nat.one_lt_two))
    (ycs : Vector Code 3)
    (hycs : ycs = B.codes #v[⟨yd.n, yd.key⟩, ⟨(Rel.nub (S°)).n, (Rel.nub (S°)).val⟩, ⟨mb, Ub⟩])
    (hfy : B.CodesFit #v[⟨yd.n, yd.key⟩, ⟨(Rel.nub (S°)).n, (Rel.nub (S°)).val⟩, ⟨mb, Ub⟩])
    (zc : Vector Code 1) (hzc : zc = C.codes #v[⟨yd.n, yd.val⟩]) (hfz : C.CodesFit #v[⟨yd.n, yd.val⟩])
    (I : ByteArray)
    (hI : I = longCount "\\" (tuples.tupleIds (ycs[0]'(Nat.zero_lt_succ 2)) #[zc[0]'Nat.zero_lt_one]).2 fun g _ =>
      gather 8 (tuples.tupleIds (ycs[0]'(Nat.zero_lt_succ 2)) #[zc[0]'Nat.zero_lt_one]).2
        (whereEqV g (classSizes (ycs[0]'(Nat.zero_lt_succ 2)).n (tuples.tupleIds (ycs[0]'(Nat.zero_lt_succ 2)) #[zc[0]'Nat.zero_lt_one]))
          (atCnt (cnt (ycs[1]'(Nat.succ_lt_succ (Nat.zero_lt_succ 1))))
            ((ycs[0]'(Nat.zero_lt_succ 2)).gather (tuples.tupleIds (ycs[0]'(Nat.zero_lt_succ 2)) #[zc[0]'Nat.zero_lt_one]).2))))
    (hk : Vals.PickFits B yd.key (ids I)) (hv : Vals.PickFits C yd.val (ids I))
    (hP : Vals.PickFits B Ub (ids (anti (ycs[2]'(Nat.lt_add_one 2)) (ycs[1]'(Nat.succ_lt_succ (Nat.zero_lt_succ 1))))))
    (hN : (vacY(B, Ub, ycs)).1.toNat * ma.toNat < USize.size) (h63 : (vacY(B, Ub, ycs)).1.toNat * ma.toNat < 2 ^ 63)
    (hA : Vals.PickFits B (vacY(B, Ub, ycs)).2 ((List.range ((vacY(B, Ub, ycs)).1.toNat * ma.toNat)).map (· / ma.toNat)))
    (hBc : Vals.PickFits C Ua ((List.range ((vacY(B, Ub, ycs)).1.toNat * ma.toNat)).map (· % ma.toNat)))
    (P Q : Rel B C) (hPe : P = yd.rows I) (hQe : Q = top (vacY(B, Ub, ycs)).2 Ua)
    (hU : P.n.toNat + Q.n.toNat < USize.size)
    (hNk : ((#[⟨P.n, P.key⟩, ⟨Q.n, Q.key⟩] : Array (Part B)).toList.map fun c : Part B => c.1.toNat).sum <
      USize.size)
    (hNv : ((#[⟨P.n, P.val⟩, ⟨Q.n, Q.val⟩] : Array (Part C)).toList.map fun c : Part C => c.1.toNat).sum <
      USize.size)
    (hFk : Vals.RazeFits B P.key Q.key) (hFv : Vals.RazeFits C P.val Q.val)
    (hUK : B.CodesFit (#v[⟨(PQ(B, C)).n, (PQ(B, C)).key⟩] : Vector (Part B) 1))
    (hUV : C.CodesFit (#v[⟨(PQ(B, C)).n, (PQ(B, C)).val⟩] : Vector (Part C) 1))
    (hUk : Vals.PickFits B (PQ(B, C)).key (ids nubI(B, C, PQ(B, C))))
    (hUv : Vals.PickFits C (PQ(B, C)).val (ids nubI(B, C, PQ(B, C)))) (x : C.El) (y : B.El) :
    rep (rightDiv R S Ua Ub) x y ↔
      (∀ c, rep S y c → rep R x c) ∧ ((∃ c, rep S y c) ∨ ((∃ p, Ua.row p = x) ∧ ∃ j, Ub.row j = y)) := by
  rw [show rightDiv R S Ua Ub = (leftDiv (S°) (R°) Ub Ua)° from rfl, rep_conv]
  show rep (leftDiv (S°) (R°) Ub Ua) y x ↔ _
  rw [rep_leftDiv (S°) (R°) Ub Ua hRK hRV hRk hRv hSK hSV hSk hSv kc hkc hfk hrn hM hMU hB hC yd hy ycs hycs hfy zc
    hzc hfz I hI hk hv hP hN h63 hA hBc P Q hPe hQe hU hNk hNv hFk hFv hUK hUV hUk hUv y x, rep_conv, rep_conv]
  exact and_congr Iff.rfl (or_congr Iff.rfl and_comm)

#print axioms rep_rightDiv

#print axioms div_y_rows
#print axioms div_y_holds
#print axioms div_keep_holds
#print axioms pickPart_rows
#print axioms div_vac_holds

end LeetQ.Rel.Rep
