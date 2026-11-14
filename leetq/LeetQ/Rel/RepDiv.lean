/-
  The divisions of `Rel`, read back. `leftDiv R S Ub Uc` joins `R.nub` and `S.nub` on the shared key into rows
  `(y, z)` (the `y` part, as `≫` joins), keeps the first row of each pair whose count equals the count of `y`
  among `R.nub`'s values (`leftDiv_keep`), and adds `⊤` on the values of `Ub` that are no value of `R` and `Uc`.
-/
import LeetQ.Rel.RepOps
import LeetQ.Rel.KernelWF.DivSpec
import LeetQ.Rel.KernelWF.CountSpec

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg

variable {A B C : Obj}

-- the pairs `(i, j)` `join l r` answers, as `join_rows` lists them: row `i` of `l`, row `j` of `r`, equal codes
set_option quotPrecheck false in
local notation "jp(" l ", " r ")" => ((List.range (Code.n l).toNat).flatMap fun i =>
  ((List.range (Code.n r).toNat).filter fun j =>
    Column.idAt (Code.b r) (Code.w r) j == Column.idAt (Code.b l) (Code.w l) i).map (i, ·))

/-- **`leftDiv`'s joined rows, read back**: one row per pair `(i, j)` of `join l r`, in its order, `x`'s row `i`
    beside `z`'s row `j`. Stated over any two codes, not `leftDiv`'s, so the statement holds no `Obj.codes`.
    Hypotheses: `join_rows`', and each side picks back at its rows of the pairs. -/
theorem div_y_rows {n₁ n₂ : USize} (l r : Code) (x : Vals B n₁) (z : Vals C n₂) (hln : l.n = n₁) (hrn' : r.n = n₂)
    (hlw : l.w = 1 ∨ l.w = 2 ∨ l.w = 4 ∨ l.w = 8 ∨ l.w = 16 ∨ l.w = 32 ∨ l.w = 64)
    (hls : l.b.size = (l.n.toNat * l.w + 7) / 8)
    (hrw : r.w = 1 ∨ r.w = 2 ∨ r.w = 4 ∨ r.w = 8 ∨ r.w = 16 ∨ r.w = 32 ∨ r.w = 64)
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

-- a pair of code columns read as one key per row, the key `tupleIds` groups by (as `DivSpec`'s)
local notation "key2(" a ", " b ")" => fun i => (Column.idAt (Code.b a) (Code.w a) i, Column.idAt (Code.b b) (Code.w b) i)

set_option maxHeartbeats 800000 in
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

#print axioms div_y_rows
#print axioms div_keep_holds

end LeetQ.Rel.Rep
