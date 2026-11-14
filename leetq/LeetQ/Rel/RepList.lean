/-
  The array ops of `Alg` read back: `cons°` (`uncons`), `cons`, and the folds over arrays built from them.
-/
import LeetQ.Rel.RepFold

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

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.Rep.rep_uncons
