/-
  The primitive array ops of `Alg` with no read-back elsewhere, read back: `nilVal`/`nil`, `atPos`, `unsnoc`.
-/
import LeetQ.Rel.RepList

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

/-- **`nilVal`, read back**: its one row is the empty array, its payload holding no cell. -/
theorem nilVal_row (B : Obj) (q : Fin (1 : USize).toNat) : Vals.row (nilVal B) q = [] := by
  rw [arr_row]
  show List.map _ (List.range (min _ (0 : USize).toNat - min _ (0 : USize).toNat)) = []
  simp

/-- **`nil`, read back**: an element of the one-row `I` goes to the empty array, and nothing else holds. -/
theorem rep_nil {K B : Obj} (I : Vals K 1) :
    ∀ u xs, rep (Alg.nil (B := B) I) u xs ↔ (∃ i, I.row i = u) ∧ xs = [] := by
  intro u xs
  rw [rep_apply]
  show (∃ i, _ ∧ _) ↔ _
  constructor
  · rintro ⟨i, hu, hx⟩; exact ⟨⟨i, hu⟩, hx.symm.trans (nilVal_row B i)⟩
  · rintro ⟨⟨i, hu⟩, rfl⟩; exact ⟨i, hu, nilVal_row B i⟩

/-- **`at(k)`, read back**: an array of `X` goes to `x` exactly when it is longer than `k` and `x` is its cell
    `k`. The rows longer than `k` (`i`) and the cells' payload places (`e`) are bound by their equations.
    Hypotheses: the payload count and `k` below `2^63` (`k.toUInt64` wraps past it), `Vals.PickFits` where `X`
    and its payload are picked. -/
theorem rep_atPos {B : Obj} {n : USize} (k : Nat) (X : Vals (.arr B) n) (hp : X.1.toNat < 2 ^ 63)
    (hk : k < 2 ^ 63)
    (i : ByteArray) (hi : i = whereBits n (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf X).2 (one k.toUInt64) n))
    (e : ByteArray) (he : e = addc (len i).toUSize (gather 8 (slicesOf X).1 i) k)
    (hKf : Vals.PickFits (.arr B) X ((List.range (len i)).map fun q => (Column.bitsAt i (q * 8) 8).toNat))
    (hEf : Vals.PickFits B X.2.2.2 ((List.range (len i)).map fun q => (Column.bitsAt e (q * 8) 8).toNat)) :
    ∀ (xs : List B.El) x, rep (atPos k X) xs x ↔ (∃ j, X.row j = xs) ∧ ∃ h : k < xs.length, x = xs[k]'h := by
  intro xs x
  have hlen : len i < USize.size := by
    rw [hi]; exact Nat.lt_of_le_of_lt (len_whereBits_le _ _) n.toNat_lt_size
  have hm : ((len i).toUSize).toNat = len i := USize.toNat_ofNat_of_lt' hlen
  have hR := fun j (hj : j < n.toNat) => slicesOf_row X hp hj
  have hA := whereGt_ids n (slicesOf X).2 hk fun j hj => by have := (hR j hj).1; omega
  rw [← hi] at hA
  have hmem : ∀ j, j ∈ QLean.Verify.ids i ↔
      j < n.toNat ∧ k < (Column.bitsAt (slicesOf X).2 (j * 8) 8).toNat := fun j => by
    rw [hA, List.mem_filter, List.mem_range, decide_eq_true_iff]
  have hs1 : len (slicesOf X).1 = n.toNat := (len_slices _ _ _ _).1
  have hk64 : (k.toUInt64).toNat = k := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hk (by decide))
  -- row `q` of the result: the array `X.row i[q]` and its cell `k`
  have hq : ∀ (q : Nat) (hq : q < len i) (h1 : len i = ((len i).toUSize).toNat)
      (h2 : len e = ((len i).toUSize).toNat),
      ∃ hj : (Column.bitsAt i (q * 8) 8).toNat < n.toNat,
        Vals.row (Vals.pick (.arr B) X i _ h1) ⟨q, by omega⟩ = X.row ⟨_, hj⟩ ∧
        ∃ hk' : k < (X.row ⟨_, hj⟩).length,
          Vals.row (Vals.pick B X.2.2.2 e _ h2) ⟨q, by omega⟩ = (X.row ⟨_, hj⟩)[k]'hk' := by
    intro q hq h1 h2
    have qb : q < ((len i).toUSize).toNat := by omega
    have hin : (Column.bitsAt i (q * 8) 8).toNat ∈ QLean.Verify.ids i := by
      have hq' : q < (QLean.Verify.ids i).length := by rw [← len_eq_ids]; exact hq
      rw [← ids_getElem hq']; exact List.getElem_mem hq'
    obtain ⟨hj, hc⟩ := (hmem _).1 hin
    obtain ⟨hLC, hln, hget⟩ := hR _ hj
    have hlq : Column.bitsAt (gather 8 (slicesOf X).1 i) (q * 8) 8 =
        Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8 :=
      gather8_get hq (by rw [hs1]; exact hj)
    have heq : (Column.bitsAt e (q * 8) 8).toNat =
        (Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat + k := by
      rw [he]; unfold addc
      rw [val_va_get _ _ _ _ qb, bitsAt_one, hlq, (valStep_add_sub (by omega) (by omega)).1 (by omega), hk64]
      exact UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (show _ < 2 ^ 63 by omega) (by decide))
    have hkl : k < (X.row ⟨_, hj⟩).length := by rw [hln]; exact hc
    refine ⟨hj, by rw [pick_row (.arr B) X i _ h1 (by rw [← h1]; exact hKf), dif_pos hj], hkl, ?_⟩
    have hlt : (Column.bitsAt e (q * 8) 8).toNat < X.1.toNat := by rw [heq]; omega
    rw [pick_row B X.2.2.2 e _ h2 (by rw [← h1]; exact hEf), dif_pos hlt, hget k hkl (by omega)]
    exact congrArg (Vals.row X.2.2.2) (Fin.ext heq)
  subst hi he
  unfold atPos
  dsimp only
  rw [longCount_eq _ _ _ hlen]
  show (∃ q, _ ∧ _) ↔ _
  constructor
  · rintro ⟨⟨q, hq'⟩, hr, hv⟩
    obtain ⟨hj, hK, hk', hV⟩ := hq q (Nat.lt_of_lt_of_eq hq' hm) hm.symm (len_val ..)
    refine ⟨⟨_, hK.symm.trans hr⟩, ?_⟩
    rw [hK] at hr
    subst hr
    exact ⟨hk', hv.symm.trans hV⟩
  · rintro ⟨⟨⟨j, hj⟩, hx⟩, hk', rfl⟩
    have hc : k < (Column.bitsAt (slicesOf X).2 (j * 8) 8).toNat := by
      rw [← (hR j hj).2.1, hx]; exact hk'
    obtain ⟨q, hq', hqe⟩ := List.getElem_of_mem ((hmem j).2 ⟨hj, hc⟩)
    rw [ids_getElem hq'] at hqe
    have hq'' := Nat.lt_of_lt_of_eq hq' (len_eq_ids _).symm
    obtain ⟨hj', hK, hk2, hV⟩ := hq q hq'' hm.symm (len_val ..)
    subst hqe
    refine ⟨⟨q, Nat.lt_of_lt_of_eq hq'' hm.symm⟩, hK.trans hx, ?_⟩
    rw [hV]
    subst hx
    rfl

/-- **`snoc°`, read back**: an array of `X` goes to `(bs, b)` exactly when it is `bs ++ [b]`. The non-empty
    rows (`i`), their starts (`l`) and their last cells' payload places (`e`) are bound by their equations.
    Hypotheses: the payload count below `2^63`, `Vals.PickFits` where `X`, its payload and the fronts (`[l, e)`,
    before `Vals.compact`, at whatever count proofs) are picked. -/
theorem rep_unsnoc {B : Obj} {n : USize} (X : Vals (.arr B) n) (hp : X.1.toNat < 2 ^ 63)
    (i : ByteArray) (hi : i = whereBits n (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf X).2 (one 0) n))
    (l : ByteArray) (hl : l = gather 8 (slicesOf X).1 i)
    (e : ByteArray) (he : e = Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul
      (add (len i).toUSize l (gather 8 (slicesOf X).2 i)) (one 1) (len i).toUSize)
    (hKf : Vals.PickFits (.arr B) X ((List.range (len i)).map fun q => (Column.bitsAt i (q * 8) 8).toNat))
    (hEf : Vals.PickFits B X.2.2.2 ((List.range (len i)).map fun q => (Column.bitsAt e (q * 8) 8).toNat))
    (hTf : ∀ (h₁ : ((len i).toUSize).toNat ≤ len l) (h₂ : ((len i).toUSize).toNat ≤ len e),
      Vals.PickFits (.arr B)
        (⟨X.1, longsN (len i).toUSize l h₁, longsN (len i).toUSize e h₂, X.2.2.2⟩ : Vals (.arr B) (len i).toUSize)
        ((List.range (len i)).map fun q => (Column.bitsAt (tilLongs (len i).toUSize) (q * 8) 8).toNat)) :
    ∀ (xs : List B.El) bs b, rep (unsnoc X) xs (bs, b) ↔ (∃ j, X.row j = xs) ∧ xs = bs ++ [b] := by
  intro xs bs b
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
  have h1n : (1 : UInt64).toNat = 1 := rfl
  have hcT : ∀ T : Vals (.arr B) (len i).toUSize,
      Vals.compact (.arr B) T = Vals.pick (.arr B) T (tilLongs _) _ (len_tilLongs _) := fun _ => rfl
  -- row `q` of the result: the array `X.row i[q]`, its front and its last cell
  have hq : ∀ (q : Nat) (hq : q < len i) (h1 : len i = ((len i).toUSize).toNat)
      (h2 : len e = ((len i).toUSize).toNat) (h₁ : ((len i).toUSize).toNat ≤ len l)
      (h₂ : ((len i).toUSize).toNat ≤ len e) (T : Vals (.arr B) (len i).toUSize)
      (hT : T = ⟨X.1, longsN (len i).toUSize l h₁, longsN (len i).toUSize e h₂, X.2.2.2⟩),
      ∃ hj : (Column.bitsAt i (q * 8) 8).toNat < n.toNat,
        Vals.row (Vals.pick (.arr B) X i _ h1) ⟨q, by omega⟩ = X.row ⟨_, hj⟩ ∧
        X.row ⟨_, hj⟩ = Vals.row (Vals.compact (.arr B) T) ⟨q, by omega⟩ ++
          [Vals.row (Vals.pick B X.2.2.2 e _ h2) ⟨q, by omega⟩] := by
    intro q hq h1 h2 h₁ h₂ T hT
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
    have ha : (Column.bitsAt (add (len i).toUSize l (gather 8 (slicesOf X).2 i)) (q * 8) 8).toNat =
        (Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat +
          (Column.bitsAt (slicesOf X).2 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat := by
      rw [add_get qb (by rw [hlq, hcq]; omega), hlq, hcq]
    have heq : (Column.bitsAt e (q * 8) 8).toNat =
        (Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat +
          (Column.bitsAt (slicesOf X).2 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat - 1 := by
      rw [he, val_va_get _ _ _ _ qb, bitsAt_one, (valStep_add_sub (by omega) (by omega)).2 (by omega),
        UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
          (Nat.lt_trans (show _ < 2 ^ 63 by omega) (by decide))), ha, h1n]
    have hlt : (Column.bitsAt e (q * 8) 8).toNat < X.1.toNat := by rw [heq]; omega
    refine ⟨hj, by rw [pick_row (.arr B) X i _ h1 (by rw [← h1]; exact hKf), dif_pos hj], ?_⟩
    have eT : ∀ (a : Nat) (ha : a < ((len i).toUSize).toNat), a = q → T.row ⟨a, ha⟩ = T.row ⟨q, qb⟩ := by
      intro a ha e; subst e; rfl
    rw [pick_row B X.2.2.2 e _ h2 (by rw [← h1]; exact hEf), dif_pos hlt, hcT,
      pick_row (.arr B) T (tilLongs _) _ (len_tilLongs _) (by rw [← h1, hT]; exact hTf h₁ h₂),
      dif_pos (show (Column.bitsAt (tilLongs (len i).toUSize) (q * 8) 8).toNat < ((len i).toUSize).toNat by
        rw [tilLongs_get qb]; exact qb),
      eT _ _ (tilLongs_get qb)]
    subst hT
    have hlo : ((longsN (len i).toUSize l h₁).get ⟨q, qb⟩).toInt =
        ((Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat : Int) := by
      rw [longsN_get, hlq]; exact toInt64_toInt (by omega)
    have hhi : ((longsN (len i).toUSize e h₂).get ⟨q, qb⟩).toInt =
        (((Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat +
          (Column.bitsAt (slicesOf X).2 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat - 1 : Nat) : Int) := by
      rw [longsN_get, toInt64_toInt (x := Column.bitsAt e (q * 8) 8) (by omega), heq]
    have hrow := arr_row (b := B) (⟨X.1, longsN (len i).toUSize l h₁, longsN (len i).toUSize e h₂, X.2.2.2⟩ :
      Vals (.arr B) (len i).toUSize) ⟨q, qb⟩
    dsimp only at hrow
    rw [hlo, hhi] at hrow
    generalize hL : (Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat = L
      at hrow heq hLC hget
    generalize hC : (Column.bitsAt (slicesOf X).2 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat = C
      at hrow heq hLC hln hc
    have e1 : min (max ((L : Nat) : Int) 0).toNat X.1.toNat = L := by omega
    have e2 : min (max ((L + C - 1 : Nat) : Int) 0).toNat X.1.toNat = L + C - 1 := by omega
    rw [e1, e2] at hrow
    rw [hrow]
    apply List.ext_getElem
    · rw [hln, List.length_append, List.length_map, List.length_range, List.length_singleton]; omega
    · intro t h1' h2'
      rw [hget t h1' (by omega), List.getElem_append]
      split
      · rw [List.getElem_map, List.getElem_range, dif_pos (show L + t < X.1.toNat by omega)]
      · rename_i hn
        rw [List.length_map, List.length_range] at hn
        rw [List.getElem_singleton]
        exact congrArg (Vals.row X.2.2.2) (Fin.ext (show L + t = (Column.bitsAt e (q * 8) 8).toNat by omega))
  have h₁ : ((len i).toUSize).toNat ≤ len l := Nat.le_of_eq (hm.trans (by rw [hl, gather_len]))
  have h₂ : ((len i).toUSize).toNat ≤ len e := Nat.le_of_eq (by rw [he, len_val])
  subst hi hl he
  unfold unsnoc
  dsimp only
  rw [longCount_eq _ _ _ hlen]
  show (∃ q, _ ∧ _) ↔ _
  constructor
  · rintro ⟨⟨q, hq'⟩, hr, hv⟩
    obtain ⟨hj, hK, hV⟩ := hq q (Nat.lt_of_lt_of_eq hq' hm) hm.symm (len_val ..) h₁ h₂ _ rfl
    refine ⟨⟨_, hK.symm.trans hr⟩, ?_⟩
    rw [← hr, hK, hV]
    exact congrArg (fun p => p.1 ++ [p.2]) hv
  · rintro ⟨⟨⟨j, hj⟩, hx⟩, hxs⟩
    have hc : 0 < (Column.bitsAt (slicesOf X).2 (j * 8) 8).toNat := by
      rw [← (hR j hj).2.1, hx, hxs, List.length_append, List.length_singleton]; omega
    obtain ⟨q, hq', hqe⟩ := List.getElem_of_mem ((hmem j).2 ⟨hj, hc⟩)
    rw [ids_getElem hq'] at hqe
    have hq'' := Nat.lt_of_lt_of_eq hq' (len_eq_ids _).symm
    obtain ⟨hj', hK, hV⟩ := hq q hq'' hm.symm (len_val ..) h₁ h₂ _ rfl
    subst hqe
    refine ⟨⟨q, Nat.lt_of_lt_of_eq hq'' hm.symm⟩, hK.trans hx, ?_⟩
    obtain ⟨e1, e2⟩ := List.append_inj' (hV.symm.trans (hx.trans hxs)) rfl
    exact Prod.ext e1 (List.singleton_inj.1 e2)

#print axioms nilVal_row
#print axioms rep_nil
#print axioms rep_atPos
#print axioms rep_unsnoc

end LeetQ.Rel.Rep
