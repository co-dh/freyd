/-
  The primitive array ops of `Alg` with no read-back elsewhere, read back: `nilVal`/`nil`, `atPos`, `unsnoc`.
-/
import LeetQ.Rel.RepList
import LeetQ.Rel.KernelWF.PrimSpec
import LeetQ.Rel.KernelWF.SliceSpec
import LeetQ.Rel.KernelWF.MemberSpec

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
    (hX : Vals.PickFits (.arr B) X (List.range n.toNat)) :
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
  -- picked row `q`: a row of `X` longer than `k`, and the payload place of its cell `k`
  have hE : ∀ q, q < len i → ∃ hj : (Column.bitsAt i (q * 8) 8).toNat < n.toNat,
      k < (Column.bitsAt (slicesOf X).2 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat ∧
      (Column.bitsAt e (q * 8) 8).toNat =
        (Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat + k := by
    intro q hq
    have qb : q < ((len i).toUSize).toNat := by omega
    have hin : (Column.bitsAt i (q * 8) 8).toNat ∈ QLean.Verify.ids i := by
      have hq' : q < (QLean.Verify.ids i).length := by rw [← len_eq_ids]; exact hq
      rw [← ids_getElem hq']; exact List.getElem_mem hq'
    obtain ⟨hj, hc⟩ := (hmem _).1 hin
    obtain ⟨hLC, -, -⟩ := hR _ hj
    have hlq : Column.bitsAt (gather 8 (slicesOf X).1 i) (q * 8) 8 =
        Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8 :=
      gather8_get hq (by rw [hs1]; exact hj)
    refine ⟨hj, hc, ?_⟩
    rw [he]; unfold addc
    rw [val_va_get _ _ _ _ qb, bitsAt_one, hlq, (valStep_add_sub (by omega) (by omega)).1 (by omega), hk64]
    exact UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (show _ < 2 ^ 63 by omega) (by decide))
  -- the picks are rows of `X` (`whereBits`), and the cells one place inside each picked row's window
  have hKf : Vals.PickFits (.arr B) X (QLean.Verify.ids i) :=
    pickFits_sublist (by rw [hi]; exact whereBits_sublist n _) hX
  have hEf : Vals.PickFits B X.2.2.2 ((List.range (len i)).map fun q => (Column.bitsAt e (q * 8) 8).toNat) := by
    refine pickFits_sublist ?_ (pickFits_payload X hKf).2
    rw [List.map_eq_flatMap]
    refine flatMap_sublist_map_flatMap (fun q => (Column.bitsAt i (q * 8) 8).toNat) _ _ fun q hq => ?_
    obtain ⟨hj, hc, heq⟩ := hE q (List.mem_range.1 hq)
    have hS := slicesOf_get X hp hj
    dsimp only
    rw [dif_pos hj, List.singleton_sublist, List.mem_range'_1]
    omega
  -- row `q` of the result: the array `X.row i[q]` and its cell `k`
  have hq : ∀ (q : Nat) (hq : q < len i) (h1 : len i = ((len i).toUSize).toNat)
      (h2 : len e = ((len i).toUSize).toNat),
      ∃ hj : (Column.bitsAt i (q * 8) 8).toNat < n.toNat,
        Vals.row (Vals.pick (.arr B) X i _ h1) ⟨q, by omega⟩ = X.row ⟨_, hj⟩ ∧
        ∃ hk' : k < (X.row ⟨_, hj⟩).length,
          Vals.row (Vals.pick B X.2.2.2 e _ h2) ⟨q, by omega⟩ = (X.row ⟨_, hj⟩)[k]'hk' := by
    intro q hq h1 h2
    obtain ⟨hj, hc, heq⟩ := hE q hq
    obtain ⟨hLC, hln, hget⟩ := hR _ hj
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
    (hX : Vals.PickFits (.arr B) X (List.range n.toNat)) :
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
  -- picked row `q`: a non-empty row of `X`, its start and the payload place of its last cell
  have hE : ∀ q, q < len i → ∃ hj : (Column.bitsAt i (q * 8) 8).toNat < n.toNat,
      0 < (Column.bitsAt (slicesOf X).2 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat ∧
      Column.bitsAt l (q * 8) 8 = Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8 ∧
      (Column.bitsAt e (q * 8) 8).toNat =
        (Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat +
          (Column.bitsAt (slicesOf X).2 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat - 1 := by
    intro q hq
    have qb : q < ((len i).toUSize).toNat := by omega
    have hin : (Column.bitsAt i (q * 8) 8).toNat ∈ QLean.Verify.ids i := by
      have hq' : q < (QLean.Verify.ids i).length := by rw [← len_eq_ids]; exact hq
      rw [← ids_getElem hq']; exact List.getElem_mem hq'
    obtain ⟨hj, hc⟩ := (hmem _).1 hin
    obtain ⟨hLC, -, -⟩ := hR _ hj
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
    refine ⟨hj, hc, hlq, ?_⟩
    rw [he, val_va_get _ _ _ _ qb, bitsAt_one, (valStep_add_sub (by omega) (by omega)).2 (by omega),
      UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
        (Nat.lt_trans (show _ < 2 ^ 63 by omega) (by decide))), ha, h1n]
  -- the picks are rows of `X` (`whereBits`); each last cell, and each front's window, inside its row's window
  have hKf : Vals.PickFits (.arr B) X (QLean.Verify.ids i) :=
    pickFits_sublist (by rw [hi]; exact whereBits_sublist n _) hX
  have hEf : Vals.PickFits B X.2.2.2 ((List.range (len i)).map fun q => (Column.bitsAt e (q * 8) 8).toNat) := by
    refine pickFits_sublist ?_ (pickFits_payload X hKf).2
    rw [List.map_eq_flatMap]
    refine flatMap_sublist_map_flatMap (fun q => (Column.bitsAt i (q * 8) 8).toNat) _ _ fun q hq => ?_
    obtain ⟨hj, hc, -, heq⟩ := hE q (List.mem_range.1 hq)
    have hS := slicesOf_get X hp hj
    dsimp only
    rw [dif_pos hj, List.singleton_sublist, List.mem_range'_1]
    omega
  have hTf : ∀ (h₁ : ((len i).toUSize).toNat ≤ len l) (h₂ : ((len i).toUSize).toNat ≤ len e),
      Vals.PickFits (.arr B)
        (⟨X.1, longsN (len i).toUSize l h₁, longsN (len i).toUSize e h₂, X.2.2.2⟩ : Vals (.arr B) (len i).toUSize)
        ((List.range (len i)).map fun q => (Column.bitsAt (tilLongs (len i).toUSize) (q * 8) 8).toNat) := by
    intro h₁ h₂
    refine pickFits_windows X _ _ ?_ hKf
    rw [List.map_congr_left (g := fun q => q) fun q hq => tilLongs_get (by rw [hm]; exact List.mem_range.1 hq),
      List.map_id']
    refine flatMap_sublist_map_flatMap (fun q => (Column.bitsAt i (q * 8) 8).toNat) _ _ fun q hq => ?_
    have hq' := List.mem_range.1 hq
    have qb : q < ((len i).toUSize).toNat := by omega
    obtain ⟨hj, hc, hlq, heq⟩ := hE q hq'
    obtain ⟨hLC, -, -⟩ := hR _ hj
    have hS := slicesOf_get X hp hj
    have hlo : ((longsN (len i).toUSize l h₁).get ⟨q, qb⟩).toInt =
        ((Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat : Int) := by
      rw [longsN_get, hlq]; exact toInt64_toInt (by omega)
    have hhi : ((longsN (len i).toUSize e h₂).get ⟨q, qb⟩).toInt =
        (((Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat +
          (Column.bitsAt (slicesOf X).2 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat - 1 : Nat) : Int) := by
      rw [longsN_get, toInt64_toInt (x := Column.bitsAt e (q * 8) 8) (by omega), heq]
    dsimp only
    rw [dif_pos qb, dif_pos hj, hlo, hhi]
    generalize (Column.bitsAt (slicesOf X).1 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat = L at hS hLC ⊢
    generalize (Column.bitsAt (slicesOf X).2 ((Column.bitsAt i (q * 8) 8).toNat * 8) 8).toNat = C at hS hLC hc ⊢
    have e1 : min (max ((L : Nat) : Int) 0).toNat X.1.toNat = L := by omega
    have e2 : min (max ((L + C - 1 : Nat) : Int) 0).toNat X.1.toNat = L + C - 1 := by omega
    rw [e1, e2, ← hS.1]
    exact List.range'_sublist_right.2 (by omega)
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
    obtain ⟨hj, hc, hlq, heq⟩ := hE q hq
    obtain ⟨hLC, hln, hget⟩ := hR _ hj
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

/-- **`zip`, read back**: a row `(xs, ys)` of `P` goes to `zip xs ys`, under its key, the pairs up to the
    shorter. The pieces `zip` computes are bound by their equations: the lesser counts `c`, `expand`'s index and
    rank columns `xi`, `xr` (at `m` copies), and the two sides' payload rows `ja`, `jb`.
    Hypotheses: `Vals.PickFits` of both sides at every row; the lesser counts summed below `2^63` and a
    `USize`; `Vals.PickFits` where the key is picked. -/
theorem rep_zip {K A B : Obj} (P : Rel K (.prod (.arr A) (.arr B)))
    (hPa : Vals.PickFits (.arr A) (Rel.val P).1 (List.range (Rel.n P).toNat))
    (hPb : Vals.PickFits (.arr B) (Rel.val P).2 (List.range (Rel.n P).toNat))
    (c : ByteArray) (hc : c = Kernel.Ew.val Ew.lesser Ew.i64 Ew.vv nul (slicesOf (Rel.val P).1).2
      (slicesOf (Rel.val P).2).2 (Rel.n P))
    (hS : ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt c (r * 8) 8).toNat).sum < 2 ^ 63)
    (hU : ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt c (r * 8) 8).toNat).sum < USize.size)
    (xi : ByteArray) (hxi : xi = expandBytes 8 0 (tilLongs (Rel.n P)) c)
    (m : USize) (hm : m = (len xi).toUSize)
    (xr : ByteArray) (hxr : xr = sub m (tilLongs m) (gather 8 (sub (Rel.n P) (sums (Rel.n P) c) c) xi))
    (ja : ByteArray) (hja : ja = add m (gather 8 (slicesOf (Rel.val P).1).1 xi) xr)
    (jb : ByteArray) (hjb : jb = add m (gather 8 (slicesOf (Rel.val P).2).1 xi) xr)
    (hKf : Vals.PickFits K (Rel.key P)
      ((List.range (Rel.n P).toNat).map fun q => (Column.bitsAt (tilLongs (Rel.n P)) (q * 8) 8).toNat)) :
    ∀ k zs, rep (zip P) k zs ↔ ∃ xs ys, rep P k (xs, ys) ∧ zs = List.zip xs ys := by
  intro k zs
  have hpa := (pickFits_payload _ hPa).1
  have hpb := (pickFits_payload _ hPb).1
  have hcl : len c = (Rel.n P).toNat := by rw [hc, len_val]
  obtain ⟨pre, hpre⟩ : ∃ f : Nat → Nat, ∀ r,
      f r = ((List.range r).map fun u => (Column.bitsAt c (u * 8) 8).toNat).sum := ⟨_, fun _ => rfl⟩
  have hpre_le : ∀ a b, a ≤ b → pre a ≤ pre b := fun a b h => by rw [hpre, hpre]; exact sum_range_le _ h
  have hpre_succ : ∀ r, pre (r + 1) = pre r + (Column.bitsAt c (r * 8) 8).toNat := fun r => by
    rw [hpre, hpre]; exact sum_range_succ' _ r
  have hpN : pre (Rel.n P).toNat < 2 ^ 63 := by rw [hpre]; exact hS
  have hsa : len (slicesOf (Rel.val P).1).1 = (Rel.n P).toNat := (len_slices _ _ _ _).1
  have hsb : len (slicesOf (Rel.val P).2).1 = (Rel.n P).toNat := (len_slices _ _ _ _).1
  have hRa := fun r (hr : r < (Rel.n P).toNat) => slicesOf_row (Rel.val P).1 hpa hr
  have hRb := fun r (hr : r < (Rel.n P).toNat) => slicesOf_row (Rel.val P).2 hpb hr
  have hcg : ∀ r, r < (Rel.n P).toNat → (Column.bitsAt c (r * 8) 8).toNat =
      min (Column.bitsAt (slicesOf (Rel.val P).1).2 (r * 8) 8).toNat
        (Column.bitsAt (slicesOf (Rel.val P).2).2 (r * 8) 8).toNat := fun r hr => by
    have := (hRa r hr).1; have := (hRb r hr).1
    rw [hc]; exact lesser_get hr (by omega) (by omega)
  -- the running ends and starts: row `r`'s new array is `[pre r, pre (r + 1))`
  have hhig : ∀ r, r < (Rel.n P).toNat →
      (Column.bitsAt (sums (Rel.n P) c) (r * 8) 8).toNat = pre (r + 1) := fun r hr => by
    have hb := hpre_le (r + 1) _ hr
    rw [sums_get (b := c) hr (by rw [hcl]; exact hr) (by rw [← hpre]; omega), ← hpre]
  have hlog : ∀ r, r < (Rel.n P).toNat →
      (Column.bitsAt (sub (Rel.n P) (sums (Rel.n P) c) c) (r * 8) 8).toNat = pre r := fun r hr => by
    have := hhig r hr; have := hpre_succ r; have := hpre_le (r + 1) _ hr
    rw [sub_get (a := sums (Rel.n P) c) (b := c) hr (by omega) (by omega)]; omega
  -- `expand`: copy `d` is cell `d - pre r` of row `r = xi[d]`
  have hI := expand_idx (n := Rel.n P) (cnt := c) (by omega) (fun t ht => by
    have := hpre_le (t + 1) (Rel.n P).toNat (by omega); rw [hpre_succ] at this; omega)
  rw [← hxi, hcl] at hI
  have hxl : len xi = pre (Rel.n P).toNat := by
    rw [len_eq_ids, hI, List.length_flatMap, hpre]; simp only [List.length_replicate]
  have hxU : len xi < USize.size := by rw [hxl, hpre]; exact hU
  have hmN : m.toNat = len xi := by rw [hm]; exact USize.toNat_ofNat_of_lt' hxU
  have hxi_at : ∀ d, d < len xi → ∃ r, r < (Rel.n P).toNat ∧ (Column.bitsAt xi (d * 8) 8).toNat = r ∧
      pre r ≤ d ∧ d < pre r + (Column.bitsAt c (r * 8) 8).toNat := by
    intro d hd
    obtain ⟨t, ht, h1, h2, h3⟩ := flatMap_get (fun t => List.replicate (Column.bitsAt c (t * 8) 8).toNat t)
      (Rel.n P).toNat d (by simp only [List.length_replicate]; rw [← hpre, ← hxl]; exact hd)
    simp only [List.length_replicate] at h1 h2 h3
    rw [List.getElem?_replicate, if_pos (by omega)] at h3
    have hpl : d < ((List.range (Rel.n P).toNat).flatMap fun t =>
        List.replicate (Column.bitsAt c (t * 8) 8).toNat t).length := by
      rw [← hI, ← len_eq_ids]; exact hd
    refine ⟨t, ht, ?_, by rw [hpre]; exact h1, by rw [hpre]; exact h2⟩
    rw [ids_get hI hpl]; rw [List.getElem?_eq_getElem hpl] at h3; exact Option.some.inj h3
  have hxi_in : ∀ r t, r < (Rel.n P).toNat → t < (Column.bitsAt c (r * 8) 8).toNat →
      (Column.bitsAt xi ((pre r + t) * 8) 8).toNat = r := by
    intro r t hr ht
    have h := flatMap_get_at (fun t => List.replicate (Column.bitsAt c (t * 8) 8).toNat t) hr (q := t)
      (by simp only [List.length_replicate]; exact ht)
    simp only [List.length_replicate, List.getElem?_replicate, ht, ↓reduceIte] at h
    rw [← hpre] at h
    have hpl : pre r + t < ((List.range (Rel.n P).toNat).flatMap fun t =>
        List.replicate (Column.bitsAt c (t * 8) 8).toNat t).length := by
      rw [← hI, ← len_eq_ids, hxl]; have := hpre_le (r + 1) _ hr; rw [hpre_succ] at this; omega
    rw [ids_get hI hpl]; rw [List.getElem?_eq_getElem hpl] at h; exact Option.some.inj h
  have hxrg : ∀ d, d < len xi →
      (Column.bitsAt xr (d * 8) 8).toNat = d - pre ((Column.bitsAt xi (d * 8) 8).toNat) := by
    intro d hd
    have := expand_rank (n := Rel.n P) (cnt := c) (by omega) (by rw [hcl, ← hpre]; exact hpN)
      (by rw [← hxi]; exact hxU) (p := d) (by rw [← hxi]; exact hd)
    rw [← hxi, ← hm, ← hxr, ← hpre] at this
    exact this
  -- copy `d` of row `r`: its cells in the two payloads (`ja`, `jb`)
  have hD : ∀ d, d < len xi → ∃ r, r < (Rel.n P).toNat ∧ pre r ≤ d ∧
      d < pre r + (Column.bitsAt c (r * 8) 8).toNat ∧ (Column.bitsAt xi (d * 8) 8).toNat = r ∧
      (Column.bitsAt ja (d * 8) 8).toNat = (Column.bitsAt (slicesOf (Rel.val P).1).1 (r * 8) 8).toNat + (d - pre r) ∧
      (Column.bitsAt jb (d * 8) 8).toNat = (Column.bitsAt (slicesOf (Rel.val P).2).1 (r * 8) 8).toNat + (d - pre r) := by
    intro d hd
    obtain ⟨r, hr, hxe, h1, h2⟩ := hxi_at d hd
    have hrk := hxrg d hd; rw [hxe] at hrk
    have hdm : d < m.toNat := by omega
    have hcr := hcg r hr
    obtain ⟨hLa, -, -⟩ := hRa r hr
    obtain ⟨hLb, -, -⟩ := hRb r hr
    have hga : Column.bitsAt (gather 8 (slicesOf (Rel.val P).1).1 xi) (d * 8) 8 =
        Column.bitsAt (slicesOf (Rel.val P).1).1 (r * 8) 8 := by
      rw [gather8_get (src := (slicesOf (Rel.val P).1).1) hd (by rw [hxe, hsa]; exact hr), hxe]
    have hgb : Column.bitsAt (gather 8 (slicesOf (Rel.val P).2).1 xi) (d * 8) 8 =
        Column.bitsAt (slicesOf (Rel.val P).2).1 (r * 8) 8 := by
      rw [gather8_get (src := (slicesOf (Rel.val P).2).1) hd (by rw [hxe, hsb]; exact hr), hxe]
    refine ⟨r, hr, h1, h2, hxe, ?_, ?_⟩
    · rw [hja, add_get (a := gather 8 (slicesOf (Rel.val P).1).1 xi) (b := xr) hdm (by rw [hga, hrk]; omega),
        hga, hrk]
    · rw [hjb, add_get (a := gather 8 (slicesOf (Rel.val P).2).1 xi) (b := xr) hdm (by rw [hgb, hrk]; omega),
        hgb, hrk]
  -- the copies' payload places are row `r`'s first `c[r]` window places, each once: a side's payload fits there
  have hfit : ∀ {Y : Obj} (x : Vals (.arr Y) (Rel.n P)) (j : ByteArray),
      Vals.PickFits (.arr Y) x (List.range (Rel.n P).toNat) →
      (∀ r, r < (Rel.n P).toNat →
        (Column.bitsAt c (r * 8) 8).toNat ≤ (Column.bitsAt (slicesOf x).2 (r * 8) 8).toNat) →
      (∀ d, d < len xi → ∀ r, (Column.bitsAt xi (d * 8) 8).toNat = r →
        (Column.bitsAt j (d * 8) 8).toNat = (Column.bitsAt (slicesOf x).1 (r * 8) 8).toNat + (d - pre r)) →
      Vals.PickFits Y x.2.2.2 ((List.range m.toNat).map fun q => (Column.bitsAt j (q * 8) 8).toNat) := by
    intro Y x j hx hcx hj
    obtain ⟨hp, hw⟩ := pickFits_payload x hx
    obtain ⟨g, hg⟩ : ∃ g : Nat → List Nat, ∀ r,
        g r = List.range' (Column.bitsAt (slicesOf x).1 (r * 8) 8).toNat (Column.bitsAt c (r * 8) 8).toNat :=
      ⟨_, fun _ => rfl⟩
    have hgl : ∀ t, ((List.range t).map fun s => (g s).length).sum = pre t := fun t => by
      rw [hpre]; simp only [hg, List.length_range']
    have he : (List.range m.toNat).map (fun q => (Column.bitsAt j (q * 8) 8).toNat) =
        (List.range (Rel.n P).toNat).flatMap g := by
      apply List.ext_getElem
      · rw [List.length_map, List.length_range, hmN, hxl, List.length_flatMap, ← hgl]
      · intro d h1 h2
        rw [List.getElem_map, List.getElem_range]
        have hd : d < len xi := by rw [← hmN]; simpa using h1
        obtain ⟨t, ht, hlo, hhi, hget⟩ := flatMap_get g (Rel.n P).toNat d (by rw [hgl, ← hxl]; exact hd)
        rw [hgl] at hlo hhi hget
        rw [hg, List.length_range'] at hhi
        have hx := hxi_in t (d - pre t) ht (by omega)
        rw [show pre t + (d - pre t) = d by omega] at hx
        rw [hj d hd t hx]
        rw [List.getElem?_eq_getElem h2, hg, List.getElem?_range' (by omega)] at hget
        simp only [Option.some.injEq] at hget
        omega
    have key : ∀ f : Nat → List Nat, (∀ r ∈ List.range (Rel.n P).toNat, (g r).Sublist (f r)) →
        ((List.range (Rel.n P).toNat).flatMap g).Sublist ((List.range (Rel.n P).toNat).flatMap f) := by
      intro f h
      have := flatMap_sublist_map_flatMap (fun r => r) g f h
      rwa [List.map_id'] at this
    refine pickFits_sublist ?_ hw
    rw [he]
    refine key _ fun r hr => ?_
    rw [List.mem_range] at hr
    dsimp only
    rw [dif_pos hr, hg, ← (slicesOf_get x hp hr).2, ← (slicesOf_get x hp hr).1]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hcx r hr)
    rw [hk, ← List.range'_append]
    exact List.sublist_append_left _ _
  have hAf := hfit (Rel.val P).1 ja hPa (fun r hr => by rw [hcg r hr]; exact Nat.min_le_left _ _)
    fun d hd r hx => by obtain ⟨r', -, -, -, hx', h1, -⟩ := hD d hd; rw [hx] at hx'; subst hx'; exact h1
  have hBf := hfit (Rel.val P).2 jb hPb (fun r hr => by rw [hcg r hr]; exact Nat.min_le_right _ _)
    fun d hd r hx => by obtain ⟨r', -, -, -, hx', -, h2⟩ := hD d hd; rw [hx] at hx'; subst hx'; exact h2
  -- the key: `Vals.compact` reads back every row
  have hkey : ∀ q : Fin (Rel.n P).toNat, (Vals.compact K (Rel.key P)).row q = (Rel.key P).row q := fun q => by
    rw [show Vals.compact K (Rel.key P) = Vals.pick K (Rel.key P) (tilLongs _) _ (len_tilLongs _) from rfl,
      pick_row K (Rel.key P) (tilLongs (Rel.n P)) (Rel.n P) (len_tilLongs _) hKf,
      dif_pos (show (Column.bitsAt (tilLongs (Rel.n P)) (q.1 * 8) 8).toNat < (Rel.n P).toNat by
        rw [tilLongs_get q.2]; exact q.2)]
    exact congrArg (Vals.row (Rel.key P)) (Fin.ext (tilLongs_get q.2))
  -- row `r` of the result: the two rows' cells paired position by position
  have hrow : ∀ (hh : (Rel.n P).toNat ≤ len (sums (Rel.n P) c)) (h1 : len ja = m.toNat)
      (h2 : len jb = m.toNat) (r : Nat) (hr : r < (Rel.n P).toNat),
      Vals.row (A := .arr (.prod A B)) (⟨m, valCol Ew.sub Ew.vv (sums (Rel.n P) c) c,
        longsN (Rel.n P) (sums (Rel.n P) c) hh,
        (Vals.pick A (Rel.val P).1.2.2.2 ja m h1, Vals.pick B (Rel.val P).2.2.2.2 jb m h2)⟩ :
          Vals (.arr (.prod A B)) (Rel.n P)) ⟨r, hr⟩ =
        List.zip (Vals.row (Rel.val P).1 ⟨r, hr⟩) (Vals.row (Rel.val P).2 ⟨r, hr⟩) := by
    intro hh h1 h2 r hr
    have e1 := hhig r hr; have e2 := hpre_succ r; have e3 := hpre_le (r + 1) _ hr; have e4 := hlog r hr
    have hlo' : ((valCol (n := Rel.n P) Ew.sub Ew.vv (sums (Rel.n P) c) c).get ⟨r, hr⟩).toInt =
        ((pre r : Nat) : Int) := by
      rw [valCol_get]; dsimp only
      rw [show Kernel.Ew.val Ew.sub Ew.i64 Ew.vv nul (sums (Rel.n P) c) c (Rel.n P) =
          sub (Rel.n P) (sums (Rel.n P) c) c from rfl,
        toInt64_toInt (x := Column.bitsAt (sub (Rel.n P) (sums (Rel.n P) c) c) (r * 8) 8) (by omega), e4]
    have hhi' : ((longsN (Rel.n P) (sums (Rel.n P) c) hh).get ⟨r, hr⟩).toInt = ((pre (r + 1) : Nat) : Int) := by
      rw [longsN_get]; dsimp only
      rw [toInt64_toInt (x := Column.bitsAt (sums (Rel.n P) c) (r * 8) 8) (by omega), e1]
    have hrw := arr_row (b := .prod A B) (⟨m, valCol (n := Rel.n P) Ew.sub Ew.vv (sums (Rel.n P) c) c,
      longsN (Rel.n P) (sums (Rel.n P) c) hh,
      (Vals.pick A (Rel.val P).1.2.2.2 ja m h1, Vals.pick B (Rel.val P).2.2.2.2 jb m h2)⟩ :
        Vals (.arr (.prod A B)) (Rel.n P)) ⟨r, hr⟩
    dsimp only at hrw
    rw [hlo', hhi'] at hrw
    have hmx : pre (r + 1) ≤ m.toNat := by rw [hmN, hxl]; exact e3
    have f1 : min (max ((pre r : Nat) : Int) 0).toNat m.toNat = pre r := by omega
    have f2 : min (max ((pre (r + 1) : Nat) : Int) 0).toNat m.toNat = pre (r + 1) := by omega
    rw [f1, f2] at hrw
    rw [hrw]
    obtain ⟨hLa, hla, hgeta⟩ := hRa r hr
    obtain ⟨hLb, hlb, hgetb⟩ := hRb r hr
    have hcr := hcg r hr
    apply List.ext_getElem
    · rw [List.length_zip, hla, hlb, List.length_map, List.length_range]; omega
    · intro t h1' h2'
      have ht : t < (Column.bitsAt c (r * 8) 8).toNat := by
        simp only [List.length_map, List.length_range] at h1'; omega
      have hb : pre r + t < m.toNat := by omega
      rw [List.getElem_map, List.getElem_range, dif_pos hb, List.getElem_zip]
      obtain ⟨r', hr', -, -, hx, hjad, hjbd⟩ := hD (pre r + t) (by omega)
      rw [hxi_in r t hr ht] at hx
      rw [← hx] at hjad hjbd
      refine Prod.ext ?_ ?_
      · show Vals.row (Vals.pick A (Rel.val P).1.2.2.2 ja m h1) ⟨pre r + t, hb⟩ = (Vals.row (Rel.val P).1 ⟨r, hr⟩)[t]
        rw [pick_row A _ ja m h1 hAf, dif_pos (show (Column.bitsAt ja ((pre r + t) * 8) 8).toNat <
          (Rel.val P).1.1.toNat by rw [hjad]; omega), hgeta t (by omega) (by omega)]
        exact congrArg _ (Fin.ext (show (Column.bitsAt ja ((pre r + t) * 8) 8).toNat =
          (Column.bitsAt (slicesOf (Rel.val P).1).1 (r * 8) 8).toNat + t by rw [hjad]; omega))
      · show Vals.row (Vals.pick B (Rel.val P).2.2.2.2 jb m h2) ⟨pre r + t, hb⟩ = (Vals.row (Rel.val P).2 ⟨r, hr⟩)[t]
        rw [pick_row B _ jb m h2 hBf, dif_pos (show (Column.bitsAt jb ((pre r + t) * 8) 8).toNat <
          (Rel.val P).2.1.toNat by rw [hjbd]; omega), hgetb t (by omega) (by omega)]
        exact congrArg _ (Fin.ext (show (Column.bitsAt jb ((pre r + t) * 8) 8).toNat =
          (Column.bitsAt (slicesOf (Rel.val P).2).1 (r * 8) 8).toNat + t by rw [hjbd]; omega))
  -- `zip` unfolded at its pieces
  subst hm
  subst hja hjb hxr hxi hc
  unfold zip expand need
  dsimp only
  rw [dif_pos hxU]
  try dsimp only
  show (∃ q, _ ∧ _) ↔ _
  constructor
  · rintro ⟨⟨r, hr⟩, hk, hv⟩
    refine ⟨Vals.row (Rel.val P).1 ⟨r, hr⟩, Vals.row (Rel.val P).2 ⟨r, hr⟩, ?_, ?_⟩
    · show ∃ q, _ ∧ _
      exact ⟨⟨r, hr⟩, (hkey _).symm.trans hk, rfl⟩
    · rw [← hv]; exact hrow _ _ _ r hr
  · rintro ⟨xs, ys, ⟨⟨r, hr⟩, hk, hv⟩, rfl⟩
    refine ⟨⟨r, hr⟩, (hkey _).trans hk, ?_⟩
    rw [hrow _ _ _ r hr, show Vals.row (Rel.val P).1 ⟨r, hr⟩ = xs from congrArg Prod.fst hv,
      show Vals.row (Rel.val P).2 ⟨r, hr⟩ = ys from congrArg Prod.snd hv]

#print axioms nilVal_row
#print axioms rep_nil
#print axioms rep_atPos
#print axioms rep_unsnoc
#print axioms rep_zip

end LeetQ.Rel.Rep
