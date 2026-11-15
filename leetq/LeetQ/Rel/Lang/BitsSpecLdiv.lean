/-
  `\` as bits: `Bits.ldiv`'s `∧` of `S`'s rows over `R`'s segments, masked by `ran R ⊗ ⊤ ∪ Ub ⊗ Uc`, holds
  `TP.ldiv`'s relation. Each part is `enc_rows` (`∧` for the rows, `∨` for each mask through the one point).
-/
import LeetQ.Rel.Lang.BitsSpec
import LeetQ.Rel.KernelWF.SortSpec
import LeetQ.Rel.KernelWF.BagSpec
import LeetQ.Rel.KernelWF.JoinContent
import LeetQ.Rel.KernelWF.RowsSpec
import LeetQ.Rel.KernelWF.ComposeKey
import LeetQ.Rel.KernelWF.Raze

namespace LeetQ.Rel.Lang.Bits

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep

/-- **`zeros n`** is `n` longs, each `0`. -/
theorem zeros_ids {n : Nat} (hn : n < min (2 ^ 63) USize.size) :
    len (zeros n) = n ∧ ∀ x ∈ ids (zeros n), x = 0 := by
  have hU : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hn (Nat.min_le_right _ _))
  have hl : len (zeros n) = n := by
    rw [len_eq_ids, ids, List.length_map, List.length_range, zeros, KernelWF.Ew.val_size, hU]
    show n * 8 / 8 = n; omega
  refine ⟨hl, fun x hx => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have hk' : k < n.toUSize.toNat := by rw [hU, ← hl, len_eq_ids]; exact hk
  rw [← ids_get rfl hk, zeros, val_va_get _ _ _ _ hk', bitsAt_one]
  have hx : (Column.bitsAt (tilLongs n.toUSize) (k * 8) 8).toNat < 2 ^ 63 := by
    rw [tilLongs_get hk']; rw [hU] at hk'; have := Nat.min_le_left (2 ^ 63) USize.size; omega
  have h := (valStep_key _ 0 hx (by decide)).1 (by simp)
  rw [show UInt64.toNat 0 = 0 from rfl, Nat.mul_zero] at h; exact h

/-- **`Bits.const true 1 w`** is the one row of ones: `bitRowsOver`'s `∧` over an empty segment. -/
theorem const_true_enc {X Y : Obj} (u : Nat → X.El) (v : Nat → Y.El) {w : Nat} (hw : w ≤ 2 ^ 27) :
    (Bits.const true 1 w).Enc u v fun _ _ => True := by
  intro i hi j hj
  change i < 1 at hi; change j < w at hj
  obtain rfl : i = 0 := by omega
  have hz : (zeros (1 + 1)).size / 8 = 1 + 1 := by
    rw [zeros, KernelWF.Ew.val_size,
      USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by omega : 1 + 1 < 2 ^ 32) USize.le_size)]; rfl
  have e := bitRowsOver_spec true w.toUSize (zeros (1 + 1)) .empty .empty 0 j _ _ (by rw [hz]; omega)
    (by rw [toUSize_fit hw]; exact hj) rfl
  rw [toUSize_fit hw] at e
  show Column.bitAt (bitRowsOver true w.toUSize (zeros (1 + 1)) .empty .empty) (0 * w + j) = true ↔ True
  rw [iff_true]; exact e.2 (by simp)

/-- A relation into the one point, read off an ascending column `i` beside a column `z` of zeros: `b` reaches the
    point iff `P` holds, iff `b` is in `i`. -/
theorem pt_iff {α : Sort _} {P : Prop} {u : Nat → α} {m : α} {i z : ByteArray} {b : Nat}
    (hz : len z = len i) (h0 : ∀ x ∈ ids z, x = 0)
    (hP : P ↔ ∃ (k : Nat) (hk : k < (ids i).length), (ids i)[k]'hk = b) :
    (P ∧ m = u 0) ↔ ∃ (k : Nat) (hk : k < (ids i).length) (hk' : k < (ids z).length),
      (ids i)[k]'hk = b ∧ u ((ids z)[k]'hk') = m := by
  rw [hP]
  constructor
  · rintro ⟨⟨k, hk, e⟩, rfl⟩
    have hk' : k < (ids z).length := by rw [← len_eq_ids, hz, len_eq_ids]; exact hk
    exact ⟨k, hk, hk', e, by rw [h0 _ (List.getElem_mem hk')]⟩
  · rintro ⟨k, hk, hk', e, rfl⟩
    exact ⟨⟨k, hk, e⟩, by rw [h0 _ (List.getElem_mem hk')]⟩

variable {A B C : Obj} {ua : Nat → A.El} {ub : Nat → B.El}

/-- **`\` as bits** (`rep_leftDiv`'s side, `rep_tableC`): from `R°`'s code pairs `y`, `a` (`y` ascending, `R` read
    off them), `S`'s matrix and the codes `kb`, `kc` of `UB`'s and `UC`'s elements, `Bits.ldiv` holds `TP.ldiv`'s
    relation: the `∧` of `S`'s rows answers the `∀` clause, the mask `ran R ⊗ ⊤ ∪ Ub ⊗ Uc` the vacuous one. -/
theorem rep_ldivB {R : TP A B} {S : TP A C} {UB : Rel B B} {UC : Rel C C} {uc : Nat → C.El} (nb : Nat)
    (y a : ByteArray) {s : Bits} (kb kc : ByteArray)
    (hs : s.Enc ua uc S.den) (hl : len a = len y) (hsort : (ids y).Pairwise (· ≤ ·)) (hJ : ∀ x ∈ ids a, x < s.na)
    (hR : ∀ b < nb, ∀ x, R.den x (ub b) ↔
      ∃ (k : Nat) (hk : k < (ids y).length) (hk' : k < (ids a).length), (ids y)[k]'hk = b ∧ ua ((ids a)[k]'hk') = x)
    (hkb : ∀ x ∈ ids kb, x < nb) (hUB : ∀ b < nb, (∃ p, UB.val.row p = ub b) ↔ b ∈ ids kb)
    (hkc : ∀ x ∈ ids kc, x < s.w) (hUC : ∀ c < s.w, (∃ q, UC.val.row q = uc c) ↔ c ∈ ids kc)
    (hnb : nb ≤ 2 ^ 27) (hfit : s.na * s.w ≤ 2 ^ 27) (hsw : s.w ≤ 2 ^ 27) (hout : nb * s.w ≤ 2 ^ 27)
    (hm : len y < min (2 ^ 63) USize.size) (hmb : len kb < min (2 ^ 63) USize.size)
    (hmc : len kc < min (2 ^ 63) USize.size) :
    (Bits.ldiv nb y a s kb kc).Enc ub uc (TP.ldiv R S UB UC).den := by
  have hsw' : 1 * s.w ≤ 2 ^ 27 := by omega
  -- the `∀` clause: `∧` of `S`'s rows over `R`'s segments
  have hd := enc_rows (ua := ub) (ub := ua) (r := fun b x => R.den x b) (t := S.den) true nb y a hs hl hsort hJ hR
    hnb hfit hsw hm
  -- `ran R ⊗ ⊤`: `R`'s segments into the one point, whose row is all ones
  obtain ⟨hzy, hzy0⟩ := zeros_ids hm
  have hran := enc_rows (ua := ub) (ub := fun _ => uc 0) (r := fun b m => (∃ x, R.den x b) ∧ m = uc 0)
    (t := fun _ _ => True) false nb y (zeros (len y)) (const_true_enc (fun _ => uc 0) uc hsw) hzy hsort
    (fun x hx => by rw [hzy0 x hx]; exact Nat.zero_lt_one)
    (fun b hb m => pt_iff (P := ∃ x, R.den x (ub b)) (u := fun _ => uc 0) hzy hzy0
      ⟨fun ⟨x, hx⟩ => let ⟨k, hk, _, e, _⟩ := (hR b hb x).1 hx; ⟨k, hk, e⟩,
        fun ⟨k, hk, e⟩ => ⟨_, (hR b hb _).2 ⟨k, hk, by rw [← len_eq_ids, hl, len_eq_ids]; exact hk, e, rfl⟩⟩⟩)
    hnb hsw' hsw hm
  -- `Ub ⊗ Uc`: `kb` sorted (`grade`, `gather`), into the one point, whose row is `kc`
  have hkb63 : ∀ i, i < len kb → (Column.bitsAt kb (i * 8) 8).toNat < 2 ^ 63 := fun i hi => by
    have hi' : i < (ids kb).length := by rw [← len_eq_ids]; exact hi
    rw [ids_get rfl hi']; have := hkb _ (List.getElem_mem hi'); omega
  obtain ⟨hgp, hgs⟩ := grade_ofLongs kb (Nat.lt_of_lt_of_le hmb (Nat.min_le_right _ _)) hkb63
  have hgt : ∀ t ∈ ids (Code.ofLongs kb).grade, t < len kb := fun t ht => List.mem_range.1 (hgp.subset ht)
  have hget : ∀ t < len kb, (ids kb).getD t 0 = (Column.bitsAt kb (t * 8) 8).toNat := fun t ht => by
    have ht' : t < (ids kb).length := by rw [← len_eq_ids]; exact ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht', Option.getD_some]
    exact (ids_get rfl ht').symm
  have hsb : (ids (gather 8 kb (Code.ofLongs kb).grade)).Pairwise (· ≤ ·) := by
    rw [ids_gather8 hgt, List.pairwise_map]
    exact hgs.imp_of_mem fun {p q} hp hq h => by rw [hget p (hgt p hp), hget q (hgt q hq)]; omega
  have hpb : (ids (gather 8 kb (Code.ofLongs kb).grade)).Perm (ids kb) := gather_perm hgp
  have hlb : len (gather 8 kb (Code.ofLongs kb).grade) = len kb := by
    rw [gather_len, len_eq_ids, hgp.length_eq, List.length_range]
  obtain ⟨hzb, hzb0⟩ := zeros_ids hmb
  obtain ⟨hzc, hzc0⟩ := zeros_ids hmc
  have hofc : (Bits.ofCodes 1 s.w (zeros (len kc)) kc).Enc (fun _ => uc 0) uc
      fun _ c => ∃ q, UC.val.row q = c := by
    intro i hi c hc
    change i < 1 at hi; change c < s.w at hc
    obtain rfl : i = 0 := by omega
    show _ ↔ ∃ q, UC.val.row q = uc c
    rw [ofCodes_at hzc.symm (fun x hx => by rw [hzc0 x hx]; exact Nat.zero_lt_one) hkc hsw'
      (by rw [hzc]; exact Nat.lt_of_lt_of_le hmc (Nat.min_le_right _ _)) hi hc, hUC c hc, List.mem_iff_getElem]
    constructor
    · rintro ⟨r, -, h2, -, e⟩; exact ⟨r, h2, e⟩
    · rintro ⟨r, h2, e⟩
      have h1 : r < (ids (zeros (len kc))).length := by rw [← len_eq_ids, hzc, len_eq_ids]; exact h2
      exact ⟨r, h1, h2, hzc0 _ (List.getElem_mem h1), e⟩
  have hvac := enc_rows (ua := ub) (ub := fun _ => uc 0) (r := fun b m => (∃ p, UB.val.row p = b) ∧ m = uc 0)
    (t := fun _ c => ∃ q, UC.val.row q = c) false nb _ (zeros (len kb)) hofc (hzb.trans hlb.symm) hsb
    (fun x hx => by rw [hzb0 x hx]; exact Nat.zero_lt_one)
    (fun b hb m => pt_iff (u := fun _ => uc 0) (hzb.trans hlb.symm) hzb0
      ((hUB b hb).trans (hpb.mem_iff.symm.trans List.mem_iff_getElem)))
    hnb hsw' hsw (by rw [hlb]; exact hmb)
  -- the rows masked by `ran R ⊗ ⊤ ∪ Ub ⊗ Uc`
  have hjoin := enc_bit _ Or (fun p q => by rw [bitStep_greater, Bool.or_eq_true]) hran hvac rfl rfl hout
  have hmeet := enc_bit _ And (fun p q => by rw [bitStep_lesser, Bool.and_eq_true]) hd hjoin rfl rfl hout
  intro b hb c hc
  refine Iff.trans (hmeet b hb c hc) ?_
  simp [TP.den]

#print axioms rep_ldivB

end LeetQ.Rel.Lang.Bits
