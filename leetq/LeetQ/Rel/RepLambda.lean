/-
  `rep` of `Λ(R)` (`transpose`): each key of `R` to the array of its values, read in `Rel(Set)` — the array of a
  key holds exactly the values `R` relates it to, and every key of `R` has a row.
-/
import LeetQ.Rel.KernelWF.RunSpec
import LeetQ.Rel.KernelWF.NubSpec
import LeetQ.Rel.KernelWF.CrossSpec

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF
open Freyd Freyd.Alg Freyd.Alg.RelSet

variable {A B : Obj}

/-- `longCount` where the count fits a `USize` runs its continuation at that count. -/
theorem longCount_eq {α : Type} [Inhabited α] (what : String) (b : ByteArray)
    (k : (n : USize) → len b = n.toNat → α) (h : len b < USize.size) :
    longCount what b k = k (len b).toUSize (USize.toNat_ofNat_of_lt' h).symm := by
  unfold longCount need; rw [dif_pos h]

/-- A long column cast to the count `M` it holds reads back its payload's longs. -/
theorem longCol_cast_get {b : ByteArray} {M : USize} (hb : len b < USize.size) (e : (len b).toUSize = M)
    (q : Fin M.toNat) : (e ▸ longCol b : Arr .long M).get q = (Column.bitsAt b (q.1 * 8) 8).toInt64 := by
  have hq : q.1 < len b := by
    have h1 := q.2; have h2 : M.toNat = len b := by rw [← e, USize.toNat_ofNat_of_lt' hb]
    omega
  rw [cast_get]
  unfold longCol need
  split
  · rw [Arr.get_long_bytes _ rfl]; dsimp only
    rw [bitsAt_extract _ (by omega), Nat.zero_add]
  · contradiction

/-- An array row holds `x` exactly when some position of the payload between the row's `lo` and `hi` holds it. -/
theorem mem_arr_row {b : Obj} {n K : USize} (lo hi : Arr .long n) (f : Vals b K) (q : Fin n.toNat) (x : b.El) :
    x ∈ Vals.row (A := .arr b) ⟨K, lo, hi, f⟩ q ↔
      ∃ s : Fin K.toNat, (lo.get q).toInt ≤ (s.1 : Int) ∧ (s.1 : Int) < (hi.get q).toInt ∧ Vals.row f s = x := by
  show x ∈ List.filterMap _ _ ↔ _
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨s, -, hs⟩
    split at hs
    · next h => exact ⟨s, h.1, h.2, Option.some.inj hs⟩
    · cases hs
  · rintro ⟨s, h1, h2, hs⟩
    exact ⟨s, List.mem_finRange s, by rw [if_pos ⟨h1, h2⟩, hs]⟩

-- `transpose`'s pieces, as it names them: the key codes, the values' order, the rows grouped, the run starts
set_option hygiene false in
local notation "kcT" => (Obj.codes A (#v[⟨(Rel.nub R).n, (Rel.nub R).key⟩] : Vector (Part A) 1))[0]'Nat.zero_lt_one
set_option hygiene false in
local notation "vpT" => Obj.sortBy B (Rel.nub R).val (tilLongs (Rel.nub R).n)
set_option hygiene false in
local notation "pT" => gather 8 vpT (Code.gather kcT vpT).grade
set_option hygiene false in
local notation "oT" => Code.runStarts (Code.gather kcT pT)
set_option hygiene false in
local notation "loT" => ByteArray.extract (oT) 0 (ByteArray.size (oT) - 8)

set_option maxHeartbeats 8000000 in
/-- **`Λ(R)`'s rows, read back against `R.nub`**: row `q` is keyed by a key `d.key.row i` of `d = R.nub`, and
    its array holds exactly the values `d` relates that key to; every key of `d` keys some row. Hypotheses: the
    key codes faithful and well formed (`rep_nub`'s `hK` at `d`), `sortBy_perm`'s `hW`, `d`'s count below
    `2⁶³`, and the picks fitting (`Vals.PickFits`) at the row order and at the run starts. -/
theorem transpose_rows (R : Rel A B)
    (hF : ∀ {i j : Nat} (hi : i < (Rel.nub R).n.toNat) (hj : j < (Rel.nub R).n.toNat),
      Column.idAt (kcT).b (kcT).w i = Column.idAt (kcT).b (kcT).w j ↔
        Vals.row (Rel.nub R).key ⟨i, hi⟩ = Vals.row (Rel.nub R).key ⟨j, hj⟩)
    (hw : (kcT).w = 1 ∨ (kcT).w = 2 ∨ (kcT).w = 4 ∨ (kcT).w = 8 ∨ (kcT).w = 16 ∨ (kcT).w = 32 ∨ (kcT).w = 64)
    (hn : (kcT).n = (Rel.nub R).n) (hs : (kcT).b.size = ((kcT).n.toNat * (kcT).w + 7) / 8)
    (hW : ∀ (B : Obj) (x : Part B), (((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 1 ∨ ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 2 ∨
      ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 4 ∨ ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 8 ∨ ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 16 ∨
      ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 32 ∨ ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 64) ∧
      ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).b.size = (((Obj.codes B #v[x])[0]'Nat.zero_lt_one).n.toNat * ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w + 7) / 8 ∧
      ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).n = x.1)
    (h63 : (Rel.nub R).n.toNat < 2 ^ 63)
    (hpk : Vals.PickFits A (Rel.nub R).key (ids pT)) (hpv : Vals.PickFits B (Rel.nub R).val (ids pT))
    (hlo : Vals.PickFits A (Vals.pickPart A (Rel.nub R).key pT).2 (ids loT)) :
    (∀ q : Fin (Alg.transpose R).n.toNat, ∃ i : Fin (Rel.nub R).n.toNat,
      Vals.row (Alg.transpose R).key q = Vals.row (Rel.nub R).key i ∧ ∀ x, x ∈ Vals.row (Alg.transpose R).val q ↔
        ∃ i' : Fin (Rel.nub R).n.toNat, Vals.row (Rel.nub R).key i' = Vals.row (Rel.nub R).key i ∧
          Vals.row (Rel.nub R).val i' = x) ∧
    ∀ i : Fin (Rel.nub R).n.toNat, ∃ q : Fin (Alg.transpose R).n.toNat,
      Vals.row (Alg.transpose R).key q = Vals.row (Rel.nub R).key i := by
  have hN : (kcT).n.toNat = (Rel.nub R).n.toNat := by rw [hn]
  have hU : (Rel.nub R).n.toNat < USize.size := (Rel.nub R).n.toNat_lt_size
  -- `til n` read back, `vp` a permutation of the rows
  have htil : (ids (tilLongs (Rel.nub R).n)).Perm (List.range (Rel.nub R).n.toNat) := by
    refine List.Perm.of_eq (List.ext_getElem (by rw [← len_eq_ids, len_tilLongs, List.length_range]) ?_)
    intro j h1 h2
    have hj : j < (Rel.nub R).n.toNat := by simpa using h2
    rw [ids_getElem h1, tilLongs_bitsAt _ hj, List.getElem_range, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by have := USize.size_le; omega)]
  have hvp : (ids vpT).Perm (List.range (kcT).n.toNat) := by
    rw [hN]; exact (sortBy_perm hW B _ _ (by rw [len_tilLongs]; exact hU)).trans htil
  obtain ⟨hpp, hgrp⟩ := grade_gather_group (kcT) hw hs vpT hvp
  -- the row order `p`: its long `s` is `P s`, every row once
  have hlp : len pT = (Rel.nub R).n.toNat := by rw [len_eq_ids, hpp.length_eq, List.length_range, hN]
  have hpl : len pT < USize.size := by rw [hlp]; exact hU
  have hpi : ∀ s < len pT, (Column.bitsAt pT (s * 8) 8).toNat < (kcT).n.toNat := fun s h => by
    have h' : s < (ids pT).length := by rw [← len_eq_ids]; exact h
    rw [← ids_getElem h']; exact List.mem_range.1 (hpp.mem_iff.1 (List.getElem_mem h'))
  have hP : ∀ s < len pT, (Column.bitsAt pT (s * 8) 8).toNat < (Rel.nub R).n.toNat := fun s h => by
    rw [← hN]; exact hpi s h
  have hsurj : ∀ i < (Rel.nub R).n.toNat, ∃ s, s < len pT ∧ (Column.bitsAt pT (s * 8) 8).toNat = i := fun i hi => by
    obtain ⟨s, hs', e⟩ := List.getElem_of_mem (hpp.mem_iff.2 (List.mem_range.2 (by rw [hN]; exact hi)))
    exact ⟨s, by rw [len_eq_ids]; exact hs', by rw [← ids_getElem hs']; exact e⟩
  have hcb : 8 ≤ (kcT).w → 8 * (kcT).b.size = (kcT).w * (kcT).n.toNat := fun h8 => by
    rcases hw with h | h | h | h | h | h | h <;> rw [h] at hs ⊢ <;> omega
  obtain ⟨hGw, hGn, -, hGid⟩ := gather_spec (kcT) pT hpl hw hcb hpi
  have hGs := gather_size (kcT) pT hpl hw
  -- the key codes along `p` are the keys of `d`
  have hcode : ∀ s t (hs' : s < len pT) (ht : t < len pT),
      (Column.idAt (Code.gather (kcT) pT).b (kcT).w s = Column.idAt (Code.gather (kcT) pT).b (kcT).w t ↔
        Vals.row (Rel.nub R).key ⟨_, hP s hs'⟩ = Vals.row (Rel.nub R).key ⟨_, hP t ht⟩) :=
    fun s t hs' ht => by rw [hGid s hs', hGid t ht]; exact hF _ _
  -- the runs of `G = kc@p`: `r j`, each key one run
  obtain ⟨m, hosz, hlast, hasc, -, hrun, hcov⟩ := code_runs (Code.gather (kcT) pT) (by rw [hGw]; exact hw)
    (by rw [hGs, hGn, hGw])
    (fun s t u h1 h2 hu e => by
      rw [hGn] at hu
      rw [hGw] at e ⊢
      rw [hGid s (by omega), hGid u (by omega)] at e
      rw [hGid t (by omega), hGid s (by omega)]
      rw [hlp, ← hN] at hu
      exact hgrp s t u h1 h2 hu e)
  rw [hGn] at hlast hrun hcov
  rw [hGw] at hrun
  -- the picked columns read back at `P s`
  have hpkd : Vals.pickPart A (Rel.nub R).key pT =
      ⟨(len pT).toUSize, Vals.pick A (Rel.nub R).key pT _ (USize.toNat_ofNat_of_lt' hpl).symm⟩ := by
    unfold Vals.pickPart need; rw [dif_pos hpl]
  have hpvd : Vals.pickPart B (Rel.nub R).val pT =
      ⟨(len pT).toUSize, Vals.pick B (Rel.nub R).val pT _ (USize.toNat_ofNat_of_lt' hpl).symm⟩ := by
    unfold Vals.pickPart need; rw [dif_pos hpl]
  have hLn : ((len pT).toUSize).toNat = len pT := USize.toNat_ofNat_of_lt' hpl
  have hp1A : (Vals.pickPart A (Rel.nub R).key pT).1.toNat = len pT := by rw [hpkd]; exact hLn
  have hp1B : (Vals.pickPart B (Rel.nub R).val pT).1.toNat = len pT := by rw [hpvd]; exact hLn
  have hkey : ∀ s (h : s < (Vals.pickPart A (Rel.nub R).key pT).1.toNat) (h' : s < len pT),
      Vals.row (Vals.pickPart A (Rel.nub R).key pT).2 ⟨s, h⟩ = Vals.row (Rel.nub R).key ⟨_, hP s h'⟩ := by
    intro s h h'; revert h; rw [hpkd]; intro h; dsimp only at h ⊢
    rw [pick_row A _ pT _ _ (by rw [hLn]; exact hpk) ⟨s, h⟩, dif_pos (hP s h')]
  have hval : ∀ s (h : s < (Vals.pickPart B (Rel.nub R).val pT).1.toNat) (h' : s < len pT),
      Vals.row (Vals.pickPart B (Rel.nub R).val pT).2 ⟨s, h⟩ = Vals.row (Rel.nub R).val ⟨_, hP s h'⟩ := by
    intro s h h'; revert h; rw [hpvd]; intro h; dsimp only at h ⊢
    rw [pick_row B _ pT _ _ (by rw [hLn]; exact hpv) ⟨s, h⟩, dif_pos (hP s h')]
  -- the run starts `o`: `lo`, `hi` their extracts, each start below the count
  generalize hO : Code.runStarts (Code.gather (kcT) pT) = o at hosz hlast hasc hrun hcov hlo
  have hrlt : ∀ j, j < m → (Column.bitsAt o (j * 8) 8).toNat < len pT := fun j hj => by
    have := hasc j m hj (Nat.le_refl m); omega
  have hrle : ∀ j, j ≤ m → (Column.bitsAt o (j * 8) 8).toNat ≤ len pT := fun j hj => by
    rcases Nat.lt_or_eq_of_le hj with h | rfl
    · have := hasc j m h (Nat.le_refl m); omega
    · omega
  have hge : ∀ j, j ≤ m → j ≤ (Column.bitsAt o (j * 8) 8).toNat := by
    intro j
    induction j with
    | zero => intro _; omega
    | succ j ih => intro hj; have := hasc j (j + 1) (by omega) hj; have := ih (by omega); omega
  have hlolen : len (o.extract 0 (o.size - 8)) = m := by simp only [len, ByteArray.size_extract]; omega
  have hloU : len (o.extract 0 (o.size - 8)) < USize.size := by
    rw [hlolen]; have := hge m (Nat.le_refl m); omega
  have hhilen : len (o.extract 8 o.size) = len (o.extract 0 (o.size - 8)) := by
    simp only [len, ByteArray.size_extract]; omega
  have hhiU : len (o.extract 8 o.size) < USize.size := by rw [hhilen]; exact hloU
  have hlo_at : ∀ j, j < m → Column.bitsAt (o.extract 0 (o.size - 8)) (j * 8) 8 = Column.bitsAt o (j * 8) 8 :=
    fun j hj => by rw [bitsAt_extract _ (by omega), Nat.zero_add]
  have hhi_at : ∀ j, j < m → Column.bitsAt (o.extract 8 o.size) (j * 8) 8 = Column.bitsAt o ((j + 1) * 8) 8 :=
    fun j hj => by rw [bitsAt_extract _ (by omega), show 8 + j * 8 = (j + 1) * 8 by omega]
  have hMn : ((len (o.extract 0 (o.size - 8))).toUSize).toNat = m := by
    rw [USize.toNat_ofNat_of_lt' hloU, hlolen]
  -- row `j` of the answer is keyed by `P (r j)`
  have hkrow : ∀ j (h : j < ((len (o.extract 0 (o.size - 8))).toUSize).toNat) (hj : j < m),
      Vals.row (Vals.pick A (Vals.pickPart A (Rel.nub R).key pT).2
        (o.extract 0 (o.size - 8)) _ (USize.toNat_ofNat_of_lt' hloU).symm) ⟨j, h⟩ =
      Vals.row (Rel.nub R).key ⟨_, hP _ (hrlt j hj)⟩ := fun j h hj => by
    rw [pick_row A _ _ _ _ (by rw [USize.toNat_ofNat_of_lt' hloU]; exact hlo) ⟨j, h⟩,
      dif_pos (by rw [hlo_at j hj, hp1A]; exact hrlt j hj)]
    exact (hkey _ _ (by rw [hlo_at j hj]; exact hrlt j hj)).trans
      (congrArg _ (Fin.ext (by dsimp only; rw [hlo_at j hj])))
  -- `transpose R` itself: its `longCount` run at the run starts
  subst hO
  unfold Alg.transpose; dsimp only
  rw [longCount_eq _ _ _ hloU]
  dsimp only
  refine ⟨fun q => ?_, fun i => ?_⟩
  · have hq : q.1 < m := by have := q.2; omega
    refine ⟨_, hkrow q.1 q.2 hq, fun x => ?_⟩
    have hq1 := hrle (q.1 + 1) (by omega)
    rw [mem_arr_row, longCol_cast_get hloU rfl, longCol_cast_get hhiU (congrArg Nat.toUSize hhilen),
      hlo_at q.1 hq, hhi_at q.1 hq, toInt_toInt64, toInt_toInt64, if_pos (by have := hrlt q.1 hq; omega),
      if_pos (by omega)]
    constructor
    · rintro ⟨s, h1, h2, hs'⟩
      have hsl : s.1 < len pT := by omega
      refine ⟨_, ?_, (hval s.1 s.2 hsl).symm.trans hs'⟩
      exact (hcode _ _ hsl (hrlt q.1 hq)).1 ((hrun s.1 q.1 hsl hq).2 ⟨by omega, by omega⟩)
    · rintro ⟨i', e1, e2⟩
      obtain ⟨s, hs', hsi⟩ := hsurj i'.1 i'.2
      have he : i' = ⟨_, hP s hs'⟩ := Fin.ext hsi.symm
      subst he
      obtain ⟨h1, h2⟩ := (hrun s q.1 hs' hq).1 ((hcode _ _ hs' (hrlt q.1 hq)).2 e1)
      exact ⟨⟨s, by rw [hp1B]; exact hs'⟩, Int.ofNat_le.2 h1, Int.ofNat_lt.2 h2, (hval s _ hs').trans e2⟩
  · obtain ⟨s, hs', hsi⟩ := hsurj i.1 i.2
    obtain ⟨j, hj, h1, h2⟩ := hcov s hs'
    refine ⟨⟨j, by rw [hMn]; exact hj⟩, (hkrow j _ hj).trans ?_⟩
    exact ((hcode _ _ (hrlt j hj) hs').1 ((hrun s j hs' hj).2 ⟨h1, h2⟩).symm).trans (congrArg _ (Fin.ext hsi))

#print axioms transpose_rows

-- `rep_nub`'s codes of `R` and the rows `nub` keeps (`NubSpec`'s local notations, restated)
set_option hygiene false in
local notation "kcR" => (Obj.codes A (#v[⟨Rel.n R, Rel.key R⟩] : Vector (Part A) 1))[0]'Nat.zero_lt_one
set_option hygiene false in
local notation "vcR" => (Obj.codes B (#v[⟨Rel.n R, Rel.val R⟩] : Vector (Part B) 1))[0]'Nat.zero_lt_one
set_option hygiene false in
local notation "nubR" => (tuples.tupleIds kcR #[vcR]).2

/-- **`rep (Λ(R))` is the power transpose of `rep R`**: the array `Λ(R)` gives a key `a` holds exactly the
    values `R` relates `a` to, and `Λ(R)` has a row at `a` exactly when `R` has a pair at `a`. Hypotheses:
    `rep_nub`'s (`hK hV hk hv`), and `transpose_rows`' at `d = R.nub`. -/
theorem rep_transpose (R : Rel A B)
    (hK : (∀ {i j : Nat} (hi : i < (Rel.n R).toNat) (hj : j < (Rel.n R).toNat),
        Column.idAt (kcR).b (kcR).w i = Column.idAt (kcR).b (kcR).w j ↔
          Vals.row (Rel.key R) ⟨i, hi⟩ = Vals.row (Rel.key R) ⟨j, hj⟩) ∧
      ((kcR).w = 1 ∨ (kcR).w = 2 ∨ (kcR).w = 4 ∨ (kcR).w = 8 ∨ (kcR).w = 16 ∨ (kcR).w = 32 ∨ (kcR).w = 64) ∧
        (kcR).n = Rel.n R ∧ (kcR).b.size = ((kcR).n.toNat * (kcR).w + 7) / 8 ∧
        ((kcR).w < 8 → (kcR).card < USize.size ∧ ∀ i < (kcR).n.toNat, Column.idAt (kcR).b (kcR).w i < (kcR).card))
    (hV : (∀ {i j : Nat} (hi : i < (Rel.n R).toNat) (hj : j < (Rel.n R).toNat),
        Column.idAt (vcR).b (vcR).w i = Column.idAt (vcR).b (vcR).w j ↔
          Vals.row (Rel.val R) ⟨i, hi⟩ = Vals.row (Rel.val R) ⟨j, hj⟩) ∧
      ((vcR).w = 1 ∨ (vcR).w = 2 ∨ (vcR).w = 4 ∨ (vcR).w = 8 ∨ (vcR).w = 16 ∨ (vcR).w = 32 ∨ (vcR).w = 64) ∧
        (vcR).n = Rel.n R ∧ (vcR).b.size = ((vcR).n.toNat * (vcR).w + 7) / 8 ∧
        ((vcR).w < 8 → (vcR).card < USize.size ∧ ∀ i < (vcR).n.toNat, Column.idAt (vcR).b (vcR).w i < (vcR).card))
    (hk : Vals.PickFits A (Rel.key R) (ids nubR)) (hv : Vals.PickFits B (Rel.val R) (ids nubR))
    (hF : ∀ {i j : Nat} (hi : i < (Rel.nub R).n.toNat) (hj : j < (Rel.nub R).n.toNat),
      Column.idAt (kcT).b (kcT).w i = Column.idAt (kcT).b (kcT).w j ↔
        Vals.row (Rel.nub R).key ⟨i, hi⟩ = Vals.row (Rel.nub R).key ⟨j, hj⟩)
    (hw : (kcT).w = 1 ∨ (kcT).w = 2 ∨ (kcT).w = 4 ∨ (kcT).w = 8 ∨ (kcT).w = 16 ∨ (kcT).w = 32 ∨ (kcT).w = 64)
    (hn : (kcT).n = (Rel.nub R).n) (hs : (kcT).b.size = ((kcT).n.toNat * (kcT).w + 7) / 8)
    (hW : ∀ (B : Obj) (x : Part B), (((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 1 ∨ ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 2 ∨
      ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 4 ∨ ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 8 ∨ ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 16 ∨
      ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 32 ∨ ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w = 64) ∧
      ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).b.size = (((Obj.codes B #v[x])[0]'Nat.zero_lt_one).n.toNat * ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).w + 7) / 8 ∧
      ((Obj.codes B #v[x])[0]'Nat.zero_lt_one).n = x.1)
    (h63 : (Rel.nub R).n.toNat < 2 ^ 63)
    (hpk : Vals.PickFits A (Rel.nub R).key (ids pT)) (hpv : Vals.PickFits B (Rel.nub R).val (ids pT))
    (hlo : Vals.PickFits A (Vals.pickPart A (Rel.nub R).key pT).2 (ids loT)) :
    (∀ a X, rep (Alg.transpose R) a X → ∀ x, x ∈ X ↔ rep R a x) ∧
      (∀ a, (∃ X, rep (Alg.transpose R) a X) ↔ ∃ b, rep R a b) := by
  have hd := rep_nub R hK hV hk hv
  have hdh : ∀ a b, (Rel.nub R).Holds a b ↔ R.Holds a b := fun a b => by
    show rep (Rel.nub R) a b ↔ rep R a b
    rw [hd]
  obtain ⟨hrow, hcov⟩ := transpose_rows R hF hw hn hs hW h63 hpk hpv hlo
  refine ⟨fun a X h x => ?_, fun a => ⟨fun ⟨X, h⟩ => ?_, fun ⟨b, hb⟩ => ?_⟩⟩
  · obtain ⟨q, hqa, hqX⟩ : (Alg.transpose R).Holds a X := h
    obtain ⟨i, hki, hmem⟩ := hrow q
    subst hqa hqX
    rw [hmem x, hki]
    exact hdh _ _
  · obtain ⟨q, hqa, -⟩ : (Alg.transpose R).Holds a X := h
    obtain ⟨i, hki, -⟩ := hrow q
    exact ⟨_, (hdh _ _).1 ⟨i, hki.symm.trans hqa, rfl⟩⟩
  · obtain ⟨i, hia, -⟩ := (hdh a b).2 hb
    obtain ⟨q, hq⟩ := hcov i
    exact ⟨_, q, hq.trans hia, rfl⟩

#print axioms rep_transpose

end LeetQ.Rel.Rep
