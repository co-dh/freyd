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

/-- A long column cast to the count `M` it holds reads back its payload's longs. -/
theorem longCol_cast_get {b : ByteArray} {M : USize} (hb : len b < USize.size) (e : (len b).toUSize = M)
    (q : Fin M.toNat) : (e ▸ longCol b : Arr .long M).get q = (Column.bitsAt b (q.1 * 8) 8).toInt64 := by
  have hq : q.1 < len b := by
    have := q.2; rw [← e, USize.toNat_ofNat_of_lt' hb] at this; exact this
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
local notation "kcT" => (Obj.codes A (#v[⟨(Rel.nub R).n, (Rel.nub R).key⟩] : Vector (Part A) 1))[0]
set_option hygiene false in
local notation "vpT" => Obj.sortBy B (Rel.nub R).val (tilLongs (Rel.nub R).n)
set_option hygiene false in
local notation "pT" => gather 8 vpT (Code.gather kcT vpT).grade
set_option hygiene false in
local notation "oT" => Code.runStarts (Code.gather kcT pT)
set_option hygiene false in
local notation "loT" => oT.extract 0 (oT.size - 8)

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
    (hW : ∀ (B : Obj) (x : Part B), (((Obj.codes B #v[x])[0]).w = 1 ∨ ((Obj.codes B #v[x])[0]).w = 2 ∨
      ((Obj.codes B #v[x])[0]).w = 4 ∨ ((Obj.codes B #v[x])[0]).w = 8 ∨ ((Obj.codes B #v[x])[0]).w = 16 ∨
      ((Obj.codes B #v[x])[0]).w = 32 ∨ ((Obj.codes B #v[x])[0]).w = 64) ∧
      ((Obj.codes B #v[x])[0]).b.size = (((Obj.codes B #v[x])[0]).n.toNat * ((Obj.codes B #v[x])[0]).w + 7) / 8 ∧
      ((Obj.codes B #v[x])[0]).n = x.1)
    (h63 : (Rel.nub R).n.toNat < 2 ^ 63)
    (hpk : Vals.PickFits A (Rel.nub R).key (ids pT)) (hpv : Vals.PickFits B (Rel.nub R).val (ids pT))
    (hlo : Vals.PickFits A (Vals.pickPart A (Rel.nub R).key pT).2 (ids loT)) :
    (∀ q : Fin (transpose R).n.toNat, ∃ i : Fin (Rel.nub R).n.toNat,
      Vals.row (transpose R).key q = Vals.row (Rel.nub R).key i ∧ ∀ x, x ∈ Vals.row (transpose R).val q ↔
        ∃ i' : Fin (Rel.nub R).n.toNat, Vals.row (Rel.nub R).key i' = Vals.row (Rel.nub R).key i ∧
          Vals.row (Rel.nub R).val i' = x) ∧
    ∀ i : Fin (Rel.nub R).n.toNat, ∃ q : Fin (transpose R).n.toNat,
      Vals.row (transpose R).key q = Vals.row (Rel.nub R).key i := by
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
  have hsurj : ∀ i < (Rel.nub R).n.toNat, ∃ s, s < len pT ∧ (Column.bitsAt pT (s * 8) 8).toNat = i := fun i hi => by
    obtain ⟨s, hs', e⟩ := List.getElem_of_mem (hpp.mem_iff.2 (List.mem_range.2 (by rw [hN]; exact hi)))
    exact ⟨s, by rw [len_eq_ids]; exact hs', by rw [← ids_getElem hs']; exact e⟩
  have hcb : 8 ≤ (kcT).w → 8 * (kcT).b.size = (kcT).w * (kcT).n.toNat := fun h8 => by
    rcases hw with h | h | h | h | h | h | h <;> rw [h] at hs ⊢ <;> omega
  obtain ⟨hGw, hGn, -, hGid⟩ := gather_spec (kcT) pT hpl hw hcb hpi
  have hGs := gather_size (kcT) pT hpl hw
  -- the runs of `G = kc@p`: `r j`, each key one run
  obtain ⟨m, hosz, hlast, hasc, -, hrun, hcov⟩ := code_runs (Code.gather (kcT) pT) (by rw [hGw]; exact hw)
    (by rw [hGs, hGn, hGw])
    (fun s t u h1 h2 hu e => by
      rw [hGn, hlp, ← hN] at hu
      rw [hGw] at e ⊢
      rw [hGid s (by rw [hlp, ← hN]; omega), hGid u (by rw [hlp, ← hN]; omega)] at e
      rw [hGid t (by rw [hlp, ← hN]; omega), hGid s (by rw [hlp, ← hN]; omega)]
      exact hgrp s t u h1 h2 hu e)
  rw [hGn, hlp] at hlast hrun hcov
  rw [hGw] at hrun
  generalize hO : Code.runStarts (Code.gather (kcT) pT) = o at hosz hlast hasc hrun hcov hlo
  -- `r j` below the count for `j < m`, and the starts read back through `lo` and `hi`
  have hrlt : ∀ j, j < m → (Column.bitsAt o (j * 8) 8).toNat < (Rel.nub R).n.toNat := fun j hj => by
    have := hasc j m hj (Nat.le_refl m); omega
  have hlolen : len (o.extract 0 (o.size - 8)) = m := by simp only [len, ByteArray.size_extract]; omega
  have hloU : len (o.extract 0 (o.size - 8)) < USize.size := by rw [hlolen]; have := hrlt; omega
  have hlo_at : ∀ j, j < m → Column.bitsAt (o.extract 0 (o.size - 8)) (j * 8) 8 = Column.bitsAt o (j * 8) 8 :=
    fun j hj => by rw [bitsAt_extract _ (by omega), Nat.zero_add]
  have hhi_at : ∀ j, j < m → Column.bitsAt (o.extract 8 o.size) (j * 8) 8 = Column.bitsAt o ((j + 1) * 8) 8 :=
    fun j hj => by rw [bitsAt_extract _ (by omega), show 8 + j * 8 = (j + 1) * 8 by omega]
  have hhilen : len (o.extract 8 o.size) = len (o.extract 0 (o.size - 8)) := by
    simp only [len, ByteArray.size_extract]; omega
  -- `transpose R` itself, its `longCount` run
  have hpkd : Vals.pickPart A (Rel.nub R).key pT =
      ⟨(len pT).toUSize, Vals.pick A (Rel.nub R).key pT _ (USize.toNat_ofNat_of_lt' hpl).symm⟩ := by
    unfold Vals.pickPart need; rw [dif_pos hpl]
  have hpvd : Vals.pickPart B (Rel.nub R).val pT =
      ⟨(len pT).toUSize, Vals.pick B (Rel.nub R).val pT _ (USize.toNat_ofNat_of_lt' hpl).symm⟩ := by
    unfold Vals.pickPart need; rw [dif_pos hpl]
  have hT : transpose R = ⟨(len (o.extract 0 (o.size - 8))).toUSize,
      Vals.pick A (Vals.pickPart A (Rel.nub R).key pT).2 (o.extract 0 (o.size - 8)) _
        (USize.toNat_ofNat_of_lt' hloU).symm,
      ⟨(Vals.pickPart B (Rel.nub R).val pT).1,
        toUSize_eq (USize.toNat_ofNat_of_lt' hloU).symm ▸ longCol (o.extract 0 (o.size - 8)),
        toUSize_eq (hhilen.trans (USize.toNat_ofNat_of_lt' hloU).symm) ▸ longCol (o.extract 8 o.size),
        (Vals.pickPart B (Rel.nub R).val pT).2⟩⟩ := by
    unfold transpose; dsimp only; rw [hO]; unfold longCount need; rw [dif_pos hloU]
  rw [hpkd] at hlo
  rw [hT, hpkd, hpvd]
  have hMn : ((len (o.extract 0 (o.size - 8))).toUSize).toNat = m := by
    rw [USize.toNat_ofNat_of_lt' hloU, hlolen]
  have hLn : ((len pT).toUSize).toNat = len pT := USize.toNat_ofNat_of_lt' hpl
  -- `P s`, the row of `d` at position `s` of `p`; the picked columns read back there
  have hkey : ∀ s (h : s < ((len pT).toUSize).toNat),
      Vals.row (Vals.pick A (Rel.nub R).key pT _ (USize.toNat_ofNat_of_lt' hpl).symm) ⟨s, h⟩ =
        Vals.row (Rel.nub R).key ⟨(Column.bitsAt pT (s * 8) 8).toNat, by rw [← hN]; exact hpi s (by omega)⟩ :=
    fun s h => by
      rw [pick_row A _ pT _ _ (by rw [hLn]; exact hpk) ⟨s, h⟩, dif_pos (by rw [← hN]; exact hpi s (by omega))]
  have hval : ∀ s (h : s < ((len pT).toUSize).toNat),
      Vals.row (Vals.pick B (Rel.nub R).val pT _ (USize.toNat_ofNat_of_lt' hpl).symm) ⟨s, h⟩ =
        Vals.row (Rel.nub R).val ⟨(Column.bitsAt pT (s * 8) 8).toNat, by rw [← hN]; exact hpi s (by omega)⟩ :=
    fun s h => by
      rw [pick_row B _ pT _ _ (by rw [hLn]; exact hpv) ⟨s, h⟩, dif_pos (by rw [← hN]; exact hpi s (by omega))]
  -- row `j` of the answer is keyed by `P (r j)`
  have hkrow : ∀ j (h : j < ((len (o.extract 0 (o.size - 8))).toUSize).toNat),
      Vals.row (Vals.pick A (Vals.pick A (Rel.nub R).key pT _ (USize.toNat_ofNat_of_lt' hpl).symm)
        (o.extract 0 (o.size - 8)) _ (USize.toNat_ofNat_of_lt' hloU).symm) ⟨j, h⟩ =
      Vals.row (Rel.nub R).key ⟨(Column.bitsAt pT ((Column.bitsAt o (j * 8) 8).toNat * 8) 8).toNat,
        by rw [← hN]; exact hpi _ (by rw [hlp]; exact hrlt j (by omega))⟩ := fun j h => by
    have hj : j < m := by omega
    rw [pick_row A _ _ _ _ (by rw [hMn]; rw [hlolen] at hlo; exact hlo) ⟨j, h⟩,
      dif_pos (by rw [hlo_at j hj, hLn, hlp]; exact hrlt j hj)]
    simp only [hlo_at j hj]
    exact hkey _ _
  -- the key codes along `p` are the keys of `d`
  have hcode : ∀ s t, s < len pT → t < len pT →
      (Column.idAt (Code.gather (kcT) pT).b (kcT).w s = Column.idAt (Code.gather (kcT) pT).b (kcT).w t ↔
        Vals.row (Rel.nub R).key ⟨(Column.bitsAt pT (s * 8) 8).toNat, by rw [← hN]; exact hpi s (by omega)⟩ =
          Vals.row (Rel.nub R).key ⟨(Column.bitsAt pT (t * 8) 8).toNat, by rw [← hN]; exact hpi t (by omega)⟩) :=
    fun s t hs' ht => by rw [hGid s hs', hGid t ht]; exact hF _ _
  refine ⟨fun q => ?_, fun i => ?_⟩
  · have hq : q.1 < m := by have := q.2; omega
    refine ⟨_, hkrow q.1 q.2, fun x => ?_⟩
    rw [mem_arr_row]
    have hlo' : ((toUSize_eq (USize.toNat_ofNat_of_lt' hloU).symm ▸ longCol (o.extract 0 (o.size - 8)) :
        Arr .long _).get q).toInt = ((Column.bitsAt o (q.1 * 8) 8).toNat : Int) := by
      rw [longCol_cast_get hloU, hlo_at q.1 hq, toInt_toInt64, if_pos (by have := hrlt q.1 hq; omega)]
    have hhi' : ((toUSize_eq (hhilen.trans (USize.toNat_ofNat_of_lt' hloU).symm) ▸
        longCol (o.extract 8 o.size) : Arr .long _).get q).toInt =
          ((Column.bitsAt o ((q.1 + 1) * 8) 8).toNat : Int) := by
      rw [longCol_cast_get (by rw [hhilen]; exact hloU), hhi_at q.1 hq, toInt_toInt64,
        if_pos (by have := hasc (q.1 + 1) m (by omega) (by omega); omega)]
      have := hasc q.1 (q.1 + 1) (by omega) (by omega); omega
    rw [hlo', hhi']
    constructor
    · rintro ⟨s, h1, h2, hs'⟩
      have hsl : s.1 < len pT := by rw [hlp]; have := hasc (q.1 + 1) m (by omega) (by omega); omega
      refine ⟨_, ?_, (hval s.1 s.2).symm.trans hs'⟩
      exact ((hcode _ _ hsl (by rw [hlp]; exact hrlt q.1 hq)).1
        ((hrun s.1 q.1 (by rw [← hlp]; exact hsl) hq).2 ⟨by omega, by omega⟩))
    · rintro ⟨i', e1, e2⟩
      obtain ⟨s, hs', hsi⟩ := hsurj i'.1 i'.2
      have he : i' = ⟨(Column.bitsAt pT (s * 8) 8).toNat, by rw [← hN]; exact hpi s hs'⟩ := Fin.ext hsi.symm
      subst he
      obtain ⟨h1, h2⟩ := (hrun s q.1 (by rw [← hlp]; exact hs') hq).1
        ((hcode _ _ hs' (by rw [hlp]; exact hrlt q.1 hq)).2 e1)
      exact ⟨⟨s, by rw [hLn]; exact hs'⟩, by omega, by omega, (hval s _).trans e2⟩
  · obtain ⟨s, hs', hsi⟩ := hsurj i.1 i.2
    obtain ⟨j, hj, h1, h2⟩ := hcov s (by rw [← hlp]; exact hs')
    refine ⟨⟨j, by rw [hMn]; exact hj⟩, (hkrow j _).trans ?_⟩
    have e := (hcode _ _ (by rw [hlp]; exact hrlt j hj) hs').1
      ((hrun s j (by rw [← hlp]; exact hs') hj).2 ⟨h1, h2⟩).symm
    exact e.trans (congrArg _ (Fin.ext hsi))

#print axioms transpose_rows

end LeetQ.Rel.Rep
