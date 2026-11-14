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

/-- An array row is, as a list, the payload's values at the positions between the row's `lo` and `hi`, in order. -/
theorem arr_row_eq {b : Obj} {n K : USize} (lo hi : Arr .long n) (f : Vals b K) (q : Fin n.toNat) :
    Vals.row (A := .arr b) ⟨K, lo, hi, f⟩ q = ((List.finRange K.toNat).filter fun s =>
      decide ((lo.get q).toInt ≤ (s.1 : Int) ∧ (s.1 : Int) < (hi.get q).toInt)).map (Vals.row f) := by
  show List.filterMap _ _ = _
  generalize List.finRange K.toNat = l
  induction l with
  | nil => rfl
  | cons s l ih =>
    by_cases h : (lo.get q).toInt ≤ (s.1 : Int) ∧ (s.1 : Int) < (hi.get q).toInt
    · rw [List.filterMap_cons, if_pos h]; dsimp only
      simp only [List.filter_cons, decide_eq_true h, ↓reduceIte, List.map_cons, ih]
    · rw [List.filterMap_cons, if_neg h]; dsimp only
      simp only [List.filter_cons, decide_eq_false h, Bool.false_eq_true, ↓reduceIte, ih]

/-- Two positions of a list without repeats holding one element are one position. -/
theorem nodup_getElem_inj {α : Type _} {l : List α} (h : l.Nodup) {i j : Nat} (hi : i < l.length)
    (hj : j < l.length) (e : l[i] = l[j]) : i = j := by
  have p := List.pairwise_iff_getElem.1 h
  rcases Nat.lt_trichotomy i j with c | c | c
  · exact absurd e (p i j hi hj c)
  · exact c
  · exact absurd e.symm (p j i hj hi c)

/-- `finRange n` ascends. -/
theorem finRange_pairwise_lt (n : Nat) : (List.finRange n).Pairwise (· < ·) :=
  List.pairwise_iff_getElem.2 fun i j hi hj c => by
    rw [List.getElem_finRange, List.getElem_finRange, Fin.lt_def]; simp only [Fin.val_cast]; exact c

/-- An ascending list of naturals below `n` is a sublist of `range n`. -/
theorem sublist_range {l : List Nat} {n : Nat} (h : l.Pairwise (· < ·)) (hl : ∀ x ∈ l, x < n) :
    l.Sublist (List.range n) := by
  rw [List.range_eq_range']
  suffices H : ∀ k lo (l : List Nat), l.Pairwise (· < ·) → (∀ x ∈ l, lo ≤ x ∧ x < lo + k) →
      l.Sublist (List.range' lo k) from
    H n 0 l h fun x hx => ⟨Nat.zero_le _, by have := hl x hx; omega⟩
  intro k
  induction k with
  | zero =>
    intro lo l _ hl
    cases l with
    | nil => exact List.Sublist.slnil
    | cons x _ => have := hl x (List.mem_cons.2 (Or.inl rfl)); omega
  | succ k ih =>
    intro lo l h hl
    rw [List.range'_succ]
    cases l with
    | nil => exact List.nil_sublist _
    | cons x l =>
      have hx := hl x (List.mem_cons.2 (Or.inl rfl))
      have hgt : ∀ y ∈ l, x < y := fun y hy => List.rel_of_pairwise_cons h hy
      have hlt : ∀ y ∈ l, y < lo + (k + 1) := fun y hy => (hl y (List.mem_cons_of_mem _ hy)).2
      by_cases e : x = lo
      · subst e
        exact (ih (x + 1) l h.of_cons fun y hy => ⟨hgt y hy, by have := hlt y hy; omega⟩).cons₂ x
      · refine (ih (lo + 1) (x :: l) h fun y hy => ?_).cons lo
        rcases List.mem_cons.1 hy with rfl | hy
        · omega
        · have := hgt y hy; have := hlt y hy; omega

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

-- `transpose`'s two casts differ only in `lo` vs `hi`, both extracts of the run starts; telling them apart (dsimp's
-- `Eq.rec` reduction, `rw`'s instance matching) otherwise evaluates `runStarts` and `gather` on the open codes
section
attribute [local irreducible] Code.runStarts Code.gather ByteArray.extract
/-- **`Λ(R)`'s rows, as lists, against `R.nub`**: row `q` is keyed by a key `d.key.row i` of `d = R.nub`, and
    its array IS `d`'s values at a list `L` of rows of `d`, each row once, `L` holding exactly the rows of `d`
    keyed like `i`, in the order `sortBy` lists `d`'s rows (`L` a sublist of `vp`): the run of that key in the
    stable grade of the key codes over the values sorted; every key of `d` keys some row. Hypotheses: the key codes faithful and well formed
    (`rep_nub`'s `hK` at `d`), `sortBy_perm`'s `hW`, `d`'s count below `2⁶³`, and the picks fitting
    (`Vals.PickFits`) at the row order and at the run starts. -/
theorem transpose_row_list (R : Rel A B)
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
      Vals.row (Alg.transpose R).key q = Vals.row (Rel.nub R).key i ∧ ∃ L : List (Fin (Rel.nub R).n.toNat),
        L.Nodup ∧ (∀ i', i' ∈ L ↔ Vals.row (Rel.nub R).key i' = Vals.row (Rel.nub R).key i) ∧
          (L.map Fin.val).Sublist (ids vpT) ∧ Vals.row (Alg.transpose R).val q = L.map (Vals.row (Rel.nub R).val)) ∧
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
  obtain ⟨hpp, hgrp, hgp, hstab⟩ := grade_gather_group (kcT) hw hs vpT hvp
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
    refine ⟨_, hkrow q.1 q.2 hq, ?_⟩
    have hq1 := hrle (q.1 + 1) (by omega)
    have hpn : (ids pT).Nodup := hpp.nodup_iff.2 List.nodup_range
    rw [arr_row_eq, longCol_cast_get hloU rfl, longCol_cast_get hhiU (congrArg Nat.toUSize hhilen),
      hlo_at q.1 hq, hhi_at q.1 hq, toInt_toInt64, toInt_toInt64, if_pos (by have := hrlt q.1 hq; omega),
      if_pos (by omega)]
    -- `S` the positions of row `q`'s run, each one's row of `d` its position under `p`
    rw [List.filter_congr (q := fun s : Fin (Vals.pickPart B (Rel.nub R).val pT).1.toNat =>
      decide ((Column.bitsAt oT (q.1 * 8) 8).toNat ≤ s.1 ∧ s.1 < (Column.bitsAt oT ((q.1 + 1) * 8) 8).toNat))
      (fun s _ => by rw [decide_eq_decide]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, by omega⟩)]
    generalize hS : (List.finRange (Vals.pickPart B (Rel.nub R).val pT).1.toNat).filter (fun s =>
      decide ((Column.bitsAt oT (q.1 * 8) 8).toNat ≤ s.1 ∧ s.1 < (Column.bitsAt oT ((q.1 + 1) * 8) 8).toNat)) = S
    have hSa : S.Pairwise (· < ·) := by rw [← hS]; exact (finRange_pairwise_lt _).filter _
    have hSn : S.Nodup := hSa.imp Fin.ne_of_lt
    have hSm : ∀ s, s ∈ S ↔
        (Column.bitsAt oT (q.1 * 8) 8).toNat ≤ s.1 ∧ s.1 < (Column.bitsAt oT ((q.1 + 1) * 8) 8).toNat := fun s => by
      rw [← hS, List.mem_filter, decide_eq_true_iff]; exact ⟨fun h => h.2, fun h => ⟨List.mem_finRange s, h⟩⟩
    have hsl : ∀ s : Fin (Vals.pickPart B (Rel.nub R).val pT).1.toNat, s.1 < len pT := fun s => by
      have := s.2; omega
    have hsl' : ∀ s : Fin (Vals.pickPart B (Rel.nub R).val pT).1.toNat, s.1 < (ids pT).length := fun s => by
      rw [← len_eq_ids]; exact hsl s
    have hinj : ∀ s s' : Fin (Vals.pickPart B (Rel.nub R).val pT).1.toNat,
        (Column.bitsAt pT (s.1 * 8) 8).toNat = (Column.bitsAt pT (s'.1 * 8) 8).toNat → s = s' := fun s s' e => by
      rw [← ids_getElem (hsl' s), ← ids_getElem (hsl' s')] at e
      exact Fin.ext (nodup_getElem_inj hpn _ _ e)
    refine ⟨S.map fun s => ⟨_, hP s.1 (hsl s)⟩,
      List.Pairwise.map _ (fun s s' h e => h (hinj s s' (by injection e))) hSn, fun i' => ?_, ?_, ?_⟩
    · rw [List.mem_map]
      constructor
      · rintro ⟨s, hs, rfl⟩
        obtain ⟨h1, h2⟩ := (hSm s).1 hs
        exact (hcode _ _ (hsl s) (hrlt q.1 hq)).1 ((hrun s.1 q.1 (hsl s) hq).2 ⟨by omega, by omega⟩)
      · intro e1
        obtain ⟨s, hs', hsi⟩ := hsurj i'.1 i'.2
        have he : i' = ⟨_, hP s hs'⟩ := Fin.ext hsi.symm
        subst he
        obtain ⟨h1, h2⟩ := (hrun s q.1 hs' hq).1 ((hcode _ _ hs' (hrlt q.1 hq)).2 e1)
        exact ⟨⟨s, by rw [hp1B]; exact hs'⟩, (hSm _).2 ⟨by omega, by omega⟩, rfl⟩
    · -- `p`'s long `s` is `vp`'s long `g s`, `g` the grade; along the run `g` ascends (the grade's ties)
      have hgl : (ids (Code.gather (kcT) vpT).grade).length = (Rel.nub R).n.toNat := by
        rw [hgp.length_eq, List.length_range, hN]
      have hvl : (ids vpT).length = (Rel.nub R).n.toNat := by rw [hvp.length_eq, List.length_range, hN]
      have hgs : ∀ s : Fin (Vals.pickPart B (Rel.nub R).val pT).1.toNat,
          s.1 < (ids (Code.gather (kcT) vpT).grade).length := fun s => by rw [hgl, ← hlp]; exact hsl s
      have hgb : ∀ s : Fin (Vals.pickPart B (Rel.nub R).val pT).1.toNat,
          (Column.bitsAt (Code.gather (kcT) vpT).grade (s.1 * 8) 8).toNat < (Rel.nub R).n.toNat := fun s => by
        rw [← ids_getElem (hgs s), ← hN]; exact List.mem_range.1 (hgp.mem_iff.1 (List.getElem_mem (hgs s)))
      have hpg : ∀ s : Fin (Vals.pickPart B (Rel.nub R).val pT).1.toNat, Column.bitsAt pT (s.1 * 8) 8 =
          Column.bitsAt vpT ((Column.bitsAt (Code.gather (kcT) vpT).grade (s.1 * 8) 8).toNat * 8) 8 := fun s =>
        gather8_get (by rw [len_eq_ids]; exact hgs s) (by rw [len_eq_ids, hvl]; exact hgb s)
      have hrq : ∀ s : Fin (Vals.pickPart B (Rel.nub R).val pT).1.toNat, s ∈ S →
          Column.idAt (Code.gather (kcT) pT).b (kcT).w s.1 =
            Column.idAt (Code.gather (kcT) pT).b (kcT).w (Column.bitsAt oT (q.1 * 8) 8).toNat := fun s hs => by
        obtain ⟨h1, h2⟩ := (hSm s).1 hs
        exact (hrun s.1 q.1 (hsl s) hq).2 ⟨by omega, by omega⟩
      have hasc' : (S.map fun s => (Column.bitsAt (Code.gather (kcT) vpT).grade (s.1 * 8) 8).toNat).Pairwise
          (· < ·) := List.pairwise_map.2 (hSa.imp_of_mem fun {s t} hs ht hst => by
        have e := (hrq s hs).trans (hrq t ht).symm
        rw [hGid s.1 (hsl s), hGid t.1 (hsl t), hpg s, hpg t] at e
        have := List.pairwise_iff_getElem.1 hstab s.1 t.1 (hgs s) (hgs t) hst
        rw [ids_getElem, ids_getElem] at this
        exact this e)
      have hr : (List.range (Rel.nub R).n.toNat).map (fun k => (ids vpT)[k]!) = ids vpT :=
        List.ext_getElem (by rw [List.length_map, List.length_range, hvl]) fun k _ h2 => by
          rw [List.getElem_map, List.getElem_range]; exact getElem!_pos (ids vpT) k h2
      have e : ((S.map fun s => (⟨_, hP s.1 (hsl s)⟩ : Fin (Rel.nub R).n.toNat)).map Fin.val) =
          (S.map fun s => (Column.bitsAt (Code.gather (kcT) vpT).grade (s.1 * 8) 8).toNat).map
            fun k => (ids vpT)[k]! := by
        rw [List.map_map, List.map_map]
        refine List.map_congr_left fun s _ => ?_
        show (Column.bitsAt pT (s.1 * 8) 8).toNat = (ids vpT)[_]!
        rw [getElem!_pos (ids vpT) _ (by rw [hvl]; exact hgb s), ids_getElem, hpg s]
      have hsub := (sublist_range hasc' fun k hk => by
        obtain ⟨s, -, rfl⟩ := List.mem_map.1 hk; exact hgb s).map fun k => (ids vpT)[k]!
      rw [hr] at hsub
      rw [e]; exact hsub
    · rw [List.map_map]
      exact List.map_congr_left fun s _ => hval s.1 s.2 (hsl s)
  · obtain ⟨s, hs', hsi⟩ := hsurj i.1 i.2
    obtain ⟨j, hj, h1, h2⟩ := hcov s hs'
    refine ⟨⟨j, by rw [hMn]; exact hj⟩, (hkrow j _ hj).trans ?_⟩
    exact ((hcode _ _ (hrlt j hj) hs').1 ((hrun s j hs' hj).2 ⟨h1, h2⟩).symm).trans (congrArg _ (Fin.ext hsi))
end

#print axioms transpose_row_list

/-- **`Λ(R)`'s rows, read back against `R.nub`**: row `q` is keyed by a key `d.key.row i` of `d = R.nub`, and
    its array holds exactly the values `d` relates that key to; every key of `d` keys some row. The membership
    reading of `transpose_row_list`, under its hypotheses. -/
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
  obtain ⟨h1, h2⟩ := transpose_row_list R hF hw hn hs hW h63 hpk hpv hlo
  refine ⟨fun q => ?_, h2⟩
  obtain ⟨i, hk, L, -, hL, -, hv⟩ := h1 q
  refine ⟨i, hk, fun x => ?_⟩
  rw [hv, List.mem_map]
  exact ⟨fun ⟨i', h, e⟩ => ⟨i', (hL i').1 h, e⟩, fun ⟨i', h, e⟩ => ⟨i', (hL i').2 h, e⟩⟩

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

/-- **`nub R` holds each pair once**: two rows of `R.nub` with one key and one value are one row — each is the
    first occurrence (`nub_mem`) of its pair in `R` (`nub_row`). Hypotheses: `rep_nub`'s. -/
theorem nub_row_inj (R : Rel A B)
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
    (t t' : Fin (Rel.nub R).n.toNat) (ek : Vals.row (Rel.nub R).key t = Vals.row (Rel.nub R).key t')
    (ev : Vals.row (Rel.nub R).val t = Vals.row (Rel.nub R).val t') : t = t' := by
  obtain ⟨hn, hrow⟩ := nub_row R hK hV hk hv
  obtain ⟨hI, hp, e1, e2⟩ := hrow t.1 t.2
  obtain ⟨hI', hp', e1', e2'⟩ := hrow t'.1 t'.2
  have hnd : (ids nubR).Nodup := by rw [nub_ids R hK hV]; exact List.nodup_range.filter _
  have hk' : Vals.row (Rel.key R) ⟨_, hp⟩ = Vals.row (Rel.key R) ⟨_, hp'⟩ := e1.symm.trans (ek.trans e1')
  have hv' : Vals.row (Rel.val R) ⟨_, hp⟩ = Vals.row (Rel.val R) ⟨_, hp'⟩ := e2.symm.trans (ev.trans e2')
  have he : (ids nubR)[t.1]'hI = (ids nubR)[t'.1]'hI' := by
    rcases Nat.lt_trichotomy ((ids nubR)[t.1]'hI) ((ids nubR)[t'.1]'hI') with h | h | h
    · exact absurd ⟨hk', hv'⟩ (((nub_mem R hK hV).1 (List.getElem_mem hI')).2 _ h)
    · exact h
    · exact absurd ⟨hk'.symm, hv'.symm⟩ (((nub_mem R hK hV).1 (List.getElem_mem hI)).2 _ h)
  exact Fin.ext (nodup_getElem_inj hnd hI hI' he)

#print axioms nub_row_inj

/-- **`rep (Λ(R))`, as lists**: the array `Λ(R)` gives a key `a` holds each value `R` relates `a` to, and each
    exactly once, in the order `sortBy` lists the rows of `d = R.nub`: it is the values of the list `L` of `d`'s
    rows keyed `a`, `L` a sublist of `sortBy`'s permutation `vp`; `Λ(R)` has a row at `a` exactly when `R` has a
    pair at `a`. `transpose_row_list` read through `nub_row_inj`. Hypotheses: `rep_transpose`'s. -/
theorem rep_transpose_list (R : Rel A B)
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
    (∀ a X, rep (Alg.transpose R) a X → X.Nodup ∧ (∀ x, x ∈ X ↔ rep R a x) ∧
      ∃ L : List (Fin (Rel.nub R).n.toNat), (L.map Fin.val).Sublist (ids vpT) ∧
        (∀ i, i ∈ L ↔ Vals.row (Rel.nub R).key i = a) ∧ X = L.map (Vals.row (Rel.nub R).val)) ∧
      (∀ a, (∃ X, rep (Alg.transpose R) a X) ↔ ∃ b, rep R a b) := by
  obtain ⟨h1, h2⟩ := rep_transpose R hK hV hk hv hF hw hn hs hW h63 hpk hpv hlo
  refine ⟨fun a X h => ?_, h2⟩
  have hm := h1 a X h
  obtain ⟨q, hqa, hqX⟩ : (Alg.transpose R).Holds a X := h
  obtain ⟨i, hki, L, hnd, hL, hsub, hv'⟩ := (transpose_row_list R hF hw hn hs hW h63 hpk hpv hlo).1 q
  refine ⟨?_, hm, L, hsub, fun i' => by rw [hL i', ← hki, hqa], hqX.symm.trans hv'⟩
  subst hqX
  rw [hv']
  exact List.pairwise_map.2 (hnd.imp_of_mem fun {i' i''} hi' hi'' h e =>
    h (nub_row_inj R hK hV hk hv i' i'' (((hL i').1 hi').trans ((hL i'').1 hi'').symm) e))

#print axioms rep_transpose_list

end LeetQ.Rel.Rep
