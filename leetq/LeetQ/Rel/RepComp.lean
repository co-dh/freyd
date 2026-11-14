/-
  `rep (R ≫ S) = rep R ≫ rep S`: `≫` joins `R.val` with `S.key` on the middle side's joint codes and picks
  `R.key` and `S.val` at the matched rows. `join_spec` reads the join back; the codes must identify rows
  (`CodesSpec`), the counts must fit, and each outer side's `Vals.pick` must read back.
-/
import LeetQ.Rel.Rep
import LeetQ.Rel.KernelWF.JoinAssembly
import LeetQ.Rel.KernelWF.CodesSpec
import LeetQ.Rel.KernelWF.CodesProd
import LeetQ.Rel.KernelWF.PickRow
import LeetQ.Rel.KernelWF.CodesSymParts

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg

variable {A B C : Obj}

/-! `≫`'s notations, one home: `open CompN` in every file that states a `≫` read-back. -/
namespace CompN
-- the two parts `≫` codes jointly, and their codes, named as `comp` names them
set_option hygiene false in
scoped notation "jcs" => (#v[⟨R.n, R.val⟩, ⟨S.n, S.key⟩] : Vector (Part _) 2)
set_option hygiene false in
scoped notation "jc" => Obj.codes _ jcs
-- the pairs `(i, j)` `join` answers, as `join_spec` reads them back: row `i` of `R`, row `j` of `S`, equal codes
set_option hygiene false in
scoped notation "jpairs" => ((List.range R.n.toNat).flatMap fun i => ((List.range S.n.toNat).filter fun j =>
  Column.idAt (jc[1]'Nat.one_lt_two).b (jc[1]'Nat.one_lt_two).w j ==
    Column.idAt (jc[0]'Nat.zero_lt_two).b (jc[0]'Nat.zero_lt_two).w i).map (i, ·))
end CompN
open CompN

section Comp

open Freyd Freyd.Alg.RelSet

/-- **`rep (R ≫ S) = rep R ≫ rep S`.** Hypotheses:
    - `hc`, the middle side's joint codes identify rows and are well formed — what `CodesSpec` concludes;
    - `hrn`, `hM`, `hMU`, the counts `join_spec` takes: `S`'s rows and the match count below `2^63`, the
      match count a `USize` (past it `≫` answers `𝟘`);
    - `hA`, `hC`, `Vals.PickFits` of `R.key` at the left rows of the join's pairs and of `S.val` at the
      right ones, which `pick_row` reads back under; a side of atoms and products fits outright
      (`pickFits_atom`, `pickFits_prod`, `join_pairs_lt`). -/
theorem rep_comp (R : Rel A B) (S : Rel B C)
    (hc : (∀ {k l : Nat} (hk : k < 2) (hl : l < 2) {i j : Nat} (hi : i < (jcs[k]'hk).1.toNat)
        (hj : j < (jcs[l]'hl).1.toNat),
        Column.idAt (jc[k]'hk).b (jc[k]'hk).w i = Column.idAt (jc[l]'hl).b (jc[l]'hl).w j ↔
          Vals.row (jcs[k]'hk).2 ⟨i, hi⟩ = Vals.row (jcs[l]'hl).2 ⟨j, hj⟩) ∧
      ∀ {k : Nat} (hk : k < 2),
        laneOK((jc[k]'hk).w) ∧
        (jc[k]'hk).n = (jcs[k]'hk).1 ∧ (jc[k]'hk).b.size = ((jc[k]'hk).n.toNat * (jc[k]'hk).w + 7) / 8 ∧
        ((jc[k]'hk).w < 8 → (jc[k]'hk).card < USize.size ∧
          ∀ i < (jc[k]'hk).n.toNat, Column.idAt (jc[k]'hk).b (jc[k]'hk).w i < (jc[k]'hk).card))
    (hrn : S.n.toNat < 2 ^ 63)
    (hM : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt (jc[1]'Nat.one_lt_two).b (jc[1]'Nat.one_lt_two).w j ==
        Column.idAt (jc[0]'Nat.zero_lt_two).b (jc[0]'Nat.zero_lt_two).w i).length).sum < 2 ^ 63)
    (hMU : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt (jc[1]'Nat.one_lt_two).b (jc[1]'Nat.one_lt_two).w j ==
        Column.idAt (jc[0]'Nat.zero_lt_two).b (jc[0]'Nat.zero_lt_two).w i).length).sum < USize.size)
    (hA : Vals.PickFits A R.key ((jpairs).map Prod.fst)) (hC : Vals.PickFits C S.val ((jpairs).map Prod.snd)) :
    rep (R ≫ S) = rep R ≫ rep S := by
  obtain ⟨hF, hW⟩ := hc
  obtain ⟨hlw, hln, hls, -⟩ := hW (k := 0) (by decide)
  obtain ⟨hrw, hrn', hrs, hrc⟩ := hW (k := 1) (by decide)
  replace hln : (jc[0]'Nat.zero_lt_two).n = R.n := hln
  replace hrn' : (jc[1]'Nat.one_lt_two).n = S.n := hrn'
  obtain ⟨hlt, hZ⟩ := join_rows _ _ hlw hls hrw hrs hrc (by rw [hrn']; exact hrn) (by rw [hln, hrn']; exact hM)
    (by rw [hln, hrn']; exact hMU)
  have hP := mem_joinPairs (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)
  rw [hln, hrn'] at hP
  refine hom_ext fun a c => ?_
  show (longCount "≫" (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).2 fun m h =>
      (⟨m, Vals.pickN A R.key (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).1 m (h ▸ join_len (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)),
        Vals.pick C S.val (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).2 m h⟩ : Rel A C)).Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c
  unfold longCount need
  rw [dif_pos hlt]
  -- the relation at whatever count `m` the join's length enters as
  suffices H : ∀ (m : USize) (hmJ : len (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).2 = m.toNat),
      (⟨m, Vals.pickN A R.key (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).1 m (hmJ ▸ join_len (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)),
        Vals.pick C S.val (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).2 m hmJ⟩ : Rel A C).Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c from H _ _
  intro m hmJ
  have e := hZ m hmJ
  rw [hln, hrn'] at e
  have hfA : Vals.PickFits A R.key
      ((List.range m.toNat).map fun q => (Column.bitsAt (fit m.toNat (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).1) (q * 8) 8).toNat) := by
    rw [show ((List.range m.toNat).map fun q => (Column.bitsAt (fit m.toNat (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).1) (q * 8) 8).toNat) =
      (jpairs).map Prod.fst by rw [e, List.map_map]; rfl]; exact hA
  have hfC : Vals.PickFits C S.val
      ((List.range m.toNat).map fun q => (Column.bitsAt (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).2 (q * 8) 8).toNat) := by
    rw [show ((List.range m.toNat).map fun q => (Column.bitsAt (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).2 (q * 8) 8).toNat) =
      (jpairs).map Prod.snd by rw [e, List.map_map]; rfl]; exact hC
  have hA' : ∀ (h : m.toNat ≤ len (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).1) (q : Fin m.toNat)
      (hin : (Column.bitsAt (fit m.toNat (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).1) (q.1 * 8) 8).toNat < R.n.toNat),
      (Vals.pickN A R.key (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).1 m h).row q = R.key.row ⟨_, hin⟩ :=
    fun h q hin => by unfold Vals.pickN; rw [pick_row A R.key _ m _ hfA q, dif_pos hin]
  simp only [Rel.Holds]
  constructor
  · rintro ⟨q, hqa, hqc⟩
    have hq : ((Column.bitsAt (fit m.toNat (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).1) (q.1 * 8) 8).toNat,
        (Column.bitsAt (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).2 (q.1 * 8) 8).toNat) ∈ jpairs := by
      rw [e]; exact List.mem_map.2 ⟨q.1, List.mem_range.2 q.2, rfl⟩
    obtain ⟨hi, hj, he⟩ := (hP _ _).1 hq
    rw [hA' _ q hi] at hqa
    rw [pick_row C S.val _ m hmJ hfC q, dif_pos hj] at hqc
    exact ⟨R.val.row ⟨_, hi⟩, ⟨⟨_, hi⟩, hqa, rfl⟩, ⟨_, hj⟩,
      ((hF (k := 0) (l := 1) (by decide) (by decide) hi hj).1 he.symm).symm, hqc⟩
  · rintro ⟨b, ⟨i, hia, hib⟩, ⟨j, hjb, hjc⟩⟩
    have he : Column.idAt (jc[1]'Nat.one_lt_two).b (jc[1]'Nat.one_lt_two).w j.1 =
        Column.idAt (jc[0]'Nat.zero_lt_two).b (jc[0]'Nat.zero_lt_two).w i.1 :=
      ((hF (k := 0) (l := 1) (by decide) (by decide) i.2 j.2).2 (hib.trans hjb.symm)).symm
    have hm := (hP i.1 j.1).2 ⟨i.2, j.2, he⟩
    rw [e] at hm
    obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hm
    obtain ⟨h1, h2⟩ := Prod.mk.inj hqe
    have hq2 := List.mem_range.1 hq
    have hi' : (Column.bitsAt (fit m.toNat (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).1) (q * 8) 8).toNat < R.n.toNat := by rw [h1]; exact i.2
    have hj' : (Column.bitsAt (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).2 (q * 8) 8).toNat < S.n.toNat := by rw [h2]; exact j.2
    refine ⟨⟨q, hq2⟩, ?_, ?_⟩
    · rw [hA' _ ⟨q, hq2⟩ hi', ← hia]; exact congrArg R.key.row (Fin.ext h1)
    · rw [pick_row C S.val _ m hmJ hfC ⟨q, hq2⟩, dif_pos hj', ← hjc]; exact congrArg S.val.row (Fin.ext h2)

/-- `rep_comp` through a boolean middle side: its codes are its bits (`codes_boolean_faithful`/`_wf`). -/
theorem rep_comp_boolean (R : Rel A (.atom .boolean)) (S : Rel (.atom .boolean) C)
    (hrn : S.n.toNat < 2 ^ 63)
    (hM : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt (jc[1]'Nat.one_lt_two).b (jc[1]'Nat.one_lt_two).w j ==
        Column.idAt (jc[0]'Nat.zero_lt_two).b (jc[0]'Nat.zero_lt_two).w i).length).sum < 2 ^ 63)
    (hMU : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt (jc[1]'Nat.one_lt_two).b (jc[1]'Nat.one_lt_two).w j ==
        Column.idAt (jc[0]'Nat.zero_lt_two).b (jc[0]'Nat.zero_lt_two).w i).length).sum < USize.size)
    (hA : Vals.PickFits A R.key ((jpairs).map Prod.fst)) (hC : Vals.PickFits C S.val ((jpairs).map Prod.snd)) :
    rep (R ≫ S) = rep R ≫ rep S :=
  rep_comp R S ⟨fun {_ _} hk hl {_ _} hi hj => codes_boolean_faithful _ hk hl hi hj,
    fun hk => have h := codes_boolean_wf _ hk; ⟨Or.inl h.2.1, h.1, h.2.2.1, h.2.2.2⟩⟩ hrn hM hMU hA hC

/-- `rep_comp` through a long-ordered middle side where `rangeOffsets` answers
    (`codes_long_faithful`/`_wf`, under their hypothesis `hro`). -/
theorem rep_comp_long {t : QAtomicType} (ht : orderKind t = some .i64) (R : Rel A (.atom t)) (S : Rel (.atom t) C)
    {os : Vector Code 2}
    (hro : rangeOffsets t ((jcs).map fun c => Arr.part c.2) (((jcs).map (·.1)).foldl (fun s n => s + n.toNat) 0) = some os)
    (hrn : S.n.toNat < 2 ^ 63)
    (hM : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt (jc[1]'Nat.one_lt_two).b (jc[1]'Nat.one_lt_two).w j ==
        Column.idAt (jc[0]'Nat.zero_lt_two).b (jc[0]'Nat.zero_lt_two).w i).length).sum < 2 ^ 63)
    (hMU : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt (jc[1]'Nat.one_lt_two).b (jc[1]'Nat.one_lt_two).w j ==
        Column.idAt (jc[0]'Nat.zero_lt_two).b (jc[0]'Nat.zero_lt_two).w i).length).sum < USize.size)
    (hA : Vals.PickFits A R.key ((jpairs).map Prod.fst)) (hC : Vals.PickFits C S.val ((jpairs).map Prod.snd)) :
    rep (R ≫ S) = rep R ≫ rep S :=
  rep_comp R S ⟨fun {_ _} hk hl {_ _} hi hj => codes_long_faithful ht _ hro hk hl hi hj,
    fun hk => codes_long_wf ht _ hro hk⟩ hrn hM hMU hA hC

end Comp

#print axioms pick_row_atom
#print axioms pick_row_prod
#print axioms rep_comp
#print axioms rep_comp_boolean
#print axioms rep_comp_long

section CompSymbol

open Freyd Freyd.Alg.RelSet

/-- `rep_comp` through a `symbol` middle side, the two counts and the two parts' dictionary counts (an interned
    part counting its dictionary, a blob its rows) each summing below a `USize`
    (`codes_symbol_parts_faithful`/`_wf`). -/
theorem rep_comp_symbol (R : Rel A (.atom .symbol)) (S : Rel (.atom .symbol) C)
    (hN : R.n.toNat + S.n.toNat < USize.size)
    (hD : ((jcs).toList.map fun c => match c.2.enc with | .enum _ o _ => o.size - 1 | _ => c.1.toNat).sum <
      USize.size)
    (hrn : S.n.toNat < 2 ^ 63)
    (hM : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt (jc[1]'Nat.one_lt_two).b (jc[1]'Nat.one_lt_two).w j ==
        Column.idAt (jc[0]'Nat.zero_lt_two).b (jc[0]'Nat.zero_lt_two).w i).length).sum < 2 ^ 63)
    (hMU : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt (jc[1]'Nat.one_lt_two).b (jc[1]'Nat.one_lt_two).w j ==
        Column.idAt (jc[0]'Nat.zero_lt_two).b (jc[0]'Nat.zero_lt_two).w i).length).sum < USize.size)
    (hA : Vals.PickFits A R.key ((jpairs).map Prod.fst)) (hC : Vals.PickFits C S.val ((jpairs).map Prod.snd)) :
    rep (R ≫ S) = rep R ≫ rep S :=
  have hN' : ((jcs).toList.map (·.1.toNat)).sum < USize.size := by simpa using hN
  rep_comp R S ⟨fun {_ _} hk hl {_ _} hi hj => codes_symbol_parts_faithful _ hN' hD hk hl hi hj,
    fun hk => codes_symbol_parts_wf _ hN' hk⟩ hrn hM hMU hA hC

end CompSymbol

#print axioms rep_comp_symbol

end LeetQ.Rel.Rep
