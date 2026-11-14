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

/-- **An atom side fits at the left rows of a join's pairs**: each is a row of that side (`join_pairs_lt`),
    so no pick misses. At an array or a sum side the pairs repeat rows and the copied windows can outgrow the
    input, so there the fit stays a hypothesis. -/
theorem pickFits_atom_fst {t : QAtomicType} {n : USize} (x : Vals (.atom t) n) {b : Nat}
    {P : Nat → Nat → Bool} :
    Vals.PickFits (.atom t) x (((List.range n.toNat).flatMap fun i => ((List.range b).filter (P i)).map (i, ·)).map
      Prod.fst) :=
  pickFits_atom x fun _ hk => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hk
    exact (join_pairs_lt hp).1

/-- **An atom side fits at the right rows of a join's pairs**, as `pickFits_atom_fst`. -/
theorem pickFits_atom_snd {t : QAtomicType} {n : USize} (x : Vals (.atom t) n) {a : Nat}
    {P : Nat → Nat → Bool} :
    Vals.PickFits (.atom t) x (((List.range a).flatMap fun i => ((List.range n.toNat).filter (P i)).map (i, ·)).map
      Prod.snd) :=
  pickFits_atom x fun _ hk => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hk
    exact (join_pairs_lt hp).2

/-- The left rows of a join's pairs: row `k` at most `b` times, and only below `a`. -/
theorem join_fst_count {b : Nat} {P : Nat → Nat → Bool} : ∀ (a k : Nat),
    (((List.range a).flatMap fun i => ((List.range b).filter (P i)).map (i, ·)).map Prod.fst).count k ≤
      if k < a then b else 0
  | 0, k => by simp
  | a + 1, k => by
    have ih := join_fst_count (b := b) (P := P) a k
    rw [List.range_succ, List.flatMap_append, List.map_append, List.count_append]
    have e : ((([a].flatMap fun i => ((List.range b).filter (P i)).map (i, ·))).map Prod.fst) =
        List.replicate ((List.range b).filter (P a)).length a := by
      rw [List.eq_replicate_iff]; simp <;> intros <;> omega
    have hb : ((List.range b).filter (P a)).length ≤ b := by simpa using List.length_filter_le (P a) (List.range b)
    rw [e, List.count_replicate]
    split at ih <;> split <;> (try split) <;> simp_all <;> omega

/-- The right rows of a join's pairs: row `k` at most `a` times, and only below `b`. -/
theorem join_snd_count {b : Nat} {P : Nat → Nat → Bool} : ∀ (a k : Nat),
    (((List.range a).flatMap fun i => ((List.range b).filter (P i)).map (i, ·)).map Prod.snd).count k ≤
      if k < b then a else 0
  | 0, k => by simp
  | a + 1, k => by
    have ih := join_snd_count (b := b) (P := P) a k
    rw [List.range_succ, List.flatMap_append, List.map_append, List.count_append]
    have e : ((([a].flatMap fun i => ((List.range b).filter (P i)).map (i, ·))).map Prod.snd) =
        (List.range b).filter (P a) := by simp [Function.comp_def]
    have hc := (List.filter_sublist (p := P a) (l := List.range b)).count_le k
    rw [e]; rw [List.count_range] at hc
    split at ih <;> split at hc <;> split <;> omega

/-- **A side fits at the left rows of a join's pairs when its reading at all rows, `b + 1` times, is below `2^63`
    and `USize.size`**: each row repeats at most `b` times (`join_fst_count`, `reads_count_le`,
    `pickFits_of_reads`). The `+ 1` pays the side's dictionary when no pair matches. -/
theorem pickFits_join_fst {X : Obj} {n : USize} (x : Vals X n) {b : Nat} {P : Nat → Nat → Bool}
    (h63 : (b + 1) * Vals.reads X x (List.range n.toNat) < 2 ^ 63)
    (hU : (b + 1) * Vals.reads X x (List.range n.toNat) < USize.size) :
    Vals.PickFits X x (((List.range n.toNat).flatMap fun i => ((List.range b).filter (P i)).map (i, ·)).map
      Prod.fst) := by
  suffices hle : Vals.reads X x _ ≤ (b + 1) * Vals.reads X x (List.range n.toNat) from
    pickFits_of_reads (Nat.lt_of_le_of_lt hle h63) (Nat.lt_of_le_of_lt hle hU)
  exact reads_count_le x (Nat.succ_pos _) fun k hk => by
    have h := join_fst_count (b := b) (P := P) n.toNat k
    have hp := List.count_pos_iff.2 hk
    split at h <;> constructor <;> omega

/-- **A side fits at the right rows of a join's pairs**, as `pickFits_join_fst` with `a + 1` readings
    (`join_snd_count`). -/
theorem pickFits_join_snd {X : Obj} {n : USize} (x : Vals X n) {a : Nat} {P : Nat → Nat → Bool}
    (h63 : (a + 1) * Vals.reads X x (List.range n.toNat) < 2 ^ 63)
    (hU : (a + 1) * Vals.reads X x (List.range n.toNat) < USize.size) :
    Vals.PickFits X x (((List.range a).flatMap fun i => ((List.range n.toNat).filter (P i)).map (i, ·)).map
      Prod.snd) := by
  suffices hle : Vals.reads X x _ ≤ (a + 1) * Vals.reads X x (List.range n.toNat) from
    pickFits_of_reads (Nat.lt_of_le_of_lt hle h63) (Nat.lt_of_le_of_lt hle hU)
  exact reads_count_le x (Nat.succ_pos _) fun k hk => by
    have h := join_snd_count (b := n.toNat) (P := P) a k
    have hp := List.count_pos_iff.2 hk
    split at h <;> constructor <;> omega

section Comp

open Freyd Freyd.Alg.RelSet

/-- **`rep (R ≫ S) = rep R ≫ rep S`.** Hypotheses:
    - `hc`, the middle side's joint codes identify rows and are well formed — what `CodesSpec` concludes;
    - `hrn`, `hM`, the counts `join_spec` takes: `S`'s rows below `2^63`, and `R`'s rows times `S`'s below
      `2^63` and a `USize`, which bounds the match count (past a `USize` `≫` answers `𝟘`);
    - `hA`, `hC`, `Vals.PickFits` of `R.key` at the left rows of the join's pairs and of `S.val` at the
      right ones, which `pick_row` reads back under; a side of atoms and products fits outright
      (`pickFits_atom_fst`, `pickFits_atom_snd`, `pickFits_prod`).
    At a middle side `B` with `B.CodesFit jcs`, `hc` is `(codes_faithful_wf B jcs _).1`. -/
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
    (hM : R.n.toNat * S.n.toNat < min (2 ^ 63) USize.size)
    (hA : Vals.PickFits A R.key ((jpairs).map Prod.fst)) (hC : Vals.PickFits C S.val ((jpairs).map Prod.snd)) :
    rep (R ≫ S) = rep R ≫ rep S := by
  obtain ⟨hF, hW⟩ := hc
  obtain ⟨hlw, hln, hls, -⟩ := hW (k := 0) (by decide)
  obtain ⟨hrw, hrn', hrs, hrc⟩ := hW (k := 1) (by decide)
  replace hln : (jc[0]'Nat.zero_lt_two).n = R.n := hln
  replace hrn' : (jc[1]'Nat.one_lt_two).n = S.n := hrn'
  obtain ⟨hlt, hZ⟩ := join_rows _ _ hlw hls hrw hrs hrc (by rw [hrn']; exact hrn) (by rw [hln, hrn']; exact hM)
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

/-- **`R ≫ S` fits at all its rows, and counts at most `R`'s rows times `S`'s**, under `rep_comp`'s hypotheses: each
    side is an input column picked at the join's pairs (`pickFits_pick`), as many as the pairs (`join_rows`,
    `range_filter_sum_le`). `hA`, `hC` follow from the inputs' readings (`pickFits_join_fst`, `pickFits_join_snd`). -/
theorem comp_fits (R : Rel A B) (S : Rel B C)
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
    (hM : R.n.toNat * S.n.toNat < min (2 ^ 63) USize.size)
    (hA : Vals.PickFits A R.key ((jpairs).map Prod.fst)) (hC : Vals.PickFits C S.val ((jpairs).map Prod.snd)) :
    Vals.PickFits A (R ≫ S).key (List.range (R ≫ S).n.toNat) ∧ Vals.PickFits C (R ≫ S).val (List.range (R ≫ S).n.toNat) ∧
      (R ≫ S).n.toNat ≤ R.n.toNat * S.n.toNat := by
  obtain ⟨-, hW⟩ := hc
  obtain ⟨hlw, hln, hls, -⟩ := hW (k := 0) (by decide)
  obtain ⟨hrw, hrn', hrs, hrc⟩ := hW (k := 1) (by decide)
  replace hln : (jc[0]'Nat.zero_lt_two).n = R.n := hln
  replace hrn' : (jc[1]'Nat.one_lt_two).n = S.n := hrn'
  obtain ⟨hlt, hZ⟩ := join_rows _ _ hlw hls hrw hrs hrc (by rw [hrn']; exact hrn) (by rw [hln, hrn']; exact hM)
  have hlen : (jpairs).length ≤ R.n.toNat * S.n.toNat := by
    rw [List.length_flatMap]; simp only [List.length_map]; exact range_filter_sum_le _ _ _
  have H : ∀ (m : USize) (hmJ : len (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).2 = m.toNat),
      Vals.PickFits A (Vals.pickN A R.key (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).1 m
        (hmJ ▸ join_len (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two))) (List.range m.toNat) ∧
      Vals.PickFits C (Vals.pick C S.val (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).2 m hmJ)
        (List.range m.toNat) ∧ m.toNat ≤ R.n.toNat * S.n.toNat := by
    intro m hmJ
    have e := hZ m hmJ
    rw [hln, hrn'] at e
    have hl : ((List.range m.toNat).map fun q =>
        (Column.bitsAt (fit m.toNat (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).1) (q * 8) 8).toNat) =
          (jpairs).map Prod.fst := by rw [e, List.map_map]; rfl
    have hr : ((List.range m.toNat).map fun q =>
        (Column.bitsAt (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).2 (q * 8) 8).toNat) =
          (jpairs).map Prod.snd := by rw [e, List.map_map]; rfl
    have hq : ∀ q ∈ List.range m.toNat, q < m.toNat := fun q hq => List.mem_range.1 hq
    have hm := congrArg List.length e
    simp only [List.length_map, List.length_range] at hm
    unfold Vals.pickN
    exact ⟨pickFits_pick A R.key _ m _ _ hq (hl ▸ hA) (hl ▸ hA), pickFits_pick C S.val _ m hmJ _ hq (hr ▸ hC) (hr ▸ hC),
      by omega⟩
  rw [show R ≫ S = longCount "≫" (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).2 (fun m h =>
      (⟨m, Vals.pickN A R.key (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).1 m (h ▸ join_len (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)),
        Vals.pick C S.val (join (jc[0]'Nat.zero_lt_two) (jc[1]'Nat.one_lt_two)).2 m h⟩ : Rel A C)) from rfl]
  unfold longCount need
  rw [dif_pos hlt]
  dsimp only
  exact H _ _

#print axioms comp_fits

end Comp

#print axioms pick_row_atom
#print axioms pick_row_prod
#print axioms rep_comp

end LeetQ.Rel.Rep
