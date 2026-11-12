/-
  `rep (R ≫ S) = rep R ≫ rep S`: `≫` joins `R.val` with `S.key` on the middle side's joint codes and picks
  `R.key` and `S.val` at the matched rows. `join_spec` reads the join back; the codes must identify rows
  (`CodesSpec`), the counts must fit, and each outer side's `Vals.pick` must read back.
-/
import LeetQ.Rel.Rep
import LeetQ.Rel.KernelWF.JoinAssembly
import LeetQ.Rel.KernelWF.CodesSpec
import LeetQ.Rel.KernelWF.CodesProd

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg

variable {A B C : Obj}

-- the two parts `≫` codes jointly, and their codes, named as `comp` names them
set_option hygiene false in
local notation "jcs" => (#v[⟨R.n, R.val⟩, ⟨S.n, S.key⟩] : Vector (Part _) 2)
set_option hygiene false in
local notation "jc" => Obj.codes _ jcs

/-- **`Vals.pick` read back at an atom**: `pickArr_get`. -/
theorem pick_row_atom {t : QAtomicType} {n : USize} (x : Vals (.atom t) n)
    (i : ByteArray) (m : USize) (h : len i = m.toNat) (q : Fin m.toNat)
    (hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat) :
    (Vals.pick (.atom t) x i m h).row q = x.row ⟨_, hin⟩ :=
  pickArr_get ⟨_, x⟩ i m h q hin

/-- **`Vals.pick` read back at a product**, from its two components'. -/
theorem pick_row_prod {a b : Obj} {n : USize} (x : Vals (.prod a b) n)
    (h1 : ∀ (i : ByteArray) (m : USize) (h : len i = m.toNat) (q : Fin m.toNat)
      (hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat), (Vals.pick a x.1 i m h).row q = x.1.row ⟨_, hin⟩)
    (h2 : ∀ (i : ByteArray) (m : USize) (h : len i = m.toNat) (q : Fin m.toNat)
      (hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat), (Vals.pick b x.2 i m h).row q = x.2.row ⟨_, hin⟩)
    (i : ByteArray) (m : USize) (h : len i = m.toNat) (q : Fin m.toNat)
    (hin : (Column.bitsAt i (q.1 * 8) 8).toNat < n.toNat) :
    (Vals.pick (.prod a b) x i m h).row q = x.row ⟨_, hin⟩ :=
  Prod.ext (h1 i m h q hin) (h2 i m h q hin)

section Comp

open Freyd Freyd.Alg.RelSet

-- elaborating `≫`'s body against `join`'s statement passes the default budget
set_option maxHeartbeats 800000 in
/-- **`rep (R ≫ S) = rep R ≫ rep S`.** Hypotheses:
    - `hc`, the middle side's joint codes identify rows and are well formed — what `CodesSpec` concludes;
    - `hrn`, `hM`, `hMU`, the counts `join_spec` takes: `S`'s rows and the match count below `2^63`, the
      match count a `USize` (past it `≫` answers `𝟘`);
    - `hA`, `hC`, `Vals.pick` read back on `R.key` and `S.val` (`pick_row_atom`, `pick_row_prod`). -/
theorem rep_comp (R : Rel A B) (S : Rel B C)
    (hc : (∀ {k l : Nat} (hk : k < 2) (hl : l < 2) {i j : Nat} (hi : i < jcs[k].1.toNat)
        (hj : j < jcs[l].1.toNat),
        Column.idAt jc[k].b jc[k].w i = Column.idAt jc[l].b jc[l].w j ↔
          Vals.row jcs[k].2 ⟨i, hi⟩ = Vals.row jcs[l].2 ⟨j, hj⟩) ∧
      ∀ {k : Nat} (hk : k < 2),
        (jc[k].w = 1 ∨ jc[k].w = 2 ∨ jc[k].w = 4 ∨ jc[k].w = 8 ∨ jc[k].w = 16 ∨ jc[k].w = 32 ∨ jc[k].w = 64) ∧
        jc[k].n = jcs[k].1 ∧ jc[k].b.size = (jc[k].n.toNat * jc[k].w + 7) / 8 ∧
        (jc[k].w < 8 → jc[k].card < USize.size ∧ ∀ i < jc[k].n.toNat, Column.idAt jc[k].b jc[k].w i < jc[k].card))
    (hrn : S.n.toNat < 2 ^ 63)
    (hM : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt jc[1].b jc[1].w j == Column.idAt jc[0].b jc[0].w i).length).sum < 2 ^ 63)
    (hMU : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt jc[1].b jc[1].w j == Column.idAt jc[0].b jc[0].w i).length).sum < USize.size)
    (hA : ∀ (i : ByteArray) (m : USize) (h : len i = m.toNat) (q : Fin m.toNat)
      (hin : (Column.bitsAt i (q.1 * 8) 8).toNat < R.n.toNat), (Vals.pick A R.key i m h).row q = R.key.row ⟨_, hin⟩)
    (hC : ∀ (i : ByteArray) (m : USize) (h : len i = m.toNat) (q : Fin m.toNat)
      (hin : (Column.bitsAt i (q.1 * 8) 8).toNat < S.n.toNat), (Vals.pick C S.val i m h).row q = S.val.row ⟨_, hin⟩) :
    rep (R ≫ S) = rep R ≫ rep S := by
  obtain ⟨hF, hW⟩ := hc
  obtain ⟨hlw, hln, hls, -⟩ := hW (k := 0) (by decide)
  obtain ⟨hrw, hrn', hrs, hrc⟩ := hW (k := 1) (by decide)
  replace hln : jc[0].n = R.n := hln
  replace hrn' : jc[1].n = S.n := hrn'
  have hZ := join_spec jc[0] jc[1] hlw hls hrw hrs hrc (hrn' ▸ hrn) (by rw [hln, hrn']; exact hM)
    (by rw [hln, hrn']; exact hMU)
  rw [hln, hrn'] at hZ
  have hJ := join_len jc[0] jc[1]
  rw [len_eq_ids, len_eq_ids] at hJ
  -- the pairs `join` answers: `(i, j)` with equal codes, `i` a row of `R`, `j` of `S`
  have hmem : ∀ i j, (i, j) ∈ (ids (join jc[0] jc[1]).1).zip (ids (join jc[0] jc[1]).2) ↔
      i < R.n.toNat ∧ j < S.n.toNat ∧ Column.idAt jc[1].b jc[1].w j = Column.idAt jc[0].b jc[0].w i := by
    intro i j; rw [hZ]; simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range, beq_iff_eq]
    constructor
    · rintro ⟨i', hi', j', ⟨hj', he⟩, hp⟩; cases hp; exact ⟨hi', hj', he⟩
    · rintro ⟨hi, hj, he⟩; exact ⟨i, hi, j, ⟨hj, he⟩, rfl⟩
  have hlt : len (join jc[0] jc[1]).2 < USize.size := by
    have := congrArg List.length hZ
    rw [List.length_zip, List.length_flatMap] at this
    rw [len_eq_ids]; simp only [List.length_map] at this; omega
  have hids : ∀ (b : ByteArray) q (hq : q < (ids b).length), (ids b)[q] = (Column.bitsAt b (q * 8) 8).toNat := by
    intro b q hq; simp [ids]
  -- row `q` of the join is its pair `q`
  have hrow : ∀ q (hq : q < len (join jc[0] jc[1]).2),
      ((Column.bitsAt (join jc[0] jc[1]).1 (q * 8) 8).toNat, (Column.bitsAt (join jc[0] jc[1]).2 (q * 8) 8).toNat) ∈
        (ids (join jc[0] jc[1]).1).zip (ids (join jc[0] jc[1]).2) := by
    intro q hq
    rw [len_eq_ids] at hq
    rw [← hids _ q (by omega), ← hids _ q hq, ← List.getElem_zip (h := by rw [List.length_zip]; omega)]
    exact List.getElem_mem _
  refine hom_ext fun a c => ?_
  show (longCount "≫" (join jc[0] jc[1]).2 fun m h =>
      (⟨m, Vals.pickN A R.key (join jc[0] jc[1]).1 m (h ▸ join_len jc[0] jc[1]),
        Vals.pick C S.val (join jc[0] jc[1]).2 m h⟩ : Rel A C)).Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c
  unfold longCount need
  rw [dif_pos hlt]
  -- the relation at whatever count `m` the join's length enters as
  suffices H : ∀ (m : USize) (hmJ : len (join jc[0] jc[1]).2 = m.toNat),
      (⟨m, Vals.pickN A R.key (join jc[0] jc[1]).1 m (hmJ ▸ join_len jc[0] jc[1]),
        Vals.pick C S.val (join jc[0] jc[1]).2 m hmJ⟩ : Rel A C).Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c from H _ _
  intro m hmJ
  have hfit : ∀ q, q < m.toNat →
      Column.bitsAt (fit m.toNat (join jc[0] jc[1]).1) (q * 8) 8 = Column.bitsAt (join jc[0] jc[1]).1 (q * 8) 8 := by
    intro q hq; unfold fit; split
    · rfl
    · rw [bitsAt_extract _ (by omega), Nat.zero_add]
  -- `pickN` is `pick` at `fit`
  have hA' : ∀ (h : m.toNat ≤ len (join jc[0] jc[1]).1) (q : Fin m.toNat)
      (hin : (Column.bitsAt (fit m.toNat (join jc[0] jc[1]).1) (q.1 * 8) 8).toNat < R.n.toNat),
      (Vals.pickN A R.key (join jc[0] jc[1]).1 m h).row q = R.key.row ⟨_, hin⟩ :=
    fun h q hin => by unfold Vals.pickN; exact hA _ m _ q hin
  simp only [Rel.Holds]
  constructor
  · rintro ⟨q, hqa, hqc⟩
    have hq : q.1 < len (join jc[0] jc[1]).2 := by have := q.2; omega
    obtain ⟨hi, hj, he⟩ := (hmem _ _).1 (hrow q.1 hq)
    have hi' : (Column.bitsAt (fit m.toNat (join jc[0] jc[1]).1) (q.1 * 8) 8).toNat < R.n.toNat := by
      rw [hfit q.1 q.2]; exact hi
    rw [hA' _ q hi'] at hqa
    rw [hC _ _ _ q hj] at hqc
    refine ⟨R.val.row ⟨_, hi⟩, ⟨⟨_, hi⟩, ?_, rfl⟩, ⟨_, hj⟩, ?_, hqc⟩
    · rw [← hqa]; exact congrArg R.key.row (Fin.ext (by simp only [hfit q.1 q.2]))
    · exact ((hF (k := 0) (l := 1) (by decide) (by decide) hi hj).1 he.symm).symm
  · rintro ⟨b, ⟨i, hia, hib⟩, ⟨j, hjb, hjc⟩⟩
    have he : Column.idAt jc[1].b jc[1].w j.1 = Column.idAt jc[0].b jc[0].w i.1 :=
      ((hF (k := 0) (l := 1) (by decide) (by decide) i.2 j.2).2 (hib.trans hjb.symm)).symm
    obtain ⟨q, hq, hp⟩ := List.getElem_of_mem ((hmem i.1 j.1).2 ⟨i.2, j.2, he⟩)
    rw [List.length_zip] at hq
    have hq2 : q < m.toNat := by rw [← hmJ, len_eq_ids]; omega
    rw [List.getElem_zip, hids _ q (by omega), hids _ q (by omega), Prod.mk.injEq] at hp
    have hi' : (Column.bitsAt (fit m.toNat (join jc[0] jc[1]).1) (q * 8) 8).toNat < R.n.toNat := by
      rw [hfit q hq2, hp.1]; exact i.2
    have hj' : (Column.bitsAt (join jc[0] jc[1]).2 (q * 8) 8).toNat < S.n.toNat := by rw [hp.2]; exact j.2
    refine ⟨⟨q, hq2⟩, ?_, ?_⟩
    · rw [hA' _ ⟨q, hq2⟩ hi', ← hia]; exact congrArg R.key.row (Fin.ext (by simp only [hfit q hq2, hp.1]))
    · rw [hC _ _ _ ⟨q, hq2⟩ hj', ← hjc]; exact congrArg S.val.row (Fin.ext hp.2)

/-- `rep_comp` through a boolean middle side: its codes are its bits (`codes_boolean_faithful`/`_wf`). -/
theorem rep_comp_boolean (R : Rel A (.atom .boolean)) (S : Rel (.atom .boolean) C)
    (hrn : S.n.toNat < 2 ^ 63)
    (hM : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt jc[1].b jc[1].w j == Column.idAt jc[0].b jc[0].w i).length).sum < 2 ^ 63)
    (hMU : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt jc[1].b jc[1].w j == Column.idAt jc[0].b jc[0].w i).length).sum < USize.size)
    (hA : ∀ (i : ByteArray) (m : USize) (h : len i = m.toNat) (q : Fin m.toNat)
      (hin : (Column.bitsAt i (q.1 * 8) 8).toNat < R.n.toNat), (Vals.pick A R.key i m h).row q = R.key.row ⟨_, hin⟩)
    (hC : ∀ (i : ByteArray) (m : USize) (h : len i = m.toNat) (q : Fin m.toNat)
      (hin : (Column.bitsAt i (q.1 * 8) 8).toNat < S.n.toNat), (Vals.pick C S.val i m h).row q = S.val.row ⟨_, hin⟩) :
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
      Column.idAt jc[1].b jc[1].w j == Column.idAt jc[0].b jc[0].w i).length).sum < 2 ^ 63)
    (hMU : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt jc[1].b jc[1].w j == Column.idAt jc[0].b jc[0].w i).length).sum < USize.size)
    (hA : ∀ (i : ByteArray) (m : USize) (h : len i = m.toNat) (q : Fin m.toNat)
      (hin : (Column.bitsAt i (q.1 * 8) 8).toNat < R.n.toNat), (Vals.pick A R.key i m h).row q = R.key.row ⟨_, hin⟩)
    (hC : ∀ (i : ByteArray) (m : USize) (h : len i = m.toNat) (q : Fin m.toNat)
      (hin : (Column.bitsAt i (q.1 * 8) 8).toNat < S.n.toNat), (Vals.pick C S.val i m h).row q = S.val.row ⟨_, hin⟩) :
    rep (R ≫ S) = rep R ≫ rep S :=
  rep_comp R S ⟨fun {_ _} hk hl {_ _} hi hj => codes_long_faithful ht _ hro hk hl hi hj,
    fun hk => codes_long_wf ht _ hro hk⟩ hrn hM hMU hA hC

end Comp

#print axioms pick_row_atom
#print axioms pick_row_prod
#print axioms rep_comp
#print axioms rep_comp_boolean
#print axioms rep_comp_long

section CompSmallInt

open Freyd Freyd.Alg.RelSet

/-- `rep_comp` through a small integral middle side (`byte`, `char`, `short`, the four-byte types) of dense
    payloads, the two counts summing below a `USize` (`codes_small_int_parts_faithful`/`_wf`). -/
theorem rep_comp_small_int {t : QAtomicType} {k₀ : Scan.Kind} (ht : orderKind t = some k₀)
    (hk₀ : k₀ = .u8 ∨ k₀ = .i16 ∨ k₀ = .i32) (R : Rel A (.atom t)) (S : Rel (.atom t) C)
    (hRv : ∃ b, R.val.enc = .bytes b) (hSk : ∃ b, S.key.enc = .bytes b) (hN : R.n.toNat + S.n.toNat < USize.size)
    (hrn : S.n.toNat < 2 ^ 63)
    (hM : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt jc[1].b jc[1].w j == Column.idAt jc[0].b jc[0].w i).length).sum < 2 ^ 63)
    (hMU : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt jc[1].b jc[1].w j == Column.idAt jc[0].b jc[0].w i).length).sum < USize.size)
    (hA : ∀ (i : ByteArray) (m : USize) (h : len i = m.toNat) (q : Fin m.toNat)
      (hin : (Column.bitsAt i (q.1 * 8) 8).toNat < R.n.toNat), (Vals.pick A R.key i m h).row q = R.key.row ⟨_, hin⟩)
    (hC : ∀ (i : ByteArray) (m : USize) (h : len i = m.toNat) (q : Fin m.toNat)
      (hin : (Column.bitsAt i (q.1 * 8) 8).toNat < S.n.toNat), (Vals.pick C S.val i m h).row q = S.val.row ⟨_, hin⟩) :
    rep (R ≫ S) = rep R ≫ rep S :=
  have hd : ∀ k (hk : k < 2), ∃ b, (jcs)[k].2.enc = .bytes b := fun k hk => by
    match k, hk with | 0, _ => exact hRv | 1, _ => exact hSk
  have hN' : ((jcs).toList.map (·.1.toNat)).sum < USize.size := by simpa using hN
  rep_comp R S ⟨fun {_ _} hk hl {_ _} hi hj => codes_small_int_parts_faithful ht hk₀ _ hd hN' hk hl hi hj,
    fun hk => codes_small_int_parts_wf ht hk₀ _ hN' hk⟩ hrn hM hMU hA hC

end CompSmallInt

#print axioms rep_comp_small_int

end LeetQ.Rel.Rep
