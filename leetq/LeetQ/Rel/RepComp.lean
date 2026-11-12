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

-- the two parts `≫` codes jointly, and their codes, named as `comp` names them
set_option hygiene false in
local notation "jcs" => (#v[⟨R.n, R.val⟩, ⟨S.n, S.key⟩] : Vector (Part _) 2)
set_option hygiene false in
local notation "jc" => Obj.codes _ jcs
-- the pairs `(i, j)` `join` answers, as `join_spec` reads them back: row `i` of `R`, row `j` of `S`, equal codes
set_option hygiene false in
local notation "jpairs" => ((List.range R.n.toNat).flatMap fun i => ((List.range S.n.toNat).filter fun j =>
  Column.idAt jc[1].b jc[1].w j == Column.idAt jc[0].b jc[0].w i).map (i, ·))

section Comp

open Freyd Freyd.Alg.RelSet

-- elaborating `≫`'s body against `join`'s statement passes the default budget
set_option maxHeartbeats 800000 in
/-- **`rep (R ≫ S) = rep R ≫ rep S`.** Hypotheses:
    - `hc`, the middle side's joint codes identify rows and are well formed — what `CodesSpec` concludes;
    - `hrn`, `hM`, `hMU`, the counts `join_spec` takes: `S`'s rows and the match count below `2^63`, the
      match count a `USize` (past it `≫` answers `𝟘`);
    - `hA`, `hC`, `Vals.PickFits` of `R.key` at the left rows of the join's pairs and of `S.val` at the
      right ones, which `pick_row` reads back under; a side of atoms and products fits outright
      (`pickFits_atom`, `pickFits_prod`, `join_pairs_lt`). -/
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
    (hA : Vals.PickFits A R.key ((jpairs).map Prod.fst)) (hC : Vals.PickFits C S.val ((jpairs).map Prod.snd)) :
    rep (R ≫ S) = rep R ≫ rep S := by
  obtain ⟨hF, hW⟩ := hc
  obtain ⟨hlw, hln, hls, -⟩ := hW (k := 0) (by decide)
  obtain ⟨hrw, hrn', hrs, hrc⟩ := hW (k := 1) (by decide)
  replace hln : jc[0].n = R.n := hln
  replace hrn' : jc[1].n = S.n := hrn'
  obtain ⟨hlt, hZ⟩ := join_rows _ _ hlw hls hrw hrs hrc (by rw [hrn']; exact hrn) (by rw [hln, hrn']; exact hM)
    (by rw [hln, hrn']; exact hMU)
  have hP := mem_joinPairs jc[0] jc[1]
  rw [hln, hrn'] at hP
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
  have e := hZ m hmJ
  rw [hln, hrn'] at e
  have hfA : Vals.PickFits A R.key
      ((List.range m.toNat).map fun q => (Column.bitsAt (fit m.toNat (join jc[0] jc[1]).1) (q * 8) 8).toNat) := by
    rw [show ((List.range m.toNat).map fun q => (Column.bitsAt (fit m.toNat (join jc[0] jc[1]).1) (q * 8) 8).toNat) =
      (jpairs).map Prod.fst by rw [e, List.map_map]; rfl]; exact hA
  have hfC : Vals.PickFits C S.val
      ((List.range m.toNat).map fun q => (Column.bitsAt (join jc[0] jc[1]).2 (q * 8) 8).toNat) := by
    rw [show ((List.range m.toNat).map fun q => (Column.bitsAt (join jc[0] jc[1]).2 (q * 8) 8).toNat) =
      (jpairs).map Prod.snd by rw [e, List.map_map]; rfl]; exact hC
  have hA' : ∀ (h : m.toNat ≤ len (join jc[0] jc[1]).1) (q : Fin m.toNat)
      (hin : (Column.bitsAt (fit m.toNat (join jc[0] jc[1]).1) (q.1 * 8) 8).toNat < R.n.toNat),
      (Vals.pickN A R.key (join jc[0] jc[1]).1 m h).row q = R.key.row ⟨_, hin⟩ :=
    fun h q hin => by unfold Vals.pickN; rw [pick_row A R.key _ m _ hfA q, dif_pos hin]
  simp only [Rel.Holds]
  constructor
  · rintro ⟨q, hqa, hqc⟩
    have hq : ((Column.bitsAt (fit m.toNat (join jc[0] jc[1]).1) (q.1 * 8) 8).toNat,
        (Column.bitsAt (join jc[0] jc[1]).2 (q.1 * 8) 8).toNat) ∈ jpairs := by
      rw [e]; exact List.mem_map.2 ⟨q.1, List.mem_range.2 q.2, rfl⟩
    obtain ⟨hi, hj, he⟩ := (hP _ _).1 hq
    rw [hA' _ q hi] at hqa
    rw [pick_row C S.val _ m hmJ hfC q, dif_pos hj] at hqc
    exact ⟨R.val.row ⟨_, hi⟩, ⟨⟨_, hi⟩, hqa, rfl⟩, ⟨_, hj⟩,
      ((hF (k := 0) (l := 1) (by decide) (by decide) hi hj).1 he.symm).symm, hqc⟩
  · rintro ⟨b, ⟨i, hia, hib⟩, ⟨j, hjb, hjc⟩⟩
    have he : Column.idAt jc[1].b jc[1].w j.1 = Column.idAt jc[0].b jc[0].w i.1 :=
      ((hF (k := 0) (l := 1) (by decide) (by decide) i.2 j.2).2 (hib.trans hjb.symm)).symm
    have hm := (hP i.1 j.1).2 ⟨i.2, j.2, he⟩
    rw [e] at hm
    obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hm
    obtain ⟨h1, h2⟩ := Prod.mk.inj hqe
    have hq2 := List.mem_range.1 hq
    have hi' : (Column.bitsAt (fit m.toNat (join jc[0] jc[1]).1) (q * 8) 8).toNat < R.n.toNat := by rw [h1]; exact i.2
    have hj' : (Column.bitsAt (join jc[0] jc[1]).2 (q * 8) 8).toNat < S.n.toNat := by rw [h2]; exact j.2
    refine ⟨⟨q, hq2⟩, ?_, ?_⟩
    · rw [hA' _ ⟨q, hq2⟩ hi', ← hia]; exact congrArg R.key.row (Fin.ext h1)
    · rw [pick_row C S.val _ m hmJ hfC ⟨q, hq2⟩, dif_pos hj', ← hjc]; exact congrArg S.val.row (Fin.ext h2)

/-- `rep_comp` through a boolean middle side: its codes are its bits (`codes_boolean_faithful`/`_wf`). -/
theorem rep_comp_boolean (R : Rel A (.atom .boolean)) (S : Rel (.atom .boolean) C)
    (hrn : S.n.toNat < 2 ^ 63)
    (hM : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt jc[1].b jc[1].w j == Column.idAt jc[0].b jc[0].w i).length).sum < 2 ^ 63)
    (hMU : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt jc[1].b jc[1].w j == Column.idAt jc[0].b jc[0].w i).length).sum < USize.size)
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
      Column.idAt jc[1].b jc[1].w j == Column.idAt jc[0].b jc[0].w i).length).sum < 2 ^ 63)
    (hMU : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt jc[1].b jc[1].w j == Column.idAt jc[0].b jc[0].w i).length).sum < USize.size)
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
    (hA : Vals.PickFits A R.key ((jpairs).map Prod.fst)) (hC : Vals.PickFits C S.val ((jpairs).map Prod.snd)) :
    rep (R ≫ S) = rep R ≫ rep S :=
  have hd : ∀ k (hk : k < 2), ∃ b, (jcs)[k].2.enc = .bytes b := fun k hk => by
    match k, hk with | 0, _ => exact hRv | 1, _ => exact hSk
  have hN' : ((jcs).toList.map (·.1.toNat)).sum < USize.size := by simpa using hN
  rep_comp R S ⟨fun {_ _} hk hl {_ _} hi hj => codes_small_int_parts_faithful ht hk₀ _ hd hN' hk hl hi hj,
    fun hk => codes_small_int_parts_wf ht hk₀ _ hN' hk⟩ hrn hM hMU hA hC

end CompSmallInt

#print axioms rep_comp_small_int

section CompGuid

open Freyd Freyd.Alg.RelSet

/-- **A `guid` side of several parts: its codes are those of its `raze`, cut back** — `guid` is dense, so
    neither a bitmap, nor `rangeOffsets`' long order, nor interned. -/
theorem codes_guid_cut {p : Nat} (cs : Vector (Part (.atom .guid)) p) (hp : 0 < p) :
    Obj.codes (.atom .guid) cs = (Obj.codes (.atom .guid) #v[raze .guid cs.toArray])[0].cut (cs.map (·.1)) := by
  have hne : ∀ d o ids, Column.intern (raze .guid cs.toArray).2.enc ≠ .enum d o ids := fun d o ids he => by
    obtain ⟨b, hb, -⟩ := guid_enc (raze .guid cs.toArray).2.wf; simp [hb, Column.intern] at he
  obtain ⟨q, hq, hc⟩ := codes_raze_cut (by decide) cs hp
    (fun k hk b he => by obtain ⟨b', hb', -⟩ := guid_enc cs[k].2.wf; rw [hb'] at he; cases he)
    (by unfold rangeOffsets; simp [orderKind]) hne
  obtain ⟨q', hq', hc'⟩ := codes_guid (raze .guid cs.toArray)
  rw [hc, hc', show q' = q from Option.some_inj.1 (hq'.symm.trans hq)]

/-- **A `guid` side of several parts: its codes are faithful jointly across the parts**, the parts' summed count
    a `USize`. -/
theorem codes_guid_parts_faithful {p : Nat} (cs : Vector (Part (.atom .guid)) p)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < cs[k].1.toNat) (hj : j < cs[l].1.toNat) :
    Column.idAt (Obj.codes (.atom .guid) cs)[k].b (Obj.codes (.atom .guid) cs)[k].w i =
        Column.idAt (Obj.codes (.atom .guid) cs)[l].b (Obj.codes (.atom .guid) cs)[l].w j ↔
      Vals.row cs[k].2 ⟨i, hi⟩ = Vals.row cs[l].2 ⟨j, hj⟩ := by
  have hd : ∀ k (hk : k < p), ∃ b, cs[k].2.enc = .bytes b := fun k _ =>
    let ⟨b, hb, _⟩ := guid_enc cs[k].2.wf; ⟨b, hb⟩
  have hX := raze_len .guid cs.toArray hN
  obtain ⟨hw, hn, -, -⟩ := codes_guid_wf (raze .guid cs.toArray)
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum = (Obj.codes (.atom .guid) #v[raze .guid cs.toArray])[0].n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hO : ∀ k, (((cs.map (·.1)).toList.take k).map (·.toNat)).sum = ((cs.toList.take k).map (·.1.toNat)).sum :=
    fun k => by rw [Vector.toList_map, ← List.map_take, List.map_map]; rfl
  have hlt : ∀ k (hk : k < p), ∀ i < cs[k].1.toNat,
      ((cs.toList.take k).map (·.1.toNat)).sum + i < (raze .guid cs.toArray).1.toNat := fun k hk i hi => by
    have := take_sum_le (cs.toList.map (·.1.toNat)) (k := k) (by simpa using hk)
    simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take] at this
    rw [hX]; exact Nat.lt_of_lt_of_le (by omega) this
  rw [codes_guid_cut cs (by omega)]
  obtain ⟨hwk, -, -, hck⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  obtain ⟨hwl, -, -, hcl⟩ := cut_get _ (cs.map (·.1)) hw hs hl
  rw [hwk, hwl, hck i (by simpa using hi), hcl j (by simpa using hj), hO, hO,
    codes_guid_faithful _ (hlt k hk i hi) (hlt l hl j hj), Vals.row_atom, Vals.row_atom, Vals.row_atom,
    Vals.row_atom, raze_get_bytes cs hd hN hk hi, raze_get_bytes cs hd hN hl hj]

/-- **A `guid` side of several parts: each part's code is well formed**, the parts' summed count a `USize`. -/
theorem codes_guid_parts_wf {p : Nat} (cs : Vector (Part (.atom .guid)) p)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size) {k : Nat} (hk : k < p) :
    let c := (Obj.codes (.atom .guid) cs)[k]
    (c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = cs[k].1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  intro c
  have hX := raze_len .guid cs.toArray hN
  obtain ⟨hw, hn, hsz, hid⟩ := codes_guid_wf (raze .guid cs.toArray)
  have hs : (((cs.map (·.1)).toList).map (·.toNat)).sum = (Obj.codes (.atom .guid) #v[raze .guid cs.toArray])[0].n.toNat := by
    rw [hn, hX, Vector.toList_map, List.map_map]; rfl
  have hle := take_sum_le ((cs.map (·.1)).toList.map (·.toNat)) (k := k) (by simpa using hk)
  simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take, hs] at hle
  have hc : c = ((Obj.codes (.atom .guid) #v[raze .guid cs.toArray])[0].cut (cs.map (·.1)))[k] := by
    show (Obj.codes (.atom .guid) cs)[k] = _; rw [codes_guid_cut cs (by omega)]
  obtain ⟨hwk, hnk, hck, hik⟩ := cut_get _ (cs.map (·.1)) hw hs hk
  have hzk := cut_size _ (cs.map (·.1)) hw hs hsz hk
  rw [hc, hwk, hnk, hck, hzk]
  refine ⟨hw, by simp, rfl, fun h8 => ⟨(hid h8).1, fun i hi => ?_⟩⟩
  rw [hik i hi]; exact (hid h8).2 _ (by omega)

/-- `rep_comp` through a `guid` middle side, the two counts summing below a `USize`
    (`codes_guid_parts_faithful`/`_wf`). -/
theorem rep_comp_guid (R : Rel A (.atom .guid)) (S : Rel (.atom .guid) C) (hN : R.n.toNat + S.n.toNat < USize.size)
    (hrn : S.n.toNat < 2 ^ 63)
    (hM : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt jc[1].b jc[1].w j == Column.idAt jc[0].b jc[0].w i).length).sum < 2 ^ 63)
    (hMU : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt jc[1].b jc[1].w j == Column.idAt jc[0].b jc[0].w i).length).sum < USize.size)
    (hA : Vals.PickFits A R.key ((jpairs).map Prod.fst)) (hC : Vals.PickFits C S.val ((jpairs).map Prod.snd)) :
    rep (R ≫ S) = rep R ≫ rep S :=
  have hN' : ((jcs).toList.map (·.1.toNat)).sum < USize.size := by simpa using hN
  rep_comp R S ⟨fun {_ _} hk hl {_ _} hi hj => codes_guid_parts_faithful _ hN' hk hl hi hj,
    fun hk => codes_guid_parts_wf _ hN' hk⟩ hrn hM hMU hA hC

end CompGuid

#print axioms codes_guid_cut
#print axioms rep_comp_guid

end LeetQ.Rel.Rep
