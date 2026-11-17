/-
  What `join` and `Obj.codes` answer, read off the Lean bodies of the qlean kernels they call: the
  content lemmas `Alg.comp` and `Alg.pair` need, beside the length lemmas of `Code.lean`. A code `c` is
  read at its lane, `Column.idAt c.b c.w i`, which is a bit at `1`, a packed id at `2`/`4` and a dense
  little-endian element at `8 … 64` (`idAt_one`, `resAt_lane`).
-/
import LeetQ.Rel.KernelWF.Lane
import QLean.RelPart.Verify.Gather
import QLean.RelPart.Verify.Search
import QLean.RelPart.Verify.SymFind

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel

/-- An injective `f` keeps every position: `l.map f` finds `f a` where `l` finds `a`. Belongs in qlean. -/
theorem idxOf_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α → β}
    (hf : ∀ a b, f a = f b → a = b) (l : List α) (a : α) : (l.map f).idxOf (f a) = l.idxOf a := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : x = a
    · subst h; simp
    · have h' : f x ≠ f a := fun e => h (hf _ _ e)
      simp only [List.map_cons, List.idxOf_cons, ih, beq_false_of_ne h, beq_false_of_ne h']

/-- **`findIdsVec` is `idxOf`**: at any two lanes, the long answered for needle `j` is the first
    position in the haystack's `hn` codes holding needle `j`'s code, one long per needle. -/
theorem findIdsVec_spec {hw nw : Nat} {hn nn : USize} {hay ndl : ByteArray}
    (hhw : laneOK(hw))
    (hnw : laneOK(nw))
    (hs : hw * hn.toNat ≤ 8 * hay.size) (ns : nw * nn.toNat ≤ 8 * ndl.size) :
    len (findIdsVec hw.toUSize hay hn nw.toUSize ndl nn) = nn.toNat ∧
    ∀ j < nn.toNat, (Column.bitsAt (findIdsVec hw.toUSize hay hn nw.toUSize ndl nn) (j * 8) 8).toNat =
      ((List.range hn.toNat).map (Column.idAt hay hw)).idxOf (Column.idAt ndl nw j) := by
  have h1 : hw.toUSize.toNat = hw := lane_toNat (by omega)
  have h2 : nw.toUSize.toNat = nw := lane_toNat (by omega)
  obtain ⟨hz, hv⟩ := findIdsVec_idxOf hw.toUSize nw.toUSize hn nn hay ndl (by rw [h1]; omega) (by rw [h2]; omega)
  simp only [h1, h2, idsCap_full (by omega) ns, idsCap_full (by omega) hs] at hz hv
  exact ⟨by simp [len, hz], hv⟩

/-- **`findVec` at one byte lane is `idxOf`**: `q`-byte codes on both sides, payloads exactly `q` bytes a
    code, not a float. -/
theorem findVec_spec {q : Nat} (hq : q = 1 ∨ q = 2 ∨ q = 4 ∨ q = 8) {hn nn : USize} {hay ndl : ByteArray}
    (hs : hay.size = q * hn.toNat) (ns : ndl.size = q * nn.toNat) :
    len (findVec q.toUSize false hay ndl) = nn.toNat ∧
    ∀ j < nn.toNat, (Column.bitsAt (findVec q.toUSize false hay ndl) (j * 8) 8).toNat =
      ((List.range hn.toNat).map (Column.idAt hay (8 * q))).idxOf (Column.idAt ndl (8 * q) j) := by
  have h1 : q.toUSize.toNat = q := lane_toNat (by omega)
  have hq0 : 0 < q := by omega
  have hd : hay.size / q = hn.toNat := by rw [hs, Nat.mul_div_cancel_left _ hq0]
  have nd : ndl.size / q = nn.toNat := by rw [ns, Nat.mul_div_cancel_left _ hq0]
  obtain ⟨hz, hv⟩ := findVec_idxOf q.toUSize false hay ndl (by rw [h1, hd]; exact hn.toNat_lt_size)
  rw [h1, nd] at hz hv
  refine ⟨by simp [len, hz], fun j hj => ?_⟩
  rw [hv j hj, if_pos (by omega)]
  have hnorm : normalise q false = id := funext fun v => by simp [normalise]
  have hid (b : ByteArray) (i : Nat) := idAt_lane b (c := q) (by omega) i
  have hl : (List.range hn.toNat).map (Column.idAt hay (8 * q)) =
      ((List.range hn.toNat).map fun i => Column.bitsAt hay (i * q) q).map UInt64.toNat := by
    simp [List.map_map, Function.comp_def, hid]
  simp only [hnorm, List.map_id, id, elemsW, hd]
  rw [hl, hid ndl, idxOf_map_inj (fun a b h => UInt64.toNat_inj.1 h)]

/-- `findVec_spec` at a sort layout's lane, as `Code.find` calls it. -/
theorem findVec_kind_spec {k : Scan.Kind} {w w' : Nat} (hq : k.width = 1 ∨ k.width = 2 ∨ k.width = 4 ∨ k.width = 8)
    (hw : w = 8 * k.width) (hw' : w' = 8 * k.width) {hn nn : USize} {hay ndl : ByteArray}
    (hs : 8 * hay.size = w * hn.toNat) (ns : 8 * ndl.size = w' * nn.toNat) :
    len (findVec k.width.toUSize false hay ndl) = nn.toNat ∧
    ∀ j < nn.toNat, (Column.bitsAt (findVec k.width.toUSize false hay ndl) (j * 8) 8).toNat =
      ((List.range hn.toNat).map (Column.idAt hay w)).idxOf (Column.idAt ndl w' j) := by
  subst hw hw'
  exact findVec_spec hq (by rw [Nat.mul_assoc] at hs; omega) (by rw [Nat.mul_assoc] at ns; omega)

/-- **`findBitVec` is `idxOf`**: bitmaps of `hn` and `nn` codes. -/
theorem findBitVec_spec (hn nn : USize) (hay ndl : ByteArray) :
    len (findBitVec hn hay nn ndl) = nn.toNat ∧
    ∀ j < nn.toNat, (Column.bitsAt (findBitVec hn hay nn ndl) (j * 8) 8).toNat =
      ((List.range hn.toNat).map (Column.idAt hay 1)).idxOf (Column.idAt ndl 1 j) := by
  obtain ⟨hz, hv⟩ := bitsAt_foldl8 nn.toNat (fun j => (findBit hn hay (Column.bitAt ndl j)).toUInt64) .empty rfl
  refine ⟨by simp [len, findBitVec, hz], fun j hj => ?_⟩
  have hb : ∀ c : Bool, ((List.range hn.toNat).map (Column.bitAt hay)).idxOf c < USize.size := fun c =>
    Nat.lt_of_le_of_lt (by simpa using idxOf_le_length c ((List.range hn.toNat).map (Column.bitAt hay)))
      hn.toNat_lt_size
  unfold findBitVec; rw [hv j hj]
  simp only [findBit, USize.toNat_toUInt64, find?_range_getD]
  rw [USize.toNat_ofNat_of_lt' (hb _)]
  have hl : (List.range hn.toNat).map (Column.idAt hay 1) =
      ((List.range hn.toNat).map (Column.bitAt hay)).map fun c : Bool => if c then 1 else 0 := by
    simp [List.map_map, Function.comp_def, idAt_one]
  rw [hl, idAt_one]
  exact (idxOf_map_inj (f := fun c : Bool => if c then 1 else 0)
    (fun a b h => by cases a <;> cases b <;> simp_all) _ _).symm

/-- **`Code.find` answers one long per code of `x`, the first position in `c` of that code**, `c.n` at a
    miss — every lane pair `Code.find` dispatches on. Hypotheses: each code is at a lane a `Code` takes,
    its payload holds its `n` codes, and a byte lane's payload holds exactly them. -/
theorem find_spec (c x : Code)
    (hcw : laneOK(c.w))
    (hxw : laneOK(x.w))
    (hcs : c.w * c.n.toNat ≤ 8 * c.b.size) (hxs : x.w * x.n.toNat ≤ 8 * x.b.size)
    (hcb : 8 ≤ c.w → 8 * c.b.size = c.w * c.n.toNat) (hxb : 8 ≤ x.w → 8 * x.b.size = x.w * x.n.toNat) :
    len (Code.find c x) = x.n.toNat ∧
    ∀ j < x.n.toNat, (Column.bitsAt (Code.find c x) (j * 8) 8).toNat =
      ((List.range c.n.toNat).map (Column.idAt c.b c.w)).idxOf (Column.idAt x.b x.w j) := by
  unfold Code.find Code.kind
  split
  next _ _ hc hx =>
    rcases laneKind_some hc with ⟨-, h1⟩ | ⟨h, -⟩
    · rcases laneKind_some hx with ⟨-, h2⟩ | ⟨h, -⟩
      · rw [h1, h2]; exact findBitVec_spec ..
      · exact absurd rfl h
    · exact absurd rfl h
  next _ _ k k' hne hc hx =>
    split
    next hk =>
      obtain rfl : k = k' := beq_iff_eq.1 hk
      have hkb : k ≠ .bit := fun h => hne h h
      rcases laneKind_some hc with ⟨h, -⟩ | ⟨-, hcw8, hq, -⟩
      · exact absurd h hkb
      rcases laneKind_some hx with ⟨h, -⟩ | ⟨-, hxw8, -⟩
      · exact absurd h hkb
      exact findVec_kind_spec hq hcw8 hxw8 (hcb (by omega)) (hxb (by omega))
    next => exact findIdsVec_spec hcw hxw hcs hxs
  next => exact findIdsVec_spec hcw hxw hcs hxs

/-- **`Code.gather` reads each index's code**: at an index column of `len i` in-range longs, code `j` of
    `c@i` is code `i[j]` of `c`, at `c`'s lane and bound — every lane `Code.gather` dispatches on.
    Hypotheses: `len i` fits a `USize`, `c` is at a lane a `Code` takes, a byte lane's payload holds
    exactly its `n` codes, and every index is below `c.n`. -/
theorem gather_spec (c : Code) (i : ByteArray) (hl : len i < USize.size)
    (hcw : laneOK(c.w))
    (hcb : 8 ≤ c.w → 8 * c.b.size = c.w * c.n.toNat)
    (hi : ∀ j < len i, (Column.bitsAt i (j * 8) 8).toNat < c.n.toNat) :
    (Code.gather c i).w = c.w ∧ (Code.gather c i).n.toNat = len i ∧ (Code.gather c i).card = c.card ∧
    ∀ j < len i, Column.idAt (Code.gather c i).b c.w j = Column.idAt c.b c.w (Column.bitsAt i (j * 8) 8).toNat := by
  unfold Code.gather longCount
  simp only [need, dif_pos hl]
  refine ⟨trivial, USize.toNat_ofNat_of_lt' hl, trivial, fun j hj => ?_⟩
  unfold Code.kind
  split
  next _ hk =>
    rcases laneKind_some hk with ⟨-, h1⟩ | ⟨h, -⟩
    · rw [h1, idAt_one, idAt_one, bitAt_gatherBits c.n c.b i j hj, if_pos (hi j hj)]
    · exact absurd rfl h
  next _ k hne hk =>
    rcases laneKind_some hk with ⟨h, -⟩ | ⟨-, hw8, hq, -⟩
    · exact absurd h hne
    have h1 : k.width.toUSize.toNat = k.width := lane_toNat (by omega)
    have hs := (gatherBytes_spec k.width.toUSize (by omega) 0 c.b i).2 j hj
    have hd : c.b.size / k.width = c.n.toNat := by
      have := hcb (by omega); rw [hw8, Nat.mul_assoc] at this
      rw [show c.b.size = k.width * c.n.toNat by omega, Nat.mul_div_cancel_left _ (by omega)]
    rw [h1, hd, if_pos (hi j hj)] at hs
    rw [hw8, idAt_lane _ (by omega), idAt_lane _ (by omega), hs]
  next _ _ =>
    have h1 : c.w.toUSize.toNat = c.w := lane_toNat (by omega)
    have hg := idAt_gatherPacked c.n c.w.toUSize c.w.toUSize 0 c.b i (by rw [h1]; omega)
      (fun _ _ => by rw [h1]; exact idAt_lt _ _ _ (by omega)) (by rw [h1]; exact Nat.two_pow_pos _) j hj
    rw [h1, if_pos (hi j hj)] at hg
    exact hg

/-- A long payload's count is its `ids`' length. -/
theorem len_eq_ids (b : ByteArray) : len b = (ids b).length := by simp [len, ids]

#print axioms find_spec
#print axioms gather_spec

end LeetQ.Rel.Alg
