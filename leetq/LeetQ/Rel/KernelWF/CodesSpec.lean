/-
  What `Obj.codes` answers, read off its Lean body: the code column of a side identifies rows exactly
  (`Column.idAt c.b c.w i = Column.idAt c.b c.w j ↔ row i = row j`), and is well formed in the sense the
  code lemmas of `JoinSpec`/`MemberSpec` take (`w` a lane, `b` exactly `⌈n·w/8⌉` bytes, every code below
  `card`, `card` a `USize` below a byte).
-/
import LeetQ.Rel.KernelWF.JoinSpec

namespace LeetQ.Rel.Alg

open QLean QLean.Kernel QLean.Verify LeetQ.Rel

/-! ## Atoms: a boolean side -/

/-- A boolean column's payload is its bitmap, `tagBits`. -/
theorem enc_tagBits {n : USize} (x : Arr .boolean n) : x.enc = .bits (tagBits x) := by
  have key : ∀ (e : Enc) (o : Option ByteArray), (o = match e with | .bits b => some b | _ => none) →
      ∀ h : o.isSome, e = .bits (o.get h) := by
    intro e o ho h; subst ho; cases e <;> first | rfl | simp at h
  exact key x.enc _ rfl _

/-- **A boolean side's codes are its bitmaps**: every part's payload is `bits` (`Enc.WF .boolean`), so
    `codes` takes its first branch, each part its own code a bit wide. -/
theorem codes_boolean {p : Nat} (cs : Vector (Part (.atom .boolean)) p) :
    Obj.codes (.atom .boolean) cs = cs.map fun c => (⟨1, c.1, 2, tagBits c.2⟩ : Code) := by
  show Alg.codes .boolean cs = _
  unfold Alg.codes
  rw [dif_neg (by decide)]
  have e : (cs.mapM fun c : Part (.atom .boolean) => some (⟨1, c.1, 2, tagBits c.2⟩ : Code)) =
      some (cs.map fun c => (⟨1, c.1, 2, tagBits c.2⟩ : Code)) := Vector.mapM_pure _
  simp only [enc_tagBits, e]

/-- **A boolean side's codes are faithful, jointly across its parts**: part `k`'s code at `i` and part `l`'s
    at `j` agree exactly when the rows do. -/
theorem codes_boolean_faithful {p : Nat} (cs : Vector (Part (.atom .boolean)) p) {k l : Nat}
    (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < cs[k].1.toNat) (hj : j < cs[l].1.toNat) :
    Column.idAt (Obj.codes (.atom .boolean) cs)[k].b (Obj.codes (.atom .boolean) cs)[k].w i =
        Column.idAt (Obj.codes (.atom .boolean) cs)[l].b (Obj.codes (.atom .boolean) cs)[l].w j ↔
      Vals.row cs[k].2 ⟨i, hi⟩ = Vals.row cs[l].2 ⟨j, hj⟩ := by
  simp only [codes_boolean, Vector.getElem_map]
  rw [idAt_one, idAt_one, Vals.row_atom, Vals.row_atom, Arr.get_bool_bits cs[k].2 (enc_tagBits _),
    Arr.get_bool_bits cs[l].2 (enc_tagBits _)]
  cases Column.bitAt (tagBits cs[k].2) i <;> cases Column.bitAt (tagBits cs[l].2) j <;> simp

/-- **A boolean side's codes are well formed**: a bit wide, `⌈n/8⌉` bytes, every code `0` or `1`, below
    `card = 2`. -/
theorem codes_boolean_wf {p : Nat} (cs : Vector (Part (.atom .boolean)) p) {k : Nat} (hk : k < p) :
    (Obj.codes (.atom .boolean) cs)[k].n = cs[k].1 ∧ (Obj.codes (.atom .boolean) cs)[k].w = 1 ∧
      (Obj.codes (.atom .boolean) cs)[k].b.size =
        ((Obj.codes (.atom .boolean) cs)[k].n.toNat * (Obj.codes (.atom .boolean) cs)[k].w + 7) / 8 ∧
      ((Obj.codes (.atom .boolean) cs)[k].w < 8 → (Obj.codes (.atom .boolean) cs)[k].card < USize.size ∧
        ∀ i < (Obj.codes (.atom .boolean) cs)[k].n.toNat,
          Column.idAt (Obj.codes (.atom .boolean) cs)[k].b (Obj.codes (.atom .boolean) cs)[k].w i <
            (Obj.codes (.atom .boolean) cs)[k].card) := by
  rw [codes_boolean, Vector.getElem_map]
  have hw := cs[k].2.wf
  rw [enc_tagBits] at hw
  refine ⟨rfl, rfl, by simpa [Enc.WF] using hw,
    fun _ => ⟨Nat.lt_of_lt_of_le (by decide : (2 : Nat) < 2 ^ 32) USize.le_size, fun i _ => ?_⟩⟩
  rw [idAt_one]; split <;> simp

#print axioms codes_boolean_faithful
#print axioms codes_boolean_wf

end LeetQ.Rel.Alg
