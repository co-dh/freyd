/-
  What `Obj.codes` answers, read off its Lean body: the code column of a side identifies rows exactly
  (`Column.idAt c.b c.w i = Column.idAt c.b c.w j ↔ row i = row j`), and is well formed in the sense the
  code lemmas of `JoinSpec`/`MemberSpec` take (`w` a lane, `b` exactly `⌈n·w/8⌉` bytes, every code below
  `card`, `card` a `USize` below a byte).
-/
import LeetQ.Rel.KernelWF.JoinSpec
import LeetQ.Rel.KernelWF.PickSpec

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

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

/-! ## Atoms: one part of an integral type below eight bytes

`byte`, `char`, `short` and the four-byte types: `rangeOffsets` declines them (it takes the eight-byte
kinds only), so `codes` interns nothing and groups: `groupIdsColumn`, ids by first appearance. -/

/-- The integral sort kinds below eight bytes. -/
theorem small_int_width {t : QAtomicType} {k : Scan.Kind} (ht : orderKind t = some k)
    (hk : k = .u8 ∨ k = .i16 ∨ k = .i32) :
    t.width = some k.width ∧ denseWidth t = some k.width ∧ t ≠ .general ∧ t ≠ .boolean ∧ t ≠ .symbol ∧
      t ≠ .guid := by
  cases t <;> simp [orderKind] at ht <;> subst ht <;> simp_all [QAtomicType.width, denseWidth, Scan.Kind.width]

/-- **The atom a small integral column reads is its low `8·w` bits**: two raw words read as one element
    exactly when they agree below `2^(8w)`. -/
theorem small_int_read {t : QAtomicType} {k : Scan.Kind} (ht : orderKind t = some k)
    (hk : k = .u8 ∨ k = .i16 ∨ k = .i32) (d : Carrier t) (v u : UInt64) :
    (Carrier.of? t (.atom (Column.atomOfBits t v (small_int_width ht hk).2.2.1))).getD d =
        (Carrier.of? t (.atom (Column.atomOfBits t u (small_int_width ht hk).2.2.1))).getD d ↔
      v.toNat % 2 ^ (8 * k.width) = u.toNat % 2 ^ (8 * k.width) := by
  have e8 : ∀ a b : UInt64, a.toUInt8 = b.toUInt8 ↔ a.toNat % 2 ^ 8 = b.toNat % 2 ^ 8 := fun a b =>
    ⟨fun h => by simpa using congrArg UInt8.toNat h, fun h => UInt8.toNat_inj.1 (by simpa using h)⟩
  have e16 : ∀ a b : UInt64, a.toUInt16.toInt16 = b.toUInt16.toInt16 ↔ a.toNat % 2 ^ 16 = b.toNat % 2 ^ 16 :=
    fun a b => ⟨fun h => by simpa using congrArg (fun z : Int16 => z.toUInt16.toNat) h,
      fun h => congrArg UInt16.toInt16 (UInt16.toNat_inj.1 (by simpa using h))⟩
  have e32 : ∀ a b : UInt64, a.toUInt32.toInt32 = b.toUInt32.toInt32 ↔ a.toNat % 2 ^ 32 = b.toNat % 2 ^ 32 :=
    fun a b => ⟨fun h => by simpa using congrArg (fun z : Int32 => z.toUInt32.toNat) h,
      fun h => congrArg UInt32.toInt32 (UInt32.toNat_inj.1 (by simpa using h))⟩
  cases t <;> simp [orderKind] at ht <;> subst ht <;>
    simp only [Column.atomOfBits, Carrier.of?, Option.getD_some, Scan.Kind.width] <;>
    first | exact e8 v u | exact e16 v u | exact e32 v u | simp at hk

/-- A small integral column's element `i` is its raw word `i` read as an atom (`get_eq_raw`). -/
theorem small_int_get {t : QAtomicType} {k : Scan.Kind} (ht : orderKind t = some k)
    (hk : k = .u8 ∨ k = .i16 ∨ k = .i32) {n : USize} (x : Arr t n) (i : Fin n.toNat) :
    x.get i = (Carrier.of? t (.atom (Column.atomOfBits t ((Enc.raw t n x.enc).toList.getD i 0)
      (small_int_width ht hk).2.2.1))).getD default := by
  rw [Arr.get_ne x i (small_int_width ht hk).2.2.1, KernelWF.get_eq_raw (small_int_width ht hk).2.1 x.wf i.2]; rfl

/-- A small integral column is dense or Frame-of-Reference encoded (`Enc.WF`). -/
theorem small_int_enc {t : QAtomicType} {k : Scan.Kind} (ht : orderKind t = some k)
    (hk : k = .u8 ∨ k = .i16 ∨ k = .i32) {n : USize} (x : Arr t n) :
    (∃ b, x.enc = .bytes b) ∨ ∃ md pk, x.enc = .foR md pk := by
  have hwf := x.wf
  revert hwf
  cases x.enc with
  | bytes b => exact fun _ => .inl ⟨b, rfl⟩
  | foR md pk => exact fun _ => .inr ⟨md, pk, rfl⟩
  | _ => intro hwf; exfalso; rcases hk with rfl | rfl | rfl <;> cases t <;> simp_all [Enc.WF, orderKind, QAtomicType.width]

/-- **One part of a small integral side is coded by `groupIdsColumn`**, read by `Code.ofIds`. -/
theorem codes_small_int {t : QAtomicType} {k : Scan.Kind} (ht : orderKind t = some k)
    (hk : k = .u8 ∨ k = .i16 ∨ k = .i32) (x : Part (.atom t)) :
    ∃ p, groupIdsColumn t x.1 x.2.enc = some p ∧
      (Obj.codes (.atom t) #v[x])[0] = Code.ofIds (len p.2) x.1 p.1 := by
  obtain ⟨hw, -, hg, hb, hs, hgu⟩ := small_int_width ht hk
  have hne : ∀ d o ids, x.2.enc ≠ .enum d o ids := fun d o ids he => by
    have := x.2.wf; rw [he] at this; cases t <;> simp_all [Enc.WF]
  have hnb : ∀ b, x.2.enc ≠ .bits b := fun b he => by
    have := x.2.wf; rw [he] at this; cases t <;> simp_all [Enc.WF]
  have hns : ∀ b o, x.2.enc ≠ .syms b o := fun b o he => by
    have := x.2.wf; rw [he] at this; cases t <;> simp_all [Enc.WF]
  have hr : raze t #[x] = x := by unfold raze; simp [hg]
  have hsome := KernelWF.groupIdsColumn_isSome hg x.2.wf fun d o ids he => by
    exfalso; cases hc : x.2.enc <;> simp_all [Column.intern]
  refine ⟨_, (Option.some_get hsome).symm, ?_⟩
  -- at a concrete type and payload constructor every branch test of `codes` reduces
  obtain ⟨n, v, hv⟩ := x
  cases v <;> try exact hv.elim
  rename_i t' n' e a
  obtain ⟨h1, h2, hwf⟩ := hv
  subst h1 h2
  rcases hk with rfl | rfl | rfl <;> cases t' <;> simp [orderKind] at ht <;>
    cases e <;> simp [Enc.WF, QAtomicType.width] at hwf <;>
    simp [Obj.codes, Alg.codes, rangeOffsets, orderKind, raze, Column.intern, Code.cut, vmapM_one, Column.encodes, Arr.enc]

/-- `Code.ofIds` over ids packed by `Verify.groupOf g m` at the width of its class count reads `Verify.groupOf g m`, the
    lane of no bits included (`Code.ofLane`'s bitmap of zeros). -/
theorem ofIds_groupOf (g : Nat → UInt64) {m : Nat} (n : USize) (hm : m < 2 ^ 64) {ids fs : ByteArray}
    (hids : ids = Column.packIds (Column.idWidthOf (Verify.firstsOf g m).length) m (Verify.groupOf g m))
    (hfs : len fs = (Verify.firstsOf g m).length) {l : Nat} (hl : l < m) :
    Column.idAt (Code.ofIds (len fs) n ids).b (Code.ofIds (len fs) n ids).w l = Verify.groupOf g m l := by
  have hL : (Verify.firstsOf g m).length ≤ m := by simpa [Verify.firstsOf] using List.length_filter_le _ (List.range m)
  have hw : (Verify.firstsOf g m).length - 1 < 2 ^ Column.idWidthOf (Verify.firstsOf g m).length := by
    have h2 := Verify.lt_widthFor ((Verify.firstsOf g m).length - 1)
    have h3 := Verify.widthFor_le ((Verify.firstsOf g m).length - 1) (by omega)
    unfold Column.idWidthOf
    generalize Column.widthFor ((Verify.firstsOf g m).length - 1) = w at h2 h3 ⊢
    refine Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) ?_)
    unfold Column.laneWidth; repeat' split
    all_goals omega
  have hb : Verify.groupOf g m l < 2 ^ Column.idWidthOf (Verify.firstsOf g m).length := by
    have := Verify.groupOf_lt (g := g) hl; omega
  have hp := Verify.idAt_packIds (w := Column.idWidthOf (Verify.firstsOf g m).length) (Verify.laneWidth_cases _) hl hb
  rw [← hids] at hp
  unfold Code.ofIds Code.ofLane
  rw [hfs]
  split
  · next h0 =>
    have h0' : Column.idWidthOf (Verify.firstsOf g m).length = 0 := by simpa using h0
    rw [h0'] at hb
    simp only [idAt_one]
    have : Verify.groupOf g m l = 0 := by omega
    rw [this]; simp [Column.bitAt, KernelWF.ba_get?, Array.getElem?_replicate] <;> split <;> simp
  · exact hp

/-- Two classes of `Verify.groupOf g m` agree exactly when the keys do. -/
theorem groupOf_eq_groupOf {g : Nat → UInt64} {m i j : Nat} (hi : i < m) (hj : j < m) :
    Verify.groupOf g m i = Verify.groupOf g m j ↔ g i = g j := by
  rw [Verify.groupOf_eq_iff (g := g) hi (Verify.groupOf_lt (g := g) hj), Verify.groupOf_get (g := g) hj]

#print axioms codes_boolean_faithful
#print axioms codes_boolean_wf

end LeetQ.Rel.Alg
