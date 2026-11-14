/-
  What `Obj.codes` answers, read off its Lean body: the code column of a side identifies rows exactly
  (`Column.idAt c.b c.w i = Column.idAt c.b c.w j ↔ row i = row j`), and is well formed in the sense the
  code lemmas of `JoinSpec`/`MemberSpec` take (`w` a lane, `b` exactly `⌈n·w/8⌉` bytes, every code below
  `card`, `card` a `USize` below a byte).
-/
import LeetQ.Rel.KernelWF.JoinSpec
import LeetQ.Rel.KernelWF.PickSpec
import QLean.Verify.ScanOver

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
    simp [Obj.codes, Alg.codes, rangeOffsets, orderKind, raze, Column.intern, Code.cut, vmapM_one, Column.encodes, Arr.enc,
      KernelWF.bitsType]

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

/-- `groupIdsColumn` of a small integral payload: a dense one by `groupIds`, an encoded one by
    `groupIdsFoR`. -/
theorem groupIdsColumn_small_int {t : QAtomicType} {k : Scan.Kind} (ht : orderKind t = some k)
    (hk : k = .u8 ∨ k = .i16 ∨ k = .i32) (n : USize) :
    (∀ b, groupIdsColumn t n (.bytes b) = some (Order.groupIds k n b)) ∧
      ∀ md pk, groupIdsColumn t n (.foR md pk) = some (Order.groupIdsFoR k n md pk) := by
  rcases hk with rfl | rfl | rfl <;> cases t <;> simp [orderKind] at ht <;>
    exact ⟨fun b => by simp [groupIdsColumn, orderKind, Enc.bytesOf], fun md pk => by simp [groupIdsColumn, orderKind]⟩

/-- A small integral payload's raw word `i`: a dense one's `w` bytes at `i·w`, an encoded one's `foRBits`. -/
theorem raw_small_int {t : QAtomicType} {k : Scan.Kind} (ht : orderKind t = some k)
    (hk : k = .u8 ∨ k = .i16 ∨ k = .i32) {n : USize} {i : Nat} (hi : i < n.toNat) :
    (∀ b, (Enc.raw t n (.bytes b)).toList.getD i 0 = Column.bitsAt b (i * k.width) k.width) ∧
      ∀ md pk, (Enc.raw t n (.foR md pk)).toList.getD i 0 = Column.foRBits md pk (Column.blockStarts md) i := by
  rcases hk with rfl | rfl | rfl <;> cases t <;> simp [orderKind] at ht <;>
    exact ⟨fun b => by simp [Enc.raw, QAtomicType.width, Scan.Kind.width, List.getD_eq_getElem?_getD, hi],
      fun md pk => by simp [Enc.raw, QAtomicType.width, List.getD_eq_getElem?_getD, hi]⟩

/-- **One part of a small integral side: its codes are faithful.** Part `0`'s codes at `i` and `j` agree
    exactly when the rows do, the part dense or Frame-of-Reference encoded. -/
theorem codes_small_int_faithful {t : QAtomicType} {k : Scan.Kind} (ht : orderKind t = some k)
    (hk : k = .u8 ∨ k = .i16 ∨ k = .i32) (x : Part (.atom t)) {i j : Nat} (hi : i < x.1.toNat)
    (hj : j < x.1.toNat) :
    Column.idAt (Obj.codes (.atom t) #v[x])[0].b (Obj.codes (.atom t) #v[x])[0].w i =
        Column.idAt (Obj.codes (.atom t) #v[x])[0].b (Obj.codes (.atom t) #v[x])[0].w j ↔
      Vals.row x.2 ⟨i, hi⟩ = Vals.row x.2 ⟨j, hj⟩ := by
  obtain ⟨p, hp, hc⟩ := codes_small_int ht hk x
  have hn64 : x.1.toNat < 2 ^ 64 := Verify.usize_lt x.1
  have hk0 : k ≠ .bit := by rcases hk with rfl | rfl | rfl <;> decide
  have hkw : k.width ≤ 8 := by rcases hk with rfl | rfl | rfl <;> decide
  have hM : 2 ^ (8 * k.width) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [hc, Vals.row_atom, Vals.row_atom, small_int_get ht hk, small_int_get ht hk, small_int_read ht hk]
  obtain ⟨b, he⟩ | ⟨md, pk, he⟩ := small_int_enc ht hk x.2
  · rw [he, (groupIdsColumn_small_int ht hk x.1).1 b, Option.some_inj] at hp
    subst hp
    have hav : min x.1.toNat (k.avail b) = x.1.toNat := by
      have hs := x.2.wf; rw [he] at hs
      rcases hk with rfl | rfl | rfl <;> cases t <;> simp [orderKind] at ht <;>
        simp_all [Enc.WF, QAtomicType.width, Scan.Kind.avail, Scan.Kind.width]
    have hspec := Verify.groupIds_spec k x.1 b
    rw [hav] at hspec
    rw [ofIds_groupOf (Order.keyAt k b) x.1 hn64 hspec.1 (by rw [len_eq_ids, hspec.2]) hi,
      ofIds_groupOf (Order.keyAt k b) x.1 hn64 hspec.1 (by rw [len_eq_ids, hspec.2]) hj,
      groupOf_eq_groupOf hi hj, Verify.keyAt_eq_iff (by rcases hk with rfl | rfl | rfl <;> simp) b i j, he,
      (raw_small_int ht hk hi).1 b, (raw_small_int ht hk hj).1 b,
      Nat.mod_eq_of_lt (Verify.bitsAt_lt _ _ _ hkw), Nat.mod_eq_of_lt (Verify.bitsAt_lt _ _ _ hkw)]
    exact UInt64.toNat_inj.symm
  · rw [he, (groupIdsColumn_small_int ht hk x.1).2 md pk, Option.some_inj] at hp
    subst hp
    have hspec := Verify.groupIdsFoR_spec k hk0 x.1 md pk
    rw [ofIds_groupOf (foRKey k md pk) x.1 hn64 hspec.1 (by rw [len_eq_ids, hspec.2]) hi,
      ofIds_groupOf (foRKey k md pk) x.1 hn64 hspec.1 (by rw [len_eq_ids, hspec.2]) hj,
      groupOf_eq_groupOf hi hj, he, (raw_small_int ht hk hi).2 md pk, (raw_small_int ht hk hj).2 md pk]
    simp only [foRKey]
    have hrank : ∀ a c : UInt64, Order.rank k a = Order.rank k c ↔ a = c := fun a c => by
      rcases hk with rfl | rfl | rfl <;> simp only [Order.rank] <;> first | exact Iff.rfl | exact UInt64.xor_left_inj _
    rw [hrank]
    constructor
    · intro h; have := congrArg UInt64.toNat h
      simpa [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) hM)] using this
    · intro h; rw [h]

/-! ## Well-formedness of a grouping code -/

/-- **`packIds` at a lane of at least one bit is `⌈m·W/8⌉` bytes**: `KernelWF.packIds_size` at a nonzero lane,
    the shape the code lemmas state their widths in. -/
theorem packIds_size {W : Nat} (hW : laneOK(W))
    (m : Nat) (f : Nat → Nat) : (Column.packIds W m f).size = (m * W + 7) / 8 :=
  KernelWF.packIds_size (Or.inr hW) m f

/-- **A grouping code is well formed**: `Code.ofIds` over the ids `Verify.groupOf g n` packed at the width
    of its class count is a lane `1 … 64`, `n` codes in `⌈n·w/8⌉` bytes, every code below the class
    count, which a `USize` holds. -/
theorem ofIds_groupOf_wf (g : Nat → UInt64) (n : USize) {ids fs : ByteArray}
    (hids : ids = Column.packIds (Column.idWidthOf (Verify.firstsOf g n.toNat).length) n.toNat
      (Verify.groupOf g n.toNat))
    (hfs : len fs = (Verify.firstsOf g n.toNat).length) :
    let c := Code.ofIds (len fs) n ids
    laneOK(c.w) ∧ c.n = n ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  intro c
  have hL : (Verify.firstsOf g n.toNat).length ≤ n.toNat := by
    simpa [Verify.firstsOf] using List.length_filter_le _ (List.range n.toNat)
  have hcard : c.card = (Verify.firstsOf g n.toNat).length := by
    show (Code.ofIds (len fs) n ids).card = _; unfold Code.ofIds Code.ofLane; rw [hfs]; split <;> rfl
  have hn : c.n = n := by show (Code.ofIds (len fs) n ids).n = _; unfold Code.ofIds Code.ofLane; split <;> rfl
  have hid : ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card := fun i hi => by
    rw [hn] at hi
    rw [show Column.idAt c.b c.w i = _ from ofIds_groupOf g n (Verify.usize_lt n) hids hfs hi, hcard]
    exact Verify.groupOf_lt hi
  have hsh : ∀ d : Code, d = Code.ofIds (len fs) n ids →
      laneOK(d.w) ∧
      d.b.size = (d.n.toNat * d.w + 7) / 8 := by
    intro d hd; subst hd
    unfold Code.ofIds Code.ofLane
    by_cases h0 : (Column.idWidthOf (len fs) == 0) = true
    · rw [if_pos h0]; exact ⟨.inl rfl, by simp [ByteArray.size]⟩
    · rw [if_neg h0]
      have hw0 : Column.idWidthOf (len fs) ≠ 0 := by simpa using h0
      have hlane := Verify.laneWidth_cases (Column.widthFor (len fs - 1))
      have hw : laneOK(Column.idWidthOf (len fs)) := by
        unfold Column.idWidthOf at hw0 ⊢; omega
      refine ⟨hw, ?_⟩
      show ids.size = _
      rw [hids, ← hfs]; exact packIds_size hw _ _
  exact ⟨(hsh c rfl).1, hn, (hsh c rfl).2, fun _ => ⟨Nat.lt_of_le_of_lt (hcard ▸ hL) n.toNat_lt_size, hid⟩⟩

/-- **One part of a small integral side: its code is well formed** — dense or Frame-of-Reference
    encoded, `groupIdsColumn`'s ids read by `Code.ofIds`. -/
theorem codes_small_int_wf {t : QAtomicType} {k : Scan.Kind} (ht : orderKind t = some k)
    (hk : k = .u8 ∨ k = .i16 ∨ k = .i32) (x : Part (.atom t)) :
    let c := (Obj.codes (.atom t) #v[x])[0]
    laneOK(c.w) ∧ c.n = x.1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  obtain ⟨p, hp, hc⟩ := codes_small_int ht hk x
  have hk0 : k ≠ .bit := by rcases hk with rfl | rfl | rfl <;> decide
  rw [hc]
  obtain ⟨b, he⟩ | ⟨md, pk, he⟩ := small_int_enc ht hk x.2
  · rw [he, (groupIdsColumn_small_int ht hk x.1).1 b, Option.some_inj] at hp
    subst hp
    have hav : min x.1.toNat (k.avail b) = x.1.toNat := by
      have hs := x.2.wf; rw [he] at hs
      rcases hk with rfl | rfl | rfl <;> cases t <;> simp [orderKind] at ht <;>
        simp_all [Enc.WF, QAtomicType.width, Scan.Kind.avail, Scan.Kind.width]
    have hspec := Verify.groupIds_spec k x.1 b
    rw [hav] at hspec
    exact ofIds_groupOf_wf (Order.keyAt k b) x.1 hspec.1 (by rw [len_eq_ids, hspec.2])
  · rw [he, (groupIdsColumn_small_int ht hk x.1).2 md pk, Option.some_inj] at hp
    subst hp
    have hspec := Verify.groupIdsFoR_spec k hk0 x.1 md pk
    exact ofIds_groupOf_wf (foRKey k md pk) x.1 hspec.1 (by rw [len_eq_ids, hspec.2])

/-! ## Atoms: the eight-byte integral types, `rangeOffsets`

`long`, `timestamp`, `timespan`, dense or Frame-of-Reference encoded: every part's elements as offsets from
the joint least element `base`, the null at `card - 1`. -/

/-- `mapM` in `Option` over a list that answers: one answer per element, in place. -/
theorem list_mapM_some {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = some ys →
      ∃ _ : ys.length = l.length, ∀ i (hi : i < l.length), f l[i] = some ys[i]
  | [], ys, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | a :: l, ys, h => by
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    obtain ⟨hl, hall⟩ := list_mapM_some hbs
    refine ⟨by simp [hl], fun i hi => ?_⟩
    cases i with
    | zero => simpa using hb
    | succ i => simpa using hall i (by simpa using hi)

/-- `mapM` in `Option` over an array that answers: one answer per element, in place. -/
theorem arr_mapM_some {α β : Type} {f : α → Option β} {xs : Array α} {ys : Array β} (h : xs.mapM f = some ys) :
    ∃ _ : ys.size = xs.size, ∀ k (hk : k < xs.size), f xs[k] = some ys[k] := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : xs.toList.mapM f with
  | none => rw [hl] at h; simp at h
  | some l =>
    rw [hl] at h
    have hy : l.toArray = ys := by simpa using h
    subst hy
    obtain ⟨hlen, hall⟩ := list_mapM_some hl
    exact ⟨by simpa using hlen, fun k hk => by simpa using hall k (by simpa using hk)⟩

/-- `mapM` in `Option` over a vector that answers: one answer per element, in place. -/
theorem vec_mapM_some {α β : Type} {p : Nat} {f : α → Option β} {xs : Vector α p} {ys : Vector β p}
    (h : xs.mapM f = some ys) {k : Nat} (hk : k < p) : f xs[k] = some ys[k] := by
  have e : xs.toArray.mapM f = some ys.toArray := by rw [← Vector.toArray_mapM, h]; rfl
  simpa using (arr_mapM_some e).2 k (by simpa using hk)

/-- A left fold whose step stays at or below both operands ends at or below its seed and every element. -/
theorem foldl_le {g : Int64 → Int64 → Int64} (hg : ∀ a y, (g a y).toInt ≤ a.toInt ∧ (g a y).toInt ≤ y.toInt) :
    ∀ (l : List Int64) (a : Int64), (l.foldl g a).toInt ≤ a.toInt ∧ ∀ x ∈ l, (l.foldl g a).toInt ≤ x.toInt
  | [], a => by simp
  | y :: l, a => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldl_le hg l (g a y)
    have := hg a y
    refine ⟨by omega, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · omega
    · exact h2 x hx

/-- A left fold whose step stays at or above both operands ends at or above its seed and every element. -/
theorem foldl_ge {g : Int64 → Int64 → Int64} (hg : ∀ a y, a.toInt ≤ (g a y).toInt ∧ y.toInt ≤ (g a y).toInt) :
    ∀ (l : List Int64) (a : Int64), a.toInt ≤ (l.foldl g a).toInt ∧ ∀ x ∈ l, x.toInt ≤ (l.foldl g a).toInt
  | [], a => by simp
  | y :: l, a => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldl_ge hg l (g a y)
    have := hg a y
    refine ⟨by omega, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · omega
    · exact h2 x hx

theorem min_toInt_le (a y : Int64) : (min a y).toInt ≤ a.toInt ∧ (min a y).toInt ≤ y.toInt := by
  by_cases h : a ≤ y
  · rw [show min a y = a from if_pos h]; exact ⟨Int.le_refl _, Int64.le_iff_toInt_le.1 h⟩
  · rw [show min a y = y from if_neg h]; have := mt Int64.le_iff_toInt_le.2 h; exact ⟨by omega, Int.le_refl _⟩

theorem max_toInt_ge (a y : Int64) : a.toInt ≤ (max a y).toInt ∧ y.toInt ≤ (max a y).toInt := by
  by_cases h : a ≤ y
  · rw [show max a y = y from if_pos h]; exact ⟨Int64.le_iff_toInt_le.1 h, Int.le_refl _⟩
  · rw [show max a y = a from if_neg h]; have := mt Int64.le_iff_toInt_le.2 h; exact ⟨Int.le_refl _, by omega⟩

/-- **`overList lesser` is at or below every element that is not the null**, and `greater` at or above. -/
theorem overList_bounds {nul seed x : Int64} {xs : List Int64} (hx : x ∈ xs) (hn : x ≠ nul) :
    (Verify.overList .lesser nul seed xs).toInt ≤ x.toInt ∧ x.toInt ≤ (Verify.overList .greater nul seed xs).toInt := by
  have hm : x ∈ xs.filter fun y => Coc.Over.boolCast .lesser || y != nul := List.mem_filter.2 ⟨hx, by simp [hn, Coc.Over.boolCast]⟩
  have hM : x ∈ xs.filter fun y => Coc.Over.boolCast .greater || y != nul := List.mem_filter.2 ⟨hx, by simp [hn, Coc.Over.boolCast]⟩
  refine ⟨(foldl_le (fun a y => ?_) _ seed).2 x hm, (foldl_ge (fun a y => ?_) _ seed).2 x hM⟩
  · simp only [Coc.Over.step]; split
    · next h => exact ⟨Int.le_refl _, Int.le_of_lt (Int64.lt_iff_toInt_lt.1 h)⟩
    · next h => have := mt Int64.lt_iff_toInt_lt.2 h; exact ⟨by omega, Int.le_refl _⟩
  · simp only [Coc.Over.step]; split
    · next h => exact ⟨Int.le_refl _, Int.le_of_lt (Int64.lt_iff_toInt_lt.1 h)⟩
    · next h => have := mt Int64.lt_iff_toInt_lt.2 h; exact ⟨by omega, Int.le_refl _⟩

/-- An eight-byte integral type's facts: its layout is eight bytes, its payload dense or encoded, its
    encoded null `nul`. -/
theorem long_facts {t : QAtomicType} (ht : orderKind t = some .i64) :
    t.width = some 8 ∧ denseWidth t = some 8 ∧ t ≠ .general ∧ Coc.nullOf t = some nul ∧ Column.encodes t = true := by
  cases t <;> simp [orderKind] at ht <;> exact ⟨rfl, rfl, by decide, rfl, rfl⟩

/-- An eight-byte integral payload is dense or Frame-of-Reference encoded (`Enc.WF`). -/
theorem long_enc {t : QAtomicType} (ht : orderKind t = some .i64) {n : USize} {e : Enc} (hwf : Enc.WF t n e) :
    (∃ b, e = .bytes b ∧ b.size = n.toNat * 8) ∨ ∃ md pk, e = .foR md pk := by
  cases e with
  | bytes b => left; refine ⟨b, rfl, ?_⟩; cases t <;> simp [orderKind] at ht <;> simpa [Enc.WF, QAtomicType.width] using hwf
  | foR md pk => exact .inr ⟨md, pk, rfl⟩
  | _ => exfalso; cases t <;> simp [orderKind] at ht <;> simp [Enc.WF] at hwf

/-- An eight-byte integral payload's raw word `i`: a dense one's eight bytes at `8i`, an encoded one's
    `foRBits`. -/
theorem raw_long {t : QAtomicType} (ht : orderKind t = some .i64) {n : USize} {i : Nat} (hi : i < n.toNat) :
    (∀ b, (Enc.raw t n (.bytes b)).toList.getD i 0 = Column.bitsAt b (i * 8) 8) ∧
      ∀ md pk, (Enc.raw t n (.foR md pk)).toList.getD i 0 = Column.foRBits md pk (Column.blockStarts md) i := by
  cases t <;> simp [orderKind] at ht <;>
    exact ⟨fun b => by simp [Enc.raw, QAtomicType.width, List.getD_eq_getElem?_getD, hi],
      fun md pk => by simp [Enc.raw, QAtomicType.width, List.getD_eq_getElem?_getD, hi]⟩

/-- **An eight-byte integral column's element is its raw word read as an `Int64`.** -/
theorem long_row_eq {t : QAtomicType} (ht : orderKind t = some .i64) {n m : USize} (x : Arr t n) (y : Arr t m)
    (i : Fin n.toNat) (j : Fin m.toNat) :
    x.get i = y.get j ↔ ((Enc.raw t n x.enc).toList.getD i 0).toInt64 = ((Enc.raw t m y.enc).toList.getD j 0).toInt64 := by
  obtain ⟨-, hd, hg, -, -⟩ := long_facts ht
  rw [Arr.get_ne x i hg, Arr.get_ne y j hg, KernelWF.get_eq_raw hd x.wf i.2, KernelWF.get_eq_raw hd y.wf j.2]
  cases t <;> simp [orderKind] at ht <;> simp [Column.atomOfBits, Carrier.of?]

/-- A shift by `-base` of an element `x` with `base ≤ x < base + 2^63`: the integer difference, not the null. -/
theorem shift_toInt {x base : Int64} (hb : base ≠ nul) (h1 : base.toInt ≤ x.toInt) (h2 : x.toInt - base.toInt < 2 ^ 63) :
    (x + -base).toInt = x.toInt - base.toInt ∧ x + -base ≠ nul := by
  have hbl := Int64.le_toInt base; have hbu := Int64.toInt_lt base
  have hxl := Int64.le_toInt x; have hxu := Int64.toInt_lt x
  have hbn : base.toInt ≠ -2 ^ 63 := fun h => hb (Int64.toInt_inj.1 (by rw [h]; decide))
  have hs : (x + -base).toInt = x.toInt - base.toInt := by
    rw [Int64.toInt_add, Int64.toInt_neg]
    simp only [Int.bmod]; split <;> split <;> omega
  refine ⟨hs, fun h => ?_⟩
  have := congrArg Int64.toInt h; rw [hs] at this
  have : nul.toInt = -2 ^ 63 := by decide
  omega

/-- **One part's `rangeOffsets` code**: `enumIds` over a payload holding each element `x i` shifted by
    `-base` (the null kept), every element that is not the null in `[base, base + card - 2]`, accepted
    when the kernel reports every row in range: `n` codes at the lane `w`, the offset `x i - base`, the null
    at `card - 1`. -/
theorem enum_part {n : USize} {card w : Nat} {base : Int64} {b' : ByteArray} (x : Nat → Int64) {c : Code}
    (hcard : card ≤ 2 ^ 63 + 1) (hcU : card ≤ USize.size) (hc2 : 2 ≤ card) (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (hd : card ≤ 2 ^ w)
    (hb : base ≠ nul)
    (hv : ∀ i < n.toNat, (Column.bitsAt b' (i * 8) 8).toInt64 = if x i = nul then nul else x i + -base)
    (hr : ∀ i < n.toNat, x i ≠ nul → base.toInt ≤ (x i).toInt ∧ (x i).toInt - base.toInt + 2 ≤ card)
    (h : (if (enumIds n card.toUSize (card - 1).toUSize w.toUSize b').2 != n then none
      else some (⟨w, n, card, (enumIds n card.toUSize (card - 1).toUSize w.toUSize b').1⟩ : Code)) = some c) :
    c.n = n ∧ c.card = card ∧ c.w = w ∧ c.b.size = (n.toNat * w + 7) / 8 ∧
      ∀ i < n.toNat, Column.idAt c.b c.w i = if x i = nul then card - 1 else ((x i).toInt - base.toInt).toNat := by
  have hS : 2 ^ 32 ≤ USize.size := USize.le_size
  have hok : (enumIds n card.toUSize (card - 1).toUSize w.toUSize b').2 = n := by
    cases hb2 : ((enumIds n card.toUSize (card - 1).toUSize w.toUSize b').2 != n) with
    | true => rw [if_pos hb2] at h; cases h
    | false => simpa using hb2
  rw [if_neg (by simpa using hok), Option.some_inj] at h
  subst h
  have hwu : w.toUSize.toNat = w := USize.toNat_ofNat_of_lt'
    (Nat.lt_of_lt_of_le (by rcases hw with rfl | rfl | rfl | rfl <;> decide : w < 2 ^ 32) hS)
  have hcu : card.toUSize.toNat ≤ card := by
    show (USize.ofNat card).toNat ≤ card
    first
      | (rw [USize.toNat_ofNat']; exact Nat.mod_le _ _)
      | (simp only [USize.ofNat, USize.toNat, UInt64.ofNat, BitVec.toNat_ofNat]; exact Nat.mod_le _ _)
      | (simp [USize.toNat_ofNat]; omega)
      | (simp; exact Nat.mod_le _ _)
  have hc1 : (card - 1).toUSize.toNat = card - 1 := USize.toNat_ofNat_of_lt' (by omega)
  refine ⟨rfl, rfl, rfl, ?_, fun i hi => ?_⟩
  · show (enumIds n card.toUSize (card - 1).toUSize w.toUSize b').1.size = _
    simp only [enumIds]; rw [hwu]
    exact packIds_size (by rcases hw with rfl | rfl | rfl | rfl <;> simp) _ _
  · have e := Verify.enumIds_idAt n card.toUSize (card - 1).toUSize w.toUSize b'
      (by rw [hwu]; rcases hw with rfl | rfl | rfl | rfl <;> simp) (by rw [hwu]; omega)
      (by rw [hc1, hwu]; omega) hok hi
    rw [hwu] at e; show Column.idAt _ w i = _; rw [e, hv i hi, hc1]
    by_cases hx : x i = nul
    · simp only [hx, if_true, nul]
    · obtain ⟨r1, r2⟩ := hr i hi hx
      obtain ⟨hs, hne⟩ := shift_toInt hb r1 (by omega)
      simp only [hx, if_false]
      rw [if_neg (by simpa [nul] using hne), hs]

/-- Negation keeps every long but the null off the null. -/
theorem neg_ne_nul {B : Int64} (hB : B ≠ nul) : -B ≠ nul := fun h => by
  have hbl := Int64.le_toInt B; have hbu := Int64.toInt_lt B
  have hbn : B.toInt ≠ -2 ^ 63 := fun e => hB (Int64.toInt_inj.1 (by rw [e]; decide))
  have := congrArg Int64.toInt h
  rw [Int64.toInt_neg, show nul.toInt = -2 ^ 63 by decide] at this
  simp only [Int.bmod] at this; split at this <;> omega

/-- A dense part's shifted payload holds each element shifted by `-B`, the null kept. -/
theorem shift_bytes {n : USize} {b : ByteArray} {B : Int64} (hB : B ≠ nul) {i : Nat} (hi : i < n.toNat) :
    (Column.bitsAt (if B == 0 then b else Kernel.Ew.val Ew.add Ew.i64 Ew.va nul b (one (-B).toUInt64) n) (i * 8) 8).toInt64 =
      if (Column.bitsAt b (i * 8) 8).toInt64 = nul then nul else (Column.bitsAt b (i * 8) 8).toInt64 + -B := by
  have hnB := neg_ne_nul hB
  by_cases h0 : (B == 0) = true
  · rw [if_pos h0]; have : B = 0 := by simpa using h0
    subst this; split <;> simp_all
  · rw [if_neg h0]
    have hu : n.toNat.toUSize = n := USize.toNat_inj.1 (USize.toNat_ofNat_of_lt' n.toNat_lt_size)
    have e := shift_elem b (-B) n.toNat_lt_size hi
    rw [hu] at e; rw [e]; simp [hnB]

/-- An encoded part's payload, decoded (and shifted by `-B` where `B ≠ 0`), holds each `foRBits` element
    shifted by `-B`, the null kept. -/
theorem shift_foR {n : USize} {md pk m q : ByteArray} {B : Int64} (hB : B ≠ nul)
    (h : (if B == 0 then some (md, pk) else Ew.foRShift false (-B) md pk n) = some (m, q)) {i : Nat} (hi : i < n.toNat) :
    (Column.bitsAt (Coc.decode 8 m q n) (i * 8) 8).toInt64 =
      if (Column.foRBits md pk (Column.blockStarts md) i).toInt64 = nul then nul
      else (Column.foRBits md pk (Column.blockStarts md) i).toInt64 + -B := by
  have hnB := neg_ne_nul hB
  have h8 : (8 : USize).toNat = 8 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have hm : ∀ v : UInt64, UInt64.ofNat (v.toNat % 2 ^ (8 * 8)) = v := fun v => by
    rw [Nat.mod_eq_of_lt (by simpa using v.toNat_lt)]; exact UInt64.ofNat_toNat
  have hdec : ∀ md pk, Column.bitsAt (Coc.decode 8 md pk n) (i * 8) 8 = Column.foRBits md pk (Column.blockStarts md) i :=
    fun md pk => by have := (Verify.decodeW 8 (by rw [h8]; decide) md pk n).2 i hi; rw [h8, hm] at this; exact this
  by_cases h0 : (B == 0) = true
  · rw [if_pos h0, Option.some_inj, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have : B = 0 := by simpa using h0
    subst this; rw [hdec]; split <;> simp_all
  · rw [if_neg h0] at h
    have hs := Verify.foRShift_spec false (-B) md pk n m q h
    simp only [Bool.false_eq_true, if_false] at hs
    have hsz : (Coc.decode 8 m q n).size = 8 * n.toNat := by
      have := (Verify.decodeW 8 (by rw [h8]; decide) m q n).1; rw [h8] at this; exact this
    have hvz := Verify.val_size8 Ew.add Ew.va Int64.minValue (Coc.decode 8 md pk n)
      (Column.pushBits ByteArray.empty (-B).toUInt64 8) n
    have e := congrArg (fun l => l[i]?) hs
    simp only [Verify.elemsW, List.getElem?_map] at e
    rw [hsz, ← hvz, Nat.mul_div_cancel_left _ (by decide), List.getElem?_range hi] at e
    simp only [Option.map_some, Option.some.injEq] at e
    have hu : n.toNat.toUSize = n := USize.toNat_inj.1 (USize.toNat_ofNat_of_lt' n.toNat_lt_size)
    have e2 := shift_elem (Coc.decode 8 md pk n) (-B) n.toNat_lt_size hi
    rw [hu, hdec] at e2
    rw [e]; exact e2.trans (by simp [hnB])

/-- The byte layout `codeKind` picks holds its count, and is at most four bytes exactly when the count is
    at most `2^32`. -/
theorem codeKind_facts (c : Nat) (hc : c ≤ 2 ^ 64) :
    c ≤ 2 ^ (8 * (codeKind c).width) ∧ ((codeKind c).width = 1 ∨ (codeKind c).width = 2 ∨
      (codeKind c).width = 4 ∨ (codeKind c).width = 8) ∧ ((codeKind c).width ≤ 4 → c ≤ 2 ^ 32) := by
  unfold codeKind
  by_cases h1 : c ≤ 2 ^ 8
  · rw [if_pos h1]; exact ⟨h1, .inl rfl, fun _ => Nat.le_trans h1 (by decide)⟩
  rw [if_neg h1]
  by_cases h2 : c ≤ 2 ^ 16
  · rw [if_pos h2]; exact ⟨h2, .inr (.inl rfl), fun _ => Nat.le_trans h2 (by decide)⟩
  rw [if_neg h2]
  by_cases h3 : c ≤ 2 ^ 32
  · rw [if_pos h3]; exact ⟨h3, .inr (.inr (.inl rfl)), fun _ => h3⟩
  rw [if_neg h3]; exact ⟨hc, .inr (.inr (.inr rfl)), fun h => absurd h (by decide)⟩

/-- **`rangeOffsets`' codes, part by part**: one `base` and `card` for every part; part `k`'s code at row
    `i` is the offset of the row's element from `base`, the null at `card - 1`, every element that is not
    the null in `[base, base + card - 2]`; the lane `8 … 64` bits wide, `⌈n·w/8⌉` bytes. -/
theorem rangeOffsets_spec {a : QAtomicType} (ha : orderKind a = some .i64) {p : Nat} {cs : Vector (USize × Enc) p}
    {total : Nat} {os : Vector Code p} (hwf : ∀ k (hk : k < p), Enc.WF a cs[k].1 cs[k].2)
    (h : rangeOffsets a cs total = some os) :
    ∃ base : Int64, ∃ card : Nat, ∀ k (hk : k < p),
      os[k].n = cs[k].1 ∧ os[k].card = card ∧ (os[k].w = 8 ∨ os[k].w = 16 ∨ os[k].w = 32 ∨ os[k].w = 64) ∧
      os[k].b.size = (cs[k].1.toNat * os[k].w + 7) / 8 ∧
      ∀ i < cs[k].1.toNat,
        Column.idAt os[k].b os[k].w i = (if ((Enc.raw a cs[k].1 cs[k].2).toList.getD i 0).toInt64 = nul
          then card - 1 else (((Enc.raw a cs[k].1 cs[k].2).toList.getD i 0).toInt64.toInt - base.toInt).toNat) ∧
        (((Enc.raw a cs[k].1 cs[k].2).toList.getD i 0).toInt64 ≠ nul →
          base.toInt ≤ ((Enc.raw a cs[k].1 cs[k].2).toList.getD i 0).toInt64.toInt ∧
          ((Enc.raw a cs[k].1 cs[k].2).toList.getD i 0).toInt64.toInt - base.toInt + 2 ≤ card) := by
  obtain ⟨-, -, -, hnul, henc⟩ := long_facts ha
  unfold rangeOffsets at h
  rw [if_neg (by simp [ha, henc])] at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  rename_i los hlos
  split at h
  · exact absurd h (by simp)
  rename_i his hhis
  generalize hlo : los.foldl min Int64.maxValue = lo at h
  generalize hhi : his.foldl max (Int64.minValue + 1) = hi at h
  split at h
  · exact absurd h (by simp)
  rename_i hc
  split at h
  · exact absurd h (by simp)
  rename_i hkw
  obtain ⟨B, hB⟩ : ∃ B, B = (if (decide (0 ≤ lo) && (codeKind (hi.toInt - Int64.toInt 0 + 2).toNat).width ==
      (codeKind (hi.toInt - lo.toInt + 2).toNat).width) = true then (0 : Int64) else lo) := ⟨_, rfl⟩
  rw [← hB] at h
  split at h
  · exact absurd h (by simp)
  rename_i hcB
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hcB
  obtain ⟨hcA, hcU⟩ := hcB
  have hlonul : lo ≠ nul := fun e => hc (by simp [e])
  have hhilo : lo.toInt ≤ hi.toInt := by
    have : ¬ hi < lo := fun e => hc (by simp [e])
    have := mt Int64.lt_iff_toInt_lt.2 this; omega
  have hloS := Int64.le_toInt lo; have hhiS := Int64.toInt_lt hi
  have hlo1 : -2 ^ 63 < lo.toInt := by
    have hn : nul.toInt = -2 ^ 63 := by decide
    have : lo.toInt ≠ nul.toInt := fun e => hlonul (Int64.toInt_inj.1 e)
    omega
  have hspan := codeKind_facts (hi.toInt - lo.toInt + 2).toNat (by omega)
  -- `B` is `lo`, or `0` below `lo` at the same lane
  have hBc : B ≠ nul ∧ B.toInt ≤ lo.toInt ∧
      (hi.toInt - B.toInt + 2).toNat ≤ 2 ^ (8 * (codeKind (hi.toInt - lo.toInt + 2).toNat).width) := by
    rw [hB]; split
    · next h0 =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h0
      have h0l := Int64.le_iff_toInt_le.1 h0.1
      have hz : (0 : Int64).toInt = 0 := by decide
      have h0w := h0.2
      try simp only [hz, Int.sub_zero] at h0w h0l ⊢
      have h0s := codeKind_facts (hi.toInt + 2).toNat (by omega)
      rw [h0w] at h0s
      refine ⟨by decide, by omega, h0s.1⟩
    · exact ⟨hlonul, Int.le_refl _, hspan.1⟩
  obtain ⟨hBn, hBlo, hcw⟩ := hBc
  refine ⟨B, (hi.toInt - B.toInt + 2).toNat, fun k hk => ?_⟩
  have hp := vec_mapM_some h hk
  obtain ⟨hls, hlall⟩ := arr_mapM_some hlos
  obtain ⟨hhs, hhall⟩ := arr_mapM_some hhis
  have hkl : k < los.size := by rw [hls]; simpa using hk
  have hkh : k < his.size := by rw [hhs]; simpa using hk
  have hlk := hlall k (by simpa using hk)
  have hhk := hhall k (by simpa using hk)
  simp only [Vector.getElem_toArray] at hlk hhk
  have hlok : lo.toInt ≤ (los[k]'hkl).toInt := by
    rw [← hlo, ← Array.foldl_toList]
    exact (foldl_le min_toInt_le los.toList _).2 _ (Array.getElem_mem_toList _)
  have hhik : (his[k]'hkh).toInt ≤ hi.toInt := by
    rw [← hhi, ← Array.foldl_toList]
    exact (foldl_ge max_toInt_ge his.toList _).2 _ (Array.getElem_mem_toList _)
  have hw : 8 * (codeKind (hi.toInt - lo.toInt + 2).toNat).width = 8 ∨
      8 * (codeKind (hi.toInt - lo.toInt + 2).toNat).width = 16 ∨
      8 * (codeKind (hi.toInt - lo.toInt + 2).toNat).width = 32 ∨
      8 * (codeKind (hi.toInt - lo.toInt + 2).toNat).width = 64 := by omega
  have hc2 : 2 ≤ (hi.toInt - B.toInt + 2).toNat := by omega
  have hrng : ∀ x : Int64, (los[k]'hkl).toInt ≤ x.toInt → x.toInt ≤ (his[k]'hkh).toInt →
      B.toInt ≤ x.toInt ∧ x.toInt - B.toInt + 2 ≤ (hi.toInt - B.toInt + 2).toNat := fun x h1 h2 => by omega
  rcases long_enc ha (hwf k hk) with ⟨b, he, hbs⟩ | ⟨md, pk, he⟩
  · rw [he] at hp hlk hhk ⊢
    dsimp only at hp hlk hhk
    rw [Option.some_inj] at hlk hhk
    have hsig : ∀ i, Ew.signed Ew.i64 (Ew.elem Ew.i64 b i) = (Column.bitsAt b (i * 8) 8).toInt64 := fun i => by
      have hw8 : Ew.width Ew.i64 = 8 := by decide
      simp only [Ew.signed, Ew.elem, hw8,
        show (Ew.i64 == Ew.u8) = false from rfl, show (Ew.i64 == Ew.i16) = false from rfl,
        show (Ew.i64 == Ew.i32) = false from rfl, Bool.false_eq_true, if_false]
    have hraw := fun i (hi : i < cs[k].1.toNat) => (raw_long ha hi).1 b
    have hbnd : ∀ i < cs[k].1.toNat, (Column.bitsAt b (i * 8) 8).toInt64 ≠ nul →
        B.toInt ≤ (Column.bitsAt b (i * 8) 8).toInt64.toInt ∧
          (Column.bitsAt b (i * 8) 8).toInt64.toInt - B.toInt + 2 ≤ (hi.toInt - B.toInt + 2).toNat := fun i hi hx => by
      have hib : i < b.size / Ew.width Ew.i64 := by rw [hbs, show Ew.width Ew.i64 = 8 by decide]; omega
      have hb := overBytes_bounds Ew.i64 nul b hib (by rw [hsig]; exact hx)
      rw [hsig, hlk, hhk] at hb
      exact hrng _ (Int64.le_iff_toInt_le.1 hb.1) (Int64.le_iff_toInt_le.1 hb.2)
    obtain ⟨h1, h2, h3, h4, h5⟩ := enum_part (fun i => (Column.bitsAt b (i * 8) 8).toInt64) hcA hcU hc2 hw hcw hBn
      (fun i hi => shift_bytes hBn hi) hbnd hp
    refine ⟨h1, h2, by rw [h3]; exact hw, by rw [h4, h3], fun i hi => ?_⟩
    rw [hraw i hi]
    exact ⟨h5 i hi, hbnd i hi⟩
  · rw [he] at hp hlk hhk ⊢
    dsimp only at hp hlk hhk
    simp only [overFoR, hnul, Option.map_some, Option.some_inj] at hlk hhk
    rw [Verify.over_eq] at hlk hhk
    cases hs : (if B == 0 then some (md, pk) else Ew.foRShift false (-B) md pk cs[k].1) with
    | none => rw [hs] at hp; simp at hp
    | some r =>
      obtain ⟨m, q⟩ := r
      rw [hs] at hp
      dsimp only [Option.bind] at hp
      simp only [enumIdsFoR] at hp
      have hraw := fun i (hi : i < cs[k].1.toNat) => (raw_long ha hi).2 md pk
      have hbnd : ∀ i < cs[k].1.toNat, (Column.foRBits md pk (Column.blockStarts md) i).toInt64 ≠ nul →
          B.toInt ≤ (Column.foRBits md pk (Column.blockStarts md) i).toInt64.toInt ∧
            (Column.foRBits md pk (Column.blockStarts md) i).toInt64.toInt - B.toInt + 2 ≤
              (hi.toInt - B.toInt + 2).toNat := fun i hi hx => by
        have hmem : (Column.foRBits md pk (Column.blockStarts md) i).toInt64 ∈ (List.range cs[k].1.toNat).map
            (fun i => (Column.foRBits md pk (Column.blockStarts md) i).toInt64) := List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
        have hb := overList_bounds (seed := Coc.Over.seed .lesser nul) hmem hx
        have hb' := overList_bounds (seed := Coc.Over.seed .greater nul) hmem hx
        rw [hlk] at hb; rw [hhk] at hb'
        exact hrng _ hb.1 hb'.2
      obtain ⟨h1, h2, h3, h4, h5⟩ := enum_part (fun i => (Column.foRBits md pk (Column.blockStarts md) i).toInt64)
        hcA hcU hc2 hw hcw hBn (fun i hi => shift_foR hBn hs hi) hbnd hp
      refine ⟨h1, h2, by rw [h3]; exact hw, by rw [h4, h3], fun i hi => ?_⟩
      rw [hraw i hi]
      exact ⟨h5 i hi, hbnd i hi⟩

/-- Offsets from one `base`, the null at `card - 1` and every other value below `card - 1`, are equal
    exactly where the values are. -/
theorem offset_iff {base x y : Int64} {card : Nat}
    (hx : x ≠ nul → base.toInt ≤ x.toInt ∧ x.toInt - base.toInt + 2 ≤ card)
    (hy : y ≠ nul → base.toInt ≤ y.toInt ∧ y.toInt - base.toInt + 2 ≤ card) :
    (if x = nul then card - 1 else (x.toInt - base.toInt).toNat) =
        (if y = nul then card - 1 else (y.toInt - base.toInt).toNat) ↔ x = y := by
  by_cases h1 : x = nul <;> by_cases h2 : y = nul
  · rw [h1, h2]; simp
  · rw [if_pos h1, if_neg h2]; obtain ⟨a, b⟩ := hy h2
    exact ⟨fun _ => by omega, fun e => (h2 (by rw [← e]; exact h1)).elim⟩
  · rw [if_neg h1, if_pos h2]; obtain ⟨a, b⟩ := hx h1
    exact ⟨fun _ => by omega, fun e => (h1 (by rw [e]; exact h2)).elim⟩
  · rw [if_neg h1, if_neg h2]; obtain ⟨a, b⟩ := hx h1; obtain ⟨c, d⟩ := hy h2
    exact ⟨fun e => Int64.toInt_inj.1 (by omega), fun e => by rw [e]⟩

/-- Where `rangeOffsets` answers, it is the code of an eight-byte integral column: no long payload is
    `bits`. -/
theorem codes_long_eq {t : QAtomicType} (ht : orderKind t = some .i64) {p : Nat} (cs : Vector (Part (.atom t)) p)
    (hp : 0 < p) {os : Vector Code p}
    (hro : rangeOffsets t (cs.map fun c => Arr.part c.2) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) = some os) :
    Obj.codes (.atom t) cs = os := by
  obtain ⟨-, -, hg, -, -⟩ := long_facts ht
  show Alg.codes t cs = os
  unfold codes; rw [dif_neg hg]
  split
  · next bs hbs =>
    have := vec_mapM_some hbs hp
    rcases long_enc ht cs[0].2.wf with ⟨b, he, -⟩ | ⟨md, pk, he⟩ <;> simp [he] at this
  · dsimp only; rw [hro]

/-- **An eight-byte integral column's codes, where `rangeOffsets` answers, are
    equal exactly where the values are, across parts.** -/
theorem codes_long_faithful {t : QAtomicType} (ht : orderKind t = some .i64) {p : Nat}
    (cs : Vector (Part (.atom t)) p) {os : Vector Code p}
    (hro : rangeOffsets t (cs.map fun c => Arr.part c.2) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) = some os)
    {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < cs[k].1.toNat) (hj : j < cs[l].1.toNat) :
    Column.idAt (Obj.codes (.atom t) cs)[k].b (Obj.codes (.atom t) cs)[k].w i =
        Column.idAt (Obj.codes (.atom t) cs)[l].b (Obj.codes (.atom t) cs)[l].w j ↔
      Vals.row cs[k].2 ⟨i, hi⟩ = Vals.row cs[l].2 ⟨j, hj⟩ := by
  obtain ⟨base, card, hs⟩ := rangeOffsets_spec ht
    (fun k hk => by simp only [Vector.getElem_map, Arr.part]; exact cs[k].2.wf) hro
  rw [codes_long_eq ht cs (by omega) hro, Vals.row_atom, Vals.row_atom, long_row_eq ht]
  obtain ⟨-, -, -, -, hk'⟩ := hs k hk; obtain ⟨-, -, -, -, hl'⟩ := hs l hl
  simp only [Vector.getElem_map, Arr.part] at hk' hl'
  rw [(hk' i hi).1, (hl' j hj).1]
  exact offset_iff (hk' i hi).2 (hl' j hj).2

/-- **An eight-byte integral column's codes, where `rangeOffsets` answers, are well
    formed**: a lane of one to eight bytes, so the id bound is vacuous. -/
theorem codes_long_wf {t : QAtomicType} (ht : orderKind t = some .i64) {p : Nat}
    (cs : Vector (Part (.atom t)) p) {os : Vector Code p}
    (hro : rangeOffsets t (cs.map fun c => Arr.part c.2) ((cs.map (·.1)).foldl (fun s n => s + n.toNat) 0) = some os)
    {k : Nat} (hk : k < p) :
    let c := (Obj.codes (.atom t) cs)[k]
    laneOK(c.w) ∧ c.n = cs[k].1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  obtain ⟨base, card, hs⟩ := rangeOffsets_spec ht
    (fun k hk => by simp only [Vector.getElem_map, Arr.part]; exact cs[k].2.wf) hro
  obtain ⟨h1, -, h3, h4, -⟩ := hs k hk
  simp only [Vector.getElem_map, Arr.part] at h1 h4
  simp only [codes_long_eq ht cs (by omega) hro]
  refine ⟨by omega, h1, by rw [h1]; exact h4, fun h => absurd h (by omega)⟩

/-! ## Atoms: one part of an eight-byte integral type where `rangeOffsets` declines

All null, a span wider than the total lane or than an `Int64` offset: `codes` groups, as for the small
integral types — `groupIds .i64` over a dense payload, `groupIdsFoR .i64` over an encoded one. -/

/-- `groupIdsColumn` of an eight-byte integral payload: a dense one by `groupIds`, an encoded one by
    `groupIdsFoR`. -/
theorem groupIdsColumn_long {t : QAtomicType} (ht : orderKind t = some .i64) (n : USize) :
    (∀ b, groupIdsColumn t n (.bytes b) = some (Order.groupIds .i64 n b)) ∧
      ∀ md pk, groupIdsColumn t n (.foR md pk) = some (Order.groupIdsFoR .i64 n md pk) := by
  cases t <;> simp [orderKind] at ht <;>
    exact ⟨fun b => by simp [groupIdsColumn, orderKind, Enc.bytesOf], fun md pk => by simp [groupIdsColumn, orderKind]⟩

/-- **One part of an eight-byte integral side where `rangeOffsets` declines is coded by `groupIdsColumn`**,
    read by `Code.ofIds`. -/
theorem codes_long_group {t : QAtomicType} (ht : orderKind t = some .i64) (x : Part (.atom t))
    (hro : rangeOffsets t (#v[x].map fun c => Arr.part c.2) ((#v[x].map (·.1)).foldl (fun s n => s + n.toNat) 0) = none) :
    ∃ p, groupIdsColumn t x.1 x.2.enc = some p ∧
      (Obj.codes (.atom t) #v[x])[0] = Code.ofIds (len p.2) x.1 p.1 := by
  obtain ⟨-, -, hg, -, -⟩ := long_facts ht
  have hsome := KernelWF.groupIdsColumn_isSome hg x.2.wf fun d o ids he => by
    exfalso; rcases long_enc ht x.2.wf with ⟨b, hb, -⟩ | ⟨md, pk, hb⟩ <;> simp [hb, Column.intern] at he
  refine ⟨_, (Option.some_get hsome).symm, ?_⟩
  -- at a concrete type and payload constructor every branch test of `codes` but `rangeOffsets` reduces
  obtain ⟨n, v, hv⟩ := x
  cases v <;> try exact hv.elim
  rename_i t' n' e a
  obtain ⟨h1, h2, hwf⟩ := hv
  subst h1 h2
  cases t' <;> simp [orderKind] at ht <;> cases e <;> simp [Enc.WF, QAtomicType.width] at hwf <;>
    simp [Arr.part, Arr.enc] at hro <;>
    simp [Obj.codes, Alg.codes, hro, orderKind, raze, Column.intern, Code.cut, vmapM_one, Column.encodes, Arr.enc,
      KernelWF.bitsType,
      Arr.part]

/-- **One part of an eight-byte integral side where `rangeOffsets` declines: its codes are faithful.** -/
theorem codes_long_group_faithful {t : QAtomicType} (ht : orderKind t = some .i64) (x : Part (.atom t))
    (hro : rangeOffsets t (#v[x].map fun c => Arr.part c.2) ((#v[x].map (·.1)).foldl (fun s n => s + n.toNat) 0) = none)
    {i j : Nat} (hi : i < x.1.toNat) (hj : j < x.1.toNat) :
    Column.idAt (Obj.codes (.atom t) #v[x])[0].b (Obj.codes (.atom t) #v[x])[0].w i =
        Column.idAt (Obj.codes (.atom t) #v[x])[0].b (Obj.codes (.atom t) #v[x])[0].w j ↔
      Vals.row x.2 ⟨i, hi⟩ = Vals.row x.2 ⟨j, hj⟩ := by
  obtain ⟨p, hp, hc⟩ := codes_long_group ht x hro
  have hn64 : x.1.toNat < 2 ^ 64 := Verify.usize_lt x.1
  have hinj : ∀ a c : UInt64, a.toInt64 = c.toInt64 ↔ a = c := fun a c =>
    ⟨fun h => by simpa using congrArg Int64.toUInt64 h, fun h => h ▸ rfl⟩
  rw [hc, Vals.row_atom, Vals.row_atom, long_row_eq ht, hinj]
  rcases long_enc ht x.2.wf with ⟨b, he, hbs⟩ | ⟨md, pk, he⟩
  · rw [he, (groupIdsColumn_long ht x.1).1 b, Option.some_inj] at hp
    subst hp
    have hav : min x.1.toNat (Scan.Kind.i64.avail b) = x.1.toNat := by
      simp [Scan.Kind.avail, Scan.Kind.width, hbs]
    have hspec := Verify.groupIds_spec .i64 x.1 b
    rw [hav] at hspec
    rw [ofIds_groupOf (Order.keyAt .i64 b) x.1 hn64 hspec.1 (by rw [len_eq_ids, hspec.2]) hi,
      ofIds_groupOf (Order.keyAt .i64 b) x.1 hn64 hspec.1 (by rw [len_eq_ids, hspec.2]) hj,
      groupOf_eq_groupOf hi hj, Verify.keyAt_eq_iff (by simp) b i j, he,
      (raw_long ht hi).1 b, (raw_long ht hj).1 b]
    rfl
  · rw [he, (groupIdsColumn_long ht x.1).2 md pk, Option.some_inj] at hp
    subst hp
    have hspec := Verify.groupIdsFoR_spec .i64 (by decide) x.1 md pk
    rw [ofIds_groupOf (foRKey .i64 md pk) x.1 hn64 hspec.1 (by rw [len_eq_ids, hspec.2]) hi,
      ofIds_groupOf (foRKey .i64 md pk) x.1 hn64 hspec.1 (by rw [len_eq_ids, hspec.2]) hj,
      groupOf_eq_groupOf hi hj, he, (raw_long ht hi).2 md pk, (raw_long ht hj).2 md pk]
    simp only [foRKey, Order.rank]
    have hm : ∀ v : UInt64, UInt64.ofNat (v.toNat % 2 ^ (8 * Scan.Kind.i64.width)) = v := fun v => by
      rw [show Scan.Kind.i64.width = 8 from rfl, Nat.mod_eq_of_lt (by simpa using v.toNat_lt)]
      exact UInt64.ofNat_toNat
    rw [hm, hm]; exact UInt64.xor_left_inj _

/-- **One part of an eight-byte integral side where `rangeOffsets` declines: its code is well formed.** -/
theorem codes_long_group_wf {t : QAtomicType} (ht : orderKind t = some .i64) (x : Part (.atom t))
    (hro : rangeOffsets t (#v[x].map fun c => Arr.part c.2) ((#v[x].map (·.1)).foldl (fun s n => s + n.toNat) 0) = none) :
    let c := (Obj.codes (.atom t) #v[x])[0]
    laneOK(c.w) ∧ c.n = x.1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  obtain ⟨p, hp, hc⟩ := codes_long_group ht x hro
  rw [hc]
  rcases long_enc ht x.2.wf with ⟨b, he, hbs⟩ | ⟨md, pk, he⟩
  · rw [he, (groupIdsColumn_long ht x.1).1 b, Option.some_inj] at hp
    subst hp
    have hav : min x.1.toNat (Scan.Kind.i64.avail b) = x.1.toNat := by
      simp [Scan.Kind.avail, Scan.Kind.width, hbs]
    have hspec := Verify.groupIds_spec .i64 x.1 b
    rw [hav] at hspec
    exact ofIds_groupOf_wf (Order.keyAt .i64 b) x.1 hspec.1 (by rw [len_eq_ids, hspec.2])
  · rw [he, (groupIdsColumn_long ht x.1).2 md pk, Option.some_inj] at hp
    subst hp
    have hspec := Verify.groupIdsFoR_spec .i64 (by decide) x.1 md pk
    exact ofIds_groupOf_wf (foRKey .i64 md pk) x.1 hspec.1 (by rw [len_eq_ids, hspec.2])

/-- **One part of an eight-byte integral side: its codes are faithful**, on either branch of `codes`. -/
theorem codes_long_one_faithful {t : QAtomicType} (ht : orderKind t = some .i64) (x : Part (.atom t))
    {i j : Nat} (hi : i < x.1.toNat) (hj : j < x.1.toNat) :
    Column.idAt (Obj.codes (.atom t) #v[x])[0].b (Obj.codes (.atom t) #v[x])[0].w i =
        Column.idAt (Obj.codes (.atom t) #v[x])[0].b (Obj.codes (.atom t) #v[x])[0].w j ↔
      Vals.row x.2 ⟨i, hi⟩ = Vals.row x.2 ⟨j, hj⟩ := by
  cases hro : rangeOffsets t (#v[x].map fun c => Arr.part c.2) ((#v[x].map (·.1)).foldl (fun s n => s + n.toNat) 0) with
  | none => exact codes_long_group_faithful ht x hro hi hj
  | some os => exact codes_long_faithful ht #v[x] hro (k := 0) (l := 0) (by decide) (by decide) hi hj

/-- **One part of an eight-byte integral side: its code is well formed**, on either branch of `codes`. -/
theorem codes_long_one_wf {t : QAtomicType} (ht : orderKind t = some .i64) (x : Part (.atom t)) :
    let c := (Obj.codes (.atom t) #v[x])[0]
    laneOK(c.w) ∧ c.n = x.1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  cases hro : rangeOffsets t (#v[x].map fun c => Arr.part c.2) ((#v[x].map (·.1)).foldl (fun s n => s + n.toNat) 0) with
  | none => exact codes_long_group_wf ht x hro
  | some os => exact codes_long_wf ht #v[x] hro (k := 0) (by decide)

/-! ## Atoms: one part of a `guid` column

`codes` groups the first positions of each element, `groupIds .i64` over `findVec 16` of the payload
against itself: two rows share a first position exactly when their sixteen bytes agree. -/

/-- Two members of a list share their first position exactly when they are equal. -/
theorem idxOf_eq_iff {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a c : α} (ha : a ∈ l) (hc : c ∈ l) :
    l.idxOf a = l.idxOf c ↔ a = c := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [List.idxOf_cons] at h
    by_cases hx : x = a <;> by_cases hy : x = c
    · exact hx.symm.trans hy
    · subst hx; rw [beq_false_of_ne hy] at h; simp at h
    · subst hy; rw [beq_false_of_ne hx] at h; simp at h
    · simp only [beq_false_of_ne hx, beq_false_of_ne hy, cond_false, Nat.add_right_cancel_iff] at h
      exact ih ((List.mem_cons.1 ha).resolve_left (Ne.symm hx)) ((List.mem_cons.1 hc).resolve_left (Ne.symm hy)) h

/-- A `guid` payload is dense, sixteen bytes an element (`Enc.WF`). -/
theorem guid_enc {n : USize} {e : Enc} (hwf : Enc.WF .guid n e) : ∃ b, e = .bytes b ∧ b.size = n.toNat * 16 := by
  cases e <;> simp [Enc.WF, QAtomicType.width] at hwf ⊢ <;> first | exact hwf | omega

/-- A `guid` element is its sixteen bytes. -/
theorem guid_get {n : USize} (x : Arr .guid n) {b : ByteArray} (he : x.enc = .bytes b) (hs : b.size = n.toNat * 16)
    (i : Fin n.toNat) : (x.get i).toArray = (b.extract (i.1 * 16) (i.1 * 16 + 16)).data := by
  have hi := i.2
  rw [Arr.get_ne x i (by decide), he]
  simp only [Enc.get, hi, if_true, Option.bind_some, Carrier.of?, Option.getD_some]
  apply Array.ext
  · simp [hs]; omega
  · intro k h1 h2
    have hk : i.1 * 16 + k < b.size := by simp at h1; omega
    simp only [Vector.toArray_ofFn, Array.getElem_ofFn, ByteArray.data_extract, Array.getElem_extract]
    rw [getElem?_pos b _ hk, Option.getD_some]; rfl

/-- `groupIdsColumn` of a `guid` payload: `groupIds .i64` of each element's first position. -/
theorem groupIdsColumn_guid (n : USize) (b : ByteArray) :
    groupIdsColumn .guid n (.bytes b) = some (Order.groupIds .i64 n (findVec 16 false b b)) := by
  simp [groupIdsColumn, Enc.bytesOf]

/-- **One part of a `guid` side is coded by `groupIdsColumn`**, read by `Code.ofIds`. -/
theorem codes_guid (x : Part (.atom .guid)) :
    ∃ p, groupIdsColumn .guid x.1 x.2.enc = some p ∧
      (Obj.codes (.atom .guid) #v[x])[0] = Code.ofIds (len p.2) x.1 p.1 := by
  have hsome := KernelWF.groupIdsColumn_isSome (by decide) x.2.wf fun d o ids he => by
    exfalso; obtain ⟨b, hb, -⟩ := guid_enc x.2.wf; simp [hb, Column.intern] at he
  refine ⟨_, (Option.some_get hsome).symm, ?_⟩
  obtain ⟨n, v, hv⟩ := x
  cases v <;> try exact hv.elim
  rename_i t' n' e a
  obtain ⟨h1, h2, hwf⟩ := hv
  subst h1 h2
  cases e <;> simp [Enc.WF, QAtomicType.width] at hwf <;>
    simp [Obj.codes, Alg.codes, rangeOffsets, orderKind, raze, Column.intern, Code.cut, vmapM_one, Column.encodes,
      Arr.enc]

/-- `findVec 16` of a `guid` payload against itself, read by `groupIds .i64`: the class ids at the width
    of the class count, the first rows. -/
theorem guid_groupIds {n : USize} {b : ByteArray} (hbs : b.size = n.toNat * 16) :
    (∀ j < n.toNat, (Column.bitsAt (findVec 16 false b b) (j * 8) 8).toNat =
      ((List.range n.toNat).map fun i => (b.extract (i * 16) (i * 16 + 16)).data).idxOf
        (b.extract (j * 16) (j * 16 + 16)).data) ∧
    (Order.groupIds .i64 n (findVec 16 false b b)).1 =
      Column.packIds (Column.idWidthOf (Verify.firstsOf (Order.keyAt .i64 (findVec 16 false b b)) n.toNat).length)
        n.toNat (Verify.groupOf (Order.keyAt .i64 (findVec 16 false b b)) n.toNat) ∧
    ids (Order.groupIds .i64 n (findVec 16 false b b)).2 =
      Verify.firstsOf (Order.keyAt .i64 (findVec 16 false b b)) n.toNat := by
  have h16 : (16 : USize).toNat = 16 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have hnb : b.size / 16 = n.toNat := by omega
  obtain ⟨hFs, hF⟩ := Verify.findVec_idxOf 16 false b b (by rw [h16, hnb]; exact n.toNat_lt_size)
  rw [h16, hnb] at hFs hF
  have hav : min n.toNat (Scan.Kind.i64.avail (findVec 16 false b b)) = n.toNat := by
    simp [Scan.Kind.avail, Scan.Kind.width, hFs]
  have hspec := Verify.groupIds_spec .i64 n (findVec 16 false b b)
  rw [hav] at hspec
  exact ⟨fun j hj => by rw [hF j hj, if_neg (by decide)], hspec⟩

/-- **One part of a `guid` side: its codes are faithful.** -/
theorem codes_guid_faithful (x : Part (.atom .guid)) {i j : Nat} (hi : i < x.1.toNat) (hj : j < x.1.toNat) :
    Column.idAt (Obj.codes (.atom .guid) #v[x])[0].b (Obj.codes (.atom .guid) #v[x])[0].w i =
        Column.idAt (Obj.codes (.atom .guid) #v[x])[0].b (Obj.codes (.atom .guid) #v[x])[0].w j ↔
      Vals.row x.2 ⟨i, hi⟩ = Vals.row x.2 ⟨j, hj⟩ := by
  obtain ⟨p, hp, hc⟩ := codes_guid x
  obtain ⟨b, he, hbs⟩ := guid_enc x.2.wf
  rw [he, groupIdsColumn_guid, Option.some_inj] at hp
  subst hp
  obtain ⟨hF, hspec⟩ := guid_groupIds hbs
  have hn64 : x.1.toNat < 2 ^ 64 := Verify.usize_lt x.1
  rw [hc, ofIds_groupOf _ x.1 hn64 hspec.1 (by rw [len_eq_ids, hspec.2]) hi,
    ofIds_groupOf _ x.1 hn64 hspec.1 (by rw [len_eq_ids, hspec.2]) hj,
    groupOf_eq_groupOf hi hj, Verify.keyAt_eq_iff (by simp) _ i j]
  show Column.bitsAt _ (i * 8) 8 = Column.bitsAt _ (j * 8) 8 ↔ _
  rw [← UInt64.toNat_inj, hF i hi, hF j hj,
    idxOf_eq_iff (a := (b.extract (i * 16) (i * 16 + 16)).data) (c := (b.extract (j * 16) (j * 16 + 16)).data)
      (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩) (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩),
    Vals.row_atom, Vals.row_atom, ← Vector.toArray_inj, guid_get x.2 he hbs, guid_get x.2 he hbs]

/-- **One part of a `guid` side: its code is well formed.** -/
theorem codes_guid_wf (x : Part (.atom .guid)) :
    let c := (Obj.codes (.atom .guid) #v[x])[0]
    laneOK(c.w) ∧ c.n = x.1 ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card) := by
  obtain ⟨p, hp, hc⟩ := codes_guid x
  obtain ⟨b, he, hbs⟩ := guid_enc x.2.wf
  rw [he, groupIdsColumn_guid, Option.some_inj] at hp
  subst hp
  obtain ⟨-, hspec⟩ := guid_groupIds hbs
  rw [hc]
  exact ofIds_groupOf_wf _ x.1 hspec.1 (by rw [len_eq_ids, hspec.2])

-- -1, 0W, 0N past 2^32 rows: the span 0W - (-1) = 2^63 is no `Int64` offset (it would wrap onto 0N's
-- code), so `rangeOffsets` declines and `codes` groups; -1, 5, 0N still answers
#guard (rangeOffsets .long #v[((3 : USize), Enc.bytes (one (-1 : Int64).toUInt64 ++ one Int64.maxValue.toUInt64 ++
  one Int64.minValue.toUInt64))] (2 ^ 33)).isNone
#guard (rangeOffsets .long #v[((3 : USize), Enc.bytes (one (-1 : Int64).toUInt64 ++ one (5 : Int64).toUInt64 ++
  one Int64.minValue.toUInt64))] (2 ^ 33)).isSome

#print axioms codes_long_faithful
#print axioms codes_long_wf
#print axioms codes_boolean_faithful
#print axioms codes_boolean_wf
#print axioms codes_small_int_faithful
#print axioms codes_small_int_wf
#print axioms codes_long_one_faithful
#print axioms codes_long_one_wf
#print axioms codes_guid_faithful
#print axioms codes_guid_wf

end LeetQ.Rel.Alg
