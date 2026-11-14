/-
  `rep` of the arithmetic and column primitives of `Alg` — `arith` (`plus`, `minus`, `times`, `div`, `mod`), `succ`,
  the literal columns `col`, `tilCol` — read in `Rel(Set)`, each stating what the kernel computes: q's `long`
  arithmetic at the row's two operands, kept where the answer is not q's null and did not wrap.
-/
import LeetQ.Rel.RepFold
import LeetQ.Rel.KernelWF.PickRow
import LeetQ.Rel.KernelWF.JoinContent
import LeetQ.Rel.KernelWF.CodesLongParts
import LeetQ.Rel.KernelWF.RazeRowRec
import LeetQ.Rel.KernelWF.CrossSpec

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

/-! ## The rows `whereBits` keeps -/

/-- A relation built by `longCount` over `whereBits n B`, its row `q` read back at the position `B`'s `q`-th set
    bit names (`g`, `h`), holds the pairs of the positions below `n` whose bit is set. -/
theorem holds_where {K V : Obj} (what : String) (n : USize) (B : ByteArray)
    (key : (r : USize) → len (whereBits n B) = r.toNat → Vals K r)
    (val : (r : USize) → len (whereBits n B) = r.toNat → Vals V r) (g : Nat → K.El) (h : Nat → V.El)
    (hkey : ∀ r hr (q : Fin r.toNat), (Column.bitsAt (whereBits n B) (q.1 * 8) 8).toNat < n.toNat →
      (key r hr).row q = g (Column.bitsAt (whereBits n B) (q.1 * 8) 8).toNat)
    (hval : ∀ r hr (q : Fin r.toNat), (Column.bitsAt (whereBits n B) (q.1 * 8) 8).toNat < n.toNat →
      (val r hr).row q = h (Column.bitsAt (whereBits n B) (q.1 * 8) 8).toNat)
    (x : K.El) (y : V.El) :
    (longCount what (whereBits n B) fun r hr => (⟨r, key r hr, val r hr⟩ : Rel K V)).Holds x y ↔
      ∃ t, t < n.toNat ∧ Column.bitAt B t = true ∧ g t = x ∧ h t = y := by
  have hl : len (whereBits n B) < USize.size := Nat.lt_of_le_of_lt (len_whereBits_le B n) n.toNat_lt_size
  rw [longCount_eq _ _ _ hl]
  obtain ⟨hI, -, hm⟩ := whereBits_ids n B
  have hn : ((len (whereBits n B)).toUSize).toNat = (ids (whereBits n B)).length := by
    rw [USize.toNat_ofNat_of_lt' hl, len_eq_ids]
  have hget : ∀ q (hq : q < (ids (whereBits n B)).length),
      (ids (whereBits n B))[q] = (Column.bitsAt (whereBits n B) (q * 8) 8).toNat := fun q hq => by simp [ids]
  constructor
  · rintro ⟨q, hk, hv⟩
    have hq : q.1 < (ids (whereBits n B)).length := hn ▸ q.2
    have hmem : (ids (whereBits n B))[q.1] ∈ (List.range n.toNat).filter (Column.bitAt B) :=
      hI ▸ List.getElem_mem hq
    rw [hget q.1 hq] at hmem
    obtain ⟨ht, hb⟩ := (hm _).1 hmem
    exact ⟨_, ht, hb, (hkey _ _ q ht).symm.trans hk, (hval _ _ q ht).symm.trans hv⟩
  · rintro ⟨t, ht, hb, hg, hh⟩
    have hmem : t ∈ ids (whereBits n B) := hI ▸ (hm t).2 ⟨ht, hb⟩
    obtain ⟨q, hq, hqe⟩ := List.getElem_of_mem hmem
    have e : (Column.bitsAt (whereBits n B) (q * 8) 8).toNat = t := (hget q hq).symm.trans hqe
    have hq' : q < ((len (whereBits n B)).toUSize).toNat := hn ▸ hq
    refine ⟨⟨q, hq'⟩, ?_, ?_⟩
    · show (key _ _).row ⟨q, hq'⟩ = x
      rw [hkey _ _ ⟨q, hq'⟩ (e ▸ ht)]; exact e ▸ hg
    · show (val _ _).row ⟨q, hq'⟩ = y
      rw [hval _ _ ⟨q, hq'⟩ (e ▸ ht)]; exact e ▸ hh

/-! ## One element of the `long` kernels -/

theorem elem_i64 (x : ByteArray) (t : Nat) : Ew.elem Ew.i64 x t = Column.bitsAt x (t * 8) 8 := by
  rw [Ew.elem, show Ew.width Ew.i64 = 8 by decide]

/-- `Ew.val` at `long` is `Ew.intStep` on the two operands: wrapping `Int64` `+ - *`, the null in, null out. -/
theorem valStep_i64 (op : UInt8) (x y : Int64) :
    Ew.valStep op Ew.i64 nul.toUInt64 x.toUInt64 y.toUInt64 = (Ew.intStep op nul x y).toUInt64 := by
  simp only [Ew.valStep, Ew.signed, Int64.toInt64_toUInt64, show (Ew.i64 == Ew.f64) = false by decide,
    show (Ew.i64 == Ew.f32) = false by decide, show (Ew.i64 == Ew.u8) = false by decide,
    show (Ew.i64 == Ew.i16) = false by decide, show (Ew.i64 == Ew.i32) = false by decide, Bool.false_eq_true,
    if_false]

theorem compare_lt_iff (x y : Int64) : compare x y = .lt ↔ x < y := by
  simp only [compare, compareOfLessAndEq]
  by_cases h : x < y
  · simp [h]
  · simp only [h, if_false]; split <;> simp

theorem compare_gt_iff (x y : Int64) : compare x y = .gt ↔ y < x := by
  simp only [compare, compareOfLessAndEq]
  by_cases h : x < y
  · simp only [h, if_true, reduceCtorEq, false_iff]; exact Int64.not_lt.2 (Int64.le_of_lt h)
  · simp only [h, if_false]
    by_cases e : x = y
    · subst e; simp [Int64.lt_irrefl]
    · simp only [e, if_false, true_iff]
      exact Int64.lt_of_le_of_ne (Int64.not_lt.1 h) (Ne.symm e)

/-- `Ew.cmpStep` at `long`, read as `Int64` order. -/
theorem cmpStep_i64 (c : UInt8) (x y : Int64) :
    Ew.cmpStep c Ew.i64 x.toUInt64 y.toUInt64 =
      (if c == Ew.eq then compare x y == .eq else if c == Ew.ne then compare x y != .eq
       else if c == Ew.lt then compare x y == .lt else if c == Ew.le then compare x y != .gt
       else if c == Ew.gt then compare x y == .gt else compare x y != .lt) := by
  simp only [Ew.cmpStep, Ew.signed, Int64.toInt64_toUInt64, show (Ew.i64 == Ew.f64) = false by decide,
    show (Ew.i64 == Ew.f32) = false by decide, show (Ew.i64 == Ew.u8) = false by decide,
    show (Ew.i64 == Ew.i16) = false by decide, show (Ew.i64 == Ew.i32) = false by decide, Bool.false_eq_true,
    if_false]

theorem cmp_ne_i64 (x y : Int64) : Ew.cmpStep Ew.ne Ew.i64 x.toUInt64 y.toUInt64 = true ↔ x ≠ y := by
  rw [cmpStep_i64]; simp [show (Ew.ne == Ew.eq) = false by decide, Std.compare_eq_iff_eq]

theorem cmp_eq_i64 (x y : Int64) : Ew.cmpStep Ew.eq Ew.i64 x.toUInt64 y.toUInt64 = true ↔ x = y := by
  rw [cmpStep_i64]; simp [Std.compare_eq_iff_eq]

theorem cmp_ge_i64 (x y : Int64) : Ew.cmpStep Ew.ge Ew.i64 x.toUInt64 y.toUInt64 = true ↔ y ≤ x := by
  rw [cmpStep_i64]
  simp only [show (Ew.ge == Ew.eq) = false by decide, show (Ew.ge == Ew.ne) = false by decide,
    show (Ew.ge == Ew.lt) = false by decide, show (Ew.ge == Ew.le) = false by decide,
    show (Ew.ge == Ew.gt) = false by decide, Bool.false_eq_true, if_false, bne_iff_ne, ne_eq, compare_lt_iff]
  exact Int64.not_lt

theorem cmp_le_i64 (x y : Int64) : Ew.cmpStep Ew.le Ew.i64 x.toUInt64 y.toUInt64 = true ↔ x ≤ y := by
  rw [cmpStep_i64]
  simp only [show (Ew.le == Ew.eq) = false by decide, show (Ew.le == Ew.ne) = false by decide,
    show (Ew.le == Ew.lt) = false by decide, show (Ew.le == Ew.le) = true by decide, Bool.false_eq_true,
    if_false, if_true, bne_iff_ne, ne_eq, compare_gt_iff]
  exact Int64.not_lt

theorem cmp_ge_zero (x : Int64) : Ew.cmpStep Ew.ge Ew.i64 x.toUInt64 0 = true ↔ 0 ≤ x := cmp_ge_i64 x 0

theorem cmp_eq_zero (x : Int64) : Ew.cmpStep Ew.eq Ew.i64 x.toUInt64 0 = true ↔ x = 0 := cmp_eq_i64 x 0

theorem bitStep_lesser (x y : Bool) : Ew.bitStep Ew.lesser x y = (x && y) := by
  cases x <;> cases y <;> decide

theorem bitStep_greater (x y : Bool) : Ew.bitStep Ew.greater x y = (x || y) := by
  cases x <;> cases y <;> decide

theorem bitStep_same (x y : Bool) : Ew.bitStep (Ew.bitCmp + Ew.eq) x y = true ↔ (x = true ↔ y = true) := by
  cases x <;> cases y <;> decide

theorem bitAt_cmp (c shape : UInt8) (x y : ByteArray) {n : USize} {t : Nat} (ht : t < n.toNat) :
    Column.bitAt (Ew.cmp c Ew.i64 shape x y n) t =
      Ew.cmpStep c Ew.i64 (Ew.elem Ew.i64 x (Ew.shapeIdx shape t).1) (Ew.elem Ew.i64 y (Ew.shapeIdx shape t).2) := by
  rw [(cmp_bitAt c Ew.i64 shape x y n).2 t (by omega)]; simp [ht]

theorem bitAt_bit (op : UInt8) (x y : ByteArray) {n : USize} {t : Nat} (ht : t < n.toNat) :
    Column.bitAt (Ew.bit op Ew.vv x y n) t = Ew.bitStep op (Column.bitAt x t) (Column.bitAt y t) := by
  rw [(Ew.bit_bitAt op Ew.vv x y n).2 t (by omega)]; simp [ht, Ew.shapeIdx]

theorem bitAt_ite {c : Prop} [Decidable c] (X Y : ByteArray) (t : Nat) :
    Column.bitAt (if c then X else Y) t = if c then Column.bitAt X t else Column.bitAt Y t := by
  split <;> rfl

theorem ite_eq_true_iff {c : Prop} [Decidable c] (x y : Bool) :
    ((if c then x else y) = true) ↔ (if c then x = true else y = true) := by
  split <;> rfl

-- `arith`'s fallthrough test is `ok` again, which the conjunction already holds
theorem and_ite_self {P A B C : Prop} {c₁ c₂ c₃ : Prop} [Decidable c₁] [Decidable c₂] [Decidable c₃] :
    (P ∧ if c₁ then A else if c₂ then B else if c₃ then C else P) ↔
      (P ∧ if c₁ then A else if c₂ then B else if c₃ then C else True) := by
  by_cases h₁ : c₁ <;> by_cases h₂ : c₂ <;> by_cases h₃ : c₃ <;> simp [h₁, h₂, h₃]

/-! ## `arith` -/

-- the one rewrite set reading `arith`'s row test and answer at the position `t` (below the count, `ht`)
set_option hygiene false in
local macro "arith_simp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [bitAt_bit _ _ _ ht, bitAt_cmp _ _ _ _ ht, bitAt_ite,
  ite_eq_true_iff, bitStep_lesser, bitStep_greater, bitStep_same, elem_one, elem_i64, Ew.shapeIdx, bitsAt_one,
  Nat.zero_mul, show (Ew.va == Ew.vv) = false by decide, show (Ew.va == Ew.va) = true by decide,
  show (Ew.vv == Ew.vv) = true by decide, if_true, if_false, Bool.false_eq_true, val_vv_get _ _ _ _ ht,
  longsOf_get W.1 ht, longsOf_get W.2 ht, valStep_i64, Bool.and_eq_true, Bool.or_eq_true, cmp_ne_i64,
  cmp_eq_i64, cmp_ge_i64, cmp_le_i64, cmp_ge_zero, cmp_eq_zero, Int64.toInt64_toUInt64] $[$loc]?)

-- the row test `arith op` keeps on top of a non-null answer `w` to `(a, b)`: `+`/`-` did not wrap (the order of
-- `w` against `a` agrees with `b`'s sign), `*` did not wrap (`w div a` gives `b` back, or `a = 0`)
set_option hygiene false in
local notation "exactA(" op ", " a ", " b ", " w ")" =>
  (if op == Ew.add then (0 ≤ b ↔ a ≤ w) else if op == Ew.sub then (0 ≤ b ↔ w ≤ a)
   else if op == Ew.mul then (Ew.intStep Ew.idiv nul w a = b ∨ a = 0) else True)

/-- **`rep (arith op W)`**: `(a, b)` a pair of `W`, to `w = Ew.intStep op nul a b` — `Int64`'s wrapping `+ - *`,
    `Int.fdiv`/`Int.fmod` for `idiv`/`imod`, q's null where an operand is null or (`idiv`/`imod`) `b = 0` — kept
    where `w` is not the null and, for `+ - *`, did not wrap (`exactA`). No hypothesis: the operands are atoms. -/
theorem rep_arith (op : UInt8) {n : USize} (W : Vals (.prod (.atom .long) (.atom .long)) n) (a b w : Int64) :
    rep (arith op W) (a, b) w ↔
      (∃ i, W.row i = (a, b)) ∧ w = Ew.intStep op nul a b ∧ w ≠ nul ∧ exactA(op, a, b, w) := by
  refine (holds_where (V := .atom .long) "arith" n _ (fun r hr => Vals.pick _ W _ r hr)
      (fun r hr => longsN r (gather 8 (Kernel.Ew.val op Ew.i64 Ew.vv nul (longsOf W.1) (longsOf W.2) n) _)
        (Nat.le_of_eq ((gather_len _ _).trans hr).symm))
      (fun t => if ht : t < n.toNat then W.row ⟨t, ht⟩ else (Obj.prod (.atom .long) (.atom .long)).dflt)
      (fun t => (Column.bitsAt (Kernel.Ew.val op Ew.i64 Ew.vv nul (longsOf W.1) (longsOf W.2) n) (t * 8) 8).toInt64)
      ?_ ?_ (a, b) w).trans ?_
  · intro r hr q hin
    dsimp only
    rw [dif_pos hin]
    exact pick_row_prod W (fun i m h q hin => pick_row_atom _ i m h q hin)
      (fun i m h q hin => pick_row_atom _ i m h q hin) _ _ _ q hin
  · intro r hr q hin
    dsimp only
    rw [Vals.row_atom, longsN_get, gather8_get (by rw [hr]; exact q.2) (by rw [len_val]; exact hin)]
  · constructor
    · rintro ⟨t, ht, hb, hg, hh⟩
      rw [dif_pos ht] at hg
      obtain ⟨e1, e2⟩ := Prod.mk.inj hg
      change W.1.get ⟨t, ht⟩ = a at e1
      change W.2.get ⟨t, ht⟩ = b at e2
      subst e1 e2
      arith_simp at hb hh
      subst hh
      exact ⟨⟨_, rfl⟩, rfl, and_ite_self.1 hb⟩
    · rintro ⟨⟨i, hi⟩, hw, hx⟩
      obtain ⟨e1, e2⟩ := Prod.mk.inj hi
      change W.1.get i = a at e1
      change W.2.get i = b at e2
      subst e1 e2 hw
      have ht := i.2
      refine ⟨i.1, ht, ?_, by rw [dif_pos ht]; rfl, ?_⟩
      · arith_simp
        exact and_ite_self.2 hx
      · arith_simp

/-- **`rep (plus W)`**: `(a, b)` in `W` to its `Int64` sum, where that did not wrap (`b`'s sign agrees with `w`'s
    order against `a`) and is not q's null; `Ew.intStep` answers the null for a null operand. -/
theorem rep_plus {n : USize} (W : Vals (.prod (.atom .long) (.atom .long)) n) (a b w : Int64) :
    rep (plus W) (a, b) w ↔
      (∃ i, W.row i = (a, b)) ∧ w = Ew.intStep Ew.add nul a b ∧ w ≠ nul ∧ (0 ≤ b ↔ a ≤ w) := by
  rw [show plus W = arith Ew.add W from rfl, rep_arith]
  simp only [show (Ew.add == Ew.add) = true by decide, if_true]

/-- **`rep (minus W)`**: `(a, b)` in `W` to `a - b` in `Int64`, where that did not wrap and is not the null. -/
theorem rep_minus {n : USize} (W : Vals (.prod (.atom .long) (.atom .long)) n) (a b w : Int64) :
    rep (minus W) (a, b) w ↔
      (∃ i, W.row i = (a, b)) ∧ w = Ew.intStep Ew.sub nul a b ∧ w ≠ nul ∧ (0 ≤ b ↔ w ≤ a) := by
  rw [show minus W = arith Ew.sub W from rfl, rep_arith]
  simp only [show (Ew.sub == Ew.add) = false by decide, show (Ew.sub == Ew.sub) = true by decide,
    Bool.false_eq_true, if_true, if_false]

/-- **`rep (times W)`**: `(a, b)` in `W` to `a * b` in `Int64`, where `w div a` takes it back to `b` (or `a = 0`)
    and it is not the null. -/
theorem rep_times {n : USize} (W : Vals (.prod (.atom .long) (.atom .long)) n) (a b w : Int64) :
    rep (times W) (a, b) w ↔ (∃ i, W.row i = (a, b)) ∧ w = Ew.intStep Ew.mul nul a b ∧ w ≠ nul ∧
      (Ew.intStep Ew.idiv nul w a = b ∨ a = 0) := by
  rw [show times W = arith Ew.mul W from rfl, rep_arith]
  simp only [show (Ew.mul == Ew.add) = false by decide, show (Ew.mul == Ew.sub) = false by decide,
    show (Ew.mul == Ew.mul) = true by decide, Bool.false_eq_true, if_true, if_false]

/-- **`rep (div W)`**: `(a, b)` in `W` to `Int.fdiv a b` (q's `div`, floor), no row where `b = 0` or an operand is
    the null (`Ew.intStep` answers the null there). -/
theorem rep_div {n : USize} (W : Vals (.prod (.atom .long) (.atom .long)) n) (a b w : Int64) :
    rep (div W) (a, b) w ↔ (∃ i, W.row i = (a, b)) ∧ w = Ew.intStep Ew.idiv nul a b ∧ w ≠ nul := by
  rw [show div W = arith Ew.idiv W from rfl, rep_arith]
  simp only [show (Ew.idiv == Ew.add) = false by decide, show (Ew.idiv == Ew.sub) = false by decide,
    show (Ew.idiv == Ew.mul) = false by decide, Bool.false_eq_true, if_false, and_true]

/-- **`rep (mod W)`**: `(a, b)` in `W` to `Int.fmod a b` (q's `mod`, the sign of `b`), no row where `b = 0` or an
    operand is the null. -/
theorem rep_mod {n : USize} (W : Vals (.prod (.atom .long) (.atom .long)) n) (a b w : Int64) :
    rep (mod W) (a, b) w ↔ (∃ i, W.row i = (a, b)) ∧ w = Ew.intStep Ew.imod nul a b ∧ w ≠ nul := by
  rw [show mod W = arith Ew.imod W from rfl, rep_arith]
  simp only [show (Ew.imod == Ew.add) = false by decide, show (Ew.imod == Ew.sub) = false by decide,
    show (Ew.imod == Ew.mul) = false by decide, Bool.false_eq_true, if_false, and_true]

/-- `Ew.intStep` of `+` off the null is `Int64`'s wrapping `+`. -/
theorem intStep_add (a b : Int64) : Ew.intStep Ew.add nul a b = if a = nul ∨ b = nul then nul else a + b := by
  simp only [Ew.intStep, show (Ew.add == Ew.add) = true by decide, if_true, Bool.or_eq_true, beq_iff_eq]

/-! ## `succ` -/

-- codes `cs` of two long columns `ps` faithful and well formed: `RepOps`' `codesOK`, rows read by `Arr.get`, without
-- its `w < 8` clause
set_option hygiene false in
local notation "codesL(" cs ", " ps ")" => ((∀ {k l : Nat} (hk : k < 2) (hl : l < 2) {i j : Nat}
    (hi : i < (ps[k]'hk).1.toNat) (hj : j < (ps[l]'hl).1.toNat),
    Column.idAt (cs[k]'hk).b (cs[k]'hk).w i = Column.idAt (cs[l]'hl).b (cs[l]'hl).w j ↔
      Arr.get (ps[k]'hk).2 ⟨i, hi⟩ = Arr.get (ps[l]'hl).2 ⟨j, hj⟩) ∧
  ∀ {k : Nat} (hk : k < 2),
    laneOK((cs[k]'hk).w) ∧
    (cs[k]'hk).n = (ps[k]'hk).1 ∧ (cs[k]'hk).b.size = ((cs[k]'hk).n.toNat * (cs[k]'hk).w + 7) / 8)

/-- `valCol` of `Ew.add` against the long `1`, element `i`: `Ew.intStep` of `+ 1`. -/
theorem valCol_succ_get {n : USize} (U : Arr .long n) (i : Fin n.toNat) :
    (valCol (n := n) Ew.add Ew.va (longsOf U) (one 1)).get i = Ew.intStep Ew.add nul (U.get i) 1 := by
  rw [Arr.get_long_bytes _ rfl, val_va_get _ _ _ _ i.2, bitsAt_one, longsOf_get U i.2,
    show (1 : UInt64) = (1 : Int64).toUInt64 from rfl, valStep_i64, Int64.toInt64_toUInt64]

/-- **`rep (succ U)`**: `u` in `U` to `u + 1` (`Ew.intStep`, wrapping), where that is an element of `U` again — so
    the top of `U` goes nowhere, and so does `Int64.maxValue`, whose wrapped successor is q's null unless `U` holds
    the null. Hypotheses: the defining equations of the successor column `s` and the codes `cs`, and `cs` faithful
    and well formed (`codesL`). -/
theorem rep_succ {n : USize} (U : Vals (.atom .long) n) (s : Arr .long n)
    (hs : s = valCol Ew.add Ew.va (longsOf U) (one 1)) (cs : Vector Code 2)
    (hcs : cs = codes .long #v[⟨n, s⟩, ⟨n, U⟩]) (hc : codesL(cs, (#v[⟨n, s⟩, ⟨n, U⟩] : Vector ((m : USize) × Arr .long m) 2)))
    (u w : Int64) :
    rep (succ U) u w ↔ (∃ i, U.row i = u) ∧ w = Ew.intStep Ew.add nul u 1 ∧ ∃ j, U.row j = w := by
  subst hs
  refine (holds_where (V := .atom .long) "succ" n _ (fun r hr => Vals.pick _ U _ r hr)
      (fun r hr => Vals.pick (.atom .long) (valCol (n := n) Ew.add Ew.va (longsOf U) (one 1)) _ r hr)
      (fun t => if ht : t < n.toNat then U.get ⟨t, ht⟩ else default)
      (fun t => if ht : t < n.toNat then (valCol (n := n) Ew.add Ew.va (longsOf U) (one 1)).get ⟨t, ht⟩
        else default) ?_ ?_ u w).trans ?_
  · intro r hr q hin
    dsimp only
    rw [dif_pos hin]; exact pick_row_atom _ _ _ _ q hin
  · intro r hr q hin
    dsimp only
    rw [dif_pos hin]; exact pick_row_atom _ _ _ _ q hin
  · rw [← hcs]
    obtain ⟨hF, hW⟩ := hc
    obtain ⟨hw0, hn0, hs0⟩ := hW (k := 0) (by decide)
    obtain ⟨hw1, hn1, hs1⟩ := hW (k := 1) (by decide)
    have hbit : ∀ t (ht : t < n.toNat), Column.bitAt ((cs[0]'Nat.zero_lt_two).member (cs[1]'Nat.one_lt_two)) t = true ↔
        ∃ j : Fin n.toNat, U.get j = (valCol (n := n) Ew.add Ew.va (longsOf U) (one 1)).get ⟨t, ht⟩ := fun t ht => by
      rw [member_bit _ _ hw0 hw1 hs0 hs1 (by rw [hn0]; exact ht)]
      constructor
      · rintro ⟨j, hj, he⟩
        have hj' : j < n.toNat := by rw [hn1] at hj; exact hj
        exact ⟨⟨j, hj'⟩, (hF (k := 1) (l := 0) (by decide) (by decide) hj' ht).1 he⟩
      · rintro ⟨j, hj⟩
        exact ⟨j.1, by rw [hn1]; exact j.2, (hF (k := 1) (l := 0) (by decide) (by decide) j.2 ht).2 hj⟩
    constructor
    · rintro ⟨t, ht, hb, hg, hh⟩
      rw [dif_pos ht] at hg hh
      obtain ⟨j, hj⟩ := (hbit t ht).1 hb
      rw [valCol_succ_get] at hh hj
      exact ⟨⟨_, hg⟩, by rw [← hh, hg], j, hj.trans hh⟩
    · rintro ⟨⟨i, hi⟩, hw, j, hj⟩
      refine ⟨i.1, i.2, (hbit i.1 i.2).2 ⟨j, ?_⟩, by rw [dif_pos i.2]; exact hi, ?_⟩
      · rw [valCol_succ_get]; exact hj.trans (hw.trans (by rw [← hi]; rfl))
      · rw [dif_pos i.2, valCol_succ_get]; exact (hw.trans (by rw [← hi]; rfl)).symm

/-! ## The columns the folds seed and count with -/

/-- **`col xs`, read back**: where `xs` fits a `USize` (else `col` stops, its model the blank column), element `i`
    is `xs[i]`. (`tilCol`'s is `tilCol_get`, `KernelWF/CrossSpec.lean`: element `i` is `Int64.ofNat i`.) -/
theorem col_get (xs : List Int64) (h : xs.length < USize.size) (i : Fin xs.length.toUSize.toNat) :
    (col xs).get i = xs[i.1]'(Nat.lt_of_lt_of_eq i.2 (USize.toNat_ofNat_of_lt' h)) := by
  have hi : i.1 < xs.length := Nat.lt_of_lt_of_eq i.2 (USize.toNat_ofNat_of_lt' h)
  have e := elemsW_foldl (fun x : Int64 => x.toUInt64) 8 (by decide) (by decide) xs
    fun x _ => Nat.lt_of_lt_of_eq (UInt64.toNat_lt_size x.toUInt64) (by decide)
  have hl : i.1 < (elemsW 8 (packLongs xs)).length := by
    simp only [elemsW, List.length_map, List.length_range, packLongs_size]; omega
  have e' := List.getElem_of_eq e hl
  simp only [elemsW, List.getElem_map, List.getElem_range] at e'
  unfold col need
  rw [dif_pos h, Arr.get_long_bytes _ rfl]
  exact (congrArg UInt64.toInt64 e').trans (Int64.toInt64_toUInt64 _)

/-- **`length X` where its `needSize` fits**: the fold of `col [0]` and `outr D ≫ succ (tilCol c)`, `c` the payload's
    count plus one — `needSize`'s continuation at that count; past it `length` stops (its model `default`). -/
theorem length_eq {E : Obj} {n : USize} (X : Vals (.arr E) n) (hX : X.1.toNat + 1 < USize.size) :
    length X = foldOn (col [0]) (fun D => outr D ≫ succ (tilCol (X.1.toNat + 1).toUSize)) X := by
  unfold length needSize need
  rw [dif_pos hX]

#print axioms col_get
#print axioms length_eq
#print axioms rep_succ
#print axioms holds_where
#print axioms rep_arith
#print axioms rep_plus
#print axioms rep_minus
#print axioms rep_times
#print axioms rep_div
#print axioms rep_mod

/-! ## Folds whose family only restricts to the pairs a round meets -/

section FoldOn

open QLean.Dep

open FoldN OpsN
-- `rep_ran`'s hypotheses at `R`, its value codes `c` bound by their equation
set_option hygiene false in
local notation "ranOK(" R ")" =>
  ∀ c : Code, c = (Obj.codes (.prod E V) (#v[⟨Rel.n R, Rel.val R⟩] : Vector (Part (.prod E V)) 1))[0]'Nat.zero_lt_one →
    (∀ {i j : Nat} (hi : i < (Rel.n R).toNat) (hj : j < (Rel.n R).toNat),
      Column.idAt c.b c.w i = Column.idAt c.b c.w j ↔ Vals.row (Rel.val R) ⟨i, hi⟩ = Vals.row (Rel.val R) ⟨j, hj⟩) ∧
    (laneOK(c.w) ∧ c.n = Rel.n R ∧
      c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
      (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)) ∧
    Vals.PickFits (.prod E V) (Rel.val R) (ids c.groupIds.2)

/-- **`foldOn` of a family that only restricts to the pairs a round meets**: where `Sf (D k)` is `S'` on the pairs
    of `D k` (`hSf`), the array `xs` goes to `w` along a chain `ys` of `S'`-steps — the family's dependence on the
    other arrays drops out, because the pair `(xs[t], ys[t+1])` a round meets is itself in `D k`. Bound values and
    hypotheses as `rep_foldOn`'s, and `rep_ran`'s at each round's pairs (`hran`, a per-round bundle). -/
theorem foldOn_on {E V : Obj} {m n : USize} (e : Vals V m) (Sf : Rel (.prod E V) (.prod E V) → Rel (.prod E V) V)
    (X : Vals (.arr E) n)
    (T : Rel .long (.arr E)) (hT : T = num (idU X) 0) (hn : n.toNat < 2 ^ 63)
    (hv : Vals.PickFits (.arr E) X (List.range n.toNat)) (hp : (Rel.val T).1.toNat < 2 ^ 63)
    (hel : ∀ k, k ≤ (Rel.val T).1.toNat → ∀ a : ByteArray, a = whereBits (Rel.n T)
        (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf (Rel.val T)).2 (one k.toUInt64) (Rel.n T)) →
      ∀ pos : ByteArray, pos = Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul
        (gather 8 (add (Rel.n T) (slicesOf (Rel.val T)).1 (slicesOf (Rel.val T)).2) a)
        (one (k + 1).toUInt64) (len a).toUSize →
      Vals.PickFits .long (Rel.key T) ((List.range (len a)).map fun q => (Column.bitsAt a (q * 8) 8).toNat) ∧
      Vals.PickFits E (Rel.val T).2.2.2 ((List.range (len a)).map fun q => (Column.bitsAt pos (q * 8) 8).toNat))
    (pend₀ : Rel .long V) (hpend : pend₀ = top (A := .long) (Rel.key T) e)
    (hN : (Rel.n T).toNat * m.toNat < USize.size) (h63 : (Rel.n T).toNat * m.toNat < 2 ^ 63)
    (hA : Vals.PickFits .long (Rel.key T) ((List.range ((Rel.n T).toNat * m.toNat)).map (· / m.toNat)))
    (hB : Vals.PickFits V e ((List.range ((Rel.n T).toNat * m.toNat)).map (· % m.toNat)))
    (step : Rel .long E → Rel .long V → Rel .long V) (hstep : step = demandStep Sf)
    (elK : Nat → Rel .long E) (hE : ∀ k, elK k = elR(T, k))
    (f : Rel .long V × Rel .long V × Nat → Rel .long V × Rel .long V × Nat) (hf : ∀ st, f st = rnd(st))
    (D : Nat → Rel (.prod E V) (.prod E V)) (hD : ∀ k, D k = ran (pair (elK k) (f^[k] (pend₀, Alg.zero, 0)).1))
    (hR : ∀ i (el : Rel .long E) (pend P S : Rel .long V), el = elK i → pend = (f^[i] (pend₀, Alg.zero, 0)).1 →
      P = (f^[i] (pend₀, Alg.zero, 0)).2.1 → S = step el pend → roundOK)
    (hS : ∀ i (el : Rel .long E) (pend : Rel .long V), el = elK i → pend = (f^[i] (pend₀, Alg.zero, 0)).1 →
      stepOn)
    (F : Rel .long V) (hF : F = foldRows T pend₀ step)
    (jc : Vector Code 2) (hjc : jc = Obj.codes .long ck2(T°, F)) (hjO : codesOK(jc, ck2(T°, F)))
    (hjn : (Rel.n F).toNat < 2 ^ 63) (hjM : msum(jc, T°, F) < 2 ^ 63) (hjU : msum(jc, T°, F) < USize.size)
    (hjA : Vals.PickFits (.arr E) (Rel.key (T°)) ((mpairs(jc, T°, F)).map Prod.fst))
    (hjC : Vals.PickFits V (Rel.val F) ((mpairs(jc, T°, F)).map Prod.snd))
    (hran : ∀ k, k < (Rel.val T).1.toNat → ∀ P : Rel .long (.prod E V),
      P = pair (elK k) (f^[k] (pend₀, Alg.zero, 0)).1 → ranOK(P))
    (S' : E.El × V.El → V.El → Prop)
    (hSf : ∀ k, k < (Rel.val T).1.toNat → ∀ p w, rep (Sf (D k)) p w ↔ (∃ a, rep (D k) a p) ∧ S' p w) :
    ∀ (xs : List E.El) w, rep (foldOn e Sf X) xs w ↔ (∃ i, X.row i = xs) ∧
      ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
        (∃ p, e.row p = ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm)) ∧
        (∀ t (ht : t < xs.length), S' (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm))
          (ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm))) ∧
        w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm) := by
  intro xs w
  rw [rep_foldOn e Sf X T hT hn hv hp hel pend₀ hpend hN h63 hA hB step hstep elK hE f hf D hD hR hS F hF jc hjc
    hjO hjn hjM hjU hjA hjC xs w]
  have hnum : ∀ r y, rep T r y ↔ ∃ i : Fin n.toNat, r = Int64.ofNat i.1 ∧ X.row i = y := by
    intro r y; subst hT
    rw [rep_num (idU X) 0 (by simpa using hn) hv r y]
    simp only [USize.toNat_zero, Nat.zero_add]; exact Iff.rfl
  -- array `i` of `X` is a row of `T`, keyed `i`, so no longer than the payload
  have hrow : ∀ i : Fin n.toNat, ∃ i' : Nat, ∃ hi' : i' < (Rel.n T).toNat,
      Vals.row (Rel.key T) ⟨i', hi'⟩ = Int64.ofNat i.1 ∧ Vals.row (Rel.val T) ⟨i', hi'⟩ = X.row i ∧
      (X.row i).length ≤ (Rel.val T).1.toNat := by
    intro i
    obtain ⟨⟨i', hi'⟩, hk, hv'⟩ := (hnum _ _).2 ⟨i, rfl, rfl⟩
    obtain ⟨h1, h2, -⟩ := slicesOf_row (Rel.val T) hp hi'
    exact ⟨i', hi', hk, hv', by rw [← hv']; omega⟩
  constructor
  · rintro ⟨⟨i, hi⟩, ys, hy, h0, hst, hw⟩
    obtain ⟨-, -, -, -, hL⟩ := hrow i
    rw [hi] at hL
    exact ⟨⟨i, hi⟩, ys, hy, h0, fun t ht => ((hSf _ (by omega) _ _).1 (hst t ht)).2, hw⟩
  · rintro ⟨⟨i, hi⟩, ys, hy, h0, hst, hw⟩
    refine ⟨⟨i, hi⟩, ys, hy, h0, ?_, hw⟩
    obtain ⟨i', hi', hk', hv', hL⟩ := hrow i
    rw [hi] at hv' hL
    have gi : ∀ a b (ha : a < ys.length) (hb : b < ys.length), a = b → ys[a] = ys[b] := by
      intro a b ha hb h; subst h; rfl
    have gx : ∀ a b (ha : a < xs.length) (hb : b < xs.length), a = b → xs[a] = xs[b] := by
      intro a b ha hb h; subst h; rfl
    -- round `k` meets `xs[|xs| - 1 - k]` at the row `i`
    have hel1 : ∀ k (hk : k < xs.length),
        rep (elK k) (Int64.ofNat i.1) (xs[xs.length - 1 - k]'(by omega)) := by
      intro k hk
      obtain ⟨hKf, hVf⟩ := hel k (by omega) _ rfl _ rfl
      rw [hE, rep_elR T k (by omega) hp _ rfl _ rfl hKf hVf]
      subst hv'
      exact ⟨⟨i', hi'⟩, hk', hk, rfl⟩
    have hst0 : rep pend₀ (Int64.ofNat i.1) (ys[xs.length]'(by omega)) := by
      subst hpend; rw [rep_top _ _ hN h63 hA hB]
      exact ⟨_, ⟨rfl, ⟨i', hi'⟩, hk'⟩, _, trivial, rfl, h0⟩
    have hrr := rounds_rep pend₀ step elK f hf hR
    -- round `j` read back at the row `i`
    have hstep1 : ∀ j v, rep (f^[j + 1] (pend₀, Alg.zero, 0)).1 (Int64.ofNat i.1) v ↔
        ∃ a u, rep (elK j) (Int64.ofNat i.1) a ∧ rep (f^[j] (pend₀, Alg.zero, 0)).1 (Int64.ofNat i.1) u ∧
          rep (Sf (D j)) (a, u) v := by
      intro j v
      rw [(hrr j).2.1]
      obtain ⟨hkO, hkn, hkM, hkU, hkA, hkB, hkC, hJ⟩ := hS j _ _ rfl rfl _ rfl
      obtain ⟨hjO', hjn', hjM', hjU', hjA', hjC'⟩ := hJ _ rfl _ (congrArg Sf (hD j)) _ rfl
      subst hstep
      exact step_rep (elK j) _ Sf _ rfl hkO hkn hkM hkU hkA hkB hkC _ rfl _ (congrArg Sf (hD j)) _ rfl
        hjO' hjn' hjM' hjU' hjA' hjC' _ v
    -- the pair round `j` meets at the row `i` is in `D j`
    have hmem : ∀ j, j < (Rel.val T).1.toNat → ∀ a u, rep (elK j) (Int64.ofNat i.1) a →
        rep (f^[j] (pend₀, Alg.zero, 0)).1 (Int64.ofNat i.1) u → ∃ q, rep (D j) q (a, u) := by
      intro j hj a u ha hu
      obtain ⟨hkO, hkn, hkM, hkU, hkA, hkB, hkC, -⟩ := hS j _ _ rfl rfl _ rfl
      obtain ⟨hK1, hK2, hpk⟩ := hran j hj _ rfl _ rfl
      refine ⟨(a, u), ?_⟩
      rw [hD j, rep_ran _ ⟨hK1, hK2⟩ hpk]
      refine ⟨rfl, Int64.ofNat i.1, ?_⟩
      rw [rep_pair _ _ hkO hkn hkM hkU hkA hkB hkC]
      exact ⟨ha, hu⟩
    have hstepAt : ∀ j (hj : j < xs.length),
        rep (f^[j] (pend₀, Alg.zero, 0)).1 (Int64.ofNat i.1) (ys[xs.length - j]'(by omega)) →
        rep (Sf (D j)) (xs[xs.length - 1 - j]'(by omega), ys[xs.length - j]'(by omega))
          (ys[xs.length - 1 - j]'(by omega)) := by
      intro j hj hu
      have h := hst (xs.length - 1 - j) (by omega)
      rw [gi (xs.length - 1 - j + 1) (xs.length - j) (by omega) (by omega) (by omega)] at h
      exact (hSf j (by omega) _ _).2 ⟨hmem j (by omega) _ _ (hel1 j hj) hu, h⟩
    have hchain : ∀ j (hj : j ≤ xs.length),
        rep (f^[j] (pend₀, Alg.zero, 0)).1 (Int64.ofNat i.1) (ys[xs.length - j]'(by omega)) := by
      intro j
      induction j with
      | zero => intro _; rw [gi (xs.length - 0) xs.length (by omega) (by omega) (Nat.sub_zero _)]; exact hst0
      | succ j ih =>
        intro hj
        rw [hstep1, gi (xs.length - (j + 1)) (xs.length - 1 - j) (by omega) (by omega) (by omega)]
        exact ⟨_, _, hel1 j (by omega), ih (by omega), hstepAt j (by omega) (ih (by omega))⟩
    intro t ht
    have h := hstepAt (xs.length - 1 - t) (by omega) (hchain _ (by omega))
    rw [gx (xs.length - 1 - (xs.length - 1 - t)) t (by omega) ht (by omega),
      gi (xs.length - (xs.length - 1 - t)) (t + 1) (by omega) (by omega) (by omega),
      gi (xs.length - 1 - (xs.length - 1 - t)) t (by omega) (by omega) (by omega)] at h
    exact h

/-! ## `sum` -/

theorem nul_toInt : nul.toInt = -2 ^ 63 := by decide

/-- `Int64`'s `+` is `Int`'s up to a multiple of `2^64`. -/
theorem toInt_add_k (a b : Int64) : ∃ k : Int, (a + b).toInt = a.toInt + b.toInt + k * 2 ^ 64 := by
  have h64 : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := by decide
  rw [Int64.toInt_add, Int.bmod_def, h64]
  have := Int.emod_add_mul_ediv (a.toInt + b.toInt) (2 ^ 64)
  split
  · exact ⟨-((a.toInt + b.toInt) / 2 ^ 64), by omega⟩
  · exact ⟨-((a.toInt + b.toInt) / 2 ^ 64) - 1, by omega⟩

/-- `Int64`'s `+` is `Int`'s where the integer sum is in range. -/
theorem toInt_add_of (a b : Int64) (h1 : -2 ^ 63 ≤ a.toInt + b.toInt) (h2 : a.toInt + b.toInt < 2 ^ 63) :
    (a + b).toInt = a.toInt + b.toInt := by
  obtain ⟨k, hk⟩ := toInt_add_k a b
  have := Int64.le_toInt (a + b)
  have := Int64.toInt_lt (a + b)
  omega

theorem ne_nul_iff (x : Int64) : x ≠ nul ↔ x.toInt ≠ -2 ^ 63 := by
  rw [← nul_toInt, ne_eq, ne_eq, Int64.toInt_inj]

/-- **One `plus` step off a non-null second operand**: kept exactly where the first operand is not the null and
    the integer sum lies strictly between the null and `2^63`; the answer is then `Int64`'s `+`. -/
theorem plus_step (a b w : Int64) (hb : b ≠ nul) :
    (w = Ew.intStep Ew.add nul a b ∧ w ≠ nul ∧ (0 ≤ b ↔ a ≤ w)) ↔
      a ≠ nul ∧ -2 ^ 63 < a.toInt + b.toInt ∧ a.toInt + b.toInt < 2 ^ 63 ∧ w = a + b := by
  rw [intStep_add]
  by_cases han : a = nul
  · rw [if_pos (Or.inl han)]
    exact ⟨fun ⟨h1, h2, _⟩ => absurd h1 h2, fun ⟨h, _⟩ => absurd han h⟩
  rw [if_neg (fun h => h.elim han hb)]
  have hs : (0 : Int64).toInt = 0 := by decide
  have han' := (ne_nul_iff a).1 han
  have hb' := (ne_nul_iff b).1 hb
  have := Int64.le_toInt a
  have := Int64.toInt_lt a
  have := Int64.le_toInt b
  have := Int64.toInt_lt b
  have := Int64.le_toInt (a + b)
  have := Int64.toInt_lt (a + b)
  obtain ⟨k, hk⟩ := toInt_add_k a b
  rw [ne_nul_iff w, Int64.le_iff_toInt_le, Int64.le_iff_toInt_le, hs]
  constructor
  · rintro ⟨rfl, hw, h1, h2⟩
    by_cases h0 : 0 ≤ b.toInt
    · have := h1 h0
      refine ⟨han, ?_, ?_, rfl⟩ <;> omega
    · have : ¬ a.toInt ≤ (a + b).toInt := fun h => absurd (h2 h) (by omega)
      refine ⟨han, ?_, ?_, rfl⟩ <;> omega
  · rintro ⟨-, h1, h2, rfl⟩
    exact ⟨rfl, by omega, fun _ => by omega, fun _ => by omega⟩

-- the suffix sums of `xs` from `t`: in `Int64` (`Fd`) and in `Int` (`Sd`)
local notation "Fd(" xs ", " t ")" => List.foldr (· + ·) (0 : Int64) (List.drop t xs)
local notation "Sd(" xs ", " t ")" => List.sum (List.map Int64.toInt (List.drop t xs))

/-- **`sum`, read back**: an array `xs` of `X` goes to its `Int64` sum `xs.foldr (· + ·) 0` exactly where no element
    is q's null and every suffix sum `Σ_{s ≥ t} xs[s]`, taken in `Int`, lies strictly between the null `-2^63` and
    `2^63` — `plus` drops a row whose sum wraps or is the null, and the fold adds from the end. Bound values and
    hypotheses as `foldOn_on`'s at `Sf = fun D => plus D.val`, `e = col [0]` (`hR`, `hS`, `hran`, `hel` per-round
    bundles; `E`, `V` are `.long` there, bound by `let`). -/
theorem Arr.rep_sum {n : USize} (X : Vals (.arr .long) n)
    (T : Rel .long (.arr .long)) (hT : T = num (idU X) 0) (hn : n.toNat < 2 ^ 63)
    (hv : Vals.PickFits (.arr .long) X (List.range n.toNat)) (hp : (Rel.val T).1.toNat < 2 ^ 63)
    (hel : ∀ k, k ≤ (Rel.val T).1.toNat → ∀ a : ByteArray, a = whereBits (Rel.n T)
        (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf (Rel.val T)).2 (one k.toUInt64) (Rel.n T)) →
      ∀ pos : ByteArray, pos = Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul
        (gather 8 (add (Rel.n T) (slicesOf (Rel.val T)).1 (slicesOf (Rel.val T)).2) a)
        (one (k + 1).toUInt64) (len a).toUSize →
      Vals.PickFits .long (Rel.key T) ((List.range (len a)).map fun q => (Column.bitsAt a (q * 8) 8).toNat) ∧
      Vals.PickFits .long (Rel.val T).2.2.2 ((List.range (len a)).map fun q => (Column.bitsAt pos (q * 8) 8).toNat))
    (pend₀ : Rel .long .long) (hpend : pend₀ = top (A := .long) (Rel.key T) (col [0]))
    (hN : (Rel.n T).toNat * (([0] : List Int64).length.toUSize).toNat < USize.size)
    (h63 : (Rel.n T).toNat * (([0] : List Int64).length.toUSize).toNat < 2 ^ 63)
    (hA : Vals.PickFits .long (Rel.key T) ((List.range ((Rel.n T).toNat *
      (([0] : List Int64).length.toUSize).toNat)).map (· / (([0] : List Int64).length.toUSize).toNat)))
    (hB : Vals.PickFits .long (col [0]) ((List.range ((Rel.n T).toNat *
      (([0] : List Int64).length.toUSize).toNat)).map (· % (([0] : List Int64).length.toUSize).toNat)))
    (Sf : Rel (.prod .long .long) (.prod .long .long) → Rel (.prod .long .long) .long)
    (hSf : Sf = fun D => plus D.val)
    (step : Rel .long .long → Rel .long .long → Rel .long .long) (hstep : step = demandStep Sf)
    (elK : Nat → Rel .long .long) (hE : ∀ k, elK k = elR(T, k))
    (f : Rel .long .long × Rel .long .long × Nat → Rel .long .long × Rel .long .long × Nat)
    (hf : ∀ st, f st = rnd(st))
    (D : Nat → Rel (.prod .long .long) (.prod .long .long))
    (hD : ∀ k, D k = ran (pair (elK k) (f^[k] (pend₀, Alg.zero, 0)).1))
    (hR : let V := Obj.long; ∀ i (el : Rel .long .long) (pend P S : Rel .long .long), el = elK i →
      pend = (f^[i] (pend₀, Alg.zero, 0)).1 → P = (f^[i] (pend₀, Alg.zero, 0)).2.1 → S = step el pend → roundOK)
    (hS : let E := Obj.long; let V := Obj.long; ∀ i (el : Rel .long .long) (pend : Rel .long .long), el = elK i →
      pend = (f^[i] (pend₀, Alg.zero, 0)).1 → stepOn)
    (F : Rel .long .long) (hF : F = foldRows T pend₀ step)
    (jc : Vector Code 2) (hjc : jc = Obj.codes .long ck2(T°, F)) (hjO : codesOK(jc, ck2(T°, F)))
    (hjn : (Rel.n F).toNat < 2 ^ 63) (hjM : msum(jc, T°, F) < 2 ^ 63) (hjU : msum(jc, T°, F) < USize.size)
    (hjA : Vals.PickFits (.arr .long) (Rel.key (T°)) ((mpairs(jc, T°, F)).map Prod.fst))
    (hjC : Vals.PickFits .long (Rel.val F) ((mpairs(jc, T°, F)).map Prod.snd))
    (hran : let E := Obj.long; let V := Obj.long; ∀ k, k < (Rel.val T).1.toNat → ∀ P : Rel .long (.prod .long .long),
      P = pair (elK k) (f^[k] (pend₀, Alg.zero, 0)).1 → ranOK(P)) :
    ∀ (xs : List Int64) (w : Int64), rep (Alg.Arr.sum X) xs w ↔ (∃ i, X.row i = xs) ∧
      (∀ t, t ≤ xs.length → -2 ^ 63 < Sd(xs, t) ∧ Sd(xs, t) < 2 ^ 63) ∧ (∀ x ∈ xs, x ≠ nul) ∧
      w = xs.foldr (· + ·) 0 := by
  intro xs w
  have hSf' : ∀ k, k < (Rel.val T).1.toNat → ∀ (p : Int64 × Int64) (w : Int64), rep (Sf (D k)) p w ↔
      (∃ a, rep (D k) a p) ∧ (w = Ew.intStep Ew.add nul p.1 p.2 ∧ w ≠ nul ∧ (0 ≤ p.2 ↔ p.1 ≤ w)) := by
    intro k _ p w
    subst hSf
    obtain ⟨a, b⟩ := p
    show rep (plus (D k).val) (a, b) w ↔ _
    rw [rep_plus]
    exact and_congr ⟨fun ⟨i, h⟩ => ⟨_, i, rfl, h⟩, fun ⟨_, i, _, h⟩ => ⟨i, h⟩⟩ Iff.rfl
  rw [show Alg.Arr.sum X = foldOn (col [0]) Sf X by subst hSf; rfl,
    foldOn_on (col [0]) Sf X T hT hn hv hp hel pend₀ hpend hN h63 hA hB step hstep elK hE f hf D hD hR hS F hF jc
      hjc hjO hjn hjM hjU hjA hjC hran _ hSf' xs w]
  refine and_congr Iff.rfl ?_
  have h1 : ([0] : List Int64).length < USize.size := by
    show 1 < USize.size; rcases USize.size_eq with e | e <;> omega
  have hcons : ∀ t (ht : t < xs.length), Sd(xs, t) = (xs[t]).toInt + Sd(xs, t + 1) ∧
      Fd(xs, t) = xs[t] + Fd(xs, t + 1) := by
    intro t ht; rw [List.drop_eq_getElem_cons ht, List.map_cons, List.sum_cons]; exact ⟨rfl, rfl⟩
  have hlast : Sd(xs, xs.length) = 0 ∧ Fd(xs, xs.length) = 0 := by simp
  constructor
  · rintro ⟨ys, hy, ⟨p, hp⟩, hst, rfl⟩
    rw [Vals.row_atom, col_get [0] h1 p] at hp
    simp only [List.getElem_singleton] at hp
    -- from the end: `ys[t]` is the suffix sum from `t`, in range, not the null
    have key : ∀ d t (ht : t ≤ xs.length), t + d = xs.length →
        ys[t]'(by omega) ≠ nul ∧ (ys[t]'(by omega)).toInt = Sd(xs, t) ∧ ys[t]'(by omega) = Fd(xs, t) ∧
          -2 ^ 63 < Sd(xs, t) ∧ Sd(xs, t) < 2 ^ 63 := by
      intro d
      induction d with
      | zero =>
        intro t ht hd
        obtain rfl : t = xs.length := by omega
        rw [← hp, hlast.1, hlast.2]
        exact ⟨by decide, by decide, rfl, by decide, by decide⟩
      | succ d ih =>
        intro t ht hd
        obtain ⟨hb, hbi, hbf, -, -⟩ := ih (t + 1) (by omega) (by omega)
        have hs := hst t (by omega)
        obtain ⟨-, h1, h2, hw⟩ := (plus_step _ _ _ hb).1 hs
        obtain ⟨eS, eF⟩ := hcons t (by omega)
        refine ⟨hs.2.1, ?_, by rw [hw, hbf, eF], ?_, ?_⟩
        · rw [hw, toInt_add_of _ _ (by omega) h2, hbi, eS]
        · rw [eS, ← hbi]; exact h1
        · rw [eS, ← hbi]; exact h2
    refine ⟨fun t ht => (key (xs.length - t) t ht (by omega)).2.2.2, fun x hx => ?_, ?_⟩
    · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
      exact ((plus_step _ _ _ (key (xs.length - (t + 1)) (t + 1) ht (by omega)).1).1 (hst t ht)).1
    · rw [(key xs.length 0 (Nat.zero_le _) (Nat.zero_add _)).2.2.1, List.drop_zero]
  · rintro ⟨hb, hnn, rfl⟩
    have hq : ∀ d t (ht : t ≤ xs.length), t + d = xs.length → (Fd(xs, t)).toInt = Sd(xs, t) := by
      intro d
      induction d with
      | zero =>
        intro t ht hd
        obtain rfl : t = xs.length := by omega
        rw [hlast.1, hlast.2]; decide
      | succ d ih =>
        intro t ht hd
        have h := ih (t + 1) (by omega) (by omega)
        obtain ⟨eS, eF⟩ := hcons t (by omega)
        have hb' := hb t ht
        rw [eS] at hb'
        rw [eF, toInt_add_of _ _ (by omega) (by omega), h, eS]
    have h0' : 0 < (([0] : List Int64).length.toUSize).toNat := by
      rw [USize.toNat_ofNat_of_lt' h1]; decide
    refine ⟨(List.range (xs.length + 1)).map fun t => Fd(xs, t), by simp,
      ⟨⟨0, h0'⟩, by rw [Vals.row_atom, col_get [0] h1]; simp⟩, fun t ht => ?_, by simp⟩
    have ey : ∀ s (hs : s < xs.length + 1),
        ((List.range (xs.length + 1)).map fun t => Fd(xs, t))[s]'(by simp; omega) = Fd(xs, s) :=
      fun s hs => by simp
    rw [ey t (by omega), ey (t + 1) (by omega)]
    obtain ⟨eS, eF⟩ := hcons t ht
    have hq1 := hq (xs.length - (t + 1)) (t + 1) ht (by omega)
    have hb0 := hb t (by omega)
    rw [eS, ← hq1] at hb0
    exact (plus_step _ _ _ ((ne_nul_iff _).2 (by rw [hq1]; have := (hb (t + 1) ht).1; omega))).2
      ⟨hnn _ (List.getElem_mem ht), hb0.1, hb0.2, eF⟩

/-! ## `length` -/

/-- `+ 1` on `Int64.ofNat m` below `2^63 - 1` is `Int64.ofNat (m + 1)`, off the null. -/
theorem intStep_ofNat_succ (m : Nat) (hm : m + 1 < 2 ^ 63) :
    Ew.intStep Ew.add nul (Int64.ofNat m) 1 = Int64.ofNat (m + 1) := by
  have e1 : (Int64.ofNat m).toInt = m := Int64.toInt_ofNat_of_lt (by omega)
  have e2 : (Int64.ofNat (m + 1)).toInt = (m + 1 : Nat) := Int64.toInt_ofNat_of_lt (by omega)
  have e3 : (1 : Int64).toInt = 1 := by decide
  have hn1 : ¬ (Int64.ofNat m = nul ∨ (1 : Int64) = nul) := by
    rintro (h | h)
    · exact (ne_nul_iff _).2 (by omega) h
    · exact (ne_nul_iff _).2 (by rw [e3]; decide) h
  rw [intStep_add, if_neg hn1]
  apply Int64.toInt_inj.1
  rw [toInt_add_of _ _ (by omega) (by omega), e1, e2, e3]
  omega

/-- **`length`, read back**: an array `xs` of `X` goes to its length. `length X` is the fold of `col [0]` and
    `outr D ≫ succ (tilCol c)`, `c` the payload's count plus one (`length_eq`); `succ (tilCol c)` never meets its
    top, since an array of `X` is no longer than the payload (`slicesOf_row`). Bound values (`c`, `sc`, `Sf`, and
    `foldOn_on`'s) by their equations. Hypotheses: the payload's count plus one fits a `USize` and is below
    `2^63` (`hX`, `h63X`), `rep_succ`'s at `tilCol c` (`hsucc`), and `foldOn_on`'s, with `rep_comp`'s at
    `outr (D k)`, `sc` in each round (`hcomp`) — `hel`, `hR`, `hS`, `hran`, `hcomp` per-round bundles (`V` is `.long`
    there, bound by `let`). -/
theorem rep_length {E : Obj} {n : USize} (X : Vals (.arr E) n)
    (hX : X.1.toNat + 1 < USize.size) (h63X : X.1.toNat + 1 < 2 ^ 63)
    (c : USize) (hc : c = (X.1.toNat + 1).toUSize) (sc : Rel .long .long) (hsc : sc = succ (tilCol c))
    (hsucc : ∀ s : Arr .long c, s = valCol Ew.add Ew.va (longsOf (tilCol c)) (one 1) →
      ∀ cs : Vector Code 2, cs = codes .long #v[⟨c, s⟩, ⟨c, tilCol c⟩] →
        codesL(cs, (#v[⟨c, s⟩, ⟨c, tilCol c⟩] : Vector ((m : USize) × Arr .long m) 2)))
    (T : Rel .long (.arr E)) (hT : T = num (idU X) 0) (hn : n.toNat < 2 ^ 63)
    (hv : Vals.PickFits (.arr E) X (List.range n.toNat)) (hp : (Rel.val T).1.toNat < 2 ^ 63)
    (hel : ∀ k, k ≤ (Rel.val T).1.toNat → ∀ a : ByteArray, a = whereBits (Rel.n T)
        (Ew.cmp Ew.gt Ew.i64 Ew.va (slicesOf (Rel.val T)).2 (one k.toUInt64) (Rel.n T)) →
      ∀ pos : ByteArray, pos = Kernel.Ew.val Ew.sub Ew.i64 Ew.va nul
        (gather 8 (add (Rel.n T) (slicesOf (Rel.val T)).1 (slicesOf (Rel.val T)).2) a)
        (one (k + 1).toUInt64) (len a).toUSize →
      Vals.PickFits .long (Rel.key T) ((List.range (len a)).map fun q => (Column.bitsAt a (q * 8) 8).toNat) ∧
      Vals.PickFits E (Rel.val T).2.2.2 ((List.range (len a)).map fun q => (Column.bitsAt pos (q * 8) 8).toNat))
    (pend₀ : Rel .long .long) (hpend : pend₀ = top (A := .long) (Rel.key T) (col [0]))
    (hN : (Rel.n T).toNat * (([0] : List Int64).length.toUSize).toNat < USize.size)
    (h63 : (Rel.n T).toNat * (([0] : List Int64).length.toUSize).toNat < 2 ^ 63)
    (hA : Vals.PickFits .long (Rel.key T) ((List.range ((Rel.n T).toNat *
      (([0] : List Int64).length.toUSize).toNat)).map (· / (([0] : List Int64).length.toUSize).toNat)))
    (hB : Vals.PickFits .long (col [0]) ((List.range ((Rel.n T).toNat *
      (([0] : List Int64).length.toUSize).toNat)).map (· % (([0] : List Int64).length.toUSize).toNat)))
    (Sf : Rel (.prod E .long) (.prod E .long) → Rel (.prod E .long) .long)
    (hSf : Sf = fun D => outr D ≫ sc)
    (step : Rel .long E → Rel .long .long → Rel .long .long) (hstep : step = demandStep Sf)
    (elK : Nat → Rel .long E) (hE : ∀ k, elK k = elR(T, k))
    (f : Rel .long .long × Rel .long .long × Nat → Rel .long .long × Rel .long .long × Nat)
    (hf : ∀ st, f st = rnd(st))
    (D : Nat → Rel (.prod E .long) (.prod E .long))
    (hD : ∀ k, D k = ran (pair (elK k) (f^[k] (pend₀, Alg.zero, 0)).1))
    (hR : let V := Obj.long; ∀ i (el : Rel .long E) (pend P S : Rel .long .long), el = elK i →
      pend = (f^[i] (pend₀, Alg.zero, 0)).1 → P = (f^[i] (pend₀, Alg.zero, 0)).2.1 → S = step el pend → roundOK)
    (hS : let V := Obj.long; ∀ i (el : Rel .long E) (pend : Rel .long .long), el = elK i →
      pend = (f^[i] (pend₀, Alg.zero, 0)).1 → stepOn)
    (F : Rel .long .long) (hF : F = foldRows T pend₀ step)
    (jc : Vector Code 2) (hjc : jc = Obj.codes .long ck2(T°, F)) (hjO : codesOK(jc, ck2(T°, F)))
    (hjn : (Rel.n F).toNat < 2 ^ 63) (hjM : msum(jc, T°, F) < 2 ^ 63) (hjU : msum(jc, T°, F) < USize.size)
    (hjA : Vals.PickFits (.arr E) (Rel.key (T°)) ((mpairs(jc, T°, F)).map Prod.fst))
    (hjC : Vals.PickFits .long (Rel.val F) ((mpairs(jc, T°, F)).map Prod.snd))
    (hran : let V := Obj.long; ∀ k, k < (Rel.val T).1.toNat → ∀ P : Rel .long (.prod E .long),
      P = pair (elK k) (f^[k] (pend₀, Alg.zero, 0)).1 → ranOK(P))
    (hcomp : ∀ rd, rd < (Rel.val T).1.toNat → ∀ kc : Vector Code 2, kc = Obj.codes .long ck2(outr (D rd), sc) →
      codesOK(kc, ck2(outr (D rd), sc)) ∧ (Rel.n sc).toNat < 2 ^ 63 ∧ msum(kc, outr (D rd), sc) < 2 ^ 63 ∧
      msum(kc, outr (D rd), sc) < USize.size ∧
      Vals.PickFits (.prod E .long) (Rel.key (outr (D rd))) ((mpairs(kc, outr (D rd), sc)).map Prod.fst) ∧
      Vals.PickFits .long (Rel.val sc) ((mpairs(kc, outr (D rd), sc)).map Prod.snd)) :
    ∀ (xs : List E.El) (w : Int64), rep (length X) xs w ↔ (∃ i, X.row i = xs) ∧ w = Int64.ofNat xs.length := by
  intro xs w
  have hcN : c.toNat = X.1.toNat + 1 := by rw [hc]; exact USize.toNat_ofNat_of_lt' hX
  -- `sc` on `m` below the payload's count is `m + 1`
  have hsc' : ∀ m w, m < X.1.toNat → (rep sc (Int64.ofNat m) w ↔ w = Int64.ofNat (m + 1)) := by
    intro m w hm
    subst hsc
    rw [rep_succ (tilCol c) _ rfl _ rfl (hsucc _ rfl _ rfl), intStep_ofNat_succ m (by omega)]
    simp only [Vals.row_atom, tilCol_get]
    constructor
    · rintro ⟨-, h, -⟩; exact h
    · rintro rfl; exact ⟨⟨⟨m, by omega⟩, rfl⟩, rfl, ⟨m + 1, by omega⟩, rfl⟩
  have hSf' : ∀ k, k < (Rel.val T).1.toNat → ∀ (p : E.El × Int64) (w : Int64), rep (Sf (D k)) p w ↔
      (∃ a, rep (D k) a p) ∧ rep sc p.2 w := by
    intro k hk p w
    obtain ⟨hK1, hK2, hpk⟩ := hran k hk _ rfl _ rfl
    obtain ⟨hcO, hcn, hcM, hcU, hcA, hcC⟩ := hcomp k hk _ rfl
    subst hSf
    show rep (outr (D k) ≫ sc) p w ↔ _
    rw [rep_comp _ _ hcO hcn hcM hcU hcA hcC, rep_outr, hD k, rep_ran _ ⟨hK1, hK2⟩ hpk]
    constructor
    · rintro ⟨y, ⟨z, ⟨rfl, hz⟩, rfl⟩, hy⟩; exact ⟨⟨p, rfl, hz⟩, hy⟩
    · rintro ⟨⟨a, rfl, hz⟩, hy⟩; exact ⟨a.2, ⟨a, ⟨rfl, hz⟩, rfl⟩, hy⟩
  rw [length_eq X hX, show foldOn (col [0]) (fun D => outr D ≫ succ (tilCol (X.1.toNat + 1).toUSize)) X =
      foldOn (col [0]) Sf X by subst hSf hsc hc; rfl,
    foldOn_on (col [0]) Sf X T hT hn hv hp hel pend₀ hpend hN h63 hA hB step hstep elK hE f hf D hD hR hS F hF jc
      hjc hjO hjn hjM hjU hjA hjC hran _ hSf' xs w]
  have h1 : ([0] : List Int64).length < USize.size := by
    show 1 < USize.size; rcases USize.size_eq with e | e <;> omega
  have hL : (∃ i, X.row i = xs) → xs.length ≤ X.1.toNat := by
    rintro ⟨⟨i, hi⟩, rfl⟩
    obtain ⟨h1, h2, -⟩ := slicesOf_row X (by omega) hi
    omega
  constructor
  · rintro ⟨hx, ys, hy, ⟨p, hp⟩, hst, hw⟩
    have hLx := hL hx
    rw [Vals.row_atom, col_get [0] h1 p] at hp
    simp only [List.getElem_singleton] at hp
    -- from the end: `ys[t]` counts the elements from `t`
    have key : ∀ d t (ht : t ≤ xs.length), t + d = xs.length →
        ys[t]'(by omega) = Int64.ofNat (xs.length - t) := by
      intro d
      induction d with
      | zero =>
        intro t ht hd
        obtain rfl : t = xs.length := by omega
        rw [← hp, Nat.sub_self]; rfl
      | succ d ih =>
        intro t ht hd
        have h : rep sc (ys[t + 1]'(by omega)) (ys[t]'(by omega)) := hst t (by omega)
        rw [ih (t + 1) (by omega) (by omega), hsc' _ _ (by omega)] at h
        rw [h]; congr 1; omega
    exact ⟨hx, by rw [hw, key xs.length 0 (Nat.zero_le _) (Nat.zero_add _), Nat.sub_zero]⟩
  · rintro ⟨hx, rfl⟩
    have hLx := hL hx
    have h0' : 0 < (([0] : List Int64).length.toUSize).toNat := by
      rw [USize.toNat_ofNat_of_lt' h1]; decide
    refine ⟨hx, (List.range (xs.length + 1)).map fun t => Int64.ofNat (xs.length - t), by simp,
      ⟨⟨0, h0'⟩, ?_⟩, fun t ht => ?_, ?_⟩
    · rw [Vals.row_atom, col_get [0] h1]
      simp only [List.getElem_map, List.getElem_range, List.getElem_singleton, Nat.sub_self]; rfl
    · simp only [List.getElem_map, List.getElem_range]
      rw [hsc' _ _ (by omega)]; congr 1; omega
    · simp only [List.getElem_map, List.getElem_range, Nat.sub_zero]

#print axioms foldOn_on
#print axioms plus_step
#print axioms Arr.rep_sum
#print axioms rep_length

end FoldOn

end LeetQ.Rel.Rep
