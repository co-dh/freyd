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

-- codes `cs` of two long columns `ps` faithful and well formed: `RepOps`' `codesOK`, rows read by `Arr.get`
set_option hygiene false in
local notation "codesOK(" cs ", " ps ")" => ((∀ {k l : Nat} (hk : k < 2) (hl : l < 2) {i j : Nat}
    (hi : i < (ps[k]'hk).1.toNat) (hj : j < (ps[l]'hl).1.toNat),
    Column.idAt (cs[k]'hk).b (cs[k]'hk).w i = Column.idAt (cs[l]'hl).b (cs[l]'hl).w j ↔
      Arr.get (ps[k]'hk).2 ⟨i, hi⟩ = Arr.get (ps[l]'hl).2 ⟨j, hj⟩) ∧
  ∀ {k : Nat} (hk : k < 2),
    ((cs[k]'hk).w = 1 ∨ (cs[k]'hk).w = 2 ∨ (cs[k]'hk).w = 4 ∨ (cs[k]'hk).w = 8 ∨ (cs[k]'hk).w = 16 ∨
      (cs[k]'hk).w = 32 ∨ (cs[k]'hk).w = 64) ∧
    (cs[k]'hk).n = (ps[k]'hk).1 ∧ (cs[k]'hk).b.size = ((cs[k]'hk).n.toNat * (cs[k]'hk).w + 7) / 8)

/-- `valCol` of `Ew.add` against the long `1`, element `i`: `Ew.intStep` of `+ 1`. -/
theorem valCol_succ_get {n : USize} (U : Arr .long n) (i : Fin n.toNat) :
    (valCol (n := n) Ew.add Ew.va (longsOf U) (one 1)).get i = Ew.intStep Ew.add nul (U.get i) 1 := by
  rw [Arr.get_long_bytes _ rfl, val_va_get _ _ _ _ i.2, bitsAt_one, longsOf_get U i.2,
    show (1 : UInt64) = (1 : Int64).toUInt64 from rfl, valStep_i64, Int64.toInt64_toUInt64]

/-- **`rep (succ U)`**: `u` in `U` to `u + 1` (`Ew.intStep`, wrapping), where that is an element of `U` again — so
    the top of `U` goes nowhere, and so does `Int64.maxValue`, whose wrapped successor is q's null unless `U` holds
    the null. Hypotheses: the defining equations of the successor column `s` and the codes `cs`, and `cs` faithful
    and well formed (`codesOK`). -/
theorem rep_succ {n : USize} (U : Vals (.atom .long) n) (s : Arr .long n)
    (hs : s = valCol Ew.add Ew.va (longsOf U) (one 1)) (cs : Vector Code 2)
    (hcs : cs = codes .long #v[⟨n, s⟩, ⟨n, U⟩]) (hc : codesOK(cs, (#v[⟨n, s⟩, ⟨n, U⟩] : Vector ((m : USize) × Arr .long m) 2)))
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

#print axioms rep_succ
#print axioms holds_where
#print axioms rep_arith
#print axioms rep_plus
#print axioms rep_minus
#print axioms rep_times
#print axioms rep_div
#print axioms rep_mod

end LeetQ.Rel.Rep
