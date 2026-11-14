/-
  `Obj.codes` faithful and well formed at every side built from the covered atoms by `.prod`, `.arr` and
  `.sum`: one recursion on `Obj` over the node theorems (`codes_prod_faithful_wf`, `codes_arr_faithful_wf`,
  `codes_sum_faithful_wf`) and the atoms' several-part theorems.
-/
import LeetQ.Rel.KernelWF.CodesArr
import LeetQ.Rel.KernelWF.CodesSymParts

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

/-- The bounds `Obj.codes` needs at every node of `A`, on the parts it hands that node: each node theorem's
    size bounds and `Vals.PickFits`; at an atom, the kinds a several-part theorem covers — boolean, a small
    integral side of dense parts, a symbol side whose dictionaries summed fit a `USize`. -/
def _root_.LeetQ.Rel.Obj.CodesFit : (A : Obj) → {p : Nat} → Vector (Part A) p → Prop
  | .atom t, p, cs => (cs.toList.map (·.1.toNat)).sum < USize.size ∧
    (t = .boolean ∨
      (∃ k₀, orderKind t = some k₀ ∧ (k₀ = .u8 ∨ k₀ = .i16 ∨ k₀ = .i32) ∧
        ∀ k (hk : k < p), ∃ b, (cs[k]'hk).2.enc = .bytes b) ∨
      (t = .symbol ∧
        (cs.toList.map fun c => match c.2.enc with | .enum _ o _ => o.size - 1 | _ => c.1.toNat).sum < USize.size))
  | .prod a b, _, cs => (cs.toList.map (·.1.toNat)).sum < USize.size ∧
    Obj.CodesFit a (cs.map fun c => (⟨c.1, c.2.1⟩ : Part a)) ∧ Obj.CodesFit b (cs.map fun c => (⟨c.1, c.2.2⟩ : Part b))
  | .arr b, p, cs => (∀ k (hk : k < p), Vals.PickFits (.arr b) (cs[k]'hk).2 (List.range (cs[k]'hk).1.toNat)) ∧
    (cs.toList.map (·.1.toNat)).sum < USize.size ∧
    (cs.toList.map fun c => ((List.range c.1.toNat).map fun r =>
      if h : r < c.1.toNat then (Vals.row (A := .arr b) c.2 ⟨r, h⟩).length else 0).sum).sum < 2 ^ 63 ∧
    (cs.toList.map fun c => ((List.range c.1.toNat).map fun r =>
      if h : r < c.1.toNat then (Vals.row (A := .arr b) c.2 ⟨r, h⟩).length else 0).sum).sum < USize.size ∧
    Obj.CodesFit b (cs.map fun c => (⟨c.2.1, c.2.2.2.2⟩ : Part b))
  | .sum a b, p, cs₀ =>
    (cs₀.toList.map (·.1.toNat)).sum < USize.size ∧
    (∀ k (hk : k < p), Vals.PickFits (.sum a b) (cs₀[k]'hk).2 (List.range (cs₀[k]'hk).1.toNat)) ∧
    (∀ k (hk : k < p), (cs₀[k]'hk).2.held.1.toNat < 2 ^ 61) ∧ (∀ k (hk : k < p), (cs₀[k]'hk).2.held.2.1.toNat < 2 ^ 61) ∧
    Obj.CodesFit a ((cs₀.map fun c => (⟨c.1, c.2.held⟩ : Part (.sum a b))).map
      fun c => (⟨c.2.1, c.2.2.2.2.2.1⟩ : Part a)) ∧
    Obj.CodesFit b ((cs₀.map fun c => (⟨c.1, c.2.held⟩ : Part (.sum a b))).map
      fun c => (⟨c.2.2.1, c.2.2.2.2.2.2⟩ : Part b))

/-- Every part `cut` answers is on the cut code's lane. -/
theorem cut_lane {p : Nat} (c : Code) (ns : Vector USize p) {k l : Nat} (hk : k < p) (hl : l < p) :
    ((c.cut ns)[k]'hk).w = ((c.cut ns)[l]'hl).w := by
  unfold Code.cut; split <;> simp

/-- **`Obj.codes` is faithful and well formed, on one lane, at every side the recursion covers**: equal codes
    exactly at equal rows, jointly across the parts; each code a lane of `1 … 64` bits, `⌈n·w/8⌉` bytes, ids below
    `card` under a byte; one lane across the parts. `Obj.CodesFit` holds the bounds node by node. -/
theorem codes_faithful_wf (A : Obj) : ∀ {p : Nat} (cs : Vector (Part A) p), A.CodesFit cs →
    ((∀ {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (cs[k]'hk).1.toNat)
        (hj : j < (cs[l]'hl).1.toNat),
        Column.idAt ((Obj.codes A cs)[k]'hk).b ((Obj.codes A cs)[k]'hk).w i =
          Column.idAt ((Obj.codes A cs)[l]'hl).b ((Obj.codes A cs)[l]'hl).w j ↔
        Vals.row (A := A) (cs[k]'hk).2 ⟨i, hi⟩ = Vals.row (A := A) (cs[l]'hl).2 ⟨j, hj⟩) ∧
      ∀ {k : Nat} (hk : k < p),
        let c := (Obj.codes A cs)[k]'hk
        (c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = (cs[k]'hk).1 ∧
        c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
        (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)) ∧
      ∀ {k l : Nat} (hk : k < p) (hl : l < p), ((Obj.codes A cs)[k]'hk).w = ((Obj.codes A cs)[l]'hl).w := by
  induction A with
  | atom t =>
    intro p cs ⟨hN, ht⟩
    rcases ht with rfl | ⟨k₀, ht, hk₀, hd⟩ | ⟨rfl, hD⟩
    · refine ⟨⟨fun hk hl _ _ hi hj => codes_boolean_faithful cs hk hl hi hj, fun hk => ?_⟩, fun hk hl => ?_⟩
      · obtain ⟨h1, h2, h3, h4⟩ := codes_boolean_wf cs hk
        exact ⟨Or.inl h2, h1, h3, h4⟩
      · rw [(codes_boolean_wf cs hk).2.1, (codes_boolean_wf cs hl).2.1]
    · refine ⟨⟨fun hk hl _ _ hi hj => codes_small_int_parts_faithful ht hk₀ cs hd hN hk hl hi hj,
        fun hk => codes_small_int_parts_wf ht hk₀ cs hN hk⟩, fun hk hl => ?_⟩
      rw [codes_small_int_cut ht hk₀ cs (by omega)]; exact cut_lane _ _ hk hl
    · refine ⟨⟨fun hk hl _ _ hi hj => codes_symbol_parts_faithful cs hN hD hk hl hi hj,
        fun hk => codes_symbol_parts_wf cs hN hk⟩, fun hk hl => ?_⟩
      rw [codes_symbol_cut cs (by omega)]; exact cut_lane _ _ hk hl
  | prod a b iha ihb =>
    intro p cs ⟨hN, ha, hb⟩
    exact codes_prod_faithful_wf cs rfl rfl rfl rfl (iha _ ha).1 (iha _ ha).2 (ihb _ hb).1 (ihb _ hb).2 hN
  | arr b ih =>
    intro p cs ⟨hfit, hN, hC, hCU, hb⟩
    exact codes_arr_faithful_wf cs rfl rfl (ih _ hb).1 (ih _ hb).2 (fun hk => hfit _ hk) hN hC hCU
  | sum a b iha ihb =>
    intro p cs₀ ⟨hN, hfit, hLa, hLb, ha, hb⟩
    exact codes_sum_faithful_wf cs₀ rfl rfl rfl rfl rfl (iha _ ha).1 (iha _ ha).2 (ihb _ hb).1 (ihb _ hb).2
      (fun hk => by simpa using hLa _ hk) (fun hk => by simpa using hLb _ hk) hN (fun hk => hfit _ hk)

#print axioms codes_faithful_wf

end LeetQ.Rel.Alg
