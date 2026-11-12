/-
  A sum side's joint codes, faithful and well formed, from its two sides' — the `.sum` branch of
  `Obj.codes` in the shape `codes_prod_faithful_wf` has, so one theorem by recursion on `Obj` can follow.

  Every index in a statement here carries its bound explicitly (`xs[k]'hk`): left to `get_elem_tactic`,
  the index proofs of this many binders ran Lean out of memory before any tactic.
-/
import LeetQ.Rel.KernelWF.CodesProdFaithful
import LeetQ.Rel.KernelWF.RazeRowRec

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

/-- A long column's dense payload holds its `n` longs. -/
theorem len_longsOf {n : USize} (x : Arr .long n) : len (longsOf x) = n.toNat := by
  obtain ⟨ws, hws⟩ : ∃ ws, longWords n x.enc = some ws := by
    rcases KernelWF.long_cases x.wf with ⟨b, h⟩ | ⟨M, P, h⟩ <;> simp [longWords, h]
  obtain ⟨B, hB, -, -, hS⟩ := Arr.dense_long x hws
  have hL : longsOf x = B := by
    have e : longBytes n x.enc = some B := by
      rcases hB with h | ⟨md, pk, h, rfl⟩ <;> simp only [longBytes, h] <;> rfl
    exact Option.some_inj.1 ((Option.some_get _).trans e)
  rw [hL]; exact hS

/-- **`Code.gather` at any index column**: code `j` of `c@i` is code `i[j]` of `c` where `i[j]` is below
    `c.n`, else `0` — `gather_spec` without its every-index-in-range hypothesis. -/
theorem gather_get (c : Code) (i : ByteArray) (hl : len i < USize.size)
    (hcw : c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64)
    (hcb : 8 ≤ c.w → 8 * c.b.size = c.w * c.n.toNat) :
    (Code.gather c i).w = c.w ∧ (Code.gather c i).n.toNat = len i ∧ (Code.gather c i).card = c.card ∧
    ∀ j < len i, Column.idAt (Code.gather c i).b c.w j =
      if (Column.bitsAt i (j * 8) 8).toNat < c.n.toNat then
        Column.idAt c.b c.w (Column.bitsAt i (j * 8) 8).toNat else 0 := by
  unfold Code.gather longCount
  simp only [need, dif_pos hl]
  refine ⟨trivial, USize.toNat_ofNat_of_lt' hl, trivial, fun j hj => ?_⟩
  unfold Code.kind
  split
  next _ hk =>
    rcases laneKind_some hk with ⟨-, h1⟩ | ⟨h, -⟩
    · rw [h1, idAt_one, idAt_one, bitAt_gatherBits c.n c.b i j hj]; split <;> simp
    · exact absurd rfl h
  next _ k hne hk =>
    rcases laneKind_some hk with ⟨h, -⟩ | ⟨-, hw8, hq, -⟩
    · exact absurd h hne
    have h1 : k.width.toUSize.toNat = k.width := lane_toNat (by omega)
    have hs := (gatherBytes_spec k.width.toUSize (by omega) 0 c.b i).2 j hj
    have hd : c.b.size / k.width = c.n.toNat := by
      have := hcb (by omega); rw [hw8, Nat.mul_assoc] at this
      rw [show c.b.size = k.width * c.n.toNat by omega, Nat.mul_div_cancel_left _ (by omega)]
    rw [h1, hd] at hs
    rw [hw8, idAt_lane _ (by omega), idAt_lane _ (by omega), hs]
    split <;> simp
  next _ _ =>
    have h1 : c.w.toUSize.toNat = c.w := lane_toNat (by omega)
    have hg := idAt_gatherPacked c.n c.w.toUSize c.w.toUSize 0 c.b i (by rw [h1]; omega)
      (fun _ _ => by rw [h1]; exact idAt_lt _ _ _ (by omega)) (by rw [h1]; exact Nat.two_pow_pos _) j hj
    rw [h1] at hg
    rw [hg]; split <;> simp

/-- **`place` read back** at any clamp and offset of a long's range: row `k`'s position clamped into
    `[0, p₀ + τ·p₁]`, plus `o₀ + τ·o₁`, `τ` the row's tag as `0`/`1` (`place_off_get` at every argument). -/
theorem place_lin_get {a b : Obj} {n : USize} (x : Vals (.sum a b) n) {p₀ p₁ o₀ o₁ : Int}
    (h0 : -2 ^ 61 < p₀ ∧ p₀ < 2 ^ 61) (h1 : -2 ^ 61 < p₁ ∧ p₁ < 2 ^ 61)
    (h2 : -2 ^ 61 < o₀ ∧ o₀ < 2 ^ 61) (h3 : -2 ^ 61 < o₁ ∧ o₁ < 2 ^ 61) (k : Fin n.toNat) :
    ((place x p₀ p₁ o₀ o₁).get k).toInt =
      max (min (x.2.2.2.1.get k).toInt (p₀ + if x.2.2.1.get k then p₁ else 0)) 0 +
        (o₀ + if x.2.2.1.get k then o₁ else 0) := by
  obtain ⟨l, r, tag, idx, xa, xb⟩ := x
  dsimp only
  unfold place
  rw [Arr.get_long_bytes _ rfl]
  dsimp only
  simp only [val_vv_get _ _ _ _ k.2, val_va_get _ _ _ _ k.2, widen_bits_get _ _ k.2, longsOf_get _ k.2,
    ← Arr.get_bool_bits _ (KernelWF.enc_tagBits tag) k]
  have e0 := int_bits_toInt p₀ (by omega) (by omega)
  have e1 := int_bits_toInt p₁ (by omega) (by omega)
  have ez := int_bits_toInt 0 (by decide) (by decide)
  have eo0 := int_bits_toInt o₀ (by omega) (by omega)
  have eo1 := int_bits_toInt o₁ (by omega) (by omega)
  have eI := congrArg Int64.toInt (Int64.toInt64_toUInt64 (idx.get k))
  generalize Column.bitsAt (int p₁) 0 8 = K1 at e1 ⊢
  generalize Column.bitsAt (int p₀) 0 8 = K0 at e0 ⊢
  generalize Column.bitsAt (int o₁) 0 8 = O1 at eo1 ⊢
  generalize Column.bitsAt (int o₀) 0 8 = O0 at eo0 ⊢
  generalize Column.bitsAt (int 0) 0 8 = Z at ez ⊢
  generalize (idx.get k).toUInt64 = I at eI ⊢
  generalize tag.get k = t
  have hT : -2 ^ 63 < (if t then (1 : UInt64) else 0).toInt64.toInt := by cases t <;> decide
  have m1 := (valStep_int (y := K1) hT (by omega)).2.2 t rfl
  rw [e1] at m1
  have l1 := (valStep_int (y := K0) (by rw [m1]; split <;> omega) (by omega)).1
    (by rw [m1]; split <;> omega) (by rw [m1]; split <;> omega)
  rw [m1, e0] at l1
  have mo := (valStep_int (y := O1) hT (by omega)).2.2 t rfl
  rw [eo1] at mo
  have ao := (valStep_int (y := O0) (by rw [mo]; split <;> omega) (by omega)).1
    (by rw [mo]; split <;> omega) (by rw [mo]; split <;> omega)
  rw [mo, eo0] at ao
  generalize Ew.valStep Ew.add Ew.i64 nul.toUInt64 (Ew.valStep Ew.mul Ew.i64 nul.toUInt64 (if t then 1 else 0) K1) K0
    = LIN at l1 ⊢
  generalize Ew.valStep Ew.add Ew.i64 nul.toUInt64 (Ew.valStep Ew.mul Ew.i64 nul.toUInt64 (if t then 1 else 0) O1) O0
    = OFF at ao ⊢
  have hles := (valStep_min_max I LIN).1
  generalize Ew.valStep Ew.lesser Ew.i64 nul.toUInt64 I LIN = LES at hles ⊢
  have hgre := (valStep_min_max LES Z).2
  generalize Ew.valStep Ew.greater Ew.i64 nul.toUInt64 LES Z = G at hgre ⊢
  rw [(valStep_int (x := G) (y := OFF) (by rw [hgre]; omega) (by rw [ao]; split <;> omega)).1
    (by rw [hgre, ao]; split <;> omega) (by rw [hgre, hles, ao, ez, l1]; split <;> omega), hgre, hles, ao, ez, l1, eI]
  cases t <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- A sum row tagged `inl`, its left side holding a value, is its left value at its clamped position. -/
theorem row_sum_inl {a b : Obj} {n : USize} (x : Vals (.sum a b) n) {q : Nat} (hq : q < n.toNat)
    (ht : Column.bitAt (tagBits x.2.2.1) q = false) (hl : 0 < x.1.toNat) :
    Vals.row (A := .sum a b) x ⟨q, hq⟩ =
      .inl (Vals.row x.2.2.2.2.1 ⟨min (max (x.2.2.2.1.get ⟨q, hq⟩).toInt 0).toNat (x.1.toNat - 1), by omega⟩) := by
  obtain ⟨l, r, tag, idx, xa, xb⟩ := x
  dsimp only at ht hl ⊢
  rw [← Arr.get_bool_bits tag (enc_tagBits tag) ⟨q, hq⟩] at ht
  simp only [Vals.row, ht, Bool.false_eq_true, ↓reduceIte, dif_pos hl]
  rfl

/-- A sum row tagged `inr`, its right side holding a value, is its right value at its clamped position. -/
theorem row_sum_inr {a b : Obj} {n : USize} (x : Vals (.sum a b) n) {q : Nat} (hq : q < n.toNat)
    (ht : Column.bitAt (tagBits x.2.2.1) q = true) (hr : 0 < x.2.1.toNat) :
    Vals.row (A := .sum a b) x ⟨q, hq⟩ =
      .inr (Vals.row x.2.2.2.2.2 ⟨min (max (x.2.2.2.1.get ⟨q, hq⟩).toInt 0).toNat (x.2.1.toNat - 1), by omega⟩) := by
  obtain ⟨l, r, tag, idx, xa, xb⟩ := x
  dsimp only at ht hr ⊢
  rw [← Arr.get_bool_bits tag (enc_tagBits tag) ⟨q, hq⟩] at ht
  simp only [Vals.row, ht, ↓reduceIte, dif_pos hr]
  rfl

/-- **One part of a sum, its sides' codes gathered at `place`**: the left gather reads a row's own left code
    where it is tagged `inl` and `0` (a miss) where `inr`, the right gather the other way round; both keep
    their code's lane and bound, `n` codes in `⌈n·w/8⌉` bytes. -/
theorem sum_part_codes {a b : Obj} {n : USize} (x : Vals (.sum a b) n) (cl cr : Code)
    (hl : x.1.toNat < 2 ^ 61) (hr : x.2.1.toNat < 2 ^ 61) (hcl : cl.n = x.1) (hcr : cr.n = x.2.1)
    (hlw : cl.w = 1 ∨ cl.w = 2 ∨ cl.w = 4 ∨ cl.w = 8 ∨ cl.w = 16 ∨ cl.w = 32 ∨ cl.w = 64)
    (hrw : cr.w = 1 ∨ cr.w = 2 ∨ cr.w = 4 ∨ cr.w = 8 ∨ cr.w = 16 ∨ cr.w = 32 ∨ cr.w = 64)
    (hls : cl.b.size = (cl.n.toNat * cl.w + 7) / 8) (hrs : cr.b.size = (cr.n.toNat * cr.w + 7) / 8)
    (hsr : ∀ q (hq : q < n.toNat), Column.bitAt (tagBits x.2.2.1) q = true → 0 < x.2.1.toNat)
    (hsl : ∀ q (hq : q < n.toNat), Column.bitAt (tagBits x.2.2.1) q = false → 0 < x.1.toNat) :
    ((cl.gather (longsOf (place x ((x.1.toNat : Int) - 1) 0 0 x.1.toNat))).w = cl.w ∧
      (cl.gather (longsOf (place x ((x.1.toNat : Int) - 1) 0 0 x.1.toNat))).n = n ∧
      (cl.gather (longsOf (place x ((x.1.toNat : Int) - 1) 0 0 x.1.toNat))).card = cl.card ∧
      (cl.gather (longsOf (place x ((x.1.toNat : Int) - 1) 0 0 x.1.toNat))).b.size = (n.toNat * cl.w + 7) / 8) ∧
    ((cr.gather (longsOf (place x ((x.2.1.toNat : Int) - 1) 0 x.2.1.toNat (-(x.2.1.toNat : Int))))).w = cr.w ∧
      (cr.gather (longsOf (place x ((x.2.1.toNat : Int) - 1) 0 x.2.1.toNat (-(x.2.1.toNat : Int))))).n = n ∧
      (cr.gather (longsOf (place x ((x.2.1.toNat : Int) - 1) 0 x.2.1.toNat (-(x.2.1.toNat : Int))))).card =
        cr.card ∧
      (cr.gather (longsOf (place x ((x.2.1.toNat : Int) - 1) 0 x.2.1.toNat (-(x.2.1.toNat : Int))))).b.size =
        (n.toNat * cr.w + 7) / 8) ∧
    ∀ q (hq : q < n.toNat),
      Column.idAt (cl.gather (longsOf (place x ((x.1.toNat : Int) - 1) 0 0 x.1.toNat))).b cl.w q =
        (if Column.bitAt (tagBits x.2.2.1) q then 0 else
          Column.idAt cl.b cl.w (min (max (x.2.2.2.1.get ⟨q, hq⟩).toInt 0).toNat (x.1.toNat - 1))) ∧
      Column.idAt (cr.gather (longsOf (place x ((x.2.1.toNat : Int) - 1) 0 x.2.1.toNat
          (-(x.2.1.toNat : Int))))).b cr.w q =
        (if Column.bitAt (tagBits x.2.2.1) q then
          Column.idAt cr.b cr.w (min (max (x.2.2.2.1.get ⟨q, hq⟩).toInt 0).toNat (x.2.1.toNat - 1)) else 0) := by
  have hlen : ∀ P : Arr .long n, len (longsOf P) < USize.size := fun P => by
    rw [len_longsOf]; exact n.toNat_lt_size
  have hbl : 8 ≤ cl.w → 8 * cl.b.size = cl.w * cl.n.toNat := fun h => by
    rw [hls]; rcases hlw with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] at h ⊢ <;> omega
  have hbr : 8 ≤ cr.w → 8 * cr.b.size = cr.w * cr.n.toNat := fun h => by
    rw [hrs]; rcases hrw with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] at h ⊢ <;> omega
  obtain ⟨gw, gn, gc, gv⟩ := gather_get cl _ (hlen (place x ((x.1.toNat : Int) - 1) 0 0 x.1.toNat)) hlw hbl
  obtain ⟨rw', rn, rc, rv⟩ :=
    gather_get cr _ (hlen (place x ((x.2.1.toNat : Int) - 1) 0 x.2.1.toNat (-(x.2.1.toNat : Int)))) hrw hbr
  have gs := gather_size cl _ (hlen (place x ((x.1.toNat : Int) - 1) 0 0 x.1.toNat)) hlw
  have rs := gather_size cr _ (hlen (place x ((x.2.1.toNat : Int) - 1) 0 x.2.1.toNat (-(x.2.1.toNat : Int)))) hrw
  rw [len_longsOf] at gn rn gs rs
  refine ⟨⟨gw, USize.toNat_inj.1 gn, gc, gs⟩, ⟨rw', USize.toNat_inj.1 rn, rc, rs⟩, fun q hq => ⟨?_, ?_⟩⟩
  · have e := place_lin_get x (p₀ := (x.1.toNat : Int) - 1) (p₁ := 0) (o₀ := 0) (o₁ := x.1.toNat)
      (by omega) (by omega) (by omega) (by omega) ⟨q, hq⟩
    rw [Arr.get_bool_bits _ (enc_tagBits _)] at e
    have hnn : 0 ≤ ((place x ((x.1.toNat : Int) - 1) 0 0 x.1.toNat).get ⟨q, hq⟩).toInt := by
      rw [e]; split <;> omega
    rw [gv q (by rw [len_longsOf]; exact hq), longsOf_get _ hq, toNat_toUInt64_of_nonneg _ hnn, e, hcl]
    cases ht : Column.bitAt (tagBits x.2.2.1) q
    · have := hsl q hq ht
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [if_pos (by omega)]; congr 1; omega
    · simp only [↓reduceIte]
      rw [if_neg (by omega)]
  · have e := place_lin_get x (p₀ := (x.2.1.toNat : Int) - 1) (p₁ := 0) (o₀ := x.2.1.toNat)
      (o₁ := -(x.2.1.toNat : Int)) (by omega) (by omega) (by omega) (by omega) ⟨q, hq⟩
    rw [Arr.get_bool_bits _ (enc_tagBits _)] at e
    have hnn : 0 ≤ ((place x ((x.2.1.toNat : Int) - 1) 0 x.2.1.toNat (-(x.2.1.toNat : Int))).get ⟨q, hq⟩).toInt := by
      rw [e]; split <;> omega
    rw [rv q (by rw [len_longsOf]; exact hq), longsOf_get _ hq, toNat_toUInt64_of_nonneg _ hnn, e, hcr]
    cases ht : Column.bitAt (tagBits x.2.2.1) q
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [if_neg (by omega)]
    · have := hsr q hq ht
      simp only [↓reduceIte]
      rw [if_pos (by omega)]; congr 1; omega

/-- The three codes of a sum row — tag, left, right — agree with another's exactly when the rows do, given
    each side's codes agree exactly when its values do. -/
theorem sum_iff {α β : Type} {t₁ t₂ : Bool} {A₁ A₂ B₁ B₂ : Nat} {R₁ R₂ : α ⊕ β}
    (hl₁ : t₁ = false → ∃ x, R₁ = .inl x) (hr₁ : t₁ = true → ∃ y, R₁ = .inr y)
    (hl₂ : t₂ = false → ∃ x, R₂ = .inl x) (hr₂ : t₂ = true → ∃ y, R₂ = .inr y)
    (hA : t₁ = false → t₂ = false → (A₁ = A₂ ↔ R₁ = R₂)) (hB : t₁ = true → t₂ = true → (B₁ = B₂ ↔ R₁ = R₂)) :
    ((((if t₁ then 1 else 0) : Nat) = (if t₂ then 1 else 0) ∧ (if t₁ then 0 else A₁) = (if t₂ then 0 else A₂)) ∧
      (if t₁ then B₁ else 0) = (if t₂ then B₂ else 0)) ↔ R₁ = R₂ := by
  cases t₁ <;> cases t₂
  · simpa using hA rfl rfl
  · obtain ⟨x, rfl⟩ := hl₁ rfl; obtain ⟨y, rfl⟩ := hr₂ rfl; simp
  · obtain ⟨y, rfl⟩ := hr₁ rfl; obtain ⟨x, rfl⟩ := hl₂ rfl; simp
  · simpa using hB rfl rfl

/-- A sum side's codes are `pairCode` of the tags' codes, the left codes gathered at `place`, then the right
    codes gathered, each laid end to end, cut at the parts' counts — of the parts made `held`. -/
theorem codes_sum_eq {a b : Obj} {p : Nat} (cs₀ : Vector (Part (.sum a b)) p) {cs : Vector (Part (.sum a b)) p}
    {pa : Vector (Part a) p} {pb : Vector (Part b) p} {ca cb T GL GR : Vector Code p}
    (hcs : cs₀.map (fun c => (⟨c.1, c.2.held⟩ : Part (.sum a b))) = cs)
    (hpa : cs.map (fun c => (⟨c.2.1, c.2.2.2.2.2.1⟩ : Part a)) = pa)
    (hpb : cs.map (fun c => (⟨c.2.2.1, c.2.2.2.2.2.2⟩ : Part b)) = pb)
    (hca : Obj.codes a pa = ca) (hcb : Obj.codes b pb = cb)
    (hT : cs.map (fun c => (⟨1, c.1, 2, tagBits c.2.2.2.1⟩ : Code)) = T)
    (hGL : Vector.zipWith (fun c k => k.gather (longsOf (place c.2 ((c.2.1.toNat : Int) - 1) 0 0 c.2.1.toNat)))
      cs ca = GL)
    (hGR : Vector.zipWith (fun c k => k.gather
      (longsOf (place c.2 ((c.2.2.1.toNat : Int) - 1) 0 c.2.2.1.toNat (-(c.2.2.1.toNat : Int))))) cs cb = GR) :
    Obj.codes (.sum a b) cs₀ =
      (pairCode false (pairCode false (Code.cat T.toArray) (Code.cat GL.toArray)).1 (Code.cat GR.toArray)).1.cut
        (T.map (·.n)) := by
  subst hcs hpa hpb hca hcb hT hGL hGR
  rw [Obj.codes]
  simp [tuples, tuples.tupleCode]

#print axioms codes_sum_eq

end LeetQ.Rel.Alg
