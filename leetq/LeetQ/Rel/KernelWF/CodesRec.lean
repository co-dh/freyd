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
    (hcw : laneOK(c.w))
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
    (hlw : laneOK(cl.w))
    (hrw : laneOK(cr.w))
    (hls : cl.b.size = (cl.n.toNat * cl.w + 7) / 8) (hrs : cr.b.size = (cr.n.toNat * cr.w + 7) / 8)
    (hsr : ∀ q, q < n.toNat → Column.bitAt (tagBits x.2.2.1) q = true → 0 < x.2.1.toNat)
    (hsl : ∀ q, q < n.toNat → Column.bitAt (tagBits x.2.2.1) q = false → 0 < x.1.toNat) :
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

/-- **A sum side's codes are faithful and well formed, on one lane**, given its two sides' are, one lane each,
    on the parts `Obj.codes` hands them (each part made `held` first): the tag, the left codes gathered at
    each row's own left position (a miss, `0`, at an `inr` row), the right ones likewise, `pairCode`d in turn.
    Bounds: the parts' summed count a `USize`, each side's payload below `2⁶¹` (`place`'s longs stay in
    range), and the rows read back through `held` (`Vals.PickFits`). -/
theorem codes_sum_faithful_wf {a b : Obj} {p : Nat} (cs₀ : Vector (Part (.sum a b)) p)
    {cs : Vector (Part (.sum a b)) p} {pa : Vector (Part a) p} {pb : Vector (Part b) p} {ca cb : Vector Code p}
    (hcs : cs₀.map (fun c => (⟨c.1, c.2.held⟩ : Part (.sum a b))) = cs)
    (hpa : cs.map (fun c => (⟨c.2.1, c.2.2.2.2.2.1⟩ : Part a)) = pa)
    (hpb : cs.map (fun c => (⟨c.2.2.1, c.2.2.2.2.2.2⟩ : Part b)) = pb)
    (hca : Obj.codes a pa = ca) (hcb : Obj.codes b pb = cb)
    (hfa : (∀ {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (pa[k]'hk).1.toNat)
        (hj : j < (pa[l]'hl).1.toNat),
        Column.idAt (ca[k]'hk).b (ca[k]'hk).w i = Column.idAt (ca[l]'hl).b (ca[l]'hl).w j ↔
          Vals.row (pa[k]'hk).2 ⟨i, hi⟩ = Vals.row (pa[l]'hl).2 ⟨j, hj⟩) ∧
      ∀ {k : Nat} (hk : k < p),
        laneOK((ca[k]'hk).w) ∧
        (ca[k]'hk).n = (pa[k]'hk).1 ∧ (ca[k]'hk).b.size = ((ca[k]'hk).n.toNat * (ca[k]'hk).w + 7) / 8 ∧
        ((ca[k]'hk).w < 8 → (ca[k]'hk).card < USize.size ∧
          ∀ i < (ca[k]'hk).n.toNat, Column.idAt (ca[k]'hk).b (ca[k]'hk).w i < (ca[k]'hk).card))
    (hla : ∀ {k l : Nat} (hk : k < p) (hl : l < p), (ca[k]'hk).w = (ca[l]'hl).w)
    (hfb : (∀ {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (pb[k]'hk).1.toNat)
        (hj : j < (pb[l]'hl).1.toNat),
        Column.idAt (cb[k]'hk).b (cb[k]'hk).w i = Column.idAt (cb[l]'hl).b (cb[l]'hl).w j ↔
          Vals.row (pb[k]'hk).2 ⟨i, hi⟩ = Vals.row (pb[l]'hl).2 ⟨j, hj⟩) ∧
      ∀ {k : Nat} (hk : k < p),
        laneOK((cb[k]'hk).w) ∧
        (cb[k]'hk).n = (pb[k]'hk).1 ∧ (cb[k]'hk).b.size = ((cb[k]'hk).n.toNat * (cb[k]'hk).w + 7) / 8 ∧
        ((cb[k]'hk).w < 8 → (cb[k]'hk).card < USize.size ∧
          ∀ i < (cb[k]'hk).n.toNat, Column.idAt (cb[k]'hk).b (cb[k]'hk).w i < (cb[k]'hk).card))
    (hlb : ∀ {k l : Nat} (hk : k < p) (hl : l < p), (cb[k]'hk).w = (cb[l]'hl).w)
    (hLa : ∀ {k : Nat} (hk : k < p), (pa[k]'hk).1.toNat < 2 ^ 61)
    (hLb : ∀ {k : Nat} (hk : k < p), (pb[k]'hk).1.toNat < 2 ^ 61)
    (hN : (cs₀.toList.map (·.1.toNat)).sum < USize.size)
    (hfit : ∀ {k : Nat} (hk : k < p),
      Vals.PickFits (.sum a b) (cs₀[k]'hk).2 (List.range (cs₀[k]'hk).1.toNat)) :
    ((∀ {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (cs₀[k]'hk).1.toNat)
        (hj : j < (cs₀[l]'hl).1.toNat),
        Column.idAt ((Obj.codes (.sum a b) cs₀)[k]'hk).b ((Obj.codes (.sum a b) cs₀)[k]'hk).w i =
          Column.idAt ((Obj.codes (.sum a b) cs₀)[l]'hl).b ((Obj.codes (.sum a b) cs₀)[l]'hl).w j ↔
        Vals.row (A := .sum a b) (cs₀[k]'hk).2 ⟨i, hi⟩ = Vals.row (A := .sum a b) (cs₀[l]'hl).2 ⟨j, hj⟩) ∧
      ∀ {k : Nat} (hk : k < p),
        let c := (Obj.codes (.sum a b) cs₀)[k]'hk
        laneOK(c.w) ∧ c.n = (cs₀[k]'hk).1 ∧
        c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
        (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)) ∧
      ∀ {k l : Nat} (hk : k < p) (hl : l < p),
        ((Obj.codes (.sum a b) cs₀)[k]'hk).w = ((Obj.codes (.sum a b) cs₀)[l]'hl).w := by
  obtain ⟨T, hT⟩ : ∃ T, cs.map (fun c => (⟨1, c.1, 2, tagBits c.2.2.2.1⟩ : Code)) = T := ⟨_, rfl⟩
  obtain ⟨GL, hGL⟩ : ∃ GL, Vector.zipWith (fun c k => k.gather
      (longsOf (place c.2 ((c.2.1.toNat : Int) - 1) 0 0 c.2.1.toNat))) cs ca = GL := ⟨_, rfl⟩
  obtain ⟨GR, hGR⟩ : ∃ GR, Vector.zipWith (fun c k => k.gather
      (longsOf (place c.2 ((c.2.2.1.toNat : Int) - 1) 0 c.2.2.1.toNat (-(c.2.2.1.toNat : Int))))) cs cb = GR :=
    ⟨_, rfl⟩
  rw [codes_sum_eq cs₀ hcs hpa hpb hca hcb hT hGL hGR]
  obtain ⟨hfa, hwa⟩ := hfa
  obtain ⟨hfb, hwb⟩ := hfb
  have hcsk : ∀ k (hk : k < p), cs[k]'hk = ⟨(cs₀[k]'hk).1, (cs₀[k]'hk).2.held⟩ := fun k hk => by
    rw [← hcs, Vector.getElem_map]
  have hpak : ∀ k (hk : k < p), pa[k]'hk = ⟨(cs[k]'hk).2.1, (cs[k]'hk).2.2.2.2.2.1⟩ := fun k hk => by
    rw [← hpa, Vector.getElem_map]
  have hpbk : ∀ k (hk : k < p), pb[k]'hk = ⟨(cs[k]'hk).2.2.1, (cs[k]'hk).2.2.2.2.2.2⟩ := fun k hk => by
    rw [← hpb, Vector.getElem_map]
  have hTk : ∀ k (hk : k < p), T[k]'hk = ⟨1, (cs[k]'hk).1, 2, tagBits (cs[k]'hk).2.2.2.1⟩ := fun k hk => by
    rw [← hT, Vector.getElem_map]
  have hGLk : ∀ k (hk : k < p), GL[k]'hk = (ca[k]'hk).gather (longsOf (place (cs[k]'hk).2
      (((cs[k]'hk).2.1.toNat : Int) - 1) 0 0 (cs[k]'hk).2.1.toNat)) := fun k hk => by
    rw [← hGL, Vector.getElem_zipWith]
  have hGRk : ∀ k (hk : k < p), GR[k]'hk = (cb[k]'hk).gather (longsOf (place (cs[k]'hk).2
      (((cs[k]'hk).2.2.1.toNat : Int) - 1) 0 (cs[k]'hk).2.2.1.toNat (-((cs[k]'hk).2.2.1.toNat : Int)))) :=
    fun k hk => by rw [← hGR, Vector.getElem_zipWith]
  have hnk : ∀ k (hk : k < p), (cs[k]'hk).1 = (cs₀[k]'hk).1 := fun k hk => by rw [hcsk k hk]
  have hside : ∀ k (hk : k < p) q, q < (cs[k]'hk).1.toNat →
      (Column.bitAt (tagBits (cs[k]'hk).2.2.2.1) q = true → 0 < (cs[k]'hk).2.2.1.toNat) ∧
      (Column.bitAt (tagBits (cs[k]'hk).2.2.2.1) q = false → 0 < (cs[k]'hk).2.1.toNat) := fun k hk q hq => by
    have h := KernelWF.held_side (cs₀[k]'hk).2 ⟨q, by rw [hnk k hk] at hq; exact hq⟩
    rw [Arr.get_bool_bits _ (enc_tagBits _)] at h
    rw [hcsk k hk]; exact h
  have hP := fun k (hk : k < p) => sum_part_codes (cs[k]'hk).2 (ca[k]'hk) (cb[k]'hk)
    (by have := hLa hk; rw [hpak k hk] at this; exact this) (by have := hLb hk; rw [hpbk k hk] at this; exact this)
    (by rw [(hwa hk).2.1, hpak k hk]) (by rw [(hwb hk).2.1, hpbk k hk])
    (hwa hk).1 (hwb hk).1 (hwa hk).2.2.1 (hwb hk).2.2.1
    (fun q hq => (hside k hk q hq).1) (fun q hq => (hside k hk q hq).2)
  have hlT : ∀ {k l : Nat} (hk : k < p) (hl : l < p), (T[k]'hk).w = (T[l]'hl).w := fun {k l} hk hl => by
    rw [hTk k hk, hTk l hl]
  have hwT : ∀ {k : Nat} (hk : k < p), laneOK((T[k]'hk).w) ∧
      (T[k]'hk).b.size = ((T[k]'hk).n.toNat * (T[k]'hk).w + 7) / 8 ∧
      ((T[k]'hk).w < 8 → ∀ i < (T[k]'hk).n.toNat, Column.idAt (T[k]'hk).b (T[k]'hk).w i < max (T[k]'hk).card 1) :=
    fun {k} hk => by
      rw [hTk k hk]
      refine ⟨Or.inl rfl, ?_, fun _ i _ => ?_⟩
      · have hw := (cs[k]'hk).2.2.2.1.wf
        rw [enc_tagBits] at hw
        simpa [Enc.WF] using hw
      · show Column.idAt _ 1 i < max 2 1
        rw [idAt_one]; split <;> decide
  have hlGL : ∀ {k l : Nat} (hk : k < p) (hl : l < p), (GL[k]'hk).w = (GL[l]'hl).w := fun {k l} hk hl => by
    rw [hGLk k hk, hGLk l hl, (hP k hk).1.1, (hP l hl).1.1]; exact hla hk hl
  have hlGR : ∀ {k l : Nat} (hk : k < p) (hl : l < p), (GR[k]'hk).w = (GR[l]'hl).w := fun {k l} hk hl => by
    rw [hGRk k hk, hGRk l hl, (hP k hk).2.1.1, (hP l hl).2.1.1]; exact hlb hk hl
  have hwGL : ∀ {k : Nat} (hk : k < p), laneOK((GL[k]'hk).w) ∧
      (GL[k]'hk).b.size = ((GL[k]'hk).n.toNat * (GL[k]'hk).w + 7) / 8 ∧
      ((GL[k]'hk).w < 8 → ∀ i < (GL[k]'hk).n.toNat,
        Column.idAt (GL[k]'hk).b (GL[k]'hk).w i < max (GL[k]'hk).card 1) := fun {k} hk => by
    rw [hGLk k hk]
    obtain ⟨⟨gw, gn, gc, gs⟩, -, gv⟩ := hP k hk
    rw [gw, gn, gs, gc]
    refine ⟨(hwa hk).1, rfl, fun h8 i hi => ?_⟩
    rw [(gv i hi).1]
    split
    · exact Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_right _ _)
    · next hb =>
      have := (hside k hk i hi).2 (by simpa using hb)
      exact Nat.lt_of_lt_of_le (((hwa hk).2.2.2 h8).2 _ (by rw [(hwa hk).2.1, hpak k hk]; dsimp only; omega))
        (Nat.le_max_left _ _)
  have hwGR : ∀ {k : Nat} (hk : k < p), laneOK((GR[k]'hk).w) ∧
      (GR[k]'hk).b.size = ((GR[k]'hk).n.toNat * (GR[k]'hk).w + 7) / 8 ∧
      ((GR[k]'hk).w < 8 → ∀ i < (GR[k]'hk).n.toNat,
        Column.idAt (GR[k]'hk).b (GR[k]'hk).w i < max (GR[k]'hk).card 1) := fun {k} hk => by
    rw [hGRk k hk]
    obtain ⟨-, ⟨gw, gn, gc, gs⟩, gv⟩ := hP k hk
    rw [gw, gn, gs, gc]
    refine ⟨(hwb hk).1, rfl, fun h8 i hi => ?_⟩
    rw [(gv i hi).2]
    split
    · next hb =>
      have := (hside k hk i hi).1 hb
      exact Nat.lt_of_lt_of_le (((hwb hk).2.2.2 h8).2 _ (by rw [(hwb hk).2.1, hpbk k hk]; dsimp only; omega))
        (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_right _ _)
  have hTn : ∀ k (hk : k < p), (T[k]'hk).n.toNat = (cs₀[k]'hk).1.toNat := fun k hk => by
    rw [hTk k hk]; exact congrArg USize.toNat (hnk k hk)
  have hGLn : ∀ k (hk : k < p), (GL[k]'hk).n.toNat = (cs₀[k]'hk).1.toNat := fun k hk => by
    rw [hGLk k hk, (hP k hk).1.2.1]; exact congrArg USize.toNat (hnk k hk)
  have hGRn : ∀ k (hk : k < p), (GR[k]'hk).n.toNat = (cs₀[k]'hk).1.toNat := fun k hk => by
    rw [hGRk k hk, (hP k hk).2.1.2.1]; exact congrArg USize.toNat (hnk k hk)
  have hLT : T.toList.map (·.n.toNat) = cs₀.toList.map (·.1.toNat) :=
    List.ext_getElem (by simp) fun k h1 _ => by
      simp only [List.getElem_map, Vector.getElem_toList]; exact hTn k (by simpa using h1)
  have hLGL : GL.toList.map (·.n.toNat) = cs₀.toList.map (·.1.toNat) :=
    List.ext_getElem (by simp) fun k h1 _ => by
      simp only [List.getElem_map, Vector.getElem_toList]; exact hGLn k (by simpa using h1)
  have hLGR : GR.toList.map (·.n.toNat) = cs₀.toList.map (·.1.toNat) :=
    List.ext_getElem (by simp) fun k h1 _ => by
      simp only [List.getElem_map, Vector.getElem_toList]; exact hGRn k (by simpa using h1)
  have hLn : (T.map (·.n)).toList.map (·.toNat) = cs₀.toList.map (·.1.toNat) := by
    rw [Vector.toList_map, List.map_map]; exact hLT
  have hO : ∀ (L : List Code) k, L.map (·.n.toNat) = cs₀.toList.map (·.1.toNat) →
      ((L.take k).map (·.n.toNat)).sum = ((cs₀.toList.take k).map (·.1.toNat)).sum := fun L k h => by
    rw [List.map_take, h, ← List.map_take]
  have hOn : ∀ k, (((T.map (·.n)).toList.take k).map (·.toNat)).sum =
      ((cs₀.toList.take k).map (·.1.toNat)).sum := fun k => by rw [List.map_take, hLn, ← List.map_take]
  have hlt : ∀ k (hk : k < p), ∀ i < (cs₀[k]'hk).1.toNat, ((cs₀.toList.take k).map (·.1.toNat)).sum + i <
      (cs₀.toList.map (·.1.toNat)).sum := fun k hk i hi => by
    have := take_sum_le (cs₀.toList.map (·.1.toNat)) (k := k) (by simpa using hk)
    simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take] at this; omega
  -- every claim names a part, so with none there is nothing to show
  -- (no `subst` of `p`: rewriting `0` through every hypothesis times out)
  rcases Nat.eq_zero_or_pos p with h0 | hp
  · exact ⟨⟨fun {_ _} hk => absurd hk (by omega), fun {_} hk => absurd hk (by omega)⟩,
      fun {_ _} hk => absurd hk (by omega)⟩
  have catT := cat_parts T hp hlT hwT (by rw [hLT]; exact hN)
  have catL := cat_parts GL hp hlGL hwGL (by rw [hLGL]; exact hN)
  have catR := cat_parts GR hp hlGR hwGR (by rw [hLGR]; exact hN)
  have hn1 : (Code.cat GL.toArray).n = (Code.cat T.toArray).n :=
    USize.toNat_inj.1 (by rw [catL.2.1, catT.2.1, hLGL, hLT])
  have hP1 := pairCode_spec false (Code.cat T.toArray) (Code.cat GL.toArray) hn1
    ⟨catT.1.1, catT.1.2.1, fun h i hi => by have := catT.1.2.2 h i hi; omega⟩
    ⟨catL.1.1, catL.1.2.1, fun h i hi => by have := catL.1.2.2 h i hi; omega⟩
  dsimp only at hP1
  obtain ⟨⟨h1w, h1n, h1s, h1id⟩, h1iff⟩ := hP1
  have hn2 : (Code.cat GR.toArray).n = (pairCode false (Code.cat T.toArray) (Code.cat GL.toArray)).1.n :=
    USize.toNat_inj.1 (by rw [catR.2.1, h1n, catT.2.1, hLGR, hLT])
  have hP2 := pairCode_spec false _ (Code.cat GR.toArray) hn2
    ⟨h1w, h1s, fun h i hi => Nat.lt_of_lt_of_le ((h1id h).2 i hi) (Nat.le_max_left _ _)⟩
    ⟨catR.1.1, catR.1.2.1, fun h i hi => by have := catR.1.2.2 h i hi; omega⟩
  dsimp only at hP2
  obtain ⟨⟨h2w, h2n, h2s, h2id⟩, h2iff⟩ := hP2
  have hs : ((T.map (·.n)).toList.map (·.toNat)).sum = (pairCode false (pairCode false (Code.cat T.toArray)
      (Code.cat GL.toArray)).1 (Code.cat GR.toArray)).1.n.toNat := by
    rw [hLn, h2n, h1n, catT.2.1, hLT]
  refine ⟨⟨fun {k l} hk hl i j hi hj => ?_, fun {k} hk => ?_⟩, fun {k l} hk hl => ?_⟩
  · obtain ⟨hwk, -, -, hck⟩ := cut_get _ (T.map (·.n)) h2w hs hk
    obtain ⟨hwl, -, -, hcl⟩ := cut_get _ (T.map (·.n)) h2w hs hl
    have hik : i < ((T.map (·.n : Code → USize))[k]'hk).toNat := by rw [Vector.getElem_map, hTn k hk]; exact hi
    have hjl : j < ((T.map (·.n : Code → USize))[l]'hl).toNat := by rw [Vector.getElem_map, hTn l hl]; exact hj
    have hoi := hlt k hk i hi
    have hoj := hlt l hl j hj
    rw [hwk, hwl, hck i hik, hcl j hjl, hOn, hOn,
      h2iff _ (by rw [h1n, catT.2.1, hLT]; exact hoi) _ (by rw [h1n, catT.2.1, hLT]; exact hoj),
      h1iff _ (by rw [catT.2.1, hLT]; exact hoi) _ (by rw [catT.2.1, hLT]; exact hoj),
      ← hO T.toList k hLT, ← hO T.toList l hLT,
      catT.2.2 k hk i (by rw [hTn k hk]; exact hi), catT.2.2 l hl j (by rw [hTn l hl]; exact hj),
      hO T.toList k hLT, hO T.toList l hLT, ← hO GL.toList k hLGL, ← hO GL.toList l hLGL,
      catL.2.2 k hk i (by rw [hGLn k hk]; exact hi), catL.2.2 l hl j (by rw [hGLn l hl]; exact hj),
      hO GL.toList k hLGL, hO GL.toList l hLGL, ← hO GR.toList k hLGR, ← hO GR.toList l hLGR,
      catR.2.2 k hk i (by rw [hGRn k hk]; exact hi), catR.2.2 l hl j (by rw [hGRn l hl]; exact hj)]
    have hik' : i < (cs[k]'hk).1.toNat := by rw [hnk k hk]; exact hi
    have hjl' : j < (cs[l]'hl).1.toNat := by rw [hnk l hl]; exact hj
    obtain ⟨⟨gwk, -, -, -⟩, ⟨rwk, -, -, -⟩, gvk⟩ := hP k hk
    obtain ⟨⟨gwl, -, -, -⟩, ⟨rwl, -, -, -⟩, gvl⟩ := hP l hl
    rw [hTk k hk, hTk l hl, hGLk k hk, hGLk l hl, hGRk k hk, hGRk l hl, gwk, gwl, rwk, rwl,
      (gvk i hik').1, (gvl j hjl').1, (gvk i hik').2, (gvl j hjl').2, idAt_one, idAt_one,
      (KernelWF.held_row _ (hfit hk) ⟨i, hi⟩).symm.trans (row_part_congr (hcsk k hk).symm hi hik'),
      (KernelWF.held_row _ (hfit hl) ⟨j, hj⟩).symm.trans (row_part_congr (hcsk l hl).symm hj hjl')]
    have sk := hside k hk i hik'
    have sl := hside l hl j hjl'
    apply sum_iff
    · exact fun h => ⟨_, row_sum_inl _ hik' h (sk.2 h)⟩
    · exact fun h => ⟨_, row_sum_inr _ hik' h (sk.1 h)⟩
    · exact fun h => ⟨_, row_sum_inl _ hjl' h (sl.2 h)⟩
    · exact fun h => ⟨_, row_sum_inr _ hjl' h (sl.1 h)⟩
    · intro h1 h2
      have := sk.2 h1
      have := sl.2 h2
      have hiA : min (max ((cs[k]'hk).2.2.2.2.1.get ⟨i, hik'⟩).toInt 0).toNat ((cs[k]'hk).2.1.toNat - 1) <
          (pa[k]'hk).1.toNat := by rw [hpak k hk]; dsimp only; omega
      have hjA : min (max ((cs[l]'hl).2.2.2.2.1.get ⟨j, hjl'⟩).toInt 0).toNat ((cs[l]'hl).2.1.toNat - 1) <
          (pa[l]'hl).1.toNat := by rw [hpak l hl]; dsimp only; omega
      rw [row_sum_inl _ hik' h1 (sk.2 h1), row_sum_inl _ hjl' h2 (sl.2 h2), Sum.inl.injEq, hfa hk hl hiA hjA,
        row_part_congr (hpak k hk) hiA _, row_part_congr (hpak l hl) hjA _]
    · intro h1 h2
      have := sk.1 h1
      have := sl.1 h2
      have hiB : min (max ((cs[k]'hk).2.2.2.2.1.get ⟨i, hik'⟩).toInt 0).toNat ((cs[k]'hk).2.2.1.toNat - 1) <
          (pb[k]'hk).1.toNat := by rw [hpbk k hk]; dsimp only; omega
      have hjB : min (max ((cs[l]'hl).2.2.2.2.1.get ⟨j, hjl'⟩).toInt 0).toNat ((cs[l]'hl).2.2.1.toNat - 1) <
          (pb[l]'hl).1.toNat := by rw [hpbk l hl]; dsimp only; omega
      rw [row_sum_inr _ hik' h1 (sk.1 h1), row_sum_inr _ hjl' h2 (sl.1 h2), Sum.inr.injEq, hfb hk hl hiB hjB,
        row_part_congr (hpbk k hk) hiB _, row_part_congr (hpbk l hl) hjB _]
  · obtain ⟨hwk, hnk', hck, hik⟩ := cut_get _ (T.map (·.n)) h2w hs hk
    have hzk := cut_size _ (T.map (·.n)) h2w hs h2s hk
    dsimp only
    rw [hzk, hwk, hnk', hck]
    refine ⟨h2w, by rw [Vector.getElem_map, hTk k hk]; exact hnk k hk, rfl, fun h8 => ⟨(h2id h8).1, fun i hi => ?_⟩⟩
    rw [hik i hi]
    refine (h2id h8).2 _ ?_
    rw [← hs, hLn, hOn]
    exact hlt k hk i (by rw [Vector.getElem_map, hTn k hk] at hi; exact hi)
  · rw [(cut_get _ (T.map (·.n)) h2w hs hk).1, (cut_get _ (T.map (·.n)) h2w hs hl).1]

#print axioms codes_sum_faithful_wf

/-! ## Arrays: `rankSlices` numbers each slice by its index among the distinct slices before it -/

/-- **One step of the fold `rankSlices` runs** keeps its reading: the ids hold `m` longs, the slices kept are
    distinct, and id `t` is the index of slice `t` among them, at most `t`; `m < 2⁶⁴` keeps an index its long. -/
theorem rankFold_step (S : Nat → Array UInt64)
    {f : ByteArray × Array (Array UInt64) → Nat → ByteArray × Array (Array UInt64)}
    (hf : ∀ ids seen j, f (ids, seen) j = match seen.findIdx? (· == S j) with
      | some k => (Column.pushBits ids (UInt64.ofNat k) 8, seen)
      | none => (Column.pushBits ids (UInt64.ofNat seen.size) 8, seen.push (S j)))
    (st : ByteArray × Array (Array UInt64)) (m : Nat) (hm : m + 1 ≤ 2 ^ 64)
    (hs : st.1.size = 8 * m) (hnd : st.2.toList.Nodup) (hsz : st.2.size ≤ m)
    (hid : ∀ t (ht : t < m), ∃ h : (Column.bitsAt st.1 (8 * t) 8).toNat < st.2.size,
      st.2[(Column.bitsAt st.1 (8 * t) 8).toNat] = S t ∧ (Column.bitsAt st.1 (8 * t) 8).toNat ≤ t) :
    (f st m).1.size = 8 * (m + 1) ∧ (f st m).2.toList.Nodup ∧ (f st m).2.size ≤ m + 1 ∧
      ∀ t (ht : t < m + 1), ∃ h : (Column.bitsAt (f st m).1 (8 * t) 8).toNat < (f st m).2.size,
        (f st m).2[(Column.bitsAt (f st m).1 (8 * t) 8).toNat] = S t ∧
        (Column.bitsAt (f st m).1 (8 * t) 8).toNat ≤ t := by
    obtain ⟨ids, seen⟩ := st
    dsimp only at hs hnd hsz hid
    -- an earlier id is not moved by the push
    have keep : ∀ v t, t < m → Column.bitsAt (Column.pushBits ids v 8) (8 * t) 8 = Column.bitsAt ids (8 * t) 8 :=
      fun v t ht => Column.bitsAt_congr _ _ _ _ fun k hk => Column.pushBits_getElem?_lt _ _ _ _ (by omega)
    have last : ∀ v, Column.bitsAt (Column.pushBits ids v 8) (8 * m) 8 = v := fun v => by
      rw [show 8 * m = ids.size by omega]; exact bitsAt_pushBits8 ids v
    rw [hf]
    split
    · next k hk =>
      obtain ⟨hkl, hb, -⟩ := Array.findIdx?_eq_some_iff_getElem.1 hk
      have hkS : seen[k] = S m := beq_iff_eq.1 hb
      dsimp only
      refine ⟨by rw [Column.pushBits_size, hs]; omega, hnd, by omega, fun t ht => ?_⟩
      by_cases htm : t < m
      · rw [keep _ t htm]
        obtain ⟨h1, e1, l1⟩ := hid t htm
        exact ⟨h1, e1, by omega⟩
      · obtain rfl : t = m := by omega
        rw [last, UInt64.toNat_ofNat_of_lt' (by first | omega | (simp only [UInt64.size]; omega))]
        exact ⟨hkl, hkS, by omega⟩
    · next hk =>
      have hn := Array.findIdx?_eq_none_iff.1 hk
      have hnot : S m ∉ seen := fun h => by have := hn _ h; simp at this
      dsimp only
      refine ⟨by rw [Column.pushBits_size, hs]; omega, ?_, by simp; omega, fun t ht => ?_⟩
      · rw [Array.toList_push, List.nodup_append]
        refine ⟨hnd, by simp, fun a ha b hb => ?_⟩
        rw [List.mem_singleton] at hb
        subst hb
        exact fun e => hnot (e ▸ Array.mem_def.2 ha)
      by_cases htm : t < m
      · rw [keep _ t htm]
        obtain ⟨h1, e1, l1⟩ := hid t htm
        exact ⟨by simp; omega, by simpa [Array.getElem_push, h1] using e1, l1⟩
      · obtain rfl : t = m := by omega
        rw [last, UInt64.toNat_ofNat_of_lt' (by first | omega | (simp only [UInt64.size]; omega))]
        exact ⟨by simp, by simp, by omega⟩

/-- **The fold `rankSlices` runs, read back** after `m` steps, `rankFold_step` by induction. -/
theorem rankFold_spec (S : Nat → Array UInt64)
    {f : ByteArray × Array (Array UInt64) → Nat → ByteArray × Array (Array UInt64)}
    (hf : ∀ ids seen j, f (ids, seen) j = match seen.findIdx? (· == S j) with
      | some k => (Column.pushBits ids (UInt64.ofNat k) 8, seen)
      | none => (Column.pushBits ids (UInt64.ofNat seen.size) 8, seen.push (S j))) :
    ∀ m, m ≤ 2 ^ 64 →
      ((List.range m).foldl f (ByteArray.empty, #[])).1.size = 8 * m ∧
      ((List.range m).foldl f (ByteArray.empty, #[])).2.toList.Nodup ∧
      ((List.range m).foldl f (ByteArray.empty, #[])).2.size ≤ m ∧
      ∀ t (ht : t < m), ∃ h : (Column.bitsAt ((List.range m).foldl f (ByteArray.empty, #[])).1 (8 * t) 8).toNat <
          ((List.range m).foldl f (ByteArray.empty, #[])).2.size,
        ((List.range m).foldl f (ByteArray.empty, #[])).2[(Column.bitsAt
          ((List.range m).foldl f (ByteArray.empty, #[])).1 (8 * t) 8).toNat] = S t ∧
        (Column.bitsAt ((List.range m).foldl f (ByteArray.empty, #[])).1 (8 * t) 8).toNat ≤ t
  | 0, _ => ⟨rfl, List.nodup_nil, Nat.le_refl _, fun _ ht => absurd ht (Nat.not_lt_zero _)⟩
  | m + 1, hm => by
    obtain ⟨hs, hnd, hsz, hid⟩ := rankFold_spec S hf m (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact rankFold_step S hf _ m hm hs hnd hsz hid

/-- **Two slices get one id exactly when they are equal**, and slice `t`'s id is at most `t`: the fold
    `rankSlices` runs, `rankFold_spec` read through the distinctness of the slices kept. -/
theorem rankFold_get (S : Nat → Array UInt64)
    {f : ByteArray × Array (Array UInt64) → Nat → ByteArray × Array (Array UInt64)}
    (hf : ∀ ids seen j, f (ids, seen) j = match seen.findIdx? (· == S j) with
      | some k => (Column.pushBits ids (UInt64.ofNat k) 8, seen)
      | none => (Column.pushBits ids (UInt64.ofNat seen.size) 8, seen.push (S j)))
    {m : Nat} (hm : m ≤ 2 ^ 64) {t t' : Nat} (ht : t < m) (ht' : t' < m) :
    (Column.bitsAt ((List.range m).foldl f (ByteArray.empty, #[])).1 (8 * t) 8 =
        Column.bitsAt ((List.range m).foldl f (ByteArray.empty, #[])).1 (8 * t') 8 ↔ S t = S t') ∧
      (Column.bitsAt ((List.range m).foldl f (ByteArray.empty, #[])).1 (8 * t) 8).toNat ≤ t := by
  obtain ⟨-, hnd, -, hid⟩ := rankFold_spec S hf m hm
  generalize (List.range m).foldl f (ByteArray.empty, #[]) = st at hnd hid ⊢
  obtain ⟨h1, e1, l1⟩ := hid t ht
  obtain ⟨h2, e2, -⟩ := hid t' ht'
  refine ⟨⟨fun e => ?_, fun e => ?_⟩, l1⟩
  · have hab : (Column.bitsAt st.1 (8 * t) 8).toNat = (Column.bitsAt st.1 (8 * t') 8).toNat := by rw [e]
    rw [← e1, ← e2]; simp only [hab]
  · have he : st.2.toList[(Column.bitsAt st.1 (8 * t) 8).toNat]'(by simpa using h1) =
        st.2.toList[(Column.bitsAt st.1 (8 * t') 8).toNat]'(by simpa using h2) := by
      simp only [Array.getElem_toList]; rw [e1, e2, e]
    refine UInt64.toNat_inj.1 ?_
    rcases Nat.lt_trichotomy (Column.bitsAt st.1 (8 * t) 8).toNat (Column.bitsAt st.1 (8 * t') 8).toNat with
      h | h | h
    · exact absurd he (List.pairwise_iff_getElem.1 hnd _ _ _ _ h)
    · exact h
    · exact absurd he.symm (List.pairwise_iff_getElem.1 hnd _ _ _ _ h)

#print axioms rankFold_get

/-- **`rankSlices`' content**: where it does not decline (`rankSlices_size`'s guards), slices `j`, `j'` of `o`
    get one id exactly when they are equal as sequences, and slice `j`'s id is at most `j`. -/
theorem rankSlices_get (w : USize) (v o : ByteArray) (hw : w.toNat ≤ 64) (ho : 8 ≤ o.size)
    (h0 : 0 ≤ (Column.bitsAt o 0 8).toInt64.toInt)
    (hcap : (Column.bitsAt o (8 * (o.size / 8 - 1)) 8).toInt64.toInt ≤
      (Column.idsCap v w.toNat (Column.bitsAt o (8 * (o.size / 8 - 1)) 8).toInt64.toInt.toNat : Int))
    (hasc : ∀ j, j < o.size / 8 - 1 →
      (Column.bitsAt o (8 * j) 8).toInt64.toInt ≤ (Column.bitsAt o (8 * (j + 1)) 8).toInt64.toInt)
    (hg : o.size / 8 - 1 ≤ 2 ^ 64) {j j' : Nat} (hj : j < o.size / 8 - 1) (hj' : j' < o.size / 8 - 1) :
    (Column.bitsAt (Order.rankSlices w v o) (8 * j) 8 = Column.bitsAt (Order.rankSlices w v o) (8 * j') 8 ↔
      (Array.range ((Column.bitsAt o (8 * (j + 1)) 8).toInt64.toInt.toNat -
          (Column.bitsAt o (8 * j) 8).toInt64.toInt.toNat)).map (fun t =>
        Column.resAt v 0 w.toNat ((Column.bitsAt o (8 * j) 8).toInt64.toInt.toNat + t)) =
      (Array.range ((Column.bitsAt o (8 * (j' + 1)) 8).toInt64.toInt.toNat -
          (Column.bitsAt o (8 * j') 8).toInt64.toInt.toNat)).map (fun t =>
        Column.resAt v 0 w.toNat ((Column.bitsAt o (8 * j') 8).toInt64.toInt.toNat + t))) ∧
      (Column.bitsAt (Order.rankSlices w v o) (8 * j) 8).toNat ≤ j := by
  simp only [Order.rankSlices]
  rw [if_neg]
  · rw [← Array.foldl_toList, Array.toList_range]
    refine rankFold_get (fun j => (Array.range ((Column.bitsAt o (8 * (j + 1)) 8).toInt64.toInt.toNat -
        (Column.bitsAt o (8 * j) 8).toInt64.toInt.toNat)).map (fun t =>
      Column.resAt v 0 w.toNat ((Column.bitsAt o (8 * j) 8).toInt64.toInt.toNat + t))) ?_ hg hj hj'
    intro _ _ _; rfl
  · simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range, not_or,
      not_exists, not_and, Nat.mul_zero]
    exact ⟨⟨⟨⟨Nat.not_lt.2 hw, Nat.not_lt.2 ho⟩, Int.not_lt.2 h0⟩, Int.not_lt.2 hcap⟩, fun j hj => Int.not_lt.2 (hasc j hj)⟩

#print axioms rankSlices_get

end LeetQ.Rel.Alg
