/-
  `inits`, `tails` and `uncat` read back. `inits` and `tails` are the private `nest` at two slice kernels:
  `nest_rep` reads `nest`'s body back at any slice kernel whose starts and ends are known per copy.
-/
import LeetQ.Rel.RepPrim
import LeetQ.Rel.RepMem
import LeetQ.Rel.KernelWF.NestSpec

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF

-- `X`'s row `r`: its start and count; the counts plus one `c` before row `r`; copy `d`'s row and rank
set_option hygiene false in
local notation "st(" r ")" => (Column.bitsAt (slicesOf X).1 (r * 8) 8).toNat
set_option hygiene false in
local notation "cn(" r ")" => (Column.bitsAt (slicesOf X).2 (r * 8) 8).toNat
set_option hygiene false in
local notation "pc(" r ")" => ((List.range r).map fun u => (Column.bitsAt c (u * 8) 8).toNat).sum
set_option hygiene false in
local notation "pn(" r ")" => ((List.range r).map fun u => (Column.bitsAt (slicesOf X).2 (u * 8) 8).toNat).sum
set_option hygiene false in
local notation "ix(" d ")" => (Column.bitsAt xi (d * 8) 8).toNat
set_option hygiene false in
local notation "rk(" d ")" => (Column.bitsAt xr (d * 8) 8).toNat

/-- **`nest`'s body, read back**: an array `xs` of `X` (row `r`) goes to the `cn(r) + 1` slices of `X`'s payload
    `[L r t, H r t)`, `t = 0 … cn(r)`, where the slice kernel `f` puts copy `d`'s start and end at
    `L ix(d) rk(d)` and `H ix(d) rk(d)` (`hL`, `hH`). The counts plus one `c`, `expand`'s index and rank columns
    `xi`, `xr` (at `m` copies) are bound by their equations. Hypotheses: the payload count below `2^63`; the counts
    plus one summed below `2^63` and a `USize`; `Vals.PickFits` where `X` and the slices are picked. -/
theorem nest_rep {B : Obj} {n : USize} (X : Vals (.arr B) n) (hp : X.1.toNat < 2 ^ 63)
    (f : (m : USize) → ByteArray × ByteArray → (i r : ByteArray) → len i = m.toNat → Arr .long m × Arr .long m)
    (c : ByteArray) (hc : c = addc n (slicesOf X).2 1)
    (hS : pn(n.toNat) + n.toNat < 2 ^ 63) (hU : pn(n.toNat) + n.toNat < USize.size)
    (xi : ByteArray) (hxi : xi = expandBytes 8 0 (tilLongs n) c)
    (m : USize) (hm : m = (len xi).toUSize)
    (xr : ByteArray) (hxr : xr = sub m (tilLongs m) (gather 8 (sub n (sums n c) c) xi))
    (L H : Nat → Nat → Nat)
    (hLH : ∀ r t, r < n.toNat → t ≤ cn(r) → L r t ≤ H r t ∧ H r t ≤ X.1.toNat)
    (hL : ∀ h d (hd : d < m.toNat), ix(d) < n.toNat → rk(d) ≤ cn(ix(d)) →
      ((f m (slicesOf X) xi xr h).1.get ⟨d, hd⟩).toInt = ((L (ix(d)) (rk(d)) : Nat) : Int))
    (hH : ∀ h d (hd : d < m.toNat), ix(d) < n.toNat → rk(d) ≤ cn(ix(d)) →
      ((f m (slicesOf X) xi xr h).2.get ⟨d, hd⟩).toInt = ((H (ix(d)) (rk(d)) : Nat) : Int))
    (hK : Vals.PickFits (.arr B) X
      ((List.range n.toNat).map fun q => (Column.bitsAt (tilLongs n) (q * 8) 8).toNat))
    (hV : ∀ h, Vals.PickFits (.arr B)
      (⟨X.1, (f m (slicesOf X) xi xr h).1, (f m (slicesOf X) xi xr h).2, X.2.2.2⟩ : Vals (.arr B) m)
      ((List.range m.toNat).map fun q => (Column.bitsAt (tilLongs m) (q * 8) 8).toNat))
    (R : Rel (.arr B) (.arr (.arr B)))
    (hR : R = expand n (addc n (slicesOf X).2 1) (fun _ => default) fun m i r hi' _ =>
      ⟨n, Vals.compact (.arr B) X,
        ⟨m, valCol Ew.sub Ew.vv (sums n (addc n (slicesOf X).2 1)) (addc n (slicesOf X).2 1),
          longsN n (sums n (addc n (slicesOf X).2 1)) (sums_le (len_val ..)),
          Vals.compact (.arr B) ⟨X.1, (f m (slicesOf X) i r hi').1, (f m (slicesOf X) i r hi').2, X.2.2.2⟩⟩⟩) :
    ∀ xs yss, rep R xs yss ↔ ∃ r, ∃ hr : r < n.toNat, Vals.row X ⟨r, hr⟩ = xs ∧
      yss = (List.range (cn(r) + 1)).map fun t => (List.range (H r t - L r t)).map fun j =>
        if h : L r t + j < X.1.toNat then Vals.row X.2.2.2 ⟨_, h⟩ else B.dflt := by
  intro xs yss
  subst hm
  have hcl : len c = n.toNat := by rw [hc, addc, len_val]
  have hRw := fun r (hr : r < n.toNat) => slicesOf_row X hp hr
  have hpre_le : ∀ a b, a ≤ b → pc(a) ≤ pc(b) := fun a b h => sum_range_le _ h
  have hpre_succ : ∀ r, pc(r + 1) = pc(r) + (Column.bitsAt c (r * 8) 8).toNat := fun r => sum_range_succ' _ r
  have hpn_le : ∀ a b, a ≤ b → pn(a) ≤ pn(b) := fun a b h => sum_range_le _ h
  have hpn_succ : ∀ r, pn(r + 1) = pn(r) + cn(r) := fun r => sum_range_succ' _ r
  have hcg : ∀ r, r < n.toNat → (Column.bitsAt c (r * 8) 8).toNat = cn(r) + 1 := fun r hr => by
    have := hpn_le (r + 1) n.toNat (by omega); rw [hpn_succ] at this
    rw [hc, addc, val_va_get _ _ _ _ hr, bitsAt_one, addOne_toNat (by omega)]
  have hcsum : ∀ r, r ≤ n.toNat → pc(r) = pn(r) + r := by
    intro r
    induction r with
    | zero => intro _; simp
    | succ r ih => intro hr; rw [hpre_succ, hpn_succ, ih (by omega), hcg r (by omega)]; omega
  have hS' : pc(n.toNat) < 2 ^ 63 := by rw [hcsum _ (Nat.le_refl _)]; exact hS
  obtain ⟨hxl, hin, -⟩ := expand_at c hcl hS' (by rw [hcsum _ (Nat.le_refl _)]; exact hU) xi hxi xr hxr
  have hxU : len xi < USize.size := by rw [hxl, hcsum _ (Nat.le_refl _)]; exact hU
  have hmN : ((len xi).toUSize).toNat = len xi := USize.toNat_ofNat_of_lt' hxU
  have hhig : ∀ r, r < n.toNat → (Column.bitsAt (sums n c) (r * 8) 8).toNat = pc(r + 1) := fun r hr => by
    have hb := hpre_le (r + 1) _ hr
    rw [sums_get (b := c) hr (by rw [hcl]; exact hr) (by omega)]
  have hlog : ∀ r, r < n.toNat → (Column.bitsAt (sub n (sums n c) c) (r * 8) 8).toNat = pc(r) := fun r hr => by
    have := hhig r hr; have := hpre_succ r; have := hpre_le (r + 1) _ hr
    rw [sub_get (a := sums n c) (b := c) hr (by omega) (by omega)]; omega
  -- the key: `Vals.compact` reads back every row
  have hkey : ∀ q : Fin n.toNat, (Vals.compact (.arr B) X).row q = X.row q := fun q => by
    rw [show Vals.compact (.arr B) X = Vals.pick (.arr B) X (tilLongs _) _ (len_tilLongs _) from rfl,
      pick_row (.arr B) X (tilLongs n) n (len_tilLongs _) hK,
      dif_pos (show (Column.bitsAt (tilLongs n) (q.1 * 8) 8).toNat < n.toNat by rw [tilLongs_get q.2]; exact q.2)]
    exact congrArg (Vals.row X) (Fin.ext (tilLongs_get q.2))
  have hq : ∀ (V : Vals (.arr B) (len xi).toUSize) k (hk : k < ((len xi).toUSize).toNat) d
      (hd : d < ((len xi).toUSize).toNat), k = d → V.row ⟨k, hk⟩ = V.row ⟨d, hd⟩ :=
    fun V k hk d hd e => congrArg _ (Fin.ext e)
  -- row `r` of the result: copies `pc(r) … pc(r + 1) - 1`, copy `pc(r) + t` the slice `[L r t, H r t)`
  have hrow : ∀ (hh : n.toNat ≤ len (sums n c)) (h1 : len xi = ((len xi).toUSize).toNat) (r : Nat)
      (hr : r < n.toNat),
      Vals.row (A := .arr (.arr B)) (⟨(len xi).toUSize, valCol Ew.sub Ew.vv (sums n c) c, longsN n (sums n c) hh,
        Vals.compact (.arr B) ⟨X.1, (f (len xi).toUSize (slicesOf X) xi xr h1).1,
          (f (len xi).toUSize (slicesOf X) xi xr h1).2, X.2.2.2⟩⟩ : Vals (.arr (.arr B)) n) ⟨r, hr⟩ =
        (List.range (cn(r) + 1)).map fun t => (List.range (H r t - L r t)).map fun j =>
          if h : L r t + j < X.1.toNat then Vals.row X.2.2.2 ⟨_, h⟩ else B.dflt := by
    intro hh h1 r hr
    have e1 := hhig r hr; have e2 := hpre_succ r; have e3 := hpre_le (r + 1) _ hr; have e4 := hlog r hr
    have hcr := hcg r hr
    have hlo' : ((valCol (n := n) Ew.sub Ew.vv (sums n c) c).get ⟨r, hr⟩).toInt = ((pc(r) : Nat) : Int) := by
      rw [valCol_get]; dsimp only
      rw [show Kernel.Ew.val Ew.sub Ew.i64 Ew.vv nul (sums n c) c n = sub n (sums n c) c from rfl,
        toInt64_toInt (x := Column.bitsAt (sub n (sums n c) c) (r * 8) 8) (by omega), e4]
    have hhi' : ((longsN n (sums n c) hh).get ⟨r, hr⟩).toInt = ((pc(r + 1) : Nat) : Int) := by
      rw [longsN_get]; dsimp only
      rw [toInt64_toInt (x := Column.bitsAt (sums n c) (r * 8) 8) (by omega), e1]
    have hrw := arr_row (b := .arr B) (⟨(len xi).toUSize, valCol (n := n) Ew.sub Ew.vv (sums n c) c,
      longsN n (sums n c) hh, Vals.compact (.arr B) ⟨X.1, (f (len xi).toUSize (slicesOf X) xi xr h1).1,
        (f (len xi).toUSize (slicesOf X) xi xr h1).2, X.2.2.2⟩⟩ : Vals (.arr (.arr B)) n) ⟨r, hr⟩
    dsimp only at hrw
    rw [hlo', hhi'] at hrw
    have hmx : pc(r + 1) ≤ ((len xi).toUSize).toNat := by rw [hmN, hxl]; exact e3
    have f1 : min (max ((pc(r) : Nat) : Int) 0).toNat ((len xi).toUSize).toNat = pc(r) := by omega
    have f2 : min (max ((pc(r + 1) : Nat) : Int) 0).toNat ((len xi).toUSize).toNat = pc(r + 1) := by omega
    rw [f1, f2] at hrw
    rw [hrw]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range]; omega
    · intro t h1' h2'
      have ht : t < cn(r) + 1 := by simp only [List.length_map, List.length_range] at h2'; exact h2'
      have hb : pc(r) + t < ((len xi).toUSize).toNat := by omega
      obtain ⟨hx, hy⟩ := hin r t hr (by omega)
      rw [List.getElem_map, List.getElem_range, dif_pos hb, List.getElem_map, List.getElem_range]
      rw [show Vals.compact (.arr B) ⟨X.1, (f (len xi).toUSize (slicesOf X) xi xr h1).1,
          (f (len xi).toUSize (slicesOf X) xi xr h1).2, X.2.2.2⟩ =
          Vals.pick (.arr B) ⟨X.1, (f (len xi).toUSize (slicesOf X) xi xr h1).1,
            (f (len xi).toUSize (slicesOf X) xi xr h1).2, X.2.2.2⟩ (tilLongs _) _ (len_tilLongs _) from rfl,
        pick_row (.arr B) _ (tilLongs _) _ (len_tilLongs _) (hV h1),
        dif_pos (show (Column.bitsAt (tilLongs (len xi).toUSize) ((pc(r) + t) * 8) 8).toNat <
          ((len xi).toUSize).toNat by rw [tilLongs_get hb]; exact hb),
        hq _ _ _ _ hb (tilLongs_get hb), arr_row]
      dsimp only
      have hLt := hL h1 (pc(r) + t) hb (by rw [hx]; exact hr) (by rw [hx, hy]; omega)
      have hHt := hH h1 (pc(r) + t) hb (by rw [hx]; exact hr) (by rw [hx, hy]; omega)
      rw [hx, hy] at hLt hHt
      rw [hLt, hHt]
      obtain ⟨hlh, hhx⟩ := hLH r t hr (by omega)
      have g1 : min (max ((L r t : Nat) : Int) 0).toNat X.1.toNat = L r t := by omega
      have g2 : min (max ((H r t : Nat) : Int) 0).toNat X.1.toNat = H r t := by omega
      simp only [g1, g2]
  -- `nest`'s body unfolded at its pieces
  subst hxr hxi hc
  subst hR
  unfold expand need
  dsimp only
  rw [dif_pos hxU]
  try dsimp only
  show (∃ q, _ ∧ _) ↔ _
  constructor
  · rintro ⟨⟨r, hr⟩, hk, hv⟩
    exact ⟨r, hr, (hkey _).symm.trans hk, by rw [← hv]; exact hrow _ _ r hr⟩
  · rintro ⟨r, hr, hx, rfl⟩
    exact ⟨⟨r, hr⟩, (hkey _).trans hx, hrow _ _ r hr⟩

/-- **`inits`, read back**: an array `xs` of `X` goes to its prefixes by increasing length, `[]` first. The counts
    plus one `c`, `expand`'s index and rank columns `xi`, `xr` (at `m` copies) are bound by their equations.
    Hypotheses: the payload count below `2^63`; the counts plus one summed below `2^63` and a `USize`;
    `Vals.PickFits` where `X` and the prefixes are picked. -/
theorem rep_inits {B : Obj} {n : USize} (X : Vals (.arr B) n) (hp : X.1.toNat < 2 ^ 63)
    (c : ByteArray) (hc : c = addc n (slicesOf X).2 1)
    (hS : pn(n.toNat) + n.toNat < 2 ^ 63) (hU : pn(n.toNat) + n.toNat < USize.size)
    (xi : ByteArray) (hxi : xi = expandBytes 8 0 (tilLongs n) c)
    (m : USize) (hm : m = (len xi).toUSize)
    (xr : ByteArray) (hxr : xr = sub m (tilLongs m) (gather 8 (sub n (sums n c) c) xi))
    (hK : Vals.PickFits (.arr B) X
      ((List.range n.toNat).map fun q => (Column.bitsAt (tilLongs n) (q * 8) 8).toNat))
    (hV : ∀ h : len xi = m.toNat, Vals.PickFits (.arr B)
      (⟨X.1, longsN m (gather 8 (slicesOf X).1 xi) (Nat.le_of_eq ((gather_len _ _).trans h).symm),
        valCol Ew.add Ew.vv (gather 8 (slicesOf X).1 xi) xr, X.2.2.2⟩ : Vals (.arr B) m)
      ((List.range m.toNat).map fun q => (Column.bitsAt (tilLongs m) (q * 8) 8).toNat)) :
    ∀ xs yss, rep (inits X) xs yss ↔ (∃ j, X.row j = xs) ∧
      yss = (List.range (xs.length + 1)).map fun k => xs.take k := by
  have hb := fun r (hr : r < n.toNat) => slicesOf_row X hp hr
  have hsl : len (slicesOf X).1 = n.toNat := (len_slices _ _ _ _).1
  intro xs yss
  rw [nest_rep X hp (fun m s i r h => (longsN m (gather 8 s.1 i) (Nat.le_of_eq ((gather_len _ _).trans h).symm),
      valCol Ew.add Ew.vv (gather 8 s.1 i) r)) c hc hS hU xi hxi m hm xr hxr (fun r _ => st(r))
    (fun r t => st(r) + t) (fun r t hr ht => by dsimp only; have := (hb r hr).1; omega)
    (fun h d hd hx _ => by
      dsimp only; have := (hb _ hx).1; exact gather_longsN_toInt _ hd h (by rw [hsl]; exact hx) (by omega))
    (fun h d hd hx hy => by
      dsimp only; have := (hb _ hx).1; exact gather_add_toInt hd h (by rw [hsl]; exact hx) (by omega))
    hK hV (inits X) rfl]
  -- row `r`'s slices are its prefixes
  have hpre : ∀ r (hr : r < n.toNat), ((List.range (cn(r) + 1)).map fun t =>
      (List.range (st(r) + t - st(r))).map fun j =>
        if h : st(r) + j < X.1.toNat then Vals.row X.2.2.2 ⟨_, h⟩ else B.dflt) =
      (List.range ((Vals.row X ⟨r, hr⟩).length + 1)).map fun k => (Vals.row X ⟨r, hr⟩).take k := by
    intro r hr
    obtain ⟨hle, hlen, hget⟩ := hb r hr
    rw [hlen]
    refine List.map_congr_left fun t ht => ?_
    rw [List.mem_range] at ht
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, List.length_take, hlen]; omega
    · intro j h1 h2
      simp only [List.length_map, List.length_range] at h1
      rw [List.getElem_map, List.getElem_range, dif_pos (by omega), List.getElem_take, hget j (by omega) (by omega)]
  constructor
  · rintro ⟨r, hr, hx, rfl⟩
    exact ⟨⟨⟨r, hr⟩, hx⟩, by rw [hpre r hr, hx]⟩
  · rintro ⟨⟨⟨r, hr⟩, hx⟩, rfl⟩
    exact ⟨r, hr, hx, by rw [hpre r hr, hx]⟩

/-- **`tails`, read back**: an array `xs` of `X` goes to its suffixes by decreasing length, `[]` last. The counts
    plus one `c`, `expand`'s index and rank columns `xi`, `xr` (at `m` copies) are bound by their equations.
    Hypotheses: the payload count below `2^63`; the counts plus one summed below `2^63` and a `USize`;
    `Vals.PickFits` where `X` and the suffixes are picked. -/
theorem rep_tails {B : Obj} {n : USize} (X : Vals (.arr B) n) (hp : X.1.toNat < 2 ^ 63)
    (c : ByteArray) (hc : c = addc n (slicesOf X).2 1)
    (hS : pn(n.toNat) + n.toNat < 2 ^ 63) (hU : pn(n.toNat) + n.toNat < USize.size)
    (xi : ByteArray) (hxi : xi = expandBytes 8 0 (tilLongs n) c)
    (m : USize) (hm : m = (len xi).toUSize)
    (xr : ByteArray) (hxr : xr = sub m (tilLongs m) (gather 8 (sub n (sums n c) c) xi))
    (hK : Vals.PickFits (.arr B) X
      ((List.range n.toNat).map fun q => (Column.bitsAt (tilLongs n) (q * 8) 8).toNat))
    (hV : ∀ h : len xi = m.toNat, Vals.PickFits (.arr B)
      (⟨X.1, valCol Ew.add Ew.vv (gather 8 (slicesOf X).1 xi) xr,
        longsN m (gather 8 (add n (slicesOf X).1 (slicesOf X).2) xi) (Nat.le_of_eq ((gather_len _ _).trans h).symm),
        X.2.2.2⟩ : Vals (.arr B) m)
      ((List.range m.toNat).map fun q => (Column.bitsAt (tilLongs m) (q * 8) 8).toNat)) :
    ∀ xs yss, rep (tails X) xs yss ↔ (∃ j, X.row j = xs) ∧
      yss = (List.range (xs.length + 1)).map fun k => xs.drop k := by
  have hb := fun r (hr : r < n.toNat) => slicesOf_row X hp hr
  have hsl : len (slicesOf X).1 = n.toNat := (len_slices _ _ _ _).1
  have hal : len (add n (slicesOf X).1 (slicesOf X).2) = n.toNat := len_val ..
  have hend : ∀ r, r < n.toNat → (Column.bitsAt (add n (slicesOf X).1 (slicesOf X).2) (r * 8) 8).toNat =
      st(r) + cn(r) := fun r hr => by
    have := (hb r hr).1; exact add_get hr (by omega)
  intro xs yss
  rw [nest_rep X hp (fun m s i r h => (valCol Ew.add Ew.vv (gather 8 s.1 i) r,
      longsN m (gather 8 (add n s.1 s.2) i) (Nat.le_of_eq ((gather_len _ _).trans h).symm))) c hc hS hU xi hxi m hm
    xr hxr (fun r t => st(r) + t) (fun r _ => st(r) + cn(r))
    (fun r t hr ht => by dsimp only; exact ⟨by omega, (hb r hr).1⟩)
    (fun h d hd hx hy => by
      dsimp only; have := (hb _ hx).1; exact gather_add_toInt hd h (by rw [hsl]; exact hx) (by omega))
    (fun h d hd hx _ => by
      dsimp only; have := (hb _ hx).1
      rw [gather_longsN_toInt _ hd h (by rw [hal]; exact hx) (by rw [hend _ hx]; omega), hend _ hx])
    hK hV (tails X) rfl]
  -- row `r`'s slices are its suffixes
  have hsuf : ∀ r (hr : r < n.toNat), ((List.range (cn(r) + 1)).map fun t =>
      (List.range (st(r) + cn(r) - (st(r) + t))).map fun j =>
        if h : st(r) + t + j < X.1.toNat then Vals.row X.2.2.2 ⟨_, h⟩ else B.dflt) =
      (List.range ((Vals.row X ⟨r, hr⟩).length + 1)).map fun k => (Vals.row X ⟨r, hr⟩).drop k := by
    intro r hr
    obtain ⟨hle, hlen, hget⟩ := hb r hr
    rw [hlen]
    refine List.map_congr_left fun t ht => ?_
    rw [List.mem_range] at ht
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, List.length_drop, hlen]; omega
    · intro j h1 h2
      simp only [List.length_map, List.length_range] at h1
      rw [List.getElem_map, List.getElem_range, dif_pos (by omega), List.getElem_drop,
        hget (t + j) (by omega) (by omega)]
      exact congrArg _ (Fin.ext (Nat.add_assoc _ _ _))
  constructor
  · rintro ⟨r, hr, hx, rfl⟩
    exact ⟨⟨⟨r, hr⟩, hx⟩, by rw [hsuf r hr, hx]⟩
  · rintro ⟨⟨⟨r, hr⟩, hx⟩, rfl⟩
    exact ⟨r, hr, hx, by rw [hsuf r hr, hx]⟩

section Uncat

open FoldN

/-- **`uncat`, read back**: an array `xs` of `X` goes to every `(ys, zs)` with `xs = ys ++ zs`. `rep_comp` at
    `Z ≫ mem Z.val`, `rep_mem` at `Z.val`, `rep_zip` at `P`, `rep_pair` at `inits X`, `tails X`, and
    `rep_inits`, `rep_tails`; `P = pair (inits X) (tails X)` and `Z = zip P` are bound by their equations, and
    each theorem's pieces (`kc`, `c'`, `xi'`, `m'`, `xr'`, `ja`, `jb`, `jc`) by theirs. Hypotheses: each theorem's,
    at its relation — size bounds, the codes faithful and well formed (`hkO`, `hjO`), `Vals.PickFits`. -/
theorem rep_uncat {B : Obj} {n : USize} (X : Vals (.arr B) n) (hp : X.1.toNat < 2 ^ 63)
    (c : ByteArray) (hc : c = addc n (slicesOf X).2 1)
    (hS : pn(n.toNat) + n.toNat < 2 ^ 63) (hU : pn(n.toNat) + n.toNat < USize.size)
    (xi : ByteArray) (hxi : xi = expandBytes 8 0 (tilLongs n) c)
    (m : USize) (hm : m = (len xi).toUSize)
    (xr : ByteArray) (hxr : xr = sub m (tilLongs m) (gather 8 (sub n (sums n c) c) xi))
    (hK : Vals.PickFits (.arr B) X
      ((List.range n.toNat).map fun q => (Column.bitsAt (tilLongs n) (q * 8) 8).toNat))
    (hVi : ∀ h : len xi = m.toNat, Vals.PickFits (.arr B)
      (⟨X.1, longsN m (gather 8 (slicesOf X).1 xi) (Nat.le_of_eq ((gather_len _ _).trans h).symm),
        valCol Ew.add Ew.vv (gather 8 (slicesOf X).1 xi) xr, X.2.2.2⟩ : Vals (.arr B) m)
      ((List.range m.toNat).map fun q => (Column.bitsAt (tilLongs m) (q * 8) 8).toNat))
    (hVt : ∀ h : len xi = m.toNat, Vals.PickFits (.arr B)
      (⟨X.1, valCol Ew.add Ew.vv (gather 8 (slicesOf X).1 xi) xr,
        longsN m (gather 8 (add n (slicesOf X).1 (slicesOf X).2) xi) (Nat.le_of_eq ((gather_len _ _).trans h).symm),
        X.2.2.2⟩ : Vals (.arr B) m)
      ((List.range m.toNat).map fun q => (Column.bitsAt (tilLongs m) (q * 8) 8).toNat))
    (kc : Vector Code 2)
    (hkc : kc = Obj.codes (.arr B)
      (#v[⟨Rel.n (inits X), Rel.key (inits X)⟩, ⟨Rel.n (tails X), Rel.key (tails X)⟩] : Vector (Part (.arr B)) 2))
    (hkO : codesOK(kc,
      (#v[⟨Rel.n (inits X), Rel.key (inits X)⟩, ⟨Rel.n (tails X), Rel.key (tails X)⟩] : Vector (Part (.arr B)) 2)))
    (hkn : (Rel.n (tails X)).toNat < 2 ^ 63) (hkM : msum(kc, inits X, tails X) < 2 ^ 63)
    (hkU : msum(kc, inits X, tails X) < USize.size)
    (hkA : Vals.PickFits (.arr B) (Rel.key (inits X)) ((mpairs(kc, inits X, tails X)).map Prod.fst))
    (hkB : Vals.PickFits (.arr (.arr B)) (Rel.val (inits X)) ((mpairs(kc, inits X, tails X)).map Prod.fst))
    (hkC : Vals.PickFits (.arr (.arr B)) (Rel.val (tails X)) ((mpairs(kc, inits X, tails X)).map Prod.snd))
    (P : Rel (.arr B) (.prod (.arr (.arr B)) (.arr (.arr B)))) (hP : P = pair (inits X) (tails X))
    (hpa : (Rel.val P).1.1.toNat < 2 ^ 63) (hpb : (Rel.val P).2.1.toNat < 2 ^ 63)
    (c' : ByteArray) (hc' : c' = Kernel.Ew.val Ew.lesser Ew.i64 Ew.vv nul (slicesOf (Rel.val P).1).2
      (slicesOf (Rel.val P).2).2 (Rel.n P))
    (hS' : ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt c' (r * 8) 8).toNat).sum < 2 ^ 63)
    (hU' : ((List.range (Rel.n P).toNat).map fun r => (Column.bitsAt c' (r * 8) 8).toNat).sum < USize.size)
    (xi' : ByteArray) (hxi' : xi' = expandBytes 8 0 (tilLongs (Rel.n P)) c')
    (m' : USize) (hm' : m' = (len xi').toUSize)
    (xr' : ByteArray) (hxr' : xr' = sub m' (tilLongs m') (gather 8 (sub (Rel.n P) (sums (Rel.n P) c') c') xi'))
    (ja : ByteArray) (hja : ja = add m' (gather 8 (slicesOf (Rel.val P).1).1 xi') xr')
    (jb : ByteArray) (hjb : jb = add m' (gather 8 (slicesOf (Rel.val P).2).1 xi') xr')
    (hKf : Vals.PickFits (.arr B) (Rel.key P)
      ((List.range (Rel.n P).toNat).map fun q => (Column.bitsAt (tilLongs (Rel.n P)) (q * 8) 8).toNat))
    (hAf : Vals.PickFits (.arr B) (Rel.val P).1.2.2.2
      ((List.range m'.toNat).map fun q => (Column.bitsAt ja (q * 8) 8).toNat))
    (hBf : Vals.PickFits (.arr B) (Rel.val P).2.2.2.2
      ((List.range m'.toNat).map fun q => (Column.bitsAt jb (q * 8) 8).toNat))
    (Z : Rel (.arr B) (.arr (.prod (.arr B) (.arr B)))) (hZ : Z = zip P)
    (jc : Vector Code 2)
    (hjc : jc = Obj.codes (.arr (.prod (.arr B) (.arr B)))
      (#v[⟨Rel.n Z, Rel.val Z⟩, ⟨Rel.n (mem Z.val), Rel.key (mem Z.val)⟩] :
        Vector (Part (.arr (.prod (.arr B) (.arr B)))) 2))
    (hjO : codesOK(jc, (#v[⟨Rel.n Z, Rel.val Z⟩, ⟨Rel.n (mem Z.val), Rel.key (mem Z.val)⟩] :
        Vector (Part (.arr (.prod (.arr B) (.arr B)))) 2)))
    (hjn : (Rel.n (mem Z.val)).toNat < 2 ^ 63) (hjM : msum(jc, Z, mem Z.val) < 2 ^ 63)
    (hjU : msum(jc, Z, mem Z.val) < USize.size)
    (hjA : Vals.PickFits (.arr B) (Rel.key Z) ((mpairs(jc, Z, mem Z.val)).map Prod.fst))
    (hjC : Vals.PickFits (.prod (.arr B) (.arr B)) (Rel.val (mem Z.val)) ((mpairs(jc, Z, mem Z.val)).map Prod.snd))
    (hv : Vals.PickFits (.arr (.prod (.arr B) (.arr B))) Z.val (List.range Z.n.toNat))
    (hk : Vals.PickFits (.arr (.prod (.arr B) (.arr B))) Z.val ((List.range Z.n.toNat).flatMap fun r =>
      if h : r < Z.n.toNat then List.replicate (Z.val.row ⟨r, h⟩).length r else [])) :
    ∀ xs ys zs, rep (uncat X) xs (ys, zs) ↔ (∃ j, X.row j = xs) ∧ xs = ys ++ zs := by
  intro xs ys zs
  have hI := rep_inits X hp c hc hS hU xi hxi m hm xr hxr hK hVi
  have hT := rep_tails X hp c hc hS hU xi hxi m hm xr hxr hK hVt
  subst hkc
  have h1 := rep_pair (inits X) (tails X) hkO hkn hkM hkU hkA hkB hkC
  have h2 := rep_zip P hpa hpb c' hc' hS' hU' xi' hxi' m' hm' xr' hxr' ja hja jb hjb hKf hAf hBf
  subst hjc
  have h3 := rep_comp Z (mem Z.val) hjO hjn hjM hjU hjA hjC
  have h4 := rep_mem Z.val hv hk
  subst hZ hP
  show rep (zip (pair (inits X) (tails X)) ≫ mem (zip (pair (inits X) (tails X))).val) xs (ys, zs) ↔ _
  rw [h3]
  constructor
  · rintro ⟨ps, hz, hm⟩
    obtain ⟨-, hmem⟩ := (h4 ps (ys, zs)).1 hm
    obtain ⟨a, b, hab, rfl⟩ := (h2 xs ps).1 hz
    rw [h1] at hab
    obtain ⟨hx, rfl⟩ := (hI xs a).1 hab.1
    obtain ⟨-, rfl⟩ := (hT xs b).1 hab.2
    refine ⟨hx, ?_⟩
    rw [List.zip_map'] at hmem
    obtain ⟨k, -, he⟩ := List.mem_map.1 hmem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact (List.take_append_drop k xs).symm
  · rintro ⟨hx, hxs⟩
    have hz := (h2 xs _).2 ⟨_, _, by rw [h1]; exact ⟨(hI xs _).2 ⟨hx, rfl⟩, (hT xs _).2 ⟨hx, rfl⟩⟩, rfl⟩
    refine ⟨_, hz, (h4 _ _).2 ⟨?_, ?_⟩⟩
    · obtain ⟨q, -, hq⟩ := hz
      exact ⟨q, hq⟩
    · rw [List.zip_map']
      exact List.mem_map.2 ⟨ys.length, List.mem_range.2 (by rw [hxs, List.length_append]; omega),
        by rw [hxs]; simp⟩

end Uncat

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.Rep.nest_rep
#print axioms LeetQ.Rel.Rep.rep_inits
#print axioms LeetQ.Rel.Rep.rep_tails
#print axioms LeetQ.Rel.Rep.rep_uncat
