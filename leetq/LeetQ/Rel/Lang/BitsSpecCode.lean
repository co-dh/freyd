/-
  `codeAll` read back: the codes it hands each table are the table's elements under one decoding map per object.
  One object's columns are coded jointly (`Obj.codes`, `Code.cat`), renumbered by `groupIds` and widened to longs
  by `gatherPacked`; code `a` decodes to the row at `a`'s first occurrence (`blockU`), and a row holds code `a`
  exactly when it is that element. This is `rep_leafB`'s premise at every leaf.
-/
import LeetQ.Rel.Lang.BitsSpec
import LeetQ.Rel.KernelWF.CodesAll
import LeetQ.Rel.KernelWF.CodesProd
import LeetQ.Rel.KernelWF.JoinAssembly
import LeetQ.Rel.KernelWF.JoinContent
import LeetQ.Rel.KernelWF.CodesSpec

namespace LeetQ.Rel.Lang.Bits

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep

/-! ### Parts end to end -/

/-- Every `g` below the summed counts is row `i` of part `k`: `g = (counts before k) + i`. -/
theorem exists_off {α : Type} (n : α → Nat) : ∀ (l : List α) {g : Nat}, g < (l.map n).sum →
    ∃ (k : Nat) (hk : k < l.length) (i : Nat), i < n l[k] ∧ g = ((l.take k).map n).sum + i
  | [], g, h => by simp at h
  | x :: l, g, h => by
    by_cases hg : g < n x
    · exact ⟨0, by simp, g, hg, by simp⟩
    · obtain ⟨k, hk, i, hi, e⟩ := exists_off n l (g := g - n x) (by simp only [List.map_cons, List.sum_cons] at h; omega)
      exact ⟨k + 1, by simp; omega, i, hi, by simp only [List.take_succ_cons, List.map_cons, List.sum_cons]; omega⟩

/-- Row `i` of part `k` lies below the summed counts. -/
theorem off_lt {α : Type} (n : α → Nat) : ∀ (l : List α) (k : Nat) (hk : k < l.length) (i : Nat), i < n l[k] →
    ((l.take k).map n).sum + i < (l.map n).sum
  | [], _, hk, _, _ => absurd hk (by simp)
  | x :: l, 0, _, i, hi => by simp only [List.take_zero, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons]
                              simp at hi; omega
  | x :: l, k + 1, hk, i, hi => by
    have := off_lt n l k (by simpa using hk) i (by simpa using hi)
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons]; omega

/-- Entry `(counts before k) + i` of the parts' lists end to end is entry `i` of part `k`. -/
theorem flatMap_off {α β : Type} (f : α → List β) : ∀ (l : List α) (k : Nat) (hk : k < l.length) (i : Nat),
    i < (f l[k]).length → (l.flatMap f)[((l.take k).map fun a => (f a).length).sum + i]? = (f l[k])[i]?
  | [], _, hk, _, _ => absurd hk (by simp)
  | x :: l, 0, _, i, hi => by
    have hi' : i < (f x).length := hi
    simp only [List.flatMap_cons, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.getElem_cons_zero]
    exact List.getElem?_append_left hi'
  | x :: l, k + 1, hk, i, hi => by
    have := flatMap_off f l k (by simpa using hk) i (by simpa using hi)
    simp only [List.flatMap_cons, List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]
    rw [Nat.add_assoc, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact this

variable {A : Obj}

/-- The parts' rows end to end. -/
def catRows (ps : Array (Part A)) : List A.El := ps.toList.flatMap fun c => (List.finRange c.1.toNat).map c.2.row

/-- Row `i` of part `k` is entry `(counts before k) + i` of `catRows`. -/
theorem catRows_off (ps : Array (Part A)) {k : Nat} (hk : k < ps.size) {i : Nat} (hi : i < ps[k].1.toNat) :
    (catRows ps)[((ps.toList.take k).map (·.1.toNat)).sum + i]? = some (ps[k].2.row ⟨i, hi⟩) := by
  have h := flatMap_off (fun c : Part A => (List.finRange c.1.toNat).map c.2.row) ps.toList k (by simpa using hk) i
    (by simpa using hi)
  simp only [List.length_map, List.length_finRange] at h
  rw [catRows, h]; simp only [Array.getElem_toList, List.getElem?_map]
  rw [List.getElem?_eq_getElem (by simpa using hi)]; simp

/-- Every node's parts sum within a `USize`, the first bound `CodesFit` states. -/
theorem codesFit_sum : ∀ (A : Obj) {p : Nat} {cs : Vector (Part A) p}, A.CodesFit cs →
    (cs.toList.map (·.1.toNat)).sum < USize.size
  | .atom _, _, _, h => h.1
  | .prod _ _, _, _, h => h.1
  | .arr _, _, _, h => h.2.1
  | .sum _ _, _, _, h => h.1

/-! ### One object's block of codes -/

/-- One object's parts coded jointly, as `codeAll` codes them: `Code.cat` of `Obj.codes`. -/
def blockCode (ps : Array (Part A)) : Code := Code.cat (A.codes (p := ps.size) ⟨ps, rfl⟩).toArray

/-- The element at code `a` of `blockCode`'s classes: the row at the class's first occurrence. -/
def blockU (ps : Array (Part A)) (a : Nat) : A.El :=
  (((firstsOf (Column.idAt (blockCode ps).b (blockCode ps).w) (blockCode ps).n.toNat)[a]?).bind
    fun f => (catRows ps)[f]?).getD A.dflt

/-- A long payload at `64` bits reads its longs. -/
theorem idAt_64 (b : ByteArray) (j : Nat) : Column.idAt b 64 j = (Column.bitsAt b (j * 8) 8).toNat := by
  rw [Column.idAt, show (64 : Nat) = 8 * 8 from rfl, resAt_lane b 8 j (Nat.le_refl _), Nat.mul_comm]

/-- `Code.cat`'s `card` is the parts' largest. -/
theorem cat_card (cs : Array Code) (hN : (cs.toList.map (·.n.toNat)).sum < USize.size) :
    (Code.cat cs).card = cs.toList.foldl (fun m c => max m c.card) 0 := by
  have hS : cs.foldl (fun s c => s + c.n.toNat) 0 = (cs.toList.map (·.n.toNat)).sum := by
    rw [← Array.foldl_toList, foldl_add_sum (fun c : Code => c.n.toNat), Nat.zero_add]
  unfold Code.cat; simp only [need, hS, hN, ↓reduceDIte, Array.foldl_toList]

theorem foldl_max_ge (l : List Code) : ∀ m₀, (m₀ ≤ l.foldl (fun m c => max m c.card) m₀) ∧
    ∀ c ∈ l, c.card ≤ l.foldl (fun m c => max m c.card) m₀ := by
  induction l with
  | nil => simp
  | cons x l ih =>
    intro m₀
    obtain ⟨h1, h2⟩ := ih (max m₀ x.card)
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, fun c hc => ?_⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 c hc

theorem foldl_max_lt (l : List Code) (B : Nat) : ∀ m₀, m₀ < B → (∀ c ∈ l, c.card < B) →
    l.foldl (fun m c => max m c.card) m₀ < B := by
  induction l with
  | nil => intro m₀ h _; exact h
  | cons x l ih =>
    intro m₀ h hl
    exact ih _ (Nat.max_lt.2 ⟨h, hl x (by simp)⟩) fun c hc => hl c (by simp [hc])

/-- **One object's block read back**: with `codesC`'s bit, the longs `codeAll` writes for the parts `ps` hold, at
    row `i` of part `k` (position `(counts before k) + i`), a code below the class count `len G.2`, and code `a` there
    exactly when the row is `blockU ps a`. -/
theorem block_spec (ps : Array (Part A)) (hp : 0 < ps.size) (hok : (A.codesC (p := ps.size) ⟨ps, rfl⟩).2 = true) :
    let cc := blockCode ps
    let I := gatherPacked cc.n (Column.idWidthOf (len cc.groupIds.2)).toUSize 64 0 cc.groupIds.1 (tilLongs cc.n)
    len cc.groupIds.2 < USize.size ∧ cc.n.toNat = (ps.toList.map (·.1.toNat)).sum ∧
      (ids I).length = cc.n.toNat ∧
      ∀ k (hk : k < ps.size) i (hi : i < ps[k].1.toNat),
        ∃ h : ((ps.toList.take k).map (·.1.toNat)).sum + i < (ids I).length,
          (ids I)[((ps.toList.take k).map (·.1.toNat)).sum + i]'h < len cc.groupIds.2 ∧
          ∀ a < len cc.groupIds.2, ((ids I)[((ps.toList.take k).map (·.1.toNat)).sum + i]'h = a ↔ ps[k].2.row ⟨i, hi⟩ = blockU ps a) := by
  intro cc I
  obtain ⟨⟨hfaith, hwf⟩, hlw⟩ := codes_faithful_wf A _ (Obj.codesC_fits A _ hok)
  have hN : (ps.toList.map (·.1.toNat)).sum < USize.size := codesFit_sum A (Obj.codesC_fits A _ hok)
  generalize hcx : A.codes (p := ps.size) ⟨ps, rfl⟩ = cx at hfaith hwf hlw
  have hcc : cc = Code.cat cx.toArray := by simp only [cc, blockCode, hcx]
  have hcn : ∀ k (hk : k < ps.size), cx[k].n = ps[k].1 := fun k hk => (hwf hk).2.1
  have hns : cx.toArray.toList.map (·.n.toNat) = ps.toList.map (·.1.toNat) :=
    List.ext_getElem (by simp) fun k h1 h2 => by simp [hcn k (by simpa using h2)]
  have hns' : cx.toList.map (·.n.toNat) = ps.toList.map (·.1.toNat) := hns
  have hoff : ∀ k, ((cx.toArray.toList.take k).map (·.n.toNat)).sum = ((ps.toList.take k).map (·.1.toNat)).sum := by
    intro k; rw [List.map_take, List.map_take, hns]
  obtain ⟨⟨hlane, hsz, -⟩, hn, hget⟩ := cat_parts cx hp hlw
    (fun hk => ⟨(hwf hk).1, (hwf hk).2.2.1, fun h8 i hi =>
      Nat.lt_of_lt_of_le (((hwf hk).2.2.2 h8).2 i hi) (Nat.le_max_left _ _)⟩) (by first | (rw [hns]; exact hN) | (rw [hns']; exact hN))
  rw [← hcc] at hlane hsz hn hget
  first | rw [hns] at hn | rw [hns'] at hn
  -- global position `g` is row `i` of part `k`
  have hpos : ∀ g < cc.n.toNat, ∃ (k : Nat) (hk : k < ps.size) (i : Nat) (hi : i < ps[k].1.toNat),
      g = ((ps.toList.take k).map (·.1.toNat)).sum + i := by
    intro g hg
    obtain ⟨k, hk, i, hi, e⟩ := exists_off (fun c : Part A => c.1.toNat) ps.toList (g := g) (by rw [← hn]; exact hg)
    exact ⟨k, by simpa using hk, i, by simpa using hi, e⟩
  have hw0 : ∀ k (hk : k < ps.size), cc.w = cx[k].w := by
    intro k hk
    have := (cat_get cx.toArray (w := cx[0].w) (hlw hp hp ▸ (hwf hp).1) (by simpa using hp)
      (fun c hc => by obtain ⟨l, hl, rfl⟩ := Array.mem_iff_getElem.1 hc; exact hlw (by simpa using hl) hp)
      (fun c hc => by obtain ⟨l, hl, rfl⟩ := Array.mem_iff_getElem.1 hc
                      rw [← hlw (by simpa using hl) hp]; exact (hwf (by simpa using hl)).2.2.1)
      (fun h8 c hc i hi => by
        obtain ⟨l, hl, rfl⟩ := Array.mem_iff_getElem.1 hc
        rw [← hlw (by simpa using hl) hp] at h8 ⊢
        exact Nat.lt_of_lt_of_le (((hwf (by simpa using hl)).2.2.2 h8).2 i hi) (Nat.le_max_left _ _))
      (by rw [hns]; exact hN)).1
    rw [hcc, this]; exact hlw hp hk
  have hread : ∀ k (hk : k < ps.size) i (hi : i < ps[k].1.toNat),
      Column.idAt cc.b cc.w (((ps.toList.take k).map (·.1.toNat)).sum + i) = Column.idAt cx[k].b cx[k].w i := by
    intro k hk i hi
    have := hget k hk i (by rw [hcn k hk]; exact hi)
    first | (rw [← hoff k]; exact this) | (rw [← hoff k] at this ⊢; exact this) | exact (hoff k) ▸ this
  -- equal codes, equal rows, across the whole block
  have hfg : ∀ k (hk : k < ps.size) i (hi : i < ps[k].1.toNat) l (hl : l < ps.size) j (hj : j < ps[l].1.toNat),
      Column.idAt cc.b cc.w (((ps.toList.take k).map (·.1.toNat)).sum + i) =
        Column.idAt cc.b cc.w (((ps.toList.take l).map (·.1.toNat)).sum + j) ↔
      ps[k].2.row ⟨i, hi⟩ = ps[l].2.row ⟨j, hj⟩ := by
    intro k hk i hi l hl j hj
    rw [hread k hk i hi, hread l hl j hj]
    exact hfaith hk hl hi hj
  have hcard : cc.w < 8 → cc.card < USize.size ∧ ∀ i < cc.n.toNat, Column.idAt cc.b cc.w i < cc.card := by
    intro h8
    have hc : cc.card = cx.toList.foldl (fun m c => max m c.card) 0 := by
      rw [hcc, cat_card _ (by first | (rw [hns]; exact hN) | (rw [hns']; exact hN))]
      rfl
    have hmem : ∀ c ∈ cx.toList, ∃ k, ∃ hk : k < ps.size, c = cx[k] := fun c hc => by
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hc; exact ⟨k, by simpa using hk, by simp⟩
    refine ⟨?_, fun g hg => ?_⟩
    · rw [hc]; refine foldl_max_lt _ _ 0 USize.size_pos fun c hc => ?_
      obtain ⟨k, hk, rfl⟩ := hmem c hc
      exact ((hwf hk).2.2.2 (by rw [← hw0 k hk]; exact h8)).1
    · obtain ⟨k, hk, i, hi, rfl⟩ := hpos g hg
      rw [hread k hk i hi, hc]
      refine Nat.lt_of_lt_of_le (((hwf hk).2.2.2 (by rw [← hw0 k hk]; exact h8)).2 i (by rw [hcn k hk]; exact hi)) ?_
      exact (foldl_max_ge _ 0).2 _ (by simp)
  obtain ⟨-, hgo⟩ := groupIds_groupOf cc hlane hsz hcard
  obtain ⟨hlen, hFle⟩ := groupIds_len cc hlane hsz hcard
  generalize hF : firstsOf (Column.idAt cc.b cc.w) cc.n.toNat = F at hlen hFle
  have hNU : cc.n.toNat < USize.size := by rw [hn]; exact hN
  have hW : (Column.idWidthOf (len cc.groupIds.2)).toUSize.toNat = Column.idWidthOf (len cc.groupIds.2) :=
    USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (idWidthOf_le _) (Nat.lt_of_lt_of_le (by decide) USize.le_size))
  have h64 : (64 : USize).toNat = 64 := USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have hU64 : USize.size ≤ 2 ^ 64 := by cases USize.size_eq <;> simp_all
  have hTl : (tilLongs cc.n).size / 8 = cc.n.toNat := by rw [← len_tilLongs cc.n]; rfl
  have hIsz : I.size = 8 * cc.n.toNat := by
    simp only [I, gatherPacked]; rw [h64, KernelWF.packIds_size (Or.inr (by decide)), hTl]; omega
  have hIl : (ids I).length = cc.n.toNat := by rw [← len_eq_ids, len, hIsz]; omega
  -- long `g` of the block is `g`'s class
  have hI : ∀ g (hg : g < (ids I).length), (ids I)[g] = Verify.groupOf (Column.idAt cc.b cc.w) cc.n.toNat g := by
    intro g hg
    have hg' : g < cc.n.toNat := hIl ▸ hg
    rw [ids_getElem, ← idAt_64]
    have e := idAt_gatherPacked cc.n (Column.idWidthOf (len cc.groupIds.2)).toUSize 64 0 cc.groupIds.1 (tilLongs cc.n)
      (by rw [h64]; simp) (fun i hi => by
        rw [hW, h64, hgo i hi]
        exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hF ▸ groupOf_lt hi) hFle) (Nat.le_trans (Nat.le_of_lt hNU) hU64))
      (by simp) g (by rw [hTl]; exact hg')
    rw [h64] at e
    rw [show I = gatherPacked cc.n (Column.idWidthOf (len cc.groupIds.2)).toUSize 64 0 cc.groupIds.1 (tilLongs cc.n)
      from rfl, e, tilLongs_get hg', if_pos hg', hW, hgo g hg']
  have hLU : len cc.groupIds.2 < USize.size := by rw [hlen]; exact Nat.lt_of_le_of_lt hFle hNU
  refine ⟨hLU, hn, hIl, fun k hk i hi => ?_⟩
  have hg : ((ps.toList.take k).map (·.1.toNat)).sum + i < cc.n.toNat := by
    rw [hn]; exact off_lt (fun c : Part A => c.1.toNat) ps.toList k (by simpa using hk) i (by simpa using hi)
  refine ⟨hIl ▸ hg, ?_, fun a ha => ?_⟩
  · rw [hI _ (hIl ▸ hg), hlen, ← hF]; exact groupOf_lt hg
  · rw [hlen] at ha
    have haF : a < (firstsOf (Column.idAt cc.b cc.w) cc.n.toNat).length := hF ▸ ha
    have hfa : F[a] < cc.n.toNat := by
      have hm : F[a] ∈ firstsOf (Column.idAt cc.b cc.w) cc.n.toNat := by rw [hF]; exact List.getElem_mem ha
      exact (mem_firstsOf_iff.1 hm).1
    obtain ⟨l, hl, j, hj, hfe⟩ := hpos _ hfa
    have hU : blockU ps a = ps[l].2.row ⟨j, hj⟩ := by
      show (((firstsOf (Column.idAt cc.b cc.w) cc.n.toNat)[a]?).bind fun f => (catRows ps)[f]?).getD A.dflt = _
      rw [hF, List.getElem?_eq_getElem ha, Option.bind_some, hfe, catRows_off ps hl hj]; rfl
    rw [hI _ (hIl ▸ hg), hU, groupOf_eq_iff hg haF, ← hfg k hk i hi l hl j hj, ← hfe]
    simp only [hF]

#print axioms block_spec

/-! ### The loop of `codeAll` -/

/-- A column as a part of `A`: its own where it is of `A`, else empty. -/
def castPart (A : Obj) : Col → Part A
  | ⟨B, p⟩ => if h : B = A then h ▸ p else ⟨0, Vals.empty A⟩

theorem castPart_eq (A : Obj) (x : Col) :
    (if h : x.1 = A then h ▸ x.2 else ⟨0, Vals.empty A⟩) = castPart A x := by
  obtain ⟨B, p⟩ := x; rfl

theorem getD_eq' {α : Type} (xs : Array α) (i : Nat) (v : α) :
    (if h : i < xs.size then xs.getInternal i h else v) = xs.getD i v := rfl

/-- An object's parts in `cs`, as `codeAll` gathers them while at the column `c`. -/
def partsOf (cs : Array Col) (A : Obj) (c : Col) : Array (Part A) :=
  ((Array.range cs.size).filter fun j => (cs.getD j c).1 == A).map fun j => castPart A (cs.getD j c)

theorem getD_lt {α : Type} (xs : Array α) {j : Nat} (hj : j < xs.size) (d : α) : xs.getD j d = xs[j] := by
  simp [Array.getD, hj]

/-- The gathered parts do not depend on the column the loop is at. -/
theorem partsOf_congr (cs : Array Col) (A : Obj) (c d : Col) : partsOf cs A c = partsOf cs A d := by
  have e : ∀ j ∈ (Array.range cs.size).toList, cs.getD j c = cs.getD j d := fun j hj => by
    have : j < cs.size := by simpa using hj
    rw [getD_lt cs this, getD_lt cs this]
  apply Array.toList_inj.1
  simp only [partsOf, Array.toList_map, Array.toList_filter]
  rw [List.filter_congr fun j hj => by rw [e j hj]]
  exact List.map_congr_left fun j hj => by rw [e j (List.mem_filter.1 hj).1]

/-- The decoding map of the object `A`: `blockU` of all its parts in `cs`. -/
def uOf (cs : Array Col) (A : Obj) : Nat → A.El := blockU (partsOf cs A ⟨A, ⟨0, Vals.empty A⟩⟩)

/-- The longs `b` written for the part `p` of `A` read back against `A`'s picked elements `q`: one code per row,
    each below `q`'s count, code `a` exactly at the rows that are `uOf cs A a`. -/
def ColOK (cs : Array Col) {A : Obj} (p : Part A) (b : ByteArray) (q : Part A) : Prop :=
  (ids b).length = p.1.toNat ∧ ∀ r (hr : r < p.1.toNat) (h : r < (ids b).length), (ids b)[r] < q.1.toNat ∧
    ∀ a < q.1.toNat, ((ids b)[r] = a ↔ p.2.row ⟨r, hr⟩ = uOf cs A a)

/-- A `for` over a list in `Option` whose body only yields carries an invariant indexed by the prefix done. -/
theorem forIn_inv {α σ : Type} (L : List α) (f : α → σ → Option (ForInStep σ)) (P : List α → σ → Prop)
    (hf : ∀ pre a s r, a ∈ L → P pre s → f a s = some r → ∃ s', r = .yield s' ∧ P (pre ++ [a]) s') :
    ∀ (l : List α), (∀ a ∈ l, a ∈ L) → ∀ pre s t, P pre s → forIn l s f = some t → P (pre ++ l) t
  | [], _, pre, s, t, hs, h => by simp only [List.forIn_nil] at h; cases h; simpa using hs
  | a :: l, hl, pre, s, t, hs, h => by
    rw [List.forIn_cons] at h
    cases hr : f a s with
    | none => rw [hr] at h; cases h
    | some r =>
      obtain ⟨s', rfl, hs'⟩ := hf pre a s r (hl a (by simp)) hs hr
      rw [hr] at h
      have := forIn_inv L f P hf l (fun b hb => hl b (by simp [hb])) (pre ++ [a]) s' t hs' h
      simpa using this

/-- What the loop of `codeAll` keeps over the columns `pre` done: one long column per column of `cs`, each object
    met so far picked once in `sps`, and every column of a picked object read back against its pick. -/
def Inv (cs : Array Col) (pre : List Col) (s : MProd (Array ByteArray) (Array Col)) : Prop :=
  s.1.size = cs.size ∧ (∀ c ∈ pre, s.2.any (·.1 == c.1) = true) ∧
  ∀ j (hj : j < cs.size) (A : Obj) (p : Part A), cs[j] = ⟨A, p⟩ → s.2.any (·.1 == A) = true →
    ∃ q, s.2.find? (·.1 == A) = some ⟨A, q⟩ ∧ ColOK cs p (s.1.getD j .empty) q

/-- The indices of `A`'s columns in `cs`, as `codeAll` gathers them while at the column `c`. -/
def jsOf (cs : Array Col) (A : Obj) (c : Col) : Array Nat := (Array.range cs.size).filter fun j => (cs.getD j c).1 == A

/-- One step of `codeAll`'s loop, at the column `c`: `codeAll`'s body with its gathered columns named. -/
def codeStep (cs : Array Col) (c : Col) (r : MProd (Array ByteArray) (Array Col)) :
    Option (ForInStep (MProd (Array ByteArray) (Array Col))) := do
  let out := r.1
  let sps := r.2
  let A := c.1
  if sps.any (·.1 == A) then return .yield ⟨out, sps⟩
  let js := jsOf cs A c
  let parts := partsOf cs A c
  let (codes, ok) := A.codesC (p := parts.size) ⟨parts, rfl⟩
  guard ok
  let cc := Code.cat codes.toArray
  let (gid, firsts) := cc.groupIds
  let ids := gatherPacked cc.n (Column.idWidthOf (len firsts)).toUSize 64 0 gid (tilLongs cc.n)
  let some (all, ok) := (if h : (parts.toList.map fun c : Part A => c.1.toNat).sum < USize.size then
    some (A.razeC parts h) else none) | none
  guard ok
  let sps := sps.push ⟨A, Vals.pickPart A all firsts⟩
  let mut out := out
  let mut o := 0
  for k in [0:js.size] do
    let n := (parts.getD k ⟨0, Vals.empty A⟩).1.toNat
    out := out.set! (js.getD k 0) (ids.extract (8 * o) (8 * (o + n)))
    o := o + n
  return .yield ⟨out, sps⟩

theorem codeAll_eq (cs : Array Col) :
    codeAll cs = (do let r ← forIn cs ⟨Array.replicate cs.size .empty, #[]⟩ (codeStep cs); pure (r.1, r.2)) := rfl

theorem find?_none_of_any {α : Type} {p : α → Bool} {xs : Array α} (h : ¬ xs.any p = true) : xs.find? p = none := by
  rw [Array.find?_eq_none]; intro x hx hp
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  exact h (Array.any_eq_true.2 ⟨i, hi, hp⟩)

#print axioms codeAll_eq

end LeetQ.Rel.Lang.Bits