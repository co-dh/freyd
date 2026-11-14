/-
  A product side's joint codes, faithful and well formed, from its two columns'.

  Every index in a statement here carries its bound explicitly (`xs[k]'hk`): left to `get_elem_tactic`,
  the index proofs of this many binders ran Lean out of memory (`std::bad_alloc` at 20 GB) before any tactic.
-/
import LeetQ.Rel.KernelWF.CodesProd

open LaneN

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

/-- **A product side's codes are faithful and well formed, on one lane**, given its two columns' are, one
    lane each, the parts' summed count a `USize`: `pairCode_spec` of the columns laid end to end
    (`cat_parts`), cut back. -/
theorem codes_prod_faithful_wf {a b : Obj} {p : Nat} (cs : Vector (Part (.prod a b)) p)
    {pa : Vector (Part a) p} {pb : Vector (Part b) p} {ca cb : Vector Code p}
    (hpa : cs.map (fun c => (⟨c.1, c.2.1⟩ : Part a)) = pa) (hpb : cs.map (fun c => (⟨c.1, c.2.2⟩ : Part b)) = pb)
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
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size) :
    ((∀ {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (cs[k]'hk).1.toNat)
        (hj : j < (cs[l]'hl).1.toNat),
        Column.idAt ((Obj.codes (.prod a b) cs)[k]'hk).b ((Obj.codes (.prod a b) cs)[k]'hk).w i =
          Column.idAt ((Obj.codes (.prod a b) cs)[l]'hl).b ((Obj.codes (.prod a b) cs)[l]'hl).w j ↔
        Vals.row (A := .prod a b) (cs[k]'hk).2 ⟨i, hi⟩ = Vals.row (A := .prod a b) (cs[l]'hl).2 ⟨j, hj⟩) ∧
      ∀ {k : Nat} (hk : k < p),
        let c := (Obj.codes (.prod a b) cs)[k]'hk
        laneOK(c.w) ∧ c.n = (cs[k]'hk).1 ∧
        c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
        (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)) ∧
      ∀ {k l : Nat} (hk : k < p) (hl : l < p),
        ((Obj.codes (.prod a b) cs)[k]'hk).w = ((Obj.codes (.prod a b) cs)[l]'hl).w := by
  rw [codes_prod_eq, hpa, hpb, hca, hcb]
  obtain ⟨hfa, hwa⟩ := hfa
  obtain ⟨hfb, hwb⟩ := hfb
  have hpa' : ∀ k (hk : k < p), pa[k]'hk = ⟨(cs[k]'hk).1, (cs[k]'hk).2.1⟩ := fun k hk => by
    rw [← hpa, Vector.getElem_map]
  have hpb' : ∀ k (hk : k < p), pb[k]'hk = ⟨(cs[k]'hk).1, (cs[k]'hk).2.2⟩ := fun k hk => by
    rw [← hpb, Vector.getElem_map]
  have hna : ∀ k (hk : k < p), (ca[k]'hk).n = (cs[k]'hk).1 := fun k hk => by rw [(hwa hk).2.1, hpa' k hk]
  have hnb : ∀ k (hk : k < p), (cb[k]'hk).n = (cs[k]'hk).1 := fun k hk => by rw [(hwb hk).2.1, hpb' k hk]
  have hLa : ca.toList.map (·.n.toNat) = cs.toList.map (·.1.toNat) :=
    List.ext_getElem (by simp) fun k h1 _ => by
      simp only [List.getElem_map, Vector.getElem_toList]; rw [hna k (by simpa using h1)]
  have hLb : cb.toList.map (·.n.toNat) = cs.toList.map (·.1.toNat) :=
    List.ext_getElem (by simp) fun k h1 _ => by
      simp only [List.getElem_map, Vector.getElem_toList]; rw [hnb k (by simpa using h1)]
  have hLn : (ca.map (·.n)).toList.map (·.toNat) = cs.toList.map (·.1.toNat) := by
    rw [Vector.toList_map, List.map_map]; exact hLa
  have hO : ∀ (L : List Code) k, L.map (·.n.toNat) = cs.toList.map (·.1.toNat) →
      ((L.take k).map (·.n.toNat)).sum = ((cs.toList.take k).map (·.1.toNat)).sum := fun L k h => by
    rw [List.map_take, h, ← List.map_take]
  have hOn : ∀ k, (((ca.map (·.n)).toList.take k).map (·.toNat)).sum = ((cs.toList.take k).map (·.1.toNat)).sum :=
    fun k => by rw [List.map_take, hLn, ← List.map_take]
  have hlt : ∀ k (hk : k < p), ∀ i < (cs[k]'hk).1.toNat, ((cs.toList.take k).map (·.1.toNat)).sum + i <
      (cs.toList.map (·.1.toNat)).sum := fun k hk i hi => by
    have := take_sum_le (cs.toList.map (·.1.toNat)) (k := k) (by simpa using hk)
    simp only [List.getElem_map, Vector.getElem_toList, ← List.map_take] at this; omega
  -- every claim names a part, so with none there is nothing to show
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact ⟨⟨fun {_ _} hk => absurd hk (Nat.not_lt_zero _), fun {_} hk => absurd hk (Nat.not_lt_zero _)⟩,
      fun {_ _} hk => absurd hk (Nat.not_lt_zero _)⟩
  have catA := cat_parts ca hp hla (fun hk => ⟨(hwa hk).1, (hwa hk).2.2.1,
    fun h i hi => Nat.lt_of_lt_of_le (((hwa hk).2.2.2 h).2 i hi) (Nat.le_max_left _ _)⟩) (by rw [hLa]; exact hN)
  have catB := cat_parts cb hp hlb (fun hk => ⟨(hwb hk).1, (hwb hk).2.2.1,
    fun h i hi => Nat.lt_of_lt_of_le (((hwb hk).2.2.2 h).2 i hi) (Nat.le_max_left _ _)⟩) (by rw [hLb]; exact hN)
  have hBA : (Code.cat cb.toArray).n = (Code.cat ca.toArray).n :=
    USize.toNat_inj.1 (by rw [catB.2.1, catA.2.1, hLb, hLa])
  have hP := pairCode_spec false (Code.cat ca.toArray) (Code.cat cb.toArray) hBA
    ⟨catA.1.1, catA.1.2.1, fun h i hi => by have := catA.1.2.2 h i hi; omega⟩
    ⟨catB.1.1, catB.1.2.1, fun h i hi => by have := catB.1.2.2 h i hi; omega⟩
  dsimp only at hP
  obtain ⟨⟨hRw, hRn, hRs, hRid⟩, hRiff⟩ := hP
  have hs : ((ca.map (·.n)).toList.map (·.toNat)).sum =
      (pairCode false (Code.cat ca.toArray) (Code.cat cb.toArray)).1.n.toNat := by
    rw [hLn, hRn, catA.2.1, hLa]
  have hab : ∀ k, ((cb.toList.take k).map (·.n.toNat)).sum = ((ca.toList.take k).map (·.n.toNat)).sum :=
    fun k => (hO _ k hLb).trans (hO _ k hLa).symm
  refine ⟨⟨fun {k l} hk hl i j hi hj => ?_, fun {k} hk => ?_⟩, fun {k l} hk hl => ?_⟩
  · obtain ⟨hwk, -, -, hck⟩ := cut_get _ (ca.map (·.n)) hRw hs hk
    obtain ⟨hwl, -, -, hcl⟩ := cut_get _ (ca.map (·.n)) hRw hs hl
    have hik : i < (ca[k]'hk).n.toNat := by rw [hna k hk]; exact hi
    have hjl : j < (ca[l]'hl).n.toNat := by rw [hna l hl]; exact hj
    rw [hwk, hwl, hck i (by rw [Vector.getElem_map]; exact hik), hcl j (by rw [Vector.getElem_map]; exact hjl),
      hOn, hOn,
      hRiff _ (by rw [catA.2.1, hLa]; exact hlt k hk i hi) _ (by rw [catA.2.1, hLa]; exact hlt l hl j hj),
      ← hO ca.toList k hLa, ← hO ca.toList l hLa, catA.2.2 k hk i hik, catA.2.2 l hl j hjl, ← hab k, ← hab l,
      catB.2.2 k hk i (by rw [hnb k hk]; exact hi), catB.2.2 l hl j (by rw [hnb l hl]; exact hj),
      hfa hk hl (by rw [hpa' k hk]; exact hi) (by rw [hpa' l hl]; exact hj),
      hfb hk hl (by rw [hpb' k hk]; exact hi) (by rw [hpb' l hl]; exact hj),
      row_part_congr (hpa' k hk) _ hi, row_part_congr (hpa' l hl) _ hj,
      row_part_congr (hpb' k hk) _ hi, row_part_congr (hpb' l hl) _ hj]
    exact (iff_of_eq (Prod.mk.injEq _ _ _ _)).symm
  · obtain ⟨hwk, hnk, hck, hik⟩ := cut_get _ (ca.map (·.n)) hRw hs hk
    have hzk := cut_size _ (ca.map (·.n)) hRw hs hRs hk
    dsimp only
    rw [hzk, hwk, hnk, hck]
    refine ⟨hRw, by rw [Vector.getElem_map, hna k hk], rfl, fun h8 => ⟨(hRid h8).1, fun i hi => ?_⟩⟩
    rw [hik i hi]
    refine (hRid h8).2 _ ?_
    rw [← hs, hLn, hOn]
    exact hlt k hk i (by rw [Vector.getElem_map, hna k hk] at hi; exact hi)
  · rw [(cut_get _ (ca.map (·.n)) hRw hs hk).1, (cut_get _ (ca.map (·.n)) hRw hs hl).1]

#print axioms codes_prod_faithful_wf

/-- **A boolean × eight-byte integral side of one part: its codes are faithful and well formed**, on
    either branch of the long column's `codes`. -/
theorem codes_prod_boolean_long_one {t : QAtomicType} (ht : orderKind t = some .i64)
    (x : Part (.prod (.atom .boolean) (.atom t))) :
    ((∀ {k l : Nat} (hk : k < 1) (hl : l < 1) {i j : Nat} (hi : i < (#v[x][k]'hk).1.toNat)
        (hj : j < (#v[x][l]'hl).1.toNat),
        Column.idAt ((Obj.codes (.prod (.atom .boolean) (.atom t)) #v[x])[k]'hk).b
            ((Obj.codes (.prod (.atom .boolean) (.atom t)) #v[x])[k]'hk).w i =
          Column.idAt ((Obj.codes (.prod (.atom .boolean) (.atom t)) #v[x])[l]'hl).b
            ((Obj.codes (.prod (.atom .boolean) (.atom t)) #v[x])[l]'hl).w j ↔
        Vals.row (A := .prod (.atom .boolean) (.atom t)) (#v[x][k]'hk).2 ⟨i, hi⟩ =
          Vals.row (A := .prod (.atom .boolean) (.atom t)) (#v[x][l]'hl).2 ⟨j, hj⟩) ∧
      ∀ {k : Nat} (hk : k < 1),
        let c := (Obj.codes (.prod (.atom .boolean) (.atom t)) #v[x])[k]'hk
        laneOK(c.w) ∧ c.n = (#v[x][k]'hk).1 ∧
        c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
        (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)) ∧
      ∀ {k l : Nat} (hk : k < 1) (hl : l < 1),
        ((Obj.codes (.prod (.atom .boolean) (.atom t)) #v[x])[k]'hk).w =
          ((Obj.codes (.prod (.atom .boolean) (.atom t)) #v[x])[l]'hl).w := by
  have hpa : #v[x].map (fun c => (⟨c.1, c.2.1⟩ : Part (.atom .boolean))) = #v[⟨x.1, x.2.1⟩] :=
    Vector.ext fun k hk => by obtain rfl : k = 0 := by omega
                              simp
  have hpb : #v[x].map (fun c => (⟨c.1, c.2.2⟩ : Part (.atom t))) = #v[⟨x.1, x.2.2⟩] :=
    Vector.ext fun k hk => by obtain rfl : k = 0 := by omega
                              simp
  have hwa := fun {k : Nat} (hk : k < 1) => codes_boolean_wf #v[⟨x.1, x.2.1⟩] hk
  refine codes_prod_faithful_wf #v[x] hpa hpb rfl rfl
    ⟨fun hk hl _ _ hi hj => codes_boolean_faithful _ hk hl hi hj,
      fun hk => ⟨Or.inl (hwa hk).2.1, (hwa hk).1, (hwa hk).2.2.1, (hwa hk).2.2.2⟩⟩
    (fun hk hl => by rw [(hwa hk).2.1, (hwa hl).2.1])
    ⟨fun {k l} hk hl _ _ hi hj => by
        obtain rfl : k = 0 := by omega
        obtain rfl : l = 0 := by omega
        exact codes_long_one_faithful ht _ hi hj,
      fun {k} hk => by obtain rfl : k = 0 := by omega
                       exact codes_long_one_wf ht _⟩
    (fun {k l} hk hl => by
      obtain rfl : k = 0 := by omega
      obtain rfl : l = 0 := by omega
      rfl)
    (by simpa using USize.toNat_lt_size x.1)

#print axioms codes_prod_boolean_long_one

end LeetQ.Rel.Alg
