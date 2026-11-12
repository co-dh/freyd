/-
  A product side's joint codes, faithful and well formed, from its two columns'.

  Every index in a statement here carries its bound explicitly (`xs[k]'hk`): left to `get_elem_tactic`,
  the index proofs of this many binders ran Lean out of memory (`std::bad_alloc` at 20 GB) before any tactic.
-/
import LeetQ.Rel.KernelWF.CodesProd

namespace LeetQ.Rel.Alg

open QLean QLean.Dep QLean.Kernel QLean.Verify LeetQ.Rel

/-- **A product side's codes are faithful and well formed, on one lane**, given its two columns' are, one
    lane each, and `pairCode` of the columns laid end to end is (`pairCode_grouped` where it groups); the
    parts' summed count a `USize`. -/
theorem codes_prod_faithful_wf {a b : Obj} {p : Nat} (cs : Vector (Part (.prod a b)) p)
    {pa : Vector (Part a) p} {pb : Vector (Part b) p} {ca cb : Vector Code p}
    (hpa : cs.map (fun c => (⟨c.1, c.2.1⟩ : Part a)) = pa) (hpb : cs.map (fun c => (⟨c.1, c.2.2⟩ : Part b)) = pb)
    (hca : Obj.codes a pa = ca) (hcb : Obj.codes b pb = cb)
    (hfa : (∀ {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (pa[k]'hk).1.toNat)
        (hj : j < (pa[l]'hl).1.toNat),
        Column.idAt (ca[k]'hk).b (ca[k]'hk).w i = Column.idAt (ca[l]'hl).b (ca[l]'hl).w j ↔
          Vals.row (pa[k]'hk).2 ⟨i, hi⟩ = Vals.row (pa[l]'hl).2 ⟨j, hj⟩) ∧
      ∀ {k : Nat} (hk : k < p),
        ((ca[k]'hk).w = 1 ∨ (ca[k]'hk).w = 2 ∨ (ca[k]'hk).w = 4 ∨ (ca[k]'hk).w = 8 ∨ (ca[k]'hk).w = 16 ∨
          (ca[k]'hk).w = 32 ∨ (ca[k]'hk).w = 64) ∧
        (ca[k]'hk).n = (pa[k]'hk).1 ∧ (ca[k]'hk).b.size = ((ca[k]'hk).n.toNat * (ca[k]'hk).w + 7) / 8 ∧
        ((ca[k]'hk).w < 8 → (ca[k]'hk).card < USize.size ∧
          ∀ i < (ca[k]'hk).n.toNat, Column.idAt (ca[k]'hk).b (ca[k]'hk).w i < (ca[k]'hk).card))
    (hla : ∀ {k l : Nat} (hk : k < p) (hl : l < p), (ca[k]'hk).w = (ca[l]'hl).w)
    (hfb : (∀ {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (pb[k]'hk).1.toNat)
        (hj : j < (pb[l]'hl).1.toNat),
        Column.idAt (cb[k]'hk).b (cb[k]'hk).w i = Column.idAt (cb[l]'hl).b (cb[l]'hl).w j ↔
          Vals.row (pb[k]'hk).2 ⟨i, hi⟩ = Vals.row (pb[l]'hl).2 ⟨j, hj⟩) ∧
      ∀ {k : Nat} (hk : k < p),
        ((cb[k]'hk).w = 1 ∨ (cb[k]'hk).w = 2 ∨ (cb[k]'hk).w = 4 ∨ (cb[k]'hk).w = 8 ∨ (cb[k]'hk).w = 16 ∨
          (cb[k]'hk).w = 32 ∨ (cb[k]'hk).w = 64) ∧
        (cb[k]'hk).n = (pb[k]'hk).1 ∧ (cb[k]'hk).b.size = ((cb[k]'hk).n.toNat * (cb[k]'hk).w + 7) / 8 ∧
        ((cb[k]'hk).w < 8 → (cb[k]'hk).card < USize.size ∧
          ∀ i < (cb[k]'hk).n.toNat, Column.idAt (cb[k]'hk).b (cb[k]'hk).w i < (cb[k]'hk).card))
    (hlb : ∀ {k l : Nat} (hk : k < p) (hl : l < p), (cb[k]'hk).w = (cb[l]'hl).w)
    (hN : (cs.toList.map (·.1.toNat)).sum < USize.size)
    (hP : let A := Code.cat ca.toArray
      let B := Code.cat cb.toArray
      let c := (pairCode false A B).1
      ((c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = A.n ∧
        c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
        (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)) ∧
      ∀ i < A.n.toNat, ∀ j < A.n.toNat, (Column.idAt c.b c.w i = Column.idAt c.b c.w j ↔
        Column.idAt A.b A.w i = Column.idAt A.b A.w j ∧ Column.idAt B.b B.w i = Column.idAt B.b B.w j)) :
    ((∀ {k l : Nat} (hk : k < p) (hl : l < p) {i j : Nat} (hi : i < (cs[k]'hk).1.toNat)
        (hj : j < (cs[l]'hl).1.toNat),
        Column.idAt ((Obj.codes (.prod a b) cs)[k]'hk).b ((Obj.codes (.prod a b) cs)[k]'hk).w i =
          Column.idAt ((Obj.codes (.prod a b) cs)[l]'hl).b ((Obj.codes (.prod a b) cs)[l]'hl).w j ↔
        Vals.row (A := .prod a b) (cs[k]'hk).2 ⟨i, hi⟩ = Vals.row (A := .prod a b) (cs[l]'hl).2 ⟨j, hj⟩) ∧
      ∀ {k : Nat} (hk : k < p),
        let c := (Obj.codes (.prod a b) cs)[k]'hk
        (c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = (cs[k]'hk).1 ∧
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
  dsimp only at hP
  obtain ⟨⟨hRw, hRn, hRs, hRid⟩, hRiff⟩ := hP
  -- every claim names a part, so there is one
  have catA := fun hp : 0 < p => cat_parts ca hp hla
    (fun hk => ⟨(hwa hk).1, (hwa hk).2.2.1, fun h => ((hwa hk).2.2.2 h).2⟩) (by rw [hLa]; exact hN)
  have catB := fun hp : 0 < p => cat_parts cb hp hlb
    (fun hk => ⟨(hwb hk).1, (hwb hk).2.2.1, fun h => ((hwb hk).2.2.2 h).2⟩) (by rw [hLb]; exact hN)
  have hs : 0 < p → ((ca.map (·.n)).toList.map (·.toNat)).sum =
      (pairCode false (Code.cat ca.toArray) (Code.cat cb.toArray)).1.n.toNat := fun hp => by
    rw [hLn, hRn, (catA hp).1, hLa]
  have hab : ∀ k, ((cb.toList.take k).map (·.n.toNat)).sum = ((ca.toList.take k).map (·.n.toNat)).sum :=
    fun k => (hO _ k hLb).trans (hO _ k hLa).symm
  refine ⟨⟨fun {k l} hk hl i j hi hj => ?_, fun {k} hk => ?_⟩, fun {k l} hk hl => ?_⟩
  · have hp : 0 < p := by omega
    obtain ⟨hwk, -, -, hck⟩ := cut_get _ (ca.map (·.n)) hRw (hs hp) hk
    obtain ⟨hwl, -, -, hcl⟩ := cut_get _ (ca.map (·.n)) hRw (hs hp) hl
    have hik : i < (ca[k]'hk).n.toNat := by rw [hna k hk]; exact hi
    have hjl : j < (ca[l]'hl).n.toNat := by rw [hna l hl]; exact hj
    rw [hwk, hwl, hck i (by rw [Vector.getElem_map]; exact hik), hcl j (by rw [Vector.getElem_map]; exact hjl),
      hOn, hOn,
      hRiff _ (by rw [(catA hp).1, hLa]; exact hlt k hk i hi) _ (by rw [(catA hp).1, hLa]; exact hlt l hl j hj),
      ← hO ca.toList k hLa, ← hO ca.toList l hLa, (catA hp).2 k hk i hik, (catA hp).2 l hl j hjl, ← hab k, ← hab l,
      (catB hp).2 k hk i (by rw [hnb k hk]; exact hi), (catB hp).2 l hl j (by rw [hnb l hl]; exact hj),
      hfa hk hl (by rw [hpa' k hk]; exact hi) (by rw [hpa' l hl]; exact hj),
      hfb hk hl (by rw [hpb' k hk]; exact hi) (by rw [hpb' l hl]; exact hj),
      row_part_congr (hpa' k hk) _ hi, row_part_congr (hpa' l hl) _ hj,
      row_part_congr (hpb' k hk) _ hi, row_part_congr (hpb' l hl) _ hj]
    exact (iff_of_eq (Prod.mk.injEq _ _ _ _)).symm
  · have hp : 0 < p := by omega
    obtain ⟨hwk, hnk, hck, hik⟩ := cut_get _ (ca.map (·.n)) hRw (hs hp) hk
    have hzk := cut_size _ (ca.map (·.n)) hRw (hs hp) hRs hk
    dsimp only
    rw [hzk, hwk, hnk, hck]
    refine ⟨hRw, by rw [Vector.getElem_map, hna k hk], rfl, fun h8 => ⟨(hRid h8).1, fun i hi => ?_⟩⟩
    rw [hik i hi]
    refine (hRid h8).2 _ ?_
    rw [← hs hp, hLn, hOn]
    exact hlt k hk i (by rw [Vector.getElem_map, hna k hk] at hi; exact hi)
  · have hp : 0 < p := by omega
    rw [(cut_get _ (ca.map (·.n)) hRw (hs hp) hk).1, (cut_get _ (ca.map (·.n)) hRw (hs hp) hl).1]

#print axioms codes_prod_faithful_wf

end LeetQ.Rel.Alg
