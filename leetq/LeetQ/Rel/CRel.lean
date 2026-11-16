/-
  Capacity checked at run time, correctness proved: an op's twin `compC`/`interC`/`unionC` answers its relation
  and a bit, the bit deciding every count bound the op's read-back theorem takes, so `rep_compC`/`rep_interC`/
  `rep_unionC` hold under that one bit. `CRel` carries the bit along a program, each op `&&`-ing its inputs' bits
  with its own.
-/
import LeetQ.Rel.KernelWF.CodesAll
import LeetQ.Rel.KernelWF.RazeFoR
import LeetQ.Rel.KernelWF.AscSpec
import LeetQ.Rel.KernelWF.NubSpec
import LeetQ.Rel.OkBit
import LeetQ.Run.CRelDef

namespace LeetQ.Rel

namespace Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet
open CompN OpsN

variable {A B C : Obj}

/-- A `fitsN` bit at `N` fits any `N` picks: `pickFits_of_fitsN` at the lists a twin reads, for `okbit`. -/
@[okbit] theorem pickFits_range (X : Obj) {n : USize} (x : Vals X n) {N : Nat} (h : Vals.fitsN X x N = true) :
    Vals.PickFits X x (List.range N) := pickFits_of_fitsN X x N h _ (by simp)

@[okbit] theorem pickFits_map_range (X : Obj) {n : USize} (x : Vals X n) {N : Nat} (f : Nat → Nat)
    (h : Vals.fitsN X x N = true) : Vals.PickFits X x ((List.range N).map f) := pickFits_of_fitsN X x N h _ (by simp)

/-- A one-part codes bit gives the one-part code faithful and well formed, in `oneOK`'s form. -/
theorem oneOK_of_codesC (X : Obj) {n : USize} (x : Vals X n) (hb : (X.codesC #v[⟨n, x⟩]).2 = true) :
    oneOK(X, n, x) := by
  have hK := (codes_faithful_wf X _ (Obj.codesC_fits X _ hb)).1
  exact ⟨fun hi hj => hK.1 (k := 0) (l := 0) Nat.zero_lt_one Nat.zero_lt_one hi hj, hK.2 (k := 0) Nat.zero_lt_one⟩

/-- Two parts' codes, mapped: the form `pairs_eq_codes` leaves at a pair. -/
theorem map_pair {α β : Type} (f : α → β) (a b : α) : #v[a, b].map f = #v[f a, f b] := by simp

attribute [okbit] Bool.and_eq_true decide_eq_true_eq Obj.codesC_fits and_self and_true true_and

/-- **`compC`'s bit is `rep_comp`'s premises**: the codes' bit gives the middle side's codes fitting (`codesC_fits`,
    whence `rep_comp`'s `hc` by `codes_faithful_wf`), the decided bounds its `hrn`, `hM`, and the picks' bits, read
    at the join's rows (`join_rows`), its `hA`, `hC` (`pickC_fits`). -/
theorem compC_ok (R : Rel A B) (S : Rel B C) (hb : (compC R S).2 = true) :
    Obj.CodesFit B jcs ∧ S.n.toNat < 2 ^ 63 ∧ R.n.toNat * S.n.toNat < min (2 ^ 63) USize.size ∧
      Vals.PickFits A R.key ((jpairs).map Prod.fst) ∧ Vals.PickFits C S.val ((jpairs).map Prod.snd) := by
  simp only [compC, okbit] at hb
  obtain ⟨⟨⟨hcb, hrn⟩, hM⟩, hp⟩ := hb
  have hcf' := Obj.codesC_fits B _ hcb
  have hc := (codes_faithful_wf B _ hcf').1
  obtain ⟨hlw, hln, hls, -⟩ := hc.2 (k := 0) (by decide)
  obtain ⟨hrw, hrn', hrs, hrc⟩ := hc.2 (k := 1) (by decide)
  replace hln : (jc[0]'Nat.zero_lt_two).n = R.n := hln
  replace hrn' : (jc[1]'Nat.one_lt_two).n = S.n := hrn'
  have hcf : (B.codesC jcs).1 = jc := by cases B <;> rfl
  -- `join_rows` on the codes `compC` joins, named as `compC` names them: a defeq check through them evaluates `join`
  rw [← hcf] at hlw hls hrw hrs hrc hln hrn'
  obtain ⟨-, hZ⟩ := join_rows _ _ hlw hls hrw hrs hrc (by rw [hrn']; exact hrn) (by rw [hln, hrn']; exact hM)
  unfold joinC longCount need at hp
  dsimp only [keyPart, valPart] at hp
  split at hp
  · rename_i hlt
    simp only [Bool.and_eq_true] at hp
    have e := hZ _ (USize.toNat_ofNat_of_lt' hlt).symm
    have hfA := Vals.pickC_fits A R.key _ _ _ hp.1
    have hfC := Vals.pickC_fits C S.val _ _ _ hp.2
    rw [hln, hrn'] at e
    rw [hcf] at e hfA hfC
    have hA : Vals.PickFits A R.key ((jpairs).map Prod.fst) := by rw [e, List.map_map]; exact hfA
    have hC : Vals.PickFits C S.val ((jpairs).map Prod.snd) := by rw [e, List.map_map]; exact hfC
    exact ⟨hcf', hrn, hM, hA, hC⟩
  · exact absurd hp Bool.false_ne_true

/-- **`rep (R ≫ S) = rep R ≫ rep S` under `compC`'s bit**: `rep_comp` at `compC_ok`'s premises. -/
theorem rep_compC (R : Rel A B) (S : Rel B C) (hb : (compC R S).2 = true) :
    rep (compC R S).1 = rep R ≫ rep S :=
  let ⟨hcf, hrn, hM, hA, hC⟩ := compC_ok R S hb; rep_comp R S (codes_faithful_wf B _ hcf).1 hrn hM hA hC

#print axioms rep_compC

/-- **`rep (R ∩ S) = rep R ∩ rep S` under `interC`'s bit**: the product codes' bit gives `rep_inter`'s `hc`
    (`codesC_fits`, `codes_faithful_wf`, `pairs_eq_codes`), the `fitsN` bits its `hk`, `hv` (`pickFits_of_fitsN`). -/
theorem rep_interC (R S : Rel A B) (hb : (interC R S).2 = true) : rep (interC R S).1 = rep R ∩ rep S := by
  simp only [interC, okbit] at hb
  exact rep_inter R S (by rw [pairs_eq_codes, map_pair]; exact (codes_faithful_wf _ _ (Obj.codesC_fits _ _ hb.1.1)).1)
    (by simp only [okbit, hb]) (by simp only [okbit, hb])

#print axioms rep_interC

/-- **`rep (R ∪ S) = rep R ∪ rep S` under `unionC`'s bit**: `need`'s guard is `rep_union`'s `hN`, the razes' bits
    its `hA`, `hB` (`razeC_fits`, `raze_row`), the codes' bits its `hK`, `hV` (`codesC_fits`, `codes_faithful_wf`),
    the `fitsN` bits its `hk`, `hv` (`pickFits_of_fitsN`). -/
theorem rep_unionC (R S : Rel A B) (hb : (unionC R S).2 = true) : rep (unionC R S).1 = rep R ∪ rep S := by
  unfold unionC need at hb
  split at hb
  · rename_i hN
    simp only [okbit] at hb
    obtain ⟨⟨⟨⟨⟨hka, hvb⟩, hkc⟩, hvc⟩, hkf⟩, hvf⟩ := hb
    -- a raze twin's `.1` is `raze` at each constructor of the side
    have hr : ∀ (X : Obj) (cs : Array (Part X)) h, (X.razeC cs h).1 = X.raze cs h := by
      intro X; cases X <;> intros <;> rfl
    simp only [hr] at hkc hvc hkf hvf
    exact rep_union R S hN (raze_row A R.key S.key (Obj.razeC_fits A _ _ _ rfl _ hka) _)
      (raze_row B R.val S.val (Obj.razeC_fits B _ _ _ rfl _ hvb) _)
      (oneOK_of_codesC A _ hkc) (oneOK_of_codesC B _ hvc) (pickFits_range A _ hkf) (pickFits_range B _ hvf)
  · exact absurd hb Bool.false_ne_true

#print axioms rep_unionC

/-- **`rep (nub R) = rep R` under `nubC`'s bit**: the codes' bits give `rep_nub`'s `hK`, `hV` (`oneOK_of_codesC`),
    the `fitsN` bits its picks. -/
theorem rep_nubC {k v : Obj} (R : Rel k v) (hb : (nubC R).2 = true) : rep (nubC R).1 = rep R := by
  simp only [nubC, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨hK, hV⟩, hk⟩, hv⟩ := hb
  rw [nubC_fst]
  exact rep_nub R (oneOK_of_codesC k R.key hK) (oneOK_of_codesC v R.val hV) (pickFits_of_fitsN k R.key _ hk _ (by simp))
    (pickFits_of_fitsN v R.val _ hv _ (by simp))

/-! ## Canonical form: rows strictly ascending by `Obj.lt` on `(key, val)` -/

/-- `A`'s key tells its elements apart: no `.general` atom and no float, whose keys merge NaNs and `±0`. -/
def _root_.LeetQ.Rel.Obj.KeyInj (A : Obj) : Prop := ∀ x y : A.El, A.key x = A.key y → x = y

/-- `R`'s rows strictly ascending by `Obj.lt` on `(key, val)`: sorted, and no row twice. -/
def _root_.LeetQ.Rel.Rel.Canon {k v : Obj} (R : Rel k v) : Prop := R.toList.Pairwise (Obj.prod k v).lt

theorem keyInj_prod {a b : Obj} (ha : a.KeyInj) (hb : b.KeyInj) : (Obj.prod a b).KeyInj := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  change a.key x ++ b.key y = a.key x' ++ b.key y' at h
  have e := Obj.key_prefix a x x' _ _ h
  rw [e, List.append_cancel_left_eq] at h
  rw [ha x x' e, hb y y' h]

/-- Two lists strictly ascending in one strict order, with the same members, are one list. -/
theorem eq_of_pairwise {α : Type} {r : α → α → Prop} (irr : ∀ a, ¬ r a a) (tr : ∀ {a b c}, r a b → r b c → r a c) :
    ∀ {l m : List α}, l.Pairwise r → m.Pairwise r → (∀ x, x ∈ l ↔ x ∈ m) → l = m
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 List.mem_cons_self) List.not_mem_nil
  | a :: _, [], _, _, h => absurd ((h a).1 List.mem_cons_self) List.not_mem_nil
  | a :: l, b :: m, hl, hm, h => by
    rw [List.pairwise_cons] at hl hm
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 List.mem_cons_self) with e | ha
      · exact e
      rcases List.mem_cons.1 ((h b).2 List.mem_cons_self) with e | hb
      · exact e.symm
      exact absurd (tr (hm.1 a ha) (hl.1 b hb)) (irr b)
    subst hab
    have hlm : ∀ x, x ∈ l ↔ x ∈ m := fun x => by
      constructor <;> intro hx
      · rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with e | hx'
        · subst e; exact absurd (hl.1 _ hx) (irr _)
        · exact hx'
      · rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with e | hx'
        · subst e; exact absurd (hm.1 _ hx) (irr _)
        · exact hx'
    rw [eq_of_pairwise irr tr hl.2 hm.2 hlm]

/-- **Canonical tables of one `rep` are one table**: the data a canonical relation holds is fixed by what it denotes. -/
theorem canon_eq {k v : Obj} {R S : Rel k v} (hR : R.Canon) (hS : S.Canon) (h : rep R = rep S) :
    R.toList = S.toList :=
  eq_of_pairwise (Obj.lt_irrefl _) (Obj.lt_trans _) hR hS fun ⟨x, y⟩ => by
    rw [← Rel.holds_iff_mem_toList, ← Rel.holds_iff_mem_toList, ← rep_apply, ← rep_apply, h]

/-- Row `t` of `R` as a pair, the default pair past its count: what `rows_spec` reads a pick as. -/
def rowAt {k v : Obj} (R : Rel k v) (t : Nat) : k.El × v.El :=
  if h : t < R.n.toNat then (R.key.row ⟨t, h⟩, R.val.row ⟨t, h⟩) else (k.dflt, v.dflt)

theorem toList_rowAt {k v : Obj} (R : Rel k v) : R.toList = (List.range R.n.toNat).map (rowAt R) :=
  List.ext_getElem (by simp [Rel.toList]) fun q h1 h2 => by
    simp only [Rel.toList, List.getElem_ofFn, List.getElem_map, List.getElem_range, rowAt]
    rw [dif_pos (by simpa [Rel.toList] using h1)]

/-- **`rows R i` as a list is `R`'s rows at the positions `i` names** (`rows_spec`). -/
theorem rows_toList {k v : Obj} (R : Rel k v) (i : ByteArray) (hl : len i < USize.size)
    (hk : Vals.PickFits k R.key (ids i)) (hv : Vals.PickFits v R.val (ids i)) :
    (R.rows i).toList = (ids i).map (rowAt R) := by
  obtain ⟨hn, hrow⟩ := rows_spec R i hl hk hv
  refine List.ext_getElem (by simp [Rel.toList, hn, len_eq_ids]) fun q h1 h2 => ?_
  simp only [Rel.toList, List.getElem_ofFn, List.getElem_map, ids_getElem, rowAt]
  exact hrow q _

/-- `canonC`'s bit, taken apart: the sort's, the two `fitsN` bits, `nubC`'s. -/
theorem canonC_bits {k v : Obj} (R : Rel k v) (hb : (canonC R).2 = true) :
    ((Obj.prod k v).sortByC (pairPart R).2 (tilLongs R.n)).2 = true ∧ Vals.fitsN k R.key R.n.toNat = true ∧
      Vals.fitsN v R.val R.n.toNat = true ∧
      (nubC (R.rows ((Obj.prod k v).sortByC (pairPart R).2 (tilLongs R.n)).1)).2 = true := by
  simp only [canonC, Bool.and_eq_true] at hb; exact ⟨hb.1.1.1, hb.1.1.2, hb.1.2, hb.2⟩

/-- The sorted rows `canonC` reads: `R`'s rows in the sort's order, a permutation of them. -/
theorem canonC_sorted {k v : Obj} (R : Rel k v) (hb : (canonC R).2 = true) :
    let s := ((Obj.prod k v).sortByC (pairPart R).2 (tilLongs R.n)).1
    (ids s).Perm (List.range R.n.toNat) ∧ (R.rows s).toList = (ids s).map (rowAt R) := by
  obtain ⟨hs, hfk, hfv, -⟩ := canonC_bits R hb
  have hl : len (tilLongs R.n) < USize.size := by rw [len_tilLongs]; exact R.n.toNat_lt_size
  have hp := sortByC_perm (Obj.prod k v) (pairPart R).2 (tilLongs R.n) hs hl
    (fun t ht => by rw [ids_tilLongs] at ht; exact List.mem_range.1 ht)
  rw [ids_tilLongs] at hp
  have hlen : (ids ((Obj.prod k v).sortByC (pairPart R).2 (tilLongs R.n)).1).length ≤ R.n.toNat := by
    rw [hp.length_eq, List.length_range]; exact Nat.le_refl _
  refine ⟨hp, rows_toList R _ ?_ (pickFits_of_fitsN k R.key _ hfk _ hlen) (pickFits_of_fitsN v R.val _ hfv _ hlen)⟩
  rw [len_eq_ids]; exact Nat.lt_of_le_of_lt hlen R.n.toNat_lt_size

/-- **`rep (canon R) = rep R` under `canonC`'s bit**: a permutation of the rows, then `nub`. -/
theorem rep_canonC {k v : Obj} (R : Rel k v) (hb : (canonC R).2 = true) : rep (canonC R).1 = rep R := by
  obtain ⟨hp, hS⟩ := canonC_sorted R hb
  rw [show (canonC R).1 = (nubC (R.rows _)).1 from rfl, rep_nubC _ (canonC_bits R hb).2.2.2]
  refine hom_ext fun x y => ?_
  rw [rep_apply, rep_apply, Rel.holds_iff_mem_toList, Rel.holds_iff_mem_toList, hS, toList_rowAt]
  exact (hp.map _).mem_iff

/-- **`canonC`'s answer is canonical** on a side whose atoms the kernels order (`Ordered`) and whose key tells
    elements apart (`KeyInj`): sorted by `sortBy_asc`, the first of each run of equal rows kept by `nub_mem`. -/
theorem canon_canonC {k v : Obj} (R : Rel k v) (hb : (canonC R).2 = true) (ho : (Obj.prod k v).Ordered)
    (hi : (Obj.prod k v).KeyInj) : (canonC R).1.Canon := by
  obtain ⟨-, hfk, hfv, hN⟩ := canonC_bits R hb
  obtain ⟨hp, hS⟩ := canonC_sorted R hb
  generalize hs : ((Obj.prod k v).sortByC (pairPart R).2 (tilLongs R.n)).1 = s at hp hS hN
  have hl : len (tilLongs R.n) < USize.size := by rw [len_tilLongs]; exact R.n.toNat_lt_size
  have hrk := pickFits_range k R.key hfk; have hrv := pickFits_range v R.val hfv
  -- the sorted rows ascend: no later row before an earlier one
  have hasc := sortBy_asc (sortsAsc_all _ ho) (pairPart R).2 (small_of_pickFits (Obj.prod k v) _ _ ⟨hrk, hrv⟩)
    (tilLongs R.n) hl (fun t ht => by rw [ids_tilLongs] at ht; exact List.mem_range.1 ht)
  rw [show (Obj.prod k v).sortBy (pairPart R).2 (tilLongs R.n) = s from hs] at hasc
  have hsort : (R.rows s).toList.Pairwise fun a b => ¬ (Obj.prod k v).lt b a := by
    rw [hS, List.pairwise_map]
    refine hasc.imp_of_mem fun {i j} hi' hj' h => ?_
    have hi' := List.mem_range.1 (hp.mem_iff.1 hi'); have hj' := List.mem_range.1 (hp.mem_iff.1 hj')
    simp only [rowAt, dif_pos hi', dif_pos hj']; exact h hi' hj'
  -- `nub` of the sorted rows: its rows at the first positions, ascending positions, no row twice
  simp only [nubC, Bool.and_eq_true] at hN
  obtain ⟨⟨⟨hK, hV⟩, hk⟩, hv⟩ := hN
  have hK := oneOK_of_codesC k _ hK; have hV := oneOK_of_codesC v _ hV
  have hk := pickFits_range k _ hk; have hv := pickFits_range v _ hv
  generalize hT : R.rows s = T at hsort hK hV hk hv
  rw [show (canonC R).1 = (nubC (R.rows s)).1 by rw [← hs]; rfl, hT, nubC_fst]
  have hsub : (ids (tuples.tupleIds (k.codes #v[⟨T.n, T.key⟩])[0] #[(v.codes #v[⟨T.n, T.val⟩])[0]]).2).Pairwise
      (· < ·) := by rw [nub_ids T hK hV]; exact (List.pairwise_lt_range).filter _
  have hlenN := (nub_row T hK hV hk hv).1
  have hlN : len (tuples.tupleIds (k.codes #v[⟨T.n, T.key⟩])[0] #[(v.codes #v[⟨T.n, T.val⟩])[0]]).2 < USize.size := by
    rw [len_eq_ids, ← hlenN]; exact T.nub.n.toNat_lt_size
  have hmemN := fun p => nub_mem T hK hV (p := p)
  have hlenS : ∀ p ∈ ids (tuples.tupleIds (k.codes #v[⟨T.n, T.key⟩])[0] #[(v.codes #v[⟨T.n, T.val⟩])[0]]).2,
      p < T.n.toNat := fun p hp' => ((hmemN p).1 hp').1
  have hle : (ids (tuples.tupleIds (k.codes #v[⟨T.n, T.key⟩])[0] #[(v.codes #v[⟨T.n, T.val⟩])[0]]).2).Sublist
      (List.range T.n.toNat) := by
    rw [nub_ids T hK hV]; exact List.filter_sublist
  unfold Rel.Canon
  rw [show T.nub = T.rows _ from rfl, rows_toList T _ hlN (pickFits_sublist hle hk) (pickFits_sublist hle hv),
    List.pairwise_map]
  rw [toList_rowAt, List.pairwise_map] at hsort
  refine hsub.imp_of_mem fun {p p'} hp' hp'' hlt => ?_
  have h1 := hlenS p hp'; have h2 := hlenS p' hp''
  have hna : ¬ (Obj.prod k v).lt (rowAt T p') (rowAt T p) := by
    have h := List.pairwise_iff_getElem.1 hsort p p' (by simpa using h1) (by simpa using h2) hlt
    simp only [List.getElem_range] at h; exact h
  have hne : rowAt T p ≠ rowAt T p' := by
    obtain ⟨_, hq⟩ := (hmemN p').1 hp''
    simp only [rowAt, dif_pos h1, dif_pos h2, ne_eq, Prod.mk.injEq]; exact hq p hlt
  rcases (Obj.prod k v).lt_trichotomy (rowAt T p) (rowAt T p') with h | h | h
  · exact h
  · exact absurd (hi _ _ h) hne
  · exact absurd h hna

#print axioms canon_canonC
#print axioms rep_canonC

end Rep

namespace CRel

open QLean QLean.Kernel LeetQ.Rel.Alg Freyd Freyd.Alg.RelSet LeetQ.Rel.Rep

variable {A B C : Obj}

/-- A guarded op's bit: the inputs' bits and the op's own. -/
@[simp] theorem guard_ok (b : Bool) (k : Unit → CRel A B) : (guard b k).ok = (b && (k ()).ok) := by cases b <;> rfl

/-- Where a bit `p` read off the result is set, the guard ran its op: `default`'s bit is false. -/
theorem guard_eq {α : Type} [Inhabited α] {b : Bool} {k : Unit → α} (p : α → Bool) (h : p (guard b k) = true)
    (hd : p default = false := by rfl) : guard b k = k () := by
  cases b
  · exact absurd (hd ▸ h) Bool.false_ne_true
  · rfl

/-- `ofC`'s bit: the twin's and `canonC`'s. -/
theorem ofC_ok {r : Rel A B × Bool} (hb : (ofC r).ok = true) : r.2 = true ∧ (canonC r.1).2 = true := by
  simpa only [ofC, Bool.and_eq_true] using hb

theorem rep_ofC {r : Rel A B × Bool} (hb : (ofC r).ok = true) : rep (ofC r).rel = rep r.1 :=
  rep_canonC r.1 (ofC_ok hb).2

/-- **Every op through `ofC` answers a canonical table** where it ran within capacity. -/
theorem canon_ofC {r : Rel A B × Bool} (hb : (ofC r).ok = true) (ho : (Obj.prod A B).Ordered)
    (hi : (Obj.prod A B).KeyInj) : (ofC r).rel.Canon :=
  canon_canonC r.1 (ofC_ok hb).2 ho hi

/-- A guarded op's inputs ran ok where it did. -/
theorem guard_ok_left {b : Bool} {k : Unit → CRel A B} (h : (guard b k).ok = true) : b = true := by
  cases b
  · exact absurd h Bool.false_ne_true
  · rfl

theorem rep_comp (R : CRel A B) (S : CRel B C) (hb : (R.comp S).ok = true) :
    rep (R.comp S).rel = rep R.rel ≫ rep S.rel := by
  have e : R.comp S = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_compC R.rel S.rel hb

theorem rep_inter (R S : CRel A B) (hb : (R.inter S).ok = true) : rep (R.inter S).rel = rep R.rel ∩ rep S.rel := by
  have e : R.inter S = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_interC R.rel S.rel hb

theorem rep_union (R S : CRel A B) (hb : (R.union S).ok = true) : rep (R.union S).rel = rep R.rel ∪ rep S.rel := by
  have e : R.union S = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_unionC R.rel S.rel hb

theorem canon_comp (R : CRel A B) (S : CRel B C) (hb : (R.comp S).ok = true) (ho : (Obj.prod A C).Ordered)
    (hi : (Obj.prod A C).KeyInj) : (R.comp S).rel.Canon := by
  have e : R.comp S = _ := guard_eq ok hb; rw [e] at hb ⊢; exact canon_ofC hb ho hi

theorem canon_inter (R S : CRel A B) (hb : (R.inter S).ok = true) (ho : (Obj.prod A B).Ordered)
    (hi : (Obj.prod A B).KeyInj) : (R.inter S).rel.Canon := by
  have e : R.inter S = _ := guard_eq ok hb; rw [e] at hb ⊢; exact canon_ofC hb ho hi

theorem canon_union (R S : CRel A B) (hb : (R.union S).ok = true) (ho : (Obj.prod A B).Ordered)
    (hi : (Obj.prod A B).KeyInj) : (R.union S).rel.Canon := by
  have e : R.union S = _ := guard_eq ok hb; rw [e] at hb ⊢; exact canon_ofC hb ho hi

/-- **`comp` is associative on data**: both bracketings answer the same rows in the same order. -/
theorem comp_assoc {D : Obj} (R : CRel A B) (S : CRel B C) (T : CRel C D) (h₁ : ((R.comp S).comp T).ok = true)
    (h₂ : (R.comp (S.comp T)).ok = true) (ho : (Obj.prod A D).Ordered) (hi : (Obj.prod A D).KeyInj) :
    ((R.comp S).comp T).rel.toList = (R.comp (S.comp T)).rel.toList := by
  have hl := guard_ok_left h₁; have hr := guard_ok_left h₂; simp only [Bool.and_eq_true] at hl hr
  refine canon_eq (canon_comp _ _ h₁ ho hi) (canon_comp _ _ h₂ ho hi) ?_
  rw [rep_comp _ _ h₁, rep_comp _ _ hl.1, rep_comp _ _ h₂, rep_comp _ _ hr.2, Cat.assoc]

/-- **`R ∩ R` is `R` on data**, for a canonical `R`. -/
theorem inter_self (R : CRel A B) (hb : (R.inter R).ok = true) (hR : R.rel.Canon) (ho : (Obj.prod A B).Ordered)
    (hi : (Obj.prod A B).KeyInj) : (R.inter R).rel.toList = R.rel.toList :=
  canon_eq (canon_inter _ _ hb ho hi) hR (by rw [rep_inter _ _ hb, Freyd.Alg.Allegory.inter_idem])

/-- **`R ∪ R` is `R` on data**, for a canonical `R`. -/
theorem union_self (R : CRel A B) (hb : (R.union R).ok = true) (hR : R.rel.Canon) (ho : (Obj.prod A B).Ordered)
    (hi : (Obj.prod A B).KeyInj) : (R.union R).rel.toList = R.rel.toList :=
  canon_eq (canon_union _ _ hb ho hi) hR (by rw [rep_union _ _ hb, Freyd.Alg.DistributiveAllegory.union_idem])

end CRel

end LeetQ.Rel
