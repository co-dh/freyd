/-
  `rep` of the second group of `Alg` ops: each executable op read in `Rel(Set)`, as `RepOps` does the first.
-/
import LeetQ.Rel.RepOps

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF
open Freyd Freyd.Alg Freyd.Alg.RelSet

variable {A B : Obj}

open OpsN

/-- Two boolean parts' codes are faithful and well formed: the codes are the bits (`codes_boolean_faithful`/`_wf`). -/
theorem codesOK_boolean (ps : Vector (Part (.atom .boolean)) 2) : codesOK(Obj.codes (.atom .boolean) ps, ps) :=
  ⟨fun hk hl _ _ hi hj => codes_boolean_faithful ps hk hl hi hj, fun hk =>
    have h := codes_boolean_wf ps hk
    ⟨Or.inl h.2.1, h.1, h.2.2.1, h.2.2.2⟩⟩

/-! ## `antiJoin`: the rows of `R` whose value is no value of `T` -/

section AntiJoin

open QLean.Verify

-- the values of `R` and of `T` as parts of `B`, their joint codes, and the rows `anti` keeps, as `antiJoin` names them
set_option hygiene false in
local notation "avp(" B ", " R ", " T ")" =>
  (#v[⟨Rel.n R, Rel.val R⟩, ⟨Rel.n T, Rel.val T⟩] : Vector (Part B) 2)
set_option hygiene false in
local notation "avc(" B ", " R ", " T ")" => Obj.codes B avp(B, R, T)
set_option hygiene false in
local notation "amiss(" B ", " R ", " T ")" =>
  anti ((avc(B, R, T))[0]'Nat.zero_lt_two) ((avc(B, R, T))[1]'Nat.one_lt_two)

/-- Row `i` of `R` is marked by `member` on the joint value codes exactly when its value is a value of `T`. -/
theorem vals_member (R : Rel A B) (T : Rel B B) (hc : codesOK(avc(B, R, T), avp(B, R, T))) {i : Nat}
    (hi : i < R.n.toNat) :
    Column.bitAt (((avc(B, R, T))[0]'Nat.zero_lt_two).member ((avc(B, R, T))[1]'Nat.one_lt_two)) i = true ↔
      ∃ j, T.val.row j = R.val.row ⟨i, hi⟩ := by
  obtain ⟨hF, hW⟩ := hc
  obtain ⟨hw0, hn0, hs0, -⟩ := hW (k := 0) (by decide)
  obtain ⟨hw1, hn1, hs1, -⟩ := hW (k := 1) (by decide)
  rw [member_bit _ _ hw0 hw1 hs0 hs1 (by rw [hn0]; exact hi)]
  constructor
  · rintro ⟨j, hj, he⟩
    have hj' : j < T.n.toNat := by rw [hn1] at hj; exact hj
    exact ⟨⟨j, hj'⟩, (hF (k := 1) (l := 0) (by decide) (by decide) hj' hi).1 he⟩
  · rintro ⟨j, h⟩
    exact ⟨j.1, by rw [hn1]; exact j.2, (hF (k := 1) (l := 0) (by decide) (by decide) j.2 hi).2 h⟩

/-- **`rep (antiJoin R T) = rep R ≫ ¬ran(rep T)`**, the coreflexive on the values no pair of `T` reaches: `anti` keeps
    the rows of `R` whose value is no value of `T` (`anti_ids`, `vals_member`), read back by `rows_keep`.
    Hypotheses: the joint value codes faithful and well formed (`hc`), `R`'s columns picking back at the kept rows. -/
theorem rep_antiJoin (R : Rel A B) (T : Rel B B) (hc : codesOK(avc(B, R, T), avp(B, R, T)))
    (hk : Vals.PickFits A R.key (ids (amiss(B, R, T)))) (hv : Vals.PickFits B R.val (ids (amiss(B, R, T)))) :
    rep (antiJoin R T) = rep R ≫ corefl (A := (⟨B.El⟩ : RelSet.{0})) fun b => ¬ ∃ y, rep T y b :=
  hom_ext fun a b => by
    obtain ⟨hw0, hn0, hs0, -⟩ := hc.2 (k := 0) (by decide)
    obtain ⟨hw1, -, hs1, -⟩ := hc.2 (k := 1) (by decide)
    have hI := (anti_ids _ _ hw0 hw1 hs0 hs1).1
    replace hn0 : ((avc(B, R, T))[0]'Nat.zero_lt_two).n = R.n := hn0
    rw [hn0] at hI
    show (R.rows (amiss(B, R, T))).Holds a b ↔ ∃ y, R.Holds a y ∧ y = b ∧ ¬ ∃ x, T.Holds x y
    rw [rows_keep R _ _ hI hk hv]
    have hnot : ∀ x : Bool, (!x) = true ↔ ¬ x = true := by decide
    constructor
    · rintro ⟨i, hia, hib, hbit⟩
      exact ⟨b, ⟨i, hia, hib⟩, rfl, fun ⟨_, j, _, hjb⟩ =>
        (hnot _).1 hbit ((vals_member R T hc i.2).2 ⟨j, hjb.trans hib.symm⟩)⟩
    · rintro ⟨y, ⟨i, hia, hiy⟩, rfl, hT⟩
      refine ⟨i, hia, hiy, (hnot _).2 fun hbit => hT ?_⟩
      obtain ⟨j, hj⟩ := (vals_member R T hc i.2).1 hbit
      exact ⟨T.key.row j, j, rfl, hj.trans hiy⟩

/-- `rep_antiJoin` at atom sides: the kept rows are rows of `R` (`anti_ids`), so both columns fit outright. -/
theorem rep_antiJoin_atoms {t t' : QAtomicType} (R : Rel (.atom t) (.atom t')) (T : Rel (.atom t') (.atom t'))
    (hc : codesOK(avc(.atom t', R, T), avp(.atom t', R, T))) :
    rep (antiJoin R T) = rep R ≫ corefl (A := (⟨(Obj.atom t').El⟩ : RelSet.{0})) fun b => ¬ ∃ y, rep T y b := by
  obtain ⟨hw0, hn0, hs0, -⟩ := hc.2 (k := 0) (by decide)
  obtain ⟨hw1, -, hs1, -⟩ := hc.2 (k := 1) (by decide)
  have hlt : ∀ f ∈ ids (amiss(.atom t', R, T)), f < R.n.toNat := fun f hf =>
    hn0 ▸ ((anti_ids _ _ hw0 hw1 hs0 hs1).2.2 f).1 hf |>.1
  exact rep_antiJoin R T hc (pickFits_atom _ hlt) (pickFits_atom _ hlt)

/-- `rep_antiJoin` with boolean values: the value codes are the bits (`codes_boolean_faithful`/`_wf`), no
    hypothesis left. -/
theorem rep_antiJoin_boolean {t : QAtomicType} (R : Rel (.atom t) (.atom .boolean))
    (T : Rel (.atom .boolean) (.atom .boolean)) :
    rep (antiJoin R T) =
      rep R ≫ corefl (A := (⟨(Obj.atom .boolean).El⟩ : RelSet.{0})) fun b => ¬ ∃ y, rep T y b :=
  rep_antiJoin_atoms R T (codesOK_boolean _)

end AntiJoin

/-! ## `entire`, `surjective`: `idU U ⊑ dom R` -/

section Entire

open QLean.Verify

-- the one-part code `distinctCorefl` groups, and `rep_dom`'s hypothesis on it
set_option hygiene false in
local notation "c1(" X ", " n ", " x ")" => (Obj.codes X (#v[⟨n, x⟩] : Vector (Part X) 1))[0]'Nat.zero_lt_one
set_option hygiene false in
local notation "oneOK(" X ", " n ", " x ")" => ((∀ {i j : Nat} (hi : i < USize.toNat n) (hj : j < USize.toNat n),
    Column.idAt (c1(X, n, x)).b (c1(X, n, x)).w i = Column.idAt (c1(X, n, x)).b (c1(X, n, x)).w j ↔
      Vals.row x ⟨i, hi⟩ = Vals.row x ⟨j, hj⟩) ∧
  (let c := c1(X, n, x)
   (c.w = 1 ∨ c.w = 2 ∨ c.w = 4 ∨ c.w = 8 ∨ c.w = 16 ∨ c.w = 32 ∨ c.w = 64) ∧ c.n = n ∧
    c.b.size = (c.n.toNat * c.w + 7) / 8 ∧
    (c.w < 8 → c.card < USize.size ∧ ∀ i < c.n.toNat, Column.idAt c.b c.w i < c.card)))

/-- `U? ⊑ dom S`, both coreflexives: every element `U` lists has an image under `S`. -/
theorem corefl_le_dom {X Y : RelSet.{0}} (P : X.carrier → Prop) (S : X ⟶ Y) :
    corefl P ⊑ corefl (fun a => ∃ b, S a b) ↔ ∀ a, P a → ∃ b, S a b := by
  rw [le_iff]
  exact ⟨fun h a ha => (h a a ⟨rfl, ha⟩).2, fun h a b ⟨e, ha⟩ => ⟨e, h a ha⟩⟩

/-- **`entire R U = true ↔ U? ⊑ dom (rep R)`**: every element `U` lists has an image under `rep R`. `entire` is
    `idU U ⊑ dom R` (`rep_le`, `rep_idU`, `rep_dom`). Hypotheses: `rep_le`'s joint pair codes of `idU U` and
    `dom R`, `rep_dom`'s on `R.key`. -/
theorem rep_entire (R : Rel A B) {m : USize} (U : Vals A m)
    (hc : codesOK(pairs #v[idU U, dom R], pcs(idU U, dom R))) (hK : oneOK(A, R.n, R.key))
    (hp : Vals.PickFits A R.key (ids (c1(A, R.n, R.key)).groupIds.2)) :
    entire R U = true ↔ ∀ a, (∃ i, U.row i = a) → ∃ b, rep R a b := by
  show (idU U ⊑ dom R) = true ↔ _
  rw [rep_le _ _ hc, rep_idU, rep_dom R hK hp]
  exact corefl_le_dom _ _

/-- **`surjective R U = true ↔ U? ⊑ ran (rep R)`**: `entire R° U` (`rep_entire`, `convArr_holds`). Hypotheses:
    `rep_entire`'s at `R°`, whose keys are `R.val`. -/
theorem rep_surjective (R : Rel A B) {m : USize} (U : Vals B m)
    (hc : codesOK(pairs #v[idU U, dom (R°)], pcs(idU U, dom (R°)))) (hK : oneOK(B, R.n, R.val))
    (hp : Vals.PickFits B R.val (ids (c1(B, R.n, R.val)).groupIds.2)) :
    surjective R U = true ↔ ∀ b, (∃ i, U.row i = b) → ∃ a, rep R a b :=
  (rep_entire (R°) U hc hK hp).trans (forall_congr' fun _ => imp_congr_right fun _ => exists_congr fun _ =>
    convArr_holds R.key R.val _ _)

/-- The joint pair codes of two boolean relations from the bits: `pairsOK_of_parts`, only the summed count left. -/
theorem pairsOK_boolean (R S : Rel (.atom .boolean) (.atom .boolean)) (hN : R.n.toNat + S.n.toNat < USize.size) :
    codesOK(pairs #v[R, S], pcs(R, S)) :=
  pairsOK_of_parts R S ⟨codesOK_boolean _, fun hk hl => (codes_boolean_wf _ hk).2.1.trans (codes_boolean_wf _ hl).2.1.symm,
    codesOK_boolean _, fun hk hl => (codes_boolean_wf _ hk).2.1.trans (codes_boolean_wf _ hl).2.1.symm,
    by simpa using hN⟩

/-- `rep_entire` with boolean keys: the universe and `dom R` together below `USize.size` rows is all that is left. -/
theorem rep_entire_boolean (R : Rel (.atom .boolean) B) {m : USize} (U : Vals (.atom .boolean) m)
    (hN : m.toNat + (dom R).n.toNat < USize.size) :
    entire R U = true ↔ ∀ a, (∃ i, U.row i = a) → ∃ b, rep R a b := by
  show (idU U ⊑ dom R) = true ↔ _
  rw [rep_le _ _ (pairsOK_boolean _ _ hN), rep_idU, rep_dom_boolean]
  exact corefl_le_dom _ _

/-- `rep_surjective` with boolean values: `rep_entire_boolean` at `R°`. -/
theorem rep_surjective_boolean (R : Rel A (.atom .boolean)) {m : USize} (U : Vals (.atom .boolean) m)
    (hN : m.toNat + (dom (R°)).n.toNat < USize.size) :
    surjective R U = true ↔ ∀ b, (∃ i, U.row i = b) → ∃ a, rep R a b :=
  (rep_entire_boolean (R°) U hN).trans (forall_congr' fun _ => imp_congr_right fun _ => exists_congr fun _ =>
    convArr_holds R.key R.val _ _)

/-! ## `simple`, `injective`, `isMap`: `R.nub`'s keys counted against its rows -/

-- the rows `nub` keeps, named as `NubSpec` names them
set_option hygiene false in
local notation "nubI(" X ", " Y ", " R ")" =>
  (tuples.tupleIds (c1(X, Rel.n R, Rel.key R)) #[c1(Y, Rel.n R, Rel.val R)]).2

/-- `g` takes each value at most once below `m` exactly when every position below `m` is a first one. -/
theorem firsts_length_iff {α : Type} [DecidableEq α] (g : Nat → α) (m : Nat) :
    (firstsOf g m).length = m ↔ ∀ {i j : Nat}, i < m → j < m → g i = g j → i = j := by
  have hall : (firstsOf g m).length = m ↔ ∀ p < m, p ∈ firstsOf g m := by
    constructor
    · intro h p hp
      have e : firstsOf g m = List.range m :=
        List.filter_sublist.eq_of_length (by rw [List.length_range]; exact h)
      rw [e]; exact List.mem_range.2 hp
    · intro h
      have e : firstsOf g m = List.range m := by
        unfold firstsOf; exact List.filter_eq_self.2 fun p hp => (List.mem_filter.1 (h p (List.mem_range.1 hp))).2
      rw [e, List.length_range]
  rw [hall]
  constructor
  · intro h i j hi hj e
    rcases Nat.lt_trichotomy i j with hij | hij | hij
    · exact absurd e ((mem_firstsOf_iff.1 (h j hj)).2 i hij)
    · exact hij
    · exact absurd e.symm ((mem_firstsOf_iff.1 (h i hi)).2 j hij)
  · intro h p hp
    exact mem_firstsOf_iff.2 ⟨hp, fun q hq e => absurd (h (Nat.lt_trans hq hp) hp e) (Nat.ne_of_lt hq)⟩

/-- Two rows of `R.nub` holding one pair are one row: `nub` keeps the first occurrence of each pair (`nub_row`,
    `nodup_firsts`). Hypotheses: `rep_nub`'s. -/
theorem nub_rows_inj (R : Rel A B) (hK : oneOK(A, R.n, R.key)) (hV : oneOK(B, R.n, R.val))
    (hk : Vals.PickFits A R.key (ids nubI(A, B, R))) (hv : Vals.PickFits B R.val (ids nubI(A, B, R)))
    {t t' : Fin R.nub.n.toNat} (h1 : R.nub.key.row t = R.nub.key.row t') (h2 : R.nub.val.row t = R.nub.val.row t') :
    t = t' := by
  obtain ⟨-, hrow⟩ := nub_row R hK hV hk hv
  obtain ⟨hI, hp, e1, e2⟩ := hrow t.1 t.2
  obtain ⟨hI', hp', e1', e2'⟩ := hrow t'.1 t'.2
  have hg : (Column.idAt (c1(A, R.n, R.key)).b (c1(A, R.n, R.key)).w ((ids nubI(A, B, R))[t.1]'hI),
        Column.idAt (c1(B, R.n, R.val)).b (c1(B, R.n, R.val)).w ((ids nubI(A, B, R))[t.1]'hI)) =
      (Column.idAt (c1(A, R.n, R.key)).b (c1(A, R.n, R.key)).w ((ids nubI(A, B, R))[t'.1]'hI'),
        Column.idAt (c1(B, R.n, R.val)).b (c1(B, R.n, R.val)).w ((ids nubI(A, B, R))[t'.1]'hI')) := by
    rw [Prod.mk.injEq, hK.1 hp hp', hV.1 hp hp']
    exact ⟨e1.symm.trans (h1.trans e1'), e2.symm.trans (h2.trans e2')⟩
  have hnd := nodup_firsts (fun i => (Column.idAt (c1(A, R.n, R.key)).b (c1(A, R.n, R.key)).w i,
    Column.idAt (c1(B, R.n, R.val)).b (c1(B, R.n, R.val)).w i)) R.n.toNat
  rw [← nub_ids R hK hV] at hnd
  have hpw := List.pairwise_iff_getElem.1 hnd
  rcases Nat.lt_trichotomy t.1 t'.1 with h | h | h
  · exact (hpw _ _ (by simpa using hI) (by simpa using hI') h (by simpa only [List.getElem_map] using hg)).elim
  · exact Fin.ext h
  · exact (hpw _ _ (by simpa using hI') (by simpa using hI) h (by simpa only [List.getElem_map] using hg.symm)).elim

/-- **`simple R = true ↔ rep R° ≫ rep R ⊑ 𝟙`**, pointwise: `simple` counts `R.nub`'s distinct keys
    (`groupIds_firsts`) against its rows, all distinct exactly when no key holds two values (`firsts_length_iff`,
    `nub_rows_inj`, `rep_nub`). Hypotheses: `rep_nub`'s, and the key code of `R.nub` that `simple` groups. -/
theorem rep_simple (R : Rel A B) (hK : oneOK(A, R.n, R.key)) (hV : oneOK(B, R.n, R.val))
    (hk : Vals.PickFits A R.key (ids nubI(A, B, R))) (hv : Vals.PickFits B R.val (ids nubI(A, B, R)))
    (hS : oneOK(A, R.nub.n, R.nub.key)) :
    simple R = true ↔ ∀ a b b', rep R a b → rep R a b' → b = b' := by
  obtain ⟨hF, hw, hn, hs, hcard⟩ := hS
  show (len (c1(A, R.nub.n, R.nub.key)).groupIds.2 == R.nub.n.toNat) = true ↔ _
  rw [beq_iff_eq, len_eq_ids, groupIds_firsts _ hw hs hcard, hn, firsts_length_iff, ← rep_nub R hK hV hk hv]
  simp only [rep_apply]
  constructor
  · rintro h a b b' ⟨t, hta, htb⟩ ⟨t', hta', htb'⟩
    have e : t = t' := Fin.ext (h t.2 t'.2 ((hF t.2 t'.2).2 (hta.trans hta'.symm)))
    subst e; exact htb.symm.trans htb'
  · intro h i j hi hj e
    have hkey := (hF hi hj).1 e
    exact congrArg Fin.val (nub_rows_inj R hK hV hk hv hkey (h _ _ _ ⟨⟨i, hi⟩, rfl, rfl⟩ ⟨⟨j, hj⟩, hkey.symm, rfl⟩))

/-- **`injective R = true ↔ rep R ≫ rep R° ⊑ 𝟙`**, pointwise: `simple R°` (`rep_simple`, `convArr_holds`).
    Hypotheses: `rep_simple`'s at `R°`, whose keys are `R.val`. -/
theorem rep_injective (R : Rel A B) (hK : oneOK(B, R.n, R.val)) (hV : oneOK(A, R.n, R.key))
    (hk : Vals.PickFits B R.val (ids nubI(B, A, (R°)))) (hv : Vals.PickFits A R.key (ids nubI(B, A, (R°))))
    (hS : oneOK(B, (Rel.nub (R°)).n, (Rel.nub (R°)).key)) :
    injective R = true ↔ ∀ a a' b, rep R a b → rep R a' b → a = a' := by
  refine (rep_simple (R°) hK hV hk hv hS).trans ⟨fun h a a' b h1 h2 => h b a a' ?_ ?_, fun h b a a' h1 h2 => h a a' b ?_ ?_⟩
  · exact (convArr_holds R.key R.val a b).2 h1
  · exact (convArr_holds R.key R.val a' b).2 h2
  · exact (convArr_holds R.key R.val a b).1 h1
  · exact (convArr_holds R.key R.val a' b).1 h2

/-- **`isMap R U = true`**: `rep R` entire on `U` and simple — `rep_entire` and `rep_simple`, their hypotheses. -/
theorem rep_isMap (R : Rel A B) {m : USize} (U : Vals A m)
    (hc : codesOK(pairs #v[idU U, dom R], pcs(idU U, dom R))) (hK : oneOK(A, R.n, R.key))
    (hp : Vals.PickFits A R.key (ids (c1(A, R.n, R.key)).groupIds.2)) (hV : oneOK(B, R.n, R.val))
    (hk : Vals.PickFits A R.key (ids nubI(A, B, R))) (hv : Vals.PickFits B R.val (ids nubI(A, B, R)))
    (hS : oneOK(A, R.nub.n, R.nub.key)) :
    isMap R U = true ↔
      (∀ a, (∃ i, U.row i = a) → ∃ b, rep R a b) ∧ ∀ a b b', rep R a b → rep R a b' → b = b' := by
  show (entire R U && simple R) = true ↔ _
  rw [Bool.and_eq_true, rep_entire R U hc hK hp, rep_simple R hK hV hk hv hS]

end Entire

#print axioms rep_antiJoin
#print axioms rep_antiJoin_boolean
#print axioms rep_entire
#print axioms rep_surjective
#print axioms rep_entire_boolean
#print axioms rep_surjective_boolean
#print axioms rep_simple
#print axioms rep_injective
#print axioms rep_isMap

end LeetQ.Rel.Rep
