/-
  The runtime ok-bit of `CRel` on the relational primitives: each twin (`antiJoinC`, `topC`, `distinctCoreflC`,
  `domC`, `ranC`, `transposeC`, `memC`, `pairC`, `numC`, `prodC`) answers its relation and a bit deciding every
  count bound its read-back theorem takes, so `rep_opC` holds under that one bit, and the `CRel` op `&&`s its
  inputs' bits with it.
-/
import LeetQ.Rel.CRel
import LeetQ.Run.CRelDef
import LeetQ.Rel.RepMem
import LeetQ.Rel.RepLambda
import LeetQ.Rel.RepOps2
import LeetQ.Rel.RepDiv
import LeetQ.Rel.RepSymDiv
import LeetQ.Rel.RepLoop
import LeetQ.Run.CRelRelDef

namespace LeetQ.Rel

namespace Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet
open OpsN

variable {A B C D E : Obj}

/-- **`rep (distinctCorefl t x) = x?` under `distinctCoreflC`'s bit**: the code's bit gives `hK` (`oneOK_of_codesC`),
    the `fitsN` bit `hp`. -/
theorem rep_distinctCoreflC (t : Obj) {n : USize} (x : Vals t n) (hb : (distinctCoreflC t x).2 = true) :
    rep (distinctCoreflC t x).1 = corefl (A := (⟨t.El⟩ : RelSet.{0})) fun a => ∃ i, x.row i = a := by
  simp only [distinctCoreflC, okbit] at hb
  exact rep_distinctCorefl t x (oneOK_of_codesC t x hb.1) (pickFits_range _ _ hb.2)

/-- **`rep (dom R) = 𝟙 ∩ rep R (rep R)°` under `domC`'s bit**: `rep_dom`'s premises as `rep_distinctCoreflC`'s. -/
theorem rep_domC (R : Rel A B) (hb : (domC R).2 = true) : rep (domC R).1 = 𝟙 _ ∩ rep R ≫ (rep R)° := by
  simp only [domC, distinctCoreflC, okbit] at hb
  exact rep_dom R (oneOK_of_codesC A R.key hb.1) (pickFits_range _ _ hb.2)

/-- **`rep (ran R) = 𝟙 ∩ (rep R)° (rep R)°°` under `ranC`'s bit**: `rep_ran`'s premises as `rep_domC`'s. -/
theorem rep_ranC (R : Rel A B) (hb : (ranC R).2 = true) : rep (ranC R).1 = 𝟙 _ ∩ (rep R)° ≫ (rep R)°° := by
  simp only [ranC, distinctCoreflC, okbit] at hb
  exact rep_ran R (oneOK_of_codesC B R.val hb.1) (pickFits_range _ _ hb.2)

/-- **`rep (antiJoin R T) = rep R ≫ ¬ran(rep T)` under `antiJoinC`'s bit**: the joint codes' bit gives `hc`
    (`codesC_fits`, `codes_faithful_wf`), the `fitsN` bits `hk`, `hv`. -/
theorem rep_antiJoinC (R : Rel A B) (T : Rel B B) (hb : (antiJoinC R T).2 = true) :
    rep (antiJoinC R T).1 = rep R ≫ corefl (A := (⟨B.El⟩ : RelSet.{0})) fun b => ¬ ∃ y, rep T y b := by
  simp only [antiJoinC, okbit] at hb
  refine rep_antiJoin R T (codes_faithful_wf B _ (Obj.codesC_fits B _ hb.1.1)).1 ?_ ?_ <;> simp only [okbit, hb]

/-- **The anti-join is canonical where `R` is**: it keeps the rows of `R` that `anti` picks (`anti_sublist`), `anti`
    running over the first joint code, whose count is `R`'s (`codes_faithful_wf`). -/
theorem canon_antiJoinC (R : Rel A B) (T : Rel B B) (hb : (antiJoinC R T).2 = true) (hR : R.Canon) :
    (antiJoinC R T).1.Canon := by
  simp only [antiJoinC, Bool.and_eq_true] at hb
  obtain ⟨-, hn0, -⟩ := (codes_faithful_wf B _ (Obj.codesC_fits B _ hb.1.1)).1.2 (k := 0) (by decide)
  refine canon_rows R hR _ ?_ hb.1.2 hb.2
  rw [Obj.codesC_fst]
  have h := anti_sublist (B.codes #v[⟨R.n, R.val⟩, ⟨T.n, T.val⟩])[0] (B.codes #v[⟨R.n, R.val⟩, ⟨T.n, T.val⟩])[1]
  rw [hn0] at h; exact h

/-- **`rep (top Ua Ub) = Ua? ⊤ Ub?` under `topC`'s bit**: the decided counts are `hN`, `h63`, the `fitsN` bits at the
    `ma · mb` rows `hA`, `hB`. -/
theorem rep_topC {ma mb : USize} (Ua : Vals A ma) (Ub : Vals B mb) (hb : (topC Ua Ub).2 = true) :
    rep (topC Ua Ub).1 = corefl (A := (⟨A.El⟩ : RelSet.{0})) (fun a => ∃ i, Ua.row i = a) ≫
      relTop ≫ corefl (A := (⟨B.El⟩ : RelSet.{0})) (fun b => ∃ j, Ub.row j = b) := by
  simp only [topC, okbit] at hb; apply rep_top <;> simp only [okbit, hb]

/-- **`rep (num R k)` under `numC`'s bit**: the decided bound is `hk`, the `fitsN` bit `hv`. -/
theorem rep_numC (R : Rel A B) (k : USize) (hb : (numC R k).2 = true) (a : Obj.long.El) (y : B.El) :
    rep (numC R k).1 a y ↔ ∃ i : Fin R.n.toNat, a = Int64.ofNat (k.toNat + i.1) ∧ R.val.row i = y := by
  simp only [numC, okbit] at hb; apply rep_num <;> simp only [okbit, hb]

/-- **`rep (R × S) = rep R × rep S` under `prodC`'s bit**: every premise of `rep_prod` decided. -/
theorem rep_prodC (R : Rel A B) (S : Rel D E) (hb : (prodC R S).2 = true) :
    rep (prodC R S).1 = rprodMap (rep R) (rep S) := by
  simp only [prodC, okbit] at hb; apply rep_prod <;> simp only [okbit, hb]

/-- **`memC`'s bit is `rep_mem`'s premises**: the `fitsN` bit its `hv`, and with it `expand`'s guard
    (`slicesOf_copies`); the keys' pick bit, at the copies `expand` makes, its `hk` (`pickC_fits`, `copies_rows`). -/
theorem memC_ok {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (memC X).2 = true) :
    Vals.PickFits (.arr B) X (List.range n.toNat) ∧
    Vals.PickFits (.arr B) X ((List.range n.toNat).flatMap fun r =>
      if h : r < n.toNat then List.replicate (X.row ⟨r, h⟩).length r else []) := by
  simp only [memC, okbit] at hb
  obtain ⟨hk, hv⟩ := hb
  have hv' := pickFits_range (.arr B) X hv
  refine ⟨hv', ?_⟩
  unfold expand need at hk
  dsimp only at hk
  rw [dif_pos (slicesOf_copies X hv').1] at hk
  rw [← copies_rows X hv']
  exact Vals.pickC_fits (.arr B) X _ _ _ hk

/-- **`rep (mem X) xs x ↔ xs is a cell of X ∧ x ∈ xs` under `memC`'s bit**: `rep_mem` at `memC_ok`'s premises. -/
theorem rep_memC {n : USize} (X : Vals (.arr B) n) (hb : (memC X).2 = true) (xs : (Obj.arr B).El) (x : B.El) :
    rep (memC X).1 xs x ↔ (∃ i, X.row i = xs) ∧ x ∈ xs :=
  rep_mem X (memC_ok X hb).1 (memC_ok X hb).2 xs x

open Prim FoldN in
/-- **`pairC`'s bit is `rep_pair`'s premises** (`pairOK`), as `compC_ok`: the keys' codes fitting, the decided
    bounds, and the three picks' bits read at the join's rows (`join_rows`, `pickC_fits`). -/
theorem pairC_ok {A B C : Obj} (R : Rel A B) (S : Rel A C) (hb : (pairC R S).2 = true) : pairOK(A, R, S) := by
  simp only [pairC, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hcb, hrn⟩, hM⟩, hp⟩ := hb
  have hcf := Obj.codesC_fits A _ hcb
  refine ⟨hcf, ?_⟩
  rintro kc rfl
  have hc := (codes_faithful_wf A _ hcf).1
  obtain ⟨hlw, hln, hls, -⟩ := hc.2 (k := 0) (by decide)
  obtain ⟨hrw, hrn', hrs, hrc⟩ := hc.2 (k := 1) (by decide)
  replace hln : ((A.codes (#v[⟨R.n, R.key⟩, ⟨S.n, S.key⟩] : Vector (Part A) 2))[0]'Nat.zero_lt_two).n = R.n := hln
  replace hrn' : ((A.codes (#v[⟨R.n, R.key⟩, ⟨S.n, S.key⟩] : Vector (Part A) 2))[1]'Nat.one_lt_two).n = S.n := hrn'
  have hcf' := Obj.codesC_fst A (#v[⟨R.n, R.key⟩, ⟨S.n, S.key⟩] : Vector (Part A) 2)
  rw [← hcf'] at hlw hls hrw hrs hrc hln hrn'
  obtain ⟨-, hZ⟩ := join_rows _ _ hlw hls hrw hrs hrc (by rw [hrn']; exact hrn) (by rw [hln, hrn']; exact hM)
  unfold pairJoinC longCount need at hp
  dsimp only at hp
  split at hp
  · rename_i hlt
    simp only [Bool.and_eq_true] at hp
    have e := hZ _ (USize.toNat_ofNat_of_lt' hlt).symm
    have hfA := Vals.pickC_fits A R.key _ _ _ hp.1.1
    have hfB := Vals.pickC_fits B R.val _ _ _ hp.1.2
    have hfC := Vals.pickC_fits C S.val _ _ _ hp.2
    rw [hln, hrn'] at e
    rw [hcf'] at e hfA hfB hfC
    exact ⟨hrn, hM, by rw [e, List.map_map]; exact hfA, by rw [e, List.map_map]; exact hfB,
      by rw [e, List.map_map]; exact hfC⟩
  · exact absurd hp Bool.false_ne_true

/-- **`rep ⟨R, S⟩ = ⟨rep R, rep S⟩` under `pairC`'s bit**: `rep_pair` at `pairC_ok`'s premises. -/
theorem rep_pairC (R : Rel A B) (S : Rel A C) (hb : (pairC R S).2 = true) :
    rep (pairC R S).1 = rpair (rep R) (rep S) := by
  obtain ⟨hcf, h⟩ := pairC_ok R S hb
  obtain ⟨hrn, hM, hA, hB, hC⟩ := h _ rfl
  exact rep_pair R S (codes_faithful_wf A _ hcf).1 hrn hM hA hB hC

/-- **`transposeByC o`'s bit gives `rep_transpose`'s premises but the order's**: `nubC`'s bits give `hK`, `hV`
    (`oneOK_of_codesC`), the `fitsN` bits `hk`, `hv`; the nub keys' codes bit `hWk` (`codesC_fits`, `nubC`'s `.1`
    read as `nub` by `simp`, the twin sitting as an argument of `keyPart`); `o`'s own bit at the nub; the decided
    count `h63`. -/
theorem transposeByC_ok (o : Rel A B → ByteArray × Bool) (R : Rel A B) (hb : (transposeByC o R).2 = true) :
    oneOK(A, R.n, R.key) ∧ oneOK(B, R.n, R.val) ∧ Vals.PickFits A R.key (List.range R.n.toNat) ∧
      Vals.PickFits B R.val (List.range R.n.toNat) ∧
      A.CodesFit (#v[⟨(Rel.nub R).n, (Rel.nub R).key⟩] : Vector (Part A) 1) ∧
      (o (Rel.nub R)).2 = true ∧ R.n.toNat < 2 ^ 63 := by
  simp only [transposeByC, nubC_fst] at hb
  simp only [keyPart, nubC, okbit] at hb
  exact ⟨oneOK_of_codesC A R.key (by simp only [hb]), oneOK_of_codesC B R.val (by simp only [hb]),
    by simp only [okbit, hb]⟩

/-- **`valSortC`'s bit makes its order a permutation of the rows**: the bit is the values' codes' (`sortByC_snd`),
    which `sortBy_nub_perm` takes as their fit (`codesC_fits`). -/
theorem valSortC_perm (d : Rel A B) (hb : (valSortC d).2 = true) :
    (ids (valSortC d).1).Perm (List.range d.n.toNat) := by
  simp only [valSortC, Obj.sortByC_snd] at hb
  exact sortBy_nub_perm d (Obj.codesC_fits B _ hb)

/-- **`transposeC`'s bit gives `rep_transpose`'s premises**: `transposeByC_ok` at `valSortC`, whose bit is the nub
    values' codes' (`sortByC_snd`), their fit `hW` (`codesC_fits`). -/
theorem transposeC_ok (R : Rel A B) (hb : (transposeC R).2 = true) :
    oneOK(A, R.n, R.key) ∧ oneOK(B, R.n, R.val) ∧ Vals.PickFits A R.key (List.range R.n.toNat) ∧
      Vals.PickFits B R.val (List.range R.n.toNat) ∧
      A.CodesFit (#v[⟨(Rel.nub R).n, (Rel.nub R).key⟩] : Vector (Part A) 1) ∧
      B.CodesFit (#v[⟨(Rel.nub R).n, (Rel.nub R).val⟩] : Vector (Part B) 1) ∧ R.n.toNat < 2 ^ 63 := by
  obtain ⟨hK, hV, hk, hv, hWk, ho, h63⟩ := transposeByC_ok valSortC R hb
  simp only [valSortC, Obj.sortByC_snd] at ho
  exact ⟨hK, hV, hk, hv, hWk, Obj.codesC_fits B _ ho, h63⟩

/-- **`rep (Λ(R))` is the power transpose of `rep R` under `transposeC`'s bit**: `rep_transpose` at
    `transposeC_ok`. -/
theorem rep_transposeC (R : Rel A B) (hb : (transposeC R).2 = true) :
    (∀ a X, rep (transposeC R).1 a X → ∀ x, x ∈ X ↔ rep R a x) ∧
      (∀ a, (∃ X, rep (transposeC R).1 a X) ↔ ∃ b, rep R a b) := by
  obtain ⟨hK, hV, hk, hv, hWk, hW, h63⟩ := transposeC_ok R hb
  exact rep_transpose R hK hV hk hv hWk _ (sortBy_nub_perm _ hW) _ (transpose_eq _) h63

/-- **`rep (R /ₛ S)` under `symDivC`'s bit**: `rep_symDiv` at the intermediates `symDivC` builds (the codes twins'
    `.1` read as `Obj.codes` by `simp`, sitting as arguments of `segments`/`symDivIds`/`symDivTailC`; then `joinC`'s
    and `⊤`'s). The codes' bits give `hfv`, `hfa`, `hfb` (`codesC_fits`), the decided counts `hNU`, `hN63`, `hRS`,
    `hUab`, the `fitsN` bits `hRk`, `hSk`, `hPa`, `hPb`, `topC`'s `hA`, `hBv`, `unionC`'s `hU`…`hUv` (as
    `rep_leftDivC`); the join picks' bit is `rep_symDiv`'s own. -/
theorem rep_symDivC {ma mb : USize} (R : Rel A C) (S : Rel B C) (Ua : Vals A ma) (Ub : Vals B mb)
    (hb : (symDivC R S Ua Ub).2 = true) (x : A.El) (y : B.El) :
    rep (symDivC R S Ua Ub).1 x y ↔
      (∀ c, rep R x c ↔ rep S y c) ∧ ((∃ c, rep R x c) ∨ ((∃ p, Ua.row p = x) ∧ ∃ j, Ub.row j = y)) := by
  simp only [symDivC, Obj.codesC_fst] at hb
  simp only [keyPart, valPart, symDivIds, okbit] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hfv, hfa⟩, hfb⟩, hNU⟩, hN63⟩, hRk⟩, hSk⟩, hRS⟩, hh⟩, hPa⟩, hPb⟩, hUab⟩, hu⟩ := hb
  simp only [symDivTailC, topC, joinC_fst, okbit] at hu
  obtain ⟨⟨⟨⟨-, -⟩, ha⟩, hbc⟩, hu⟩ := hu
  unfold unionC need at hu
  split at hu
  · rename_i hU
    simp only [okbit] at hu
    obtain ⟨⟨⟨⟨⟨hka, hvb⟩, hkc⟩, hvc⟩, hkf⟩, hvf⟩ := hu
    have hFk := Obj.razeC_fits A _ _ _ rfl _ hka
    have hFv := Obj.razeC_fits B _ _ _ rfl _ hvb
    simp only [razeC_fst] at hkc hvc hkf hvf
    exact rep_symDiv R S Ua Ub _ rfl (Obj.codesC_fits C _ hfv) _ rfl (Obj.codesC_fits A _ hfa) _ rfl
      (Obj.codesC_fits B _ hfb) _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl hNU hN63 _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
      _ rfl _ rfl _ _ rfl rfl _ rfl _ rfl (pickFits_range A R.key hRk) (pickFits_range B S.key hSk) hRS hh
      (pickFits_range A Ua hPa) (pickFits_range B Ub hPb) hUab
      -- `⊤`'s rows count the vacuous parts as `topC` read them, which equal `vacA`'s, `vacB`'s by unfolding only
      (pickFits_map_range A _ _ ha) (pickFits_map_range B _ _ hbc) _ _ rfl rfl hU hFk hFv
      (Obj.codesC_fits A _ hkc) (Obj.codesC_fits B _ hvc) (pickFits_range A _ hkf) (pickFits_range B _ hvf) x y
  · exact absurd hu Bool.false_ne_true

-- the keys `leftDiv` joins: `nub`'s, coded jointly
set_option hygiene false in
local notation "dks" => (#v[⟨(Rel.nub R).n, (Rel.nub R).key⟩, ⟨(Rel.nub S).n, (Rel.nub S).key⟩] : Vector (Part A) 2)

/-- **`rep (R \ S)` under `leftDivC`'s bit**: `rep_leftDiv` at the intermediates `leftDivC` builds (each twin's `.1`
    read as its op by `simp`, the twins sitting as arguments of `divTailC`/`keyPart`: `nubC_fst`, `codesC_fst`, `joinC_fst`). `nubC`'s bits give `hRK`…`hSv`
    (`codesC_fits`, `pickFits_of_fitsN`), the codes' bits `hfk`, `hfy`, `hfz`, the join picks' bits, read at the
    join's rows (`join_rows`), `hB`, `hC`, `topC`'s `hA`, `hBc`, `unionC`'s `hU`…`hUv` (as `rep_unionC`). -/
theorem rep_leftDivC {mb mc : USize} (R : Rel A B) (S : Rel A C) (Ub : Vals B mb) (Uc : Vals C mc)
    (hb : (leftDivC R S Ub Uc).2 = true) (b : B.El) (c : C.El) :
    rep (leftDivC R S Ub Uc).1 b c ↔
      (∀ a, rep R a b → rep S a c) ∧ ((∃ a, rep R a b) ∨ ((∃ p, Ub.row p = b) ∧ ∃ j, Uc.row j = c)) := by
  simp only [leftDivC, nubC_fst, Obj.codesC_fst, joinC_fst] at hb
  simp only [keyPart, valPart, divTailC, nubC, okbit] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hRK, hRV⟩, hRk⟩, hRv⟩, ⟨⟨⟨hSK, hSV⟩, hSk⟩, hSv⟩⟩, hk⟩, hSn⟩, hRS⟩, hy⟩, hycs⟩, hzc⟩, hP⟩, hUbc⟩,
    hq, hu⟩ := hb
  have hRK' := Obj.codesC_fits A _ hRK; have hRV' := Obj.codesC_fits B _ hRV
  have hSK' := Obj.codesC_fits A _ hSK; have hSV' := Obj.codesC_fits C _ hSV
  have hRk' := pickFits_range A R.key hRk; have hRv' := pickFits_range B R.val hRv
  have hSk' := pickFits_range A S.key hSk; have hSv' := pickFits_range C S.val hSv
  have hfk := Obj.codesC_fits A _ hk
  -- the join's rows, as `rep_compC`; `nub` keeps at most the input's rows
  have nR := nub_count_le R (one_ok _ hRK') (one_ok _ hRV') hRk' hRv'
  have nS := nub_count_le S (one_ok _ hSK') (one_ok _ hSV') hSk' hSv'
  have hM : (Rel.nub R).n.toNat * (Rel.nub S).n.toNat < min (2 ^ 63) USize.size :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul nR nS) hRS
  have hc := (codes_faithful_wf A _ hfk).1
  obtain ⟨hlw, hln, hls, -⟩ := hc.2 (k := 0) (by decide)
  obtain ⟨hrw, hrn', hrs, hrc⟩ := hc.2 (k := 1) (by decide)
  replace hln : ((A.codes dks)[0]'Nat.zero_lt_two).n = (Rel.nub R).n := hln
  replace hrn' : ((A.codes dks)[1]'Nat.one_lt_two).n = (Rel.nub S).n := hrn'
  obtain ⟨-, hZ⟩ := join_rows _ _ hlw hls hrw hrs hrc (by rw [hrn']; exact Nat.lt_of_le_of_lt nS hSn)
    (by rw [hln, hrn']; exact hM)
  unfold joinC longCount need at hy; dsimp only at hy
  split at hy
  · rename_i hlt
    simp only [Bool.and_eq_true] at hy
    have e := hZ _ (USize.toNat_ofNat_of_lt' hlt).symm
    have hfB := Vals.pickC_fits B _ _ _ _ hy.1
    have hfC := Vals.pickC_fits C _ _ _ _ hy.2
    unfold unionC need at hu
    split at hu
    · rename_i hU
      simp only [okbit] at hu
      obtain ⟨⟨⟨⟨⟨hka, hvb⟩, hkc⟩, hvc⟩, hkf⟩, hvf⟩ := hu
      have hFk := Obj.razeC_fits B _ _ _ rfl _ hka
      have hFv := Obj.razeC_fits C _ _ _ rfl _ hvb
      simp only [razeC_fst] at hkc hvc hkf hvf
      simp only [topC, okbit] at hq
      obtain ⟨⟨-, ha⟩, hbc⟩ := hq
      exact rep_leftDiv R S Ub Uc hRK' hRV' hRk' hRv' hSK' hSV' hSk' hSv' _ rfl hfk hSn hRS
        (by rw [e, List.map_map]; exact hfB) (by rw [e, List.map_map]; exact hfC) _ rfl _ rfl
        (Obj.codesC_fits B _ hycs) _ rfl (Obj.codesC_fits C _ hzc) _ rfl (pickFits_range B Ub hP) hUbc
        -- `⊤`'s rows count the vacuous part as `topC` read it, which equals `vacY`'s by unfolding only
        (pickFits_map_range B _ _ ha) (pickFits_map_range C Uc _ hbc) _ _ rfl rfl hU hFk hFv
        (Obj.codesC_fits B _ hkc) (Obj.codesC_fits C _ hvc) (pickFits_range B _ hkf) (pickFits_range C _ hvf) b c
    · exact absurd hu Bool.false_ne_true
  · exact absurd hy Bool.false_ne_true

/-- **`rep (R / S)` under `rightDivC`'s bit**, which is `leftDivC`'s at `S°`, `R°`: `rep_leftDivC` there, read through
    `rep_conv`. The objects are named as in `rep_rightDiv`. -/
theorem rep_rightDivC {ma mb : USize} (R : Rel C A) (S : Rel B A) (Ua : Vals C ma) (Ub : Vals B mb)
    (hb : (rightDivC R S Ua Ub).2 = true) (x : C.El) (y : B.El) :
    rep (rightDivC R S Ua Ub).1 x y ↔
      (∀ c, rep S y c → rep R x c) ∧ ((∃ c, rep S y c) ∨ ((∃ p, Ua.row p = x) ∧ ∃ j, Ub.row j = y)) := by
  rw [show (rightDivC R S Ua Ub).1 = ((leftDivC (S°) (R°) Ub Ua).1)° from rfl, rep_conv]
  show rep (leftDivC (S°) (R°) Ub Ua).1 y x ↔ _
  rw [rep_leftDivC (S°) (R°) Ub Ua hb y x, rep_conv, rep_conv]
  exact and_congr Iff.rfl (or_congr Iff.rfl and_comm)

#print axioms rep_leftDivC
#print axioms rep_rightDivC
#print axioms rep_distinctCoreflC
#print axioms rep_domC
#print axioms rep_ranC
#print axioms rep_antiJoinC
#print axioms rep_topC
#print axioms rep_numC
#print axioms rep_prodC
#print axioms rep_memC
#print axioms rep_pairC
#print axioms rep_transposeC
#print axioms transposeC_ok
#print axioms rep_symDivC

end Rep

namespace CRel

open QLean QLean.Kernel LeetQ.Rel.Alg Freyd Freyd.Alg Freyd.Alg.RelSet LeetQ.Rel.Rep

variable {A B C D E : Obj}

theorem rep_symDiv {ma mb : USize} (R : CRel A C) (S : CRel B C) (Ua : Vals A ma) (Ub : Vals B mb)
    (hb : (R.symDiv S Ua Ub).ok = true) (x : A.El) (y : B.El) :
    rep (R.symDiv S Ua Ub).rel x y ↔ (∀ c, rep R.rel x c ↔ rep S.rel y c) ∧
      ((∃ c, rep R.rel x c) ∨ ((∃ p, Ua.row p = x) ∧ ∃ j, Ub.row j = y)) := by
  have e : R.symDiv S Ua Ub = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_symDivC R.rel S.rel Ua Ub hb x y

theorem rep_leftDiv {mb mc : USize} (R : CRel A B) (S : CRel A C) (Ub : Vals B mb) (Uc : Vals C mc)
    (hb : (R.leftDiv S Ub Uc).ok = true) (b : B.El) (c : C.El) :
    rep (R.leftDiv S Ub Uc).rel b c ↔ (∀ a, rep R.rel a b → rep S.rel a c) ∧
      ((∃ a, rep R.rel a b) ∨ ((∃ p, Ub.row p = b) ∧ ∃ j, Uc.row j = c)) := by
  have e : R.leftDiv S Ub Uc = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_leftDivC R.rel S.rel Ub Uc hb b c

theorem rep_rightDiv {ma mb : USize} (R : CRel C A) (S : CRel B A) (Ua : Vals C ma) (Ub : Vals B mb)
    (hb : (R.rightDiv S Ua Ub).ok = true) (x : C.El) (y : B.El) :
    rep (R.rightDiv S Ua Ub).rel x y ↔ (∀ c, rep S.rel y c → rep R.rel x c) ∧
      ((∃ c, rep S.rel y c) ∨ ((∃ p, Ua.row p = x) ∧ ∃ j, Ub.row j = y)) := by
  have e : R.rightDiv S Ua Ub = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_rightDivC R.rel S.rel Ua Ub hb x y

theorem rep_antiJoin (R : CRel A B) (T : CRel B B) (hb : (R.antiJoin T).ok = true) :
    rep (R.antiJoin T).rel = rep R.rel ≫ corefl (A := (⟨B.El⟩ : RelSet.{0})) fun b => ¬ ∃ y, rep T.rel y b := by
  have e : R.antiJoin T = _ := guard_eq ok hb; rw [e] at hb ⊢; exact rep_antiJoinC R.rel T.rel hb

/-- **`CRel.antiJoin` is canonical where `R` is**: `canon_antiJoinC`. -/
theorem canon_antiJoin (R : CRel A B) (T : CRel B B) (hb : (R.antiJoin T).ok = true) (hR : R.rel.Canon) :
    (R.antiJoin T).rel.Canon := by
  have e : R.antiJoin T = _ := guard_eq ok hb; rw [e] at hb ⊢; exact canon_antiJoinC R.rel T.rel hb hR

theorem rep_top {ma mb : USize} (Ua : Vals A ma) (Ub : Vals B mb) (hb : (top Ua Ub).ok = true) :
    rep (top Ua Ub).rel = corefl (A := (⟨A.El⟩ : RelSet.{0})) (fun a => ∃ i, Ua.row i = a) ≫
      relTop ≫ corefl (A := (⟨B.El⟩ : RelSet.{0})) (fun b => ∃ j, Ub.row j = b) :=
  by unfold CRel.top at hb ⊢; rw [rep_ofC hb]; exact rep_topC Ua Ub (ofC_ok hb).1

theorem rep_distinctCorefl (t : Obj) {n : USize} (x : Vals t n) (hb : (distinctCorefl t x).ok = true) :
    rep (distinctCorefl t x).rel = corefl (A := (⟨t.El⟩ : RelSet.{0})) fun a => ∃ i, x.row i = a :=
  by unfold CRel.distinctCorefl at hb ⊢; rw [rep_ofC hb]; exact rep_distinctCoreflC t x (ofC_ok hb).1

/-- **`𝟙 R` is `R` on data**: `𝟙` the coreflexive on `U`, which holds every source of the canonical `R`. -/
theorem id_comp {m : USize} (U : Vals A m) (R : CRel A B) (hb : ((distinctCorefl A U).comp R).ok = true)
    (hU : ∀ x y, rep R.rel x y → ∃ i, U.row i = x) (hR : R.rel.Canon) (ho : (Obj.prod A B).Ordered)
    (hi : (Obj.prod A B).KeyInj) : ((distinctCorefl A U).comp R).rel.toList = R.rel.toList := by
  have hl := guard_ok_left hb; simp only [Bool.and_eq_true] at hl
  refine canon_eq (canon_comp _ _ hb ho hi) hR ?_
  rw [rep_comp _ _ hb, rep_distinctCorefl A U hl.1]
  refine hom_ext fun x y => ⟨?_, fun h => ⟨x, ⟨rfl, hU x y h⟩, h⟩⟩
  rintro ⟨z, ⟨rfl, -⟩, h⟩; exact h

/-- **`R 𝟙` is `R` on data**: `𝟙` the coreflexive on `U`, which holds every target of the canonical `R`. -/
theorem comp_id {m : USize} (R : CRel A B) (U : Vals B m) (hb : (R.comp (distinctCorefl B U)).ok = true)
    (hU : ∀ x y, rep R.rel x y → ∃ i, U.row i = y) (hR : R.rel.Canon) (ho : (Obj.prod A B).Ordered)
    (hi : (Obj.prod A B).KeyInj) : (R.comp (distinctCorefl B U)).rel.toList = R.rel.toList := by
  have hl := guard_ok_left hb; simp only [Bool.and_eq_true] at hl
  refine canon_eq (canon_comp _ _ hb ho hi) hR ?_
  rw [rep_comp _ _ hb, rep_distinctCorefl B U hl.2]
  refine hom_ext fun x y => ⟨?_, fun h => ⟨y, h, rfl, hU x y h⟩⟩
  rintro ⟨z, h, rfl, -⟩; exact h

theorem rep_dom (R : CRel A B) (hb : R.dom.ok = true) : rep R.dom.rel = 𝟙 _ ∩ rep R.rel ≫ (rep R.rel)° := by
  have e : R.dom = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_domC R.rel hb

theorem rep_ran (R : CRel A B) (hb : R.ran.ok = true) : rep R.ran.rel = 𝟙 _ ∩ (rep R.rel)° ≫ (rep R.rel)°° := by
  have e : R.ran = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_ranC R.rel hb

theorem rep_transpose (R : CRel A B) (hb : R.transpose.ok = true) :
    (∀ a X, rep R.transpose.rel a X → ∀ x, x ∈ X ↔ rep R.rel a x) ∧
      (∀ a, (∃ X, rep R.transpose.rel a X) ↔ ∃ b, rep R.rel a b) := by
  have e : R.transpose = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_transposeC R.rel hb

theorem rep_mem {n : USize} (X : Vals (.arr B) n) (hb : (mem X).ok = true) (xs : (Obj.arr B).El) (x : B.El) :
    rep (mem X).rel xs x ↔ (∃ i, X.row i = xs) ∧ x ∈ xs :=
  by unfold CRel.mem at hb ⊢; rw [rep_ofC hb]; exact rep_memC X (ofC_ok hb).1 xs x

theorem rep_pair (R : CRel A B) (S : CRel A C) (hb : (R.pair S).ok = true) :
    rep (R.pair S).rel = rpair (rep R.rel) (rep S.rel) := by
  have e : R.pair S = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_pairC R.rel S.rel hb

theorem rep_num (R : CRel A B) (k : USize) (hb : (R.num k).ok = true) (a : Obj.long.El) (y : B.El) :
    rep (R.num k).rel a y ↔ ∃ i : Fin R.rel.n.toNat, a = Int64.ofNat (k.toNat + i.1) ∧ R.rel.val.row i = y := by
  have e : R.num k = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_numC R.rel k hb a y

theorem rep_prod (R : CRel A B) (S : CRel D E) (hb : (R.prod S).ok = true) :
    rep (R.prod S).rel = rprodMap (rep R.rel) (rep S.rel) := by
  have e : R.prod S = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_prodC R.rel S.rel hb

end CRel

end LeetQ.Rel
