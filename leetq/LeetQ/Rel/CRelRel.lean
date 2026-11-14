/-
  The runtime ok-bit of `CRel` on the relational primitives: each twin (`antiJoinC`, `topC`, `distinctCoreflC`,
  `domC`, `ranC`, `transposeC`, `memC`, `pairC`, `numC`, `prodC`) answers its relation and a bit deciding every
  count bound its read-back theorem takes, so `rep_opC` holds under that one bit, and the `CRel` op `&&`s its
  inputs' bits with it.
-/
import LeetQ.Rel.CRel
import LeetQ.Rel.RepMem
import LeetQ.Rel.RepLambda
import LeetQ.Rel.RepOps2
import LeetQ.Rel.RepDiv
import LeetQ.Rel.RepLoop

namespace LeetQ.Rel

namespace Alg

variable {A B D E : Obj}

/-- `R × S` and whether it ran within capacity: `rep_prod`'s bounds decided as it states them, the pair count and
    each column's reads repeated once per row of the other side; `prod` itself runs. Here, not beside `prod`,
    because `Vals.reads` is defined after `Alg`. -/
def prodC (R : Rel A B) (S : Rel D E) : Rel (.prod A D) (.prod B E) × Bool :=
  (prod R S, decide (R.n.toNat * S.n.toNat < USize.size) && decide (R.n.toNat * S.n.toNat < 2 ^ 63) &&
    decide ((S.n.toNat + 1) * Vals.reads A R.key (List.range R.n.toNat) < min (2 ^ 63) USize.size) &&
    decide ((S.n.toNat + 1) * Vals.reads B R.val (List.range R.n.toNat) < min (2 ^ 63) USize.size) &&
    decide ((R.n.toNat + 1) * Vals.reads D S.key (List.range S.n.toNat) < min (2 ^ 63) USize.size) &&
    decide ((R.n.toNat + 1) * Vals.reads E S.val (List.range S.n.toNat) < min (2 ^ 63) USize.size))

end Alg

namespace Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet
open OpsN

variable {A B C D E : Obj}

/-- A one-part codes bit gives the one-part code faithful and well formed, in `oneOK`'s form. -/
theorem oneOK_of_codesC (X : Obj) {n : USize} (x : Vals X n) (hb : (X.codesC #v[⟨n, x⟩]).2 = true) :
    oneOK(X, n, x) := by
  have hK := (codes_faithful_wf X _ (Obj.codesC_fits X _ hb)).1
  exact ⟨fun hi hj => hK.1 (k := 0) (l := 0) Nat.zero_lt_one Nat.zero_lt_one hi hj, hK.2 (k := 0) Nat.zero_lt_one⟩

/-- **`rep (distinctCorefl t x) = x?` under `distinctCoreflC`'s bit**: the code's bit gives `hK` (`oneOK_of_codesC`),
    the `fitsN` bit `hp`. -/
theorem rep_distinctCoreflC (t : Obj) {n : USize} (x : Vals t n) (hb : (distinctCoreflC t x).2 = true) :
    rep (distinctCoreflC t x).1 = corefl (A := (⟨t.El⟩ : RelSet.{0})) fun a => ∃ i, x.row i = a := by
  simp only [distinctCoreflC, Bool.and_eq_true] at hb
  exact rep_distinctCorefl t x (oneOK_of_codesC t x hb.1) (pickFits_of_fitsN t x _ hb.2 _ (by simp))

/-- **`rep (dom R) = 𝟙 ∩ rep R (rep R)°` under `domC`'s bit**: `rep_dom`'s premises as `rep_distinctCoreflC`'s. -/
theorem rep_domC (R : Rel A B) (hb : (domC R).2 = true) : rep (domC R).1 = 𝟙 _ ∩ rep R ≫ (rep R)° := by
  simp only [domC, distinctCoreflC, Bool.and_eq_true] at hb
  exact rep_dom R (oneOK_of_codesC A R.key hb.1) (pickFits_of_fitsN A R.key _ hb.2 _ (by simp))

/-- **`rep (ran R) = 𝟙 ∩ (rep R)° (rep R)°°` under `ranC`'s bit**: `rep_ran`'s premises as `rep_domC`'s. -/
theorem rep_ranC (R : Rel A B) (hb : (ranC R).2 = true) : rep (ranC R).1 = 𝟙 _ ∩ (rep R)° ≫ (rep R)°° := by
  simp only [ranC, distinctCoreflC, Bool.and_eq_true] at hb
  exact rep_ran R (oneOK_of_codesC B R.val hb.1) (pickFits_of_fitsN B R.val _ hb.2 _ (by simp))

/-- **`rep (antiJoin R T) = rep R ≫ ¬ran(rep T)` under `antiJoinC`'s bit**: the joint codes' bit gives `hc`
    (`codesC_fits`, `codes_faithful_wf`), the `fitsN` bits `hk`, `hv`. -/
theorem rep_antiJoinC (R : Rel A B) (T : Rel B B) (hb : (antiJoinC R T).2 = true) :
    rep (antiJoinC R T).1 = rep R ≫ corefl (A := (⟨B.El⟩ : RelSet.{0})) fun b => ¬ ∃ y, rep T y b := by
  simp only [antiJoinC, Bool.and_eq_true] at hb
  obtain ⟨⟨hcb, hk⟩, hv⟩ := hb
  exact rep_antiJoin R T (codes_faithful_wf B _ (Obj.codesC_fits B _ hcb)).1
    (pickFits_of_fitsN A R.key _ hk _ (by simp)) (pickFits_of_fitsN B R.val _ hv _ (by simp))

/-- **`rep (top Ua Ub) = Ua? ⊤ Ub?` under `topC`'s bit**: the decided counts are `hN`, `h63`, the `fitsN` bits at the
    `ma · mb` rows `hA`, `hB`. -/
theorem rep_topC {ma mb : USize} (Ua : Vals A ma) (Ub : Vals B mb) (hb : (topC Ua Ub).2 = true) :
    rep (topC Ua Ub).1 = corefl (A := (⟨A.El⟩ : RelSet.{0})) (fun a => ∃ i, Ua.row i = a) ≫
      relTop ≫ corefl (A := (⟨B.El⟩ : RelSet.{0})) (fun b => ∃ j, Ub.row j = b) := by
  simp only [topC, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hN, h63⟩, ha⟩, hb⟩ := hb
  exact rep_top Ua Ub hN h63 (pickFits_of_fitsN A Ua _ ha _ (by simp)) (pickFits_of_fitsN B Ub _ hb _ (by simp))

/-- **`rep (num R k)` under `numC`'s bit**: the decided bound is `hk`, the `fitsN` bit `hv`. -/
theorem rep_numC (R : Rel A B) (k : USize) (hb : (numC R k).2 = true) (a : Obj.long.El) (y : B.El) :
    rep (numC R k).1 a y ↔ ∃ i : Fin R.n.toNat, a = Int64.ofNat (k.toNat + i.1) ∧ R.val.row i = y := by
  simp only [numC, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact rep_num R k hb.1 (pickFits_of_fitsN B R.val _ hb.2 _ (by simp)) a y

/-- **`rep (R × S) = rep R × rep S` under `prodC`'s bit**: every premise of `rep_prod` decided. -/
theorem rep_prodC (R : Rel A B) (S : Rel D E) (hb : (prodC R S).2 = true) :
    rep (prodC R S).1 = rprodMap (rep R) (rep S) := by
  simp only [prodC, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨hN, h63⟩, hA⟩, hB⟩, hC⟩, hD⟩ := hb
  exact rep_prod R S hN h63 hA hB hC hD

/-- **`memC`'s bit is `rep_mem`'s premises**: the `fitsN` bit its `hv`, and with it `expand`'s guard
    (`slicesOf_copies`); the keys' pick bit, at the copies `expand` makes, its `hk` (`pickC_fits`, `copies_rows`). -/
theorem memC_ok {B : Obj} {n : USize} (X : Vals (.arr B) n) (hb : (memC X).2 = true) :
    Vals.PickFits (.arr B) X (List.range n.toNat) ∧
    Vals.PickFits (.arr B) X ((List.range n.toNat).flatMap fun r =>
      if h : r < n.toNat then List.replicate (X.row ⟨r, h⟩).length r else []) := by
  simp only [memC, Bool.and_eq_true] at hb
  obtain ⟨hk, hv⟩ := hb
  have hv' : Vals.PickFits (.arr B) X (List.range n.toNat) := pickFits_of_fitsN (.arr B) X _ hv _ (by simp)
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

/-- **`rep (Λ(R))` is the power transpose of `rep R` under `transposeC`'s bit**: `nub`'s codes' bits give `hK`, `hV`
    (`oneOK_of_codesC`), the `fitsN` bits `hk`, `hv`, the nub sides' codes bits `hWk`, `hW` (`codesC_fits`), the
    decided count `h63`. -/
theorem rep_transposeC (R : Rel A B) (hb : (transposeC R).2 = true) :
    (∀ a X, rep (transposeC R).1 a X → ∀ x, x ∈ X ↔ rep R a x) ∧
      (∀ a, (∃ X, rep (transposeC R).1 a X) ↔ ∃ b, rep R a b) := by
  simp only [transposeC, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨hK, hV⟩, hk⟩, hv⟩, hWk⟩, hW⟩, h63⟩ := hb
  exact rep_transpose R (oneOK_of_codesC A R.key hK) (oneOK_of_codesC B R.val hV)
    (pickFits_of_fitsN A R.key _ hk _ (by simp)) (pickFits_of_fitsN B R.val _ hv _ (by simp))
    (Obj.codesC_fits A _ hWk) (Obj.codesC_fits B _ hW) h63

-- the keys `leftDiv` joins: `nub`'s, coded jointly
set_option hygiene false in
local notation "dks" => (#v[⟨(Rel.nub R).n, (Rel.nub R).key⟩, ⟨(Rel.nub S).n, (Rel.nub S).key⟩] : Vector (Part A) 2)

/-- **`rep (R \ S)` under `leftDivC`'s bit**: `rep_leftDiv` at the intermediates `leftDivC` builds (each twin's `.1`
    read as its op by `simp`, the twins sitting as arguments of `divTailC`/`keyPart`: `nubC_fst`, `codesC_fst`, `divJoinC_fst`). `nubC`'s bits give `hRK`…`hSv`
    (`codesC_fits`, `pickFits_of_fitsN`), the codes' bits `hfk`, `hfy`, `hfz`, the join picks' bits, read at the
    join's rows (`join_rows`), `hB`, `hC`, `topC`'s `hA`, `hBc`, `unionC`'s `hU`…`hUv` (as `rep_unionC`). -/
theorem rep_leftDivC {mb mc : USize} (R : Rel A B) (S : Rel A C) (Ub : Vals B mb) (Uc : Vals C mc)
    (hb : (leftDivC R S Ub Uc).2 = true) (b : B.El) (c : C.El) :
    rep (leftDivC R S Ub Uc).1 b c ↔
      (∀ a, rep R a b → rep S a c) ∧ ((∃ a, rep R a b) ∨ ((∃ p, Ub.row p = b) ∧ ∃ j, Uc.row j = c)) := by
  simp only [leftDivC, nubC_fst, Obj.codesC_fst, divJoinC_fst] at hb
  simp only [keyPart, valPart, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hr, hs⟩, hk⟩, hSn⟩, hRS⟩, hy⟩, hycs⟩, hzc⟩, hP⟩, hUbc⟩, hu⟩ := hb
  simp only [divTailC, Bool.and_eq_true] at hu
  obtain ⟨hq, hu⟩ := hu
  simp only [nubC, Bool.and_eq_true] at hr hs
  obtain ⟨⟨⟨hRK, hRV⟩, hRk⟩, hRv⟩ := hr
  obtain ⟨⟨⟨hSK, hSV⟩, hSk⟩, hSv⟩ := hs
  have hRK' := Obj.codesC_fits A _ hRK; have hRV' := Obj.codesC_fits B _ hRV
  have hSK' := Obj.codesC_fits A _ hSK; have hSV' := Obj.codesC_fits C _ hSV
  have hRk' := pickFits_of_fitsN A R.key _ hRk (List.range R.n.toNat) (by simp)
  have hRv' := pickFits_of_fitsN B R.val _ hRv (List.range R.n.toNat) (by simp)
  have hSk' := pickFits_of_fitsN A S.key _ hSk (List.range S.n.toNat) (by simp)
  have hSv' := pickFits_of_fitsN C S.val _ hSv (List.range S.n.toNat) (by simp)
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
  unfold divJoinC longCount need at hy; dsimp only at hy
  split at hy
  · rename_i hlt
    simp only [Bool.and_eq_true] at hy
    have e := hZ _ (USize.toNat_ofNat_of_lt' hlt).symm
    have hfB := Vals.pickC_fits B _ _ _ _ hy.1
    have hfC := Vals.pickC_fits C _ _ _ _ hy.2
    unfold unionC need at hu
    split at hu
    · rename_i hU
      simp only [Bool.and_eq_true] at hu
      obtain ⟨⟨⟨⟨⟨hka, hvb⟩, hkc⟩, hvc⟩, hkf⟩, hvf⟩ := hu
      have hFk := Obj.razeC_fits B _ _ _ rfl _ hka
      have hFv := Obj.razeC_fits C _ _ _ rfl _ hvb
      simp only [razeC_fst] at hkc hvc hkf hvf
      simp only [topC, Bool.and_eq_true, decide_eq_true_eq] at hq
      obtain ⟨⟨-, ha⟩, hbc⟩ := hq
      exact rep_leftDiv R S Ub Uc hRK' hRV' hRk' hRv' hSK' hSV' hSk' hSv' _ rfl hfk hSn hRS
        (by rw [e, List.map_map]; exact hfB) (by rw [e, List.map_map]; exact hfC) _ rfl _ rfl
        (Obj.codesC_fits B _ hycs) _ rfl (Obj.codesC_fits C _ hzc) _ rfl
        (pickFits_of_fitsN B Ub _ hP _ (by simp)) hUbc
        -- `⊤`'s rows count the vacuous part as `topC` read it, which equals `vacY`'s by unfolding only
        (pickFits_of_fitsN B _ _ ha _ (by simp only [List.length_map, List.length_range]; exact Nat.le_refl _))
        (pickFits_of_fitsN C Uc _ hbc _ (by simp only [List.length_map, List.length_range]; exact Nat.le_refl _))
        _ _ rfl rfl hU hFk hFv (Obj.codesC_fits B _ hkc) (Obj.codesC_fits C _ hvc)
        (pickFits_of_fitsN B _ _ hkf _ (by simp only [List.length_range]; exact Nat.le_refl _))
        (pickFits_of_fitsN C _ _ hvf _ (by simp only [List.length_range]; exact Nat.le_refl _)) b c
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

end Rep

namespace CRel

open QLean QLean.Kernel LeetQ.Rel.Alg Freyd Freyd.Alg Freyd.Alg.RelSet LeetQ.Rel.Rep

variable {A B C D E : Obj}

/-- `R ≫ ¬ran(T)`, ok where both inputs are and `antiJoinC` ran within capacity. -/
def antiJoin (R : CRel A B) (T : CRel B B) : CRel A B := let r := antiJoinC R.rel T.rel; ⟨r.1, R.ok && T.ok && r.2⟩

/-- `⊤` on the universes `Ua`, `Ub`, ok where `topC` ran within capacity. -/
def top {ma mb : USize} (Ua : Vals A ma) (Ub : Vals B mb) : CRel A B := let r := topC Ua Ub; ⟨r.1, r.2⟩

/-- The coreflexive on the distinct elements of `x`, ok where `distinctCoreflC` ran within capacity. -/
def distinctCorefl (t : Obj) {n : USize} (x : Vals t n) : CRel t t := let r := distinctCoreflC t x; ⟨r.1, r.2⟩

/-- `dom R`, ok where `R` is and `domC` ran within capacity. -/
def dom (R : CRel A B) : CRel A A := let r := domC R.rel; ⟨r.1, R.ok && r.2⟩

/-- `ran R`, ok where `R` is and `ranC` ran within capacity. -/
def ran (R : CRel A B) : CRel B B := let r := ranC R.rel; ⟨r.1, R.ok && r.2⟩

/-- `Λ(R)`, ok where `R` is and `transposeC` ran within capacity. -/
def transpose (R : CRel A B) : CRel A (.arr B) := let r := transposeC R.rel; ⟨r.1, R.ok && r.2⟩

/-- `∋` on the arrays `X`, ok where `memC` ran within capacity. -/
def mem {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) B := let r := memC X; ⟨r.1, r.2⟩

/-- `⟨R, S⟩`, ok where both inputs are and `pairC` ran within capacity. -/
def pair (R : CRel A B) (S : CRel A C) : CRel A (.prod B C) := let r := pairC R.rel S.rel; ⟨r.1, R.ok && S.ok && r.2⟩

/-- The rows of `R` numbered from `k`, ok where `R` is and `numC` ran within capacity. -/
def num (R : CRel A B) (k : USize) : CRel .long B := let r := numC R.rel k; ⟨r.1, R.ok && r.2⟩

/-- `R × S`, ok where both inputs are and `prodC` ran within capacity. -/
def prod (R : CRel A B) (S : CRel D E) : CRel (.prod A D) (.prod B E) :=
  let r := prodC R.rel S.rel; ⟨r.1, R.ok && S.ok && r.2⟩

/-- `R \ S` on the universes `Ub`, `Uc`, ok where both inputs are and `leftDivC` ran within capacity. -/
def leftDiv {mb mc : USize} (R : CRel A B) (S : CRel A C) (Ub : Vals B mb) (Uc : Vals C mc) : CRel B C :=
  let r := leftDivC R.rel S.rel Ub Uc; ⟨r.1, R.ok && S.ok && r.2⟩

/-- `R / S` on the universes `Ua`, `Ub`, ok where both inputs are and `rightDivC` ran within capacity. -/
def rightDiv {ma mb : USize} (R : CRel A C) (S : CRel B C) (Ua : Vals A ma) (Ub : Vals B mb) : CRel A B :=
  let r := rightDivC R.rel S.rel Ua Ub; ⟨r.1, R.ok && S.ok && r.2⟩

theorem rep_leftDiv {mb mc : USize} (R : CRel A B) (S : CRel A C) (Ub : Vals B mb) (Uc : Vals C mc)
    (hb : (R.leftDiv S Ub Uc).ok = true) (b : B.El) (c : C.El) :
    rep (R.leftDiv S Ub Uc).rel b c ↔ (∀ a, rep R.rel a b → rep S.rel a c) ∧
      ((∃ a, rep R.rel a b) ∨ ((∃ p, Ub.row p = b) ∧ ∃ j, Uc.row j = c)) :=
  rep_leftDivC R.rel S.rel Ub Uc (by simp only [leftDiv, Bool.and_eq_true] at hb; exact hb.2) b c

theorem rep_rightDiv {ma mb : USize} (R : CRel C A) (S : CRel B A) (Ua : Vals C ma) (Ub : Vals B mb)
    (hb : (R.rightDiv S Ua Ub).ok = true) (x : C.El) (y : B.El) :
    rep (R.rightDiv S Ua Ub).rel x y ↔ (∀ c, rep S.rel y c → rep R.rel x c) ∧
      ((∃ c, rep S.rel y c) ∨ ((∃ p, Ua.row p = x) ∧ ∃ j, Ub.row j = y)) :=
  rep_rightDivC R.rel S.rel Ua Ub (by simp only [rightDiv, Bool.and_eq_true] at hb; exact hb.2) x y

theorem rep_antiJoin (R : CRel A B) (T : CRel B B) (hb : (R.antiJoin T).ok = true) :
    rep (R.antiJoin T).rel = rep R.rel ≫ corefl (A := (⟨B.El⟩ : RelSet.{0})) fun b => ¬ ∃ y, rep T.rel y b :=
  rep_antiJoinC R.rel T.rel (by simp only [antiJoin, Bool.and_eq_true] at hb; exact hb.2)

theorem rep_top {ma mb : USize} (Ua : Vals A ma) (Ub : Vals B mb) (hb : (top Ua Ub).ok = true) :
    rep (top Ua Ub).rel = corefl (A := (⟨A.El⟩ : RelSet.{0})) (fun a => ∃ i, Ua.row i = a) ≫
      relTop ≫ corefl (A := (⟨B.El⟩ : RelSet.{0})) (fun b => ∃ j, Ub.row j = b) :=
  rep_topC Ua Ub hb

theorem rep_distinctCorefl (t : Obj) {n : USize} (x : Vals t n) (hb : (distinctCorefl t x).ok = true) :
    rep (distinctCorefl t x).rel = corefl (A := (⟨t.El⟩ : RelSet.{0})) fun a => ∃ i, x.row i = a :=
  rep_distinctCoreflC t x hb

theorem rep_dom (R : CRel A B) (hb : R.dom.ok = true) : rep R.dom.rel = 𝟙 _ ∩ rep R.rel ≫ (rep R.rel)° :=
  rep_domC R.rel (by simp only [dom, Bool.and_eq_true] at hb; exact hb.2)

theorem rep_ran (R : CRel A B) (hb : R.ran.ok = true) : rep R.ran.rel = 𝟙 _ ∩ (rep R.rel)° ≫ (rep R.rel)°° :=
  rep_ranC R.rel (by simp only [ran, Bool.and_eq_true] at hb; exact hb.2)

theorem rep_transpose (R : CRel A B) (hb : R.transpose.ok = true) :
    (∀ a X, rep R.transpose.rel a X → ∀ x, x ∈ X ↔ rep R.rel a x) ∧
      (∀ a, (∃ X, rep R.transpose.rel a X) ↔ ∃ b, rep R.rel a b) :=
  rep_transposeC R.rel (by simp only [transpose, Bool.and_eq_true] at hb; exact hb.2)

theorem rep_mem {n : USize} (X : Vals (.arr B) n) (hb : (mem X).ok = true) (xs : (Obj.arr B).El) (x : B.El) :
    rep (mem X).rel xs x ↔ (∃ i, X.row i = xs) ∧ x ∈ xs :=
  rep_memC X hb xs x

theorem rep_pair (R : CRel A B) (S : CRel A C) (hb : (R.pair S).ok = true) :
    rep (R.pair S).rel = rpair (rep R.rel) (rep S.rel) :=
  rep_pairC R.rel S.rel (by simp only [pair, Bool.and_eq_true] at hb; exact hb.2)

theorem rep_num (R : CRel A B) (k : USize) (hb : (R.num k).ok = true) (a : Obj.long.El) (y : B.El) :
    rep (R.num k).rel a y ↔ ∃ i : Fin R.rel.n.toNat, a = Int64.ofNat (k.toNat + i.1) ∧ R.rel.val.row i = y :=
  rep_numC R.rel k (by simp only [num, Bool.and_eq_true] at hb; exact hb.2) a y

theorem rep_prod (R : CRel A B) (S : CRel D E) (hb : (R.prod S).ok = true) :
    rep (R.prod S).rel = rprodMap (rep R.rel) (rep S.rel) :=
  rep_prodC R.rel S.rel (by simp only [prod, Bool.and_eq_true] at hb; exact hb.2)

end CRel

end LeetQ.Rel
