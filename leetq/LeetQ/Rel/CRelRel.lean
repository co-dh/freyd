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
  rw [distinctCoreflC_fst]
  simp only [distinctCoreflC, Bool.and_eq_true] at hb
  exact rep_distinctCorefl t x (oneOK_of_codesC t x hb.1) (pickFits_of_fitsN t x _ hb.2 _ (by simp))

/-- **`rep (dom R) = 𝟙 ∩ rep R (rep R)°` under `domC`'s bit**: `rep_dom`'s premises as `rep_distinctCoreflC`'s. -/
theorem rep_domC (R : Rel A B) (hb : (domC R).2 = true) : rep (domC R).1 = 𝟙 _ ∩ rep R ≫ (rep R)° := by
  rw [show (domC R).1 = dom R from distinctCoreflC_fst A R.key]
  simp only [domC, distinctCoreflC, Bool.and_eq_true] at hb
  exact rep_dom R (oneOK_of_codesC A R.key hb.1) (pickFits_of_fitsN A R.key _ hb.2 _ (by simp))

/-- **`rep (ran R) = 𝟙 ∩ (rep R)° (rep R)°°` under `ranC`'s bit**: `rep_ran`'s premises as `rep_domC`'s. -/
theorem rep_ranC (R : Rel A B) (hb : (ranC R).2 = true) : rep (ranC R).1 = 𝟙 _ ∩ (rep R)° ≫ (rep R)°° := by
  rw [show (ranC R).1 = ran R from distinctCoreflC_fst B R.val]
  simp only [ranC, distinctCoreflC, Bool.and_eq_true] at hb
  exact rep_ran R (oneOK_of_codesC B R.val hb.1) (pickFits_of_fitsN B R.val _ hb.2 _ (by simp))

/-- **`rep (antiJoin R T) = rep R ≫ ¬ran(rep T)` under `antiJoinC`'s bit**: the joint codes' bit gives `hc`
    (`codesC_fits`, `codes_faithful_wf`), the `fitsN` bits `hk`, `hv`. -/
theorem rep_antiJoinC (R : Rel A B) (T : Rel B B) (hb : (antiJoinC R T).2 = true) :
    rep (antiJoinC R T).1 = rep R ≫ corefl (A := (⟨B.El⟩ : RelSet.{0})) fun b => ¬ ∃ y, rep T y b := by
  rw [antiJoinC_fst]
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

/-- **`rep (mem X) xs x ↔ xs is a cell of X ∧ x ∈ xs` under `memC`'s bit**: the `fitsN` bit gives `hv`, and with it
    `expand`'s guard (`slicesOf_copies`); the keys' pick bit, at the copies `expand` makes, `hk` (`pickC_fits`,
    `copies_rows`). -/
theorem rep_memC {n : USize} (X : Vals (.arr B) n) (hb : (memC X).2 = true) (xs : (Obj.arr B).El) (x : B.El) :
    rep (memC X).1 xs x ↔ (∃ i, X.row i = xs) ∧ x ∈ xs := by
  rw [memC_fst]
  simp only [memC, Bool.and_eq_true] at hb
  obtain ⟨hk, hv⟩ := hb
  have hv' := pickFits_of_fitsN (.arr B) X _ hv _ (by simp)
  refine rep_mem X hv' ?_ xs x
  unfold expand need at hk
  dsimp only at hk
  rw [dif_pos (slicesOf_copies X hv').1] at hk
  rw [← copies_rows X hv']
  exact Vals.pickC_fits (.arr B) X _ _ _ hk

-- the keys `pair` codes jointly, named as `pairC` names them
set_option hygiene false in
local notation "pcs" => (#v[⟨R.n, R.key⟩, ⟨S.n, S.key⟩] : Vector (Part A) 2)

/-- **`rep ⟨R, S⟩ = ⟨rep R, rep S⟩` under `pairC`'s bit**, as `rep_compC`: the codes' bit gives `hc`, the decided
    bounds `hrn`, `hM`, and the picks' bits, read at the join's rows (`join_rows`), `hA`, `hB`, `hC`. -/
theorem rep_pairC (R : Rel A B) (S : Rel A C) (hb : (pairC R S).2 = true) :
    rep (pairC R S).1 = rpair (rep R) (rep S) := by
  rw [pairC_fst]
  simp only [pairC, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hcb, hrn⟩, hM⟩, hp⟩ := hb
  have hc := (codes_faithful_wf A _ (Obj.codesC_fits A _ hcb)).1
  obtain ⟨hlw, hln, hls, -⟩ := hc.2 (k := 0) (by decide)
  obtain ⟨hrw, hrn', hrs, hrc⟩ := hc.2 (k := 1) (by decide)
  replace hln : ((A.codes pcs)[0]'Nat.zero_lt_two).n = R.n := hln
  replace hrn' : ((A.codes pcs)[1]'Nat.one_lt_two).n = S.n := hrn'
  have hcf := Obj.codesC_fst A pcs
  rw [← hcf] at hlw hls hrw hrs hrc hln hrn'
  obtain ⟨-, hZ⟩ := join_rows _ _ hlw hls hrw hrs hrc (by rw [hrn']; exact hrn) (by rw [hln, hrn']; exact hM)
  unfold longCount need at hp
  split at hp
  · rename_i hlt
    simp only [Bool.and_eq_true] at hp
    have e := hZ _ (USize.toNat_ofNat_of_lt' hlt).symm
    have hfA := Vals.pickC_fits A R.key _ _ _ hp.1.1
    have hfB := Vals.pickC_fits B R.val _ _ _ hp.1.2
    have hfC := Vals.pickC_fits C S.val _ _ _ hp.2
    rw [hln, hrn'] at e
    rw [hcf] at e hfA hfB hfC
    exact rep_pair R S hc hrn hM (by rw [e, List.map_map]; exact hfA) (by rw [e, List.map_map]; exact hfB)
      (by rw [e, List.map_map]; exact hfC)
  · exact absurd hp Bool.false_ne_true

/-- **`rep (Λ(R))` is the power transpose of `rep R` under `transposeC`'s bit**: `nub`'s codes' bits give `hK`, `hV`
    (`oneOK_of_codesC`), the `fitsN` bits `hk`, `hv`, the nub sides' codes bits `hWk`, `hW` (`codesC_fits`), the
    decided count `h63`. -/
theorem rep_transposeC (R : Rel A B) (hb : (transposeC R).2 = true) :
    (∀ a X, rep (transposeC R).1 a X → ∀ x, x ∈ X ↔ rep R a x) ∧
      (∀ a, (∃ X, rep (transposeC R).1 a X) ↔ ∃ b, rep R a b) := by
  rw [transposeC_fst]
  simp only [transposeC, Obj.codesC_fst, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨hK, hV⟩, hk⟩, hv⟩, hWk⟩, hW⟩, h63⟩ := hb
  exact rep_transpose R (oneOK_of_codesC A R.key hK) (oneOK_of_codesC B R.val hV)
    (pickFits_of_fitsN A R.key _ hk _ (by simp)) (pickFits_of_fitsN B R.val _ hv _ (by simp))
    (Obj.codesC_fits A _ hWk) (Obj.codesC_fits B _ hW) h63

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
