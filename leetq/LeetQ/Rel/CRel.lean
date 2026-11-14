/-
  Capacity checked at run time, correctness proved: an op's twin `compC`/`interC`/`unionC` answers its relation
  and a bit, the bit deciding every count bound the op's read-back theorem takes, so `rep_compC`/`rep_interC`/
  `rep_unionC` hold under that one bit. `CRel` carries the bit along a program, each op `&&`-ing its inputs' bits
  with its own.
-/
import LeetQ.Rel.KernelWF.CodesAll
import LeetQ.Rel.KernelWF.RazeRowAll

namespace LeetQ.Rel

/-- A relation and whether every op that built it ran within capacity. -/
structure CRel (k v : Obj) where
  rel : Rel k v
  ok : Bool

namespace Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet
open CompN OpsN

variable {A B C : Obj}

/-- **`rep (R ≫ S) = rep R ≫ rep S` under `compC`'s bit**: the codes' bit gives `rep_comp`'s `hc`
    (`codesC_fits`, `codes_faithful_wf`), the decided bounds its `hrn`, `hM`, and the picks' bits, read at the
    join's rows (`join_rows`), its `hA`, `hC` (`pickC_fits`). -/
theorem rep_compC (R : Rel A B) (S : Rel B C) (hb : (compC R S).2 = true) :
    rep (compC R S).1 = rep R ≫ rep S := by
  rw [compC_fst]
  simp only [compC, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hcb, hrn⟩, hM⟩, hp⟩ := hb
  have hc := (codes_faithful_wf B _ (Obj.codesC_fits B _ hcb)).1
  obtain ⟨hlw, hln, hls, -⟩ := hc.2 (k := 0) (by decide)
  obtain ⟨hrw, hrn', hrs, hrc⟩ := hc.2 (k := 1) (by decide)
  replace hln : (jc[0]'Nat.zero_lt_two).n = R.n := hln
  replace hrn' : (jc[1]'Nat.one_lt_two).n = S.n := hrn'
  have hcf : (B.codesC jcs).1 = jc := by cases B <;> rfl
  -- `join_rows` on the codes `compC` joins, named as `compC` names them: a defeq check through them evaluates `join`
  rw [← hcf] at hlw hls hrw hrs hrc hln hrn'
  obtain ⟨-, hZ⟩ := join_rows _ _ hlw hls hrw hrs hrc (by rw [hrn']; exact hrn) (by rw [hln, hrn']; exact hM)
  unfold longCount need at hp
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
    exact rep_comp R S hc hrn hM hA hC
  · exact absurd hp Bool.false_ne_true

#print axioms rep_compC

/-- **`rep (R ∩ S) = rep R ∩ rep S` under `interC`'s bit**: the product codes' bit gives `rep_inter`'s `hc`
    (`codesC_fits`, `codes_faithful_wf`, `pairs_eq_codes`), the `fitsN` bits its `hk`, `hv` (`pickFits_of_fitsN`). -/
theorem rep_interC (R S : Rel A B) (hb : (interC R S).2 = true) : rep (interC R S).1 = rep R ∩ rep S := by
  rw [interC_fst]
  simp only [interC, Bool.and_eq_true] at hb
  obtain ⟨⟨hcb, hk⟩, hv⟩ := hb
  have hc := (codes_faithful_wf (.prod A B) _ (Obj.codesC_fits (.prod A B) _ hcb)).1
  have e : ∀ {α β : Type} (f : α → β) (a b : α), #v[a, b].map f = #v[f a, f b] := fun _ _ _ => by simp
  have hp : pairsOK(R, S) := by rw [pairs_eq_codes, e]; exact hc
  exact rep_inter R S hp (pickFits_of_fitsN A R.key _ hk _ (by simp)) (pickFits_of_fitsN B R.val _ hv _ (by simp))

#print axioms rep_interC

/-- **`rep (R ∪ S) = rep R ∪ rep S` under `unionC`'s bit**: `need`'s guard is `rep_union`'s `hN`, the razes' bits
    its `hA`, `hB` (`razeC_fits`, `raze_row`), the codes' bits its `hK`, `hV` (`codesC_fits`, `codes_faithful_wf`),
    the `fitsN` bits its `hk`, `hv` (`pickFits_of_fitsN`). -/
theorem rep_unionC
    -- not a size bound: `razeTo`'s read-back of two atom parts, proved only at the encodings `razeTo2_fits` covers
    (hat : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
      (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
        USize.size), Vals.RazeFits (.atom t) x y →
      (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
    (R S : Rel A B) (hb : (unionC R S).2 = true) : rep (unionC R S).1 = rep R ∪ rep S := by
  rw [unionC_fst]
  unfold unionC need at hb
  split at hb
  · rename_i hN
    simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨⟨⟨⟨hka, hvb⟩, hkc⟩, hvc⟩, hkf⟩, hvf⟩ := hb
    have hFa := Obj.razeC_fits A R.key S.key _ rfl _ hka
    have hFb := Obj.razeC_fits B R.val S.val _ rfl _ hvb
    -- a raze twin's `.1` is `raze` at each constructor of the side
    have hr : ∀ (X : Obj) (cs : Array (Part X)) h, (X.razeC cs h).1 = X.raze cs h := by
      intro X; cases X <;> intros <;> rfl
    simp only [hr] at hkc hvc hkf hvf
    have hK := (codes_faithful_wf A _ (Obj.codesC_fits A _ hkc)).1
    have hV := (codes_faithful_wf B _ (Obj.codesC_fits B _ hvc)).1
    exact rep_union R S hN (fun k hk => raze_row hat A R.key S.key hFa _ k hk)
      (fun k hk => raze_row hat B R.val S.val hFb _ k hk)
      ⟨fun hi hj => hK.1 (k := 0) (l := 0) Nat.zero_lt_one Nat.zero_lt_one hi hj, hK.2 (k := 0) Nat.zero_lt_one⟩
      ⟨fun hi hj => hV.1 (k := 0) (l := 0) Nat.zero_lt_one Nat.zero_lt_one hi hj, hV.2 (k := 0) Nat.zero_lt_one⟩
      (pickFits_of_fitsN A _ _ hkf _ (by simp)) (pickFits_of_fitsN B _ _ hvf _ (by simp))
  · exact absurd hb Bool.false_ne_true

#print axioms rep_unionC

end Rep

namespace CRel

open QLean QLean.Kernel LeetQ.Rel.Alg Freyd Freyd.Alg.RelSet LeetQ.Rel.Rep

variable {A B C : Obj}

/-- `R ≫ S`, ok where both inputs are and `compC` ran within capacity. -/
def comp (R : CRel A B) (S : CRel B C) : CRel A C := let r := compC R.rel S.rel; ⟨r.1, R.ok && S.ok && r.2⟩

/-- `R ∩ S`, ok where both inputs are and `interC` ran within capacity. -/
def inter (R S : CRel A B) : CRel A B := let r := interC R.rel S.rel; ⟨r.1, R.ok && S.ok && r.2⟩

/-- `R ∪ S`, ok where both inputs are and `unionC` ran within capacity. -/
def union (R S : CRel A B) : CRel A B := let r := unionC R.rel S.rel; ⟨r.1, R.ok && S.ok && r.2⟩

theorem rep_comp (R : CRel A B) (S : CRel B C) (hb : (R.comp S).ok = true) :
    rep (R.comp S).rel = rep R.rel ≫ rep S.rel :=
  rep_compC R.rel S.rel (by simp only [comp, Bool.and_eq_true] at hb; exact hb.2)

theorem rep_inter (R S : CRel A B) (hb : (R.inter S).ok = true) : rep (R.inter S).rel = rep R.rel ∩ rep S.rel :=
  rep_interC R.rel S.rel (by simp only [inter, Bool.and_eq_true] at hb; exact hb.2)

/-- `hat`: `rep_unionC`'s. -/
theorem rep_union
    (hat : ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
      (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
        USize.size), Vals.RazeFits (.atom t) x y →
      (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList)
    (R S : CRel A B) (hb : (R.union S).ok = true) : rep (R.union S).rel = rep R.rel ∪ rep S.rel :=
  rep_unionC hat R.rel S.rel (by simp only [union, Bool.and_eq_true] at hb; exact hb.2)

end CRel

end LeetQ.Rel
