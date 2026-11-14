/-
  `rep (R ≫ S) = rep R ≫ rep S` through a middle side whose joint codes read the raze of `R.val` and `S.key`
  back (`raze_get`): a small integral, float or `guid` side, in any encoding. Above `RazeFoR`, which `RepComp`
  sits below.
-/
import LeetQ.Rel.RepComp
import LeetQ.Rel.KernelWF.CodesNumParts
import LeetQ.Rel.KernelWF.CodesGuidParts

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg CompN Freyd Freyd.Alg.RelSet

variable {A C : Obj}

/-- `rep_comp` through a small integral or float middle side (`byte`, `char`, `short`, the four-byte types,
    `real`, `float`, `datetime`) in any encoding, the two counts summing below a `USize`, below `2^32` at a
    float side, where an ALP join offsets them (`codes_dense_faithful_wf`). -/
theorem rep_comp_dense {t : QAtomicType} {k₀ : Scan.Kind} (ht : orderKind t = some k₀)
    (hk₀ : k₀ = .u8 ∨ k₀ = .i16 ∨ k₀ = .i32 ∨ k₀ = .f32 ∨ k₀ = .f64) (R : Rel A (.atom t)) (S : Rel (.atom t) C)
    (hN : R.n.toNat + S.n.toNat < USize.size) (h32 : Column.alpEncodes t = true → R.n.toNat + S.n.toNat < 2 ^ 32)
    (hrn : S.n.toNat < 2 ^ 63)
    (hM : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt (jc[1]'Nat.one_lt_two).b (jc[1]'Nat.one_lt_two).w j ==
        Column.idAt (jc[0]'Nat.zero_lt_two).b (jc[0]'Nat.zero_lt_two).w i).length).sum < 2 ^ 63)
    (hMU : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt (jc[1]'Nat.one_lt_two).b (jc[1]'Nat.one_lt_two).w j ==
        Column.idAt (jc[0]'Nat.zero_lt_two).b (jc[0]'Nat.zero_lt_two).w i).length).sum < USize.size)
    (hA : Vals.PickFits A R.key ((jpairs).map Prod.fst)) (hC : Vals.PickFits C S.val ((jpairs).map Prod.snd)) :
    rep (R ≫ S) = rep R ≫ rep S :=
  have hN' : ((jcs).toList.map (·.1.toNat)).sum < USize.size := by simpa using hN
  have hc := codes_dense_faithful_wf ht hk₀ _ hN' fun _ h => by simpa using h32 h
  rep_comp R S ⟨fun {_ _} hk hl {_ _} hi hj => hc.1.1 hk hl hi hj, fun hk => hc.1.2 hk⟩ hrn hM hMU hA hC

/-- `rep_comp` through a `guid` middle side, the two counts summing below a `USize`
    (`codes_guid_parts_faithful`/`_wf`). -/
theorem rep_comp_guid (R : Rel A (.atom .guid)) (S : Rel (.atom .guid) C) (hN : R.n.toNat + S.n.toNat < USize.size)
    (hrn : S.n.toNat < 2 ^ 63)
    (hM : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt (jc[1]'Nat.one_lt_two).b (jc[1]'Nat.one_lt_two).w j ==
        Column.idAt (jc[0]'Nat.zero_lt_two).b (jc[0]'Nat.zero_lt_two).w i).length).sum < 2 ^ 63)
    (hMU : ((List.range R.n.toNat).map fun i => ((List.range S.n.toNat).filter fun j =>
      Column.idAt (jc[1]'Nat.one_lt_two).b (jc[1]'Nat.one_lt_two).w j ==
        Column.idAt (jc[0]'Nat.zero_lt_two).b (jc[0]'Nat.zero_lt_two).w i).length).sum < USize.size)
    (hA : Vals.PickFits A R.key ((jpairs).map Prod.fst)) (hC : Vals.PickFits C S.val ((jpairs).map Prod.snd)) :
    rep (R ≫ S) = rep R ≫ rep S :=
  have hN' : ((jcs).toList.map (·.1.toNat)).sum < USize.size := by simpa using hN
  rep_comp R S ⟨fun {_ _} hk hl {_ _} hi hj => codes_guid_parts_faithful _ hN' hk hl hi hj,
    fun hk => codes_guid_parts_wf _ hN' hk⟩ hrn hM hMU hA hC

end LeetQ.Rel.Rep

#print axioms LeetQ.Rel.Rep.rep_comp_dense
#print axioms LeetQ.Rel.Rep.rep_comp_guid
