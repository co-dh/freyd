/-
  `rep` of the second group of `Alg` ops: each executable op read in `Rel(Set)`, as `RepOps` does the first.
-/
import LeetQ.Rel.RepOps

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF
open Freyd Freyd.Alg Freyd.Alg.RelSet

variable {A B : Obj}

-- codes `cs` of two parts `ps` faithful and well formed, `RepOps`' `codesOK` (a local notation, so restated here)
set_option hygiene false in
local notation "codesOK(" cs ", " ps ")" => ((∀ {k l : Nat} (hk : k < 2) (hl : l < 2) {i j : Nat}
    (hi : i < (ps[k]'hk).1.toNat) (hj : j < (ps[l]'hl).1.toNat),
    Column.idAt (cs[k]'hk).b (cs[k]'hk).w i = Column.idAt (cs[l]'hl).b (cs[l]'hl).w j ↔
      Vals.row (ps[k]'hk).2 ⟨i, hi⟩ = Vals.row (ps[l]'hl).2 ⟨j, hj⟩) ∧
  ∀ {k : Nat} (hk : k < 2),
    ((cs[k]'hk).w = 1 ∨ (cs[k]'hk).w = 2 ∨ (cs[k]'hk).w = 4 ∨ (cs[k]'hk).w = 8 ∨ (cs[k]'hk).w = 16 ∨
      (cs[k]'hk).w = 32 ∨ (cs[k]'hk).w = 64) ∧
    (cs[k]'hk).n = (ps[k]'hk).1 ∧ (cs[k]'hk).b.size = ((cs[k]'hk).n.toNat * (cs[k]'hk).w + 7) / 8 ∧
    ((cs[k]'hk).w < 8 → (cs[k]'hk).card < USize.size ∧
      ∀ i < (cs[k]'hk).n.toNat, Column.idAt (cs[k]'hk).b (cs[k]'hk).w i < (cs[k]'hk).card))

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
  anti ((avc(B, R, T))[0]'(by decide)) ((avc(B, R, T))[1]'(by decide))

/-- Row `i` of `R` is marked by `member` on the joint value codes exactly when its value is a value of `T`. -/
theorem vals_member (R : Rel A B) (T : Rel B B) (hc : codesOK(avc(B, R, T), avp(B, R, T))) {i : Nat}
    (hi : i < R.n.toNat) :
    Column.bitAt (((avc(B, R, T))[0]'(by decide)).member ((avc(B, R, T))[1]'(by decide))) i = true ↔
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
    replace hn0 : ((avc(B, R, T))[0]'(by decide)).n = R.n := hn0
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
  rep_antiJoin_atoms R T ⟨fun hk hl _ _ hi hj => codes_boolean_faithful _ hk hl hi hj, fun hk =>
    have h := codes_boolean_wf avp(.atom .boolean, R, T) hk
    ⟨Or.inl h.2.1, h.1, h.2.2.1, h.2.2.2⟩⟩

end AntiJoin

#print axioms rep_antiJoin
#print axioms rep_antiJoin_boolean

end LeetQ.Rel.Rep
