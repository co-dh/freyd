/-
  What `Obj.raze` of two parts READS: row `k` of the razed side is row `k` of the first part below its count, and
  row `k - n` of the second past it — at every shape of side, one lemma per constructor of `Obj`, each taking the
  read-back of its components as a hypothesis, so a side's read-back is these lemmas composed along its shape.
  An atom's read-back is `razeTo`'s list (`razeTo_toList_bytes`, `_boolean`, `_general`); the encodings those do
  not cover stay as the atom lemma's one hypothesis `hA`.
-/
import LeetQ.Rel.RepOps

namespace LeetQ.Rel.KernelWF

open QLean QLean.Kernel QLean.Dep LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.Rep
open Freyd Freyd.Alg Freyd.Alg.RelSet

/-- A value moved along an equation is the value. -/
theorem ndrec_heq {α : Sort u} {φ : α → Sort v} {a b : α} (h : a = b) (x : φ a) :
    HEq (@Eq.ndrec α a φ x b h) x := by subst h; rfl

/-- A value moved back along a type equation is the value. -/
theorem mpr_heq {α β : Sort u} (h : α = β) (x : β) : HEq (Eq.mpr h x) x := by subst h; rfl

/-- `Obj.raze` of equal part arrays: one side. -/
theorem raze_heq {A : Obj} {cs cs' : Array (Part A)} (e : cs = cs')
    (h : (cs.toList.map fun c : Part A => c.1.toNat).sum < USize.size)
    (h' : (cs'.toList.map fun c : Part A => c.1.toNat).sum < USize.size) :
    HEq (A.raze cs h) (A.raze cs' h') := by subst e; rfl

/-- **Row read-back of `raze` at an atom**: the razed column's element `k` is the first part's below its count,
    the second's past it. `hA`: `razeTo`'s list is the parts' lists one after another (`razeTo2_bytes`,
    `_boolean`, `_general` discharge it). -/
theorem raze_row_atom {t : QAtomicType} {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size)
    (hA : (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList) (k : Nat)
    (hk : k < ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum.toUSize.toNat) :
    Vals.row ((Obj.atom t).raze #[⟨n, x⟩, ⟨m, y⟩] hN) ⟨k, hk⟩ =
      if h : k < n.toNat then Vals.row (A := .atom t) x ⟨k, h⟩
      else Vals.row (A := .atom t) y ⟨k - n.toNat, by have := raze2_cnt (X := .atom t) x y hN; omega⟩ := by
  have hc := raze2_cnt (X := .atom t) x y hN
  have hl : k < (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList.length := by
    rw [hA, List.length_append, Arr.length_toList, Arr.length_toList]; omega
  show Arr.get (razeTo t _ rfl hN) ⟨k, hk⟩ = _
  rw [← Arr.getElem_toList _ k hl]
  simp only [hA, List.getElem_append, Arr.length_toList, Vals.row_atom, Arr.getElem_toList]

/-- Two parts' `razeTo` list, from the `flatMap` the `razeTo_toList_*` lemmas conclude. -/
theorem razeTo2_toList {t : QAtomicType} {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size)
    (h : (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList =
      (#[⟨n, x⟩, ⟨m, y⟩] : Array ((k : USize) × Arr t k)).toList.flatMap (·.2.toList)) :
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList := by
  rw [h]; simp

/-- `raze_row_atom`'s `hA` at two dense parts (`razeTo_toList_bytes`). -/
theorem razeTo2_bytes {t : QAtomicType} {n m : USize} (x : Arr t n) (y : Arr t m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
      USize.size)
    (hx : ∃ b, x.enc = .bytes b) (hy : ∃ b, y.enc = .bytes b) :
    (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList :=
  razeTo2_toList x y hN (razeTo_toList_bytes _ rfl hN fun c hc => by
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hx
    · exact hy)

/-- `raze_row_atom`'s `hA` at `boolean` (`razeTo_toList_boolean`). -/
theorem razeTo2_boolean {n m : USize} (x : Arr .boolean n) (y : Arr .boolean m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom .boolean))).toList.map
      fun c : Part (.atom .boolean) => c.1.toNat).sum < USize.size) :
    (razeTo .boolean #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList :=
  razeTo2_toList x y hN (razeTo_toList_boolean _ rfl hN)

/-- `raze_row_atom`'s `hA` at `general` (`razeTo_toList_general`). -/
theorem razeTo2_general {n m : USize} (x : Arr .general n) (y : Arr .general m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom .general))).toList.map
      fun c : Part (.atom .general) => c.1.toNat).sum < USize.size) :
    (razeTo .general #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList :=
  razeTo2_toList x y hN (razeTo_toList_general _ rfl hN)

/-- **Row read-back of `raze` at a product**: each component razed on its own (`iha`, `ihb`). -/
theorem raze_row_prod {a b : Obj} {n m : USize} (x : Vals (.prod a b) n) (y : Vals (.prod a b) m)
    (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.prod a b))).toList.map fun c : Part (.prod a b) => c.1.toNat).sum <
      USize.size)
    (iha : ∀ hN' k hk, Vals.row (a.raze #[⟨n, x.1⟩, ⟨m, y.1⟩] hN') ⟨k, hk⟩ =
      if h : k < n.toNat then Vals.row x.1 ⟨k, h⟩
      else Vals.row y.1 ⟨k - n.toNat, by have := raze2_cnt x.1 y.1 hN'; omega⟩)
    (ihb : ∀ hN' k hk, Vals.row (b.raze #[⟨n, x.2⟩, ⟨m, y.2⟩] hN') ⟨k, hk⟩ =
      if h : k < n.toNat then Vals.row x.2 ⟨k, h⟩
      else Vals.row y.2 ⟨k - n.toNat, by have := raze2_cnt x.2 y.2 hN'; omega⟩) (k : Nat)
    (hk : k < ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.prod a b))).toList.map
      fun c : Part (.prod a b) => c.1.toNat).sum.toUSize.toNat) :
    Vals.row ((Obj.prod a b).raze #[⟨n, x⟩, ⟨m, y⟩] hN) ⟨k, hk⟩ =
      if h : k < n.toNat then Vals.row x ⟨k, h⟩
      else Vals.row y ⟨k - n.toNat, by have := raze2_cnt x y hN; omega⟩ := by
  have hc := raze2_cnt x y hN
  have ha : ((#[⟨n, x.1⟩, ⟨m, y.1⟩] : Array (Part a)).toList.map fun c : Part a => c.1.toNat).sum < USize.size := by
    simpa using hN
  have hb : ((#[⟨n, x.2⟩, ⟨m, y.2⟩] : Array (Part b)).toList.map fun c : Part b => c.1.toNat).sum < USize.size := by
    simpa using hN
  have hka : k < ((#[⟨n, x.1⟩, ⟨m, y.1⟩] : Array (Part a)).toList.map fun c : Part a => c.1.toNat).sum.toUSize.toNat := by
    rw [raze2_cnt x.1 y.1 ha]; omega
  have hkb : k < ((#[⟨n, x.2⟩, ⟨m, y.2⟩] : Array (Part b)).toList.map fun c : Part b => c.1.toNat).sum.toUSize.toNat := by
    rw [raze2_cnt x.2 y.2 hb]; omega
  rw [Obj.raze.eq_2, Vals.row.eq_2]
  refine Eq.trans (b := (Vals.row (a.raze #[⟨n, x.1⟩, ⟨m, y.1⟩] ha) ⟨k, hka⟩,
    Vals.row (b.raze #[⟨n, x.2⟩, ⟨m, y.2⟩] hb) ⟨k, hkb⟩)) (Prod.ext ?_ ?_) ?_
  any_goals
    apply row_heq
    all_goals first | rfl | skip
  case refine_1.hvw =>
    dsimp only
    first
      | exact HEq.trans (ndrec_heq (φ := fun S : Nat => Vals a S.toUSize) _ _) (raze_heq (by simp) _ _)
      | exact HEq.trans (eqRec_heq (φ := fun S : Nat => Vals a S.toUSize) _ _) (raze_heq (by simp) _ _)
      | exact HEq.trans (ndrec_heq (φ := fun S : Nat => Vals a S.toUSize) _ _) (raze_heq rfl _ _)
  case refine_2.hvw =>
    dsimp only
    first
      | exact HEq.trans (ndrec_heq (φ := fun S : Nat => Vals b S.toUSize) _ _) (raze_heq (by simp) _ _)
      | exact HEq.trans (eqRec_heq (φ := fun S : Nat => Vals b S.toUSize) _ _) (raze_heq (by simp) _ _)
      | exact HEq.trans (ndrec_heq (φ := fun S : Nat => Vals b S.toUSize) _ _) (raze_heq rfl _ _)
  rw [iha ha k hka, ihb hb k hkb]
  by_cases h : k < n.toNat
  · simp only [dif_pos h]; rfl
  · simp only [dif_neg h]; rfl

end LeetQ.Rel.KernelWF

namespace LeetQ.Rel.Rep

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet

variable {A B : Obj}

/-! The relation `∪` razes before its `nub`, and that relation's codes and first rows, named as `rep_nub` names
    them; one home: `open RazeN` in every file that reads them. Unhygienic: they capture `A`, `B`, `R`, `S`, `hNk`,
    `hNv`. Not in `UnionN`, whose users keep `Uc` free as a name. -/
namespace RazeN
set_option hygiene false in
scoped notation "Uc" => (⟨_, A.raze #[⟨R.n, R.key⟩, ⟨S.n, S.key⟩] hNk, B.raze #[⟨R.n, R.val⟩, ⟨S.n, S.val⟩] hNv⟩ : Rel A B)
set_option hygiene false in
scoped notation "kcU" => (Obj.codes A (#v[⟨(Uc).n, (Uc).key⟩] : Vector (Part A) 1))[0]'Nat.zero_lt_one
set_option hygiene false in
scoped notation "vcU" => (Obj.codes B (#v[⟨(Uc).n, (Uc).val⟩] : Vector (Part B) 1))[0]'Nat.zero_lt_one
set_option hygiene false in
scoped notation "nubU" => (tuples.tupleIds kcU #[vcU]).2
end RazeN
open RazeN

/-- `∪` within the fits bound: the `nub` of the razed relation. -/
theorem union_eq_nub (R S : Rel A B) (hN : R.n.toNat + S.n.toNat < USize.size)
    (hNk : ((#[⟨R.n, R.key⟩, ⟨S.n, S.key⟩] : Array (Part A)).toList.map fun c : Part A => c.1.toNat).sum <
      USize.size)
    (hNv : ((#[⟨R.n, R.val⟩, ⟨S.n, S.val⟩] : Array (Part B)).toList.map fun c : Part B => c.1.toNat).sum <
      USize.size) :
    R ∪ S = (Uc).nub := by
  show need _ _ _ _ = _
  unfold need; rw [dif_pos hN]

/-- **`rep (R ∪ S) = rep R ∪ rep S`**: `∪` razes the keys and the values, read back by `hA`, `hB`, so the razed
    relation holds the pairs of `R` and of `S` (`holds_two`), and its `nub` holds the same (`rep_nub`, whose code
    hypotheses `hK`, `hV`, `hk`, `hv` are stated on the razed relation). `hN`: the row count fits a `USize`
    (past it `∪` answers `𝟘`); `hNk`, `hNv`: the same count, as the two `raze`s state it. -/
theorem rep_union (R S : Rel A B) (hN : R.n.toNat + S.n.toNat < USize.size)
    (hNk : ((#[⟨R.n, R.key⟩, ⟨S.n, S.key⟩] : Array (Part A)).toList.map fun c : Part A => c.1.toNat).sum <
      USize.size)
    (hNv : ((#[⟨R.n, R.val⟩, ⟨S.n, S.val⟩] : Array (Part B)).toList.map fun c : Part B => c.1.toNat).sum <
      USize.size)
    (hA : ∀ k hk, Vals.row (A.raze #[⟨R.n, R.key⟩, ⟨S.n, S.key⟩] hNk) ⟨k, hk⟩ =
      if h : k < R.n.toNat then Vals.row R.key ⟨k, h⟩
      else Vals.row S.key ⟨k - R.n.toNat, by have := raze2_cnt R.key S.key hNk; omega⟩)
    (hB : ∀ k hk, Vals.row (B.raze #[⟨R.n, R.val⟩, ⟨S.n, S.val⟩] hNv) ⟨k, hk⟩ =
      if h : k < R.n.toNat then Vals.row R.val ⟨k, h⟩
      else Vals.row S.val ⟨k - R.n.toNat, by have := raze2_cnt R.val S.val hNv; omega⟩)
    (hK : (∀ {i j : Nat} (hi : i < (Uc).n.toNat) (hj : j < (Uc).n.toNat),
        Column.idAt (kcU).b (kcU).w i = Column.idAt (kcU).b (kcU).w j ↔
          Vals.row (Uc).key ⟨i, hi⟩ = Vals.row (Uc).key ⟨j, hj⟩) ∧
      ((kcU).w = 1 ∨ (kcU).w = 2 ∨ (kcU).w = 4 ∨ (kcU).w = 8 ∨ (kcU).w = 16 ∨ (kcU).w = 32 ∨ (kcU).w = 64) ∧
        (kcU).n = (Uc).n ∧ (kcU).b.size = ((kcU).n.toNat * (kcU).w + 7) / 8 ∧
        ((kcU).w < 8 → (kcU).card < USize.size ∧ ∀ i < (kcU).n.toNat, Column.idAt (kcU).b (kcU).w i < (kcU).card))
    (hV : (∀ {i j : Nat} (hi : i < (Uc).n.toNat) (hj : j < (Uc).n.toNat),
        Column.idAt (vcU).b (vcU).w i = Column.idAt (vcU).b (vcU).w j ↔
          Vals.row (Uc).val ⟨i, hi⟩ = Vals.row (Uc).val ⟨j, hj⟩) ∧
      ((vcU).w = 1 ∨ (vcU).w = 2 ∨ (vcU).w = 4 ∨ (vcU).w = 8 ∨ (vcU).w = 16 ∨ (vcU).w = 32 ∨ (vcU).w = 64) ∧
        (vcU).n = (Uc).n ∧ (vcU).b.size = ((vcU).n.toNat * (vcU).w + 7) / 8 ∧
        ((vcU).w < 8 → (vcU).card < USize.size ∧ ∀ i < (vcU).n.toNat, Column.idAt (vcU).b (vcU).w i < (vcU).card))
    (hk : Vals.PickFits A (Uc).key (ids nubU)) (hv : Vals.PickFits B (Uc).val (ids nubU)) :
    rep (R ∪ S) = rep R ∪ rep S := by
  rw [union_eq_nub R S hN hNk hNv, rep_nub (Uc) hK hV hk hv]
  have hn : (Uc).n.toNat = R.n.toNat + S.n.toNat := raze2_cnt R.key S.key hNk
  refine hom_ext fun a b => ?_
  rw [union_apply]
  exact holds_two (Uc).key (Uc).val R S hn (fun k hk => hA k hk) (fun k hk => hB k hk) a b

#print axioms rep_union

/-- `rep_union` at boolean sides: the razed sides read back by `razeTo2_boolean`, the razed relation's codes are
    its bits (`codes_boolean_faithful`/`_wf`), and `nub` picks its rows only (`nub_mem`, `pickFits_atom`). -/
theorem rep_union_boolean (R S : Rel (.atom .boolean) (.atom .boolean)) (hN : R.n.toNat + S.n.toNat < USize.size) :
    rep (R ∪ S) = rep R ∪ rep S := by
  have hNk : ((#[⟨R.n, R.key⟩, ⟨S.n, S.key⟩] : Array (Part (.atom .boolean))).toList.map
      fun c : Part (.atom .boolean) => c.1.toNat).sum < USize.size := by simpa using hN
  have hNv : ((#[⟨R.n, R.val⟩, ⟨S.n, S.val⟩] : Array (Part (.atom .boolean))).toList.map
      fun c : Part (.atom .boolean) => c.1.toNat).sum < USize.size := by simpa using hN
  refine rep_union R S hN hNk hNv (raze_row_atom R.key S.key hNk (razeTo2_boolean _ _ hNk))
    (raze_row_atom R.val S.val hNv (razeTo2_boolean _ _ hNv)) ?hK ?hV
    (pickFits_atom _ fun _ hp => ((nub_mem _ ?hK ?hV).1 hp).1) (pickFits_atom _ fun _ hp => ((nub_mem _ ?hK ?hV).1 hp).1)
  case hK => exact ⟨fun hi hj => codes_boolean_faithful _ (k := 0) (l := 0) (by decide) (by decide) hi hj,
    by have h := codes_boolean_wf (#v[⟨_, (Obj.atom .boolean).raze #[⟨R.n, R.key⟩, ⟨S.n, S.key⟩] hNk⟩] :
           Vector (Part _) 1) (k := 0) (by decide)
       exact ⟨Or.inl h.2.1, h.1, h.2.2.1, h.2.2.2⟩⟩
  case hV => exact ⟨fun hi hj => codes_boolean_faithful _ (k := 0) (l := 0) (by decide) (by decide) hi hj,
    by have h := codes_boolean_wf (#v[⟨_, (Obj.atom .boolean).raze #[⟨R.n, R.val⟩, ⟨S.n, S.val⟩] hNv⟩] :
           Vector (Part _) 1) (k := 0) (by decide)
       exact ⟨Or.inl h.2.1, h.1, h.2.2.1, h.2.2.2⟩⟩

/-- `rep_junc` at a boolean value side: the razed values read back by `razeTo2_boolean`. -/
theorem rep_junc_boolean (R : Rel A (.atom .boolean)) (S : Rel B (.atom .boolean))
    (hN : R.n.toNat + S.n.toNat < USize.size) (h63 : R.n.toNat + S.n.toNat ≤ 2 ^ 63) :
    rep (LeetQ.Rel.Alg.junc R S) = Freyd.Alg.junc (sumCop (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩) (rep R) (rep S) :=
  rep_junc R S hN h63 fun hN' => raze_row_atom R.val S.val hN' (razeTo2_boolean _ _ hN')

#print axioms rep_union_boolean
#print axioms rep_junc_boolean

end LeetQ.Rel.Rep
