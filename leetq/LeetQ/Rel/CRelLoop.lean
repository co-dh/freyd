/-
  The runtime ok-bit on the iterative composites `suffix`, `loopOn`/`loop` and on `tic`: an iterative op's round
  answers its new state and a bit, the `&&` of its pieces' twins' bits; `iterC` carries the `&&` of the rounds it
  ran, and `iterC_run` reads each run round's bit back. The proofs use only the rounds `iter` ran (`done` failing
  up to them): each such round's read-back comes from its pieces' `rep_<op>C`. What stays is not a size bound:
  a step's spec (`loopOn`'s `F`, at the rounds whose step bit is set) and `unionC`'s `hat`.
-/
import LeetQ.Rel.CRelFold
import LeetQ.Rel.CRelList
import LeetQ.Rel.RepLoop
import LeetQ.Rel.RepMerge

namespace LeetQ.Rel

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet
open LeetQ.Rel.Rep LeetQ.Rel.Rep.FoldN LeetQ.Rel.Rep.OpsN LeetQ.Rel.Rep.Prim LeetQ.Rel.Rep.ListN

-- `unionC`'s `hat`: `razeTo`'s read-back of two atom parts, not a size bound
set_option quotPrecheck false in
local notation "hatOK" => ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
  (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
    USize.size), Vals.RazeFits (.atom t) x y → (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList

namespace Rep

/-- **`tic` under `ticC`'s bit**: `tic_of` at its pieces' read-backs, `rep_consC`, `rep_compC`, `rep_initsC`,
    `rep_tailC`. -/
theorem rep_ticC {K B : Obj} (P : Rel K (.prod B (.arr B))) (hb : (ticC P).2 = true) :
    ∀ k zss, rep (ticC P).1 k zss ↔ ∃ b bs, rep P k (b, bs) ∧
      zss = (List.range (bs.length + 1)).map fun j => (b :: bs).take (j + 1) := by
  simp only [ticC, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨hC, hN⟩, hI⟩, hT⟩, hr⟩ := hb
  exact tic_of P _ rfl _ rfl (rep_consC P hC) (rep_compC _ _ hI) (rep_initsC _ hN) (rep_compC _ _ hr)
    (rep_tailC _ hT)

/-- **`suffix` under `suffixC`'s bit**: `suffix_rounds`, each round `iter` ran read back by `suffix_round_of` at
    its bit (`iterC_run`): `ranC`'s codes and `fitsN` bits, `rep_tailC`, `rep_compC`, `rep_unionC`. -/
theorem rep_suffixC {B : Obj} {n : USize} (X : Vals (.arr B) n) (hat : hatOK) (hb : (suffixC X).2 = true) :
    ∀ xs ys, rep (suffixC X).1 xs ys ↔ (∃ j, X.row j = xs) ∧ ys <:+ xs :=
  suffix_rounds X (fun s => (suffixRound s).1) (fun _ _ => rfl) fun i hi hne => by
    have h := iterC_run (X.1.toNat + 1) (fun s : Rel (.arr B) (.arr B) × Rel (.arr B) (.arr B) => s.2.n == 0)
      suffixRound (idU X, idU X) hb i (by omega) hne
    rw [show (fun s => (suffixRound s).1)^[i + 1] (idU X, idU X) =
      (suffixRound ((fun s => (suffixRound s).1)^[i] (idU X, idU X))).1 from rfl]
    generalize (fun s => (suffixRound s).1)^[i] (idU X, idU X) = st at h ⊢
    obtain ⟨S, F⟩ := st
    simp only [suffixRound, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hW, hT⟩, hC⟩, hU⟩ := h
    simp only [ranC, distinctCoreflC, Bool.and_eq_true] at hW
    exact suffix_round_of S F (rep_tailC _ hT) (rep_compC _ _ hC)
      (rep_ran_corefl F (one_ok _ (Obj.codesC_fits _ _ hW.1)) (pickFits_of_fitsN _ _ _ hW.2 _ (by simp)))
      (rep_unionC hat _ _ hU)

/-- The pairs `(c, y)` a round of `loopOn` meets at its states `St`, whose `ran` its step sees. -/
def loopPairs {K X Y : Obj} (St : Rel K (.prod X (.arr Y))) : Rel (.prod X (.arr Y)) (.prod X Y) :=
  pair (outl (ran St)) (outl (outr (ran St) ≫ uncons (ran (outr (ran St))).val))

/-- **`loopOn` under `loopOnC`'s bit**: `loopOn_rounds`, each round `iter` ran read back by `loop_round_set` at its
    bit (`iterC_run`): `ranC`'s and `domC`'s codes and `fitsN` bits, `rep_unconsC`, `rep_compC`, `rep_pairC`,
    `rep_nubC`, `rep_antiJoinC`, `rep_unionC`. What stays: the step's spec `hS` at the rounds whose step bit is
    set, and `unionC`'s `hat`. -/
theorem rep_loopOnC {K X Y : Obj} (F : Rel (.prod X Y) (.prod X Y) → Rel (.prod X Y) X × Bool)
    (P : Rel K (.prod X (.arr Y))) (hat : hatOK) (hb : (loopOnC F P).2 = true)
    (Fr : Nat → X.El × Y.El → X.El → Prop)
    (hS : ∀ i, (F (ran (loopPairs ((fun s => (loopRound F s).1)^[i] (Alg.zero, P)).2))).2 = true →
      ∀ cy c', Fr i cy c' ↔ rep (F (ran (loopPairs ((fun s => (loopRound F s).1)^[i] (Alg.zero, P)).2))).1 cy c') :
    ∀ k c, rep (loopOnC F P).1 k c ↔ ∃ c₀ xs, rep P k (c₀, xs) ∧ ∃ g : Nat → X.El, g 0 = c₀ ∧
      (∀ t (ht : t < xs.length), Fr t (g t, xs[t]'ht) (g (t + 1))) ∧ c = g xs.length := by
  have e : (loopOnC F P).1 = loopOn (fun D => (F D).1) P := by
    simp only [loopOnC, loopOn, iterC_fst]; rfl
  have hf : ∀ (out : Rel K X) (St : Rel K (.prod X (.arr Y))) D u p, D = ran St → u = outr D ≫ uncons (ran (outr D)).val → p = pair (outl D) (outl u) →
      (loopRound F (out, St)).1 =
        (out ∪ St ≫ outl (antiJoin D (dom u)), Rel.nub (St ≫ pair (p ≫ (F (ran p)).1) (outr u))) := by
    intro out St D u p hD hu hp; subst hD hu hp; rw [← nubC_fst]; rfl
  have one : ∀ i, i ≤ (Rel.val P).2.1.toNat →
      (∀ i' ≤ i, (((fun s => (loopRound F s).1)^[i'] (Alg.zero, P)).2.n == 0) = false) →
      (∀ k (c' : X.El) (ys : List Y.El), rep ((fun s => (loopRound F s).1)^[i + 1] (Alg.zero, P)).2 k (c', ys) ↔
        ∃ c y, rep ((fun s => (loopRound F s).1)^[i] (Alg.zero, P)).2 k (c, y :: ys) ∧ Fr i (c, y) c') ∧
      ∀ k (c : X.El), rep ((fun s => (loopRound F s).1)^[i + 1] (Alg.zero, P)).1 k c ↔
        rep ((fun s => (loopRound F s).1)^[i] (Alg.zero, P)).1 k c ∨
          rep ((fun s => (loopRound F s).1)^[i] (Alg.zero, P)).2 k (c, []) := by
    intro i hi hne
    have h := iterC_run ((Rel.val P).2.1.toNat + 1) (fun s : Rel K X × Rel K (.prod X (.arr Y)) => s.2.n == 0)
      (loopRound F) (Alg.zero, P) hb i (by omega) hne
    have hSi := hS i
    rw [show (fun s => (loopRound F s).1)^[i + 1] (Alg.zero, P) =
      (loopRound F ((fun s => (loopRound F s).1)^[i] (Alg.zero, P))).1 from rfl]
    generalize (fun s => (loopRound F s).1)^[i] (Alg.zero, P) = st at h hSi ⊢
    obtain ⟨out, St⟩ := st
    simp only [loopRound, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hW⟩, hc⟩, hu⟩, hp⟩, hG⟩, hQ⟩, hR⟩, hT⟩, hN⟩, hdu⟩, hA⟩, hO⟩, hU⟩ := h
    simp only [ranC, domC, distinctCoreflC, Bool.and_eq_true] at hD hW hdu
    have hr := loop_round_set out St _ _ _ _ _ _ _ _ _
      (rep_ran_corefl St (one_ok _ (Obj.codesC_fits _ _ hD.1)) (pickFits_of_fitsN _ _ _ hD.2 _ (by simp)))
      (rep_ran_corefl _ (one_ok _ (Obj.codesC_fits _ _ hW.1)) (pickFits_of_fitsN _ _ _ hW.2 _ (by simp <;> exact Nat.le_refl _)))
      (rep_unconsC _ hc) (rep_compC _ _ hu) (rep_pairC _ _ hp) (rep_compC _ _ hQ) (rep_pairC _ _ hR)
      (rep_compC _ _ hT) (by rw [← nubC_fst]; exact rep_nubC _ hN)
      (rep_dom_corefl _ (one_ok _ (Obj.codesC_fits _ _ hdu.1)) (pickFits_of_fitsN _ _ _ hdu.2 _ (by simp <;> exact Nat.le_refl _)))
      (rep_antiJoinC _ _ hA) (rep_compC _ _ hO) (rep_unionC hat _ _ hU)
    have hFr := hSi hG
    simp only [loopRound, nubC_fst]
    exact ⟨fun k c' ys => (hr.1 k c' ys).trans
      (exists_congr fun c => exists_congr fun y => and_congr Iff.rfl (hFr _ _).symm), hr.2⟩
  rw [e]
  exact loopOn_rounds (fun D => (F D).1) P (fun s => (loopRound F s).1) hf Fr (fun i hi hne => (one i hi hne).1)
    (fun i hi hne => (one i hi hne).2)

/-- **`loop` under `loopC`'s bit**: `rep_loopOnC` at the step `F` with no bit of its own, its spec `rep F`. -/
theorem rep_loopC {K X Y : Obj} (F : Rel (.prod X Y) X) (P : Rel K (.prod X (.arr Y))) (hat : hatOK)
    (hb : (loopC F P).2 = true) :
    ∀ k c, rep (loopC F P).1 k c ↔ ∃ c₀ xs, rep P k (c₀, xs) ∧ ∃ g : Nat → X.El, g 0 = c₀ ∧
      (∀ t (ht : t < xs.length), rep F (g t, xs[t]'ht) (g (t + 1))) ∧ c = g xs.length :=
  rep_loopOnC (fun _ => (F, true)) P hat hb (fun _ => rep F) fun _ _ _ _ => Iff.rfl

-- `merge`'s test `q` read back as `le`: on a coreflexive `D` of the pairs `S`, where its bit is set, a pair of `S`
-- passes exactly when `le` holds; the spec of the test, not a size bound
set_option hygiene false in
local notation "testOK(" q ")" =>
  ∀ (D : Rel (.prod B B) (.prod B B)) (S : (Obj.prod B B).El → Prop),
    rep D = corefl (A := (⟨(Obj.prod B B).El⟩ : RelSet.{0})) S → (q D).2 = true →
    ∀ a b, S (a, b) → ((∃ c, rep (q D).1 (a, b) c) ↔ le a b = true)

/-- **One round of `mergeOn` under its bit**: `merge_round_set` at its twins' read-backs — `ranC`'s and `domC`'s
    codes and `fitsN` bits, `rep_unconsC`, `rep_compC`, `rep_pairC`, `rep_snocC`, `rep_antiJoinC`, `rep_unionC`,
    `rep_catC` — and the test's spec `hq` at the pairs of heads the round meets. -/
theorem rep_mergeRoundC {K B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool)
    (le : B.El → B.El → Bool) (hat : hatOK) (hq : testOK(q)) (out : Rel K (.arr B))
    (St : Rel K (.prod (.prod (.arr B) (.arr B)) (.arr B))) (hb : (mergeRound q (out, St)).2 = true) :
    (∀ k s', rep (mergeRound q (out, St)).1.2 k s' ↔ ∃ a x b y acc, rep St k ((a :: x, b :: y), acc) ∧
      (le a b = true ∧ s' = ((x, b :: y), acc ++ [a]) ∨ le a b = false ∧ s' = ((a :: x, y), acc ++ [b]))) ∧
    ∀ k z, rep (mergeRound q (out, St)).1.1 k z ↔
      rep out k z ∨ ∃ x y acc, rep St k ((x, y), acc) ∧ (x = [] ∨ y = []) ∧ z = acc ++ x ++ y := by
  simp only [mergeRound, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hcx⟩, hux⟩, hcy⟩, huy⟩, hpu⟩, hbo⟩, hh⟩, hrh⟩, hG⟩, hhq⟩, hl⟩,
    hA1⟩, hS1⟩, hN1⟩, hP1⟩, hL1⟩, hnb⟩, hA2⟩, hS2⟩, hN2⟩, hP2⟩, hL2⟩, htk⟩, hT⟩, hfl⟩, hSf⟩, hc1⟩, hC1⟩, hc2⟩,
    hC2⟩, hO⟩, hU⟩ := hb
  simp only [ranC, domC, distinctCoreflC, Bool.and_eq_true] at hD hbo hrh hl
  have eRh := rep_ran_corefl _ (one_ok _ (Obj.codesC_fits _ _ hrh.1))
    (pickFits_of_fitsN _ _ _ hrh.2 _ (by simp <;> exact Nat.le_refl _))
  simp only [mergeRound]
  exact merge_round_set le out St
    (hD := rep_ran_corefl St (one_ok _ (Obj.codesC_fits _ _ hD.1)) (pickFits_of_fitsN _ _ _ hD.2 _ (by simp)))
    (hx := rfl) (hy := rfl) (hacc := rfl)
    (hUx := rep_unconsC _ hcx) (hux := rep_compC _ _ hux) (hUy := rep_unconsC _ hcy) (huy := rep_compC _ _ huy)
    (hpu := rep_pairC _ _ hpu)
    (hboth := rep_dom_corefl _ (one_ok _ (Obj.codesC_fits _ _ hbo.1))
      (pickFits_of_fitsN _ _ _ hbo.2 _ (by simp <;> exact Nat.le_refl _)))
    (hh := rep_pairC _ _ hh) (hrh := eRh)
    (htest := fun a b hab => hq _ _ eRh hG a b (by rw [eRh] at hab; exact hab.2))
    (hhq := rep_compC _ _ hhq)
    (hl := rep_dom_corefl _ (one_ok _ (Obj.codesC_fits _ _ hl.1))
      (pickFits_of_fitsN _ _ _ hl.2 _ (by simp <;> exact Nat.le_refl _)))
    (hA1 := rep_pairC _ _ hA1) (hS1 := rep_pairC _ _ hS1) (hN1 := rep_snocC _ hN1) (hP1 := rep_pairC _ _ hP1)
    (hL1 := rep_compC _ _ hL1) (hnb := rep_antiJoinC _ _ hnb)
    (hA2 := rep_pairC _ _ hA2) (hS2 := rep_pairC _ _ hS2) (hN2 := rep_snocC _ hN2) (hP2 := rep_pairC _ _ hP2)
    (hL2 := rep_compC _ _ hL2) (htk := rep_unionC hat _ _ htk) (hT := rep_compC _ _ hT)
    (hfl := rep_antiJoinC _ _ hfl) (hSf := rep_compC _ _ hSf)
    (hc1 := rep_pairC _ _ hc1) (hC1 := rep_catC _ hC1) (hc2 := rep_pairC _ _ hc2) (hC2 := rep_catC _ hC2)
    (hO := rep_compC _ _ hO) (hU := rep_unionC hat _ _ hU)

/-- **`mergeOn` under `mergeOnC`'s bit**: `mergeOn_rounds`, the first state read back by `merge_init` at its bit
    (`ranC`'s codes and `fitsN` bits, `topC`'s count and fit, `pairC_ok`, `compC_cmpOK`), each round `iter` ran by
    `rep_mergeRoundC` at its bit (`iterC_run`). What stays: the test's spec `hq` and `unionC`'s `hat`. -/
theorem rep_mergeOnC {K B : Obj} (q : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool)
    (P : Rel K (.prod (.arr B) (.arr B))) (le : B.El → B.El → Bool) (hat : hatOK) (hq : testOK(q))
    (hb : (mergeOnC q P).2 = true) :
    ∀ k zs, rep (mergeOnC q P).1 k zs ↔ ∃ xs ys, rep P k (xs, ys) ∧ zs = List.merge xs ys le := by
  simp only [mergeOnC, Bool.and_eq_true] at hb
  obtain ⟨hI, hit⟩ := hb
  simp only [mergeInitC, topC, Bool.and_eq_true, decide_eq_true_eq] at hI
  obtain ⟨⟨⟨hR, ⟨⟨⟨-, h63⟩, hfa⟩, -⟩⟩, hQ⟩, hM⟩ := hI
  simp only [ranC, distinctCoreflC, Bool.and_eq_true] at hR
  have h0 := merge_init P ⟨⟨Obj.codesC_fits _ _ hR.1, pickFits_of_fitsN _ _ _ hR.2 _ (by simp)⟩, h63,
    pickFits_of_fitsN _ _ _ hfa _ (by simp <;> exact Nat.le_refl _), pairC_ok _ _ hQ, compC_cmpOK _ _ hM⟩
  rw [mergeOnC_fst]
  refine mergeOn_rounds (fun D => (q D).1) P le (fun s => (mergeRound q s).1) ?_ _ rfl h0
    (fun i hi hne => (rep_mergeRoundC q le hat hq _ _ (iterC_run _ _ _ _ hit i (by omega) hne)).1)
    (fun i hi hne => (rep_mergeRoundC q le hat hq _ _ (iterC_run _ _ _ _ hit i (by omega) hne)).2)
  intro out St D hD x hx y hy acc hacc ux hux uy huy both hboth h hh l hl
  subst hD hx hy hacc hux huy hboth hh hl
  rfl

/-- **`merge` under `mergeC`'s bit**: `rep_mergeOnC`, the test `pairsIn Q` read back by `rep_pairsIn` at
    `compC`'s bit; `le a b` any Boolean test with `le a b = true` exactly when `a Q b` (`hle`). -/
theorem rep_mergeC {K B : Obj} (Q : Rel B B) (P : Rel K (.prod (.arr B) (.arr B))) (le : B.El → B.El → Bool)
    (hle : ∀ a b, le a b = true ↔ rep Q a b) (hat : hatOK) (hb : (mergeC Q P).2 = true) :
    ∀ k zs, rep (mergeC Q P).1 k zs ↔ ∃ xs ys, rep P k (xs, ys) ∧ zs = List.merge xs ys le := by
  refine rep_mergeOnC _ P le hat (fun D S hD hc a b hS => ?_) hb
  have eP := rep_pairsIn Q D (compC_cmpOK _ _ hc)
  constructor
  · rintro ⟨c, h⟩
    obtain ⟨h1, h2⟩ := (eP _ _).1 h
    rw [hD] at h1
    obtain ⟨rfl, -⟩ := h1
    exact (hle a b).2 h2
  · intro h
    exact ⟨(a, b), (eP _ _).2 ⟨by rw [hD]; exact ⟨rfl, hS⟩, (hle a b).1 h⟩⟩

#print axioms rep_ticC
#print axioms rep_suffixC
#print axioms rep_loopOnC
#print axioms rep_loopC
#print axioms rep_mergeRoundC
#print axioms rep_mergeOnC
#print axioms rep_mergeC

end Rep

namespace CRel

variable {K X Y B : Obj}

/-- `tic`, ok where `P` is and `ticC` ran within capacity. -/
def tic (P : CRel K (.prod B (.arr B))) : CRel K (.arr (.arr B)) := let r := ticC P.rel; ⟨r.1, P.ok && r.2⟩

/-- `suffix` on the arrays `X`, ok where `suffixC` ran within capacity. -/
def suffix {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) := let r := suffixC X; ⟨r.1, r.2⟩

/-- `loopOn` on a step over `CRel`s, ok where `P` is, every round's step was and `loopOnC` ran within capacity. The
    step sees its input as ok: its bit is already in the loop's. -/
def loopOn (F : CRel (.prod X Y) (.prod X Y) → CRel (.prod X Y) X) (P : CRel K (.prod X (.arr Y))) : CRel K X :=
  let r := loopOnC (fun D => let s := F ⟨D, true⟩; (s.rel, s.ok)) P.rel; ⟨r.1, P.ok && r.2⟩

/-- `loop(F)`, ok where `F` and `P` are and `loopC` ran within capacity. -/
def loop (F : CRel (.prod X Y) X) (P : CRel K (.prod X (.arr Y))) : CRel K X :=
  let r := loopC F.rel P.rel; ⟨r.1, F.ok && P.ok && r.2⟩

theorem rep_tic (P : CRel K (.prod B (.arr B))) (hb : (tic P).ok = true) :
    ∀ k zss, rep (tic P).rel k zss ↔ ∃ b bs, rep P.rel k (b, bs) ∧
      zss = (List.range (bs.length + 1)).map fun j => (b :: bs).take (j + 1) :=
  rep_ticC P.rel (by simp only [tic, Bool.and_eq_true] at hb; exact hb.2)

/-- `hat`: `rep_unionC`'s. -/
theorem rep_suffix {n : USize} (X : Vals (.arr B) n) (hat : hatOK) (hb : (suffix X).ok = true) :
    ∀ xs ys, rep (suffix X).rel xs ys ↔ (∃ j, X.row j = xs) ∧ ys <:+ xs :=
  rep_suffixC X hat hb

/-- `hat`: `rep_unionC`'s; `hS` the step's spec at each round whose step was ok. -/
theorem rep_loopOn (F : CRel (.prod X Y) (.prod X Y) → CRel (.prod X Y) X) (P : CRel K (.prod X (.arr Y)))
    (hat : hatOK) (hb : (loopOn F P).ok = true) (Fr : Nat → X.El × Y.El → X.El → Prop)
    (hS : ∀ i, (F ⟨Alg.ran (loopPairs ((fun s => (loopRound (fun D => let s := F ⟨D, true⟩; (s.rel, s.ok)) s).1)^[i]
        (Alg.zero, P.rel)).2), true⟩).ok = true →
      ∀ cy c', Fr i cy c' ↔ rep (F ⟨Alg.ran (loopPairs ((fun s => (loopRound (fun D => let s := F ⟨D, true⟩;
        (s.rel, s.ok)) s).1)^[i] (Alg.zero, P.rel)).2), true⟩).rel cy c') :
    ∀ k c, rep (loopOn F P).rel k c ↔ ∃ c₀ xs, rep P.rel k (c₀, xs) ∧ ∃ g : Nat → X.El, g 0 = c₀ ∧
      (∀ t (ht : t < xs.length), Fr t (g t, xs[t]'ht) (g (t + 1))) ∧ c = g xs.length :=
  rep_loopOnC _ P.rel hat (by simp only [loopOn, Bool.and_eq_true] at hb; exact hb.2) Fr hS

/-- `hat`: `rep_unionC`'s. -/
theorem rep_loop (F : CRel (.prod X Y) X) (P : CRel K (.prod X (.arr Y))) (hat : hatOK) (hb : (loop F P).ok = true) :
    ∀ k c, rep (loop F P).rel k c ↔ ∃ c₀ xs, rep P.rel k (c₀, xs) ∧ ∃ g : Nat → X.El, g 0 = c₀ ∧
      (∀ t (ht : t < xs.length), rep F.rel (g t, xs[t]'ht) (g (t + 1))) ∧ c = g xs.length :=
  rep_loopC F.rel P.rel hat (by simp only [loop, Bool.and_eq_true] at hb; exact hb.2)

/-- `mergeOn` on a test over `CRel`s, ok where `P` is, every round's test was and `mergeOnC` ran within capacity.
    The test sees its input as ok: its bit is already in the merge's. -/
def mergeOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) (P : CRel K (.prod (.arr B) (.arr B))) :
    CRel K (.arr B) :=
  let r := mergeOnC (fun D => let s := q ⟨D, true⟩; (s.rel, s.ok)) P.rel; ⟨r.1, P.ok && r.2⟩

/-- `merge(Q)`, ok where `Q` and `P` are and `mergeC` ran within capacity. -/
def merge (Q : CRel B B) (P : CRel K (.prod (.arr B) (.arr B))) : CRel K (.arr B) :=
  let r := mergeC Q.rel P.rel; ⟨r.1, Q.ok && P.ok && r.2⟩

/-- `hat`: `rep_unionC`'s; `hq` the test's spec on a coreflexive where the test was ok. -/
theorem rep_mergeOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B))
    (P : CRel K (.prod (.arr B) (.arr B))) (le : B.El → B.El → Bool) (hat : hatOK)
    (hq : ∀ (D : Rel (.prod B B) (.prod B B)) (S : (Obj.prod B B).El → Prop),
      rep D = corefl (A := (⟨(Obj.prod B B).El⟩ : RelSet.{0})) S → (q ⟨D, true⟩).ok = true →
      ∀ a b, S (a, b) → ((∃ c, rep (q ⟨D, true⟩).rel (a, b) c) ↔ le a b = true))
    (hb : (mergeOn q P).ok = true) :
    ∀ k zs, rep (mergeOn q P).rel k zs ↔ ∃ xs ys, rep P.rel k (xs, ys) ∧ zs = List.merge xs ys le :=
  rep_mergeOnC _ P.rel le hat hq (by simp only [mergeOn, Bool.and_eq_true] at hb; exact hb.2)

/-- `hat`: `rep_unionC`'s; `hle`: `le` decides `Q`. -/
theorem rep_merge (Q : CRel B B) (P : CRel K (.prod (.arr B) (.arr B))) (le : B.El → B.El → Bool)
    (hle : ∀ a b, le a b = true ↔ rep Q.rel a b) (hat : hatOK) (hb : (merge Q P).ok = true) :
    ∀ k zs, rep (merge Q P).rel k zs ↔ ∃ xs ys, rep P.rel k (xs, ys) ∧ zs = List.merge xs ys le :=
  rep_mergeC Q.rel P.rel le hle hat (by simp only [merge, Bool.and_eq_true] at hb; exact hb.2)

end CRel

end LeetQ.Rel
