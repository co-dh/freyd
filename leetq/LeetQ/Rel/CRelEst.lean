/-
  The runtime ok-bit on the ops that take a test: `pairsIn`, `swapIn`, `estOn`/`est`, `thinOn`/`thin`,
  `orderedOn`/`ordered`, `sortSet`. A twin takes its test as `qC : Rel → Rel × Bool` and `&&`s the test's bit with
  its pieces'; `ranC_oneFit`, `domC_oneFit`, `diffC_ok`, `antiJoinC_ok` read one piece's bit as the bundle the plain
  read-back (`rep_estOn`, `rep_thinOn`, `rep_orderedOn`, …) takes at it, so each `rep_<op>C` is that read-back under
  the twin's bit. What stays is not a size bound: the test's own spec, which a caller applies at the test bits each
  `rep_<op>C` hands back.
-/
import LeetQ.Rel.CRelLoop
import LeetQ.Run.CRelLoopDef
import LeetQ.Rel.CRelPower
import LeetQ.Run.CRelPowerDef
import LeetQ.Rel.RepSort
import LeetQ.Run.CRelEstDef

namespace LeetQ.Rel

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet
open LeetQ.Rel.Rep LeetQ.Rel.Rep.FoldN LeetQ.Rel.Rep.OpsN LeetQ.Rel.Rep.Prim LeetQ.Rel.Rep.ListN

namespace Rep

variable {A B : Obj}

/-! ## A piece's bit as the bundle the plain read-backs take -/

/-- `ranC`'s bit is `rep_ran_corefl`'s premises (`oneFit`). -/
theorem ranC_oneFit (R : Rel A B) (hb : (ranC R).2 = true) : oneFit(B, Rel.n R, Rel.val R) := by
  simp only [ranC, distinctCoreflC, Bool.and_eq_true] at hb
  exact ⟨Obj.codesC_fits B _ hb.1, pickFits_of_fitsN B R.val _ hb.2 _ (by simp)⟩

/-- `domC`'s bit is `rep_dom_corefl`'s premises (`oneFit`). -/
theorem domC_oneFit (R : Rel A B) (hb : (domC R).2 = true) : oneFit(A, Rel.n R, Rel.key R) := by
  simp only [domC, distinctCoreflC, Bool.and_eq_true] at hb
  exact ⟨Obj.codesC_fits A _ hb.1, pickFits_of_fitsN A R.key _ hb.2 _ (by simp)⟩

/-- `diffC`'s bit is `rep_diff`'s premises (`diffOK`): `diffC_bits`, the `fitsN` bits read as picks. -/
theorem diffC_ok (R S : Rel A B) (hb : (diffC R S).2 = true) : diffOK(A, B, R, S) :=
  let ⟨hp, hk, hv⟩ := diffC_bits R S hb
  fun _ e' => by subst e'; exact ⟨hp, pickFits_range A _ hk, pickFits_range B _ hv⟩


/-- `antiJoinC`'s bit is `rep_antiJoin`'s premises (`ajOK`), as `rep_antiJoinC`'s. -/
theorem antiJoinC_ok (R : Rel A B) (T : Rel B B) (hb : (antiJoinC R T).2 = true) : ajOK(B, R, T) := by
  simp only [antiJoinC, Bool.and_eq_true] at hb
  obtain ⟨⟨hcb, hk⟩, hv⟩ := hb
  exact ⟨Obj.codesC_fits B _ hcb, pickFits_of_fitsN A R.key _ hk _ (by simp),
    pickFits_of_fitsN B R.val _ hv _ (by simp)⟩

/-! ## `pairsIn`, `swapIn` -/

/-- **`pairsIn` under `pairsInC`'s bit**: `rep_pairsIn` at `compC`'s (`compC_cmpOK`). -/
theorem rep_pairsInC (Q : Rel B B) (D : Rel (.prod B B) (.prod B B)) (hb : (pairsInC Q D).2 = true) :
    ∀ p p', rep (pairsInC Q D).1 p p' ↔ rep D p p' ∧ rep Q p'.1 p'.2 :=
  rep_pairsIn Q D (compC_cmpOK _ _ hb)

/-- **`swapInC`'s bit is `rep_swapIn`'s premises** at the test `(qC ·).1`, `ranC`'s `oneFit` at the swapped pairs, and
    the test's own bit at the pairs it sees. -/
theorem swapInC_ok (qC : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool)
    (D : Rel (.prod B B) (.prod B B)) (hb : (swapInC qC D).2 = true) :
    pairOK(.prod B B, outr D, outl D) ∧
      oneFit(.prod B B, Rel.n (pair (outr D) (outl D)), Rel.val (pair (outr D) (outl D))) ∧
      (qC (ran (pair (outr D) (outl D)))).2 = true ∧
      cmpOK(.prod B B, pair (outr D) (outl D), (qC (ran (pair (outr D) (outl D)))).1) ∧
      oneFit(.prod B B, Rel.n (pair (outr D) (outl D) ≫ (qC (ran (pair (outr D) (outl D)))).1),
        Rel.key (pair (outr D) (outl D) ≫ (qC (ran (pair (outr D) (outl D)))).1)) := by
  simp only [swapInC, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨hs, hE⟩, ht⟩, hM⟩, hd⟩ := hb
  exact ⟨pairC_ok _ _ hs, ranC_oneFit _ hE, ht, compC_cmpOK _ _ hM, domC_oneFit _ hd⟩

/-- **`swapIn` under `swapInC`'s bit**: `rep_swapIn` at `swapInC_ok`. -/
theorem rep_swapInC (qC : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool)
    (D : Rel (.prod B B) (.prod B B)) (hb : (swapInC qC D).2 = true) :
    ∀ p p', rep (swapInC qC D).1 p p' ↔ p = p' ∧ ∃ u v w, ((∃ y, rep D p (y, u)) ∧ ∃ z, rep D p (v, z)) ∧
      rep (qC (ran (pair (outr D) (outl D)))).1 (u, v) w := by
  obtain ⟨hs, -, -, hM, hd⟩ := swapInC_ok qC D hb
  exact rep_swapIn (fun r => (qC r).1) D _ rfl _ rfl _ rfl ⟨hs, hM, hd⟩

/-! ## `estOn`, `est`, `thinOn`, `thin` -/

/-- **`estOnC`'s bit is the test's at `D = ran ⟨G,G⟩` and `rep_estOn`'s premises** at the test `(qC ·).1`. -/
theorem estOnC_ok (qC : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool) (G : Rel A B)
    (hb : (estOnC qC G).2 = true)
    (P : Rel A (.prod B B)) (hP : P = pair G G) (D : Rel (.prod B B) (.prod B B)) (hD : D = ran P)
    (V : Rel B B) (hV : V = ran G) (W : Rel B (.prod B B)) (hW : W = pair V V)
    (N : Rel (.prod B B) (.prod B B)) (hN : N = ran W) (Y : Rel (.prod B B) (.prod B B)) (hY : Y = D \ (qC D).1)
    (Z : Rel (.prod B B) (.prod B B)) (hZ : Z = Y \ N) (M : Rel A B) (hM : M = P ≫ outl Z) :
    (qC D).2 = true ∧ pairOK(A, G, G) ∧ oneFit(.prod B B, Rel.n P, Rel.val P) ∧ oneFit(B, Rel.n G, Rel.val G) ∧
      pairOK(B, V, V) ∧ oneFit(.prod B B, Rel.n W, Rel.val W) ∧ diffOK(.prod B B, .prod B B, D, (qC D).1) ∧
      diffOK(.prod B B, .prod B B, Y, N) ∧ cmpOK(.prod B B, P, outl Z) ∧ diffOK(A, B, G, M) := by
  subst hP hD hV hW hN hY hZ hM
  simp only [estOnC, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hP, hD⟩, hV⟩, ht⟩, hY⟩, hW⟩, hN⟩, hZ⟩, hM⟩, hr⟩ := hb
  exact ⟨ht, pairC_ok _ _ hP, ranC_oneFit _ hD, ranC_oneFit _ hV, pairC_ok _ _ hW, ranC_oneFit _ hN,
    diffC_ok _ _ hY, diffC_ok _ _ hZ, compC_cmpOK _ _ hM, diffC_ok _ _ hr⟩

/-- **`estOn` under `estOnC`'s bit**: `rep_estOn` at `estOnC_ok`, with the test's bit at `D` for its spec. -/
theorem rep_estOnC (qC : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool) (G : Rel A B)
    (hb : (estOnC qC G).2 = true) :
    (qC (ran (pair G G))).2 = true ∧ ∀ a b, rep (estOnC qC G).1 a b ↔ rep G a b ∧
      ¬ ∃ c, rep G a c ∧ c ≠ b ∧ ¬ rep (qC (ran (pair G G))).1 (b, c) (b, c) := by
  obtain ⟨ht, h⟩ := estOnC_ok qC G hb _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
  exact ⟨ht, rep_estOn (fun r => (qC r).1) G _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl h⟩

/-- **`est(Q)` under `estC`'s bit**: `rep_est` at `estOnC_ok`, the test's bit its `hq` (`compC_cmpOK`). -/
theorem rep_estC (Q : Rel B B) (G : Rel A B) (hb : (estC Q G).2 = true) :
    ∀ a b, rep (estC Q G).1 a b ↔ rep G a b ∧ ∀ c, rep G a c → c ≠ b → rep Q b c := by
  obtain ⟨ht, h⟩ := estOnC_ok (pairsInC Q) G hb _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
  exact rep_est Q G _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl h (compC_cmpOK _ _ ht)

/-- **`thinOnC`'s bit is the test's and `swapInC`'s at `D = ran ⟨G,G⟩`, `ranC`'s `oneFit` at `⟨G,G⟩`, and
    `rep_thinOn`'s premises** at the test `(qC ·).1`. -/
theorem thinOnC_ok (qC : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool) (G : Rel A B)
    (hb : (thinOnC qC G).2 = true) :
    (qC (ran (pair G G))).2 = true ∧ (swapInC qC (ran (pair G G))).2 = true ∧
      oneFit(.prod B B, Rel.n (pair G G), Rel.val (pair G G)) ∧
      (pairOK(A, G, G) ∧
        diffOK(.prod B B, .prod B B, (qC (ran (pair G G))).1, (swapInC qC (ran (pair G G))).1) ∧
        cmpOK(.prod B B, pair G G, outr ((qC (ran (pair G G))).1 \ (swapInC qC (ran (pair G G))).1)) ∧
        diffOK(A, B, G, pair G G ≫ outr ((qC (ran (pair G G))).1 \ (swapInC qC (ran (pair G G))).1))) := by
  simp only [thinOnC, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨hP, hD⟩, ht⟩, hS⟩, hY⟩, hM⟩, hr⟩ := hb
  exact ⟨ht, hS, ranC_oneFit _ hD, pairC_ok _ _ hP, diffC_ok _ _ hY, compC_cmpOK _ _ hM, diffC_ok _ _ hr⟩

/-- **`thinOn` under `thinOnC`'s bit**: `rep_thinOn` at `thinOnC_ok`, with the test's and `swapInC`'s bits at `D`
    (`rep_swapInC`) for the test's spec. -/
theorem rep_thinOnC (qC : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool) (G : Rel A B)
    (hb : (thinOnC qC G).2 = true) :
    (qC (ran (pair G G))).2 = true ∧ (swapInC qC (ran (pair G G))).2 = true ∧ ∀ a c, rep (thinOnC qC G).1 a c ↔
      rep G a c ∧ ¬ ∃ b b' y, rep G a b ∧ rep G a b' ∧ rep (qC (ran (pair G G))).1 (b, b') (y, c) ∧
        ¬ rep (swapInC qC (ran (pair G G))).1 (b, b') (y, c) := by
  obtain ⟨ht, hS, -, h⟩ := thinOnC_ok qC G hb
  exact ⟨ht, hS, rep_thinOn (fun r => (qC r).1) G _ rfl _ rfl _ rfl _ rfl _ rfl h⟩

/-- **`thin(Q)` under `thinC`'s bit**: `rep_thin` at `thinOnC_ok` and `swapInC_ok`, the two test bits its `hqD`,
    `hqE` (`compC_cmpOK`). -/
theorem rep_thinC (Q : Rel B B) (G : Rel A B) (hb : (thinC Q G).2 = true) :
    ∀ a c, rep (thinC Q G).1 a c ↔ rep G a c ∧ ¬ ∃ b, rep G a b ∧ rep Q b c ∧ ¬ rep Q c b := by
  obtain ⟨ht, hS, hDf, h⟩ := thinOnC_ok (pairsInC Q) G hb
  obtain ⟨hs, hEf, hqE, hM, hd⟩ := swapInC_ok (pairsInC Q) _ hS
  exact rep_thin Q G _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl h ⟨hs, hM, hd⟩ hDf hEf
    (compC_cmpOK _ _ ht) (compC_cmpOK _ _ hqE)

/-! ## `orderedOn`, `ordered`, `sortSet` -/

/-- **`orderedOn` under `orderedOnC`'s bit**: `rep_orderedOn` at its pieces' bits — `suffix` by `rep_suffixC`, then
    `ranC_oneFit`, `unconsC_fits`, `compC_cmpOK`, `memC_ok`, `pairC_ok`, `antiJoinC_ok`, `domC_oneFit` — with the
    test's bit at `ordPairs X` for its spec. -/
theorem rep_orderedOnC (qC : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool) {n : USize}
    (X : Vals (.arr B) n) (hb : (orderedOnC qC X).2 = true) :
    (qC (ordPairs X)).2 = true ∧
      (∀ xs y zs z, (∃ i, X.row i = xs) → (y :: zs) <:+ xs → z ∈ zs → rep (ordPairs X) (y, z) (y, z)) ∧
      ∀ xs ys, rep (orderedOnC qC X).1 xs ys ↔ (∃ i, X.row i = xs) ∧ ys = xs ∧
        ∀ y zs, (y :: zs) <:+ xs → ∀ z ∈ zs, ∃ w, rep (qC (ordPairs X)).1 w (y, z) := by
  simp only [orderedOnC, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hS, hW⟩, hu⟩, hT⟩, hD⟩, hV⟩, hm⟩, hM⟩, hyz⟩, hE⟩, ht⟩, hbad⟩, hdb⟩, hC⟩, hdC⟩, hr⟩ := hb
  have hm' := memC_ok _ hm
  exact ⟨ht, rep_orderedOn (fun r => (qC r).1) X (rep_suffixC X hS) _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
    _ rfl _ rfl _ rfl _ rfl
    ⟨ranC_oneFit _ hW, fun _ e _ _ _ _ => by subst e; exact unconsC_fits _ hu, compC_cmpOK _ _ hT,
      ranC_oneFit _ hD, ranC_oneFit _ hV, hm'.1, hm'.2, compC_cmpOK _ _ hM, pairC_ok _ _ hyz, ranC_oneFit _ hE,
      antiJoinC_ok _ _ hbad, domC_oneFit _ hdb, compC_cmpOK _ _ hC, domC_oneFit _ hdC, antiJoinC_ok _ _ hr⟩⟩

/-- **`ordered(Q)` under `orderedC`'s bit**: `rep_orderedOnC` at `pairsInC Q`, in `Pairwise` form
    (`pairwise_of_orderedOn`), the test's bit its `hq` (`compC_cmpOK`). -/
theorem rep_orderedC (Q : Rel B B) {n : USize} (X : Vals (.arr B) n) (hb : (orderedC Q X).2 = true) :
    ∀ xs ys, rep (orderedC Q X).1 xs ys ↔ (∃ i, X.row i = xs) ∧ ys = xs ∧ xs.Pairwise (fun y z => rep Q y z) := by
  obtain ⟨ht, h1, h2⟩ := rep_orderedOnC (pairsInC Q) X hb
  exact pairwise_of_orderedOn Q X _ (ordPairs X) (compC_cmpOK (ordPairs X) _ ht) h1 h2

/-- **`sortSet(Q)` under `sortSetC`'s bit**: `rep_sortSet` at `rep_orderedC` and `compC`'s bit (`compC_cmpOK`). -/
theorem rep_sortSetC (Q : Rel B B) {n : USize} (Y : Vals (.arr B) n) (hb : (sortSetC Q Y).2 = true) :
    ∀ s ys, rep (sortSetC Q Y).1 s ys ↔
      rep (setify Y) ys s ∧ (∃ i, Y.row i = ys) ∧ ys.Pairwise (fun y z => rep Q y z) := by
  simp only [sortSetC, Bool.and_eq_true] at hb
  exact rep_sortSet Q Y (rep_orderedC Q Y hb.1.2) (compC_cmpOK _ _ hb.2)

/-- **`thinL(Q)` under `thinLC`'s bit, elementwise**: an array `xs` of `X` goes to `ys` exactly when `ys` is a
    sublist of `xs` and each element of `xs` is `Q`-above some element of `ys`. Each piece read back by its twin
    (`rep_subseqC`, `ranC_oneFit`, `rep_setifyC`, `rep_memC`, `rep_compC`, `rep_rightDivC`, `rep_leftDivC`,
    `rep_interC`), each piece named once read. -/
theorem rep_thinLC (Q : Rel B B) {n : USize} (X : Vals (.arr B) n) (hb : (thinLC Q X).2 = true) :
    ∀ xs ys, rep (thinLC Q X).1 xs ys ↔ (∃ i, X.row i = xs) ∧ ys.Sublist xs ∧ ∀ a ∈ xs, ∃ y ∈ ys, rep Q y a := by
  simp only [thinLC, okbit] at hb ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hU, hW⟩, hs⟩, hm⟩, hQS⟩, hRd⟩, hLd⟩, hT⟩, hH⟩, hG⟩, hr⟩ := hb
  have eU := rep_subseqC X hU
  have hWf := ranC_oneFit _ hW
  generalize (subseqC X).1 = U at eU hWf hW hs hm hQS hRd hLd hT hH hG hr ⊢
  have eW : ∀ a b, rep (ranC U).1 a b ↔ a = b ∧ ∃ x, rep U x a := fun a b => by
    show rep (ran U) a b ↔ _
    rw [rep_ran_corefl U (one_ok _ hWf.1) hWf.2]; exact Iff.rfl
  generalize (ranC U).1 = W at eW hs hm hQS hRd hLd hT hH hG hr ⊢
  obtain ⟨eS1, eS2⟩ := rep_setifyC _ hs
  generalize (setifyC W.val).1 = St at eS1 eS2 hm hQS hRd hLd hT hH hG hr ⊢
  have eM := rep_memC _ hm
  generalize (memC St.val).1 = mS at eM hQS hRd hLd hT hH hG hr ⊢
  have eX : ∀ a s, rep (mS°) a s ↔ (∃ i, St.val.row i = s) ∧ a ∈ s := fun a s => by rw [rep_conv]; exact eM s a
  have eQS : ∀ a t, rep (compC (Q°) (mS°)).1 a t ↔ ∃ y, rep Q y a ∧ (∃ j, St.val.row j = t) ∧ y ∈ t := fun a t => by
    rw [rep_compC _ _ hQS, Freyd.Alg.RelSet.comp_apply]
    exact exists_congr fun y => and_congr (by rw [rep_conv]; exact Iff.rfl) (eX y t)
  generalize (compC (Q°) (mS°)).1 = QS at eQS hLd hT hH hG hr ⊢
  -- `⊇ ∩ (∈ \ Q°∈)` on two sets of `St.val`: the second a subset of the first, each element of the first above one
  have eT : ∀ s t, (∃ i, St.val.row i = s) → (∃ j, St.val.row j = t) →
      (rep (interC (rightDivC mS mS St.val St.val).1 (leftDivC (mS°) QS St.val St.val).1).1 s t ↔
        (∀ c ∈ t, c ∈ s) ∧ ∀ a ∈ s, ∃ y ∈ t, rep Q y a) := by
    intro s t hs ht
    rw [rep_interC _ _ hT]
    show rep (rightDivC mS mS St.val St.val).1 s t ∧ rep (leftDivC (mS°) QS St.val St.val).1 s t ↔ _
    rw [rep_rightDivC _ _ _ _ hRd s t, rep_leftDivC _ _ _ _ hLd s t]
    simp only [eM, eX, eQS]
    constructor
    · rintro ⟨⟨hr, -⟩, ⟨hl, -⟩⟩
      refine ⟨fun c hc => (hr c ⟨ht, hc⟩).2, fun a ha => ?_⟩
      obtain ⟨y, hq, -, hy⟩ := hl a ⟨hs, ha⟩
      exact ⟨y, hy, hq⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨fun c ⟨_, hc⟩ => ⟨hs, h1 c hc⟩, Or.inr ⟨hs, ht⟩⟩, ⟨fun a ⟨_, ha⟩ => ?_, Or.inr ⟨hs, ht⟩⟩⟩
      obtain ⟨y, hy, hq⟩ := h2 a ha
      exact ⟨y, hq, ht, hy⟩
  generalize (interC (rightDivC mS mS St.val St.val).1 (leftDivC (mS°) QS St.val St.val).1).1 = Tt at eT hH hG hr ⊢
  have eH : ∀ xs t, rep (compC St Tt).1 xs t ↔ ∃ s, rep St xs s ∧ rep Tt s t := fun xs t => by
    rw [rep_compC _ _ hH, Freyd.Alg.RelSet.comp_apply]
  generalize (compC St Tt).1 = H at eH hG hr ⊢
  have eG : ∀ xs ys, rep (compC H (St°)).1 xs ys ↔ ∃ t, rep H xs t ∧ rep St ys t := fun xs ys => by
    rw [rep_compC _ _ hG, Freyd.Alg.RelSet.comp_apply]
    exact exists_congr fun t => and_congr Iff.rfl (by rw [rep_conv]; exact Iff.rfl)
  generalize (compC H (St°)).1 = G at eG hr ⊢
  -- a row of `W.val`: an array `U` reaches
  have hrow : ∀ x zs, rep U x zs → ∃ i, W.val.row i = zs := fun x zs h => by
    obtain ⟨i, -, hi⟩ := id ((eW zs zs).2 ⟨rfl, x, h⟩); exact ⟨i, hi⟩
  intro xs ys
  rw [rep_interC _ _ hr]
  show rep G xs ys ∧ rep U xs ys ↔ _
  rw [and_comm, eG, eU, and_assoc]
  refine and_congr_right fun hx => and_congr_right fun hsl => ⟨?_, fun hq => ?_⟩
  · rintro ⟨t, hh, ht⟩ a ha
    obtain ⟨s, hs, hT⟩ := (eH _ _).1 hh
    obtain ⟨i, -, hi⟩ := id hs
    obtain ⟨j, -, hj⟩ := id ht
    obtain ⟨-, hq⟩ := (eT s t ⟨i, hi⟩ ⟨j, hj⟩).1 hT
    obtain ⟨y, hy, hQ⟩ := hq a (((eS1 xs s hs).2 a).2 ha)
    exact ⟨y, ((eS1 ys t ht).2 y).1 hy, hQ⟩
  · obtain ⟨s, hs⟩ := (eS2 xs).2 (hrow xs xs ((eU xs xs).2 ⟨hx, List.Sublist.refl _⟩))
    obtain ⟨t, ht⟩ := (eS2 ys).2 (hrow xs ys ((eU xs ys).2 ⟨hx, hsl⟩))
    obtain ⟨i, -, hi⟩ := id hs
    obtain ⟨j, -, hj⟩ := id ht
    refine ⟨t, (eH _ _).2 ⟨s, hs, (eT s t ⟨i, hi⟩ ⟨j, hj⟩).2 ⟨fun c hc => ?_, fun a ha => ?_⟩⟩, ht⟩
    · exact ((eS1 xs s hs).2 c).2 (hsl.subset (((eS1 ys t ht).2 c).1 hc))
    · obtain ⟨y, hy, hQ⟩ := hq a (((eS1 xs s hs).2 a).1 ha)
      exact ⟨y, ((eS1 ys t ht).2 y).2 hy, hQ⟩

#print axioms rep_thinLC
#print axioms rep_diffC
#print axioms rep_swapInC
#print axioms rep_estOnC
#print axioms rep_estC
#print axioms rep_thinOnC
#print axioms rep_thinC
#print axioms rep_orderedOnC
#print axioms rep_orderedC
#print axioms rep_sortSetC

end Rep

namespace CRel

variable {A B : Obj}

theorem rep_thinL (Q : CRel B B) {n : USize} (X : Vals (.arr B) n) (hb : (thinL Q X).ok = true) :
    ∀ xs ys, rep (thinL Q X).rel xs ys ↔ (∃ i, X.row i = xs) ∧ ys.Sublist xs ∧ ∀ a ∈ xs, ∃ y ∈ ys, rep Q.rel y a := by
  have e : thinL Q X = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_thinLC Q.rel X hb

theorem rep_pairsIn (Q : CRel B B) (D : CRel (.prod B B) (.prod B B)) (hb : (pairsIn Q D).ok = true) :
    ∀ p p', rep (pairsIn Q D).rel p p' ↔ rep D.rel p p' ∧ rep Q.rel p'.1 p'.2 := by
  have e : pairsIn Q D = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_pairsInC Q.rel D.rel hb

theorem rep_swapIn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) (D : CRel (.prod B B) (.prod B B))
    (hb : (swapIn q D).ok = true) :
    ∀ p p', rep (swapIn q D).rel p p' ↔ p = p' ∧ ∃ u v w, ((∃ y, rep D.rel p (y, u)) ∧ ∃ z, rep D.rel p (v, z)) ∧
      rep (q ⟨Alg.ran (Alg.pair (outr D.rel) (outl D.rel)), true⟩).rel (u, v) w := by
  have e : swapIn q D = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_swapInC (testC q) D.rel hb

/-- The test's spec applies where `(q ⟨D, true⟩).ok`, the first conjunct. -/
theorem rep_estOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) (G : CRel A B)
    (hb : (estOn q G).ok = true) :
    (q ⟨Alg.ran (Alg.pair G.rel G.rel), true⟩).ok = true ∧ ∀ a b, rep (estOn q G).rel a b ↔ rep G.rel a b ∧
      ¬ ∃ c, rep G.rel a c ∧ c ≠ b ∧ ¬ rep (q ⟨Alg.ran (Alg.pair G.rel G.rel), true⟩).rel (b, c) (b, c) := by
  have e : estOn q G = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_estOnC (testC q) G.rel hb

/-- The test's spec applies where `(q ⟨D, true⟩).ok`, the first conjunct; `swapIn`'s bit reads it back
    (`rep_swapInC`). -/
theorem rep_thinOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) (G : CRel A B)
    (hb : (thinOn q G).ok = true) :
    (q ⟨Alg.ran (Alg.pair G.rel G.rel), true⟩).ok = true ∧
      (swapInC (testC q) (Alg.ran (Alg.pair G.rel G.rel))).2 = true ∧ ∀ a c, rep (thinOn q G).rel a c ↔
      rep G.rel a c ∧ ¬ ∃ b b' y, rep G.rel a b ∧ rep G.rel a b' ∧
        rep (q ⟨Alg.ran (Alg.pair G.rel G.rel), true⟩).rel (b, b') (y, c) ∧
        ¬ rep (swapInC (testC q) (Alg.ran (Alg.pair G.rel G.rel))).1 (b, b') (y, c) := by
  have e : thinOn q G = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_thinOnC (testC q) G.rel hb

theorem rep_est (Q : CRel B B) (G : CRel A B) (hb : (est Q G).ok = true) :
    ∀ a b, rep (est Q G).rel a b ↔ rep G.rel a b ∧ ∀ c, rep G.rel a c → c ≠ b → rep Q.rel b c := by
  have e : est Q G = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_estC Q.rel G.rel hb

theorem rep_thin (Q : CRel B B) (G : CRel A B) (hb : (thin Q G).ok = true) :
    ∀ a c, rep (thin Q G).rel a c ↔ rep G.rel a c ∧ ¬ ∃ b, rep G.rel a b ∧ rep Q.rel b c ∧ ¬ rep Q.rel c b := by
  have e : thin Q G = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_thinC Q.rel G.rel hb

/-- The test's spec applies where `(q ⟨ordPairs X, true⟩).ok`, the first conjunct. -/
theorem rep_orderedOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) {n : USize}
    (X : Vals (.arr B) n) (hb : (orderedOn q X).ok = true) :
    (q ⟨ordPairs X, true⟩).ok = true ∧
      (∀ xs y zs z, (∃ i, X.row i = xs) → (y :: zs) <:+ xs → z ∈ zs → rep (ordPairs X) (y, z) (y, z)) ∧
      ∀ xs ys, rep (orderedOn q X).rel xs ys ↔ (∃ i, X.row i = xs) ∧ ys = xs ∧
        ∀ y zs, (y :: zs) <:+ xs → ∀ z ∈ zs, ∃ w, rep (q ⟨ordPairs X, true⟩).rel w (y, z) :=
  by unfold CRel.orderedOn at hb ⊢; rw [rep_ofC hb]; exact rep_orderedOnC (testC q) X (ofC_ok hb).1

theorem rep_ordered (Q : CRel B B) {n : USize} (X : Vals (.arr B) n) (hb : (ordered Q X).ok = true) :
    ∀ xs ys, rep (ordered Q X).rel xs ys ↔ (∃ i, X.row i = xs) ∧ ys = xs ∧ xs.Pairwise (fun y z => rep Q.rel y z) := by
  have e : ordered Q X = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_orderedC Q.rel X hb

theorem rep_sortSet (Q : CRel B B) {n : USize} (Y : Vals (.arr B) n) (hb : (sortSet Q Y).ok = true) :
    ∀ s ys, rep (sortSet Q Y).rel s ys ↔
      rep (Alg.setify Y) ys s ∧ (∃ i, Y.row i = ys) ∧ ys.Pairwise (fun y z => rep Q.rel y z) := by
  have e : sortSet Q Y = _ := guard_eq ok hb; rw [e] at hb ⊢; rw [rep_ofC hb]; replace hb := (ofC_ok hb).1; exact rep_sortSetC Q.rel Y hb

end CRel

end LeetQ.Rel
