/-
  The runtime ok-bit on the ops that take a test: `pairsIn`, `swapIn`, `estOn`/`est`, `thinOn`/`thin`,
  `orderedOn`/`ordered`, `sortSet`. A twin takes its test as `qC : Rel → Rel × Bool` and `&&`s the test's bit with
  its pieces'; `ranC_oneFit`, `domC_oneFit`, `diffC_ok`, `antiJoinC_ok` read one piece's bit as the bundle the plain
  read-back (`rep_estOn`, `rep_thinOn`, `rep_orderedOn`, …) takes at it, so each `rep_<op>C` is that read-back under
  the twin's bit. What stays is not a size bound: the test's own spec, which a caller applies at the test bits each
  `rep_<op>C` hands back, and `unionC`'s `hat` inside `suffix`.
-/
import LeetQ.Rel.CRelLoop
import LeetQ.Rel.CRelPower
import LeetQ.Rel.RepSort

namespace LeetQ.Rel

open QLean QLean.Kernel QLean.Verify LeetQ.Rel LeetQ.Rel.Alg LeetQ.Rel.KernelWF Freyd Freyd.Alg Freyd.Alg.RelSet
open LeetQ.Rel.Rep LeetQ.Rel.Rep.FoldN LeetQ.Rel.Rep.OpsN LeetQ.Rel.Rep.Prim LeetQ.Rel.Rep.ListN

-- `unionC`'s `hat` inside `suffix`, as `CRelLoop`'s (local there): `razeTo`'s read-back of two atom parts
set_option quotPrecheck false in
local notation "hatOK" => ∀ (t : QAtomicType) {n m : USize} (x : Arr t n) (y : Arr t m)
  (hN : ((#[⟨n, x⟩, ⟨m, y⟩] : Array (Part (.atom t))).toList.map fun c : Part (.atom t) => c.1.toNat).sum <
    USize.size), Vals.RazeFits (.atom t) x y → (razeTo t #[⟨n, x⟩, ⟨m, y⟩] rfl hN).toList = x.toList ++ y.toList

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

/-- `diffC`'s bit is `rep_diff`'s premises (`diffOK`), as `rep_interC`'s: the product codes' bit its `hc`
    (`codesC_fits`, `codes_faithful_wf`, `pairs_eq_codes`), the `fitsN` bits its `hk`, `hv`. -/
theorem diffC_ok (R S : Rel A B) (hb : (diffC R S).2 = true) : diffOK(A, B, R, S) := by
  simp only [diffC, Bool.and_eq_true] at hb
  obtain ⟨⟨hcb, hk⟩, hv⟩ := hb
  have hc := (codes_faithful_wf (.prod A B) _ (Obj.codesC_fits (.prod A B) _ hcb)).1
  have e : ∀ {α β : Type} (f : α → β) (a b : α), #v[a, b].map f = #v[f a, f b] := fun _ _ _ => by simp
  have hp : pairsOK(R, S) := by rw [pairs_eq_codes, e]; exact hc
  exact fun _ e' => by
    subst e'; exact ⟨hp, pickFits_of_fitsN A R.key _ hk _ (by simp), pickFits_of_fitsN B R.val _ hv _ (by simp)⟩


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

/-- The pairs `(y, z)` `orderedOn` compares on `X`, `y` heading a suffix of an array of `X` and `z` in its rest: the
    coreflexive its test runs on. -/
def ordPairs {n : USize} (X : Vals (.arr B) n) : Rel (.prod B B) (.prod B B) :=
  let D := ran (suffix X ≫ uncons (ran (suffix X)).val)
  ran (pair (outl D) (outr D ≫ mem (ran (outr D)).val))

/-- **`orderedOn` under `orderedOnC`'s bit**: `rep_orderedOn` at its pieces' bits — `suffix` by `rep_suffixC`, then
    `ranC_oneFit`, `unconsC_fits`, `compC_cmpOK`, `memC_ok`, `pairC_ok`, `antiJoinC_ok`, `domC_oneFit` — with the
    test's bit at `ordPairs X` for its spec. What stays: `unionC`'s `hat`. -/
theorem rep_orderedOnC (qC : Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool) {n : USize}
    (X : Vals (.arr B) n) (hat : hatOK) (hb : (orderedOnC qC X).2 = true) :
    (qC (ordPairs X)).2 = true ∧
      (∀ xs y zs z, (∃ i, X.row i = xs) → (y :: zs) <:+ xs → z ∈ zs → rep (ordPairs X) (y, z) (y, z)) ∧
      ∀ xs ys, rep (orderedOnC qC X).1 xs ys ↔ (∃ i, X.row i = xs) ∧ ys = xs ∧
        ∀ y zs, (y :: zs) <:+ xs → ∀ z ∈ zs, ∃ w, rep (qC (ordPairs X)).1 w (y, z) := by
  simp only [orderedOnC, Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hS, hW⟩, hu⟩, hT⟩, hD⟩, hV⟩, hm⟩, hM⟩, hyz⟩, hE⟩, ht⟩, hbad⟩, hdb⟩, hC⟩, hdC⟩, hr⟩ := hb
  have hm' := memC_ok _ hm
  exact ⟨ht, rep_orderedOn (fun r => (qC r).1) X (rep_suffixC X hat hS) _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
    _ rfl _ rfl _ rfl _ rfl
    ⟨ranC_oneFit _ hW, fun _ e _ _ _ _ => by subst e; exact unconsC_fits _ hu, compC_cmpOK _ _ hT,
      ranC_oneFit _ hD, ranC_oneFit _ hV, hm'.1, hm'.2, compC_cmpOK _ _ hM, pairC_ok _ _ hyz, ranC_oneFit _ hE,
      antiJoinC_ok _ _ hbad, domC_oneFit _ hdb, compC_cmpOK _ _ hC, domC_oneFit _ hdC, antiJoinC_ok _ _ hr⟩⟩

/-- **`ordered(Q)` under `orderedC`'s bit**: `rep_orderedOnC` at `pairsInC Q`, in `Pairwise` form
    (`pairwise_of_orderedOn`), the test's bit its `hq` (`compC_cmpOK`). What stays: `unionC`'s `hat`. -/
theorem rep_orderedC (Q : Rel B B) {n : USize} (X : Vals (.arr B) n) (hat : hatOK) (hb : (orderedC Q X).2 = true) :
    ∀ xs ys, rep (orderedC Q X).1 xs ys ↔ (∃ i, X.row i = xs) ∧ ys = xs ∧ xs.Pairwise (fun y z => rep Q y z) := by
  obtain ⟨ht, h1, h2⟩ := rep_orderedOnC (pairsInC Q) X hat hb
  exact pairwise_of_orderedOn Q X _ (ordPairs X) (compC_cmpOK (ordPairs X) _ ht) h1 h2

/-- **`sortSet(Q)` under `sortSetC`'s bit**: `rep_sortSet` at `rep_orderedC` and `compC`'s bit (`compC_cmpOK`). What
    stays: `unionC`'s `hat`. -/
theorem rep_sortSetC (Q : Rel B B) {n : USize} (Y : Vals (.arr B) n) (hat : hatOK) (hb : (sortSetC Q Y).2 = true) :
    ∀ s ys, rep (sortSetC Q Y).1 s ys ↔
      rep (setify Y) ys s ∧ (∃ i, Y.row i = ys) ∧ ys.Pairwise (fun y z => rep Q y z) := by
  simp only [sortSetC, Bool.and_eq_true] at hb
  exact rep_sortSet Q Y (rep_orderedC Q Y hat hb.1.2) (compC_cmpOK _ _ hb.2)

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

/-- A test over `CRel`s as a twin's test: it sees its input as ok, whose bit is already in the op's. -/
def testC (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) :
    Rel (.prod B B) (.prod B B) → Rel (.prod B B) (.prod B B) × Bool :=
  fun D => let s := q ⟨D, true⟩; (s.rel, s.ok)

/-- `pairsIn Q D`, ok where `Q`, `D` are and `pairsInC` ran within capacity. -/
def pairsIn (Q : CRel B B) (D : CRel (.prod B B) (.prod B B)) : CRel (.prod B B) (.prod B B) :=
  let r := pairsInC Q.rel D.rel; ⟨r.1, Q.ok && D.ok && r.2⟩

/-- `swapIn q D`, ok where `D` is, the test was and `swapInC` ran within capacity. -/
def swapIn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) (D : CRel (.prod B B) (.prod B B)) :
    CRel (.prod B B) (.prod B B) := let r := swapInC (testC q) D.rel; ⟨r.1, D.ok && r.2⟩

/-- `estOn q G`, ok where `G` is, the test was and `estOnC` ran within capacity. -/
def estOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) (G : CRel A B) : CRel A B :=
  let r := estOnC (testC q) G.rel; ⟨r.1, G.ok && r.2⟩

/-- `thinOn q G`, ok where `G` is, the test was and `thinOnC` ran within capacity. -/
def thinOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) (G : CRel A B) : CRel A B :=
  let r := thinOnC (testC q) G.rel; ⟨r.1, G.ok && r.2⟩

/-- `est(Q)` on `G`, ok where `Q`, `G` are and `estC` ran within capacity. -/
def est (Q : CRel B B) (G : CRel A B) : CRel A B := let r := estC Q.rel G.rel; ⟨r.1, Q.ok && G.ok && r.2⟩

/-- `thin(Q)` on `G`, ok where `Q`, `G` are and `thinC` ran within capacity. -/
def thin (Q : CRel B B) (G : CRel A B) : CRel A B := let r := thinC Q.rel G.rel; ⟨r.1, Q.ok && G.ok && r.2⟩

/-- `orderedOn q` on `X`, ok where the test was and `orderedOnC` ran within capacity. -/
def orderedOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) {n : USize} (X : Vals (.arr B) n) :
    CRel (.arr B) (.arr B) := let r := orderedOnC (testC q) X; ⟨r.1, r.2⟩

/-- `ordered(Q)` on `X`, ok where `Q` is and `orderedC` ran within capacity. -/
def ordered (Q : CRel B B) {n : USize} (X : Vals (.arr B) n) : CRel (.arr B) (.arr B) :=
  let r := orderedC Q.rel X; ⟨r.1, Q.ok && r.2⟩

/-- `sortSet(Q)` on `Y`, ok where `Q` is and `sortSetC` ran within capacity. -/
def sortSet (Q : CRel B B) {n : USize} (Y : Vals (.arr B) n) : CRel (.arr B) (.arr B) :=
  let r := sortSetC Q.rel Y; ⟨r.1, Q.ok && r.2⟩

theorem rep_pairsIn (Q : CRel B B) (D : CRel (.prod B B) (.prod B B)) (hb : (pairsIn Q D).ok = true) :
    ∀ p p', rep (pairsIn Q D).rel p p' ↔ rep D.rel p p' ∧ rep Q.rel p'.1 p'.2 :=
  rep_pairsInC Q.rel D.rel (by simp only [pairsIn, Bool.and_eq_true] at hb; exact hb.2)

theorem rep_swapIn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) (D : CRel (.prod B B) (.prod B B))
    (hb : (swapIn q D).ok = true) :
    ∀ p p', rep (swapIn q D).rel p p' ↔ p = p' ∧ ∃ u v w, ((∃ y, rep D.rel p (y, u)) ∧ ∃ z, rep D.rel p (v, z)) ∧
      rep (q ⟨Alg.ran (Alg.pair (outr D.rel) (outl D.rel)), true⟩).rel (u, v) w :=
  rep_swapInC (testC q) D.rel (by simp only [swapIn, Bool.and_eq_true] at hb; exact hb.2)

/-- The test's spec applies where `(q ⟨D, true⟩).ok`, the first conjunct. -/
theorem rep_estOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) (G : CRel A B)
    (hb : (estOn q G).ok = true) :
    (q ⟨Alg.ran (Alg.pair G.rel G.rel), true⟩).ok = true ∧ ∀ a b, rep (estOn q G).rel a b ↔ rep G.rel a b ∧
      ¬ ∃ c, rep G.rel a c ∧ c ≠ b ∧ ¬ rep (q ⟨Alg.ran (Alg.pair G.rel G.rel), true⟩).rel (b, c) (b, c) :=
  rep_estOnC (testC q) G.rel (by simp only [estOn, Bool.and_eq_true] at hb; exact hb.2)

/-- The test's spec applies where `(q ⟨D, true⟩).ok`, the first conjunct; `swapIn`'s bit reads it back
    (`rep_swapInC`). -/
theorem rep_thinOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) (G : CRel A B)
    (hb : (thinOn q G).ok = true) :
    (q ⟨Alg.ran (Alg.pair G.rel G.rel), true⟩).ok = true ∧
      (swapInC (testC q) (Alg.ran (Alg.pair G.rel G.rel))).2 = true ∧ ∀ a c, rep (thinOn q G).rel a c ↔
      rep G.rel a c ∧ ¬ ∃ b b' y, rep G.rel a b ∧ rep G.rel a b' ∧
        rep (q ⟨Alg.ran (Alg.pair G.rel G.rel), true⟩).rel (b, b') (y, c) ∧
        ¬ rep (swapInC (testC q) (Alg.ran (Alg.pair G.rel G.rel))).1 (b, b') (y, c) :=
  rep_thinOnC (testC q) G.rel (by simp only [thinOn, Bool.and_eq_true] at hb; exact hb.2)

theorem rep_est (Q : CRel B B) (G : CRel A B) (hb : (est Q G).ok = true) :
    ∀ a b, rep (est Q G).rel a b ↔ rep G.rel a b ∧ ∀ c, rep G.rel a c → c ≠ b → rep Q.rel b c :=
  rep_estC Q.rel G.rel (by simp only [est, Bool.and_eq_true] at hb; exact hb.2)

theorem rep_thin (Q : CRel B B) (G : CRel A B) (hb : (thin Q G).ok = true) :
    ∀ a c, rep (thin Q G).rel a c ↔ rep G.rel a c ∧ ¬ ∃ b, rep G.rel a b ∧ rep Q.rel b c ∧ ¬ rep Q.rel c b :=
  rep_thinC Q.rel G.rel (by simp only [thin, Bool.and_eq_true] at hb; exact hb.2)

/-- `hat`: `rep_unionC`'s; the test's spec applies where `(q ⟨ordPairs X, true⟩).ok`, the first conjunct. -/
theorem rep_orderedOn (q : CRel (.prod B B) (.prod B B) → CRel (.prod B B) (.prod B B)) {n : USize}
    (X : Vals (.arr B) n) (hat : hatOK) (hb : (orderedOn q X).ok = true) :
    (q ⟨ordPairs X, true⟩).ok = true ∧
      (∀ xs y zs z, (∃ i, X.row i = xs) → (y :: zs) <:+ xs → z ∈ zs → rep (ordPairs X) (y, z) (y, z)) ∧
      ∀ xs ys, rep (orderedOn q X).rel xs ys ↔ (∃ i, X.row i = xs) ∧ ys = xs ∧
        ∀ y zs, (y :: zs) <:+ xs → ∀ z ∈ zs, ∃ w, rep (q ⟨ordPairs X, true⟩).rel w (y, z) :=
  rep_orderedOnC (testC q) X hat hb

/-- `hat`: `rep_unionC`'s. -/
theorem rep_ordered (Q : CRel B B) {n : USize} (X : Vals (.arr B) n) (hat : hatOK) (hb : (ordered Q X).ok = true) :
    ∀ xs ys, rep (ordered Q X).rel xs ys ↔ (∃ i, X.row i = xs) ∧ ys = xs ∧ xs.Pairwise (fun y z => rep Q.rel y z) :=
  rep_orderedC Q.rel X hat (by simp only [ordered, Bool.and_eq_true] at hb; exact hb.2)

/-- `hat`: `rep_unionC`'s. -/
theorem rep_sortSet (Q : CRel B B) {n : USize} (Y : Vals (.arr B) n) (hat : hatOK) (hb : (sortSet Q Y).ok = true) :
    ∀ s ys, rep (sortSet Q Y).rel s ys ↔
      rep (Alg.setify Y) ys s ∧ (∃ i, Y.row i = ys) ∧ ys.Pairwise (fun y z => rep Q.rel y z) :=
  rep_sortSetC Q.rel Y hat (by simp only [sortSet, Bool.and_eq_true] at hb; exact hb.2)

end CRel

end LeetQ.Rel
