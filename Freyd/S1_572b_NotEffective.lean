import Freyd.S1_572_Recursive

/-!
# §1.572 (second half): R is NOT an effective regular category

The book (§1.572): "R is not effective: if E is an equivalence relation on ω which
appears as a level of ω → α, then a left-inverse α → ω chooses a set of
representatives for E, forcing E to be not just recursively enumerable, but
recursive."

This file supplies the halting-problem diagonalization behind that sentence and the
categorical statement itself, on top of `Freyd.S1_572_Recursive` (Kleene codes
`RecCode`, big-step `Eval`, the category R on `ExtNat` with its AC-regular
structure).

Layout:
* **Stage 1** — arithmetized computation witnesses: a `Nat`-level *derivation
  checker* `nodeOK`/`acceptN` (numbers encode whole `Eval`-derivations; checking a
  purported derivation is elementary arithmetic), with soundness and completeness
  against `Eval`.  This is the step-indexed-evaluation workhorse in witness form:
  `Kc e := ∃ wit, acceptN e wit = 1` is the halting set "code `e` halts on input
  `e`", and membership is semi-decided by searching `wit`.
* **Stage 2** — `Kc` is not recursive (`K_not_recursive`): the classical
  diagonalization, using `Eval.det` and the `mu` constructor.
* **Stage 3** — the checker itself is a *recursive* function of R
  (`Recursive2 acceptN`), so the equivalence relation `E` glueing `2e ~ 2e+1`
  exactly for `e ∈ Kc` is enumerated by a morphism of R; `E` is an equivalence
  relation in R (§1.567 sense) but NOT the level of any cover — a splitting would
  decide `Kc` (`r_not_effective`).
-/

namespace Freyd.Rcat

/-! ## Stage 1a: numbers as lists — `consN`-lists over the Cantor pairing

  A list of numbers is coded by `nil = 0`, `consN a l = cp a l + 1` (the `+ 1`
  keeps `consN` injective and nonzero, so a list is nonempty iff it is nonzero). -/

/-- Cons for number-coded lists. -/
noncomputable def consN (a l : Nat) : Nat := cp a l + 1

/-- Head of a number-coded list (0 on nil). -/
noncomputable def headN (l : Nat) : Nat := cfst (l - 1)

/-- Tail of a number-coded list (0 on nil). -/
noncomputable def tailN (l : Nat) : Nat := csnd (l - 1)

@[simp] theorem headN_consN (a l : Nat) : headN (consN a l) = a := by
  simp [headN, consN, cfst_cp]

@[simp] theorem tailN_consN (a l : Nat) : tailN (consN a l) = l := by
  simp [tailN, consN, csnd_cp]

theorem consN_ne_zero (a l : Nat) : consN a l ≠ 0 := Nat.succ_ne_zero _

/-- A nonzero code is a cons of its head and tail. -/
theorem consN_eta {l : Nat} (h : l ≠ 0) : consN (headN l) (tailN l) = l := by
  show cp (cfst (l - 1)) (csnd (l - 1)) + 1 = l
  rw [cp_surj (l - 1)]
  omega

/-- Drop `j` entries: `dropN 0 l = l`, `dropN (j+1) l = tailN (dropN j l)`. -/
noncomputable def dropN : Nat → Nat → Nat
  | 0, l => l
  | j + 1, l => tailN (dropN j l)

/-- The `j`-th entry of a number-coded list (0 out of range). -/
noncomputable def nthN (j l : Nat) : Nat := headN (dropN j l)

@[simp] theorem dropN_zero (l : Nat) : dropN 0 l = l := rfl

@[simp] theorem dropN_succ (j l : Nat) : dropN (j + 1) l = tailN (dropN j l) := rfl

theorem dropN_tailN (j l : Nat) : dropN j (tailN l) = dropN (j + 1) l := by
  induction j with
  | zero => rfl
  | succ j ih => show tailN (dropN j (tailN l)) = _; rw [ih]; rfl

@[simp] theorem nthN_zero (l : Nat) : nthN 0 l = headN l := rfl

theorem nthN_succ_consN (j a l : Nat) : nthN (j + 1) (consN a l) = nthN j l := by
  show headN (dropN (j + 1) (consN a l)) = headN (dropN j l)
  rw [← dropN_tailN, tailN_consN]

@[simp] theorem nthN_consN_zero (a l : Nat) : nthN 0 (consN a l) = a := by
  simp [nthN]

/-! ## Stage 1b: input vectors and code trees as numbers -/

/-- A `Vec k` as a number-coded list. -/
noncomputable def encVec : {k : Nat} → Vec k → Nat
  | 0, _ => 0
  | _ + 1, v => consN (v 0) (encVec (vtail v))

@[simp] theorem encVec_zero (v : Vec 0) : encVec v = 0 := rfl

theorem encVec_vcons {k : Nat} (a : Nat) (v : Vec k) :
    encVec (vcons a v) = consN a (encVec v) := by
  show consN (vcons a v 0) (encVec (vtail (vcons a v))) = consN a (encVec v)
  rw [vcons_zero, vtail_vcons]

theorem headN_encVec {k : Nat} (v : Vec (k + 1)) : headN (encVec v) = v 0 := by
  show headN (consN (v 0) (encVec (vtail v))) = v 0
  rw [headN_consN]

theorem tailN_encVec {k : Nat} (v : Vec (k + 1)) : tailN (encVec v) = encVec (vtail v) := by
  show tailN (consN (v 0) (encVec (vtail v))) = encVec (vtail v)
  rw [tailN_consN]

theorem nthN_encVec : ∀ {k : Nat} (v : Vec k) (i : Fin k), nthN i.val (encVec v) = v i := by
  intro k
  induction k with
  | zero => intro _ i; exact absurd i.isLt (Nat.not_lt_zero _)
  | succ k ih =>
    intro v i
    rcases i with ⟨(_ | j), hi⟩
    · show nthN 0 (consN (v 0) (encVec (vtail v))) = v 0
      rw [nthN_consN_zero]
    · show nthN (j + 1) (consN (v 0) (encVec (vtail v))) = _
      rw [nthN_succ_consN, ih (vtail v) ⟨j, Nat.lt_of_succ_lt_succ hi⟩]
      rfl

theorem dropN_encVec_len : ∀ {k : Nat} (v : Vec k), dropN k (encVec v) = 0 := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro v
    show dropN (k + 1) (encVec v) = 0
    rw [← vcons_head_tail v, encVec_vcons, ← dropN_tailN, tailN_consN]
    exact ih (vtail v)

theorem dropN_encVec_ne : ∀ {k : Nat} (v : Vec k) (j : Nat), j < k →
    dropN j (encVec v) ≠ 0 := by
  intro k
  induction k with
  | zero => intro _ j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    intro v j hj
    rw [← vcons_head_tail v, encVec_vcons]
    match j with
    | 0 => exact consN_ne_zero _ _
    | j + 1 =>
      rw [← dropN_tailN, tailN_consN]
      exact ih (vtail v) j (Nat.lt_of_succ_lt_succ hj)

/-- A number-coded list with exactly `k` entries (nonempty at each stage below `k`,
    empty at `k`) IS the encoding of the vector of its entries. -/
theorem encVec_of_checks : ∀ {k : Nat} (l : Nat), (∀ j, j < k → dropN j l ≠ 0) →
    dropN k l = 0 → encVec (fun i : Fin k => nthN i.val l) = l := by
  intro k
  induction k with
  | zero => intro l _ h0; exact h0.symm
  | succ k ih =>
    intro l hne hend
    have hl0 : l ≠ 0 := hne 0 (Nat.succ_pos _)
    have htail : encVec (fun i : Fin k => nthN i.val (tailN l)) = tailN l := by
      refine ih (tailN l) (fun j hj => ?_) ?_
      · rw [dropN_tailN]; exact hne (j + 1) (Nat.succ_lt_succ hj)
      · rw [dropN_tailN]; exact hend
    calc encVec (fun i : Fin (k + 1) => nthN i.val l)
        = consN (nthN 0 l) (encVec (vtail fun i : Fin (k + 1) => nthN i.val l)) := rfl
      _ = consN (headN l) (encVec (fun i : Fin k => nthN (i.val + 1) l)) := rfl
      _ = consN (headN l) (encVec (fun i : Fin k => nthN i.val (tailN l))) := by
            congr 1; apply congrArg; funext i
            show headN (dropN (i.val + 1) l) = headN (dropN i.val (tailN l))
            rw [dropN_tailN]
      _ = consN (headN l) (tailN l) := by rw [htail]
      _ = l := consN_eta hl0

/-- Gödel number of a Kleene code.  Tags: 0 zero, 1 succ, 2 proj, 3 comp, 4 prec,
    5 mu.  `comp` records the middle arity `m` explicitly so the checker can
    recover it. -/
noncomputable def encCode : {k : Nat} → RecCode k → Nat
  | _, .zero => cp 0 0
  | _, .succ => cp 1 0
  | _, .proj i => cp 2 i.val
  | _, .comp (m := m) f gs =>
      cp 3 (cp m (cp (encCode f) (encVec fun j => encCode (gs j))))
  | _, .prec g h => cp 4 (cp (encCode g) (encCode h))
  | _, .mu f => cp 5 (encCode f)

/-! ## Stage 1c: arithmetic indicators

  All checking is done with 0/1-valued arithmetic built from `eqInd`. -/

theorem eqInd_one_iff {a b : Nat} : eqInd a b = 1 ↔ a = b := by
  constructor
  · intro h
    by_cases hab : a = b
    · exact hab
    · rw [eqInd_ne hab] at h; omega
  · exact eqInd_eq

theorem eqInd_zero_iff {a b : Nat} : eqInd a b = 0 ↔ a ≠ b := by
  constructor
  · intro h hab
    rw [eqInd_eq hab] at h; omega
  · exact eqInd_ne

/-- Strict-order indicator: `ltInd a b = 1` iff `a < b`, else 0. -/
noncomputable def ltInd (a b : Nat) : Nat := eqInd (a + 1 - b) 0

theorem ltInd_of_lt {a b : Nat} (h : a < b) : ltInd a b = 1 := eqInd_eq (by omega)

theorem ltInd_of_ge {a b : Nat} (h : ¬ a < b) : ltInd a b = 0 := eqInd_ne (by omega)

theorem ltInd_one_iff {a b : Nat} : ltInd a b = 1 ↔ a < b := by
  constructor
  · intro h
    by_cases hab : a < b
    · exact hab
    · rw [ltInd_of_ge hab] at h; omega
  · exact ltInd_of_lt

/-- Disequality indicator. -/
noncomputable def neInd (a b : Nat) : Nat := 1 - eqInd a b

theorem neInd_of_ne {a b : Nat} (h : a ≠ b) : neInd a b = 1 := by
  rw [neInd, eqInd_ne h]

theorem neInd_one_iff {a b : Nat} : neInd a b = 1 ↔ a ≠ b := by
  constructor
  · intro h hab
    rw [neInd, eqInd_eq hab] at h; omega
  · exact neInd_of_ne

/-- In ℕ, a product is 1 exactly when both factors are. -/
theorem mul_eq_one_iff {a b : Nat} : a * b = 1 ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro h
    match a, b with
    | 0, b => rw [Nat.zero_mul] at h; omega
    | a, 0 => rw [Nat.mul_zero] at h; omega
    | a + 1, b + 1 =>
      have : (a + 1) * (b + 1) = a * b + a + b + 1 := by
        rw [Nat.mul_succ, Nat.succ_mul]; omega
      rw [this] at h
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      exact ⟨by omega, by omega⟩
  · rintro ⟨ha, hb⟩; rw [ha, hb]

/-- Bounded conjunction: product of `F 0 * ⋯ * F (m-1)`. -/
def bAllN (F : Nat → Nat) : Nat → Nat
  | 0 => 1
  | m + 1 => bAllN F m * F m

theorem bAllN_eq_one {F : Nat → Nat} : ∀ {m : Nat}, (∀ j, j < m → F j = 1) →
    bAllN F m = 1 := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    show bAllN F m * F m = 1
    rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h m (Nat.lt_succ_self m),
      Nat.mul_one]

theorem of_bAllN_eq_one {F : Nat → Nat} : ∀ {m : Nat}, bAllN F m = 1 →
    ∀ j, j < m → F j = 1 := by
  intro m
  induction m with
  | zero => intro _ j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ m ih =>
    intro h j hj
    obtain ⟨h1, h2⟩ := mul_eq_one_iff.mp h
    rcases Nat.lt_or_ge j m with hjm | hjm
    · exact ih h1 j hjm
    · have : j = m := by omega
      rw [this]; exact h2

theorem bAllN_congr {F G : Nat → Nat} : ∀ {m : Nat}, (∀ j, j < m → F j = G j) →
    bAllN F m = bAllN G m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    show bAllN F m * F m = bAllN G m * G m
    rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h m (Nat.lt_succ_self m)]

/-! ## Stage 1d: derivation nodes and the local checker

  A WITNESS is a number-coded list `W` of NODES; the node at index `i` is
  `mkNode c ins y kids` claiming "code `c` on input list `ins` evaluates to `y`",
  with `kids` pointing at the (strictly earlier) sub-derivation nodes.  `nodeOK i W`
  checks the claim of node `i` locally — pure arithmetic in `(i, W)`.  Every access
  to a child node goes through the guarded read `rdN` (0 unless the index is `< i`),
  so a node's check only depends on the list up to `i` — this gives stability of
  checked prefixes under appending new nodes. -/

/-- Node constructor: claimed code, input list, output, child pointers. -/
noncomputable def mkNode (c ins y kids : Nat) : Nat := cp c (cp ins (cp y kids))

/-- Claimed code of a node. -/
noncomputable def codeOf (nd : Nat) : Nat := cfst nd
/-- Claimed input list of a node. -/
noncomputable def insOf (nd : Nat) : Nat := cfst (csnd nd)
/-- Claimed output of a node. -/
noncomputable def outOf (nd : Nat) : Nat := cfst (csnd (csnd nd))
/-- Child pointers of a node. -/
noncomputable def kidsOf (nd : Nat) : Nat := csnd (csnd (csnd nd))

@[simp] theorem codeOf_mkNode (c ins y kids : Nat) : codeOf (mkNode c ins y kids) = c := by
  simp [codeOf, mkNode, cfst_cp]
@[simp] theorem insOf_mkNode (c ins y kids : Nat) : insOf (mkNode c ins y kids) = ins := by
  simp [insOf, mkNode, cfst_cp, csnd_cp]
@[simp] theorem outOf_mkNode (c ins y kids : Nat) : outOf (mkNode c ins y kids) = y := by
  simp [outOf, mkNode, cfst_cp, csnd_cp]
@[simp] theorem kidsOf_mkNode (c ins y kids : Nat) : kidsOf (mkNode c ins y kids) = kids := by
  simp [kidsOf, mkNode, csnd_cp]

/-- Guarded node read: node `idx` of `W`, or 0 unless `idx < i`. -/
noncomputable def rdN (i idx W : Nat) : Nat := ltInd idx i * nthN idx W

theorem rdN_of_lt {i idx : Nat} (h : idx < i) (W : Nat) : rdN i idx W = nthN idx W := by
  rw [rdN, ltInd_of_lt h, Nat.one_mul]

theorem rdN_congr {i W W' : Nat} (h : ∀ idx, idx < i → nthN idx W = nthN idx W')
    (idx : Nat) : rdN i idx W = rdN i idx W' := by
  by_cases hlt : idx < i
  · rw [rdN, rdN, h idx hlt]
  · rw [rdN, rdN, ltInd_of_ge hlt, Nat.zero_mul, Nat.zero_mul]

/-! Accessor bundle for the node under scrutiny.  (Recomputation is free — these
    are specification-level functions, never run.) -/

/-- Constructor tag of node `i`'s claimed code. -/
noncomputable def tagAt (i W : Nat) : Nat := cfst (codeOf (nthN i W))
/-- Payload of node `i`'s claimed code. -/
noncomputable def plAt (i W : Nat) : Nat := csnd (codeOf (nthN i W))
/-- Input list of node `i`. -/
noncomputable def insAt (i W : Nat) : Nat := insOf (nthN i W)
/-- Output of node `i`. -/
noncomputable def outAt (i W : Nat) : Nat := outOf (nthN i W)
/-- Child pointers of node `i`. -/
noncomputable def kidsAt (i W : Nat) : Nat := kidsOf (nthN i W)

/-! ### `comp` nodes — tag 3

  Code payload `cp m (cp f gsL)`; kids `cp fIdx gIdxs`.  Node claims: each gs-child
  `j < m` evaluates `gsL_j` on the same input; the f-child evaluates `f` on exactly
  the list of gs-outputs, giving this node's output. -/

/-- Middle arity of a comp node. -/
noncomputable def cmpM (i W : Nat) : Nat := cfst (plAt i W)
/-- Outer code of a comp node. -/
noncomputable def cmpF (i W : Nat) : Nat := cfst (csnd (plAt i W))
/-- List of inner codes of a comp node. -/
noncomputable def cmpGs (i W : Nat) : Nat := csnd (csnd (plAt i W))
/-- Pointer to the f-child. -/
noncomputable def cmpFIdx (i W : Nat) : Nat := cfst (kidsAt i W)
/-- Pointers to the gs-children. -/
noncomputable def cmpGIdx (i W : Nat) : Nat := csnd (kidsAt i W)
/-- The f-child node (guarded read). -/
noncomputable def cmpFnd (i W : Nat) : Nat := rdN i (cmpFIdx i W) W
/-- The f-child's input list (= the claimed middle values). -/
noncomputable def cmpFIns (i W : Nat) : Nat := insOf (cmpFnd i W)

/-- Check of the `j`-th gs-child of a comp node. -/
noncomputable def gOK (j i W : Nat) : Nat :=
  ltInd (nthN j (cmpGIdx i W)) i
  * eqInd (codeOf (rdN i (nthN j (cmpGIdx i W)) W)) (nthN j (cmpGs i W))
  * eqInd (insOf (rdN i (nthN j (cmpGIdx i W)) W)) (insAt i W)
  * eqInd (outOf (rdN i (nthN j (cmpGIdx i W)) W)) (nthN j (cmpFIns i W))
  * neInd (dropN j (cmpFIns i W)) 0

/-- Local check of a comp node. -/
noncomputable def compOK (i W : Nat) : Nat :=
  ltInd (cmpFIdx i W) i
  * eqInd (codeOf (cmpFnd i W)) (cmpF i W)
  * eqInd (outOf (cmpFnd i W)) (outAt i W)
  * eqInd (dropN (cmpM i W) (cmpFIns i W)) 0
  * bAllN (fun j => gOK j i W) (cmpM i W)

/-! ### `prec` nodes — tag 4

  Code payload `cp g h`.  Recursion argument = head of the input list.  Base
  (`head = 0`): one child, `g` on the tail.  Step (`head = n+1`): two children —
  the SAME prec code on `n :: tail` (kids `cp iA iB`, child A), then `h` on
  `n :: rA :: tail` (child B). -/

/-- Base child node of a prec node. -/
noncomputable def prNd0 (i W : Nat) : Nat := rdN i (cfst (kidsAt i W)) W
/-- Step child B (the h-evaluation). -/
noncomputable def prNdB (i W : Nat) : Nat := rdN i (csnd (kidsAt i W)) W

/-- Local check of a prec node. -/
noncomputable def precOK (i W : Nat) : Nat :=
  eqInd (headN (insAt i W)) 0 *
    (ltInd (cfst (kidsAt i W)) i
     * eqInd (codeOf (prNd0 i W)) (cfst (plAt i W))
     * eqInd (insOf (prNd0 i W)) (tailN (insAt i W))
     * eqInd (outOf (prNd0 i W)) (outAt i W))
  + neInd (headN (insAt i W)) 0 *
    (ltInd (cfst (kidsAt i W)) i
     * ltInd (csnd (kidsAt i W)) i
     * eqInd (codeOf (prNd0 i W)) (codeOf (nthN i W))
     * eqInd (insOf (prNd0 i W)) (consN (headN (insAt i W) - 1) (tailN (insAt i W)))
     * eqInd (codeOf (prNdB i W)) (csnd (plAt i W))
     * eqInd (insOf (prNdB i W))
         (consN (headN (insAt i W) - 1) (consN (outOf (prNd0 i W)) (tailN (insAt i W))))
     * eqInd (outOf (prNdB i W)) (outAt i W))

/-! ### `mu` nodes — tag 5

  Code payload = the inner code `f`.  Kids = list of `y+1` pointers (`y` = output):
  child `t` evaluates `f` on `t :: ins`, nonzero for `t < y`, zero at `t = y`. -/

/-- The `t`-th child of a mu node. -/
noncomputable def muNd (t i W : Nat) : Nat := rdN i (nthN t (kidsAt i W)) W

/-- Check of the `t`-th (strict, nonzero-output) child of a mu node. -/
noncomputable def muStepOK (t i W : Nat) : Nat :=
  ltInd (nthN t (kidsAt i W)) i
  * eqInd (codeOf (muNd t i W)) (plAt i W)
  * eqInd (insOf (muNd t i W)) (consN t (insAt i W))
  * neInd (outOf (muNd t i W)) 0

/-- Local check of a mu node. -/
noncomputable def muOK (i W : Nat) : Nat :=
  bAllN (fun t => muStepOK t i W) (outAt i W)
  * (ltInd (nthN (outAt i W) (kidsAt i W)) i
     * eqInd (codeOf (muNd (outAt i W) i W)) (plAt i W)
     * eqInd (insOf (muNd (outAt i W) i W)) (consN (outAt i W) (insAt i W))
     * eqInd (outOf (muNd (outAt i W) i W)) 0)

/-- THE LOCAL CHECKER: node `i` of witness list `W` makes a locally valid claim.
    Exactly one tag indicator fires, so `nodeOK i W = 1` iff the branch for the
    claimed code's constructor checks out. -/
noncomputable def nodeOK (i W : Nat) : Nat :=
  eqInd (tagAt i W) 0 * eqInd (outAt i W) 0
  + eqInd (tagAt i W) 1 * eqInd (outAt i W) (headN (insAt i W) + 1)
  + eqInd (tagAt i W) 2 * eqInd (outAt i W) (nthN (plAt i W) (insAt i W))
  + eqInd (tagAt i W) 3 * compOK i W
  + eqInd (tagAt i W) 4 * precOK i W
  + eqInd (tagAt i W) 5 * muOK i W

/-! ### Branch extraction and branch builders

  `nodeOK` is a sum of guarded branches with mutually exclusive guards: once the
  tag is known, `nodeOK = 1` collapses to the corresponding branch. -/

section Branches

/-- Collapse the six-branch guarded sum to the branch selected by the tag. -/
theorem sum6_0 {t : Nat} (ht : t = 0) (B0 B1 B2 B3 B4 B5 : Nat) :
    eqInd t 0 * B0 + eqInd t 1 * B1 + eqInd t 2 * B2 + eqInd t 3 * B3
      + eqInd t 4 * B4 + eqInd t 5 * B5 = B0 := by
  subst ht
  rw [eqInd_eq rfl, eqInd_ne (by omega : (0:Nat) ≠ 1), eqInd_ne (by omega : (0:Nat) ≠ 2),
    eqInd_ne (by omega : (0:Nat) ≠ 3), eqInd_ne (by omega : (0:Nat) ≠ 4),
    eqInd_ne (by omega : (0:Nat) ≠ 5)]
  omega

theorem sum6_1 {t : Nat} (ht : t = 1) (B0 B1 B2 B3 B4 B5 : Nat) :
    eqInd t 0 * B0 + eqInd t 1 * B1 + eqInd t 2 * B2 + eqInd t 3 * B3
      + eqInd t 4 * B4 + eqInd t 5 * B5 = B1 := by
  subst ht
  rw [eqInd_eq rfl, eqInd_ne (by omega : (1:Nat) ≠ 0), eqInd_ne (by omega : (1:Nat) ≠ 2),
    eqInd_ne (by omega : (1:Nat) ≠ 3), eqInd_ne (by omega : (1:Nat) ≠ 4),
    eqInd_ne (by omega : (1:Nat) ≠ 5)]
  omega

theorem sum6_2 {t : Nat} (ht : t = 2) (B0 B1 B2 B3 B4 B5 : Nat) :
    eqInd t 0 * B0 + eqInd t 1 * B1 + eqInd t 2 * B2 + eqInd t 3 * B3
      + eqInd t 4 * B4 + eqInd t 5 * B5 = B2 := by
  subst ht
  rw [eqInd_eq rfl, eqInd_ne (by omega : (2:Nat) ≠ 0), eqInd_ne (by omega : (2:Nat) ≠ 1),
    eqInd_ne (by omega : (2:Nat) ≠ 3), eqInd_ne (by omega : (2:Nat) ≠ 4),
    eqInd_ne (by omega : (2:Nat) ≠ 5)]
  omega

theorem sum6_3 {t : Nat} (ht : t = 3) (B0 B1 B2 B3 B4 B5 : Nat) :
    eqInd t 0 * B0 + eqInd t 1 * B1 + eqInd t 2 * B2 + eqInd t 3 * B3
      + eqInd t 4 * B4 + eqInd t 5 * B5 = B3 := by
  subst ht
  rw [eqInd_eq rfl, eqInd_ne (by omega : (3:Nat) ≠ 0), eqInd_ne (by omega : (3:Nat) ≠ 1),
    eqInd_ne (by omega : (3:Nat) ≠ 2), eqInd_ne (by omega : (3:Nat) ≠ 4),
    eqInd_ne (by omega : (3:Nat) ≠ 5)]
  omega

theorem sum6_4 {t : Nat} (ht : t = 4) (B0 B1 B2 B3 B4 B5 : Nat) :
    eqInd t 0 * B0 + eqInd t 1 * B1 + eqInd t 2 * B2 + eqInd t 3 * B3
      + eqInd t 4 * B4 + eqInd t 5 * B5 = B4 := by
  subst ht
  rw [eqInd_eq rfl, eqInd_ne (by omega : (4:Nat) ≠ 0), eqInd_ne (by omega : (4:Nat) ≠ 1),
    eqInd_ne (by omega : (4:Nat) ≠ 2), eqInd_ne (by omega : (4:Nat) ≠ 3),
    eqInd_ne (by omega : (4:Nat) ≠ 5)]
  omega

theorem sum6_5 {t : Nat} (ht : t = 5) (B0 B1 B2 B3 B4 B5 : Nat) :
    eqInd t 0 * B0 + eqInd t 1 * B1 + eqInd t 2 * B2 + eqInd t 3 * B3
      + eqInd t 4 * B4 + eqInd t 5 * B5 = B5 := by
  subst ht
  rw [eqInd_eq rfl, eqInd_ne (by omega : (5:Nat) ≠ 0), eqInd_ne (by omega : (5:Nat) ≠ 1),
    eqInd_ne (by omega : (5:Nat) ≠ 2), eqInd_ne (by omega : (5:Nat) ≠ 3),
    eqInd_ne (by omega : (5:Nat) ≠ 4)]
  omega

variable {i W : Nat}

theorem zeroOK_of_nodeOK (h : nodeOK i W = 1) (ht : tagAt i W = 0) :
    outAt i W = 0 := by
  unfold nodeOK at h
  rw [sum6_0 ht] at h
  exact eqInd_one_iff.mp h

theorem succOK_of_nodeOK (h : nodeOK i W = 1) (ht : tagAt i W = 1) :
    outAt i W = headN (insAt i W) + 1 := by
  unfold nodeOK at h
  rw [sum6_1 ht] at h
  exact eqInd_one_iff.mp h

theorem projOK_of_nodeOK (h : nodeOK i W = 1) (ht : tagAt i W = 2) :
    outAt i W = nthN (plAt i W) (insAt i W) := by
  unfold nodeOK at h
  rw [sum6_2 ht] at h
  exact eqInd_one_iff.mp h

theorem compOK_of_nodeOK (h : nodeOK i W = 1) (ht : tagAt i W = 3) :
    compOK i W = 1 := by
  unfold nodeOK at h
  rwa [sum6_3 ht] at h

theorem precOK_of_nodeOK (h : nodeOK i W = 1) (ht : tagAt i W = 4) :
    precOK i W = 1 := by
  unfold nodeOK at h
  rwa [sum6_4 ht] at h

theorem muOK_of_nodeOK (h : nodeOK i W = 1) (ht : tagAt i W = 5) :
    muOK i W = 1 := by
  unfold nodeOK at h
  rwa [sum6_5 ht] at h

theorem nodeOK_of_tag0 (ht : tagAt i W = 0) (hy : outAt i W = 0) : nodeOK i W = 1 := by
  unfold nodeOK; rw [sum6_0 ht]; exact eqInd_eq hy

theorem nodeOK_of_tag1 (ht : tagAt i W = 1) (hy : outAt i W = headN (insAt i W) + 1) :
    nodeOK i W = 1 := by
  unfold nodeOK; rw [sum6_1 ht]; exact eqInd_eq hy

theorem nodeOK_of_tag2 (ht : tagAt i W = 2) (hy : outAt i W = nthN (plAt i W) (insAt i W)) :
    nodeOK i W = 1 := by
  unfold nodeOK; rw [sum6_2 ht]; exact eqInd_eq hy

theorem nodeOK_of_tag3 (ht : tagAt i W = 3) (hb : compOK i W = 1) : nodeOK i W = 1 := by
  unfold nodeOK; rwa [sum6_3 ht]

theorem nodeOK_of_tag4 (ht : tagAt i W = 4) (hb : precOK i W = 1) : nodeOK i W = 1 := by
  unfold nodeOK; rwa [sum6_4 ht]

theorem nodeOK_of_tag5 (ht : tagAt i W = 5) (hb : muOK i W = 1) : nodeOK i W = 1 := by
  unfold nodeOK; rwa [sum6_5 ht]

/-- Collapse the two-branch base/step sum of `precOK` (base selected). -/
theorem guard2_zero {n base step : Nat} (hn : n = 0) :
    eqInd n 0 * base + neInd n 0 * step = base := by
  subst hn; rw [eqInd_eq rfl, neInd, eqInd_eq rfl]; omega

/-- Collapse the two-branch base/step sum of `precOK` (step selected). -/
theorem guard2_succ {n base step : Nat} (hn : n ≠ 0) :
    eqInd n 0 * base + neInd n 0 * step = step := by
  rw [eqInd_ne hn, neInd, eqInd_ne hn]; omega

end Branches

/-! Equation lemmas for `encCode` (the nested recursion may compile
    non-definitionally, so we register them explicitly). -/

@[simp] theorem encCode_zero {k : Nat} : encCode (.zero : RecCode k) = cp 0 0 := by
  simp [encCode]
@[simp] theorem encCode_succ : encCode .succ = cp 1 0 := by simp [encCode]
@[simp] theorem encCode_proj {k : Nat} (i : Fin k) : encCode (.proj i) = cp 2 i.val := by
  simp [encCode]
@[simp] theorem encCode_comp {k m : Nat} (f : RecCode m) (gs : Fin m → RecCode k) :
    encCode (.comp f gs) = cp 3 (cp m (cp (encCode f) (encVec fun j => encCode (gs j)))) := by
  simp [encCode]
@[simp] theorem encCode_prec {k : Nat} (g : RecCode k) (h : RecCode (k + 2)) :
    encCode (.prec g h) = cp 4 (cp (encCode g) (encCode h)) := by simp [encCode]
@[simp] theorem encCode_mu {k : Nat} (f : RecCode (k + 1)) :
    encCode (.mu f) = cp 5 (encCode f) := by simp [encCode]

/-! ## Stage 1e: SOUNDNESS — an accepted claim really evaluates

  Strong induction on the node index (packaged as induction on an exclusive upper
  bound `B`): every locally valid node whose claimed code and input list are the
  encodings of a REAL code and input vector correctly claims a value of `Eval`. -/

theorem checkSound : ∀ (B W : Nat), (∀ j, j < B → nodeOK j W = 1) →
    ∀ i, i < B → ∀ {k : Nat} (c : RecCode k) (v : Vec k),
      codeOf (nthN i W) = encCode c → insOf (nthN i W) = encVec v →
      Eval c v (outOf (nthN i W)) := by
  intro B
  induction B with
  | zero => intro W _ i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ B ih =>
    intro W hval i hi k c v hcode hins
    have hOK : nodeOK i W = 1 := hval i hi
    have hval' : ∀ j, j < B → nodeOK j W = 1 := fun j hj => hval j (Nat.lt_succ_of_lt hj)
    have hiB : i ≤ B := Nat.lt_succ_iff.mp hi
    -- the induction hypothesis, repackaged for a child pointer idx < i
    have child : ∀ idx, idx < i → ∀ {k' : Nat} (c' : RecCode k') (v' : Vec k'),
        codeOf (nthN idx W) = encCode c' → insOf (nthN idx W) = encVec v' →
        Eval c' v' (outOf (nthN idx W)) :=
      fun idx hidx _ c' v' h1 h2 => ih W hval' idx (Nat.lt_of_lt_of_le hidx hiB) c' v' h1 h2
    cases c with
    | zero =>
      have htag : tagAt i W = 0 := by
        show cfst (codeOf (nthN i W)) = 0
        rw [hcode, encCode_zero, cfst_cp]
      have hout : outOf (nthN i W) = 0 := zeroOK_of_nodeOK hOK htag
      rw [hout]; exact .zero
    | succ =>
      have htag : tagAt i W = 1 := by
        show cfst (codeOf (nthN i W)) = 1
        rw [hcode, encCode_succ, cfst_cp]
      have hout : outAt i W = headN (insAt i W) + 1 := succOK_of_nodeOK hOK htag
      have hhd : headN (insAt i W) = v 0 := by
        show headN (insOf (nthN i W)) = v 0
        rw [hins, headN_encVec]
      show Eval .succ v (outAt i W)
      rw [hout, hhd]; exact .succ
    | proj j =>
      have htag : tagAt i W = 2 := by
        show cfst (codeOf (nthN i W)) = 2
        rw [hcode, encCode_proj, cfst_cp]
      have hpl : plAt i W = j.val := by
        show csnd (codeOf (nthN i W)) = j.val
        rw [hcode, encCode_proj, csnd_cp]
      have hout : outAt i W = nthN (plAt i W) (insAt i W) := projOK_of_nodeOK hOK htag
      show Eval (.proj j) v (outAt i W)
      rw [hout, hpl]
      show Eval (.proj j) v (nthN j.val (insAt i W))
      have : nthN j.val (insAt i W) = v j := by
        show nthN j.val (insOf (nthN i W)) = v j
        rw [hins, nthN_encVec]
      rw [this]; exact .proj j
    | @comp _ m f gs =>
      have htag : tagAt i W = 3 := by
        show cfst (codeOf (nthN i W)) = 3
        rw [hcode, encCode_comp, cfst_cp]
      have hpl : plAt i W = cp m (cp (encCode f) (encVec fun j => encCode (gs j))) := by
        show csnd (codeOf (nthN i W)) = _
        rw [hcode, encCode_comp, csnd_cp]
      have hm : cmpM i W = m := by rw [cmpM, hpl, cfst_cp]
      have hfc : cmpF i W = encCode f := by rw [cmpF, hpl, csnd_cp, cfst_cp]
      have hgsc : cmpGs i W = encVec (fun j => encCode (gs j)) := by
        rw [cmpGs, hpl, csnd_cp, csnd_cp]
      have hb := compOK_of_nodeOK hOK htag
      unfold compOK at hb
      obtain ⟨hb, hgAll⟩ := mul_eq_one_iff.mp hb
      obtain ⟨hb, hdrop⟩ := mul_eq_one_iff.mp hb
      obtain ⟨hb, hfout⟩ := mul_eq_one_iff.mp hb
      obtain ⟨hflt, hfcode⟩ := mul_eq_one_iff.mp hb
      have hfIdx : cmpFIdx i W < i := ltInd_one_iff.mp hflt
      have hfnd : cmpFnd i W = nthN (cmpFIdx i W) W := rdN_of_lt hfIdx W
      -- the claimed middle values
      let w : Vec m := fun j => nthN j.val (cmpFIns i W)
      -- per-child extraction
      have hgs : ∀ j : Fin m,
          nthN j.val (cmpGIdx i W) < i ∧
          codeOf (nthN (nthN j.val (cmpGIdx i W)) W) = encCode (gs j) ∧
          insOf (nthN (nthN j.val (cmpGIdx i W)) W) = insAt i W ∧
          outOf (nthN (nthN j.val (cmpGIdx i W)) W) = w j ∧
          dropN j.val (cmpFIns i W) ≠ 0 := by
        intro j
        have hj := of_bAllN_eq_one hgAll j.val (by rw [hm] at hgAll ⊢; exact j.isLt)
        unfold gOK at hj
        obtain ⟨hj, hne⟩ := mul_eq_one_iff.mp hj
        obtain ⟨hj, hout⟩ := mul_eq_one_iff.mp hj
        obtain ⟨hj, hins'⟩ := mul_eq_one_iff.mp hj
        obtain ⟨hlt, hcode'⟩ := mul_eq_one_iff.mp hj
        have hltj : nthN j.val (cmpGIdx i W) < i := ltInd_one_iff.mp hlt
        have hrd : rdN i (nthN j.val (cmpGIdx i W)) W = nthN (nthN j.val (cmpGIdx i W)) W :=
          rdN_of_lt hltj W
        rw [hrd] at hcode' hins' hout
        refine ⟨hltj, ?_, eqInd_one_iff.mp hins', eqInd_one_iff.mp hout, neInd_one_iff.mp hne⟩
        rw [eqInd_one_iff.mp hcode', hgsc, nthN_encVec]
      -- gs-children evaluate
      have hEvalG : ∀ j : Fin m, Eval (gs j) v (w j) := by
        intro j
        obtain ⟨hlt, hcode', hins', hout, _⟩ := hgs j
        have := child _ hlt (gs j) v hcode' (by rw [hins']; exact hins)
        rwa [hout] at this
      -- the f-child's input list is exactly the vector of middle values
      have hfIns : cmpFIns i W = encVec w := by
        have hd0 : dropN m (cmpFIns i W) = 0 := by
          have := eqInd_one_iff.mp hdrop; rwa [hm] at this
        have hdne : ∀ j, j < m → dropN j (cmpFIns i W) ≠ 0 :=
          fun j hj => (hgs ⟨j, hj⟩).2.2.2.2
        exact (encVec_of_checks (cmpFIns i W) hdne hd0).symm
      -- f evaluates on the middle values to this node's output
      have hEvalF : Eval f w (outAt i W) := by
        have hc : codeOf (nthN (cmpFIdx i W) W) = encCode f := by
          rw [← hfnd]; rw [eqInd_one_iff.mp hfcode, hfc]
        have hi' : insOf (nthN (cmpFIdx i W) W) = encVec w := by
          rw [← hfnd]
          show cmpFIns i W = encVec w
          exact hfIns
        have := child _ hfIdx f w hc hi'
        have hout' : outOf (nthN (cmpFIdx i W) W) = outAt i W := by
          rw [← hfnd]; exact eqInd_one_iff.mp hfout
        rwa [hout'] at this
      exact .comp w hEvalG hEvalF
    | prec g hstep =>
      have htag : tagAt i W = 4 := by
        show cfst (codeOf (nthN i W)) = 4
        rw [hcode, encCode_prec, cfst_cp]
      have hpl : plAt i W = cp (encCode g) (encCode hstep) := by
        show csnd (codeOf (nthN i W)) = _
        rw [hcode, encCode_prec, csnd_cp]
      have hb := precOK_of_nodeOK hOK htag
      unfold precOK at hb
      have hhd : headN (insAt i W) = v 0 := by
        show headN (insOf (nthN i W)) = v 0
        rw [hins, headN_encVec]
      have htl : tailN (insAt i W) = encVec (vtail v) := by
        show tailN (insOf (nthN i W)) = _
        rw [hins, tailN_encVec]
      rw [hhd] at hb
      rcases hv0 : v 0 with _ | n
      · -- base: recursion argument 0
        rw [guard2_zero hv0] at hb
        obtain ⟨hb, hout⟩ := mul_eq_one_iff.mp hb
        obtain ⟨hb, hins0⟩ := mul_eq_one_iff.mp hb
        obtain ⟨hlt0, hcode0⟩ := mul_eq_one_iff.mp hb
        have hidx : cfst (kidsAt i W) < i := ltInd_one_iff.mp hlt0
        have hrd : prNd0 i W = nthN (cfst (kidsAt i W)) W := rdN_of_lt hidx W
        have hcg : codeOf (nthN (cfst (kidsAt i W)) W) = encCode g := by
          rw [← hrd, eqInd_one_iff.mp hcode0, hpl, cfst_cp]
        have hig : insOf (nthN (cfst (kidsAt i W)) W) = encVec (vtail v) := by
          rw [← hrd, eqInd_one_iff.mp hins0, htl]
        have hEg := child _ hidx g (vtail v) hcg hig
        have hog : outOf (nthN (cfst (kidsAt i W)) W) = outAt i W := by
          rw [← hrd]; exact eqInd_one_iff.mp hout
        rw [hog] at hEg
        exact .prec_zero hv0 hEg
      · -- step: recursion argument n+1
        rw [guard2_succ (by omega : v 0 ≠ 0), hv0, Nat.add_sub_cancel] at hb
        obtain ⟨hb, houtB⟩ := mul_eq_one_iff.mp hb
        obtain ⟨hb, hinsB⟩ := mul_eq_one_iff.mp hb
        obtain ⟨hb, hcodeB⟩ := mul_eq_one_iff.mp hb
        obtain ⟨hb, hinsA⟩ := mul_eq_one_iff.mp hb
        obtain ⟨hb, hcodeA⟩ := mul_eq_one_iff.mp hb
        obtain ⟨hltA, hltB⟩ := mul_eq_one_iff.mp hb
        have hidxA : cfst (kidsAt i W) < i := ltInd_one_iff.mp hltA
        have hidxB : csnd (kidsAt i W) < i := ltInd_one_iff.mp hltB
        have hrdA : prNd0 i W = nthN (cfst (kidsAt i W)) W := rdN_of_lt hidxA W
        have hrdB : prNdB i W = nthN (csnd (kidsAt i W)) W := rdN_of_lt hidxB W
        -- child A: the same prec code, one step down
        have hcA : codeOf (nthN (cfst (kidsAt i W)) W) = encCode (.prec g hstep) := by
          rw [← hrdA, eqInd_one_iff.mp hcodeA, hcode]
        have hiA : insOf (nthN (cfst (kidsAt i W)) W) = encVec (vcons n (vtail v)) := by
          rw [← hrdA, eqInd_one_iff.mp hinsA, htl, encVec_vcons]
        have hEA := child _ hidxA (.prec g hstep) (vcons n (vtail v)) hcA hiA
        -- child B: the h-step on n :: rA :: tail
        have hcB : codeOf (nthN (csnd (kidsAt i W)) W) = encCode hstep := by
          rw [← hrdB, eqInd_one_iff.mp hcodeB, hpl, csnd_cp]
        have hiB' : insOf (nthN (csnd (kidsAt i W)) W)
            = encVec (vcons n (vcons (outOf (prNd0 i W)) (vtail v))) := by
          rw [← hrdB, eqInd_one_iff.mp hinsB, htl, encVec_vcons, encVec_vcons]
        have hEB := child _ hidxB hstep (vcons n (vcons (outOf (prNd0 i W)) (vtail v))) hcB hiB'
        have hoB : outOf (nthN (csnd (kidsAt i W)) W) = outAt i W := by
          rw [← hrdB]; exact eqInd_one_iff.mp houtB
        rw [hoB] at hEB
        have hEA' : Eval (.prec g hstep) (vcons n (vtail v)) (outOf (prNd0 i W)) := by
          rwa [hrdA]
        exact .prec_succ hv0 hEA' hEB
    | mu f =>
      have htag : tagAt i W = 5 := by
        show cfst (codeOf (nthN i W)) = 5
        rw [hcode, encCode_mu, cfst_cp]
      have hpl : plAt i W = encCode f := by
        show csnd (codeOf (nthN i W)) = _
        rw [hcode, encCode_mu, csnd_cp]
      have hb := muOK_of_nodeOK hOK htag
      have hinsAt : insAt i W = encVec v := hins
      unfold muOK at hb
      obtain ⟨hAll, hfin⟩ := mul_eq_one_iff.mp hb
      obtain ⟨hfin, hout0⟩ := mul_eq_one_iff.mp hfin
      obtain ⟨hfin, hinsY⟩ := mul_eq_one_iff.mp hfin
      obtain ⟨hltY, hcodeY⟩ := mul_eq_one_iff.mp hfin
      -- strict children t < y: nonzero values
      have hstrict : ∀ t, t < outAt i W →
          Eval f (vcons t v) (outOf (muNd t i W)) ∧ outOf (muNd t i W) ≠ 0 := by
        intro t ht
        have hj := of_bAllN_eq_one hAll t ht
        unfold muStepOK at hj
        obtain ⟨hj, hne⟩ := mul_eq_one_iff.mp hj
        obtain ⟨hj, hinsT⟩ := mul_eq_one_iff.mp hj
        obtain ⟨hltT, hcodeT⟩ := mul_eq_one_iff.mp hj
        have hidxT : nthN t (kidsAt i W) < i := ltInd_one_iff.mp hltT
        have hrdT : muNd t i W = nthN (nthN t (kidsAt i W)) W := rdN_of_lt hidxT W
        have hcT : codeOf (nthN (nthN t (kidsAt i W)) W) = encCode f := by
          rw [← hrdT, eqInd_one_iff.mp hcodeT, hpl]
        have hiT : insOf (nthN (nthN t (kidsAt i W)) W) = encVec (vcons t v) := by
          rw [← hrdT, eqInd_one_iff.mp hinsT, hinsAt, encVec_vcons]
        have hE := child _ hidxT f (vcons t v) hcT hiT
        rw [← hrdT] at hE
        exact ⟨hE, neInd_one_iff.mp hne⟩
      -- final child t = y: value 0
      have hidxY : nthN (outAt i W) (kidsAt i W) < i := ltInd_one_iff.mp hltY
      have hrdY : muNd (outAt i W) i W = nthN (nthN (outAt i W) (kidsAt i W)) W :=
        rdN_of_lt hidxY W
      have hcY : codeOf (nthN (nthN (outAt i W) (kidsAt i W)) W) = encCode f := by
        rw [← hrdY, eqInd_one_iff.mp hcodeY, hpl]
      have hiY : insOf (nthN (nthN (outAt i W) (kidsAt i W)) W)
          = encVec (vcons (outAt i W) v) := by
        rw [← hrdY, eqInd_one_iff.mp hinsY, hinsAt, encVec_vcons]
      have hEY := child _ hidxY f (vcons (outAt i W) v) hcY hiY
      rw [← hrdY, eqInd_one_iff.mp hout0] at hEY
      refine .mu (fun t => outOf (muNd t i W) - 1) hEY ?_
      intro t ht
      obtain ⟨hE, hne⟩ := hstrict t ht
      have : outOf (muNd t i W) - 1 + 1 = outOf (muNd t i W) := by omega
      rwa [this]

/-! ## Stage 1f: COMPLETENESS — every evaluation has an accepted witness

  Witness lists are built as Lean `List Nat`s (nodes in dependency order, children
  before parents) and only encoded at the end.  Because every child access in
  `nodeOK` is guarded below the node's own index, a checked prefix stays checked
  when the list grows — `nodeOK_congr` below is the only stability fact needed. -/

/-- Encode a `List Nat` as a number-coded list. -/
noncomputable def encListN : List Nat → Nat
  | [] => 0
  | a :: L => consN a (encListN L)

theorem nthN_encListN_prefix : ∀ (L : List Nat) (L' : List Nat) (j : Nat), j < L.length →
    nthN j (encListN (L ++ L')) = nthN j (encListN L) := by
  intro L
  induction L with
  | nil => intro L' j hj; exact absurd hj (Nat.not_lt_zero _)
  | cons a L ih =>
    intro L' j hj
    match j with
    | 0 =>
      show nthN 0 (consN a (encListN (L ++ L'))) = nthN 0 (consN a (encListN L))
      rw [nthN_consN_zero, nthN_consN_zero]
    | j + 1 =>
      show nthN (j + 1) (consN a (encListN (L ++ L'))) = nthN (j + 1) (consN a (encListN L))
      rw [nthN_succ_consN, nthN_succ_consN]
      exact ih L' j (Nat.lt_of_succ_lt_succ hj)

theorem nthN_encListN_at : ∀ (L : List Nat) (nd : Nat) (L' : List Nat),
    nthN L.length (encListN (L ++ nd :: L')) = nd := by
  intro L
  induction L with
  | nil => intro nd L'; exact nthN_consN_zero nd (encListN L')
  | cons a L ih =>
    intro nd L'
    show nthN (L.length + 1) (consN a (encListN (L ++ nd :: L'))) = nd
    rw [nthN_succ_consN]
    exact ih nd L'

/-- STABILITY: `nodeOK i` only reads the witness at indices `≤ i` (its own node
    directly, children through the guarded `rdN`), so it is invariant under any
    change beyond `i`. -/
theorem nodeOK_congr {i W W' : Nat} (hle : ∀ idx, idx ≤ i → nthN idx W = nthN idx W') :
    nodeOK i W = nodeOK i W' := by
  have hown : nthN i W = nthN i W' := hle i (Nat.le_refl i)
  have hrd : ∀ idx, rdN i idx W = rdN i idx W' :=
    rdN_congr fun idx h => hle idx (Nat.le_of_lt h)
  have hfnd : cmpFnd i W = cmpFnd i W' := by
    unfold cmpFnd cmpFIdx kidsAt
    rw [hown]; exact hrd _
  unfold nodeOK compOK precOK muOK gOK muStepOK cmpFnd cmpFIns cmpFIdx cmpGIdx cmpF cmpM
    cmpGs prNd0 prNdB muNd tagAt plAt insAt outAt kidsAt
  simp only [hown, hrd, hfnd]

/-- All nodes of a witness list check out. -/
def allValidL (L : List Nat) : Prop := ∀ j, j < L.length → nodeOK j (encListN L) = 1

theorem allValidL_nil : allValidL [] := fun _ hj => absurd hj (Nat.not_lt_zero _)

/-- Append one node to a valid list: old nodes stay valid by stability, so only the
    new node needs a check. -/
theorem appendNode {M : List Nat} (nd : Nat) (hM : allValidL M)
    (hnew : nodeOK M.length (encListN (M ++ [nd])) = 1) :
    allValidL (M ++ [nd]) ∧ M.length < (M ++ [nd]).length ∧
      nthN M.length (encListN (M ++ [nd])) = nd := by
  refine ⟨?_, ?_, nthN_encListN_at M nd []⟩
  · intro j hj
    simp only [List.length_append, List.length_cons, List.length_nil] at hj
    rcases Nat.lt_or_ge j M.length with hlt | hge
    · have hstab : nodeOK j (encListN (M ++ [nd])) = nodeOK j (encListN M) :=
        nodeOK_congr fun idx hidx =>
          nthN_encListN_prefix M [nd] idx (Nat.lt_of_le_of_lt hidx hlt)
      rw [hstab]; exact hM j hlt
    · have hj' : j = M.length := by omega
      subst hj'; exact hnew
  · simp only [List.length_append, List.length_cons, List.length_nil]; omega

/-- The builder property: a claim triple (code number, input list, output) can be
    installed — with a full sub-derivation — on top of any valid witness list. -/
def Builds (cnum insnum outnum : Nat) : Prop :=
  ∀ L : List Nat, allValidL L → ∃ L' : List Nat, allValidL (L ++ L') ∧
    ∃ idx, idx < (L ++ L').length ∧
      codeOf (nthN idx (encListN (L ++ L'))) = cnum ∧
      insOf (nthN idx (encListN (L ++ L'))) = insnum ∧
      outOf (nthN idx (encListN (L ++ L'))) = outnum

/-- Build a whole finite family of claims (used for the `comp` children and the
    `mu` search column). -/
theorem buildsFamily {m : Nat} (T : Fin m → Nat × Nat × Nat)
    (hT : ∀ j, Builds (T j).1 (T j).2.1 (T j).2.2) :
    ∀ L, allValidL L → ∃ L', allValidL (L ++ L') ∧
      ∃ idx : Fin m → Nat, ∀ j, idx j < (L ++ L').length ∧
        codeOf (nthN (idx j) (encListN (L ++ L'))) = (T j).1 ∧
        insOf (nthN (idx j) (encListN (L ++ L'))) = (T j).2.1 ∧
        outOf (nthN (idx j) (encListN (L ++ L'))) = (T j).2.2 := by
  induction m with
  | zero =>
    intro L hL
    refine ⟨[], by rw [List.append_nil]; exact hL, fun j => j.elim0, fun j => j.elim0⟩
  | succ m ih =>
    intro L hL
    obtain ⟨L₁, hval₁, i₀, hi₀, hc₀, hi₀', ho₀⟩ := hT 0 L hL
    obtain ⟨L₂, hval₂, idx, hidx⟩ :=
      ih (fun j => T j.succ) (fun j => hT j.succ) (L ++ L₁) hval₁
    rw [List.append_assoc] at hval₂
    refine ⟨L₁ ++ L₂, hval₂, fun j => Fin.cases i₀ idx j, fun j => ?_⟩
    refine Fin.cases ?_ ?_ j
    · -- index 0: stability of the first build under the later appends
      simp only [Fin.cases_zero]
      have hstab : nthN i₀ (encListN (L ++ (L₁ ++ L₂))) = nthN i₀ (encListN (L ++ L₁)) := by
        rw [← List.append_assoc]
        exact nthN_encListN_prefix (L ++ L₁) L₂ i₀ hi₀
      have hlen : i₀ < (L ++ (L₁ ++ L₂)).length := by
        rw [← List.append_assoc]
        simp only [List.length_append] at hi₀ ⊢
        omega
      exact ⟨hlen, by rw [hstab]; exact hc₀, by rw [hstab]; exact hi₀',
        by rw [hstab]; exact ho₀⟩
    · intro j
      simp only [Fin.cases_succ]
      have h := hidx j
      rw [List.append_assoc] at h
      exact h

/-! Builder lemmas: `nodeOK i W = 1` from the decoded content of the node and of
    its children.  These isolate the pairing arithmetic from the list bookkeeping
    of `checkComplete`. -/

/-- A comp node checks out. -/
theorem nodeOK_comp_build {i W m fidx y' insN fcode gcodes gidxs wN : Nat}
    (hcode : codeOf (nthN i W) = cp 3 (cp m (cp fcode gcodes)))
    (hins : insOf (nthN i W) = insN)
    (hout : outOf (nthN i W) = y')
    (hkids : kidsOf (nthN i W) = cp fidx gidxs)
    (hfidx : fidx < i)
    (hfcode : codeOf (nthN fidx W) = fcode)
    (hfins : insOf (nthN fidx W) = wN)
    (hfout : outOf (nthN fidx W) = y')
    (hdrop : dropN m wN = 0)
    (hchild : ∀ j, j < m →
       nthN j gidxs < i ∧
       codeOf (nthN (nthN j gidxs) W) = nthN j gcodes ∧
       insOf (nthN (nthN j gidxs) W) = insN ∧
       outOf (nthN (nthN j gidxs) W) = nthN j wN ∧
       dropN j wN ≠ 0) :
    nodeOK i W = 1 := by
  have htag : tagAt i W = 3 := by unfold tagAt; rw [hcode, cfst_cp]
  have hpl : plAt i W = cp m (cp fcode gcodes) := by unfold plAt; rw [hcode, csnd_cp]
  have hM : cmpM i W = m := by unfold cmpM; rw [hpl, cfst_cp]
  have hF : cmpF i W = fcode := by unfold cmpF; rw [hpl, csnd_cp, cfst_cp]
  have hGs : cmpGs i W = gcodes := by unfold cmpGs; rw [hpl, csnd_cp, csnd_cp]
  have hFIdx : cmpFIdx i W = fidx := by unfold cmpFIdx kidsAt; rw [hkids, cfst_cp]
  have hGIdx : cmpGIdx i W = gidxs := by unfold cmpGIdx kidsAt; rw [hkids, csnd_cp]
  have hFnd : cmpFnd i W = nthN fidx W := by
    unfold cmpFnd; rw [hFIdx]; exact rdN_of_lt hfidx W
  have hFIns : cmpFIns i W = wN := by unfold cmpFIns; rw [hFnd]; exact hfins
  have hinsAt : insAt i W = insN := hins
  have houtAt : outAt i W = y' := hout
  refine nodeOK_of_tag3 htag ?_
  have hgOK : ∀ j, j < m → gOK j i W = 1 := by
    intro j hj
    obtain ⟨h1, h2, h3, h4, h5⟩ := hchild j hj
    unfold gOK
    rw [hGIdx, hGs, hFIns, hinsAt, rdN_of_lt h1, h2, h3, h4, ltInd_of_lt h1,
      eqInd_eq rfl, eqInd_eq rfl, eqInd_eq rfl, neInd_of_ne h5]
  unfold compOK
  rw [hFIdx, hFnd, hFIns, hM, hF, hfcode, hfout, houtAt, hdrop, ltInd_of_lt hfidx,
    eqInd_eq rfl, eqInd_eq rfl, eqInd_eq rfl, bAllN_eq_one hgOK]

/-- A prec node with recursion argument 0 checks out. -/
theorem nodeOK_prec_base {i W gcode hcode' insN y' idx0 kB : Nat}
    (hcode : codeOf (nthN i W) = cp 4 (cp gcode hcode'))
    (hins : insOf (nthN i W) = insN)
    (hhd : headN insN = 0)
    (hout : outOf (nthN i W) = y')
    (hkids : kidsOf (nthN i W) = cp idx0 kB)
    (hidx : idx0 < i)
    (h0c : codeOf (nthN idx0 W) = gcode)
    (h0i : insOf (nthN idx0 W) = tailN insN)
    (h0o : outOf (nthN idx0 W) = y') : nodeOK i W = 1 := by
  have htag : tagAt i W = 4 := by unfold tagAt; rw [hcode, cfst_cp]
  have hpl : plAt i W = cp gcode hcode' := by unfold plAt; rw [hcode, csnd_cp]
  have hinsAt : insAt i W = insN := hins
  have hkidsAt : kidsAt i W = cp idx0 kB := hkids
  have hnd0 : prNd0 i W = nthN idx0 W := by
    unfold prNd0; rw [hkidsAt, cfst_cp]; exact rdN_of_lt hidx W
  have houtAt : outAt i W = y' := hout
  refine nodeOK_of_tag4 htag ?_
  unfold precOK
  rw [hinsAt, guard2_zero hhd, hkidsAt, cfst_cp, hnd0, hpl, cfst_cp, h0c, h0i, h0o,
    houtAt, ltInd_of_lt hidx, eqInd_eq rfl, eqInd_eq rfl, eqInd_eq rfl]

/-- A prec node with positive recursion argument checks out. -/
theorem nodeOK_prec_step {i W gcode hcode' insN n y' rA iA iB : Nat}
    (hcode : codeOf (nthN i W) = cp 4 (cp gcode hcode'))
    (hins : insOf (nthN i W) = insN)
    (hhd : headN insN = n + 1)
    (hout : outOf (nthN i W) = y')
    (hkids : kidsOf (nthN i W) = cp iA iB)
    (hA : iA < i) (hB : iB < i)
    (hAc : codeOf (nthN iA W) = cp 4 (cp gcode hcode'))
    (hAi : insOf (nthN iA W) = consN n (tailN insN))
    (hAo : outOf (nthN iA W) = rA)
    (hBc : codeOf (nthN iB W) = hcode')
    (hBi : insOf (nthN iB W) = consN n (consN rA (tailN insN)))
    (hBo : outOf (nthN iB W) = y') : nodeOK i W = 1 := by
  have htag : tagAt i W = 4 := by unfold tagAt; rw [hcode, cfst_cp]
  have hpl : plAt i W = cp gcode hcode' := by unfold plAt; rw [hcode, csnd_cp]
  have hinsAt : insAt i W = insN := hins
  have hkidsAt : kidsAt i W = cp iA iB := hkids
  have hndA : prNd0 i W = nthN iA W := by
    unfold prNd0; rw [hkidsAt, cfst_cp]; exact rdN_of_lt hA W
  have hndB : prNdB i W = nthN iB W := by
    unfold prNdB; rw [hkidsAt, csnd_cp]; exact rdN_of_lt hB W
  have houtAt : outAt i W = y' := hout
  refine nodeOK_of_tag4 htag ?_
  unfold precOK
  rw [hinsAt, guard2_succ (by rw [hhd]; omega)]
  rw [hkidsAt, cfst_cp, csnd_cp]
  rw [hndA, hndB]
  rw [hhd, Nat.add_sub_cancel, hpl, csnd_cp, hAc, hcode, hAi, hAo, hBc, hBi, hBo,
    houtAt, ltInd_of_lt hA, ltInd_of_lt hB, eqInd_eq rfl, eqInd_eq rfl, eqInd_eq rfl,
    eqInd_eq rfl, eqInd_eq rfl]

/-- A mu node checks out. -/
theorem nodeOK_mu_build {i W fcode insN y kidsN : Nat}
    (hcode : codeOf (nthN i W) = cp 5 fcode)
    (hins : insOf (nthN i W) = insN)
    (hout : outOf (nthN i W) = y)
    (hkids : kidsOf (nthN i W) = kidsN)
    (hchild : ∀ t, t ≤ y → nthN t kidsN < i ∧
        codeOf (nthN (nthN t kidsN) W) = fcode ∧
        insOf (nthN (nthN t kidsN) W) = consN t insN ∧
        (t < y → outOf (nthN (nthN t kidsN) W) ≠ 0) ∧
        (t = y → outOf (nthN (nthN t kidsN) W) = 0)) : nodeOK i W = 1 := by
  have htag : tagAt i W = 5 := by unfold tagAt; rw [hcode, cfst_cp]
  have hpl : plAt i W = fcode := by unfold plAt; rw [hcode, csnd_cp]
  have hinsAt : insAt i W = insN := hins
  have houtAt : outAt i W = y := hout
  have hkidsAt : kidsAt i W = kidsN := hkids
  refine nodeOK_of_tag5 htag ?_
  have hstep : ∀ t, t < y → muStepOK t i W = 1 := by
    intro t ht
    obtain ⟨h1, h2, h3, h4, _⟩ := hchild t (Nat.le_of_lt ht)
    have hnd : muNd t i W = nthN (nthN t kidsN) W := by
      unfold muNd; rw [hkidsAt]; exact rdN_of_lt h1 W
    unfold muStepOK
    rw [hkidsAt, hnd, hpl, hinsAt, h2, h3, ltInd_of_lt h1, eqInd_eq rfl, eqInd_eq rfl,
      neInd_of_ne (h4 ht)]
  obtain ⟨h1, h2, h3, _, h5⟩ := hchild y (Nat.le_refl y)
  have hnd : muNd y i W = nthN (nthN y kidsN) W := by
    unfold muNd; rw [hkidsAt]; exact rdN_of_lt h1 W
  unfold muOK
  rw [houtAt, hkidsAt, hnd, hpl, hinsAt, h2, h3, h5 rfl, ltInd_of_lt h1,
    eqInd_eq rfl, eqInd_eq rfl, eqInd_eq rfl,
    bAllN_eq_one (F := fun t => muStepOK t i W) hstep]

/-- COMPLETENESS: every `Eval`-derivation yields an accepted witness for its
    encoded claim, on top of any valid prefix. -/
theorem checkComplete : ∀ {k : Nat} {c : RecCode k} {v : Vec k} {y : Nat},
    Eval c v y → Builds (encCode c) (encVec v) y := by
  intro k c v y h
  induction h with
  | zero =>
    rename_i k' v'
    intro L hL
    have hnew : nodeOK L.length
        (encListN (L ++ [mkNode (encCode (.zero : RecCode k')) (encVec v') 0 0])) = 1 := by
      have hself := nthN_encListN_at L (mkNode (encCode (.zero : RecCode k')) (encVec v') 0 0) []
      refine nodeOK_of_tag0 ?_ ?_
      · show cfst (codeOf (nthN L.length _)) = 0
        rw [hself, codeOf_mkNode, encCode_zero, cfst_cp]
      · show outOf (nthN L.length _) = 0
        rw [hself, outOf_mkNode]
    obtain ⟨hval, hlen, hself⟩ := appendNode _ hL hnew
    exact ⟨_, hval, L.length, hlen, by rw [hself, codeOf_mkNode],
      by rw [hself, insOf_mkNode], by rw [hself, outOf_mkNode]⟩
  | succ =>
    rename_i v'
    intro L hL
    have hnew : nodeOK L.length
        (encListN (L ++ [mkNode (encCode .succ) (encVec v') (v' 0 + 1) 0])) = 1 := by
      have hself := nthN_encListN_at L (mkNode (encCode .succ) (encVec v') (v' 0 + 1) 0) []
      refine nodeOK_of_tag1 ?_ ?_
      · show cfst (codeOf (nthN L.length _)) = 1
        rw [hself, codeOf_mkNode, encCode_succ, cfst_cp]
      · show outOf (nthN L.length _) = headN (insOf (nthN L.length _)) + 1
        rw [hself, outOf_mkNode, insOf_mkNode, headN_encVec]
    obtain ⟨hval, hlen, hself⟩ := appendNode _ hL hnew
    exact ⟨_, hval, L.length, hlen, by rw [hself, codeOf_mkNode],
      by rw [hself, insOf_mkNode], by rw [hself, outOf_mkNode]⟩
  | proj i =>
    rename_i k' v'
    intro L hL
    have hnew : nodeOK L.length
        (encListN (L ++ [mkNode (encCode (.proj i)) (encVec v') (v' i) 0])) = 1 := by
      have hself := nthN_encListN_at L (mkNode (encCode (.proj i)) (encVec v') (v' i) 0) []
      refine nodeOK_of_tag2 ?_ ?_
      · show cfst (codeOf (nthN L.length _)) = 2
        rw [hself, codeOf_mkNode, encCode_proj, cfst_cp]
      · show outOf (nthN L.length _)
            = nthN (csnd (codeOf (nthN L.length _))) (insOf (nthN L.length _))
        rw [hself, outOf_mkNode, codeOf_mkNode, insOf_mkNode, encCode_proj, csnd_cp,
          nthN_encVec]
    obtain ⟨hval, hlen, hself⟩ := appendNode _ hL hnew
    exact ⟨_, hval, L.length, hlen, by rw [hself, codeOf_mkNode],
      by rw [hself, insOf_mkNode], by rw [hself, outOf_mkNode]⟩
  | comp w hg hf ihg ihf =>
    rename_i k' m f gs v' y'
    intro L hL
    -- children: the m inner evaluations, then the outer one
    obtain ⟨L₁, hval₁, gidx, hgidx⟩ :=
      buildsFamily (fun j => (encCode (gs j), encVec v', w j)) (fun j => ihg j) L hL
    obtain ⟨L₂, hval₂, fidx, hflen, hfcode, hfins, hfout⟩ := ihf (L ++ L₁) hval₁
    -- the new node
    obtain ⟨nd, hnd⟩ : ∃ nd, nd = mkNode (encCode (.comp f gs)) (encVec v') y'
        (cp fidx (encVec fun j => gidx j)) := ⟨_, rfl⟩
    have hself := nthN_encListN_at ((L ++ L₁) ++ L₂) nd []
    have hnew : nodeOK ((L ++ L₁) ++ L₂).length
        (encListN (((L ++ L₁) ++ L₂) ++ [nd])) = 1 := by
      refine nodeOK_comp_build (m := m) (fidx := fidx) (y' := y') (insN := encVec v')
        (fcode := encCode f) (gcodes := encVec fun j => encCode (gs j))
        (gidxs := encVec fun j => gidx j) (wN := encVec w)
        ?_ ?_ ?_ ?_ hflen ?_ ?_ ?_ (dropN_encVec_len w) ?_
      · rw [hself, hnd, codeOf_mkNode, encCode_comp]
      · rw [hself, hnd, insOf_mkNode]
      · rw [hself, hnd, outOf_mkNode]
      · rw [hself, hnd, kidsOf_mkNode]
      · rw [nthN_encListN_prefix _ [nd] fidx hflen]; exact hfcode
      · rw [nthN_encListN_prefix _ [nd] fidx hflen]; exact hfins
      · rw [nthN_encListN_prefix _ [nd] fidx hflen]; exact hfout
      · intro j hj
        obtain ⟨hjlen, hjc, hji, hjo⟩ := hgidx ⟨j, hj⟩
        have hjc' : codeOf (nthN (gidx ⟨j, hj⟩) (encListN (L ++ L₁)))
            = encCode (gs ⟨j, hj⟩) := hjc
        have hji' : insOf (nthN (gidx ⟨j, hj⟩) (encListN (L ++ L₁))) = encVec v' := hji
        have hjo' : outOf (nthN (gidx ⟨j, hj⟩) (encListN (L ++ L₁))) = w ⟨j, hj⟩ := hjo
        have hnth : nthN j (encVec fun j' => gidx j') = gidx ⟨j, hj⟩ :=
          nthN_encVec _ ⟨j, hj⟩
        have hstab : nthN (gidx ⟨j, hj⟩) (encListN (((L ++ L₁) ++ L₂) ++ [nd]))
            = nthN (gidx ⟨j, hj⟩) (encListN (L ++ L₁)) := by
          rw [List.append_assoc (L ++ L₁) L₂ [nd]]
          exact nthN_encListN_prefix (L ++ L₁) (L₂ ++ [nd]) _ hjlen
        have hjlenM : gidx ⟨j, hj⟩ < ((L ++ L₁) ++ L₂).length := by
          simp only [List.length_append] at hjlen ⊢; omega
        refine ⟨?_, ?_, ?_, ?_, dropN_encVec_ne w j hj⟩
        · rw [hnth]; exact hjlenM
        · rw [hnth, hstab, hjc', nthN_encVec (fun j' => encCode (gs j')) ⟨j, hj⟩]
        · rw [hnth, hstab, hji']
        · rw [hnth, hstab, hjo', nthN_encVec w ⟨j, hj⟩]
    obtain ⟨hvalAll, hlen, hself'⟩ := appendNode nd hval₂ hnew
    have hEq : L ++ (L₁ ++ (L₂ ++ [nd])) = ((L ++ L₁) ++ L₂) ++ [nd] := by
      simp only [List.append_assoc]
    refine ⟨L₁ ++ (L₂ ++ [nd]), ?_, ((L ++ L₁) ++ L₂).length, ?_, ?_, ?_, ?_⟩
    · rw [hEq]; exact hvalAll
    · rw [hEq]; exact hlen
    · rw [hEq, hself', hnd, codeOf_mkNode]
    · rw [hEq, hself', hnd, insOf_mkNode]
    · rw [hEq, hself', hnd, outOf_mkNode]
  | prec_zero h0 hg ihg =>
    rename_i k' g hstep v' y'
    intro L hL
    obtain ⟨L₁, hval₁, idx0, hi0, hc0, hins0, ho0⟩ := ihg L hL
    have hc0' : codeOf (nthN idx0 (encListN (L ++ L₁))) = encCode g := hc0
    have hins0' : insOf (nthN idx0 (encListN (L ++ L₁))) = encVec (vtail v') := hins0
    have ho0' : outOf (nthN idx0 (encListN (L ++ L₁))) = y' := ho0
    obtain ⟨nd, hnd⟩ : ∃ nd, nd = mkNode (encCode (.prec g hstep)) (encVec v') y'
        (cp idx0 0) := ⟨_, rfl⟩
    have hself := nthN_encListN_at (L ++ L₁) nd []
    have hnew : nodeOK (L ++ L₁).length (encListN ((L ++ L₁) ++ [nd])) = 1 := by
      refine nodeOK_prec_base (gcode := encCode g) (hcode' := encCode hstep)
        (insN := encVec v') (y' := y') (idx0 := idx0) (kB := 0)
        ?_ ?_ ?_ ?_ ?_ hi0 ?_ ?_ ?_
      · rw [hself, hnd, codeOf_mkNode, encCode_prec]
      · rw [hself, hnd, insOf_mkNode]
      · rw [headN_encVec]; exact h0
      · rw [hself, hnd, outOf_mkNode]
      · rw [hself, hnd, kidsOf_mkNode]
      · rw [nthN_encListN_prefix _ [nd] idx0 hi0]; exact hc0'
      · rw [nthN_encListN_prefix _ [nd] idx0 hi0, tailN_encVec]; exact hins0'
      · rw [nthN_encListN_prefix _ [nd] idx0 hi0]; exact ho0'
    obtain ⟨hvalAll, hlen, hself'⟩ := appendNode nd hval₁ hnew
    have hEq : L ++ (L₁ ++ [nd]) = (L ++ L₁) ++ [nd] := by
      simp only [List.append_assoc]
    refine ⟨L₁ ++ [nd], ?_, (L ++ L₁).length, ?_, ?_, ?_, ?_⟩
    · rw [hEq]; exact hvalAll
    · rw [hEq]; exact hlen
    · rw [hEq, hself', hnd, codeOf_mkNode]
    · rw [hEq, hself', hnd, insOf_mkNode]
    · rw [hEq, hself', hnd, outOf_mkNode]
  | prec_succ h0 hr hh ihr ihh =>
    rename_i k' g hstep v' n rA y'
    intro L hL
    obtain ⟨L₁, hval₁, iA, hiA, hcA, hinsA, hoA⟩ := ihr L hL
    obtain ⟨L₂, hval₂, iB, hiB, hcB, hinsB, hoB⟩ := ihh (L ++ L₁) hval₁
    have hcA' : codeOf (nthN iA (encListN (L ++ L₁))) = encCode (.prec g hstep) := hcA
    have hinsA' : insOf (nthN iA (encListN (L ++ L₁)))
        = encVec (vcons n (vtail v')) := hinsA
    have hoA' : outOf (nthN iA (encListN (L ++ L₁))) = rA := hoA
    have hcB' : codeOf (nthN iB (encListN ((L ++ L₁) ++ L₂))) = encCode hstep := hcB
    have hinsB' : insOf (nthN iB (encListN ((L ++ L₁) ++ L₂)))
        = encVec (vcons n (vcons rA (vtail v'))) := hinsB
    have hoB' : outOf (nthN iB (encListN ((L ++ L₁) ++ L₂))) = y' := hoB
    obtain ⟨nd, hnd⟩ : ∃ nd, nd = mkNode (encCode (.prec g hstep)) (encVec v') y'
        (cp iA iB) := ⟨_, rfl⟩
    have hself := nthN_encListN_at ((L ++ L₁) ++ L₂) nd []
    have hstabA : nthN iA (encListN (((L ++ L₁) ++ L₂) ++ [nd]))
        = nthN iA (encListN (L ++ L₁)) := by
      rw [List.append_assoc (L ++ L₁) L₂ [nd]]
      exact nthN_encListN_prefix (L ++ L₁) (L₂ ++ [nd]) _ hiA
    have hstabB : nthN iB (encListN (((L ++ L₁) ++ L₂) ++ [nd]))
        = nthN iB (encListN ((L ++ L₁) ++ L₂)) :=
      nthN_encListN_prefix _ [nd] _ hiB
    have hiAM : iA < ((L ++ L₁) ++ L₂).length := by
      simp only [List.length_append] at hiA ⊢; omega
    have hnew : nodeOK ((L ++ L₁) ++ L₂).length
        (encListN (((L ++ L₁) ++ L₂) ++ [nd])) = 1 := by
      refine nodeOK_prec_step (gcode := encCode g) (hcode' := encCode hstep)
        (insN := encVec v') (n := n) (y' := y') (rA := rA) (iA := iA) (iB := iB)
        ?_ ?_ ?_ ?_ ?_ hiAM hiB ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hself, hnd, codeOf_mkNode, encCode_prec]
      · rw [hself, hnd, insOf_mkNode]
      · rw [headN_encVec]; exact h0
      · rw [hself, hnd, outOf_mkNode]
      · rw [hself, hnd, kidsOf_mkNode]
      · rw [hstabA, hcA', encCode_prec]
      · rw [hstabA, hinsA', tailN_encVec, encVec_vcons]
      · rw [hstabA, hoA']
      · rw [hstabB, hcB']
      · rw [hstabB, hinsB', tailN_encVec, encVec_vcons, encVec_vcons]
      · rw [hstabB, hoB']
    obtain ⟨hvalAll, hlen, hself'⟩ := appendNode nd hval₂ hnew
    have hEq : L ++ (L₁ ++ (L₂ ++ [nd])) = ((L ++ L₁) ++ L₂) ++ [nd] := by
      simp only [List.append_assoc]
    refine ⟨L₁ ++ (L₂ ++ [nd]), ?_, ((L ++ L₁) ++ L₂).length, ?_, ?_, ?_, ?_⟩
    · rw [hEq]; exact hvalAll
    · rw [hEq]; exact hlen
    · rw [hEq, hself', hnd, codeOf_mkNode]
    · rw [hEq, hself', hnd, insOf_mkNode]
    · rw [hEq, hself', hnd, outOf_mkNode]
  | mu r hy hlt ihy ihlt =>
    rename_i k' f v' y'
    intro L hL
    -- the search column: children t = 0, …, y'
    have hT : ∀ t : Fin (y' + 1), Builds (encCode f) (encVec (vcons t.val v'))
        (if t.val = y' then 0 else r t.val + 1) := by
      intro t
      by_cases hty : t.val = y'
      · rw [if_pos hty, hty]; exact ihy
      · rw [if_neg hty]
        exact ihlt t.val (by have := t.isLt; omega)
    obtain ⟨L₁, hval₁, kidx, hkidx⟩ := buildsFamily
      (fun t : Fin (y' + 1) =>
        (encCode f, encVec (vcons t.val v'), if t.val = y' then 0 else r t.val + 1))
      hT L hL
    obtain ⟨nd, hnd⟩ : ∃ nd, nd = mkNode (encCode (.mu f)) (encVec v') y'
        (encVec fun t : Fin (y' + 1) => kidx t) := ⟨_, rfl⟩
    have hself := nthN_encListN_at (L ++ L₁) nd []
    have hnew : nodeOK (L ++ L₁).length (encListN ((L ++ L₁) ++ [nd])) = 1 := by
      refine nodeOK_mu_build (fcode := encCode f) (insN := encVec v') (y := y')
        (kidsN := encVec fun t : Fin (y' + 1) => kidx t) ?_ ?_ ?_ ?_ ?_
      · rw [hself, hnd, codeOf_mkNode, encCode_mu]
      · rw [hself, hnd, insOf_mkNode]
      · rw [hself, hnd, outOf_mkNode]
      · rw [hself, hnd, kidsOf_mkNode]
      · intro t ht
        have htlt : t < y' + 1 := by omega
        obtain ⟨htlen, htc, hti, hto⟩ := hkidx ⟨t, htlt⟩
        have htc' : codeOf (nthN (kidx ⟨t, htlt⟩) (encListN (L ++ L₁)))
            = encCode f := htc
        have hti' : insOf (nthN (kidx ⟨t, htlt⟩) (encListN (L ++ L₁)))
            = encVec (vcons t v') := hti
        have hto' : outOf (nthN (kidx ⟨t, htlt⟩) (encListN (L ++ L₁)))
            = if t = y' then 0 else r t + 1 := hto
        have hnth : nthN t (encVec fun t' : Fin (y' + 1) => kidx t') = kidx ⟨t, htlt⟩ :=
          nthN_encVec _ ⟨t, htlt⟩
        have hstab : nthN (kidx ⟨t, htlt⟩) (encListN ((L ++ L₁) ++ [nd]))
            = nthN (kidx ⟨t, htlt⟩) (encListN (L ++ L₁)) :=
          nthN_encListN_prefix _ [nd] _ htlen
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hnth]; exact htlen
        · rw [hnth, hstab, htc']
        · rw [hnth, hstab, hti', encVec_vcons]
        · intro htly
          rw [hnth, hstab, hto', if_neg (by omega)]
          omega
        · intro htey
          rw [hnth, hstab, hto', if_pos htey]
    obtain ⟨hvalAll, hlen, hself'⟩ := appendNode nd hval₁ hnew
    have hEq : L ++ (L₁ ++ [nd]) = (L ++ L₁) ++ [nd] := by
      simp only [List.append_assoc]
    refine ⟨L₁ ++ [nd], ?_, (L ++ L₁).length, ?_, ?_, ?_, ?_⟩
    · rw [hEq]; exact hvalAll
    · rw [hEq]; exact hlen
    · rw [hEq, hself', hnd, codeOf_mkNode]
    · rw [hEq, hself', hnd, insOf_mkNode]
    · rw [hEq, hself', hnd, outOf_mkNode]

/-! ## Stage 1g: the universal checker and the halting set `Kc`

  `acceptOn (cp e r) wit = 1` checks a witness that code `e` halts on input `r`.
  The diagonal specialization `acceptN e wit = acceptOn (cp e e) wit` holds iff
  `wit = cp W i` where `W` is a fully checked witness list
  whose node `i` claims "code number `e`, on the one-entry input list `[e]`,
  evaluates (to something)".  `Kc e` — "the code numbered `e` halts on input `e`" —
  is the Σ₁ set searched over `wit`. -/

/-- Universal accept predicate: `er = cp e r` packs the code number `e` and input `r`. -/
noncomputable def acceptOn (er wit : Nat) : Nat :=
  bAllN (fun j => nodeOK j (cfst wit)) (csnd wit + 1)
  * eqInd (codeOf (nthN (csnd wit) (cfst wit))) (cfst er)
  * eqInd (insOf (nthN (csnd wit) (cfst wit))) (consN (csnd er) 0)
/-- The claimed output of an accepting witness (depends only on `wit`). -/
noncomputable def uOut (_er wit : Nat) : Nat := outOf (nthN (csnd wit) (cfst wit))

/-- The output extractor as a UNARY recursive function of `wit` alone. -/
noncomputable def uOutW (wit : Nat) : Nat := outOf (nthN (csnd wit) (cfst wit))

theorem uOut_eq (er wit : Nat) : uOut er wit = uOutW wit := rfl

theorem encVec_one (e : Nat) : encVec (fun _ : Fin 1 => e) = consN e 0 := rfl

/-- SOUNDNESS: an accepted witness for a REAL unary code `c` numbered `cfst er`
    certifies a real evaluation of `c` on input `[csnd er]`, with value `uOut er wit`. -/
theorem acceptOn_sound {er wit : Nat} (h : acceptOn er wit = 1)
    {c : RecCode 1} (hc : cfst er = encCode c) :
    Eval c (fun _ => csnd er) (uOut er wit) := by
  unfold acceptOn at h
  obtain ⟨h, hins⟩ := mul_eq_one_iff.mp h
  obtain ⟨hall, hcode⟩ := mul_eq_one_iff.mp h
  have hval : ∀ j, j < csnd wit + 1 → nodeOK j (cfst wit) = 1 := of_bAllN_eq_one hall
  have hcode' : codeOf (nthN (csnd wit) (cfst wit)) = encCode c := by
    rw [eqInd_one_iff.mp hcode, hc]
  have hins' : insOf (nthN (csnd wit) (cfst wit)) = encVec (fun _ : Fin 1 => csnd er) := by
    rw [eqInd_one_iff.mp hins, encVec_one]
  exact checkSound (csnd wit + 1) (cfst wit) hval (csnd wit) (Nat.lt_succ_self _)
    c _ hcode' hins'

/-- COMPLETENESS: a real evaluation `Eval c [r] y` is certified by some witness for
    the packed input `cp (encCode c) r`, with claimed output exactly `y`. -/
theorem acceptOn_complete {c : RecCode 1} {r y : Nat} (h : Eval c (fun _ => r) y) :
    ∃ wit, acceptOn (cp (encCode c) r) wit = 1 ∧ uOut (cp (encCode c) r) wit = y := by
  obtain ⟨L', hval, i, hlen, hcode, hins, hout⟩ := checkComplete h [] allValidL_nil
  rw [List.nil_append] at hval hlen hcode hins hout
  refine ⟨cp (encListN L') i, ?_, ?_⟩
  · unfold acceptOn
    rw [cfst_cp, csnd_cp, cfst_cp, csnd_cp]
    have hval' : ∀ j, j < i + 1 → nodeOK j (encListN L') = 1 := fun j hj => hval j (by omega)
    rw [bAllN_eq_one hval', hcode, hins, encVec_one, eqInd_eq rfl, eqInd_eq rfl]
  · unfold uOut
    rw [cfst_cp, csnd_cp, hout]
/-- The accept predicate (0/1-valued arithmetic in `(e, wit)`). -/
noncomputable def acceptN (e wit : Nat) : Nat :=
  acceptOn (cp e e) wit

/-- The diagonal halting checker is the universal checker run on `(e,e)`. -/
theorem acceptN_eq_acceptOn (e wit : Nat) : acceptN e wit = acceptOn (cp e e) wit := rfl

/-- The halting set: some witness certifies that code number `e` halts on `e`. -/
def Kc (e : Nat) : Prop := ∃ wit, acceptN e wit = 1

/-- Accepted witnesses are sound: if `Kc e` and `c` is a real unary code numbered
    `e`, then `c` really halts on input `e`. -/
theorem Kc_sound {e : Nat} (h : Kc e) (c : RecCode 1) (hc : encCode c = e) :
    ∃ y, Eval c (fun _ => e) y := by
  obtain ⟨wit, hwit⟩ := h
  refine ⟨uOut (cp e e) wit, ?_⟩
  have hAccept : acceptOn (cp e e) wit = 1 := by
    rwa [← acceptN_eq_acceptOn]
  have hCode : cfst (cp e e) = encCode c := by rw [cfst_cp, hc]
  simpa only [csnd_cp] using acceptOn_sound hAccept hCode

/-- Halting is certified: if the unary code `c` halts on its own code number, its
    code number is in `Kc`. -/
theorem Kc_complete {c : RecCode 1} {y : Nat} (h : Eval c (fun _ => encCode c) y) :
    Kc (encCode c) := by
  obtain ⟨wit, hAccept, _⟩ := acceptOn_complete h
  exact ⟨wit, by rwa [acceptN_eq_acceptOn]⟩

/-! ## Stage 2: the halting set is NOT recursive

  The classical diagonalization.  Given a total recursive characteristic function
  `χ` of `Kc`, the code `d := μt. χ(e)` (the inner code ignores the search
  variable) halts on `e` exactly when `χ e ≠ 1`; running `d` on its own code
  number `e₀ = encCode d` gives `Kc e₀ ↔ ¬ Kc e₀`.  Uses only `Eval.det`, the
  `mu` constructor, and Stage 1's `Kc_sound`/`Kc_complete`. -/

theorem K_not_recursive : ¬ ∃ χ : Nat → Nat, Recursive1 χ ∧ ∀ e, (Kc e ↔ χ e = 1) := by
  rintro ⟨χ, hχrec, hχ⟩
  -- normalize the characteristic function to be 0/1-valued
  have hχ₂rec : Recursive1 fun e => eqInd (χ e) 1 :=
    Recursive1.comp2 Recursive2.eqInd hχrec (Recursive1.const 1)
  obtain ⟨cχ, hcχ⟩ := hχ₂rec
  -- the inner binary code (t, e) ↦ eqInd (χ e) 1, ignoring the search variable t
  have hinner : ∀ v : Vec 2, Eval (.comp cχ fun _ : Fin 1 => .proj 1) v
      (eqInd (χ (v 1)) 1) := by
    intro v
    exact .comp (fun _ => v 1) (fun _ => .proj 1) (hcχ fun _ => v 1)
  -- behaviour of the diagonal code d := μ(inner) on an abstract input E:
  -- it DIVERGES when χ E = 1 and halts (with 0) when χ E ≠ 1
  have key1 : ∀ E y : Nat, eqInd (χ E) 1 = 1 →
      ¬ Eval (.mu (.comp cχ fun _ : Fin 1 => .proj 1 : RecCode 2)) (fun _ => E) y := by
    intro E y h1 hy
    cases hy with
    | mu r hy0 _ =>
      have hval := hinner (vcons y fun _ : Fin 1 => E)
      have h1' : eqInd (χ ((vcons y fun _ : Fin 1 => E) 1)) 1 = 1 := by
        rw [vcons_one]; exact h1
      rw [h1'] at hval
      exact absurd (Eval.det hy0 hval) (by omega)
  have key2 : ∀ E : Nat, eqInd (χ E) 1 = 0 →
      Eval (.mu (.comp cχ fun _ : Fin 1 => .proj 1 : RecCode 2)) (fun _ => E) 0 := by
    intro E h0
    refine .mu (fun _ => 0) ?_ (fun i hi => absurd hi (Nat.not_lt_zero i))
    have hval := hinner (vcons 0 fun _ : Fin 1 => E)
    have hz : eqInd (χ ((vcons 0 fun _ : Fin 1 => E) 1)) 1 = 0 := by
      rw [vcons_one]; exact h0
    rwa [hz] at hval
  -- run d on its own code number
  by_cases hK : Kc (encCode (RecCode.mu (.comp cχ fun _ : Fin 1 => .proj 1 : RecCode 2)))
  · obtain ⟨y, hy⟩ := Kc_sound hK (.mu (.comp cχ fun _ : Fin 1 => .proj 1 : RecCode 2)) rfl
    exact key1 _ y (eqInd_eq ((hχ _).mp hK)) hy
  · exact hK (Kc_complete (key2 _ (eqInd_ne fun h => hK ((hχ _).mpr h))))

/-! ## Stage 3a: the checker is a RECURSIVE function

  `acceptN` was built from `cp`-arithmetic, guarded reads and bounded products
  precisely so that it falls under the closure lemmas of `S1_572_Recursive`.
  Two new closure principles are needed: primitive recursion WITH parameters
  (the raw `prec` constructor, of which `natIter` was the parameterless case)
  and the bounded product `bAllN`. -/

/-- Primitive recursion with parameters (the semantics of the `prec` code). -/
def precNat {k : Nat} (g : Vec k → Nat) (h : Vec (k + 2) → Nat) : Nat → Vec k → Nat
  | 0, w => g w
  | n + 1, w => h (vcons n (vcons (precNat g h n w) w))

/-- Closure under primitive recursion with parameters. -/
theorem RecursiveV.precNat {k : Nat} {g : Vec k → Nat} {h : Vec (k + 2) → Nat}
    (hg : RecursiveV g) (hh : RecursiveV h) :
    RecursiveV fun v : Vec (k + 1) => precNat g h (v 0) (vtail v) := by
  obtain ⟨cg, hcg⟩ := hg
  obtain ⟨ch, hch⟩ := hh
  refine ⟨.prec cg ch, fun v => ?_⟩
  have key : ∀ (n : Nat) (w : Vec k),
      Eval (.prec cg ch) (vcons n w) (Rcat.precNat g h n w) := by
    intro n w
    induction n with
    | zero => exact .prec_zero rfl (hcg w)
    | succ n ih =>
      exact .prec_succ rfl ih (hch (vcons n (vcons (Rcat.precNat g h n w) w)))
  have := key (v 0) (vtail v)
  rwa [vcons_head_tail v] at this

theorem Recursive2.const (c : Nat) : Recursive2 fun _ _ => c := RecursiveV.const 2 c

theorem Recursive1.tailN : Recursive1 tailN := by
  show Recursive1 fun l => Rcat.csnd (l - 1)
  have h1 : Recursive1 fun l => l - 1 := Recursive1.sub (show Recursive1 fun n => n from RecursiveV.proj 0) (Recursive1.const 1)
  exact Recursive1.comp h1 Recursive1.csnd

theorem Recursive1.headN : Recursive1 headN := by
  show Recursive1 fun l => Rcat.cfst (l - 1)
  have h1 : Recursive1 fun l => l - 1 := Recursive1.sub (show Recursive1 fun n => n from RecursiveV.proj 0) (Recursive1.const 1)
  exact Recursive1.comp h1 Recursive1.cfst

theorem Recursive2.dropN : Recursive2 dropN := by
  have base := RecursiveV.precNat (k := 1) (g := fun w => w 0)
    (h := fun u : Vec 3 => tailN (u 1))
    (RecursiveV.proj 0) (RecursiveV.comp1 Recursive1.tailN (RecursiveV.proj 1))
  refine base.congr fun v => ?_
  have aux : ∀ (n : Nat) (w : Vec 1),
      Rcat.precNat (fun w => w 0) (fun u : Vec 3 => tailN (u 1)) n w
        = Rcat.dropN n (w 0) := by
    intro n w
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg tailN ih
  exact aux (v 0) (vtail v)

theorem Recursive2.nthN : Recursive2 nthN :=
  RecursiveV.comp1 Recursive1.headN Recursive2.dropN

theorem Recursive2.ltInd : Recursive2 ltInd := by
  show Recursive2 fun a b => Rcat.eqInd (a + 1 - b) 0
  have h1 : Recursive2 fun a b => a + 1 :=
    Recursive2.comp2 Recursive2.add (show Recursive2 fun a _ => a from RecursiveV.proj 0) (Recursive2.const 1)
  have h2 : Recursive2 fun a b => a + 1 - b :=
    Recursive2.comp2 Recursive2.sub h1 (show Recursive2 fun _ b => b from RecursiveV.proj 1)
  exact Recursive2.comp2 Recursive2.eqInd h2 (Recursive2.const 0)

theorem Recursive2.neInd : Recursive2 neInd := by
  show Recursive2 fun a b => 1 - Rcat.eqInd a b
  exact Recursive2.comp2 Recursive2.sub (Recursive2.const 1) Recursive2.eqInd

theorem Recursive2.consN : Recursive2 consN := by
  show Recursive2 fun a l => Rcat.cp a l + 1
  exact Recursive2.comp2 Recursive2.add Recursive2.cp (Recursive2.const 1)

theorem Recursive1.codeOf : Recursive1 codeOf := Recursive1.cfst

theorem Recursive1.insOf : Recursive1 insOf := by
  show Recursive1 fun nd => Rcat.cfst (Rcat.csnd nd)
  exact Recursive1.comp Recursive1.csnd Recursive1.cfst

theorem Recursive1.outOf : Recursive1 outOf := by
  show Recursive1 fun nd => Rcat.cfst (Rcat.csnd (Rcat.csnd nd))
  have h1 : Recursive1 fun nd => Rcat.csnd (Rcat.csnd nd) :=
    Recursive1.comp Recursive1.csnd Recursive1.csnd
  exact Recursive1.comp h1 Recursive1.cfst

theorem Recursive1.kidsOf : Recursive1 kidsOf := by
  show Recursive1 fun nd => Rcat.csnd (Rcat.csnd (Rcat.csnd nd))
  have h1 : Recursive1 fun nd => Rcat.csnd (Rcat.csnd nd) :=
    Recursive1.comp Recursive1.csnd Recursive1.csnd
  exact Recursive1.comp h1 Recursive1.csnd

/-- Closure under bounded products: if `F` is recursive so is
    `v ↦ Π_{j < v 0} F (j :: tail v)`. -/
theorem RecursiveV.bAll {k : Nat} {F : Vec (k + 1) → Nat} (hF : RecursiveV F) :
    RecursiveV fun v : Vec (k + 1) => bAllN (fun j => F (vcons j (vtail v))) (v 0) := by
  have hh : RecursiveV fun u : Vec (k + 2) => u 1 * F (vcons (u 0) (vtail (vtail u))) := by
    refine RecursiveV.comp2 Recursive2.mul (RecursiveV.proj 1) ?_
    refine RecursiveV.comp (f := F)
      (gs := fun i u => (vcons (u 0) (vtail (vtail u))) i) hF ?_
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact RecursiveV.proj 0
    · exact RecursiveV.proj j.succ.succ
  have base := RecursiveV.precNat (RecursiveV.const k 1) hh
  refine base.congr fun v => ?_
  have aux : ∀ (n : Nat) (w : Vec k),
      Rcat.precNat (fun _ => 1)
        (fun u : Vec (k + 2) => u 1 * F (vcons (u 0) (vtail (vtail u))))
        n w = bAllN (fun j => F (vcons j w)) n := by
    intro n w
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg (fun x => x * F (vcons n w)) ih
  exact aux (v 0) (vtail v)

/-- Bounded product with a recursive bound, at the same arity. -/
theorem RecursiveV.bAllComp {k : Nat} {F : Vec (k + 1) → Nat} {b : Vec k → Nat}
    (hF : RecursiveV F) (hb : RecursiveV b) :
    RecursiveV fun v : Vec k => bAllN (fun j => F (vcons j v)) (b v) := by
  refine RecursiveV.comp
    (f := fun u : Vec (k + 1) => bAllN (fun j => F (vcons j (vtail u))) (u 0))
    (gs := fun idx (v : Vec k) => (vcons (b v) v) idx) (RecursiveV.bAll hF) ?_
  intro idx
  refine Fin.cases ?_ (fun j => ?_) idx
  · exact hb
  · exact RecursiveV.proj j

/-! Ternary recursiveness and lifting combinators, for the per-child checks. -/

/-- Ternary recursive functions. -/
def Recursive3 (f : Nat → Nat → Nat → Nat) : Prop :=
  RecursiveV fun v : Vec 3 => f (v 0) (v 1) (v 2)

theorem Recursive3.comp1 {F : Nat → Nat} (hF : Recursive1 F) {f : Nat → Nat → Nat → Nat}
    (hf : Recursive3 f) : Recursive3 fun a b c => F (f a b c) :=
  RecursiveV.comp1 hF hf

theorem Recursive3.comp2 {H : Nat → Nat → Nat} (hH : Recursive2 H)
    {f g : Nat → Nat → Nat → Nat} (hf : Recursive3 f) (hg : Recursive3 g) :
    Recursive3 fun a b c => H (f a b c) (g a b c) :=
  RecursiveV.comp2 hH hf hg

theorem Recursive3.const (c : Nat) : Recursive3 fun _ _ _ => c := RecursiveV.const 3 c

/-- Lift a binary recursive function to the last two of three arguments. -/
theorem Recursive3.lift23 {f : Nat → Nat → Nat} (hf : Recursive2 f) :
    Recursive3 fun _ b c => f b c :=
  RecursiveV.comp (f := fun w : Vec 2 => f (w 0) (w 1))
    (gs := fun i (v : Vec 3) => v i.succ) hf (fun i => RecursiveV.proj i.succ)

/-! ### Recursiveness of the checker, bottom-up along its definition

  Elaboration note: `comp1` always gets its unary `F` explicitly (higher-order
  unification against the folded checker constants picks wrong splits), and every
  intermediate gets an explicit `Recursive2 fun i W => …` type so the final
  `exact` is a pure definitional check. -/

theorem Recursive2.tagAt : Recursive2 tagAt := by
  have h1 : Recursive1 fun x => Rcat.cfst (Rcat.cfst x) :=
    Recursive1.comp Recursive1.cfst Recursive1.cfst
  have h2 : Recursive2 fun i W => Rcat.cfst (Rcat.cfst (Rcat.nthN i W)) :=
    RecursiveV.comp1 (F := fun x => Rcat.cfst (Rcat.cfst x)) h1 Recursive2.nthN
  exact h2

theorem Recursive2.plAt : Recursive2 plAt := by
  have h1 : Recursive1 fun x => Rcat.csnd (Rcat.cfst x) :=
    Recursive1.comp Recursive1.cfst Recursive1.csnd
  have h2 : Recursive2 fun i W => Rcat.csnd (Rcat.cfst (Rcat.nthN i W)) :=
    RecursiveV.comp1 (F := fun x => Rcat.csnd (Rcat.cfst x)) h1 Recursive2.nthN
  exact h2

theorem Recursive2.insAt : Recursive2 insAt := by
  have h2 : Recursive2 fun i W => Rcat.insOf (Rcat.nthN i W) :=
    RecursiveV.comp1 (F := Rcat.insOf) Recursive1.insOf Recursive2.nthN
  exact h2

theorem Recursive2.outAt : Recursive2 outAt := by
  have h2 : Recursive2 fun i W => Rcat.outOf (Rcat.nthN i W) :=
    RecursiveV.comp1 (F := Rcat.outOf) Recursive1.outOf Recursive2.nthN
  exact h2

theorem Recursive2.kidsAt : Recursive2 kidsAt := by
  have h2 : Recursive2 fun i W => Rcat.kidsOf (Rcat.nthN i W) :=
    RecursiveV.comp1 (F := Rcat.kidsOf) Recursive1.kidsOf Recursive2.nthN
  exact h2

theorem Recursive2.cmpM : Recursive2 cmpM := by
  have h2 : Recursive2 fun i W => Rcat.cfst (Rcat.plAt i W) :=
    RecursiveV.comp1 (F := Rcat.cfst) Recursive1.cfst Recursive2.plAt
  exact h2

theorem Recursive2.cmpF : Recursive2 cmpF := by
  have h2 : Recursive2 fun i W => Rcat.insOf (Rcat.plAt i W) :=
    RecursiveV.comp1 (F := Rcat.insOf) Recursive1.insOf Recursive2.plAt
  exact h2

theorem Recursive2.cmpGs : Recursive2 cmpGs := by
  have h1 : Recursive1 fun x => Rcat.csnd (Rcat.csnd x) :=
    Recursive1.comp Recursive1.csnd Recursive1.csnd
  have h2 : Recursive2 fun i W => Rcat.csnd (Rcat.csnd (Rcat.plAt i W)) :=
    RecursiveV.comp1 (F := fun x => Rcat.csnd (Rcat.csnd x)) h1 Recursive2.plAt
  exact h2

theorem Recursive2.cmpFIdx : Recursive2 cmpFIdx := by
  have h2 : Recursive2 fun i W => Rcat.cfst (Rcat.kidsAt i W) :=
    RecursiveV.comp1 (F := Rcat.cfst) Recursive1.cfst Recursive2.kidsAt
  exact h2

theorem Recursive2.cmpGIdx : Recursive2 cmpGIdx := by
  have h2 : Recursive2 fun i W => Rcat.csnd (Rcat.kidsAt i W) :=
    RecursiveV.comp1 (F := Rcat.csnd) Recursive1.csnd Recursive2.kidsAt
  exact h2

theorem Recursive2.cmpFnd : Recursive2 cmpFnd := by
  have ha : Recursive2 fun i W => Rcat.ltInd (Rcat.cmpFIdx i W) i :=
    Recursive2.comp2 Recursive2.ltInd Recursive2.cmpFIdx (show Recursive2 fun a _ => a from RecursiveV.proj 0)
  have hb : Recursive2 fun i W => Rcat.nthN (Rcat.cmpFIdx i W) W :=
    Recursive2.comp2 Recursive2.nthN Recursive2.cmpFIdx (show Recursive2 fun _ b => b from RecursiveV.proj 1)
  have h2 : Recursive2 fun i W =>
      Rcat.ltInd (Rcat.cmpFIdx i W) i * Rcat.nthN (Rcat.cmpFIdx i W) W :=
    Recursive2.comp2 Recursive2.mul ha hb
  exact h2

theorem Recursive2.cmpFIns : Recursive2 cmpFIns := by
  have h2 : Recursive2 fun i W => Rcat.insOf (Rcat.cmpFnd i W) :=
    RecursiveV.comp1 (F := Rcat.insOf) Recursive1.insOf Recursive2.cmpFnd
  exact h2

theorem Recursive3.gOK : Recursive3 gOK := by
  have hgidx : Recursive3 fun _ i W => Rcat.cmpGIdx i W :=
    Recursive3.lift23 Recursive2.cmpGIdx
  have hidx : Recursive3 fun j i W => Rcat.nthN j (Rcat.cmpGIdx i W) :=
    Recursive3.comp2 Recursive2.nthN (show Recursive3 fun a _ _ => a from RecursiveV.proj 0) hgidx
  have hnd : Recursive3 fun j i W =>
      Rcat.ltInd (Rcat.nthN j (Rcat.cmpGIdx i W)) i
        * Rcat.nthN (Rcat.nthN j (Rcat.cmpGIdx i W)) W :=
    Recursive3.comp2 Recursive2.mul
      (Recursive3.comp2 Recursive2.ltInd hidx (show Recursive3 fun _ b _ => b from RecursiveV.proj 1))
      (Recursive3.comp2 Recursive2.nthN hidx (show Recursive3 fun _ _ c => c from RecursiveV.proj 2))
  have hfins : Recursive3 fun _ i W => Rcat.cmpFIns i W :=
    Recursive3.lift23 Recursive2.cmpFIns
  have f1 : Recursive3 fun j i W => Rcat.ltInd (Rcat.nthN j (Rcat.cmpGIdx i W)) i :=
    Recursive3.comp2 Recursive2.ltInd hidx (show Recursive3 fun _ b _ => b from RecursiveV.proj 1)
  have f2 : Recursive3 fun j i W =>
      Rcat.eqInd (Rcat.codeOf (Rcat.ltInd (Rcat.nthN j (Rcat.cmpGIdx i W)) i
        * Rcat.nthN (Rcat.nthN j (Rcat.cmpGIdx i W)) W)) (Rcat.nthN j (Rcat.cmpGs i W)) :=
    Recursive3.comp2 Recursive2.eqInd
      (Recursive3.comp1 (F := Rcat.codeOf) Recursive1.codeOf hnd)
      (Recursive3.comp2 Recursive2.nthN (show Recursive3 fun a _ _ => a from RecursiveV.proj 0) (Recursive3.lift23 Recursive2.cmpGs))
  have f3 : Recursive3 fun j i W =>
      Rcat.eqInd (Rcat.insOf (Rcat.ltInd (Rcat.nthN j (Rcat.cmpGIdx i W)) i
        * Rcat.nthN (Rcat.nthN j (Rcat.cmpGIdx i W)) W)) (Rcat.insAt i W) :=
    Recursive3.comp2 Recursive2.eqInd
      (Recursive3.comp1 (F := Rcat.insOf) Recursive1.insOf hnd)
      (Recursive3.lift23 Recursive2.insAt)
  have f4 : Recursive3 fun j i W =>
      Rcat.eqInd (Rcat.outOf (Rcat.ltInd (Rcat.nthN j (Rcat.cmpGIdx i W)) i
        * Rcat.nthN (Rcat.nthN j (Rcat.cmpGIdx i W)) W)) (Rcat.nthN j (Rcat.cmpFIns i W)) :=
    Recursive3.comp2 Recursive2.eqInd
      (Recursive3.comp1 (F := Rcat.outOf) Recursive1.outOf hnd)
      (Recursive3.comp2 Recursive2.nthN (show Recursive3 fun a _ _ => a from RecursiveV.proj 0) hfins)
  have f5 : Recursive3 fun j i W => Rcat.neInd (Rcat.dropN j (Rcat.cmpFIns i W)) 0 :=
    Recursive3.comp2 Recursive2.neInd
      (Recursive3.comp2 Recursive2.dropN (show Recursive3 fun a _ _ => a from RecursiveV.proj 0) hfins) (Recursive3.const 0)
  have h2 : Recursive3 fun j i W =>
      Rcat.ltInd (Rcat.nthN j (Rcat.cmpGIdx i W)) i
      * Rcat.eqInd (Rcat.codeOf (Rcat.ltInd (Rcat.nthN j (Rcat.cmpGIdx i W)) i
          * Rcat.nthN (Rcat.nthN j (Rcat.cmpGIdx i W)) W)) (Rcat.nthN j (Rcat.cmpGs i W))
      * Rcat.eqInd (Rcat.insOf (Rcat.ltInd (Rcat.nthN j (Rcat.cmpGIdx i W)) i
          * Rcat.nthN (Rcat.nthN j (Rcat.cmpGIdx i W)) W)) (Rcat.insAt i W)
      * Rcat.eqInd (Rcat.outOf (Rcat.ltInd (Rcat.nthN j (Rcat.cmpGIdx i W)) i
          * Rcat.nthN (Rcat.nthN j (Rcat.cmpGIdx i W)) W)) (Rcat.nthN j (Rcat.cmpFIns i W))
      * Rcat.neInd (Rcat.dropN j (Rcat.cmpFIns i W)) 0 :=
    Recursive3.comp2 Recursive2.mul (Recursive3.comp2 Recursive2.mul
      (Recursive3.comp2 Recursive2.mul (Recursive3.comp2 Recursive2.mul f1 f2) f3) f4) f5
  exact h2

theorem Recursive2.compOK : Recursive2 compOK := by
  have b1 : Recursive2 fun i W => Rcat.ltInd (Rcat.cmpFIdx i W) i :=
    Recursive2.comp2 Recursive2.ltInd Recursive2.cmpFIdx (show Recursive2 fun a _ => a from RecursiveV.proj 0)
  have b2 : Recursive2 fun i W =>
      Rcat.eqInd (Rcat.codeOf (Rcat.cmpFnd i W)) (Rcat.cmpF i W) :=
    Recursive2.comp2 Recursive2.eqInd
      (RecursiveV.comp1 (F := Rcat.codeOf) Recursive1.codeOf Recursive2.cmpFnd)
      Recursive2.cmpF
  have b3 : Recursive2 fun i W =>
      Rcat.eqInd (Rcat.outOf (Rcat.cmpFnd i W)) (Rcat.outAt i W) :=
    Recursive2.comp2 Recursive2.eqInd
      (RecursiveV.comp1 (F := Rcat.outOf) Recursive1.outOf Recursive2.cmpFnd)
      Recursive2.outAt
  have b4 : Recursive2 fun i W =>
      Rcat.eqInd (Rcat.dropN (Rcat.cmpM i W) (Rcat.cmpFIns i W)) 0 :=
    Recursive2.comp2 Recursive2.eqInd
      (Recursive2.comp2 Recursive2.dropN Recursive2.cmpM Recursive2.cmpFIns)
      (Recursive2.const 0)
  have b5 : RecursiveV fun v : Vec 2 =>
      bAllN (fun j => Rcat.gOK j (v 0) (v 1)) (Rcat.cmpM (v 0) (v 1)) :=
    RecursiveV.bAllComp Recursive3.gOK Recursive2.cmpM
  have b5' : Recursive2 fun i W => bAllN (fun j => Rcat.gOK j i W) (Rcat.cmpM i W) := b5
  have h2 : Recursive2 fun i W =>
      Rcat.ltInd (Rcat.cmpFIdx i W) i
      * Rcat.eqInd (Rcat.codeOf (Rcat.cmpFnd i W)) (Rcat.cmpF i W)
      * Rcat.eqInd (Rcat.outOf (Rcat.cmpFnd i W)) (Rcat.outAt i W)
      * Rcat.eqInd (Rcat.dropN (Rcat.cmpM i W) (Rcat.cmpFIns i W)) 0
      * bAllN (fun j => Rcat.gOK j i W) (Rcat.cmpM i W) :=
    Recursive2.comp2 Recursive2.mul (Recursive2.comp2 Recursive2.mul
      (Recursive2.comp2 Recursive2.mul (Recursive2.comp2 Recursive2.mul b1 b2) b3) b4) b5'
  exact h2

theorem Recursive2.precOK : Recursive2 precOK := by
  have hHd : Recursive2 fun i W => Rcat.headN (Rcat.insAt i W) :=
    RecursiveV.comp1 (F := Rcat.headN) Recursive1.headN Recursive2.insAt
  have hTl : Recursive2 fun i W => Rcat.tailN (Rcat.insAt i W) :=
    RecursiveV.comp1 (F := Rcat.tailN) Recursive1.tailN Recursive2.insAt
  have hndB : Recursive2 fun i W =>
      Rcat.ltInd (Rcat.cmpGIdx i W) i * Rcat.nthN (Rcat.cmpGIdx i W) W :=
    Recursive2.comp2 Recursive2.mul
      (Recursive2.comp2 Recursive2.ltInd Recursive2.cmpGIdx (show Recursive2 fun a _ => a from RecursiveV.proj 0))
      (Recursive2.comp2 Recursive2.nthN Recursive2.cmpGIdx (show Recursive2 fun _ b => b from RecursiveV.proj 1))
  have hn1 : Recursive2 fun i W => Rcat.headN (Rcat.insAt i W) - 1 :=
    Recursive2.comp2 Recursive2.sub hHd (Recursive2.const 1)
  have c1 : Recursive2 fun i W => Rcat.eqInd (Rcat.headN (Rcat.insAt i W)) 0 :=
    Recursive2.comp2 Recursive2.eqInd hHd (Recursive2.const 0)
  have c2 : Recursive2 fun i W => Rcat.ltInd (Rcat.cmpFIdx i W) i :=
    Recursive2.comp2 Recursive2.ltInd Recursive2.cmpFIdx (show Recursive2 fun a _ => a from RecursiveV.proj 0)
  have c3 : Recursive2 fun i W =>
      Rcat.eqInd (Rcat.codeOf (Rcat.cmpFnd i W)) (Rcat.cmpM i W) :=
    Recursive2.comp2 Recursive2.eqInd
      (RecursiveV.comp1 (F := Rcat.codeOf) Recursive1.codeOf Recursive2.cmpFnd)
      Recursive2.cmpM
  have c4 : Recursive2 fun i W =>
      Rcat.eqInd (Rcat.cmpFIns i W) (Rcat.tailN (Rcat.insAt i W)) :=
    Recursive2.comp2 Recursive2.eqInd Recursive2.cmpFIns hTl
  have c5 : Recursive2 fun i W =>
      Rcat.eqInd (Rcat.outOf (Rcat.cmpFnd i W)) (Rcat.outAt i W) :=
    Recursive2.comp2 Recursive2.eqInd
      (RecursiveV.comp1 (F := Rcat.outOf) Recursive1.outOf Recursive2.cmpFnd)
      Recursive2.outAt
  have base : Recursive2 fun i W => Rcat.eqInd (Rcat.headN (Rcat.insAt i W)) 0 *
      (Rcat.ltInd (Rcat.cmpFIdx i W) i
        * Rcat.eqInd (Rcat.codeOf (Rcat.cmpFnd i W)) (Rcat.cmpM i W)
        * Rcat.eqInd (Rcat.cmpFIns i W) (Rcat.tailN (Rcat.insAt i W))
        * Rcat.eqInd (Rcat.outOf (Rcat.cmpFnd i W)) (Rcat.outAt i W)) :=
    Recursive2.comp2 Recursive2.mul c1 (Recursive2.comp2 Recursive2.mul
      (Recursive2.comp2 Recursive2.mul (Recursive2.comp2 Recursive2.mul c2 c3) c4) c5)
  have d1 : Recursive2 fun i W => Rcat.neInd (Rcat.headN (Rcat.insAt i W)) 0 :=
    Recursive2.comp2 Recursive2.neInd hHd (Recursive2.const 0)
  have d3 : Recursive2 fun i W => Rcat.ltInd (Rcat.cmpGIdx i W) i :=
    Recursive2.comp2 Recursive2.ltInd Recursive2.cmpGIdx (show Recursive2 fun a _ => a from RecursiveV.proj 0)
  have d4 : Recursive2 fun i W =>
      Rcat.eqInd (Rcat.codeOf (Rcat.cmpFnd i W)) (Rcat.codeOf (Rcat.nthN i W)) :=
    Recursive2.comp2 Recursive2.eqInd
      (RecursiveV.comp1 (F := Rcat.codeOf) Recursive1.codeOf Recursive2.cmpFnd)
      (RecursiveV.comp1 (F := Rcat.codeOf) Recursive1.codeOf Recursive2.nthN)
  have d5 : Recursive2 fun i W => Rcat.eqInd (Rcat.cmpFIns i W)
      (Rcat.consN (Rcat.headN (Rcat.insAt i W) - 1) (Rcat.tailN (Rcat.insAt i W))) :=
    Recursive2.comp2 Recursive2.eqInd Recursive2.cmpFIns
      (Recursive2.comp2 Recursive2.consN hn1 hTl)
  have d6 : Recursive2 fun i W => Rcat.eqInd
      (Rcat.codeOf (Rcat.ltInd (Rcat.cmpGIdx i W) i * Rcat.nthN (Rcat.cmpGIdx i W) W))
      (Rcat.csnd (Rcat.plAt i W)) :=
    Recursive2.comp2 Recursive2.eqInd
      (RecursiveV.comp1 (F := Rcat.codeOf) Recursive1.codeOf hndB)
      (RecursiveV.comp1 (F := Rcat.csnd) Recursive1.csnd Recursive2.plAt)
  have d7 : Recursive2 fun i W => Rcat.eqInd
      (Rcat.insOf (Rcat.ltInd (Rcat.cmpGIdx i W) i * Rcat.nthN (Rcat.cmpGIdx i W) W))
      (Rcat.consN (Rcat.headN (Rcat.insAt i W) - 1)
        (Rcat.consN (Rcat.outOf (Rcat.cmpFnd i W)) (Rcat.tailN (Rcat.insAt i W)))) :=
    Recursive2.comp2 Recursive2.eqInd
      (RecursiveV.comp1 (F := Rcat.insOf) Recursive1.insOf hndB)
      (Recursive2.comp2 Recursive2.consN hn1 (Recursive2.comp2 Recursive2.consN
        (RecursiveV.comp1 (F := Rcat.outOf) Recursive1.outOf Recursive2.cmpFnd) hTl))
  have d8 : Recursive2 fun i W => Rcat.eqInd
      (Rcat.outOf (Rcat.ltInd (Rcat.cmpGIdx i W) i * Rcat.nthN (Rcat.cmpGIdx i W) W))
      (Rcat.outAt i W) :=
    Recursive2.comp2 Recursive2.eqInd
      (RecursiveV.comp1 (F := Rcat.outOf) Recursive1.outOf hndB) Recursive2.outAt
  have step : Recursive2 fun i W => Rcat.neInd (Rcat.headN (Rcat.insAt i W)) 0 *
      (Rcat.ltInd (Rcat.cmpFIdx i W) i
        * Rcat.ltInd (Rcat.cmpGIdx i W) i
        * Rcat.eqInd (Rcat.codeOf (Rcat.cmpFnd i W)) (Rcat.codeOf (Rcat.nthN i W))
        * Rcat.eqInd (Rcat.cmpFIns i W)
            (Rcat.consN (Rcat.headN (Rcat.insAt i W) - 1) (Rcat.tailN (Rcat.insAt i W)))
        * Rcat.eqInd
            (Rcat.codeOf (Rcat.ltInd (Rcat.cmpGIdx i W) i * Rcat.nthN (Rcat.cmpGIdx i W) W))
            (Rcat.csnd (Rcat.plAt i W))
        * Rcat.eqInd
            (Rcat.insOf (Rcat.ltInd (Rcat.cmpGIdx i W) i * Rcat.nthN (Rcat.cmpGIdx i W) W))
            (Rcat.consN (Rcat.headN (Rcat.insAt i W) - 1)
              (Rcat.consN (Rcat.outOf (Rcat.cmpFnd i W)) (Rcat.tailN (Rcat.insAt i W))))
        * Rcat.eqInd
            (Rcat.outOf (Rcat.ltInd (Rcat.cmpGIdx i W) i * Rcat.nthN (Rcat.cmpGIdx i W) W))
            (Rcat.outAt i W)) :=
    Recursive2.comp2 Recursive2.mul d1
      (Recursive2.comp2 Recursive2.mul (Recursive2.comp2 Recursive2.mul
        (Recursive2.comp2 Recursive2.mul (Recursive2.comp2 Recursive2.mul
          (Recursive2.comp2 Recursive2.mul (Recursive2.comp2 Recursive2.mul c2 d3) d4)
            d5) d6) d7) d8)
  have h2 := Recursive2.comp2 Recursive2.add base step
  exact h2

theorem Recursive3.muStepOK : Recursive3 muStepOK := by
  have hidx : Recursive3 fun t i W => Rcat.nthN t (Rcat.kidsAt i W) :=
    Recursive3.comp2 Recursive2.nthN (show Recursive3 fun a _ _ => a from RecursiveV.proj 0) (Recursive3.lift23 Recursive2.kidsAt)
  have hnd : Recursive3 fun t i W =>
      Rcat.ltInd (Rcat.nthN t (Rcat.kidsAt i W)) i
        * Rcat.nthN (Rcat.nthN t (Rcat.kidsAt i W)) W :=
    Recursive3.comp2 Recursive2.mul
      (Recursive3.comp2 Recursive2.ltInd hidx (show Recursive3 fun _ b _ => b from RecursiveV.proj 1))
      (Recursive3.comp2 Recursive2.nthN hidx (show Recursive3 fun _ _ c => c from RecursiveV.proj 2))
  have m1 : Recursive3 fun t i W => Rcat.ltInd (Rcat.nthN t (Rcat.kidsAt i W)) i :=
    Recursive3.comp2 Recursive2.ltInd hidx (show Recursive3 fun _ b _ => b from RecursiveV.proj 1)
  have m2 : Recursive3 fun t i W =>
      Rcat.eqInd (Rcat.codeOf (Rcat.ltInd (Rcat.nthN t (Rcat.kidsAt i W)) i
        * Rcat.nthN (Rcat.nthN t (Rcat.kidsAt i W)) W)) (Rcat.plAt i W) :=
    Recursive3.comp2 Recursive2.eqInd
      (Recursive3.comp1 (F := Rcat.codeOf) Recursive1.codeOf hnd)
      (Recursive3.lift23 Recursive2.plAt)
  have m3 : Recursive3 fun t i W =>
      Rcat.eqInd (Rcat.insOf (Rcat.ltInd (Rcat.nthN t (Rcat.kidsAt i W)) i
        * Rcat.nthN (Rcat.nthN t (Rcat.kidsAt i W)) W))
        (Rcat.consN t (Rcat.insAt i W)) :=
    Recursive3.comp2 Recursive2.eqInd
      (Recursive3.comp1 (F := Rcat.insOf) Recursive1.insOf hnd)
      (Recursive3.comp2 Recursive2.consN (show Recursive3 fun a _ _ => a from RecursiveV.proj 0) (Recursive3.lift23 Recursive2.insAt))
  have m4 : Recursive3 fun t i W =>
      Rcat.neInd (Rcat.outOf (Rcat.ltInd (Rcat.nthN t (Rcat.kidsAt i W)) i
        * Rcat.nthN (Rcat.nthN t (Rcat.kidsAt i W)) W)) 0 :=
    Recursive3.comp2 Recursive2.neInd
      (Recursive3.comp1 (F := Rcat.outOf) Recursive1.outOf hnd) (Recursive3.const 0)
  have h2 : Recursive3 fun t i W =>
      Rcat.ltInd (Rcat.nthN t (Rcat.kidsAt i W)) i
      * Rcat.eqInd (Rcat.codeOf (Rcat.ltInd (Rcat.nthN t (Rcat.kidsAt i W)) i
          * Rcat.nthN (Rcat.nthN t (Rcat.kidsAt i W)) W)) (Rcat.plAt i W)
      * Rcat.eqInd (Rcat.insOf (Rcat.ltInd (Rcat.nthN t (Rcat.kidsAt i W)) i
          * Rcat.nthN (Rcat.nthN t (Rcat.kidsAt i W)) W))
          (Rcat.consN t (Rcat.insAt i W))
      * Rcat.neInd (Rcat.outOf (Rcat.ltInd (Rcat.nthN t (Rcat.kidsAt i W)) i
          * Rcat.nthN (Rcat.nthN t (Rcat.kidsAt i W)) W)) 0 :=
    Recursive3.comp2 Recursive2.mul (Recursive3.comp2 Recursive2.mul
      (Recursive3.comp2 Recursive2.mul m1 m2) m3) m4
  exact h2

theorem Recursive2.muOK : Recursive2 muOK := by
  have hball : RecursiveV fun v : Vec 2 =>
      bAllN (fun t => Rcat.muStepOK t (v 0) (v 1)) (Rcat.outAt (v 0) (v 1)) :=
    RecursiveV.bAllComp Recursive3.muStepOK Recursive2.outAt
  have hball' : Recursive2 fun i W =>
      bAllN (fun t => Rcat.muStepOK t i W) (Rcat.outAt i W) := hball
  have hyidx : Recursive2 fun i W => Rcat.nthN (Rcat.outAt i W) (Rcat.kidsAt i W) :=
    Recursive2.comp2 Recursive2.nthN Recursive2.outAt Recursive2.kidsAt
  have hynd : Recursive2 fun i W =>
      Rcat.ltInd (Rcat.nthN (Rcat.outAt i W) (Rcat.kidsAt i W)) i
        * Rcat.nthN (Rcat.nthN (Rcat.outAt i W) (Rcat.kidsAt i W)) W :=
    Recursive2.comp2 Recursive2.mul
      (Recursive2.comp2 Recursive2.ltInd hyidx (show Recursive2 fun a _ => a from RecursiveV.proj 0))
      (Recursive2.comp2 Recursive2.nthN hyidx (show Recursive2 fun _ b => b from RecursiveV.proj 1))
  have e1 : Recursive2 fun i W =>
      Rcat.ltInd (Rcat.nthN (Rcat.outAt i W) (Rcat.kidsAt i W)) i :=
    Recursive2.comp2 Recursive2.ltInd hyidx (show Recursive2 fun a _ => a from RecursiveV.proj 0)
  have e2 : Recursive2 fun i W =>
      Rcat.eqInd (Rcat.codeOf (Rcat.ltInd (Rcat.nthN (Rcat.outAt i W) (Rcat.kidsAt i W)) i
        * Rcat.nthN (Rcat.nthN (Rcat.outAt i W) (Rcat.kidsAt i W)) W)) (Rcat.plAt i W) :=
    Recursive2.comp2 Recursive2.eqInd
      (RecursiveV.comp1 (F := Rcat.codeOf) Recursive1.codeOf hynd) Recursive2.plAt
  have e3 : Recursive2 fun i W =>
      Rcat.eqInd (Rcat.insOf (Rcat.ltInd (Rcat.nthN (Rcat.outAt i W) (Rcat.kidsAt i W)) i
        * Rcat.nthN (Rcat.nthN (Rcat.outAt i W) (Rcat.kidsAt i W)) W))
        (Rcat.consN (Rcat.outAt i W) (Rcat.insAt i W)) :=
    Recursive2.comp2 Recursive2.eqInd
      (RecursiveV.comp1 (F := Rcat.insOf) Recursive1.insOf hynd)
      (Recursive2.comp2 Recursive2.consN Recursive2.outAt Recursive2.insAt)
  have e4 : Recursive2 fun i W =>
      Rcat.eqInd (Rcat.outOf (Rcat.ltInd (Rcat.nthN (Rcat.outAt i W) (Rcat.kidsAt i W)) i
        * Rcat.nthN (Rcat.nthN (Rcat.outAt i W) (Rcat.kidsAt i W)) W)) 0 :=
    Recursive2.comp2 Recursive2.eqInd
      (RecursiveV.comp1 (F := Rcat.outOf) Recursive1.outOf hynd) (Recursive2.const 0)
  have h2 : Recursive2 fun i W =>
      bAllN (fun t => Rcat.muStepOK t i W) (Rcat.outAt i W)
      * (Rcat.ltInd (Rcat.nthN (Rcat.outAt i W) (Rcat.kidsAt i W)) i
        * Rcat.eqInd (Rcat.codeOf (Rcat.ltInd (Rcat.nthN (Rcat.outAt i W) (Rcat.kidsAt i W)) i
            * Rcat.nthN (Rcat.nthN (Rcat.outAt i W) (Rcat.kidsAt i W)) W)) (Rcat.plAt i W)
        * Rcat.eqInd (Rcat.insOf (Rcat.ltInd (Rcat.nthN (Rcat.outAt i W) (Rcat.kidsAt i W)) i
            * Rcat.nthN (Rcat.nthN (Rcat.outAt i W) (Rcat.kidsAt i W)) W))
            (Rcat.consN (Rcat.outAt i W) (Rcat.insAt i W))
        * Rcat.eqInd (Rcat.outOf (Rcat.ltInd (Rcat.nthN (Rcat.outAt i W) (Rcat.kidsAt i W)) i
            * Rcat.nthN (Rcat.nthN (Rcat.outAt i W) (Rcat.kidsAt i W)) W)) 0) :=
    Recursive2.comp2 Recursive2.mul hball' (Recursive2.comp2 Recursive2.mul
      (Recursive2.comp2 Recursive2.mul (Recursive2.comp2 Recursive2.mul e1 e2) e3) e4)
  exact h2

theorem Recursive2.nodeOK : Recursive2 nodeOK := by
  have hHd : Recursive2 fun i W => Rcat.headN (Rcat.insAt i W) :=
    RecursiveV.comp1 (F := Rcat.headN) Recursive1.headN Recursive2.insAt
  have t0 : Recursive2 fun i W =>
      Rcat.eqInd (Rcat.tagAt i W) 0 * Rcat.eqInd (Rcat.outAt i W) 0 :=
    Recursive2.comp2 Recursive2.mul
      (Recursive2.comp2 Recursive2.eqInd Recursive2.tagAt (Recursive2.const 0))
      (Recursive2.comp2 Recursive2.eqInd Recursive2.outAt (Recursive2.const 0))
  have t1 : Recursive2 fun i W =>
      Rcat.eqInd (Rcat.tagAt i W) 1
        * Rcat.eqInd (Rcat.outAt i W) (Rcat.headN (Rcat.insAt i W) + 1) :=
    Recursive2.comp2 Recursive2.mul
      (Recursive2.comp2 Recursive2.eqInd Recursive2.tagAt (Recursive2.const 1))
      (Recursive2.comp2 Recursive2.eqInd Recursive2.outAt
        (Recursive2.comp2 Recursive2.add hHd (Recursive2.const 1)))
  have t2 : Recursive2 fun i W =>
      Rcat.eqInd (Rcat.tagAt i W) 2
        * Rcat.eqInd (Rcat.outAt i W) (Rcat.nthN (Rcat.plAt i W) (Rcat.insAt i W)) :=
    Recursive2.comp2 Recursive2.mul
      (Recursive2.comp2 Recursive2.eqInd Recursive2.tagAt (Recursive2.const 2))
      (Recursive2.comp2 Recursive2.eqInd Recursive2.outAt
        (Recursive2.comp2 Recursive2.nthN Recursive2.plAt Recursive2.insAt))
  have t3 : Recursive2 fun i W => Rcat.eqInd (Rcat.tagAt i W) 3 * Rcat.compOK i W :=
    Recursive2.comp2 Recursive2.mul
      (Recursive2.comp2 Recursive2.eqInd Recursive2.tagAt (Recursive2.const 3))
      Recursive2.compOK
  have t4 : Recursive2 fun i W => Rcat.eqInd (Rcat.tagAt i W) 4 * Rcat.precOK i W :=
    Recursive2.comp2 Recursive2.mul
      (Recursive2.comp2 Recursive2.eqInd Recursive2.tagAt (Recursive2.const 4))
      Recursive2.precOK
  have t5 : Recursive2 fun i W => Rcat.eqInd (Rcat.tagAt i W) 5 * Rcat.muOK i W :=
    Recursive2.comp2 Recursive2.mul
      (Recursive2.comp2 Recursive2.eqInd Recursive2.tagAt (Recursive2.const 5))
      Recursive2.muOK
  have h2 : Recursive2 fun i W =>
      Rcat.eqInd (Rcat.tagAt i W) 0 * Rcat.eqInd (Rcat.outAt i W) 0
      + Rcat.eqInd (Rcat.tagAt i W) 1
          * Rcat.eqInd (Rcat.outAt i W) (Rcat.headN (Rcat.insAt i W) + 1)
      + Rcat.eqInd (Rcat.tagAt i W) 2
          * Rcat.eqInd (Rcat.outAt i W) (Rcat.nthN (Rcat.plAt i W) (Rcat.insAt i W))
      + Rcat.eqInd (Rcat.tagAt i W) 3 * Rcat.compOK i W
      + Rcat.eqInd (Rcat.tagAt i W) 4 * Rcat.precOK i W
      + Rcat.eqInd (Rcat.tagAt i W) 5 * Rcat.muOK i W :=
    Recursive2.comp2 Recursive2.add (Recursive2.comp2 Recursive2.add
      (Recursive2.comp2 Recursive2.add (Recursive2.comp2 Recursive2.add
        (Recursive2.comp2 Recursive2.add t0 t1) t2) t3) t4) t5
  exact h2

/-- The universal accept predicate is a recursive function of R. -/
theorem Recursive2_acceptOn : Recursive2 acceptOn := by
  unfold acceptOn
  have hF : Recursive3 fun j _ wit => nodeOK j (cfst wit) :=
    Recursive3.comp2 Recursive2.nodeOK (show Recursive3 fun a _ _ => a from RecursiveV.proj 0)
      (Recursive3.comp1 (F := cfst) Recursive1.cfst (show Recursive3 fun _ _ c => c from RecursiveV.proj 2))
  have hb : Recursive2 fun _ wit => csnd wit + 1 :=
    Recursive2.comp2 Recursive2.add (Recursive2.ofSnd Recursive1.csnd) (Recursive2.const 1)
  have hball' : Recursive2 fun _ wit =>
      bAllN (fun j => nodeOK j (cfst wit)) (csnd wit + 1) :=
    RecursiveV.bAllComp hF hb
  have hroot : Recursive2 fun _ wit => nthN (csnd wit) (cfst wit) :=
    Recursive2.comp2 Recursive2.nthN (Recursive2.ofSnd Recursive1.csnd)
      (Recursive2.ofSnd Recursive1.cfst)
  have a2 : Recursive2 fun er wit =>
      eqInd (codeOf (nthN (csnd wit) (cfst wit))) (cfst er) :=
    Recursive2.comp2 Recursive2.eqInd
      (RecursiveV.comp1 (F := codeOf) Recursive1.codeOf hroot)
      (Recursive2.ofFst Recursive1.cfst)
  have a3 : Recursive2 fun er wit =>
      eqInd (insOf (nthN (csnd wit) (cfst wit))) (consN (csnd er) 0) :=
    Recursive2.comp2 Recursive2.eqInd
      (RecursiveV.comp1 (F := insOf) Recursive1.insOf hroot)
      (Recursive2.comp2 Recursive2.consN (Recursive2.ofFst Recursive1.csnd) (Recursive2.const 0))
  exact Recursive2.comp2 Recursive2.mul (Recursive2.comp2 Recursive2.mul hball' a2) a3

theorem Recursive1_uOutW : Recursive1 uOutW :=
  Recursive1.comp (f := fun wit => nthN (csnd wit) (cfst wit))
    (Recursive1.comp2 Recursive2.nthN Recursive1.csnd Recursive1.cfst) Recursive1.outOf

/-- `uOut` is a recursive function of R. -/
theorem Recursive2_uOut : Recursive2 uOut := by
  have h1 : Recursive1 fun wit => nthN (csnd wit) (cfst wit) :=
    Recursive1.comp2 Recursive2.nthN Recursive1.csnd Recursive1.cfst
  exact Recursive2.ofSnd (Recursive1.comp h1 Recursive1.outOf)

/-- STAGE 3a HEADLINE: the diagonal accept predicate is recursive by specialization
    of the universal checker — the machine that semi-decides the halting set is
    itself a machine of R. -/
theorem Recursive2.acceptN : Recursive2 acceptN := by
  have hUniversal : Recursive2 fun e wit => Rcat.acceptOn (Rcat.cp e e) wit :=
    Recursive2.comp2 Rcat.Recursive2_acceptOn
      (Recursive2.comp2 Recursive2.cp
        (show Recursive2 fun e _ => e from RecursiveV.proj 0)
        (show Recursive2 fun e _ => e from RecursiveV.proj 0))
      (show Recursive2 fun _ wit => wit from RecursiveV.proj 1)
  simpa only [Rcat.acceptN] using hUniversal

/-! ## Stage 3b: the enumerated equivalence relation E on ω

  The set `E := Δ ∪ {(2e, 2e+1), (2e+1, 2e) | e ∈ Kc}` glues the two points
  `2e, 2e+1` exactly when `e` halts on itself.  `E` is only recursively
  ENUMERABLE, never recursive — so it enters R not as a recursive set of pairs
  but as the IMAGE of the total recursive enumeration `n ↦ (l0 n, r0 n)`:
  index `4m` yields the diagonal pair `(m, m)`; indices `4w+1` / `4w+2` yield
  `(2e, 2e+1)` / `(2e+1, 2e)` when `w = cp e wit` is an accepted halting witness
  for `e`, and the (already covered) pair `(0,0)` otherwise. -/

/-- 0/1 test: is `w = cp e wit` an accepted halting witness for `e`? -/
noncomputable def accOne (w : Nat) : Nat := eqInd (acceptN (cfst w) (csnd w)) 1

theorem accOne_cases (w : Nat) : accOne w = 1 ∨ accOne w = 0 := by
  by_cases h : acceptN (cfst w) (csnd w) = 1
  · exact Or.inl (eqInd_eq h)
  · exact Or.inr (eqInd_ne h)

/-- Left column of the enumeration of E. -/
noncomputable def l0 (n : Nat) : Nat :=
  eqInd (n % 4) 0 * (n / 4)
  + eqInd (n % 4) 1 * (accOne (n / 4) * (2 * cfst (n / 4)))
  + eqInd (n % 4) 2 * (accOne (n / 4) * (2 * cfst (n / 4) + 1))

/-- Right column of the enumeration of E. -/
noncomputable def r0 (n : Nat) : Nat :=
  eqInd (n % 4) 0 * (n / 4)
  + eqInd (n % 4) 1 * (accOne (n / 4) * (2 * cfst (n / 4) + 1))
  + eqInd (n % 4) 2 * (accOne (n / 4) * (2 * cfst (n / 4)))

theorem l0_val0 {n : Nat} (h : n % 4 = 0) : l0 n = n / 4 := by
  unfold l0
  rw [h, eqInd_eq rfl, eqInd_ne (by omega : (0:Nat) ≠ 1), eqInd_ne (by omega : (0:Nat) ≠ 2)]
  omega

theorem r0_val0 {n : Nat} (h : n % 4 = 0) : r0 n = n / 4 := by
  unfold r0
  rw [h, eqInd_eq rfl, eqInd_ne (by omega : (0:Nat) ≠ 1), eqInd_ne (by omega : (0:Nat) ≠ 2)]
  omega

theorem l0_val1 {n : Nat} (h : n % 4 = 1) : l0 n = accOne (n / 4) * (2 * cfst (n / 4)) := by
  unfold l0
  rw [h, eqInd_eq rfl, eqInd_ne (by omega : (1:Nat) ≠ 0), eqInd_ne (by omega : (1:Nat) ≠ 2)]
  omega

theorem r0_val1 {n : Nat} (h : n % 4 = 1) :
    r0 n = accOne (n / 4) * (2 * cfst (n / 4) + 1) := by
  unfold r0
  rw [h, eqInd_eq rfl, eqInd_ne (by omega : (1:Nat) ≠ 0), eqInd_ne (by omega : (1:Nat) ≠ 2)]
  omega

theorem l0_val2 {n : Nat} (h : n % 4 = 2) :
    l0 n = accOne (n / 4) * (2 * cfst (n / 4) + 1) := by
  unfold l0
  rw [h, eqInd_eq rfl, eqInd_ne (by omega : (2:Nat) ≠ 0), eqInd_ne (by omega : (2:Nat) ≠ 1)]
  omega

theorem r0_val2 {n : Nat} (h : n % 4 = 2) : r0 n = accOne (n / 4) * (2 * cfst (n / 4)) := by
  unfold r0
  rw [h, eqInd_eq rfl, eqInd_ne (by omega : (2:Nat) ≠ 0), eqInd_ne (by omega : (2:Nat) ≠ 1)]
  omega

theorem l0_val3 {n : Nat} (h : n % 4 = 3) : l0 n = 0 := by
  unfold l0
  rw [h, eqInd_ne (by omega : (3:Nat) ≠ 0), eqInd_ne (by omega : (3:Nat) ≠ 1),
    eqInd_ne (by omega : (3:Nat) ≠ 2)]
  omega

theorem r0_val3 {n : Nat} (h : n % 4 = 3) : r0 n = 0 := by
  unfold r0
  rw [h, eqInd_ne (by omega : (3:Nat) ≠ 0), eqInd_ne (by omega : (3:Nat) ≠ 1),
    eqInd_ne (by omega : (3:Nat) ≠ 2)]
  omega

/-- The set enumerated by `(l0, r0)`. -/
def ESet (a b : Nat) : Prop := ∃ n, l0 n = a ∧ r0 n = b

/-- E is: the diagonal, plus the glued pair `{2e, 2e+1}` for each halting `e`. -/
theorem ESet_iff {a b : Nat} :
    ESet a b ↔ a = b ∨ (a / 2 = b / 2 ∧ a ≠ b ∧ Kc (a / 2)) := by
  constructor
  · rintro ⟨n, ha, hb⟩
    have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases h4 with h | h | h | h
    · left; rw [← ha, ← hb, l0_val0 h, r0_val0 h]
    · rw [l0_val1 h] at ha
      rw [r0_val1 h] at hb
      rcases accOne_cases (n / 4) with hacc | hacc
      · rw [hacc, Nat.one_mul] at ha hb
        right
        have hK : Kc (cfst (n / 4)) := ⟨csnd (n / 4), eqInd_one_iff.mp hacc⟩
        have he : a / 2 = cfst (n / 4) := by omega
        exact ⟨by omega, by omega, he ▸ hK⟩
      · rw [hacc, Nat.zero_mul] at ha hb
        left; omega
    · rw [l0_val2 h] at ha
      rw [r0_val2 h] at hb
      rcases accOne_cases (n / 4) with hacc | hacc
      · rw [hacc, Nat.one_mul] at ha hb
        right
        have hK : Kc (cfst (n / 4)) := ⟨csnd (n / 4), eqInd_one_iff.mp hacc⟩
        have he : a / 2 = cfst (n / 4) := by omega
        exact ⟨by omega, by omega, he ▸ hK⟩
      · rw [hacc, Nat.zero_mul] at ha hb
        left; omega
    · left; rw [← ha, ← hb, l0_val3 h, r0_val3 h]
  · rintro (rfl | ⟨hdiv, hne, hK⟩)
    · refine ⟨4 * a, ?_, ?_⟩
      · rw [l0_val0 (by omega)]; omega
      · rw [r0_val0 (by omega)]; omega
    · obtain ⟨wit, hwit⟩ := hK
      have haccw : accOne (cp (a / 2) wit) = 1 := by
        unfold accOne
        rw [cfst_cp, csnd_cp]
        exact eqInd_eq hwit
      have hcase : (a = 2 * (a / 2) ∧ b = 2 * (a / 2) + 1)
          ∨ (a = 2 * (a / 2) + 1 ∧ b = 2 * (a / 2)) := by omega
      rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · refine ⟨4 * cp (a / 2) wit + 1, ?_, ?_⟩
        · rw [l0_val1 (by omega), show (4 * cp (a / 2) wit + 1) / 4 = cp (a / 2) wit
            from by omega, haccw, cfst_cp, Nat.one_mul]
          omega
        · rw [r0_val1 (by omega), show (4 * cp (a / 2) wit + 1) / 4 = cp (a / 2) wit
            from by omega, haccw, cfst_cp, Nat.one_mul]
          omega
      · refine ⟨4 * cp (a / 2) wit + 2, ?_, ?_⟩
        · rw [l0_val2 (by omega), show (4 * cp (a / 2) wit + 2) / 4 = cp (a / 2) wit
            from by omega, haccw, cfst_cp, Nat.one_mul]
          omega
        · rw [r0_val2 (by omega), show (4 * cp (a / 2) wit + 2) / 4 = cp (a / 2) wit
            from by omega, haccw, cfst_cp, Nat.one_mul]
          omega

theorem ESet_refl (a : Nat) : ESet a a := ESet_iff.mpr (Or.inl rfl)

theorem ESet_symm {a b : Nat} (h : ESet a b) : ESet b a := by
  rcases ESet_iff.mp h with rfl | ⟨h1, h2, h3⟩
  · exact ESet_refl a
  · exact ESet_iff.mpr (Or.inr ⟨by omega, by omega, by rw [← h1]; exact h3⟩)

theorem ESet_trans {a b c : Nat} (hab : ESet a b) (hbc : ESet b c) : ESet a c := by
  rcases ESet_iff.mp hab with rfl | ⟨h1, h2, h3⟩
  · exact hbc
  · rcases ESet_iff.mp hbc with rfl | ⟨h1', h2', h3'⟩
    · exact hab
    · by_cases hac : a = c
      · exact hac ▸ ESet_refl a
      · exact ESet_iff.mpr (Or.inr ⟨by omega, hac, h3⟩)

/-! Recursiveness of the two columns. -/

theorem accOne_rec : Recursive1 accOne := by
  have h1 : Recursive1 fun w => Rcat.acceptN (Rcat.cfst w) (Rcat.csnd w) :=
    Recursive1.comp2 Recursive2.acceptN Recursive1.cfst Recursive1.csnd
  have h2 : Recursive1 fun w => Rcat.eqInd (Rcat.acceptN (Rcat.cfst w) (Rcat.csnd w)) 1 :=
    Recursive1.comp2 Recursive2.eqInd h1 (Recursive1.const 1)
  exact h2

theorem l0_rec : Recursive1 l0 := by
  have hmod : Recursive1 fun n => n % 4 := Recursive1.modConst 3
  have hdiv : Recursive1 fun n => n / 4 := Recursive1.divConst 3
  have hcf : Recursive1 fun n => Rcat.cfst (n / 4) := Recursive1.comp hdiv Recursive1.cfst
  have h2cf : Recursive1 fun n => 2 * Rcat.cfst (n / 4) :=
    Recursive1.mul (Recursive1.const 2) hcf
  have hacc4 : Recursive1 fun n => accOne (n / 4) := Recursive1.comp hdiv accOne_rec
  have t0 : Recursive1 fun n => Rcat.eqInd (n % 4) 0 * (n / 4) :=
    Recursive1.mul (Recursive1.comp2 Recursive2.eqInd hmod (Recursive1.const 0)) hdiv
  have t1 : Recursive1 fun n =>
      Rcat.eqInd (n % 4) 1 * (accOne (n / 4) * (2 * Rcat.cfst (n / 4))) :=
    Recursive1.mul (Recursive1.comp2 Recursive2.eqInd hmod (Recursive1.const 1))
      (Recursive1.mul hacc4 h2cf)
  have t2 : Recursive1 fun n =>
      Rcat.eqInd (n % 4) 2 * (accOne (n / 4) * (2 * Rcat.cfst (n / 4) + 1)) :=
    Recursive1.mul (Recursive1.comp2 Recursive2.eqInd hmod (Recursive1.const 2))
      (Recursive1.mul hacc4 (Recursive1.add h2cf (Recursive1.const 1)))
  have h2 : Recursive1 fun n =>
      Rcat.eqInd (n % 4) 0 * (n / 4)
      + Rcat.eqInd (n % 4) 1 * (accOne (n / 4) * (2 * Rcat.cfst (n / 4)))
      + Rcat.eqInd (n % 4) 2 * (accOne (n / 4) * (2 * Rcat.cfst (n / 4) + 1)) :=
    Recursive1.add (Recursive1.add t0 t1) t2
  exact h2

theorem r0_rec : Recursive1 r0 := by
  have hmod : Recursive1 fun n => n % 4 := Recursive1.modConst 3
  have hdiv : Recursive1 fun n => n / 4 := Recursive1.divConst 3
  have hcf : Recursive1 fun n => Rcat.cfst (n / 4) := Recursive1.comp hdiv Recursive1.cfst
  have h2cf : Recursive1 fun n => 2 * Rcat.cfst (n / 4) :=
    Recursive1.mul (Recursive1.const 2) hcf
  have hacc4 : Recursive1 fun n => accOne (n / 4) := Recursive1.comp hdiv accOne_rec
  have t0 : Recursive1 fun n => Rcat.eqInd (n % 4) 0 * (n / 4) :=
    Recursive1.mul (Recursive1.comp2 Recursive2.eqInd hmod (Recursive1.const 0)) hdiv
  have t1 : Recursive1 fun n =>
      Rcat.eqInd (n % 4) 1 * (accOne (n / 4) * (2 * Rcat.cfst (n / 4) + 1)) :=
    Recursive1.mul (Recursive1.comp2 Recursive2.eqInd hmod (Recursive1.const 1))
      (Recursive1.mul hacc4 (Recursive1.add h2cf (Recursive1.const 1)))
  have t2 : Recursive1 fun n =>
      Rcat.eqInd (n % 4) 2 * (accOne (n / 4) * (2 * Rcat.cfst (n / 4))) :=
    Recursive1.mul (Recursive1.comp2 Recursive2.eqInd hmod (Recursive1.const 2))
      (Recursive1.mul hacc4 h2cf)
  have h2 : Recursive1 fun n =>
      Rcat.eqInd (n % 4) 0 * (n / 4)
      + Rcat.eqInd (n % 4) 1 * (accOne (n / 4) * (2 * Rcat.cfst (n / 4) + 1))
      + Rcat.eqInd (n % 4) 2 * (accOne (n / 4) * (2 * Rcat.cfst (n / 4))) :=
    Recursive1.add (Recursive1.add t0 t1) t2
  exact h2

/-! The enumeration as morphisms of R, and E as a binary relation. -/

/-- The left column as a morphism ω ⟶ ω of R. -/
noncomputable def lMor : (omega : ExtNat) ⟶ omega := ⟨l0, l0_rec⟩

/-- The right column as a morphism ω ⟶ ω of R. -/
noncomputable def rMor : (omega : ExtNat) ⟶ omega := ⟨r0, r0_rec⟩

/-- The joint enumeration ω ⟶ ω×ω. -/
noncomputable def FE : (omega : ExtNat) ⟶ prod omega omega := pair lMor rMor

/-- E as a binary relation on ω in R: the IMAGE of the enumeration `FE`,
    with its two projections as columns.  (The image absorbs the repetitions of
    the sloppy enumeration; joint monicity is monicity of the image.) -/
noncomputable def ERel : BinRel ExtNat omega omega where
  src := (image FE).dom
  colA := (image FE).arr ≫ fst
  colB := (image FE).arr ≫ snd
  isMonicPair := by
    intro X f g hA hB
    have h_fst : (f ≫ (image FE).arr) ≫ fst = (g ≫ (image FE).arr) ≫ fst := by
      simpa [Cat.assoc] using hA
    have h_snd : (f ≫ (image FE).arr) ≫ snd = (g ≫ (image FE).arr) ≫ snd := by
      simpa [Cat.assoc] using hB
    have hfg : f ≫ (image FE).arr = g ≫ (image FE).arr := by
      rw [pair_uniq _ _ (f ≫ (image FE).arr) rfl rfl, pair_uniq _ _ (g ≫ (image FE).arr) rfl rfl,
        h_fst, h_snd]
    exact (image FE).monic f g hfg

/-! Pointwise membership: the elements of `ERel.src` present exactly the pairs of
    `ESet`.  Both directions go through the split cover `image.lift FE`. -/

/-- Covers of R are pointwise surjective (they split). -/
theorem cover_surj {α β : ExtNat} {f : α ⟶ β} (hc : Cover f) (b : El β) :
    ∃ a : El α, f.1 a = b := by
  obtain ⟨s, hs⟩ := cover_split f hc
  exact ⟨s.1 b, Mor.congr hs b⟩

theorem ERel_mem (p : El ERel.src) : ESet (ERel.colA.1 p) (ERel.colB.1 p) := by
  obtain ⟨n, hn⟩ := cover_surj (image_lift_cover FE) p
  have harr : (image FE).arr.1 p = FE.1 n := by
    rw [← hn]
    exact Mor.congr (image.lift_fac FE) n
  refine ⟨n, ?_, ?_⟩
  · have hcA : ERel.colA.1 p = (FE ≫ fst).1 n := by
      show ((image FE).arr ≫ fst).1 p = (FE ≫ fst).1 n
      rw [comp_fn, comp_fn, harr]
    rw [hcA]
    exact (Mor.congr (fst_pair lMor rMor) n).symm
  · have hcB : ERel.colB.1 p = (FE ≫ snd).1 n := by
      show ((image FE).arr ≫ snd).1 p = (FE ≫ snd).1 n
      rw [comp_fn, comp_fn, harr]
    rw [hcB]
    exact (Mor.congr (snd_pair lMor rMor) n).symm

theorem ERel_lift (n : Nat) :
    ERel.colA.1 ((image.lift FE).1 n) = l0 n ∧ ERel.colB.1 ((image.lift FE).1 n) = r0 n := by
  refine ⟨?_, ?_⟩
  · have hcA : ERel.colA.1 ((image.lift FE).1 n) = (FE ≫ fst).1 n := by
      show ((image FE).arr ≫ fst).1 ((image.lift FE).1 n) = (FE ≫ fst).1 n
      rw [comp_fn, comp_fn, ← comp_fn (image.lift FE) (image FE).arr n,
        Mor.congr (image.lift_fac FE) n]
    rw [hcA]
    exact Mor.congr (fst_pair lMor rMor) n
  · have hcB : ERel.colB.1 ((image.lift FE).1 n) = (FE ≫ snd).1 n := by
      show ((image FE).arr ≫ snd).1 ((image.lift FE).1 n) = (FE ≫ snd).1 n
      rw [comp_fn, comp_fn, ← comp_fn (image.lift FE) (image FE).arr n,
        Mor.congr (image.lift_fac FE) n]
    rw [hcB]
    exact Mor.congr (snd_pair lMor rMor) n

/-! ## μ-search morphisms

  A total recursive search (least zero of a recursive test, preprocessed by a
  morphism into ω) is again a morphism of R — this is where the book's
  "a left-inverse chooses representatives" gets its computational content. -/

theorem eqInd_le_one (a b : Nat) : eqInd a b ≤ 1 := by
  by_cases h : a = b
  · rw [eqInd_eq h]
    exact Nat.le_refl 1
  · rw [eqInd_ne h]
    omega

/-- Search test: does index `m` enumerate exactly the pair coded by `w`? -/
noncomputable def pairTest (m w : Nat) : Nat :=
  1 - eqInd (l0 m) (cfst w) * eqInd (r0 m) (csnd w)

theorem pairTest_rec : Recursive2 pairTest := by
  have h1 : Recursive2 fun m w => Rcat.eqInd (l0 m) (Rcat.cfst w) :=
    Recursive2.comp2 Recursive2.eqInd (Recursive2.ofFst l0_rec)
      (Recursive2.ofSnd Recursive1.cfst)
  have h2 : Recursive2 fun m w => Rcat.eqInd (r0 m) (Rcat.csnd w) :=
    Recursive2.comp2 Recursive2.eqInd (Recursive2.ofFst r0_rec)
      (Recursive2.ofSnd Recursive1.csnd)
  have h3 : Recursive2 fun m w =>
      1 - Rcat.eqInd (l0 m) (Rcat.cfst w) * Rcat.eqInd (r0 m) (Rcat.csnd w) :=
    Recursive2.comp2 Recursive2.sub (Recursive2.const 1)
      (Recursive2.comp2 Recursive2.mul h1 h2)
  exact h3

theorem pairTest_zero_iff {m a b : Nat} :
    pairTest m (cp a b) = 0 ↔ (l0 m = a ∧ r0 m = b) := by
  unfold pairTest
  rw [cfst_cp, csnd_cp]
  constructor
  · intro h
    by_cases hx : l0 m = a
    · by_cases hy : r0 m = b
      · exact ⟨hx, hy⟩
      · rw [eqInd_ne hy, Nat.mul_zero] at h; omega
    · rw [eqInd_ne hx, Nat.zero_mul] at h; omega
  · rintro ⟨hx, hy⟩
    rw [eqInd_eq hx, eqInd_eq hy]

/-- Pair two ω-valued morphisms through the Cantor pairing. -/
noncomputable def cpMor {α : ExtNat} (x y : α ⟶ (omega : ExtNat)) :
    α ⟶ (omega : ExtNat) :=
  ⟨fun a => cp (x.1 a) (y.1 a), by
    match α with
    | some n => exact trivial
    | none =>
      show Recursive1 fun k => Rcat.cp (x.1 k) (y.1 k)
      have hx : Recursive1 fun k => x.1 k := x.2
      have hy : Recursive1 fun k => y.1 k := y.2
      exact Recursive1.comp2 Recursive2.cp hx hy⟩

/-- Total μ-search along a morphism: the least-zero point of a recursive test,
    preprocessed by `g`, is a morphism `α ⟶ ω`. -/
theorem searchMor {α : ExtNat} (t : Nat → Nat → Nat) (ht : Recursive2 t)
    (g : α ⟶ (omega : ExtNat)) (htot : ∀ a : El α, ∃ m, t m (g.1 a) = 0) :
    ∃ h : α ⟶ (omega : ExtNat), ∀ a : El α,
      t (h.1 a) (g.1 a) = 0 ∧ ∀ i, i < toNat (h.1 a) → t i (g.1 a) ≠ 0 := by
  refine ⟨⟨fun a => theLeast (fun m => t m (g.1 a) = 0) (htot a), ?_⟩,
    fun a => ⟨theLeast_mem _ (htot a), fun i hi => theLeast_min _ (htot a) i hi⟩⟩
  match α, g, htot with
  | some n, g, htot => exact trivial
  | none, g, htot =>
    show Recursive1 fun k => theLeast (fun m => t m (g.1 k) = 0) (htot k)
    have hg : Recursive1 fun k => g.1 k := g.2
    have ht₂ : Recursive2 fun i k => t i (g.1 k) :=
      Recursive2.comp2 ht (show Recursive2 fun a _ => a from RecursiveV.proj 0) (Recursive2.ofSnd hg)
    exact Recursive1.mu ht₂
      (fun k => theLeast_mem (fun m => t m (g.1 k) = 0) (htot k))
      (fun k i hik => theLeast_min (fun m => t m (g.1 k) = 0) (htot k) i hik)

/-- KEY CONSTRUCTION: any pair of morphisms into ω that pointwise lands in `ESet`
    factors through E's table — search the enumeration index, then lift. -/
theorem searchIntoE {α : ExtNat} (x y : α ⟶ (omega : ExtNat))
    (htot : ∀ a : El α, ESet (x.1 a) (y.1 a)) :
    ∃ h : α ⟶ ERel.src, h ≫ ERel.colA = x ∧ h ≫ ERel.colB = y := by
  have htot' : ∀ a : El α, ∃ m, pairTest m ((cpMor x y).1 a) = 0 := by
    intro a
    obtain ⟨m, hm1, hm2⟩ := htot a
    exact ⟨m, pairTest_zero_iff.mpr ⟨hm1, hm2⟩⟩
  obtain ⟨hs, hspec⟩ := searchMor pairTest pairTest_rec (cpMor x y) htot'
  have hkey : ∀ a : El α, l0 (hs.1 a) = x.1 a ∧ r0 (hs.1 a) = y.1 a := by
    intro a
    have h0 := (hspec a).1
    exact pairTest_zero_iff.mp h0
  refine ⟨hs ≫ image.lift FE, Mor.ext fun a => ?_, Mor.ext fun a => ?_⟩
  · show ERel.colA.1 ((image.lift FE).1 (hs.1 a)) = x.1 a
    rw [(ERel_lift (hs.1 a)).1]
    exact (hkey a).1
  · show ERel.colB.1 ((image.lift FE).1 (hs.1 a)) = y.1 a
    rw [(ERel_lift (hs.1 a)).2]
    exact (hkey a).2

/-! ## E is an equivalence relation of R (§1.567 sense) -/

/-- Composite membership: the elements of `(E ⊚ E).src` present pairs of the
    transitive closure — which is `ESet` itself. -/
theorem EE_mem (q : El (ERel ⊚ ERel).src) :
    ESet ((ERel ⊚ ERel).colA.1 q) ((ERel ⊚ ERel).colB.1 q) := by
  -- unfold the composite: pullback of the B-leg over the A-leg, then image
  obtain ⟨u, hu⟩ := cover_surj (image_lift_cover
    (pair ((HasPullbacks.has ERel.colB ERel.colA).cone.π₁ ≫ ERel.colA)
          ((HasPullbacks.has ERel.colB ERel.colA).cone.π₂ ≫ ERel.colB))) q
  have harr : (image (pair ((HasPullbacks.has ERel.colB ERel.colA).cone.π₁ ≫ ERel.colA)
      ((HasPullbacks.has ERel.colB ERel.colA).cone.π₂ ≫ ERel.colB))).arr.1 q
      = (pair ((HasPullbacks.has ERel.colB ERel.colA).cone.π₁ ≫ ERel.colA)
        ((HasPullbacks.has ERel.colB ERel.colA).cone.π₂ ≫ ERel.colB)).1 u := by
    rw [← hu]
    exact Mor.congr (image.lift_fac _) u
  have hA : (ERel ⊚ ERel).colA.1 q
      = ERel.colA.1 ((HasPullbacks.has ERel.colB ERel.colA).cone.π₁.1 u) := by
    show ((image (pair ((HasPullbacks.has ERel.colB ERel.colA).cone.π₁ ≫ ERel.colA)
        ((HasPullbacks.has ERel.colB ERel.colA).cone.π₂ ≫ ERel.colB))).arr ≫ fst).1 q = _
    rw [comp_fn, harr,
      ← comp_fn _ fst u, fst_pair, comp_fn]
  have hB : (ERel ⊚ ERel).colB.1 q
      = ERel.colB.1 ((HasPullbacks.has ERel.colB ERel.colA).cone.π₂.1 u) := by
    show ((image (pair ((HasPullbacks.has ERel.colB ERel.colA).cone.π₁ ≫ ERel.colA)
        ((HasPullbacks.has ERel.colB ERel.colA).cone.π₂ ≫ ERel.colB))).arr ≫ snd).1 q = _
    rw [comp_fn, harr,
      ← comp_fn _ snd u, snd_pair, comp_fn]
  have hmid : ERel.colB.1 ((HasPullbacks.has ERel.colB ERel.colA).cone.π₁.1 u)
      = ERel.colA.1 ((HasPullbacks.has ERel.colB ERel.colA).cone.π₂.1 u) := by
    have := Mor.congr (HasPullbacks.has ERel.colB ERel.colA).cone.w u
    rwa [comp_fn, comp_fn] at this
  rw [hA, hB]
  exact ESet_trans
    (ESet_trans (ERel_mem _) (hmid ▸ ESet_refl _))
    (ERel_mem _)

/-- **E is an equivalence relation in R** — reflexive (a diagonal-index morphism),
    symmetric (μ-search for the swapped pair's index), transitive (μ-search for
    the composed pair's index; `ESet` is transitive as a set). -/
theorem ERel_equivalence : EquivalenceRelation ERel := by
  refine ⟨?_, ?_, ?_⟩
  · -- reflexive
    obtain ⟨h, hA, hB⟩ := searchIntoE (Cat.id (omega : ExtNat)) (Cat.id omega)
      (fun n => ESet_refl n)
    exact ⟨h, hA, hB⟩
  · -- symmetric
    obtain ⟨h, hA, hB⟩ := searchIntoE ERel.colB ERel.colA
      (fun p => ESet_symm (ERel_mem p))
    exact ⟨⟨h, hB, hA⟩⟩
  · -- transitive
    obtain ⟨h, hA, hB⟩ := searchIntoE (ERel ⊚ ERel).colA (ERel ⊚ ERel).colB EE_mem
    exact ⟨⟨h, hA, hB⟩⟩

/-! ## Stage 3c: E is NOT effective — R is not an effective regular category

  Suppose E were the level (kernel pair) of a cover `x : ω → Q`.  In R covers
  split (`cover_split`), so `x` has a section `s`; then `x ≫ s` is a RECURSIVE
  choice of representatives for E, and comparing the representatives of `2e` and
  `2e+1` DECIDES the halting set — contradiction with `K_not_recursive`.  This is
  the book's "a left-inverse α → ω chooses a set of representatives for E,
  forcing E to be not just recursively enumerable, but recursive". -/

/-- The canonical element of the terminator of R. -/
noncomputable def pt1 : El (one : ExtNat) := ⟨0, Nat.one_pos⟩

/-- The point of R at an element. -/
noncomputable def elPt {γ : ExtNat} (c : El γ) : (one : ExtNat) ⟶ γ :=
  ⟨fun _ => c, isMor_finite _⟩

/-- `x`-equal elements are presented by the level relation `x ⊚ x°`: the witness
    is a point of the pullback of `x` over itself, pushed into the image. -/
theorem levelSet_of_eq {Q : ExtNat} (x : (omega : ExtNat) ⟶ Q) {a b : Nat}
    (hab : x.1 a = x.1 b) :
    ∃ w : El (graph x ⊚ (graph x)°).src,
      (graph x ⊚ (graph x)°).colA.1 w = a ∧ (graph x ⊚ (graph x)°).colB.1 w = b := by
  have hw : elPt a ≫ (graph x).colB = elPt b ≫ ((graph x)°).colA :=
    Mor.ext fun _ => hab
  refine ⟨((HasPullbacks.has (graph x).colB ((graph x)°).colA).lift
    ⟨one, elPt a, elPt b, hw⟩ ≫ image.lift
      (pair ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₁ ≫ (graph x).colA)
        ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₂
          ≫ ((graph x)°).colB))).1 pt1, ?_, ?_⟩
  · have harr : (image (pair
        ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₁ ≫ (graph x).colA)
        ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₂
          ≫ ((graph x)°).colB))).arr.1
        ((image.lift (pair
          ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₁ ≫ (graph x).colA)
          ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₂
            ≫ ((graph x)°).colB))).1
          (((HasPullbacks.has (graph x).colB ((graph x)°).colA).lift
            ⟨one, elPt a, elPt b, hw⟩).1 pt1))
        = (pair
          ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₁ ≫ (graph x).colA)
          ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₂
            ≫ ((graph x)°).colB)).1
          (((HasPullbacks.has (graph x).colB ((graph x)°).colA).lift
            ⟨one, elPt a, elPt b, hw⟩).1 pt1) :=
      Mor.congr (image.lift_fac _) _
    show ((image (pair
        ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₁ ≫ (graph x).colA)
        ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₂
          ≫ ((graph x)°).colB))).arr ≫ fst).1
        ((image.lift (pair
          ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₁ ≫ (graph x).colA)
          ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₂
            ≫ ((graph x)°).colB))).1
          (((HasPullbacks.has (graph x).colB ((graph x)°).colA).lift
            ⟨one, elPt a, elPt b, hw⟩).1 pt1)) = a
    rw [comp_fn, harr, ← comp_fn _ fst, fst_pair, comp_fn]
    exact Mor.congr ((HasPullbacks.has (graph x).colB ((graph x)°).colA).lift_fst
      ⟨one, elPt a, elPt b, hw⟩) pt1
  · have harr : (image (pair
        ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₁ ≫ (graph x).colA)
        ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₂
          ≫ ((graph x)°).colB))).arr.1
        ((image.lift (pair
          ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₁ ≫ (graph x).colA)
          ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₂
            ≫ ((graph x)°).colB))).1
          (((HasPullbacks.has (graph x).colB ((graph x)°).colA).lift
            ⟨one, elPt a, elPt b, hw⟩).1 pt1))
        = (pair
          ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₁ ≫ (graph x).colA)
          ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₂
            ≫ ((graph x)°).colB)).1
          (((HasPullbacks.has (graph x).colB ((graph x)°).colA).lift
            ⟨one, elPt a, elPt b, hw⟩).1 pt1) :=
      Mor.congr (image.lift_fac _) _
    show ((image (pair
        ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₁ ≫ (graph x).colA)
        ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₂
          ≫ ((graph x)°).colB))).arr ≫ snd).1
        ((image.lift (pair
          ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₁ ≫ (graph x).colA)
          ((HasPullbacks.has (graph x).colB ((graph x)°).colA).cone.π₂
            ≫ ((graph x)°).colB))).1
          (((HasPullbacks.has (graph x).colB ((graph x)°).colA).lift
            ⟨one, elPt a, elPt b, hw⟩).1 pt1)) = b
    rw [comp_fn, harr, ← comp_fn _ snd, snd_pair, comp_fn]
    exact Mor.congr ((HasPullbacks.has (graph x).colB ((graph x)°).colA).lift_snd
      ⟨one, elPt a, elPt b, hw⟩) pt1

/-- **E is not effective**: it is not the level of any cover of R. -/
theorem ERel_not_effective : ¬ IsEffective ERel := by
  rintro ⟨_, Q, x, hcov, hEle, hlevE⟩
  obtain ⟨⟨h₁, h₁A, h₁B⟩⟩ := hEle
  obtain ⟨⟨h₂, h₂A, h₂B⟩⟩ := hlevE
  -- (1) E-related points are identified by x (E is below the level of x)
  have hxeq : ERel.colA ≫ x = ERel.colB ≫ x := by
    have hll := level_legs_comp x
    calc ERel.colA ≫ x = (h₁ ≫ (graph x ⊚ (graph x)°).colA) ≫ x := by rw [h₁A]
      _ = h₁ ≫ ((graph x ⊚ (graph x)°).colA ≫ x) := Cat.assoc _ _ _
      _ = h₁ ≫ ((graph x ⊚ (graph x)°).colB ≫ x) := by rw [hll]
      _ = (h₁ ≫ (graph x ⊚ (graph x)°).colB) ≫ x := (Cat.assoc _ _ _).symm
      _ = ERel.colB ≫ x := by rw [h₁B]
  have hxESet : ∀ a b : Nat, ESet a b → x.1 a = x.1 b := by
    intro a b hab
    obtain ⟨n, hna, hnb⟩ := hab
    have hthis := Mor.congr hxeq ((image.lift FE).1 n)
    rw [comp_fn, comp_fn, (ERel_lift n).1, (ERel_lift n).2, hna, hnb] at hthis
    exact hthis
  -- (2) x-identified points are E-related (the level of x is below E)
  have hExSet : ∀ a b : Nat, x.1 a = x.1 b → ESet a b := by
    intro a b hab
    obtain ⟨w, hwa, hwb⟩ := levelSet_of_eq x hab
    have hm := ERel_mem (h₂.1 w)
    have e1 : ERel.colA.1 (h₂.1 w) = a := by
      have hc := Mor.congr h₂A w
      rw [comp_fn] at hc
      rw [hc, hwa]
    have e2 : ERel.colB.1 (h₂.1 w) = b := by
      have hc := Mor.congr h₂B w
      rw [comp_fn] at hc
      rw [hc, hwb]
    rw [e1, e2] at hm
    exact hm
  -- (3) covers split, so the representative chooser x ≫ s is recursive and
  -- decides the halting set
  obtain ⟨s, hs⟩ := cover_split x hcov
  have hrepx : ∀ a b : Nat, morN (x ≫ s) a = morN (x ≫ s) b ↔ x.1 a = x.1 b := by
    intro a b
    constructor
    · intro h
      have ha := morN_spec (x ≫ s) (a : El (omega : ExtNat))
      have hb := morN_spec (x ≫ s) (b : El (omega : ExtNat))
      have hsx : s.1 (x.1 a) = s.1 (x.1 b) := by
        have : toNat ((x ≫ s).1 a) = toNat ((x ≫ s).1 b) := by
          rw [← ha, ← hb]; exact h
        exact toNat_inj this
      calc x.1 a = (s ≫ x).1 (x.1 a) := (Mor.congr hs (x.1 a)).symm
        _ = x.1 (s.1 (x.1 a)) := rfl
        _ = x.1 (s.1 (x.1 b)) := by rw [hsx]
        _ = (s ≫ x).1 (x.1 b) := rfl
        _ = x.1 b := Mor.congr hs (x.1 b)
    · intro h
      have ha' : morN (x ≫ s) a = toNat ((x ≫ s).1 a) :=
        morN_spec (x ≫ s) (a : El (omega : ExtNat))
      have hb' : morN (x ≫ s) b = toNat ((x ≫ s).1 b) :=
        morN_spec (x ≫ s) (b : El (omega : ExtNat))
      rw [ha', hb']
      show toNat (s.1 (x.1 a)) = toNat (s.1 (x.1 b))
      rw [h]
  -- the decision procedure for Kc
  apply K_not_recursive
  refine ⟨fun e => eqInd (morN (x ≫ s) (2 * e)) (morN (x ≫ s) (2 * e + 1)), ?_, ?_⟩
  · -- it is recursive
    have hdb : Recursive1 fun e => 2 * e :=
      Recursive1.mul (Recursive1.const 2) (show Recursive1 fun n => n from RecursiveV.proj 0)
    have h1 : Recursive1 fun e => morN (x ≫ s) (2 * e) :=
      Recursive1.comp hdb (morN_rec (x ≫ s))
    have h2 : Recursive1 fun e => morN (x ≫ s) (2 * e + 1) :=
      Recursive1.comp (Recursive1.add hdb (Recursive1.const 1)) (morN_rec (x ≫ s))
    exact Recursive1.comp2 Recursive2.eqInd h1 h2
  · -- it decides Kc
    intro e
    constructor
    · intro hK
      have hE : ESet (2 * e) (2 * e + 1) :=
        ESet_iff.mpr (Or.inr ⟨by omega, by omega, by
          rw [show (2 * e) / 2 = e from by omega]; exact hK⟩)
      exact eqInd_eq ((hrepx _ _).mpr (hxESet _ _ hE))
    · intro hχ
      have hE : ESet (2 * e) (2 * e + 1) :=
        hExSet _ _ ((hrepx _ _).mp (eqInd_one_iff.mp hχ))
      rcases ESet_iff.mp hE with h | ⟨_, _, hK⟩
      · omega
      · rw [show (2 * e) / 2 = e from by omega] at hK
        exact hK

/-- **§1.572 HEADLINE (negative part): R is NOT an effective regular category.**
    The equivalence relation `E` — gluing `2e ~ 2e+1` exactly when `e` halts on
    itself — is an equivalence relation of R but the level of no cover. -/
theorem r_not_effective :
    ¬ ∀ (E : BinRel ExtNat omega omega), EquivalenceRelation E → IsEffective E :=
  fun h => ERel_not_effective (h ERel ⟨ERel_equivalence.1, ERel_equivalence.2.1,
    ERel_equivalence.2.2⟩)

/-- The witness form of the headline. -/
theorem r_not_effective_witness :
    ∃ E : BinRel ExtNat omega omega, EquivalenceRelation E ∧ ¬ IsEffective E :=
  ⟨ERel, ERel_equivalence, ERel_not_effective⟩


end Freyd.Rcat
