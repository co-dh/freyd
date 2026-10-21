/-
  The basis every verb of `LeetQ.Rel` is composed from.  Most of it is `RelRep`'s own (`AOP/A6_FinRel`):
  `R ≫ S`, `R.conv` (as a test), `R.inter T`, `R.union S`, `RelRep.corefl p` (`p?`), `R.pair S` (`⟨R,S⟩`),
  `.ofFn f` (a function as a relation), `R.dom`, `R.first`/`R.last` (`est(<)`/`est(>)` on a fibre listed in
  position order), `R.est L`, `R.override S` (`R`, else `S` where `R` is empty), `R.compT T`, and
  `Λ(R) = RelRep.transpose R`.  What is added here is what those leave out: the list as a relation, the
  orders and windows on positions, the converse of a relation out of the positions listed again, the
  complement of a domain, a composite test, and the folds of a collected fibre.
-/
import AOP.A6_FinRel

namespace LeetQ.Rel

open Freyd.Alg.RelSet (RelRep RelTest FinRel)
open scoped Freyd.Alg.RelSet.RelRep

/-- `Λ(R)`: each fibre collected, in position order. -/
scoped prefix:max "Λ" => RelRep.transpose

variable {A B : Type} [DecidableEq A] [DecidableEq B]

/-- `ix(xs) : ℕ ⇸ A`: position `i` to `xs[i]`. -/
def ix (xs : List A) : RelRep Nat A := .vec xs.toArray rfl

/-- The identity on the positions `0 … n-1`. -/
def idn (n : Nat) : RelRep Nat Nat := RelRep.corefl (decide <| · < n)

/-- The total relation `⊤ : X ⇸ ℕ` onto the positions `0 … n-1`, in order: what `Λ`, `first` and `#` range over. -/
def tot {X : Type} (n : Nat) : RelRep X Nat := .enum fun _ => List.range n

/-- `≥` on positions, `i ↦ j ≤ i` in order: the prefix a running aggregate folds. -/
def ge : RelRep Nat Nat := .enum fun i => List.range (i + 1)

/-- `>` on positions, `i ↦ j < i` in order: `i` copies of `i`'s row is `⟨id, >⟩ ≫ π₁`. -/
def gt : RelRep Nat Nat := .enum List.range

/-- `W(n) = {(i,j) | i-n < j ≤ i}`, in order: the window of the moving aggregates. -/
def win (n : Nat) : RelRep Nat Nat := .enum fun i => List.range' (i + 1 - n) (min n (i + 1))

/-- `i ↦ i+k`, defined where that is a position: `pred = shift (-1)`. -/
def shift (k : Int) : RelRep Nat Nat :=
  .enum fun i => if 0 ≤ (i : Int) + k then [((i : Int) + k).toNat] else []

/-- `R°` for `R` out of the positions `0 … n-1`, listed again: each value's positions in increasing order,
    so `(cv n R).first` is the first position holding a value.  `R.conv` is only a test. -/
def cv (n : Nat) (R : RelRep Nat A) : RelRep A Nat :=
  .pairs (FinRel.ofList ((List.range n).flatMap fun i => (R.app i).map (·, i)))

/-- `(∉ dom R)?`: the coreflexive on what `R` relates to nothing. -/
def ndom (R : RelRep A B) : RelRep A A := RelRep.corefl fun a => (R.app a).isEmpty

/-- `R ≫ L ≫ S°` as a test on positions: some value of `i` is `L`-related to some value of `j`. -/
def via (R : RelRep Nat A) (L : RelTest A B) (S : RelRep Nat B) : RelTest Nat Nat := R.compT (S.compT L.conv).conv

/-- `b` before `a` in the order `lt` on values, ties broken by position: what `rank` counts. -/
def lex (lt : A → A → Bool) : RelTest (A × Nat) (A × Nat) := .test fun a b => lt b.1 a.1 || (b.1 == a.1 && b.2 < a.2)

/-- `∋ : List A ⇸ A`, a list to its members in order. -/
def mem : RelRep (List A) A := .enum id

/-- `⦇z, op⦈` on a fibre `Λ` collected. -/
def fold (z : B) (op : B → A → B) : RelRep (List A) B := .ofFn (·.foldl op z)

/-- `⦇op⦈` seeded by the first member; the empty fibre folds to nothing. -/
def fold1 (op : A → A → A) : RelRep (List A) A := .enum fun | [] => [] | x :: xs => [xs.foldl op x]

/-- The length of a collected fibre. -/
def len : RelRep (List A) Nat := fold 0 fun n _ => n + 1

/-! ## Running folds in one pass -/

open Freyd.Alg.RelSet (rangeFold rangeFold_eq)

/-- `Λ(S) ≫ G` at `i` is `G` of `S`'s fibre at `i`, collected. -/
theorem app_Λ {C : Type} [DecidableEq C] (S : RelRep Nat A) (G : RelRep (List A) C) (i : Nat) :
    (Λ(S) ≫ G).app i = G.app (S.app i) := by
  rw [RelRep.app_comp, RelRep.transpose_eq, RelRep.app_ofFn, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- **The scan law**: the prefix at `i+1` is the prefix at `i` with `i+1`'s fibre appended, so its fold is the
    fold at `i` folded on by that fibre alone. -/
theorem scan_succ (z : B) (op : B → A → B) (R : RelRep Nat A) (i : Nat) :
    (Λ(ge ≫ R) ≫ fold z op).app (i + 1) = ((Λ(ge ≫ R) ≫ fold z op).app i).map fun w => (R.app (i + 1)).foldl op w := by
  rw [app_Λ, app_Λ, RelRep.app_comp, RelRep.app_comp]
  show [((List.range (i + 1 + 1)).flatMap R.app).foldl op z] = [((List.range (i + 1)).flatMap R.app).foldl op z].map
    fun w => (R.app (i + 1)).foldl op w
  rw [List.range_succ (n := i + 1), List.flatMap_append, List.foldl_append, List.flatMap_singleton]; rfl

/-- `Λ(≥ ≫ R) ≫ ⦇z, op⦈` on the positions `0 … n-1`, by the scan law in one pass from the left, as a `vec`:
    no prefix is listed again (`app_scanR`). -/
def scanR (n : Nat) (z : B) (op : B → A → B) (R : RelRep Nat A) : RelRep Nat B :=
  R.withFib fun g => .vec (rangeFold (fun (p : B × Array B) i => let w := (g i).foldl op p.1; (w, p.2.push w))
    n 0 (z, Array.mkEmpty n)).2 rfl

/-- **`scanR` is the running fold** at every position `i < n`. -/
theorem app_scanR (n : Nat) (z : B) (op : B → A → B) (R : RelRep Nat A) (i : Nat) (h : i < n) :
    (scanR n z op R).app i = (Λ(ge ≫ R) ≫ fold z op).app i := by
  let pf := fun m => ((List.range m).flatMap R.app).foldl op z
  have go : ∀ m, ((List.range m).foldl (fun (p : B × Array B) i => let w := (R.fib i).foldl op p.1; (w, p.2.push w))
      (z, Array.mkEmpty n)) = (pf m, ((List.range m).map fun j => pf (j + 1)).toArray) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp [pf, List.range_succ, ← Array.foldl_toList, List.flatMap_append, List.foldl_append]
  rw [scanR, RelRep.withFib_eq, RelRep.app_vec, rangeFold_eq, ← List.range_eq_range']
  dsimp only
  rw [go n, cast_eq, List.getElem?_toArray, List.getElem?_map, List.getElem?_range h, app_Λ, RelRep.app_comp]
  rfl

/-- `⦇op⦈`'s state: nothing before the first member, which then seeds the fold. -/
def step1 (op : A → A → A) (o : Option A) (a : A) : Option A := some (o.elim a (op · a))

/-- `⦇op⦈` is the fold of `step1` from nothing. -/
theorem fold1_eq (op : A → A → A) (l : List A) : (fold1 op).app l = (l.foldl (step1 op) none).toList := by
  have go : ∀ (xs : List A) w, xs.foldl (step1 op) (some w) = some (xs.foldl op w) := by
    intro xs; induction xs with
    | nil => intro w; rfl
    | cons x xs ih => intro w; exact ih (op w x)
  cases l with
  | nil => rfl
  | cons x xs => exact (congrArg Option.toList (go xs x)).symm

/-- Keeping each member in turn ends at the last. -/
theorem foldl_some (l : List A) (o : Option A) : l.foldl (fun _ a => some a) o = l.getLast?.or o := by
  induction l generalizing o with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, List.getLast?_cons]; cases xs.getLast? <;> rfl

/-! ## The least of a fibre as a left fold -/

/-- `min` in the order `le`: the first unless it is not below the second, so a tie keeps the earlier. -/
def minBy (le : A → A → Bool) (a b : A) : A := if le a b then a else b

/-- **`first(est(le)) = ⦇min⦈`** on a fibre, `le` total and transitive: the first member `le`-below every member is
    the fold of `minBy le`, which replaces the least so far only by one strictly below it. -/
theorem est_first (le : A → A → Bool) (total : ∀ a b, le a b ∨ le b a) (trans : ∀ a b c, le a b → le b c → le a c)
    (l : List A) : (RelRep.estList le l).head?.toList = (fold1 (minBy le)).app l := by
  have refl : ∀ a, le a a := fun a => (total a a).elim id id
  cases l with
  | nil => rfl
  | cons x xs =>
    -- `m` is the least of `l`, and the first member of `l` below it
    let inv : List A → A → Prop := fun l m => m ∈ l ∧ (∀ v ∈ l, le m v) ∧ l.find? (le · m) = some m
    have step : ∀ l m y, inv l m → inv (l ++ [y]) (minBy le m y) := by
      intro l m y ⟨hm, hmin, hfind⟩
      unfold minBy
      by_cases h : le m y
      · rw [if_pos h]
        refine ⟨List.mem_append_left _ hm, fun v hv => ?_, by rw [List.find?_append, hfind]; rfl⟩
        rcases List.mem_append.1 hv with hv | hv
        · exact hmin v hv
        · rw [List.mem_singleton.1 hv]; exact h
      · rw [if_neg h]
        have hy : le y m := (total m y).resolve_left h
        refine ⟨List.mem_append_right _ (List.mem_singleton_self _), fun v hv => ?_, ?_⟩
        · rcases List.mem_append.1 hv with hv | hv
          · exact trans _ _ _ hy (hmin v hv)
          · rw [List.mem_singleton.1 hv]; exact refl y
        · rw [List.find?_append, List.find?_eq_none.2 fun v hv hvy => h (trans _ _ _ (hmin v hv) hvy)]
          simp [refl]
    have go : ∀ (ys l : List A) m, inv l m → inv (l ++ ys) (ys.foldl (minBy le) m) := by
      intro ys
      induction ys with
      | nil => intro l m h; simpa using h
      | cons y ys ih => intro l m h; rw [← List.singleton_append, ← List.append_assoc]; exact ih _ _ (step l m y h)
    obtain ⟨hm, hmin, hfind⟩ := go xs [x] x ⟨by simp, fun v hv => by rw [List.mem_singleton.1 hv]; exact refl x,
      by simp [refl]⟩
    rw [List.singleton_append] at hm hmin hfind
    have hf : RelRep.estList le (x :: xs) = (x :: xs).filter (le · (xs.foldl (minBy le) x)) := by
      rw [RelRep.estList]
      exact List.filter_congr fun v _ => Bool.eq_iff_iff.2 ⟨fun hv => List.all_eq_true.1 hv _ hm,
        fun hv => List.all_eq_true.2 fun y hy => trans _ _ _ hv (hmin y hy)⟩
    rw [hf, List.head?_filter, hfind]; rfl

omit [DecidableEq A] in
/-- `minBy` is associative for `le` total and transitive. -/
theorem minBy_assoc (le : A → A → Bool) (total : ∀ a b, le a b ∨ le b a) (trans : ∀ a b c, le a b → le b c → le a c)
    (a b c : A) : minBy le (minBy le a b) c = minBy le a (minBy le b c) := by
  unfold minBy
  cases hab : le a b <;> cases hbc : le b c <;> cases hac : le a c <;>
    simp only [hab, hbc, hac, if_true, if_false, Bool.false_eq_true]
  all_goals first | rfl | simp [trans _ _ _ hab hbc] at hac | simp [trans _ _ _ hac ((total b c).resolve_left (by simp [hbc]))] at hab

omit [DecidableEq A] in
theorem minBy_idem (le : A → A → Bool) (a : A) : minBy le a a = a := by unfold minBy; split <;> rfl

/-! ## A moving fold in two passes

The window `W(n)` at `i` is a suffix of the block of width `n` before `i`'s and a prefix of `i`'s block, so its fold
is the suffix fold within blocks merged with the prefix fold within blocks: two passes, whatever `n`. -/

/-- The fold of `step1 op` over the fibres of the positions `s … s+m-1`. -/
def wfold (op : A → A → A) (R : RelRep Nat A) (s m : Nat) : Option A :=
  ((List.range' s m).flatMap R.app).foldl (step1 op) none

omit [DecidableEq A] in
/-- A fold of `step1 op` from `o` is `o` merged with the fold from nothing, `op` associative. -/
theorem foldl_step1 (op : A → A → A) (assoc : ∀ a b c, op (op a b) c = op a (op b c)) (l : List A) (o : Option A) :
    l.foldl (step1 op) o = Option.merge op o (l.foldl (step1 op) none) := by
  induction l generalizing o with
  | nil => cases o <;> rfl
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (step1 op o x), ih (step1 op none x)]
    generalize xs.foldl (step1 op) none = w
    cases o <;> cases w <;> simp [step1, Option.merge, assoc]

omit [DecidableEq A] in
/-- **The fold of a concatenation is the merge of the folds.** -/
theorem wfold_add (op : A → A → A) (assoc : ∀ a b c, op (op a b) c = op a (op b c)) (R : RelRep Nat A)
    (s m k : Nat) : wfold op R s (m + k) = Option.merge op (wfold op R s m) (wfold op R (s + m) k) := by
  rw [wfold, wfold, wfold, ← List.range'_append_1, List.flatMap_append, List.foldl_append, foldl_step1 op assoc]

theorem succ_mod {i n : Nat} (hn : 0 < n) : (i + 1) % n = if i % n + 1 = n then 0 else i % n + 1 := by
  have h1 := Nat.mod_add_div i n; have h2 := Nat.mod_lt i hn
  split
  · rw [show i + 1 = 0 + n * (i / n + 1) by rw [Nat.mul_add, Nat.mul_one]; omega, Nat.add_mul_mod_self_left,
      Nat.zero_mod]
  · rw [show i + 1 = (i % n + 1) + n * (i / n) by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- A scan over one value per position is the fold of the prefix of those values. -/
theorem app_scanR_one {C : Type} [DecidableEq C] (N : Nat) (z : B) (op : B → C → B) (X : RelRep Nat C) (g : Nat → C)
    (hX : ∀ t, X.app t = [g t]) (i : Nat) (h : i < N) :
    (scanR N z op X).app i = [((List.range (i + 1)).map g).foldl op z] := by
  have e : ∀ l : List Nat, l.flatMap X.app = l.map g := fun l => by
    induction l with
    | nil => rfl
    | cons t l ih => rw [List.flatMap_cons, List.map_cons, hX, ih]; rfl
  rw [app_scanR _ _ _ _ _ h, app_Λ, RelRep.app_comp]
  show [((List.range (i + 1)).flatMap X.app).foldl op z] = _
  rw [e]

/-- Each position with the fold of its fibre. -/
def pos (op : A → A → A) (R : RelRep Nat A) : RelRep Nat (Nat × Option A) :=
  (RelRep.ofFn id).pair (Λ(R) ≫ fold none (step1 op))

theorem app_pos (op : A → A → A) (R : RelRep Nat A) (t : Nat) : (pos op R).app t = [(t, wfold op R t 1)] := by
  rw [pos, RelRep.app_pair, RelRep.app_ofFn, app_Λ]
  simp [fold, RelRep.app_ofFn, RelRep.cross, wfold, List.range'_one]

/-- The prefix fold within blocks of width `n`: one pass from the left, restarting at each block. -/
def bpre (op : A → A → A) (n N : Nat) (R : RelRep Nat A) : RelRep Nat (Option A) :=
  scanR N none (fun o p => if p.1 % n = 0 then p.2 else Option.merge op o p.2) (pos op R)

theorem app_bpre (op : A → A → A) (assoc : ∀ a b c, op (op a b) c = op a (op b c)) {n : Nat} (hn : 0 < n) (N : Nat)
    (R : RelRep Nat A) (i : Nat) (h : i < N) : (bpre op n N R).app i = [wfold op R (i - i % n) (i % n + 1)] := by
  rw [bpre, app_scanR_one N _ _ _ _ (app_pos op R) i h]
  congr 1
  induction i with
  | zero => simp [wfold, Option.merge]
  | succ i ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [succ_mod hn]
    by_cases hc : i % n + 1 = n
    · simp [hc]
    · have := Nat.mod_le i n
      simp only [hc, if_false, Nat.add_one_ne_zero]
      rw [show i + 1 - (i % n + 1) = i - i % n by omega, wfold_add op assoc R (i - i % n) (i % n + 1) 1,
        show i - i % n + (i % n + 1) = i + 1 by omega]

/-- The suffix fold within blocks of width `n`: the same pass on the positions reversed. -/
def bsuf (op : A → A → A) (n N : Nat) (R : RelRep Nat A) : RelRep Nat (Option A) :=
  .ofFn (N - 1 - ·) ≫ scanR N none (fun o p => if (p.1 + 1) % n = 0 then p.2 else Option.merge op p.2 o)
    (.ofFn (N - 1 - ·) ≫ pos op R)

theorem app_bsuf (op : A → A → A) (assoc : ∀ a b c, op (op a b) c = op a (op b c)) {n : Nat} (hn : 0 < n) (N : Nat)
    (R : RelRep Nat A) (j : Nat) (h : j < N) : (bsuf op n N R).app j = [wfold op R j (min (N - j) (n - j % n))] := by
  have hr : ∀ t, (RelRep.ofFn (N - 1 - ·) ≫ pos op R).app t = [(N - 1 - t, wfold op R (N - 1 - t) 1)] := fun t => by
    rw [RelRep.app_comp, RelRep.app_ofFn, List.flatMap_cons, List.flatMap_nil, List.append_nil, app_pos]
  have go : ∀ r, r < N → ((List.range (r + 1)).map fun t => (N - 1 - t, wfold op R (N - 1 - t) 1)).foldl
      (fun o p => if (p.1 + 1) % n = 0 then p.2 else Option.merge op p.2 o) none
      = wfold op R (N - 1 - r) (min (r + 1) (n - (N - 1 - r) % n)) := by
    intro r
    induction r with
    | zero =>
      intro _
      have := Nat.mod_lt (N - 1 - 0) hn
      rw [show min (0 + 1) (n - (N - 1 - 0) % n) = 1 by omega]
      simp only [Nat.zero_add, List.range_one, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      split
      · rfl
      · cases wfold op R (N - 1 - 0) 1 <;> rfl
    | succ r ih =>
      intro hr1
      rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      rw [show N - 1 - r = N - 1 - (r + 1) + 1 by omega]
      generalize N - 1 - (r + 1) = j
      rw [succ_mod hn]
      have := Nat.mod_lt j hn
      by_cases hc : j % n + 1 = n
      · simp only [hc, if_true]
        rw [show min (r + 1 + 1) (n - j % n) = 1 by omega]
      · simp only [hc, if_false, Nat.add_one_ne_zero]
        rw [show min (r + 1 + 1) (n - j % n) = 1 + min (r + 1) (n - (j % n + 1)) by omega, wfold_add op assoc R]
  rw [bsuf, RelRep.app_comp, RelRep.app_ofFn, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    app_scanR_one N _ _ _ _ hr _ (by omega), go _ (by omega), show N - 1 - (N - 1 - j) = j by omega,
    show N - 1 - j + 1 = N - j by omega]

/-- `Λ(W(n) ≫ R) ≫ ⦇op⦈` on the positions `0 … N-1` in two passes: the suffix fold within blocks at the window's
    start, `n` before, merged with the prefix fold within blocks at its end (`app_mwin`). -/
def mwin (op : A → A → A) (n N : Nat) (R : RelRep Nat A) : RelRep Nat A :=
  RelRep.corefl (fun _ => decide (0 < n)) ≫ (bpre op n N R).pair ((shift (1 - n) ≫ bsuf op n N R).override
    (.ofFn fun _ => none)) ≫ .enum fun q => (Option.merge op q.2 q.1).toList

/-- **`mwin` is the window fold** at every position `i < N`, `op` associative and idempotent. -/
theorem app_mwin (op : A → A → A) (assoc : ∀ a b c, op (op a b) c = op a (op b c)) (idem : ∀ a, op a a = a)
    (n N : Nat) (R : RelRep Nat A) (i : Nat) (h : i < N) : (mwin op n N R).app i = (Λ(win n ≫ R) ≫ fold1 op).app i := by
  rw [app_Λ, fold1_eq, RelRep.app_comp]
  show _ = (wfold op R (i + 1 - n) (min n (i + 1))).toList
  rw [mwin, RelRep.app_comp]
  by_cases hn : 0 < n
  · simp only [RelRep.corefl, RelRep.app_enum, hn, decide_true, if_true, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, RelRep.app_comp, RelRep.app_pair, app_bpre op assoc hn N R i h, RelRep.override_eq]
    have h1 := Nat.mod_add_div (i + 1 - n) n
    have h2 := Nat.mod_lt (i + 1 - n) hn
    by_cases hle : n ≤ i + 1
    · have e : (shift (1 - n)).app i = [i + 1 - n] := by
        show (if 0 ≤ (i : Int) + (1 - (n : Int)) then [((i : Int) + (1 - (n : Int))).toNat] else []) = _
        rw [if_pos (by omega)]; congr 1; omega
      rw [e, List.flatMap_cons, List.flatMap_nil, List.append_nil, app_bsuf op assoc hn N R _ (by omega)]
      simp only [List.cons_ne_nil, if_false, RelRep.cross, List.flatMap_cons, List.flatMap_nil, List.map_cons,
        List.map_nil, List.append_nil]
      rw [show min (N - (i + 1 - n)) (n - (i + 1 - n) % n) = n - (i + 1 - n) % n by omega,
        Nat.min_eq_left hle]
      by_cases hr : (i + 1 - n) % n = 0
      · have hi := Nat.add_mul_mod_self_left (n - 1) n ((i + 1 - n) / n)
        rw [show n - 1 + n * ((i + 1 - n) / n) = i by omega, Nat.mod_eq_of_lt (a := n - 1) (by omega)] at hi
        rw [hr, hi, show i - (n - 1) = i + 1 - n by omega, show n - 1 + 1 = n by omega, Nat.sub_zero]
        cases wfold op R (i + 1 - n) n <;> simp [Option.merge, idem]
      · have hi := Nat.add_mul_mod_self_left ((i + 1 - n) % n - 1) n ((i + 1 - n) / n + 1)
        rw [show (i + 1 - n) % n - 1 + n * ((i + 1 - n) / n + 1) = i by rw [Nat.mul_add, Nat.mul_one]; omega,
          Nat.mod_eq_of_lt (a := (i + 1 - n) % n - 1) (by omega)] at hi
        rw [hi, show i - ((i + 1 - n) % n - 1) = i + 1 - n + (n - (i + 1 - n) % n) by omega,
          show (i + 1 - n) % n - 1 + 1 = (i + 1 - n) % n by omega,
          show wfold op R (i + 1 - n) n = wfold op R (i + 1 - n) ((n - (i + 1 - n) % n) + (i + 1 - n) % n) by
            congr 1; omega, wfold_add op assoc R]
    · have e : (shift (1 - n)).app i = [] := by
        show (if 0 ≤ (i : Int) + (1 - (n : Int)) then [((i : Int) + (1 - (n : Int))).toNat] else []) = _
        rw [if_neg (by omega)]
      rw [e, List.flatMap_nil, Nat.mod_eq_of_lt (by omega), Nat.sub_self, show i + 1 - n = 0 by omega,
        Nat.min_eq_right (by omega)]
      simp only [if_true, RelRep.app_ofFn, RelRep.cross, List.flatMap_cons, List.flatMap_nil, List.map_cons,
        List.map_nil, List.append_nil]
      cases wfold op R 0 (i + 1) <;> rfl
  · simp only [RelRep.corefl, RelRep.app_enum, hn, decide_false]
    rw [show n = 0 by omega, Nat.min_eq_left (Nat.zero_le _)]; rfl

end LeetQ.Rel
