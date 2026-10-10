/-
  LeetCode 42 — Trapping Rain Water.  Spec (cell count): `water ≜ |R(<) ∩ D|`, `D ≜ (≥)R(≥) ∩ (≤)R(≥)`.
  Derivation: `|R(<) ∩ D| = Σ(col)` with `col ≜ ⟪lvl,R⟫ (−)`, `lvl ≜ Λ(D) est(≥) = ⟪pmax,smax⟫ min`, and the two
  running maxima are the scans `pre`, `suf`, so `Σ(col)` is the two-pass `prog`.  Mathlib-free, constructive.
-/
import AOP.A7_2_RelSet
import AOP.A6_GenFold

namespace Freyd.Alg.RelSet.LC42

open Freyd CL PowerAllegory

/-- Indices `Fin n` (the bars) and values `ℕ` (heights, cell levels). -/
abbrev Idx (xs : List Nat) : RelSet.{0} := ⟨Fin xs.length⟩
abbrev Val : RelSet.{0} := ⟨Nat⟩

variable (xs : List Nat)

/-! ## The specification -/

/-- `R(xs) : Idx ⟶ Val`, `i ↦ xs[i]`: the bar heights. -/
def R : Idx xs ⟶ Val := graph fun i => xs[i]

/-- `D ≜ (≥)R(≥) ∩ (≤)R(≥)`: cell `(i,k)` is sheltered, a bar `≥ k` at or left of `i` and one at or right of `i`. -/
def D : Idx xs ⟶ Val := ((· ≥ ·) ≫ R xs ≫ (· ≥ ·)) ∩ ((· ≤ ·) ≫ R xs ≫ (· ≥ ·))

/-- `W ≜ R(<) ∩ D`: cell `(i,k)` holds water, above the bar at `i` and sheltered. -/
def W : Idx xs ⟶ Val := (R xs ≫ (· < ·)) ∩ D xs

/-- `W` is decidable: its two `∃`s range over the finite `Idx`. -/
instance (i : Fin xs.length) (k : Nat) : Decidable (W xs i k) :=
  decidable_of_iff (xs[i] < k ∧ (∃ j ∈ List.finRange xs.length, j ≤ i ∧ k ≤ xs[j]) ∧
      ∃ j ∈ List.finRange xs.length, i ≤ j ∧ k ≤ xs[j])
    ⟨fun ⟨h, ⟨j, _, hj, hk⟩, ⟨j', _, hj', hk'⟩⟩ => ⟨⟨_, rfl, h⟩, ⟨j, hj, _, rfl, hk⟩, ⟨j', hj', _, rfl, hk'⟩⟩,
     fun ⟨⟨_, e, h⟩, ⟨j, hj, _, e1, hk⟩, ⟨j', hj', _, e2, hk'⟩⟩ => by
       subst e e1 e2; exact ⟨h, ⟨j, List.mem_finRange j, hj, hk⟩, ⟨j', List.mem_finRange j', hj', hk'⟩⟩⟩

/-- A bound on every cell level: one above the tallest bar. -/
def bound : Nat := xs.foldr max 0 + 1

/-- `water ≜ |R(<) ∩ D|`, the number of cells that hold water. -/
def water : Nat := card (List.finRange xs.length) (bound xs) (W xs)

/-! ## The program: two scans and a sum -/

/-- `suf(xs)[i] = max(xs[i..])`, the running maximum from the right, one `foldr`. -/
def suf : List Nat → List Nat := List.foldr (fun x s => max x (s.getD 0 0) :: s) []

/-- `pre(xs)[i] = max(xs[..i])`, the running maximum from the left: `suf` of the reverse, reversed. -/
def pre (xs : List Nat) : List Nat := (suf xs.reverse).reverse

def prog (xs : List Nat) : Nat := (List.zipWith (· - ·) (List.zipWith min (pre xs) (suf xs)) xs).sum

/-! ## The scans (pointwise leaf facts) -/

theorem length_suf : ∀ xs : List Nat, (suf xs).length = xs.length
  | [] => rfl
  | _ :: xs => congrArg (· + 1) (length_suf xs)

theorem length_pre : (pre xs).length = xs.length := by simp [pre, length_suf]

theorem le_foldr_max : ∀ (l : List Nat) (y : Nat), y ∈ l → y ≤ l.foldr max 0
  | x :: l, y, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_foldr_max l y h) (Nat.le_max_right _ _)

/-- `suf(xs)[i]` is the greatest of `xs[j]`, `i ≤ j`. -/
theorem suf_spec : ∀ (xs : List Nat) (i : Nat), i < xs.length →
    (∀ j (hj : j < xs.length), i ≤ j → xs[j] ≤ (suf xs).getD i 0) ∧
      ∃ j, ∃ hj : j < xs.length, i ≤ j ∧ (suf xs).getD i 0 = xs[j]
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | x :: xs, 0, _ => by
    show (∀ j (hj : j < xs.length + 1), 0 ≤ j → (x :: xs)[j] ≤ max x ((suf xs).getD 0 0)) ∧
      ∃ j, ∃ hj : j < xs.length + 1, 0 ≤ j ∧ max x ((suf xs).getD 0 0) = (x :: xs)[j]
    cases xs with
    | nil => exact ⟨fun j hj _ => by cases j with | zero => simp [suf] | succ j => simp at hj, ⟨0, by simp, Nat.le_refl 0, by simp [suf]⟩⟩
    | cons y ys =>
      obtain ⟨h1, j, hj, _, e⟩ := suf_spec (y :: ys) 0 (by simp)
      refine ⟨fun j hj _ => ?_, ?_⟩
      · cases j with
        | zero => exact Nat.le_max_left _ _
        | succ j => exact Nat.le_trans (h1 j (by simpa using hj) (Nat.zero_le _)) (Nat.le_max_right _ _)
      · by_cases hx : (suf (y :: ys)).getD 0 0 ≤ x
        · exact ⟨0, by simp, Nat.le_refl 0, by rw [Nat.max_eq_left hx]; rfl⟩
        · exact ⟨j + 1, by simpa using hj, Nat.zero_le _, by
            rw [Nat.max_eq_right (Nat.le_of_lt (Nat.lt_of_not_le hx)), e]; rfl⟩
  | x :: xs, i + 1, h => by
    obtain ⟨h1, j, hj, hij, e⟩ := suf_spec xs i (by simpa using h)
    refine ⟨fun j hj hij => ?_, ⟨j + 1, by simpa using hj, by omega, by simpa [suf] using e⟩⟩
    cases j with
    | zero => omega
    | succ j => simpa [suf] using h1 j (by simpa using hj) (by omega)

/-- `pre(xs)[i]` is the greatest of `xs[j]`, `j ≤ i`. -/
theorem pre_spec (i : Nat) (hi : i < xs.length) :
    (∀ j (hj : j < xs.length), j ≤ i → xs[j] ≤ (pre xs).getD i 0) ∧
      ∃ j, ∃ hj : j < xs.length, j ≤ i ∧ (pre xs).getD i 0 = xs[j] := by
  have hr : (pre xs).getD i 0 = (suf xs.reverse).getD (xs.length - 1 - i) 0 := by
    simp [pre, List.getD_eq_getElem?_getD, length_suf, hi]; rw [List.getElem?_eq_getElem (by simp [length_suf]; omega)]; rfl
  obtain ⟨h1, j, hj, hij, e⟩ := suf_spec xs.reverse (xs.length - 1 - i) (by simp; omega)
  rw [hr]
  refine ⟨fun j' hj' hji => ?_, ⟨xs.length - 1 - j, by simp at hj; omega, by simp at hj; omega, ?_⟩⟩
  · have := h1 (xs.length - 1 - j') (by simp; omega) (by omega)
    simpa [List.getElem_reverse, show xs.length - 1 - (xs.length - 1 - j') = j' by omega] using this
  · rw [e, List.getElem_reverse]

/-! ## Step 2: `lvl = ⟪pmax, smax⟫ min` -/

/-- `pf(i) = pre(xs)[i]`, `sf(i) = suf(xs)[i]`, `lv(i) = min(pf(i), sf(i))`. -/
def pf (i : Fin xs.length) : Nat := (pre xs).getD i 0
def sf (i : Fin xs.length) : Nat := (suf xs).getD i 0
def lv (i : Fin xs.length) : Nat := min (pf xs i) (sf xs i)

/-- `pmax ≜ Λ((≥)R) est(≥)`: the tallest bar at or left of `i`. -/
def pmax : Idx xs ⟶ Val := Λ ((· ≥ ·) ≫ R xs) ≫ est (· ≥ ·)
/-- `smax ≜ Λ((≤)R) est(≥)`: the tallest bar at or right of `i`. -/
def smax : Idx xs ⟶ Val := Λ ((· ≤ ·) ≫ R xs) ≫ est (· ≥ ·)
/-- `lvl ≜ Λ(D) est(≥)`: the highest sheltered cell over `i`, the water level. -/
def lvl : Idx xs ⟶ Val := Λ (D xs) ≫ est (· ≥ ·)

theorem pf_greatest (i : Fin xs.length) :
    ((· ≥ ·) ≫ R xs) i (pf xs i) ∧ ∀ z, ((· ≥ ·) ≫ R xs) i z → z ≤ pf xs i :=
  let ⟨_, j, hj, hji, e⟩ := pre_spec xs i i.2
  ⟨⟨⟨j, hj⟩, hji, e⟩, fun _ ⟨j', hj', e'⟩ => e' ▸ (pre_spec xs i i.2).1 j' j'.2 hj'⟩

theorem sf_greatest (i : Fin xs.length) :
    ((· ≤ ·) ≫ R xs) i (sf xs i) ∧ ∀ z, ((· ≤ ·) ≫ R xs) i z → z ≤ sf xs i :=
  let ⟨_, j, hj, hij, e⟩ := suf_spec xs i i.2
  ⟨⟨⟨j, hj⟩, hij, e⟩, fun _ ⟨j', hj', e'⟩ => e' ▸ (suf_spec xs i i.2).1 j' j'.2 hj'⟩

/-- `D = ⟪pmax, smax⟫ min (≥)`: sheltered is below both running maxima. -/
theorem D_eq : D xs = ⟪pmax xs, smax xs⟫ ≫ minR ≫ (· ≥ ·) :=
  calc D xs
      = ((((· ≥ ·) : Idx xs ⟶ Idx xs) ≫ R xs) ≫ (· ≥ ·)) ∩ ((((· ≤ ·) : Idx xs ⟶ Idx xs) ≫ R xs) ≫ (· ≥ ·)) := by simp only [D, Cat.assoc]
    _ = (pmax xs ≫ (· ≥ ·)) ∩ (smax xs ≫ (· ≥ ·)) := by
        rw [down_est _ _ (pf_greatest xs), down_est _ _ (sf_greatest xs)]; rfl
    _ = ⟪pmax xs, smax xs⟫ ≫ minR ≫ (· ≥ ·) := down_inter _ _

/-- `pmax = pf`, the prefix scan. -/
theorem pmax_eq : pmax xs = (graph (pf xs) : Idx xs ⟶ Val) := Λ_est_greatest _ _ (pf_greatest xs)
/-- `smax = sf`, the suffix scan. -/
theorem smax_eq : smax xs = (graph (sf xs) : Idx xs ⟶ Val) := Λ_est_greatest _ _ (sf_greatest xs)

/-- `⟪pmax, smax⟫ min = lv`, the scans' pointwise minimum. -/
theorem pair_min : ⟪pmax xs, smax xs⟫ ≫ minR = (graph (lv xs) : Idx xs ⟶ Val) := by
  rw [pmax_eq, smax_eq, minR, rpair_graph, graph_comp]; rfl

/-- `lvl = ⟪pmax, smax⟫ min`. -/
theorem lvl_eq : lvl xs = ⟪pmax xs, smax xs⟫ ≫ minR :=
  calc lvl xs
      = Λ ((⟪pmax xs, smax xs⟫ ≫ minR) ≫ (· ≥ ·)) ≫ est (· ≥ ·) := by rw [lvl, D_eq, Cat.assoc]
    _ = ⟪pmax xs, smax xs⟫ ≫ minR := est_down _ (by rw [pair_min]; exact graph_simple _)

/-- `D = lvl (≥)`: a cell is sheltered iff it is at or below the water level. -/
theorem D_lvl : D xs = lvl xs ≫ (· ≥ ·) := by rw [D_eq, lvl_eq, Cat.assoc]

/-! ## Step 1: `|R(<) ∩ D| = Σ(col)` -/

/-- The fibre of `R(<) ∩ D` at `i` is the interval `(xs[i], lv(i)]`. -/
theorem W_iff (i : Fin xs.length) (k : Nat) : W xs i k ↔ xs[i] < k ∧ k ≤ lv xs i := by
  show (R xs ≫ (· < ·)) i k ∧ D xs i k ↔ _
  rw [D_lvl, lvl_eq, pair_min]
  exact ⟨fun ⟨⟨_, e, h⟩, _, e', hk⟩ => by subst e e'; exact ⟨h, hk⟩, fun ⟨h, hk⟩ => ⟨⟨_, rfl, h⟩, _, rfl, hk⟩⟩

theorem lv_lt (i : Fin xs.length) : lv xs i < bound xs :=
  let ⟨_, j, hj, _, e⟩ := suf_spec xs i i.2
  Nat.lt_succ_of_le (Nat.le_trans (Nat.min_le_right _ _)
    (by show (suf xs).getD i 0 ≤ _; rw [e]; exact le_foldr_max xs _ (List.getElem_mem hj)))

/-- `|R(<) ∩ D| = Σ_i (lv(i) − xs[i])`. -/
theorem water_cols : water xs = ((List.finRange xs.length).map fun i => lv xs i - xs[i]).sum :=
  card_intervals _ _ _ (fun i : Fin xs.length => xs[i]) (lv xs) (W_iff xs) (lv_lt xs)

/-- `col ≜ ⟪lvl, R⟫ (−)`: the water over bar `i`. -/
def col : Idx xs ⟶ Val := ⟪lvl xs, R xs⟫ ≫ graph fun p => p.1 - p.2

/-- `Σ(col) ≜ range ⦇[0, (col×𝟙) (+)]⦈`: the columns summed by a fold over the indices. -/
def colSum : dL Unit ⟶ Val := (graph fun _ => List.finRange xs.length) ≫
  relCata (I := listInitial (Fin xs.length)) (junc (sumCop (dL Unit) ⟨Fin xs.length × Nat⟩) (graph fun _ => 0)
    (rprodMap (col xs) (𝟙 Val) ≫ graph fun p : Nat × Nat => p.1 + p.2))

/-! ## Step 3–4: the fold is the two-pass sum -/

theorem col_eq : col xs = (graph fun i => lv xs i - xs[i] : Idx xs ⟶ Val) := by
  rw [col, lvl_eq, pair_min, R, rpair_graph, graph_comp]

/-- `Σ(col) = Σ_i (lv(i) − xs[i])`: `col` is a map, so the fold is `foldr` (`foldr_cata`). -/
theorem colSum_eq : colSum xs
    = (graph fun _ => ((List.finRange xs.length).map fun i => lv xs i - xs[i]).sum : dL Unit ⟶ Val) := by
  have arm : rprodMap (col xs) (𝟙 Val) ≫ graph (fun p : Nat × Nat => p.1 + p.2)
      = graph fun p : Fin xs.length × Nat => (lv xs p.1 - xs[p.1]) + p.2 := by
    rw [col_eq]
    exact hom_ext fun p _ => ⟨fun ⟨⟨_, _⟩, ⟨e1, e2⟩, e⟩ => by subst e1 e2; exact e,
      fun e => ⟨(lv xs p.1 - xs[p.1], p.2), ⟨rfl, rfl⟩, e⟩⟩
  rw [colSum, arm, ← consScalarAlg_eq_junc (fun _ => 0) (fun i s => (lv xs i - xs[i]) + s), ← foldr_cata,
    graph_comp, List.sum, List.foldr_map]

theorem cols_prog : (List.finRange xs.length).map (fun i => lv xs i - xs[i])
    = List.zipWith (· - ·) (List.zipWith min (pre xs) (suf xs)) xs :=
  List.ext_getElem (by simp [length_pre, length_suf]) fun k _ _ => by
    simp [lv, pf, sf, List.getD_eq_getElem?_getD, length_pre, length_suf, *]

/-! ## The derivation -/

/-- **The two-pass program counts the water cells**: `|R(<) ∩ D| = Σ(⟪lvl,R⟫ (−)) = prog`. -/
theorem water_prog : (graph fun _ => water xs : dL Unit ⟶ Val) = graph fun _ => prog xs :=
  calc (graph fun _ => water xs : dL Unit ⟶ Val)
      = graph fun _ => ((List.finRange xs.length).map fun i => lv xs i - xs[i]).sum := by rw [water_cols]
    _ = colSum xs := (colSum_eq xs).symm
    _ = graph fun _ => prog xs := by rw [colSum_eq, cols_prog]; rfl

#eval prog [0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]   -- 6
#eval prog [4, 2, 0, 3, 2, 5]                     -- 9
#eval prog []                                     -- 0
#eval water [0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]  -- 6, the spec counted directly
#print axioms water_prog

end Freyd.Alg.RelSet.LC42
