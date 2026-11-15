/-
  LeetCode 238 — Product of Array Except Self — as an ALLEGORY PROGRAM.

  Problem: given `nums : List Int`, return `out` with `out[i] = ∏_{j≠i} nums[j]` (no division —
  some inputs contain `0`, so "divide by `nums[i]`" is unsound).

  Same recipe as `leet/L56.lean`/`Freyd/leetcode.md` S0, with a two-pass twist from S1/S10
  (`Freyd/leetcode.md`): the classic solution is prefix-product × suffix-product.

  1. **Data** — a plain `List Int` (the recipe's data object; no `SnocList` machinery needed,
     as in `L56`). The answer object is the SAME type, same length.

  2. **Program** — `solveFn nums = zipWith (·*·) (prefixProducts nums) (suffixProducts nums)`.
     * `prefixProducts nums = preScan 1 nums`, where `preScan acc (x::xs) = acc :: preScan (acc*x)
       xs` THREADS the running product DOWN the argument (an ordinary accumulator-carrying fold,
       the `L56`-`mergeRun`/`L121`-tuple shape): `pre[i] = ∏_{j<i} nums[j]`.
     * `suffixProducts nums = (sufScan nums).1`, where `sufScan (x::xs) = (tot :: sl, tot*x)` with
       `(sl, tot) := sufScan xs` builds the running product on the RETURN side (S10's "carry a
       whole row" shape read backwards: no reversal, no fuel — plain single-argument structural
       recursion on `nums`, the second component `tot` doubling as "total product of the
       already-processed suffix"): `suf[i] = ∏_{j>i} nums[j]`.

  3. **Specification** — an INDEX-explicit relation, not an order to extremize (a structural-
     output problem like `L56`'s interval merge): `prodExcept nums i := (nums.take i).prod *
     (nums.drop (i+1)).prod`, the honest "product of everything except position `i`" via a
     take/drop split (no division). Correctness needs BOTH the output's length (`= nums.length`)
     and its value at every index (phrased via `List.getElem?`, `[i]? = some v`, which sidesteps
     dependent `i < l.length` proof-term bookkeeping while still pinning down both facts at once
     via `getElem?_eq_some_iff`).

  4. **Correctness** — the crux is `preScan_get?`/`sufScan_get?`, each a plain structural induction
     strengthening "the fold equals the spec" from a bare list to an EXPLICIT per-index formula
     (S10's move), landing on `acc * (nums.take i).prod` / `(nums.drop (i+1)).prod` respectively.
     `solve_value` combines them through Lean core's OWN `getElem?_zipWith_eq_some` (no hand-
     rolled `zipWith` reasoning needed — it is already in `Init.Data.List.Zip`, reused instead of
     rederived, per DRY). `solve_correct` packages `solve := graph solveFn` in `Rel(Set)` and
     restates `IsProductExceptSelf`.

  Mathlib-free; all algebra is `Int.mul_assoc`/`Int.mul_comm`/`Int.one_mul` (Lean core,
  `Init/Data/Int/Lemmas.lean`) — no `ring`, no `omega` on multiplication (nonlinear). Axioms
  `⊆ {propext, Quot.sound}` (inherited transitively via `Rel(Set)`'s `hom_ext`/`graph_map`, exactly
  as in `L56`); no `Classical.choice`.
-/
import AOP.A6_1_RelSet
import Freyd.RelSet

namespace Freyd.Alg.RelSet.LC238

open Freyd

/-! ## Mathlib-free `Int` list product -/

/-- The product of a list of integers (empty product `= 1`). -/
def listProd : List Int → Int
  | [] => 1
  | x :: xs => x * listProd xs

@[simp] theorem listProd_nil : listProd ([] : List Int) = 1 := rfl
@[simp] theorem listProd_cons (x : Int) (xs : List Int) : listProd (x :: xs) = x * listProd xs := rfl

/-! ## Data & answer object: a plain `List Int`, same object both sides -/

/-- The object of integer lists in `Rel(Set)` — both the input `nums` and the output live here. -/
abbrev Nums : RelSet.{0} := ⟨List Int⟩

/-! ## Program, part 1: exclusive PREFIX products — an accumulator threaded DOWN the recursion -/

/-- `preScan acc (x :: xs) = acc :: preScan (acc*x) xs`: emit the running product `acc`, then fold
    `x` into it before recursing. `acc` is carried, not itself decreasing — ordinary structural
    recursion on the list argument (same shape as `L56`'s `mergeRun cur`). -/
def preScan (acc : Int) : List Int → List Int
  | [] => []
  | x :: xs => acc :: preScan (acc * x) xs

@[simp] theorem preScan_nil (acc : Int) : preScan acc ([] : List Int) = [] := rfl
@[simp] theorem preScan_cons (acc x : Int) (xs : List Int) :
    preScan acc (x :: xs) = acc :: preScan (acc * x) xs := rfl

/-- The exclusive prefix products: `pre[i] = ∏_{j<i} nums[j]`, `pre[0] = 1`. -/
def prefixProducts (nums : List Int) : List Int := preScan 1 nums

/-! ## Program, part 2: exclusive SUFFIX products — the running product built on the RETURN side

  No reversal, no fuel: `sufScan` is a plain structural recursion on `nums` whose second output
  component happens to double as "the total product of everything already folded in". -/

/-- `sufScan (x :: xs) = (tot :: sl, tot * x)` where `(sl, tot) := sufScan xs`: `sl` is `xs`'s own
    suffix-product list (untouched — inserting `x` in FRONT never changes what comes after `xs`'s
    elements), `tot` is `xs`'s total product (the suffix product FOR `x` itself), and the new total
    folds `x` in. -/
def sufScan : List Int → List Int × Int
  | [] => ([], 1)
  | x :: xs => ((sufScan xs).2 :: (sufScan xs).1, (sufScan xs).2 * x)

@[simp] theorem sufScan_nil : sufScan ([] : List Int) = ([], 1) := rfl
@[simp] theorem sufScan_cons (x : Int) (xs : List Int) :
    sufScan (x :: xs) = ((sufScan xs).2 :: (sufScan xs).1, (sufScan xs).2 * x) := rfl

/-- The exclusive suffix products: `suf[i] = ∏_{j>i} nums[j]`, `suf[last] = 1`. -/
def suffixProducts (nums : List Int) : List Int := (sufScan nums).1

/-! ## The program -/

/-- **The allegory program's underlying function**: zip the prefix- and suffix-product scans. -/
def solveFn (nums : List Int) : List Int :=
  List.zipWith (· * ·) (prefixProducts nums) (suffixProducts nums)

/-! ## The specification -/

/-- **The spec, honest and division-free**: the product of everything except position `i`, via a
    `take`/`drop` split of `nums` around `i`. -/
def prodExcept (nums : List Int) (i : Nat) : Int :=
  listProd (nums.take i) * listProd (nums.drop (i + 1))

/-- **Full correctness of a candidate output**: right length, and every index carries the honest
    product-except-self value (`[i]?`, so both "`i` is in range" and "the value there is right"
    are packaged in one clause per `List.getElem?_eq_some_iff`). -/
def IsProductExceptSelf (nums out : List Int) : Prop :=
  out.length = nums.length ∧ ∀ i, i < nums.length → out[i]? = some (prodExcept nums i)

/-! ## Length lemmas -/

theorem length_preScan (acc : Int) (nums : List Int) : (preScan acc nums).length = nums.length := by
  induction nums generalizing acc with
  | nil => rfl
  | cons x xs ih => rw [preScan_cons, List.length_cons, List.length_cons, ih]

theorem length_sufScan (nums : List Int) : (sufScan nums).1.length = nums.length := by
  induction nums with
  | nil => rfl
  | cons x xs ih => rw [sufScan_cons, List.length_cons, List.length_cons, ih]

/-- **Length correctness**: `solveFn` preserves the input's length. -/
theorem length_solveFn (nums : List Int) : (solveFn nums).length = nums.length := by
  unfold solveFn prefixProducts suffixProducts
  rw [List.length_zipWith, length_preScan, length_sufScan, Nat.min_self]

/-! ## Value lemmas — the crux: strengthen each scan to an EXPLICIT per-index formula (S10) -/

/-- `preScan acc nums` at index `i < nums.length` equals `acc` times the product of `nums`'s first
    `i` elements — the exclusive-prefix-product formula, carrying `acc` through the induction. -/
theorem preScan_get? (nums : List Int) (acc : Int) (i : Nat) (hi : i < nums.length) :
    (preScan acc nums)[i]? = some (acc * listProd (nums.take i)) := by
  induction nums generalizing acc i with
  | nil => exact absurd hi (Nat.not_lt_zero i)
  | cons x xs ih =>
    cases i with
    | zero => rw [preScan_cons, List.getElem?_cons_zero, List.take_zero, listProd_nil, Int.mul_one]
    | succ j =>
      have hj : j < xs.length := by rw [List.length_cons] at hi; omega
      rw [preScan_cons, List.getElem?_cons_succ, ih (acc * x) j hj, List.take_succ_cons,
        listProd_cons, Int.mul_assoc]

/-- `sufScan nums`'s second component is the total product of `nums` (up to commutativity — the
    fold multiplies "product-of-tail times head", `listProd` multiplies "head times product-of-
    tail"). -/
theorem sufScan_snd (nums : List Int) : (sufScan nums).2 = listProd nums := by
  induction nums with
  | nil => rfl
  | cons x xs ih => rw [sufScan_cons, ih, listProd_cons, Int.mul_comm]

/-- `sufScan nums`'s list at index `i < nums.length` equals the product of everything AFTER
    position `i` — the exclusive-suffix-product formula. -/
theorem sufScan_get? (nums : List Int) (i : Nat) (hi : i < nums.length) :
    (sufScan nums).1[i]? = some (listProd (nums.drop (i + 1))) := by
  induction nums generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero i)
  | cons x xs ih =>
    cases i with
    | zero => rw [sufScan_cons, List.getElem?_cons_zero, sufScan_snd, List.drop_succ_cons, List.drop_zero]
    | succ j =>
      have hj : j < xs.length := by rw [List.length_cons] at hi; omega
      rw [sufScan_cons, List.getElem?_cons_succ, ih j hj, List.drop_succ_cons]

/-- **Value correctness (headline content)**: `solveFn nums` carries the honest product-except-
    self value at every in-range index — combines `preScan_get?`/`sufScan_get?` through Lean
    core's `getElem?_zipWith_eq_some`. -/
theorem solve_value (nums : List Int) (i : Nat) (hi : i < nums.length) :
    (solveFn nums)[i]? = some (prodExcept nums i) := by
  unfold solveFn
  rw [List.getElem?_zipWith_eq_some]
  refine ⟨_, _, preScan_get? nums 1 i hi, sufScan_get? nums i hi, ?_⟩
  unfold prodExcept; rw [Int.one_mul]

/-- **Correctness (headline)**: for every input, `solveFn` computes a faithful product-except-
    self list — right length, right value at every index. Fully constructive. -/
theorem solveFn_correct (nums : List Int) : IsProductExceptSelf nums (solveFn nums) :=
  ⟨length_solveFn nums, solve_value nums⟩

/-! ## Packaging as a genuine `Rel(Set)` morphism -/

/-- **The allegory program**: LeetCode 238's solution as a morphism `Nums ⟶ Nums` in `Rel(Set)`. -/
def solve : Nums ⟶ Nums := graph solveFn

/-- `solve` is a `Map` (it is the graph of a function). -/
theorem solve_map : Map solve := graph_map solveFn

/-- **The program refines the specification** (pointwise in `Rel(Set)`): whatever `solve` relates
    `nums` to is a faithful product-except-self list. -/
theorem solve_correct (nums out : List Int) (h : solve nums out) : IsProductExceptSelf nums out := by
  have hout : out = solveFn nums := h
  rw [hout]; exact solveFn_correct nums

/-! ## Specification and the structural-output headline -/

/-- The **specification** as a morphism `Nums ⟶ Nums` in `Rel(Set)`: `out` is the honest product-
    except-self list of `nums` (`IsProductExceptSelf`, stated via `prodExcept`, program-independent). -/
def spec : Nums ⟶ Nums := fun nums out => IsProductExceptSelf nums out

/-- **Uniqueness**: an `IsProductExceptSelf` output is unique — two candidates of the right length
    with the right value at every in-range index agree at every index (both `none` out of range),
    hence are equal by list extensionality. -/
theorem product_unique (nums o₁ o₂ : List Int)
    (h₁ : IsProductExceptSelf nums o₁) (h₂ : IsProductExceptSelf nums o₂) : o₁ = o₂ := by
  apply List.ext_getElem?
  intro i
  rcases Nat.lt_or_ge i nums.length with hi | hi
  · rw [h₁.2 i hi, h₂.2 i hi]
  · rw [List.getElem?_eq_none (by rw [h₁.1]; exact hi), List.getElem?_eq_none (by rw [h₂.1]; exact hi)]

/-- **`solve` equals `spec` as relations** — the STRUCTURAL-OUTPUT headline: existence
    (`solveFn_correct`) plus uniqueness (`product_unique`) make the program exactly the product-
    except-self relation. -/
theorem solve_eq_spec : solve = spec := by
  apply hom_ext; intro nums out
  show (out = solveFn nums) ↔ IsProductExceptSelf nums out
  constructor
  · intro h; rw [h]; exact solveFn_correct nums
  · intro h; exact product_unique nums out (solveFn nums) h (solveFn_correct nums)

/-! ## Running the program -/

-- LeetCode 238's own example: `[1,2,3,4] → [24,12,8,6]`.
example : solveFn [1, 2, 3, 4] = [24, 12, 8, 6] := by decide
-- With a zero: every OTHER output collapses to `0`, but the zero's own slot survives.
example : solveFn [0, 4, 0] = [0, 0, 0] := by decide
-- A single negative flips the sign of every other slot.
example : solveFn [-1, 1, 2] = [2, -2, -1] := by decide

end Freyd.Alg.RelSet.LC238
