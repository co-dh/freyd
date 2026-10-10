/-
  LeetRunNat — L62 L70: the NAT-AXIS DP problems RUN in the
  relation-algebra interpreter's fold evaluator (`rel.RelInterp`'s `ProgEval`).

  These were previously skipped because their recursion is not a fold over the input LIST:
  L62/L70 fold over `Nat` — the initial algebra of `G X = 1 ⊕ X` (`zero`/`succ`).  They fit the
  interpreter once

  * the Nat axis is bridged onto the term language: `natSL n` is `n` written in unary as an
    `SL Unit` (`n` snocs over a wrapped unit; `wrap () = zero`, each snoc = one successor), so
    a `Prog.cata` over `natSL n` IS the Nat catamorphism.  `natSL`, its defining law
    `ProgEval.foldSL_natSL : foldSL … (natSL n) = cataNat b s n`, and the genuine `Nat.rec` fold
    `cataNat` now live in the ONE unified `ProgEval` (`rel/RelInterp`), used here via `open`.

  Wired (2):
  * L62 unique paths — iterate the DP row down the grid's `m` axis: a cata over `natSL m` with
    the row (`SnocList Nat Nat`, `n+1` columns) as carrier, base `initRow n`, step `stepRow` —
    `LC62`'s own algebra verbatim; `evalP (prog62 n) (natSL m) = LC62.solveFn (m+1) (n+1)`
    (`prog62_solve`), so `LC62.solve_correct` transfers to the interpreter run.
  * L70 climbing stairs — the tupled `(climb k, climb (k+1))` linearization as the Nat-fold:
    base `(1, 1)`, step `(a, b) ↦ (b, a + b)` — `LC70.fibPair`'s algebra verbatim;
    `evalP prog70 (natSL k) = LC70.solveFn k` (`prog70_solve`).

  `SL` is nonempty by design, and `natSL 0 = wrap ()` is the Nat leaf itself — the Nat axis has
  no out-of-range edge case.

  Mathlib-free; axioms ⊆ {propext, Quot.sound}.
-/
import rel.RelInterp
import leet.L62
import leet.L70

namespace Freyd.Alg.FinRel.NatH

open Freyd.Alg.FinRel.ProgEval
open Freyd.Alg.RelSet

/-! ## The Nat axis: `cataNat`, the unary bridge `natSL`, and its bridge law `foldSL_natSL`
    all live in the ONE unified `ProgEval` (`rel/RelInterp`) — used here via `open ProgEval`. -/

/-! ## L62 — unique paths: the DP row folded down the grid's `m` axis

  `LC62.rowAt m n` — `rowAt 0 n = initRow n`, `rowAt (m+1) n = stepRow (rowAt m n)` — is
  literally `m`-fold iteration of `stepRow` from `initRow n`: a Nat-cata with the whole DP row
  (`SnocList Nat Nat`, `n+1` columns) as carrier.  The answer projects the row's last entry. -/

/-- LC 62 as a term: cata over the unary `m` axis, carrier the DP row (`LC62`'s own `initRow`
    base and `stepRow` prefix-sum step), then read off the bottom-right corner. -/
def prog62 (n : Nat) : Prog (SL Unit) Nat :=
  .comp (.cata (fun _ => LC62.initRow n) (fun row _ => LC62.stepRow row)) (.fn LC62.lastOf)

/-- The Nat-cata of `LC62`'s algebra is `LC62.rowAt` — the L-file's own DP row. -/
theorem cataNat_rowAt (n : Nat) :
    ∀ m, cataNat (LC62.initRow n) LC62.stepRow m = LC62.rowAt m n
  | 0 => rfl
  | m + 1 => by
    show LC62.stepRow (cataNat (LC62.initRow n) LC62.stepRow m) = LC62.stepRow (LC62.rowAt m n)
    rw [cataNat_rowAt n m]

/-- **The wiring is exact**: the interpreter run computes `LC62.solveFn` (whence, by
    `LC62.solve_correct`, the true path count `LC62.paths (m+1) (n+1)`). -/
theorem prog62_solve (n m : Nat) :
    evalP (prog62 n) (natSL m) = LC62.solveFn (m + 1) (n + 1) := by
  show LC62.lastOf (foldSL (fun _ => LC62.initRow n) (fun row _ => LC62.stepRow row) (natSL m))
    = LC62.solveFn (m + 1) (n + 1)
  rw [foldSL_natSL, cataNat_rowAt]
  rfl

-- The L-file's own examples (`solveFn 3 7 = 28` etc.), on the interpreter's Nat axis:
example : evalP (prog62 6) (natSL 2) = 28 := by decide  -- 3 × 7 grid
example : evalP (prog62 2) (natSL 2) = 6 := by decide   -- 3 × 3 grid
example : evalP (prog62 4) (natSL 0) = 1 := by decide   -- 1 × 5 grid
example : evalP (prog62 0) (natSL 4) = 1 := by decide   -- 5 × 1 grid

#eval evalP (prog62 6) (natSL 2)  -- 28

/-! ## L70 — climbing stairs: the tupled Fibonacci fold over `Nat`

  `LC70.fibPair` — `(1, 1)` at zero, `(a, b) ↦ (b, a + b)` at each successor — is already the
  Nat-cata with the pair `(climb k, climb (k+1))` as carrier (the tupling/linearization trick);
  the answer projects the first component. -/

/-- LC 70 as a term: the tupled fold over the unary `n` axis (`LC70.fibPair`'s algebra
    verbatim), then project `climb n`. -/
def prog70 : Prog (SL Unit) Nat :=
  .comp (.cata (fun _ => ((1, 1) : Nat × Nat)) (fun p _ => (p.2, p.1 + p.2))) (.fn Prod.fst)

/-- The Nat-cata of `LC70`'s algebra is `LC70.fibPair` — the L-file's own tupled fold. -/
theorem cataNat_fibPair :
    ∀ k, cataNat ((1, 1) : Nat × Nat) (fun p => (p.2, p.1 + p.2)) k = LC70.fibPair k
  | 0 => rfl
  | k + 1 => by
    show (fun p : Nat × Nat => (p.2, p.1 + p.2))
        (cataNat ((1, 1) : Nat × Nat) (fun p => (p.2, p.1 + p.2)) k)
      = LC70.fibPair (k + 1)
    rw [cataNat_fibPair k]
    rfl

/-- **The wiring is exact**: the interpreter run computes `LC70.solveFn` (whence, by
    `LC70.solve_correct`, the true stair count `LC70.climb k`). -/
theorem prog70_solve (k : Nat) : evalP prog70 (natSL k) = LC70.solveFn k := by
  show (foldSL (fun _ => ((1, 1) : Nat × Nat)) (fun p _ => (p.2, p.1 + p.2)) (natSL k)).1
    = LC70.solveFn k
  rw [foldSL_natSL, cataNat_fibPair]
  rfl

-- The L-file's own examples, on the interpreter's Nat axis:
example : evalP prog70 (natSL 0) = 1 := by decide
example : evalP prog70 (natSL 2) = 2 := by decide
example : evalP prog70 (natSL 3) = 3 := by decide
example : evalP prog70 (natSL 5) = 8 := by decide

#eval evalP prog70 (natSL 5)  -- 8

end Freyd.Alg.FinRel.NatH
