import LeetQ.Run.Alg

/-! # AC-3 (arc consistency, Mackworth's algorithm 3): the delta-round kernel of `νX : s ∩ ⋂ₖ Aₖ\(X Cₖ)`

The run-path definitions only, on `Alg`'s C twins; their agreement with the naive rounds is `AC3.lean`. -/

namespace LeetQ.Rel.Alg

open LeetQ.Rel

/-- One arc `A\(X C)` of an AC-3 body (`A : V ⟶ V`, `C : D ⟶ D`), with `𝟙(D)` for its division. -/
structure Revise (V D : Obj) where
  A : Rel V V
  C : Rel D D
  UV : Rel V V
  UD : Rel D D

/-- `as.foldl step Y` on a step twin, and whether it ran within capacity: the `&&` of every step's bit. -/
def foldlC {V D : Obj} {γ : Type} (step : Rel V D → γ → Rel V D × Bool) (as : List γ) (Y : Rel V D) : Rel V D × Bool :=
  as.foldl (fun p a => let r := step p.1 a; (r.1, p.2 && r.2)) (Y, true)

/-- The naive round's arc step `Y ∩ A\(X C)`, and its bit: `compC`'s, `leftDivC`'s, `interC`'s. -/
def naiveStepC {V D : Obj} (X Y : Rel V D) (a : Revise V D) : Rel V D × Bool :=
  let c := compC X a.C; let L := leftDivC a.A c.1 a.UV.key a.UD.key; let i := interC Y L.1
  (i.1, c.2 && L.2 && i.2)

/-- The AC-3 body `s ∩ ⋂ₖ Aₖ\(X Cₖ)`, one naive round, and whether it ran within capacity. -/
def acRoundC {V D : Obj} (s : Rel V D) (as : List (Revise V D)) (X : Rel V D) : Rel V D × Bool :=
  foldlC (naiveStepC X) as s

/-- The AC-3 body, one naive round: `fixOn` on it is `νX` the naive way. -/
def acRound {V D : Obj} (s : Rel V D) (as : List (Revise V D)) (X : Rel V D) : Rel V D := (acRoundC s as X).1

/-- The delta round's arc step `(antiJoin Y° T)° ∪ (Y ∩ (Δ A)\(Δ X C))`, `T = ran(Δ A)`: `(Δ A)\…` is `⊤` at every
    `x ∉ T`, so the division runs only on the rows `T` (its universe there, so no vacuous row is made) and `Y`'s other
    rows are kept. The bit is the `&&` of its ops'. -/
def deltaStepC {V D : Obj} (X : Rel V D) (Δ : Rel V V) (Y : Rel V D) (a : Revise V D) : Rel V D × Bool :=
  let R := compC Δ a.A; let T := ranC R.1; let j := antiJoinC Y° T.1
  let ΔX := compC Δ X; let S := compC ΔX.1 a.C
  let L := leftDivC R.1 S.1 T.1.key a.UD.key; let i := interC Y L.1; let u := unionC j.1° i.1
  (u.1, R.2 && T.2 && j.2 && ΔX.2 && S.2 && L.2 && i.2 && u.2)

/-- One delta round of the AC-3 body, from `(X, Δ)`, `Δ ⊑ 𝟙(V)` the variables whose domain shrank last round:
    `X′ = X ∩ ⋂ₖ (Δ Aₖ)\(X Cₖ)` and `Δ′ = dom(X − X′)`, `X − X′` the anti-join of the pairs; and whether it ran
    within capacity. The tie to the naive round is `AC3.acDelta_round`. -/
def acDeltaC {V D : Obj} (as : List (Revise V D)) (p : Rel V D × Rel V V) : (Rel V D × Rel V V) × Bool :=
  let X' := foldlC (deltaStepC p.1 p.2) as p.1
  let g := antiJoinC (idU (t := Obj.prod V D) (p.1.key, p.1.val)) (idU (t := Obj.prod V D) (X'.1.key, X'.1.val))
  let r := ranC (outl g.1)
  ((X'.1, r.1), X'.2 && g.2 && r.2)

/-- One delta round: `acDeltaC`'s state. -/
def acDelta {V D : Obj} (as : List (Revise V D)) (p : Rel V D × Rel V V) : Rel V D × Rel V V := (acDeltaC as p).1

/-- `νX : s ∩ ⋂ₖ Aₖ\(X Cₖ)` by delta rounds from `(s, 𝟙(V))` — the first the naive round — until `Δ′ = 𝟘`,
    at most `|s| + 1`, with the rounds run; and whether it ran within capacity: `nubC`'s bit `&&` `iterC`'s. -/
def acFixC {V D : Obj} (s : Rel V D) (as : List (Revise V D)) (U : Rel V V) : (Rel V D × Nat) × Bool :=
  let x := nubC s
  let r := iterC (x.1.n.toNat + 1) (fun st => st.2.1.n == 0)
    (fun st => let d := acDeltaC as (st.1, st.2.1); ((d.1.1, d.1.2, st.2.2 + 1), d.2)) (x.1, U, 0)
  ((r.1.1, r.1.2.2), x.2 && r.2)

/-- `νX : s ∩ ⋂ₖ Aₖ\(X Cₖ)` by delta rounds: `acFixC`'s answer. -/
def acFix {V D : Obj} (s : Rel V D) (as : List (Revise V D)) (U : Rel V V) : Rel V D × Nat := (acFixC s as U).1

end LeetQ.Rel.Alg
