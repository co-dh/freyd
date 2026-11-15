import LeetQ.Rel.Programs.Blocks
import LeetQ.Rel.Programs.SudokuAC
import LeetQ.Rel.AC3

/-! The Rel language on the blocks world of `doc/rel-lang-design.md` §g, the program `Programs.blocks`; its
    front-end errors; the parser's round trip on every operator of §b. Every program runs as its expansion
    (`rel_program`, `Expand`): its definitions `n.expanded`, its prints `n.prints`, its checks and ok bits
    `n.failures`, `n.ok`; a front-end error is read off a text by `Expand.read`, which evaluates nothing. -/

namespace LeetQ.Rel.Lang.Test

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Alg QLean

-- the prelude's definitions type-check
#guard (typesOf none).isOk
#guard Programs.prelude.ok

/-- The program `prog` and the text `src` read after it, in the scope `prog` leaves after the prelude. -/
def extend (prog : Program) (src : String) : Except Err Program := do
  pure (prog ++ (← Parse.parseIn (Parse.after (Parse.scope Programs.prelude) prog) src))

/-- The definition `n` of an expansion at the objects `A ⟶ B`. -/
def get (gs : List (String × Gen.Gv)) (n : String) (A B : Obj) : Option (Rel A B) := do
  let (_, ⟨A', B', c⟩) ← gs.find? (·.1 == n)
  if h : A' = A ∧ B' = B then some (h.1 ▸ h.2 ▸ c.rel) else none

/-- The value printed by each line of `ps`, after its ` = `. -/
def printed (ps : List String) : List String := ps.map fun s => (s.splitOn " = ").getLastD ""

abbrev XX : Obj := .prod .long .long
abbrev St : Obj := .arr XX

/-- `plan`'s moves in the order of their step. -/
def moves (gs : List (String × Gen.Gv)) : Option (List (Int64 × Int64)) :=
  (get gs "plan" .long XX).map fun R => (R.nub.toList.mergeSort fun a b => decide (a.1 ≤ b.1)).map (·.2)

rel_program given after Programs.blocks where
    qR : [X×X] ⟶ X×X ≜ QR(∋)
    qM : [X×X] ⟶ X×X ≜ QM(∋)
    qF : [X×X] ⟶ X×X ≜ Qc⇝
    qh : [X×X] ⟶ [X×X] ≜ Qh(∋)

-- the program with the start state and the goal replaced
rel_program table from Programs.blocks where
    S₀ : X ⟶ X ≜ {(A,A),(B,B),(C,C)}
    G : X ⟶ X ≜ {(A,B),(B,C)}
rel_program cycle from Programs.blocks where
    S₀ : X ⟶ X ≜ {(A,A),(B,B),(C,C)}
    G : X ⟶ X ≜ {(A,B),(B,A)}

/-- `Λ(S)est(P)`, `Λ(S)thin(P)` with the order `P` a family (the rows of §e on `S∋`) against the order closed
    (the closed row), on the reachable states — `est` of a map is the map — and on their complements, where a
    block has two values. -/
rel_program orders after Programs.blocks where
    O : X ⟶ X ≜ {(A,A),(A,B),(A,C),(B,B),(B,C),(C,C)}
    Of : [X×X] ⟶ X×X ≜ Q⊤(St,X)⟨𝟙,O⟩
    lc(S : X ⟶ X) : X ⟶ X ≜ Λ(S)est(O)
    lf(S : X ⟶ X, V : X ⟶ X) : X ⟶ X ≜ Λ(S)est(V)
    tc(S : X ⟶ X) : X ⟶ [X] ≜ Λ(S)thin(O)
    tf(S : X ⟶ X, V : X ⟶ X) : X ⟶ [X] ≜ Λ(S)thin(V)
    Y(S : X ⟶ X) : X ⟶ X ≜ ∼S
    check Qlc(∋) = Q∋
    check Qlf(∋,Of) = Qlc(∋)
    check Qlf(Y(∋),Of) = Qlc(Y(∋))
    check Qtf(∋,Of) = Qtc(∋)
    check Qtf(Y(∋),Of) = Qtc(Y(∋))
    print s₀lf(Y(∋),Of)
    print s₀tf(Y(∋),Of)

/-- A body given families of two indices, `∋` at `St` and `ζ∋` at `N` (the `k`-th state's pairs), runs at
    `St×N`: the fibre at `(s,k)` is `s ∩ ζ(k)`. Against the same meet written by hand, and at `(s₀,0)`, `(s₀,1)`. -/
rel_program twoIdx after Programs.blocks where
    k(S : X ⟶ X, T : X ⟶ X) : X ⟶ X ≜ S ∩ T
    check (Q×𝟙(N))k(∋,ζ∋) = (Q×𝟙(N))⟨π₁∋,π₂ζ∋⟩cor(𝟙)π₁
    print (s₀×{(0,0)})k(∋,ζ∋)
    print (s₀×{(1,1)})k(∋,ζ∋)

-- `ζ(0) = S₀`; `ζ(1)` is `S₀` with `C` moved to the table
#guard twoIdx.ok && twoIdx.prints == [
  "s₀ × {(0, 0)} k(∋, ζ ∋) = {(((A, A) (B, B) (C, A), 0), (A, A)), (((A, A) (B, B) (C, A), 0), (B, B)), " ++
    "(((A, A) (B, B) (C, A), 0), (C, A))}",
  "s₀ × {(1, 1)} k(∋, ζ ∋) = {(((A, A) (B, B) (C, A), 1), (A, A)), (((A, A) (B, B) (C, A), 1), (B, B))}"]

-- at `S₀`, `∼S₀` gives `A` the values `B C`, `B` the values `A C`, `C` the values `B C`: the least of each
#guard orders.ok && orders.prints == [
  "s₀ lf(Y(∋), Of) = {((A, A) (B, B) (C, A), (A, B)), ((A, A) (B, B) (C, A), (B, A)), " ++
    "((A, A) (B, B) (C, A), (C, B))}",
  "s₀ tf(Y(∋), Of) = {((A, A) (B, B) (C, A), (A, [B])), ((A, A) (B, B) (C, A), (B, [A])), " ++
    "((A, A) (B, B) (C, A), (C, [B]))}"]

rel_program printPlan after Programs.blocks where
    print plan

#guard given.ok && table.ok && cycle.ok
-- the file's own `check plan = …` holds and it prints nothing; `plan` printed here is the move list below
#guard Programs.blocks.ok && Programs.blocks.prints == [] && given.prints == []
#guard printPlan.prints == ["plan = {(0, (C, C)), (1, (B, C)), (2, (A, B))}"]
#guard moves Programs.blocks.expanded == some [(2, 2), (1, 2), (0, 1)]
#guard moves table.expanded == some [(1, 2), (0, 1)]
#guard moves cycle.expanded == some []

/-! The rest of the original file (front-end errors, round trips, lists, arith, fixed points, AC traces) is
    converted in `/data/tmp/rel-139/Test.next.lean` and lands in the next step (see the handoff). -/

end LeetQ.Rel.Lang.Test
