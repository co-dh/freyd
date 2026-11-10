import LeetQ.Rel.Lang.Eval
import LeetQ.Rel.BlocksRel

/-! The Rel language on the blocks world of `doc/rel-lang-design.md` §g, read from `programs/blocks.rel`; its
    front-end errors; the parser's round trip on every operator of §b. The module builds in 4.1 s (lake, three
    plans and every guard), each closed definition evaluated once (`run`, `hoist`). -/

namespace LeetQ.Rel.Lang.Test

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Alg QLean

/-- The blocks, as `Blocks` declares them: `𝟙` there is all blocks on the table. -/
local instance : Univ Blocks.X := ⟨_, Blocks.xs⟩

def blocks : String := include_str "../../../programs/blocks.rel"

/-- The definition `n` at the objects `A ⟶ B`. -/
def get (o : Out) (n : String) (A B : Obj) : Option (Rel A B) := do
  let (_, ⟨A', B', R⟩, _, _) ← o.vals.find? (·.1 == n)
  if h : A' = A ∧ B' = B then some (h.1 ▸ h.2 ▸ R) else none

abbrev XX : Obj := .prod .long .long
abbrev St : Obj := .arr XX

/-- `plan`'s moves in the order of their step. -/
def moves (o : Out) : Option (List (Int64 × Int64)) :=
  (get o "plan" .long XX).map fun R => (R.nub.toList.mergeSort fun a b => decide (a.1 ≤ b.1)).map (·.2)

/-- The program with the start state and the goal replaced, at the AST: the lines `S₀ ≜ …`, `G ≜ …`. -/
def variant (s g : String) : Except Err Out := do
  let prog ← Parse.parse blocks
  let s ← Parse.parseExpr s; let g ← Parse.parseExpr g
  run (prog.map fun
    | .defn p "S₀" [] _ => .defn p "S₀" [] (.rel s)
    | .defn p "G" [] _ => .defn p "G" [] (.rel g)
    | d => d)

def given : Except Err Out := runText (blocks ++ "qR ≜ QR(∋)\nqM ≜ QM(∋)\nqF ≜ QcF\nqh ≜ Qh(∋)\n")
def table : Except Err Out := variant "{(A,A),(B,B),(C,C)}" "{(A,B),(B,C)}"
def cycle : Except Err Out := variant "{(A,A),(B,B),(C,C)}" "{(A,B),(B,A)}"

def ok (r : Except Err Out) : Out := match r with | .ok o => o | .error _ => {}

#guard given.isOk && table.isOk && cycle.isOk
#guard (ok given).prints == ["plan = {(0, (C, C)), (1, (B, C)), (2, (A, B))}"]
#guard moves (ok given) == some [(2, 2), (1, 2), (0, 1)]
#guard moves (ok given) == some Blocks.plan
#guard moves (ok table) == some [(1, 2), (0, 1)]
#guard moves (ok table) == some (Blocks.solve 𝟙 Blocks.G)
#guard moves (ok cycle) == some []
#guard moves (ok cycle) == some (Blocks.solve 𝟙 (ofPairs [(0, 1), (1, 0)]))

/-! The elaborated definitions against `BlocksRel`'s transcription, as sets, on the reachable states. -/

def Q₁ : Rel St St := BlocksRel.Q Blocks.S₀
#guard get (ok given) "Q" St St == some Q₁
#guard get (ok given) "qR" St XX == some (BlocksRel.R Q₁ (Q₁ ≫ Alg.mem Q₁.val))
#guard get (ok given) "qM" St XX == some (BlocksRel.M Q₁ (Q₁ ≫ Alg.mem Q₁.val))
#guard get (ok given) "qF" St XX == some (BlocksRel.c Q₁ ≫ BlocksRel.F (Alg.ran (BlocksRel.c Q₁)))
#guard get (ok given) "qh" St St == some (BlocksRel.H Blocks.S₀ Blocks.G)

/-! One front-end error of each class, at its line. -/

def errAt (src : String) (line : Nat) (what : String) : Bool :=
  match runText src with
  | .error e => e.pos.line == line && (e.msg.splitOn what).length > 1
  | .ok _ => false

-- unknown name
#guard errAt "obj X = {A,B,C}\nf ≜ {(A,B)}\ng ≜ fh\n" 3 "unknown name 'h'"
-- type mismatch
#guard errAt "obj X = {A,B,C}\nobj N = 0…3\na ≜ {(A,B)}\nb ≜ {(1,2)}\nf ≜ ab\n" 5 "found N, expected X"
-- a family given where the row is not liftable
#guard errAt "obj X = {A,B,C}\nobj St = 𝒫(X×X)\nL(S : X ⟶ X) ≜ ⦇S,S⦈\nf ≜ L(∋)\n" 3 "not liftable"
-- a term that needs a universe its object does not have
#guard errAt "obj X = {A,B,C}\nobj St = 𝒫(X×X)\nprint ⊤(St,X)\n" 3 "has no universe"

/-! The parser's round trip: each operator row of §b, printed as it was read. -/

def trip (s : String) : Bool :=
  match Parse.parseExpr s [("R", 0), ("S", 0), ("p", 0), ("e", 0)] ["X"] with
  | .ok e => e.show == s
  | .error _ => false

#guard ["R S", "R°", "R ∩ S", "R ∪ S", "R − S", "∼R", "R ⇒ S", "𝟘", "⊤", "𝟙", "⊤(X, X)", "𝟙(X)", "dom(R)",
  "ran(R)", "R \\ S", "R / S", "frac(R, S)", "⟨R, S⟩", "π₁", "π₂", "R × S", "[R, S]", "inl", "inr", "R + S",
  "Λ(R)", "∋", "∈", "E(R)", "P(R)", "union", "τ", "nil", "α", "cons°", "⦇e, S⦈", "F(R)", "est(R)", "thin(R)",
  "filter(p)", "takewhile(p)", "length", "sum", "head", "tail", "prefix", "suffix", "succ", "plus", "≤", "<",
  "{(A, B), (B, A)}", "R S ∪ S R", "R ∩ S ∪ R", "R ∪ (S ∩ R)", "(R ∪ S) R", "R (S p)", "∼(R S)°", "(∼R)°",
  "∼R S"].all trip

/-! The parser on each line of `blocks.rel`: every composite and infix term in parentheses, as the note reads the
    formula (§c), not as the parser happens to print it. -/

def reading : Decl → Option (String × String)
  | .defn _ n _ (.rel e) => some (n, e.render 0 true)
  | .defn _ n _ (.test e f) => some (n, s!"{e.render 0 true} ⊑ {f.render 0 true}")
  | .print _ e => some ("print", e.render 0 true)
  | _ => none

#guard match Parse.parse blocks with
  | .error _ => false
  | .ok p => p.filterMap reading == [
    ("S₀", "{(C, A), (A, A), (B, B)}"),
    ("G", "{(A, B), (B, C)}"),
    ("R", "(S ∩ ∼𝟙)"),
    ("M", "∼((R(S)° ⊤) ∪ (⊤ R(S)))"),
    ("S'", "((S ∩ ∼(p ⊤)) ∪ p)"),
    ("h", "G ⊑ S"),
    ("c", "⟨𝟙, M(∋)⟩"),
    ("F", "S'((π₁ ∋), π₂)"),
    ("t", "(c Λ(F))"),
    ("s₀", "ran(Λ((⊤(X, X) ⟨𝟙, S₀⟩)))"),
    ("r", "Λ((s₀ ⊤(St, N)))"),
    ("L", "ran((r ⦇ran(⟨D, ((D ⊤) {(0, 0)})⟩), (π₂ ∪ (π₂ ⟨(π₁ B), (π₂ succ)⟩))⦈))"),
    ("Q", "ran((L(s₀, t) π₁))"),
    ("H", "(Q h(∋))"),
    ("C", "L(H, (Q t)°)"),
    ("W", "((C π₁)° (C π₂))"),
    ("δ", "(Λ(W) est(≤))"),
    ("K", "((Q c) dom((((Λ(F) δ) succ) ∩ (π₁ δ))))"),
    ("≼", "(((π₁ <) π₁°) ∪ ((π₁ π₁°) ∩ ((π₂ ≤) π₂°)))"),
    ("σ", "(Λ((K π₂)) est(≼))"),
    ("ν", "(⟨dom(σ), σ⟩ Λ(F))"),
    ("Z", "L(s₀, ν)"),
    ("ζ", "((Z π₂)° (Z π₁))"),
    ("plan", "(ζ σ)"),
    ("print", "plan")]

end LeetQ.Rel.Lang.Test
