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

def given : Except Err Out := runText (blocks ++ "qR ≜ QR(∋)\nqM ≜ QM(∋)\nqF ≜ Qc⇝\nqh ≜ Qh(∋)\n")
def table : Except Err Out := variant "{(A,A),(B,B),(C,C)}" "{(A,B),(B,C)}"
def cycle : Except Err Out := variant "{(A,A),(B,B),(C,C)}" "{(A,B),(B,A)}"

def ok (r : Except Err Out) : Out := match r with | .ok o => o | .error _ => {}

/-- `Λ(S)est(P)`, `Λ(S)thin(P)` with the order `P` a family (the rows of §e on `S∋`) against the order closed
    (the closed row), on the reachable states — `est` of a map is the map — and on their complements, where a
    block has two values. -/
def orders : Except Err Out := runText (blocks ++ "O ≜ {(A,A),(A,B),(A,C),(B,B),(B,C),(C,C)}\n" ++
  "Of ≜ Q⊤(St,X)⟨𝟙,O⟩\nlc(S : X ⟶ X) ≜ Λ(S)est(O)\nlf(S : X ⟶ X, V : X ⟶ X) ≜ Λ(S)est(V)\n" ++
  "tc(S : X ⟶ X) ≜ Λ(S)thin(O)\ntf(S : X ⟶ X, V : X ⟶ X) ≜ Λ(S)thin(V)\nY(S : X ⟶ X) ≜ ∼S\n" ++
  "check Qlc(∋) = Q∋\ncheck Qlf(∋,Of) = Qlc(∋)\ncheck Qlf(Y(∋),Of) = Qlc(Y(∋))\n" ++
  "check Qtf(∋,Of) = Qtc(∋)\ncheck Qtf(Y(∋),Of) = Qtc(Y(∋))\nprint s₀lf(Y(∋),Of)\nprint s₀tf(Y(∋),Of)\n")

/-- A body given families of two indices, `∋` at `St` and `ζ∋` at `N` (the `k`-th state's pairs), runs at
    `St×N`: the fibre at `(s,k)` is `s ∩ ζ(k)`. Against the same meet written by hand, and at `(s₀,0)`, `(s₀,1)`. -/
def twoIdx : Except Err Out := runText (blocks ++ "k(S : X ⟶ X, T : X ⟶ X) ≜ S ∩ T\n" ++
  "check (Q×𝟙(N))k(∋,ζ∋) = (Q×𝟙(N))⟨π₁∋,π₂ζ∋⟩dom(π₁ ∩ π₂)π₁\n" ++
  "print (s₀×{(0,0)})k(∋,ζ∋)\nprint (s₀×{(1,1)})k(∋,ζ∋)\n")

/-- `X⦇e,S⦈` given a family (§e): at each key of a three-key family, the fibre of the lifted fold is the fold of
    the fibre. `p(R)` holds the pairs `(a,b)` with `b` at most two steps of `R` from `a`. -/
def foldLaw : Except Err Out := runText ("obj X = {A,B,C}\nobj K = 0…2\nobj L = 5…6\nobj 1 = {∗}\n" ++
  "ℓ ≜ Λ(⊤(1,L))\np(R : X ⟶ X) ≜ ran(ℓ⦇ran⟨𝟙,𝟙⟩, π₂ ∪ (π₂(𝟙×R))⦈)\n" ++
  "R₀ ≜ {(A,B)}\nR₁ ≜ {(A,B),(B,C)}\nR₂ ≜ {(A,B),(B,C),(C,A)}\n" ++
  "Fm ≜ {(0,0)}⊤(K,X)⟨𝟙,R₀⟩ ∪ ({(1,1)}⊤(K,X)⟨𝟙,R₁⟩) ∪ ({(2,2)}⊤(K,X)⟨𝟙,R₂⟩)\n" ++
  "pF ≜ p(Fm)\np₀ ≜ p(R₀)\np₁ ≜ p(R₁)\np₂ ≜ p(R₂)\n")

#guard let o := ok foldLaw
  [((0 : Int64), "p₀"), (1, "p₁"), (2, "p₂")].all fun (k, n) =>
    match get o "pF" .long (.prod XX XX), get o n XX XX with
    | some F, some R =>
      let f := (F.toList.filter (·.1 == k)).map (·.2)
      !R.toList.isEmpty && f.all R.toList.contains && R.toList.all f.contains
    | _, _ => false

/-- Object variables (§e): `uq : α ⟶ β` at `X ⟶ N` and at `N ⟶ X` against the ground copies `uX`, `uN`; and
    `d : α ⟶ α` given `Fm : K ⟶ X×X`, which `α ⟶ α` reads as a family, against `d` of each fibre. -/
def objVars : Except Err Out := runText ("obj X = {A,B,C}\nobj N = {x,y,z}\nobj K = 0…2\n" ++
  "uq(R : α ⟶ β) ≜ R ∩ (R°\\𝟙)\nuX(R : X ⟶ N) ≜ R ∩ (R°\\𝟙)\nuN(R : N ⟶ X) ≜ R ∩ (R°\\𝟙)\n" ++
  "R₁ ≜ {(A,x),(A,y),(B,z)}\nR₂ ≜ {(x,A),(y,B),(y,C),(z,C)}\na₁ ≜ uq(R₁)\nb₁ ≜ uX(R₁)\na₂ ≜ uq(R₂)\nb₂ ≜ uN(R₂)\n" ++
  "d(R : α ⟶ α) ≜ R ∩ (R°\\𝟙)\nF₀ ≜ {(A,B),(A,C)}\nF₁ ≜ {(A,B),(B,C)}\nF₂ ≜ {(A,A),(B,A),(B,B),(C,A)}\n" ++
  "Fm ≜ {(0,0)}⊤(K,X)⟨𝟙,F₀⟩ ∪ ({(1,1)}⊤(K,X)⟨𝟙,F₁⟩) ∪ ({(2,2)}⊤(K,X)⟨𝟙,F₂⟩)\n" ++
  "dF ≜ d(Fm)\nd₀ ≜ d(F₀)\nd₁ ≜ d(F₁)\nd₂ ≜ d(F₂)\n")

#guard let o := ok objVars
  let g (n : String) := get o n .long .long
  objVars.isOk && g "a₁" == g "b₁" && g "a₂" == g "b₂" && (g "a₁").map (·.toList) == some [(1, 2)] &&
    (g "a₂").map (·.n) == some 2 &&
    [((0 : Int64), "d₀"), (1, "d₁"), (2, "d₂")].all fun (k, n) =>
      match get o "dF" .long XX, g n with
      | some F, some R =>
        let f := (F.toList.filter (·.1 == k)).map (·.2)
        f.all R.toList.contains && R.toList.all f.contains && (k == 0 || !f.isEmpty)
      | _, _ => false

-- `ζ(0) = S₀`; `ζ(1)` is `S₀` with `C` moved to the table
#guard (ok twoIdx).prints.drop 1 == [
  "s₀ × {(0, 0)} k(∋, ζ ∋) = {(({(A, A), (B, B), (C, A)}, 0), (A, A)), (({(A, A), (B, B), (C, A)}, 0), (B, B)), " ++
    "(({(A, A), (B, B), (C, A)}, 0), (C, A))}",
  "s₀ × {(1, 1)} k(∋, ζ ∋) = {(({(A, A), (B, B), (C, A)}, 1), (A, A)), (({(A, A), (B, B), (C, A)}, 1), (B, B))}"]

-- at `S₀`, `∼S₀` gives `A` the values `B C`, `B` the values `A C`, `C` the values `B C`: the least of each
#guard (ok orders).prints.drop 1 == [
  "s₀ lf(Y(∋), Of) = {({(A, A), (B, B), (C, A)}, (A, B)), ({(A, A), (B, B), (C, A)}, (B, A)), " ++
    "({(A, A), (B, B), (C, A)}, (C, B))}",
  "s₀ tf(Y(∋), Of) = {({(A, A), (B, B), (C, A)}, (A, {B})), ({(A, A), (B, B), (C, A)}, (B, {A})), " ++
    "({(A, A), (B, B), (C, A)}, (C, {B}))}"]

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
-- a definition or parameter taking a builtin's name, or a name already defined or declared
#guard errAt "obj B = 0…1\nq ≜ π₁\nπ₂ ≜ π₁π₁\n" 3 "`π₂` is a builtin"
#guard errAt "obj B = 0…1\nf(S, E : B ⟶ B) ≜ S ∩ E\n" 2 "`E` is a builtin"
#guard errAt "obj B = 0…1\nK ≜ π₁\nq ≜ K\nK ≜ π₂\n" 4 "`K` is already defined at line 2"
#guard errAt "obj B = 0…1\nB ≜ π₁\n" 2 "`B` is already defined at line 1"
-- an object variable met at two objects, in one parameter's type or across two; a defined name is no variable
#guard errAt "obj X = {A,B,C}\nobj N = 0…3\nf(R : α ⟶ α) ≜ R\ng ≜ f({(A,1)})\n" 4
  "`α` in the type of 'R' is both X and N"
#guard errAt "obj X = {A,B,C}\nobj N = 0…3\nh(R : α ⟶ X, S : α ⟶ X) ≜ R\ng ≜ h({(A,B)},{(1,B)})\n" 4
  "`α` in the type of 'S' is both X and N"
#guard errAt "obj X = {A,B,C}\nπ ≜ 𝟙(X)\nf(R : π ⟶ π) ≜ R\n" 3 "expected an object, found 'π'"
-- a `where` item taking a defined name, a parameter's, an earlier item's or a builtin's; an item used outside
#guard errAt "obj B = 0…1\nK ≜ π₁\nf ≜ a where a ≜ π₂, K ≜ π₁\n" 3 "`K` is already defined at line 2"
#guard errAt "obj B = 0…1\nf(S) ≜ a where a ≜ S, S ≜ π₁\n" 2 "`S` is already a parameter of `f`"
#guard errAt "obj B = 0…1\nf ≜ a where a ≜ π₂, a ≜ π₁\n" 2 "`a` is already an item"
#guard errAt "obj B = 0…1\nf ≜ a where a ≜ π₂, π₁ ≜ a\n" 2 "`π₁` is a builtin"
#guard errAt "obj B = 0…1\nf ≜ a where a ≜ π₂\ng ≜ a\n" 3 "unknown name 'a'"

/-! The parser's round trip: each operator row of §b, printed as it was read. -/

def parsed (s : String) : Except Err Expr := Parse.parseExpr s [("R", 0), ("S", 0), ("p", 0), ("e", 0)] ["X"]
def trip (s : String) : Bool := match parsed s with | .ok e => e.show == s | .error _ => false
/-- `s` reads as `r`, every composite and infix term of `r` in parentheses (§c: one level, left to right). -/
def reads (s r : String) : Bool := match parsed s with | .ok e => e.render 0 true == r | .error _ => false

#guard ["R S", "R°", "R ∩ S", "R ∪ S", "R − S", "∼R", "R ⇒ S", "𝟘", "⊤", "𝟙", "⊤(X, X)", "𝟙(X)", "dom(R)",
  "ran(R)", "R \\ S", "R / S", "frac(R, S)", "⟨R, S⟩", "π₁", "π₂", "R × S", "[R, S]", "inl", "inr", "R + S",
  "Λ(R)", "∋", "∈", "E(R)", "P(R)", "union", "τ", "nil", "α", "cons°", "⦇e, S⦈", "F(R)", "est(R)", "thin(R)",
  "filter(p)", "takewhile(p)", "length", "sum", "head", "tail", "prefix", "suffix", "succ", "plus", "≤", "<",
  "{(A, B), (B, A)}", "R ∪ S R", "R S ∪ R", "R ∩ S ∪ R", "R ∪ S ∩ R", "R ∪ (S R)", "R (S p)", "∼(R S)°",
  "(∼R)°", "∼R S"].all trip

#guard [("R ∪ S R", "((R ∪ S) R)"), ("R S ∪ R", "((R S) ∪ R)"), ("R ∩ S ∪ R", "((R ∩ S) ∪ R)"),
  ("R ∪ S ∩ R", "((R ∪ S) ∩ R)"), ("∼R S", "(∼R S)"), ("R ∪ (S R)", "(R ∪ (S R))")].all fun (s, r) => reads s r

/-! The parser on each line of `blocks.rel`: every composite and infix term in parentheses, as the note reads the
    formula (§c), not as the parser happens to print it. -/

def reading : Decl → Option (String × String)
  | .defn _ n _ (.rel e) => some (n, e.render 0 true)
  | .defn _ n _ (.test e f) => some (n, s!"{e.render 0 true} ⊑ {f.render 0 true}")
  | .print _ e => some ("print", e.render 0 true)
  | _ => none

-- a `where` item in place in the body and in the items after it (§c)
#guard match Parse.parse "obj B = 0…1\nf(S) ≜ b ∪ S where a ≜ π₁, b ≜ a π₂ S\n" with
  | .ok p => p.filterMap reading == [("f", "(((π₁ π₂) S) ∪ S)")]
  | .error _ => false

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
    ("⇝", "S'((π₁ ∋), π₂)"),
    ("t", "(c Λ(⇝))"),
    ("s₀", "ran(Λ((⊤(X, X) ⟨𝟙, S₀⟩)))"),
    ("r", "Λ((s₀ ⊤(St, N)))"),
    ("L", "ran((r ⦇ran(⟨D, ((D ⊤) {(0, 0)})⟩), (π₂ ∪ (π₂ ⟨(π₁ B), (π₂ succ)⟩))⦈))"),
    ("Q", "ran((L(s₀, t) π₁))"),
    ("H", "(Q h(∋))"),
    ("C", "L(H, (Q t)°)"),
    ("W", "((C π₁)° (C π₂))"),
    ("δ", "(Λ(W) est(≤))"),
    ("K", "((Q c) dom((((Λ(⇝) δ) succ) ∩ (π₁ δ))))"),
    ("≼", "(((π₁ <) π₁°) ∪ ((π₁ π₁°) ∩ ((π₂ ≤) π₂°)))"),
    ("σ", "(Λ((K π₂)) est(≼))"),
    ("ν", "(⟨dom(σ), σ⟩ Λ(⇝))"),
    ("Z", "L(s₀, ν)"),
    ("ζ", "((Z π₂)° (Z π₁))"),
    ("plan", "(ζ σ)"),
    ("print", "plan")]

end LeetQ.Rel.Lang.Test
