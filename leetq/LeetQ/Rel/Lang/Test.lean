import LeetQ.Rel.Lang.Eval
import LeetQ.Rel.Programs.Blocks
import LeetQ.Rel.Programs.SudokuAC
import LeetQ.Rel.AcFix

/-! The Rel language on the blocks world of `doc/rel-lang-design.md` §g, the program `Programs.blocks`; its
    front-end errors; the parser's round trip on every operator of §b. The module builds in 4.1 s (lake, three
    plans and every guard), each closed definition evaluated once (`run`, `hoist`). -/

namespace LeetQ.Rel.Lang.Test

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Alg QLean

-- the prelude's definitions type-check
#guard (typesOf none).isOk

/-- The program `prog` and the text `src` read after it, in the scope `prog` leaves after the prelude. -/
def extend (prog : Program) (src : String) : Except Err Program := do
  pure (prog ++ (← Parse.parseIn (Parse.after (Parse.scope Programs.prelude) prog) src))

/-- Run the program `prog` with the text `src` after it (`extend`). -/
def runExt (prog : Program) (src : String) : Except Err Out := extend prog src >>= runProgram

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
  -- the file's `check plan = …` states the plan of its own S₀ and G, so it is dropped for a variant
  let prog := Programs.blocks.filter fun | .check .. => false | _ => true
  let s ← Parse.parseExpr s; let g ← Parse.parseExpr g
  runProgram (prog.map fun
    | .defn p "S₀" [] _ ty => .defn p "S₀" [] (.rel s) ty
    | .defn p "G" [] _ ty => .defn p "G" [] (.rel g) ty
    | d => d)

def given : Except Err Out := runExt Programs.blocks ("qR : [X×X] ⟶ X×X ≜ QR(∋)\nqM : [X×X] ⟶ X×X ≜ QM(∋)\n" ++
  "qF : [X×X] ⟶ X×X ≜ Qc⇝\nqh : [X×X] ⟶ [X×X] ≜ Qh(∋)\n")
def table : Except Err Out := variant "{(A,A),(B,B),(C,C)}" "{(A,B),(B,C)}"
def cycle : Except Err Out := variant "{(A,A),(B,B),(C,C)}" "{(A,B),(B,A)}"

def ok (r : Except Err Out) : Out := match r with | .ok o => o | .error _ => {}

/-- `Λ(S)est(P)`, `Λ(S)thin(P)` with the order `P` a family (the rows of §e on `S∋`) against the order closed
    (the closed row), on the reachable states — `est` of a map is the map — and on their complements, where a
    block has two values. -/
def orders : Except Err Out := runExt Programs.blocks ("O : X ⟶ X ≜ {(A,A),(A,B),(A,C),(B,B),(B,C),(C,C)}\n" ++
  "Of : [X×X] ⟶ X×X ≜ Q⊤(St,X)⟨𝟙,O⟩\nlc(S : X ⟶ X) : X ⟶ X ≜ Λ(S)est(O)\n" ++
  "lf(S : X ⟶ X, V : X ⟶ X) : X ⟶ X ≜ Λ(S)est(V)\ntc(S : X ⟶ X) : X ⟶ [X] ≜ Λ(S)thin(O)\n" ++
  "tf(S : X ⟶ X, V : X ⟶ X) : X ⟶ [X] ≜ Λ(S)thin(V)\nY(S : X ⟶ X) : X ⟶ X ≜ ∼S\n" ++
  "check Qlc(∋) = Q∋\ncheck Qlf(∋,Of) = Qlc(∋)\ncheck Qlf(Y(∋),Of) = Qlc(Y(∋))\n" ++
  "check Qtf(∋,Of) = Qtc(∋)\ncheck Qtf(Y(∋),Of) = Qtc(Y(∋))\nprint s₀lf(Y(∋),Of)\nprint s₀tf(Y(∋),Of)\n")

/-- A body given families of two indices, `∋` at `St` and `ζ∋` at `N` (the `k`-th state's pairs), runs at
    `St×N`: the fibre at `(s,k)` is `s ∩ ζ(k)`. Against the same meet written by hand, and at `(s₀,0)`, `(s₀,1)`. -/
def twoIdx : Except Err Out := runExt Programs.blocks ("k(S : X ⟶ X, T : X ⟶ X) : X ⟶ X ≜ S ∩ T\n" ++
  "check (Q×𝟙(N))k(∋,ζ∋) = (Q×𝟙(N))⟨π₁∋,π₂ζ∋⟩cor(𝟙)π₁\n" ++
  "print (s₀×{(0,0)})k(∋,ζ∋)\nprint (s₀×{(1,1)})k(∋,ζ∋)\n")

/-- `X⦇e,S⦈` given a family (§e): at each key of a three-key family, the fibre of the lifted fold is the fold of
    the fibre. `p(R)` holds the pairs `(a,b)` with `b` at most two steps of `R` from `a`. -/
def foldLaw : Except Err Out := runText ("obj X = {A,B,C}\nobj K = 0…2\nobj L = 5…6\n" ++
  "ℓ : 1 ⟶ [L] ≜ Λ(⊤(1,L))\np(R : X ⟶ X) : X×X ⟶ X×X ≜ ran(ℓ⦇ran⟨𝟙,𝟙⟩, π₂ ∪ (π₂(𝟙×R))⦈)\n" ++
  "R₀ : X ⟶ X ≜ {(A,B)}\nR₁ : X ⟶ X ≜ {(A,B),(B,C)}\nR₂ : X ⟶ X ≜ {(A,B),(B,C),(C,A)}\n" ++
  "Fm : K ⟶ X×X ≜ {(0,0)}⊤(K,X)⟨𝟙,R₀⟩ ∪ ({(1,1)}⊤(K,X)⟨𝟙,R₁⟩) ∪ ({(2,2)}⊤(K,X)⟨𝟙,R₂⟩)\n" ++
  "pF : K ⟶ (X×X)×(X×X) ≜ p(Fm)\np₀ : X×X ⟶ X×X ≜ p(R₀)\np₁ : X×X ⟶ X×X ≜ p(R₁)\np₂ : X×X ⟶ X×X ≜ p(R₂)\n")

#guard let o := ok foldLaw
  [((0 : Int64), "p₀"), (1, "p₁"), (2, "p₂")].all fun (k, n) =>
    match get o "pF" .long (.prod XX XX), get o n XX XX with
    | some F, some R =>
      let f := (F.toList.filter (·.1 == k)).map (·.2)
      !R.toList.isEmpty && f.all R.toList.contains && R.toList.all f.contains
    | _, _ => false

/-- A lifted fold whose step has closed parts (§e, cost of the keyed fold): `G`, `∼R ∩ G` (a complement, so
    `⊤`), `dom(R)`, `π₂⟨π₁,π₁⟩`, each keyed on the pairs a round meets; at every key the fibre is the fold of
    the fibre. -/
def foldClosed : Except Err Out := runText ("obj X = {A,B,C}\nobj K = 0…2\nobj L = 5…6\n" ++
  "ℓ : 1 ⟶ [L] ≜ Λ(⊤(1,L))\nG : X ⟶ X ≜ {(A,B),(C,C)}\n" ++
  "p(R : X ⟶ X) : X×X ⟶ X×X ≜ ran(ℓ⦇ran⟨𝟙,𝟙⟩, π₂(𝟙×G) ∪ (π₂(𝟙×(∼R ∩ G))) ∪ (π₂(𝟙×dom(R))) ∪ (π₂⟨π₁,π₁⟩)⦈)\n" ++
  "R₀ : X ⟶ X ≜ {(A,B)}\nR₁ : X ⟶ X ≜ {(A,B),(B,C)}\nR₂ : X ⟶ X ≜ {(A,B),(B,C),(C,A)}\n" ++
  "Fm : K ⟶ X×X ≜ {(0,0)}⊤(K,X)⟨𝟙,R₀⟩ ∪ ({(1,1)}⊤(K,X)⟨𝟙,R₁⟩) ∪ ({(2,2)}⊤(K,X)⟨𝟙,R₂⟩)\n" ++
  "pF : K ⟶ (X×X)×(X×X) ≜ p(Fm)\np₀ : X×X ⟶ X×X ≜ p(R₀)\np₁ : X×X ⟶ X×X ≜ p(R₁)\np₂ : X×X ⟶ X×X ≜ p(R₂)\n")

#guard let o := ok foldClosed
  [((0 : Int64), "p₀"), (1, "p₁"), (2, "p₂")].all fun (k, n) =>
    match get o "pF" .long (.prod XX XX), get o n XX XX with
    | some F, some R =>
      let f := (F.toList.filter (·.1 == k)).map (·.2)
      !R.toList.isEmpty && f.all R.toList.contains && R.toList.all f.contains
    | _, _ => false

/-- Object variables (§e): `uq : α ⟶ β` at `X ⟶ N` and at `N ⟶ X` against the ground copies `uX`, `uN`; and
    `d : α ⟶ α` given `Fm : K ⟶ X×X`, which `α ⟶ α` reads as a family, against `d` of each fibre. -/
def objVars : Except Err Out := runText ("obj X = {A,B,C}\nobj N = {x,y,z}\nobj K = 0…2\n" ++
  "uq(R : α ⟶ β) : α ⟶ β ≜ R ∩ (R°\\𝟙)\nuX(R : X ⟶ N) : X ⟶ N ≜ R ∩ (R°\\𝟙)\n" ++
  "uN(R : N ⟶ X) : N ⟶ X ≜ R ∩ (R°\\𝟙)\nR₁ : X ⟶ N ≜ {(A,x),(A,y),(B,z)}\nR₂ : N ⟶ X ≜ {(x,A),(y,B),(y,C),(z,C)}\n" ++
  "a₁ : X ⟶ N ≜ uq(R₁)\nb₁ : X ⟶ N ≜ uX(R₁)\na₂ : N ⟶ X ≜ uq(R₂)\nb₂ : N ⟶ X ≜ uN(R₂)\n" ++
  "d(R : α ⟶ α) : α ⟶ α ≜ R ∩ (R°\\𝟙)\nF₀ : X ⟶ X ≜ {(A,B),(A,C)}\nF₁ : X ⟶ X ≜ {(A,B),(B,C)}\n" ++
  "F₂ : X ⟶ X ≜ {(A,A),(B,A),(B,B),(C,A)}\n" ++
  "Fm : K ⟶ X×X ≜ {(0,0)}⊤(K,X)⟨𝟙,F₀⟩ ∪ ({(1,1)}⊤(K,X)⟨𝟙,F₁⟩) ∪ ({(2,2)}⊤(K,X)⟨𝟙,F₂⟩)\n" ++
  "dF : K ⟶ X×X ≜ d(Fm)\nd₀ : X ⟶ X ≜ d(F₀)\nd₁ : X ⟶ X ≜ d(F₁)\nd₂ : X ⟶ X ≜ d(F₂)\n")

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
#guard (ok twoIdx).prints == [
  "s₀ × {(0, 0)} k(∋, ζ ∋) = {(((A, A) (B, B) (C, A), 0), (A, A)), (((A, A) (B, B) (C, A), 0), (B, B)), " ++
    "(((A, A) (B, B) (C, A), 0), (C, A))}",
  "s₀ × {(1, 1)} k(∋, ζ ∋) = {(((A, A) (B, B) (C, A), 1), (A, A)), (((A, A) (B, B) (C, A), 1), (B, B))}"]

-- at `S₀`, `∼S₀` gives `A` the values `B C`, `B` the values `A C`, `C` the values `B C`: the least of each
#guard (ok orders).prints == [
  "s₀ lf(Y(∋), Of) = {((A, A) (B, B) (C, A), (A, B)), ((A, A) (B, B) (C, A), (B, A)), " ++
    "((A, A) (B, B) (C, A), (C, B))}",
  "s₀ tf(Y(∋), Of) = {((A, A) (B, B) (C, A), (A, [B])), ((A, A) (B, B) (C, A), (B, [A])), " ++
    "((A, A) (B, B) (C, A), (C, [B]))}"]

#guard given.isOk && table.isOk && cycle.isOk
-- the file's own `check plan = …` holds and it prints nothing; `plan` printed here is the move list below
#guard (ok given).prints == []
#guard (ok (runExt Programs.blocks "print plan\n")).prints == ["plan = {(0, (C, C)), (1, (B, C)), (2, (A, B))}"]
#guard moves (ok given) == some [(2, 2), (1, 2), (0, 1)]
#guard moves (ok table) == some [(1, 2), (0, 1)]
#guard moves (ok cycle) == some []

/-! The elaborated definitions, as sets, on the reachable states. -/

/-- The definition `n` at `St ⟶ B` holds the rows `xs`, whatever their order and multiplicity. -/
def rowsAre {B : Obj} [BEq B.El] (n : String) (xs : List (St.El × B.El)) : Bool :=
  match get (ok given) n St B with
  | some R => R.toList.all xs.contains && xs.all R.toList.contains
  | none => false

/-- The 13 states reachable from `S₀`. -/
def reach : List St.El := [[(0, 0), (1, 1), (2, 0)], [(0, 0), (1, 2), (2, 0)], [(0, 0), (1, 1), (2, 1)],
  [(0, 0), (1, 1), (2, 2)], [(0, 2), (1, 1), (2, 1)], [(0, 1), (1, 1), (2, 2)], [(0, 2), (1, 1), (2, 2)],
  [(0, 0), (1, 0), (2, 2)], [(0, 0), (1, 2), (2, 2)], [(0, 1), (1, 1), (2, 0)], [(0, 2), (1, 0), (2, 2)],
  [(0, 0), (1, 0), (2, 1)], [(0, 1), (1, 2), (2, 2)]]

#guard rowsAre (B := St) "Q" (reach.map fun s => (s, s))
#guard rowsAre (B := XX) "qR" [([(0, 0), (1, 1), (2, 0)], 2, 0), ([(0, 0), (1, 2), (2, 0)], 1, 2),
  ([(0, 0), (1, 2), (2, 0)], 2, 0), ([(0, 0), (1, 1), (2, 1)], 2, 1), ([(0, 2), (1, 1), (2, 1)], 0, 2),
  ([(0, 2), (1, 1), (2, 1)], 2, 1), ([(0, 1), (1, 1), (2, 2)], 0, 1), ([(0, 2), (1, 1), (2, 2)], 0, 2),
  ([(0, 0), (1, 0), (2, 2)], 1, 0), ([(0, 0), (1, 2), (2, 2)], 1, 2), ([(0, 1), (1, 1), (2, 0)], 0, 1),
  ([(0, 1), (1, 1), (2, 0)], 2, 0), ([(0, 2), (1, 0), (2, 2)], 0, 2), ([(0, 2), (1, 0), (2, 2)], 1, 0),
  ([(0, 0), (1, 0), (2, 1)], 1, 0), ([(0, 0), (1, 0), (2, 1)], 2, 1), ([(0, 1), (1, 2), (2, 2)], 0, 1),
  ([(0, 1), (1, 2), (2, 2)], 1, 2)]
#guard rowsAre (B := St) "qh" [([(0, 1), (1, 2), (2, 2)], [(0, 1), (1, 2), (2, 2)])]

/-! One front-end error of each class, at its line. -/

def errAt (src : String) (line : Nat) (what : String) : Bool :=
  match runText src with
  | .error e => e.pos.line == line && (e.msg.splitOn what).length > 1
  | .ok _ => false

-- unknown name
#guard errAt "obj X = {A,B,C}\nf : X ⟶ X ≜ {(A,B)}\ng ≜ fh\n" 3 "unknown name 'h'"
-- type mismatch
#guard errAt "obj X = {A,B,C}\nobj N = 0…3\na : X ⟶ X ≜ {(A,B)}\nb : N ⟶ N ≜ {(1,2)}\nf ≜ ab\n" 5
  "found N, expected X"
-- a family given where the row is not liftable
#guard errAt "obj X = {A,B,C}\nobj St = 𝒫(X×X)\nL(S : X ⟶ X) : X ⟶ X ≜ ⦇S,S⦈\nf : St ⟶ X×X ≜ L(∋)\n" 3
  "not liftable"
-- a term that needs a universe its object does not have
#guard errAt "obj X = {A,B,C}\nobj St = 𝒫(X×X)\nprint ⊤(St,X)\n" 3 "has no universe"
-- a definition or parameter taking a builtin's name, or a name already defined or declared
#guard errAt "obj B = 0…1\nq : α×β ⟶ α ≜ π₁\nπ₂ ≜ π₁π₁\n" 3 "`π₂` is a builtin"
#guard errAt "obj B = 0…1\nf(S : B ⟶ B, E : B ⟶ B) : B ⟶ B ≜ S ∩ E\n" 2 "`E` is a builtin"
#guard errAt "obj B = 0…1\nK : α×β ⟶ α ≜ π₁\nq : α×β ⟶ α ≜ K\nK ≜ π₂\n" 4 "`K` is already defined at line 2"
#guard errAt "obj B = 0…1\nB ≜ π₁\n" 2 "`B` is already defined at line 1"
-- an object variable met at two objects, in one parameter's type or across two; a defined name is no variable
#guard errAt "obj X = {A,B,C}\nobj N = 0…3\nf(R : α ⟶ α) : α ⟶ α ≜ R\ng ≜ f({(A,1)})\n" 4
  "`α` in the type of 'R' is both X and N"
#guard errAt "obj X = {A,B,C}\nobj N = 0…3\nh(R : α ⟶ X, S : α ⟶ X) : α ⟶ X ≜ R\ng ≜ h({(A,B)},{(1,B)})\n" 4
  "`α` in the type of 'S' is both X and N"
#guard errAt "obj X = {A,B,C}\nπ : X ⟶ X ≜ 𝟙(X)\nf(R : π ⟶ π) ≜ R\n" 3 "expected an object, found 'π'"
-- a `where` item taking a defined name, a parameter's, an earlier item's or a builtin's; an item used outside
#guard errAt "obj B = 0…1\nK : α×β ⟶ α ≜ π₁\nf ≜ a where a ≜ π₂, K ≜ π₁\n" 3 "`K` is already defined at line 2"
#guard errAt "obj B = 0…1\nf(S : B ⟶ B) : B ⟶ B ≜ a where a ≜ S, S ≜ π₁\n" 2 "`S` is already a parameter of `f`"
#guard errAt "obj B = 0…1\nf : α×β ⟶ β ≜ a where a ≜ π₂, a ≜ π₁\n" 2 "`a` is already an item"
#guard errAt "obj B = 0…1\nf : α×β ⟶ β ≜ a where a ≜ π₂, π₁ ≜ a\n" 2 "`π₁` is a builtin"
#guard errAt "obj B = 0…1\nf : α×β ⟶ β ≜ a where a ≜ π₂\ng ≜ a\n" 3 "unknown name 'a'"

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
  "(∼R)°", "∼R S", "{((A, B), A), ((B, A), B)}", "{(A, (B, (A, B)))}"].all trip

#guard ["inits", "tails", "cat", "cat°", "zip", "snoc", "snoc°", "init", "concat", "perm", "setify", "bagify",
  "subseq", "tic", "ordered(R)", "sort(R)", "thinL(R)", "merge(R)", "loop(R)", "R inits concat", "⟨R, S⟩ merge(p)"].all trip

/-! The list builtins of §b on arrays built by `Λ` and `cons`, each value as `Algebra.lean`'s guard of the op
    states it: `x` is `a ↦ [3 1 2]`, `b ↦ [1 5]`; `y` is `a ↦ [7]`, `b ↦ [8 9]`; `z` is `a ↦ [3 3 1 2]`. -/
def lists : Except Err Out := runText ("obj N = 0…9\nobj K = {a,b}\n" ++
  "x : K ⟶ [N] ≜ ⟨{(a,3),(b,1)}, Λ({(a,1),(a,2),(b,5)})⟩cons\ny : K ⟶ [N] ≜ Λ({(a,7),(b,8),(b,9)})\n" ++
  "z : K ⟶ [N] ≜ ⟨{(a,3)}, x⟩cons\n" ++
  "print x inits\nprint x tails\nprint ⟨x,y⟩cat\nprint x cat°\nprint ⟨x,y⟩zip\nprint ⟨x,{(a,4),(b,6)}⟩snoc\n" ++
  "print x snoc°\nprint x init\nprint x inits concat\nprint y perm\nprint z setify\nprint z bagify\n" ++
  "print x ordered(≤)\nprint x sort(≤)\nprint y subseq\nprint x thinL(≤)\n" ++
  "print ⟨Λ({(a,1),(a,5)}),Λ({(a,2),(a,3)})⟩merge(≤)\nprint ⟨{(a,0),(b,1)},x⟩loop(plus)\n" ++
  "print ⟨{(a,5)},Λ({(a,1),(a,2)})⟩tic\n")

-- `thinL(≤)` runs the one-pass thinning: each element bumped into the thinned rest keeps the lower of the two
#guard (ok lists).prints == [
  "x inits = {(a, [] [3] [3 1] [3 1 2]), (b, [] [1] [1 5])}",
  "x tails = {(a, [3 1 2] [1 2] [2] []), (b, [1 5] [5] [])}",
  "⟨x, y⟩ cat = {(a, 3 1 2 7), (b, 1 5 8 9)}",
  "x cat° = {(a, ([], 3 1 2)), (a, ([3], 1 2)), (a, (3 1, [2])), (a, (3 1 2, [])), " ++
    "(b, ([], 1 5)), (b, ([1], [5])), (b, (1 5, []))}",
  "⟨x, y⟩ zip = {(a, [(3, 7)]), (b, (1, 8) (5, 9))}",
  "⟨x, {(a, 4), (b, 6)}⟩ snoc = {(a, 3 1 2 4), (b, 1 5 6)}",
  "x snoc° = {(a, (3 1, 2)), (b, ([1], 5))}",
  "x init = {(a, 3 1), (b, [1])}",
  "x inits concat = {(a, 3 3 1 3 1 2), (b, 1 1 5)}",
  "y perm = {(a, [7]), (b, 8 9), (b, 9 8)}",
  "z setify = {(a, 1 2 3)}",
  "z bagify = {(a, 1 2 3 3)}",
  "x ordered(≤) = {(b, 1 5)}",
  "x sort(≤) = {(a, 1 2 3), (b, 1 5)}",
  "y subseq = {(a, []), (a, [7]), (b, []), (b, [8]), (b, 8 9), (b, [9])}",
  "x thinL(≤) = {(a, [1]), (b, [1])}",
  "⟨Λ({(a, 1), (a, 5)}), Λ({(a, 2), (a, 3)})⟩ merge(≤) = {(a, 1 2 3 5)}",
  "⟨{(a, 0), (b, 1)}, x⟩ loop(plus) = {(a, 6), (b, 7)}",
  "⟨{(a, 5)}, Λ({(a, 1), (a, 2)})⟩ tic = {(a, [5] [5 1] [5 1 2])}"]

/-! `at(i)`, positions from `0`, on the arrays `x` above: `at(0) = head`, `tail at(i) = at(i+1)`, and a position
    past every array's end the empty relation. -/
#guard ["at(0)", "at(12)", "R at(2) S"].all trip
def ats : Except Err Out := runText ("obj N = 0…9\nobj K = {a,b}\n" ++
  "x : K ⟶ [N] ≜ ⟨{(a,3),(b,1)}, Λ({(a,1),(a,2),(b,5)})⟩cons\n" ++
  "print x at(0)\nprint x at(1)\nprint x at(2)\nprint x at(3)\n" ++
  "check x at(0) = x head\ncheck x tail at(0) = x at(1)\ncheck x tail at(1) = x at(2)\n" ++
  "check x tail at(2) = x at(3)\ncheck x at(3) = 𝟘\n")
#guard (ok ats).prints == ["x at(0) = {(a, 3), (b, 1)}", "x at(1) = {(a, 1), (b, 5)}", "x at(2) = {(a, 2)}",
  "x at(3) = {}"]
#guard match runText "obj N = 0…9\nf : [N] ⟶ N ≜ at(x)\n" with
  | .error e => e.msg == "at( ) takes a position, a number from 0, found 'x'" | .ok _ => false
#guard match runText "obj N = 0…9\nf : [N] ⟶ N ≜ at(-1)\n" with
  | .error e => e.msg == "at( ) takes a position from 0 that fits a long, found -1" | .ok _ => false

/-- A list builtin in a lifted body takes the closed row (§e): at each key of a two-key family the fibre of the
    lifted body is the body on the fibre. -/
def listsLifted : Except Err Out := runText ("obj N = 0…9\nobj K = {a,b}\nobj J = {i,j}\n" ++
  "R₀ : K ⟶ N ≜ {(a,3),(a,1)}\nR₁ : K ⟶ N ≜ {(a,2),(b,5),(b,1)}\n" ++
  "Fm : J ⟶ K×N ≜ {(i,i)}⊤(J,K)⟨𝟙,R₀⟩ ∪ ({(j,j)}⊤(J,K)⟨𝟙,R₁⟩)\n" ++
  "f(S : K ⟶ N) : K ⟶ [[N]] ≜ ⟨S,Λ(S)⟩cons inits ∪ (Λ(S)cat°π₁ tails)\nfF : J ⟶ K×[[N]] ≜ f(Fm)\n" ++
  "check {(i,i)}fF = {(i,i)}⊤(J,K)⟨𝟙,f(R₀)⟩\ncheck {(j,j)}fF = {(j,j)}⊤(J,K)⟨𝟙,f(R₁)⟩\n")

#guard listsLifted.isOk

/-- Orders on demand (§a): each operator runs its order on the pairs it compares, here `R ≜ length ≤ length°` on
    `[N]`, which has no universe; a closed order as before; and `∼R`, tested as the complement of `R`'s test. -/
def onDemand : Except Err Out := runText ("obj N = 0…9\nobj K = {a,b}\n" ++
  "L : K ⟶ [[N]] ≜ {(a,[1 2] [3] [8]),(b,[5] [4 6 7] [9])}\nG : K ⟶ [[N]] ≜ Λ(L∋)\n" ++
  "R : [α] ⟶ [β] ≜ length ≤(N,N) length°\np : [α] ⟶ [α] ≜ dom(length{(1,1)})\n" ++
  "print G est(R)\nprint G thin(R)\nprint L filter(p)\nprint L takewhile(p)\n" ++
  "print {(a,[3] [1 2]),(b,[1 2] [3])} ordered(R)\nprint L sort(R)\nprint L thinL(R)\n" ++
  "print ⟨L sort(R),{(a,[[1 2]]),(b,[[5]])}⟩merge(R)\nprint Λ({(a,3),(a,1),(b,5)})est(≤)\nprint G est(∼R)\n")

#guard (ok onDemand).prints == [
  "G est(R) = {(a, [3]), (a, [8]), (b, [5]), (b, [9])}",
  "G thin(R) = {(a, [3] [8]), (b, [5] [9])}",
  "L filter(p) = {(a, [3] [8]), (b, [5] [9])}",
  "L takewhile(p) = {(a, []), (b, [[5]])}",
  "{(a, [3] [1 2]), (b, [1 2] [3])} ordered(R) = {(a, [3] [1 2])}",
  "L sort(R) = {(a, [3] [8] [1 2]), (a, [8] [3] [1 2]), (b, [5] [9] [4 6 7]), (b, [9] [5] [4 6 7])}",
  "L thinL(R) = {(a, [[3]]), (a, [[8]]), (b, [[5]]), (b, [[9]])}",
  "⟨L sort(R), {(a, [[1 2]]), (b, [[5]])}⟩ merge(R) = {(a, [3] [8] [1 2] [1 2]), (a, [8] [3] [1 2] [1 2]), " ++
    "(b, [5] [9] [5] [4 6 7]), (b, [9] [5] [5] [4 6 7])}",
  "Λ({(a, 3), (a, 1), (b, 5)}) est(≤) = {(a, 1), (b, 5)}",
  "G est(∼R) = {(a, 1 2), (b, 4 6 7)}"]
-- refused: an order with a leaf that reads its argument whole, so neither side of its composition is tested
#guard errAt ("obj N = 0…9\nobj K = {a,b}\nL : K ⟶ [[N]] ≜ {(a,[1 2] [3])}\n" ++
  "S : [N] ⟶ [α] ≜ ran(𝟙([N])) length ≤(N,N) length°\nprint L sort(S)\n") 5
  "⊤'s target: [N] has no universe"

/-! The kernel's value verbs of §b on pairs of numbers, each `Alg.arith` with its opcode: a result outside the
    declared object has no row (`minus` below `0`, as `succ` at the top), nor a zero divisor. -/

def arith : Except Err Out := runText ("obj N = 0…20\n" ++
  "w : N×N ⟶ N×N ≜ {((7,2),(7,2)),((2,7),(2,7)),((7,0),(7,0)),((3,5),(3,5))}\n" ++
  "print w plus\nprint w times\nprint w minus\nprint w div\nprint w mod\nprint w max\nprint w min\n" ++
  "D : N×N ⟶ N×N ≜ dom(𝟙(N×N) div)\ncheck D⟨⟨π₂,div⟩times,mod⟩plus = Dπ₁\ncheck D⟨mod,π₂⟩ = D⟨mod,π₂⟩(𝟙 ∩ (π₁ < π₂°))\n")

-- `a = b·div + mod` and `mod < b` on every pair of `N` with a divisor other than `0`
#guard arith.isOk
#guard (ok arith).prints == [
  "w plus = {((2, 7), 9), ((3, 5), 8), ((7, 0), 7), ((7, 2), 9)}",
  "w times = {((2, 7), 14), ((3, 5), 15), ((7, 0), 0), ((7, 2), 14)}",
  "w minus = {((7, 0), 7), ((7, 2), 5)}",
  "w div = {((2, 7), 0), ((3, 5), 0), ((7, 2), 3)}",
  "w mod = {((2, 7), 2), ((3, 5), 3), ((7, 2), 1)}",
  "w max = {((2, 7), 7), ((3, 5), 5), ((7, 0), 7), ((7, 2), 7)}",
  "w min = {((2, 7), 2), ((3, 5), 3), ((7, 0), 0), ((7, 2), 2)}"]

#guard ["plus", "times", "minus", "div", "mod", "max", "min", "⟨R, S⟩ times", "R mod°"].all trip

/-- A value verb in a lifted body takes the closed row (§e): at each key the fibre is the body on the fibre. -/
def arithLifted : Except Err Out := runText ("obj N = 0…9\nobj K = {a,b}\nobj J = {i,j}\n" ++
  "R₀ : K ⟶ N ≜ {(a,3),(b,1)}\nR₁ : K ⟶ N ≜ {(a,2),(b,5),(b,1)}\n" ++
  "Fm : J ⟶ K×N ≜ {(i,i)}⊤(J,K)⟨𝟙,R₀⟩ ∪ ({(j,j)}⊤(J,K)⟨𝟙,R₁⟩)\n" ++
  "f(S : K ⟶ N) : K ⟶ N ≜ ⟨S,S⟩times ∪ (⟨S succ,S⟩mod)\nfF : J ⟶ K×N ≜ f(Fm)\n" ++
  "check {(i,i)}fF = {(i,i)}⊤(J,K)⟨𝟙,f(R₀)⟩\ncheck {(j,j)}fF = {(j,j)}⊤(J,K)⟨𝟙,f(R₁)⟩\nprint f(R₀)\n")

#guard arithLifted.isOk
#guard (ok arithLifted).prints == ["f(R₀) = {(a, 1), (a, 9), (b, 0), (b, 1)}"]

/-- B&dM's digits of a number (`val_converse_eq`): `op°`, the converse of `op(n,d) = 10n+d` on a digit `d`,
    taken from `x` once a round until it reaches `0`, each digit put on the front of the list. The rounds `K`
    hold no number of `N`, so a literal's words name one object (§c). -/
def digits : Except Err Out := runText ("obj N = 0…199\nobj K = 200…203\n" ++
  "ten : N ⟶ N ≜ ⊤(N,N){(10,10)}\ndg : N ⟶ N ≜ dom(<{(10,10)})\nop : N×N ⟶ N ≜ ⟨⟨π₁,π₁ ten⟩times,π₂ dg⟩plus\n" ++
  "x : N ⟶ N ≜ {(107,107)}\nr : N ⟶ [K] ≜ Λ(x⊤(N,K))\nnz : N ⟶ N ≜ 𝟙(N) − {(0,0)}\n" ++
  "step : N×[N] ⟶ N×[N] ≜ ⟨π₁{(0,0)},π₂⟩ ∪ ⟨π₁ nz op° π₁,⟨π₁ nz op° π₂,π₂⟩cons⟩\n" ++
  "ds : N ⟶ [N] ≜ r⦇ran(x⟨𝟙,nil⟩),π₂ step⦈π₂\nprint ds\n")

#guard (ok digits).prints == ["ds = {(107, 1 0 7)}"]

-- a prelude definition given a family through a typed parameter: the lifted body reaches `perm`, closed on `[N]`
#guard errAt "obj N = 0…3\nobj St = 𝒫(N×N)\nf(S : N ⟶ N) : [N] ⟶ [N] ≜ sort(S)\ng : St ⟶ [N]×[N] ≜ f(∋)\n" 3
  "a closed term in a lifted body: [N] has no universe"

-- a nested literal (§c): each leaf position its own object, the side their product
#guard match runText "obj X = {A,B}\nobj N = 0…1\nL : X×N ⟶ N×X ≜ {((A,0),(1,B)),((B,1),(0,A))}\nprint L\n" with
  | .ok o => o.prints == ["L = {((A, 0), (1, B)), ((B, 1), (0, A))}"] &&
    (get o "L" (.prod .long .long) (.prod .long .long)).map (·.toList) == some [((0, 0), (1, 1)), ((1, 1), (0, 0))]
  | .error _ => false
#guard errAt "obj X = {A,B}\nL ≜ {((A,B),A),(A,B)}\n" 2 "nest alike"

/-! Array literals (§c): two or more items juxtaposed, or `[…]`; an element position is one object over the
    elements of all rows' arrays there, at any depth and on either side; printed as it is read. -/

/-- The value printed by each `print` of `src`, after its ` = `. -/
def printed (src : String) : List String := (ok (runText src)).prints.map fun s => (s.splitOn " = ").getLastD ""

/-! Declared types (§e). -/

-- a body that is not the declared type; a definition with none, told the type it has
#guard errAt "obj X = {A,B}\nobj N = 0…1\nf : X ⟶ N ≜ 𝟙(X)\n" 3 "`f` is declared X ⟶ N, but its body is X ⟶ X"
#guard errAt "obj X = {A,B}\nf ≜ 𝟙(X)\n" 2 "`f` has no type; it is f : X ⟶ X"
#guard errAt "obj X = {A,B}\nf(R : X ⟶ X) ≜ R°\n" 2 "`f` has no type; it is f(R : X ⟶ X) : X ⟶ X"
-- one generic definition at two objects in one program: its variables instantiated at each use
#guard printed ("obj X = {A,B}\nobj N = 0…1\nsw : α×β ⟶ β×α ≜ ⟨π₂,π₁⟩\nprint {((A,0),(A,0))}sw\n" ++
  "print {((1,B),(1,B))}sw\n") == ["{((A, 0), (0, A))}", "{((1, B), (B, 1))}"]
-- the declared type determines an object the body leaves open: `nil`'s source and element
#guard printed "obj N = 0…3\ne : 1 ⟶ [N] ≜ nil\nprint e\n" == ["{(∗, [])}"]
-- `typesOf` prints each definition's head as it is declared
def heads : List String := ["f : X ⟶ X", "g(R : α ⟶ β) : β ⟶ α", "_≼_(R : α ⟶ β, S : β ⟶ γ) : α ⟶ γ"]
#guard match typesOf (some ("obj X = {A,B}\n" ++
    String.join ((heads.zip ["𝟙", "R°", "R S"]).map fun (h, b) => s!"{h} ≜ {b}\n"))) with
  | .ok ts => ts == heads
  | .error _ => false
-- a `where` item takes no type of its own, nor does a test
#guard printed "obj B = 0…1\nf : B×B ⟶ B ≜ a where a ≜ π₂\nprint {((0,1),(0,1))}f\n" == ["{((0, 1), 1)}"]
#guard errAt "obj B = 0…1\nf : B×B ⟶ B ≜ a where a : B×B ⟶ B ≜ π₂\n" 2
  "the `where` item `a` takes no type: make it a top-level definition to give it one"
#guard errAt "obj X = {A,B}\nh(S : X ⟶ X) : X ⟶ X ≜ 𝟙 ⊑ S\n" 2 "the test `h` has no type of its own"

def arrs : String :="obj N = -3…9\nobj K = {a,b}\n" ++
  "x : 1 ⟶ [N] ≜ {(∗,3 1 2)}\nxc : 1 ⟶ [N] ≜ ⟨{(∗,3)}, ⟨{(∗,1)}, ⟨{(∗,2)}, nil⟩cons⟩cons⟩cons\ncheck x = xc\ncheck {(∗,[3 1 2])} = xc\n" ++
  "check {(∗,[1])} = ⟨{(∗,1)},nil⟩cons\ncheck {(∗,[1] [2 3])} = ⟨{(∗,[1])},⟨{(∗,2 3)},nil⟩cons⟩cons\n" ++
  "check {(∗,(1,2) (3,4))} = ⟨{(∗,(1,2))},⟨{(∗,(3,4))},nil⟩cons⟩cons\n" ++
  "print x\nprint {(a b,1)}\nprint {(∗,(1,2) (3,4))}\nprint {(∗,[1] [2 3])}\nprint {((a,1 2),[3])}\n" ++
  "print {(a,-1 2),(b,[])}\nprint {(∗,[1 2] [])}\nprint {(3 1 2,a b)}\nprint {(∗,[[]] [[1]])}\n"

#guard printed arrs == ["{(∗, 3 1 2)}", "{(a b, 1)}", "{(∗, (1, 2) (3, 4))}", "{(∗, [1] [2 3])}",
  "{((a, 1 2), [3])}", "{(a, -1 2), (b, [])}", "{(∗, [1 2] [])}", "{(3 1 2, a b)}", "{(∗, [[]] [[1]])}"]
#guard match runText arrs with
  | .ok o => (get o "x" .long (.arr .long)).map (·.toList) == some [((0 : Int64), [(3 : Int64), 1, 2])]
  | .error _ => false
-- a printed literal reads back as itself
#guard ["{(∗, 3 1 2)}", "{(∗, [1] [2 3])}", "{((a, 1 2), [3])}", "{(b, [])}", "{(∗, (1, 2) (3, 4))}"].all trip
-- an element position whose arrays are all empty, a word in no object, rows nesting differently, a comma
def arrE : String := "obj N = 0…9\n"
def emptyErr : String := "the object of [] cannot be read off an empty array: write nil(A,[O])"
/-- `src` fails at `line`, `col` with `what` in the message. -/
def errAtCol (src : String) (line col : Nat) (what : String) : Bool :=
  match runText src with
  | .error e => e.pos.line == line && e.pos.col == col && (e.msg.splitOn what).length > 1
  | .ok _ => false
-- nothing determines the object: the error at the literal
#guard errAtCol (arrE ++ "print {(∗,[])}\n") 2 7 emptyErr
#guard errAtCol (arrE ++ "print {(∗,[[]] [])}\n") 2 7 emptyErr
#guard errAtCol (arrE ++ "print {(∗,[])} ∪ {(∗,[])}\n") 2 7 emptyErr
-- an untyped definition names the type its body has, the object left open a variable
#guard errAt (arrE ++ "e ≜ {(∗,[])}\n") 2 "`e` has no type; it is e : 1 ⟶ [α]"
-- the context determines it (§c): the other side of a check, the other operand, the declared type, the
-- composition, the pair
def arrCtx : String := arrE ++ "obj K = {a,b}\ne : 1 ⟶ [N] ≜ nil\nx : 1 ⟶ [N] ≜ {(∗,1 2)}\n" ++
  "check e = {(∗,[])}\ncheck {(∗,[])} = e\ncheck e ⊑ {(∗,[])}\n" ++
  "check x ∪ {(∗,[])} = {(∗,1 2),(∗,[])}\ncheck x ∩ {(∗,[])} = 𝟘(1,[N])\ncheck x − {(∗,[])} = x\n" ++
  "d : 1 ⟶ [N] ≜ {(∗,[])}\ncheck d = e\nnn : 1 ⟶ [[N]] ≜ {(∗,[[]])}\ncheck nn = ⟨e,nil⟩cons\n" ++
  "c : 1 ⟶ N ≜ {(∗,[])}{([],3),([1],4)}\ncheck c = {(∗,3)}\n" ++
  "check ⟨{(∗,[])},{(∗,a)}⟩ = ⟨e,{(∗,a)}⟩\ncheck {(∗,[] [3])} = ⟨e,⟨{(∗,[3])},nil⟩cons⟩cons\n" ++
  "print d\nprint nn\n"
#guard printed arrCtx == ["{(∗, [])}", "{(∗, [[]])}"]
-- words two objects hold: open too, fixed by the context, else the error at the literal
def twoObjs : String := "obj A = {a,b}\nobj B = {a,c}\n"
#guard printed (twoObjs ++ "x : A ⟶ B ≜ {(a,a)}\nprint x\n") == ["{(a, a)}"]
#guard errAtCol (twoObjs ++ "print {(a,c)}\n") 3 7 "the elements [a] are in [B, A]; write the literal after its object"
-- a wrong expectation is a failed check, not an object error
#guard errAt (arrE ++ "x : 1 ⟶ [N] ≜ {(∗,1 2)}\ncheck x = {(∗,[])}\n") 3 "check failed"
#guard errAt (arrE ++ "e ≜ {(∗,1 12)}\n") 2 "no declared object has the elements [1, 12]"
#guard errAt (arrE ++ "e ≜ {(∗,1 2),(∗,3)}\n") 2
  "the rows of a literal nest alike: found 3, expected the form of 1 2"
#guard errAt (arrE ++ "e ≜ {(∗,(1,2) 3)}\n") 2 "the rows of a literal nest alike: found 3, expected the form of (1, 2)"
#guard errAt (arrE ++ "e ≜ {(∗,[1,2])}\n") 2 "the elements of an array are separated by spaces, not ','"

/-! Signed numbers (§a, §c): a range `-3…3`, signed literal words, `succ ≤ <` and the value verbs on it, each
    against Lean's `Int` (`div` floors and `mod` takes the divisor's sign, as q's: `Int.fdiv`, `Int.fmod`); a print
    lists numbers by value. -/

def zs : List Int := (List.range 7).map fun k : Nat => (k : Int) - 3
def signed : Except Err Out := runText ("obj Z = -3…3\nobj K = {a,b}\n" ++
  "x : K ⟶ Z ≜ {(a,-1),(b,2),(a,-3)} -- a comment, after a signed literal\nprint x\nprint Λ(x)\n" ++
  "print x − {(a,-3)}\nprint {(-1,-1)}−{(2,2)}\ns : Z ⟶ Z ≜ 𝟙(Z) succ\nle : Z ⟶ Z ≜ 𝟙(Z) ≤\nlt : Z ⟶ Z ≜ 𝟙(Z) <\n" ++
  "W : Z×Z ⟶ Z×Z ≜ 𝟙(Z×Z)\npl : Z×Z ⟶ Z ≜ W plus\ntm : Z×Z ⟶ Z ≜ W times\nmi : Z×Z ⟶ Z ≜ W minus\n" ++
  "dv : Z×Z ⟶ Z ≜ W div\nmd : Z×Z ⟶ Z ≜ W mod\nmx : Z×Z ⟶ Z ≜ W max\nmn : Z×Z ⟶ Z ≜ W min\n")

def sameSet {α : Type} [BEq α] (a b : List α) : Bool := a.all b.contains && b.all a.contains
def ints (R : Rel .long .long) : List (Int × Int) := R.toList.map fun (a, b) => (a.toInt, b.toInt)

#guard signed.isOk
#guard (ok signed).prints == ["x = {(a, -3), (a, -1), (b, 2)}", "Λ(x) = {(a, -3 -1), (b, [2])}",
  "x − {(a, -3)} = {(a, -1), (b, 2)}", "{(-1, -1)} − {(2, 2)} = {(-1, -1)}"]
-- `succ` at `-1` gives `0`, at the top `3` nothing; `≤`, `<` the numeric order
#guard (get (ok signed) "s" .long .long).map ints == some ((zs.filter (· < 3)).map fun a => (a, a + 1))
#guard [("le", fun (a b : Int) => decide (a ≤ b)), ("lt", fun a b => decide (a < b))].all fun (n, f) =>
  match get (ok signed) n .long .long with
  | some R => sameSet (ints R) ((zs.flatMap fun a => zs.map (a, ·)).filter fun (a, b) => f a b)
  | none => false
-- each verb on every pair of `Z`: a row exactly where the result is in `Z` and the divisor is not `0`
#guard [("pl", fun (a b : Int) => some (a + b)), ("tm", fun a b => some (a * b)), ("mi", fun a b => some (a - b)),
    ("dv", fun a b => if b == 0 then none else some (a.fdiv b)),
    ("md", fun a b => if b == 0 then none else some (a.fmod b)),
    ("mx", fun a b => some (max a b)), ("mn", fun a b => some (min a b))].all fun (n, f) =>
  match get (ok signed) n (.prod .long .long) .long with
  | some R => sameSet (R.toList.map fun ((a, b), c) => ((a.toInt, b.toInt), c.toInt))
      ((zs.flatMap fun a => zs.map (a, ·)).filterMap fun (a, b) =>
        (f a b).bind fun c => if zs.contains c then some ((a, b), c) else none)
  | none => false
-- `-5…-1` is a range; `3…-3` is empty, refused at its last number; a word other than a number is no range bound
#guard match runText "obj Z = -5…-1\nprint 𝟙(Z) succ\n" with
  | .ok o => o.prints == ["𝟙(Z) succ = {(-5, -4), (-4, -3), (-3, -2), (-2, -1)}"]
  | .error _ => false
#guard match runText "obj X = {A}\nobj Z = 3…-3\n" with
  | .error e => e.pos.line == 2 && e.pos.col == 11 && e.msg == "the range 3…-3 is empty: -3 is below 3"
  | .ok _ => false
#guard errAt "obj Z = -3…3\nf ≜ {(-4,0)}\n" 2 "no declared object has the elements [-4]"
-- a `-` with no digit after it is no sign: `R -3` ends the term, `R −3` is a difference before no term
#guard errAt "obj Z = -3…3\nR : Z ⟶ Z ≜ 𝟙(Z)\nf ≜ R -3\n" 3 "expected the end of the line, found '-'"
#guard errAt "obj Z = -3…3\nR : Z ⟶ Z ≜ 𝟙(Z)\nf ≜ R −3\n" 3 "expected a term, found '3'"
#guard ["{(A, -1)}", "{((-1, B), -20)}", "R − S"].all trip

#guard [("R ∪ S R", "((R ∪ S) R)"), ("R S ∪ R", "((R S) ∪ R)"), ("R ∩ S ∪ R", "((R ∩ S) ∪ R)"),
  ("R ∪ S ∩ R", "((R ∪ S) ∩ R)"), ("∼R S", "(∼R S)"), ("R ∪ (S R)", "(R ∪ (S R))")].all fun (s, r) => reads s r

/-! The parser on each line of `Programs.blocks`: every composite and infix term in parentheses, as the note reads the
    formula (§c), not as the parser happens to print it. -/

def reading : Decl → Option (String × String)
  | .defn _ n _ (.rel e) _ => some (n, e.render 0 true)
  | .defn _ n _ (.test e f) _ => some (n, s!"{e.render 0 true} ⊑ {f.render 0 true}")
  | .print _ e => some ("print", e.render 0 true)
  | .check _ e f eq => some ("check", s!"{e.render 0 true} {if eq then "=" else "⊑"} {f.render 0 true}")
  | _ => none

-- a `where` item in place in the body and in the items after it (§c)
#guard match Parse.parse "obj B = 0…1\nf(S) ≜ b ∪ S where a ≜ π₁, b ≜ a π₂ S\n" with
  | .ok p => p.filterMap reading == [("f", "(((π₁ π₂) S) ∪ S)")]
  | .error _ => false

/-! Terms on an object with no universe (§a): a converse pushed to the leaves, a division tested on the pairs a
    meet supplies, `R×S` as `⟨π₁R,π₂S⟩`; and what is still refused. Expected values by hand. -/


def chs : String := "obj Ch = {a,b}\nobj N = 0…3\nx : 1 ⟶ [Ch] ≜ {(∗,a b)}\n" ++
  "y : 1 ⟶ [Ch] ≜ {(∗,a a b)}\nns : 1 ⟶ [N] ≜ {(∗,2 3)}\n" ++
  "ms : 1 ⟶ [N] ≜ {(∗,3 1 2)}\nks : 1 ⟶ [N] ≜ {(∗,3 1 1)}\n" ++
  "ok : α×[α] ⟶ α×[α] ≜ cor(≤/∋)\n"

-- the converse: `(RS)° = S°R°`, `∩`, a pair with one side's converse, `R°° = R`, a coreflexive, `cons° = uncons`
#guard printed (chs ++ "print x cons° (perm cons°)°\nprint x (perm ∩ perm)° cons°\nprint x ⟨cons°π₁, perm⟩°° π₂\n" ++
  "print x (dom(π₁{(a,a)}) cons)°\nprint x (dom(π₁{(b,b)}) cons)°\n") ==
  ["{(∗, a b), (∗, b a)}", "{(∗, (a, [b])), (∗, (b, [a]))}", "{(∗, a b), (∗, b a)}",
   "{(∗, (a, [b]))}", "{}"]
-- refused at a leaf whose converse does not run on demand: `π₁` in `⟨π₁,π₂⟩°`, `∋` in `∈`
#guard errAt (chs ++ "print x (cons° ⟨π₁,π₂⟩ cons)°\n") 9 "the converse of π₁ does not run on demand"
#guard errAt (chs ++ "print {(∗,a)} ∈\n") 9 "the converse of ∋ does not run on demand"
-- a division tested on the pairs: `R/S`, `R\S`, `frac`, `∼`, `−`, each beside a term run on demand
#guard printed (chs ++ "print ⟨{(∗,1)},ns⟩ok\nprint ⟨{(∗,3)},ns⟩ok\nprint ⟨{(∗,2)},ns⟩ok\n" ++
  "print ms (∋ ∩ (cons\\(π₁ ≤)))\nprint ks (subseq ∩ frac(∋,∋))\n" ++
  "print ⟨{(∗,3)},ns⟩(π₂ ∩ (π₁∼(≤/∋)))\nprint ⟨{(∗,1)},ns⟩(π₂ ∩ (π₁∼(≤/∋)))\nprint ⟨{(∗,3)},ns⟩(π₂ − (π₁(≤/∋)))\n") ==
  ["{(∗, (1, 2 3))}", "{}", "{(∗, (2, 2 3))}", "{(∗, 3)}", "{(∗, 3 1), (∗, 3 1 1)}",
   "{(∗, 2 3)}", "{}", "{(∗, 2 3)}"]
-- refused: a division with no term on demand to test it against, and a meet of two
#guard errAt (chs ++ "print {(∗,1)}(≤/∋)\n") 9 "R/S reads its operands whole"
#guard errAt (chs ++ "print {(∗,1)}((≤/∋) ∩ (≤/∋))\n") 9 "R/S reads its operands whole"
-- `R×S` on demand as `⟨π₁R,π₂S⟩`; closed, as before
#guard printed (chs ++ "print ⟨{(1,1)},⟨{(1,2)},Λ({(1,1)})⟩⟩(𝟙×π₁)plus\nprint y cons°(𝟙×perm)\n" ++
  "print ⟨x,{(∗,b)}⟩(perm×𝟙)\nprint {(1,1)}×{(2,3)}\n") ==
  ["{(1, 3)}", "{(∗, (a, a b)), (∗, (a, b a))}", "{(∗, (a b, b)), (∗, (b a, b))}", "{((1, 2), (1, 3))}"]
-- refused: an operand that does not run, named; the object printed as the program writes it, `[Ch]`
#guard errAt (chs ++ "print ⟨{(∗,a)},{(∗,b)}⟩(∈×𝟙)\n") 9 "the converse of ∋ does not run on demand"
#guard errAt (chs ++ "print ⟨{(∗,a)},{(∗,b)}⟩(∈×𝟙)\n") 9 "[Ch] has no universe"
-- `loop(F)` runs `F` on the pairs each round meets: a state that is an array (a copy, a reverse, the
-- subsequences), and a pair with an array (the copy with its length)
#guard printed (chs ++ "print x ⟨nil,𝟙⟩loop(snoc)\nprint y ⟨nil,𝟙⟩loop(⟨π₂,π₁⟩cons)\nprint x ⟨nil,𝟙⟩loop(snoc ∪ π₁)\n" ++
  "print x ⟨⟨nil,⊤{(0,0)}⟩,𝟙⟩loop(⟨⟨π₁π₁,π₂⟩snoc,π₁π₂ succ⟩)\n") ==
  ["{(∗, a b)}", "{(∗, b a a)}", "{(∗, []), (∗, [a]), (∗, a b), (∗, [b])}", "{(∗, (a b, 2))}"]
-- refused: an `F` that runs neither way, the leaf named
#guard errAt (chs ++ "print x ⟨nil,𝟙⟩loop(snoc ran(snoc))\n") 9 "ran( ) reads its argument whole: [Ch]×Ch has no universe"

/-! The prelude (§c): each definition moved there against the builtin it replaced (`Alg.perm`, `Alg.ordered`, and
    `sort(Q) = perm ordered(Q)`), on a repeated element, the empty array, two element objects and arrays of arrays;
    the converses; the declared infix operators; the errors. -/

def pre : Except Err Out := runText ("obj N = 0…9\nobj K = {a,b,c,d}\nobj Ch = {p,q}\n" ++
  "x : K ⟶ [N] ≜ {(a,3 1 2),(b,2 1 2),(c,[]),(d,[5])}\nle : N ⟶ N ≜ 𝟙(N) ≤\npm : K ⟶ [N] ≜ x perm\n" ++
  "od : K ⟶ [N] ≜ x ordered(≤)\nst : K ⟶ [N] ≜ x sort(≤)\ny : K ⟶ [Ch] ≜ {(a,p q p),(b,[])}\n" ++
  "py : K ⟶ [Ch] ≜ y perm\nz : K ⟶ [[N]] ≜ {(a,[1 2] [3] []),(b,[] [])}\npz : K ⟶ [[N]] ≜ z perm\n")

def same {A B : Obj} (R S : Rel A B) : Bool := R ⊑ S && S ⊑ R
def is {B : Obj} (o : Out) (n : String) (R : Rel .long B) : Bool := ((get o n .long B).map (same · R)).getD false

#guard let o := ok pre
  match get o "x" .long (.arr .long), get o "le" .long .long with
  | some X, some Le =>
    let U := (Alg.ran X).val; let P := Alg.perm U
    is o "pm" (X ≫ P) && is o "od" (X ≫ Alg.ordered Le U) && is o "st" (X ≫ P ≫ Alg.ordered Le (Alg.ran P).val)
  | _, _ => false
#guard let o := ok pre
  match get o "y" .long (.arr .long), get o "z" .long (.arr (.arr .long)) with
  | some Y, some Z => is o "py" (Y ≫ Alg.perm (Alg.ran Y).val) && is o "pz" (Z ≫ Alg.perm (Alg.ran Z).val)
  | _, _ => false

-- the converses: `perm° = perm` (the one rule kept for a definition), `ordered(Q)` a coreflexive, and
-- `sort(Q)° = ordered(Q)° perm°` from them
#guard printed ("obj N = 0…9\nx : 1 ⟶ [N] ≜ {(∗,1 2 3)}\nprint x perm°\nprint x ordered(≤)°\nprint x sort(≤)°\n" ++
  "print {(∗,3 1 2)} sort(≤)°\n") ==
  ["{(∗, 1 2 3), (∗, 1 3 2), (∗, 2 1 3), (∗, 2 3 1), (∗, 3 1 2), (∗, 3 2 1)}", "{(∗, 1 2 3)}",
   "{(∗, 1 2 3), (∗, 1 3 2), (∗, 2 1 3), (∗, 2 3 1), (∗, 3 1 2), (∗, 3 2 1)}", "{}"]

-- a declared infix operator: `R + S = ⟨R,S⟩plus`, the prelude's `⇒` and `⊕`, a program's own `_≼_`, each read at
-- the one level with `∩`, left to right
#guard printed ("obj N = 0…9\nw : N×N ⟶ N×N ≜ {((2,3),(2,3)),((4,1),(4,1))}\nprint w(π₁ + π₂)\n" ++
  "check w(π₁ + π₂) = w⟨π₁,π₂⟩plus\n_≼_(R : α ⟶ β, S : β ⟶ α) : α ⟶ β ≜ R ∩ S°\nprint {(1,1),(2,2)}(≤ ≼ ≤)\nprint {(1,1)}(≤ ≼ ≤ ∪ <)\nprint {(1,1)}(< ∪ 𝟙(N) ≼ ≤)\n" ++
  "print {(1,1)}(𝟙(N) ∩ {(1,2)} ⇒ <)\nprint {(1,1)}inl(N,N+N)(𝟙 ⊕ succ)\n") ==
  ["{((2, 3), 5), ((4, 1), 5)}", "{(1, 1), (2, 2)}",
   "{(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9)}", "{(1, 1)}",
   "{(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9)}", "{(1, inl 1)}"]
#guard ["R ⇒ S", "R ⊕ S", "R + S", "frac(R, S)", "∈", "perm", "ordered(R)", "sort(R)", "cor(R)"].all trip
-- `cor(R)`: the pairs of `R` as a coreflexive on `A×B`
#guard printed "obj N = 0…3\nprint {((1,2),(1,2)),((2,1),(2,1)),((3,3),(3,3))}cor(≤)\n" ==
  ["{((1, 2), (1, 2)), ((3, 3), (3, 3))}"]
#guard [("R ∩ S ⇒ R", "((R ∩ S) ⇒ R)"), ("R ⇒ S ∩ R", "((R ⇒ S) ∩ R)"), ("R S + R", "((R S) + R)"),
  ("R + S R", "((R + S) R)")].all fun (s, r) => reads s r
-- infix only: used before its arguments, alone, or declared with other than two parameters
#guard errAt "obj B = 0…1\nf ≜ ⇒(π₁,π₂)\n" 2 "`⇒` is an infix operator: write `R ⇒ S`, not `⇒(R, S)`"
#guard errAt "obj B = 0…1\nf ≜ π₁ ∪ ⇒\n" 2 "`⇒` is an infix operator: it stands between two terms, `R ⇒ S`"
#guard errAt "obj B = 0…1\n_≼_(R) ≜ R\n" 2 "the infix operator `≼` takes two parameters, `_≼_(R, S)`, found 1"
-- a prelude name taken again, as a definition, an infix operator's name or an object
#guard errAt "obj N = 0…9\nperm ≜ 𝟙(N)\n" 2 "`perm` is already defined in the prelude"
#guard errAt "obj N = 0…9\n⊕ ≜ 𝟙(N)\n" 2 "`⊕` is already defined in the prelude"
#guard errAt "obj N = 0…9\n_sort_(R,S) ≜ R ∩ S\n" 2 "`sort` is already defined in the prelude"
#guard errAt "obj 1 = {∗}\nobj N = 0…9\n" 1 "`1` is already defined in the prelude"
-- an error of the prelude's own text, and one raised in a prelude body at a use: the prelude's line, the use's
#guard match Parse.parseIn { cs := #[] } "    f ≜ g\n" >>= (runWith · "obj X = {A}\n") with
  | .error e => toString e == "in the prelude, line 1, col 9: unknown name 'g'"
  | .ok _ => false
#guard match Parse.parseIn { cs := #[] } "    f(R : α ⟶ β) : α ⟶ β ≜ R g\n" >>=
    (runWith · "obj X = {A}\nx : X ⟶ X ≜ {(A,A)}\ny : X ⟶ X ≜ f(x)\n") with
  | .error e => e.pos.line == 3 && e.msg == "in the prelude's `f` (its line 1): unknown name 'g'"
  | .ok _ => false

#guard Programs.blocks.filterMap reading == [
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
    ("r", "Λ((s₀ ⊤))"),
    ("L", "ran((r ⦇ran(⟨D, ((D ⊤) {(0, 0)})⟩), (π₂ ∪ (π₂ ⟨(π₁ B), (π₂ succ)⟩))⦈))"),
    ("Q", "ran((L(s₀, t) π₁))"),
    ("H", "(Q h(∋))"),
    ("C", "L(H, (Q t)°)"),
    ("W", "((C π₁)° (C π₂))"),
    ("δ", "(Λ(W) est(≤))"),
    ("K", "((Q c) dom((((Λ(⇝) δ) succ) ∩ (π₁ δ))))"),
    ("≼", "(((π₁ <) π₁°) ∪ ((π₁ π₁°) ∩ ((π₂ ≤) π₂°)))"),
    ("σ", "(Λ((K π₂)) est(≼))"),
    ("nx", "(⟨dom(σ), σ⟩ Λ(⇝))"),
    ("Z", "L(s₀, nx)"),
    ("ζ", "((Z π₂)° (Z π₁))"),
    ("plan", "(ζ σ)"),
    ("check", "plan = {(0, (C, C)), (1, (B, C)), (2, (A, B))}")]

/-! Fixed points `μX : φ`, `νX : φ`: printed as read, run against their rounds written out, and refused where the
    body is not monotonic in `X` or the rounds have no bound. -/

#guard ["νZ : R ∩ Z", "(μZ : 𝟙 ∪ (R Z)) S", "R° ∪ (νZ : R ∩ (S \\ (Z R)))", "⟨νZ : R ∩ Z, S⟩"].all trip
-- `R*`, the least `X` with `𝟙 ∪ RX ⊑ X`, against the closure written out
#guard (runText ("obj N = 0…4\nR : N ⟶ N ≜ {(0,1),(1,2),(2,3)}\nc : N ⟶ N ≜ μX : 𝟙 ∪ (R X)\n" ++
  "check c = {(0,0),(1,1),(2,2),(3,3),(4,4),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)}\n")).isOk
-- the points with an infinite `R`-path: the rounds from `𝟙` written out, which stop changing at the second
#guard (runText ("obj N = 0…5\nR : N ⟶ N ≜ {(0,1),(1,2),(2,0),(3,4)}\nv : N ⟶ N ≜ νX : 𝟙(N) ∩ dom(R X)\n" ++
  "x₁ : N ⟶ N ≜ 𝟙(N) ∩ dom(R 𝟙(N))\nx₂ : N ⟶ N ≜ 𝟙(N) ∩ dom(R x₁)\nx₃ : N ⟶ N ≜ 𝟙(N) ∩ dom(R x₂)\n" ++
  "check v = x₂\ncheck x₃ = x₂\ncheck v = {(0,0),(1,1),(2,2)}\n")).isOk
-- arc consistency on `y = x²` with both arcs, `x → y` by `sq` and `y → x` by `sq°`
#guard (runText ("obj V = {x,y}\nobj D = 0…9\nA : V ⟶ V ≜ {(x,y)}\nsq : D ⟶ D ≜ {(0,0),(1,1),(2,4),(3,9)}\n" ++
  "revise(A : α ⟶ α, C : β ⟶ β, X : α ⟶ β) : α ⟶ β ≜ A\\(X C)\ns : V ⟶ D ≜ ⊤(V,D)\n" ++
  "z : V ⟶ D ≜ νZ : s ∩ revise(A,sq,Z) ∩ revise(A°,sq°,Z)\n" ++
  "check z = {(x,0),(x,1),(x,2),(x,3),(y,0),(y,1),(y,4),(y,9)}\n")).isOk
-- `X` under an operator not monotonic in its argument, or in an antitone place; `ν` with no bound; `μ` on an array
#guard errAt "obj B = 0…1\nf : B ⟶ B ≜ νX : ⊤(B,B) ∩ (Λ(X)∋)\n" 2
  "νX: X occurs under Λ at 2:30; Λ is not monotonic in its argument, so the fixed point need not exist"
#guard errAt "obj B = 0…1\nr : B ⟶ B ≜ {(0,1)}\nf : B ⟶ B ≜ μX : r ∪ X\\r\n" 3
  "μX: X occurs in the left operand of \\ at 3:22 (antitone); X must occur only in monotonic positions"
#guard errAt "obj B = 0…1\nr : B ⟶ B ≜ {(0,1)}\nf : B ⟶ B ≜ νX : r X\n" 3
  "νX needs a bound: write S ∩ φ with S not mentioning X (⊤(A,B) for the whole object)"
#guard errAt "obj B = 0…1\nr : B ⟶ [B] ≜ {(0,[1])}\nf : B ⟶ [B] ≜ μX : r ∪ X\n" 3
  "μX: [B] has no universe; an array object can grow every round"
#guard errAt "obj X = {A,B,C}\nobj St = 𝒫(X×X)\nL(S : X ⟶ X) : X ⟶ X ≜ νZ : S ∩ Z\nf : St ⟶ X×X ≜ L(∋)\n" 3
  "νZ given a family is not liftable"
#guard errAt "obj B = 0…1\nνx : B ⟶ B ≜ 𝟙(B)\n" 2 "the name 'νx' reads as a fixed point"

/-! `ν` of an AC-3 body runs by delta rounds (`Alg.acFix`): its result against the naive rounds (`Alg.fixOn` on
    `Alg.acRound`, called directly), and each path's work per round. -/

/-- An AC-3 body read from `o`: the bound `s`, the arcs `(A, C)` by name, the universes `uv`, `ud`. -/
def acOf (o : Out) (s uv ud : String) (arcs : List (String × String)) :
    Option ((V : Obj) × (D : Obj) × Rel V D × Rel V V × List (Revise V D)) := do
  let (_, ⟨V, D, sR⟩, _, _) ← o.vals.find? (·.1 == s)
  let UV ← get o uv V V; let UD ← get o ud D D
  let as ← arcs.mapM fun (a, c) => return (⟨← get o a V V, ← get o c D D, UV, UD⟩ : Revise V D)
  pure ⟨V, D, sR, UV, as⟩

/-- The language's `z`, the delta rounds and the naive rounds give one relation. -/
def acAgree (o : Out) (z s uv ud : String) (arcs : List (String × String)) : Bool :=
  match acOf o s uv ud arcs with
  | some ⟨V, D, s, U, as⟩ =>
    let d := (acFix s as U).1; let n := (fixOn (s.n.toNat + 1) (acRound s as) s).1
    d == n && (get o z V D).any (· == d)
  | none => false

/-- One round's work: the cells divided over `Σₖ |ran(Δ Aₖ)|`, and the rows the divisions join `Σₖ |(Δ Aₖ)° (Δ X Cₖ)|`. -/
def acWork {V D : Obj} (as : List (Revise V D)) (X : Rel V D) (Δ : Rel V V) : Nat × Nat :=
  as.foldl (fun (c, j) a => let R := (Δ ≫ a.A).nub
    (c + (ran R).n.toNat, j + (R° ≫ (Δ ≫ X ≫ a.C).nub).n.toNat)) (0, 0)

/-- The delta rounds' work, until `Δ = 𝟘`. -/
def deltaTrace {V D : Obj} (as : List (Revise V D)) : Nat → Rel V D → Rel V V → List (Nat × Nat × Nat)
  | 0, _, _ => []
  | f + 1, X, Δ => if Δ.n == 0 then [] else
    let (X', Δ') := acDelta as (X, Δ); let w := acWork as X Δ
    (w.1, w.2, X'.n.toNat) :: deltaTrace as f X' Δ'

/-- The naive rounds' work, until a round leaves the row count. -/
def naiveTrace {V D : Obj} (s : Rel V D) (as : List (Revise V D)) (U : Rel V V) :
    Nat → Rel V D → List (Nat × Nat × Nat)
  | 0, _ => []
  | f + 1, X => let X' := (acRound s as X).nub; let w := acWork as X U
    (w.1, w.2, X'.n.toNat) :: if X'.n == X.n then [] else naiveTrace s as U f X'

/-- Both traces: per round (cells divided over, rows joined, rows of `X` after). -/
def acTraces (o : Out) (s uv ud : String) (arcs : List (String × String)) :
    List (Nat × Nat × Nat) × List (Nat × Nat × Nat) :=
  match acOf o s uv ud arcs with
  | some ⟨_, _, s, U, as⟩ => (deltaTrace as (s.n.toNat + 1) s.nub U, naiveTrace s as U (s.n.toNat + 1) s.nub)
  | none => ([], [])

def sudokuEx : Out := ok (runExt Programs.sudokuac "uV : Cell ⟶ Cell ≜ 𝟙(Cell)\nuD : D ⟶ D ≜ 𝟙(D)\nne : D ⟶ D ≜ ≠\n")

def squareEx : Out := ok (runText ("obj V = {x,y}\nobj D = 0…9\nA : V ⟶ V ≜ {(x,y)}\nAc : V ⟶ V ≜ A°\n" ++
  "sq : D ⟶ D ≜ {(0,0),(1,1),(2,4),(3,9)}\nsqc : D ⟶ D ≜ sq°\nuV : V ⟶ V ≜ 𝟙(V)\nuD : D ⟶ D ≜ 𝟙(D)\n" ++
  "revise(A : α ⟶ α, C : β ⟶ β, X : α ⟶ β) : α ⟶ β ≜ A\\(X C)\ns : V ⟶ D ≜ ⊤(V,D)\n" ++
  "z : V ⟶ D ≜ νZ : s ∩ revise(A,sq,Z) ∩ revise(A°,sq°,Z)\n"))

#guard acAgree sudokuEx "s" "s₀" "uV" "uD" [("peer", "ne")]
#guard acAgree squareEx "z" "s" "uV" "uD" [("A", "sq"), ("Ac", "sqc")]
-- SudokuAC, both 11 rounds, 489 → 81 rows: the delta rounds join 39780 rows in all, the naive ones 148200
#guard acTraces sudokuEx "s₀" "uV" "uD" [("peer", "ne")] ==
  ([(81, 13980, 183), (81, 9100, 163), (81, 3140, 142), (80, 3640, 122), (80, 3120, 113), (68, 1520, 107),
    (71, 1020, 103), (42, 680, 93), (65, 1660, 83), (73, 1600, 81), (34, 320, 81)],
   [(81, 13980, 183), (81, 13900, 163), (81, 13800, 142), (81, 13660, 122), (81, 13540, 113), (81, 13440, 107),
    (81, 13380, 103), (81, 13340, 93), (81, 13200, 83), (81, 13000, 81), (81, 12960, 81)])

end LeetQ.Rel.Lang.Test
