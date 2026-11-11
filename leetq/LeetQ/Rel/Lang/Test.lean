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

/-- A lifted fold whose step has closed parts (§e, cost of the keyed fold): `G`, `∼R ∩ G` (a complement, so
    `⊤`), `dom(R)`, `π₂⟨π₁,π₁⟩`, each keyed on the pairs a round meets; at every key the fibre is the fold of
    the fibre. -/
def foldClosed : Except Err Out := runText ("obj X = {A,B,C}\nobj K = 0…2\nobj L = 5…6\nobj 1 = {∗}\n" ++
  "ℓ ≜ Λ(⊤(1,L))\nG ≜ {(A,B),(C,C)}\n" ++
  "p(R : X ⟶ X) ≜ ran(ℓ⦇ran⟨𝟙,𝟙⟩, π₂(𝟙×G) ∪ (π₂(𝟙×(∼R ∩ G))) ∪ (π₂(𝟙×dom(R))) ∪ (π₂⟨π₁,π₁⟩)⦈)\n" ++
  "R₀ ≜ {(A,B)}\nR₁ ≜ {(A,B),(B,C)}\nR₂ ≜ {(A,B),(B,C),(C,A)}\n" ++
  "Fm ≜ {(0,0)}⊤(K,X)⟨𝟙,R₀⟩ ∪ ({(1,1)}⊤(K,X)⟨𝟙,R₁⟩) ∪ ({(2,2)}⊤(K,X)⟨𝟙,R₂⟩)\n" ++
  "pF ≜ p(Fm)\np₀ ≜ p(R₀)\np₁ ≜ p(R₁)\np₂ ≜ p(R₂)\n")

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
  "(∼R)°", "∼R S", "{((A, B), A), ((B, A), B)}", "{(A, (B, (A, B)))}"].all trip

#guard ["inits", "tails", "cat", "cat°", "zip", "snoc", "snoc°", "init", "concat", "perm", "setify", "bagify",
  "subseq", "tic", "ordered(R)", "sort(R)", "thinL(R)", "merge(R)", "loop(R)", "R inits concat", "⟨R, S⟩ merge(p)"].all trip

/-! The list builtins of §b on arrays built by `Λ` and `cons`, each value as `Algebra.lean`'s guard of the op
    states it: `x` is `a ↦ [3 1 2]`, `b ↦ [1 5]`; `y` is `a ↦ [7]`, `b ↦ [8 9]`; `z` is `a ↦ [3 3 1 2]`. -/
def lists : Except Err Out := runText ("obj N = 0…9\nobj K = {a,b}\n" ++
  "x ≜ ⟨{(a,3),(b,1)}, Λ({(a,1),(a,2),(b,5)})⟩cons\ny ≜ Λ({(a,7),(b,8),(b,9)})\nz ≜ ⟨{(a,3)}, x⟩cons\n" ++
  "print x inits\nprint x tails\nprint ⟨x,y⟩cat\nprint x cat°\nprint ⟨x,y⟩zip\nprint ⟨x,{(a,4),(b,6)}⟩snoc\n" ++
  "print x snoc°\nprint x init\nprint x inits concat\nprint y perm\nprint z setify\nprint z bagify\n" ++
  "print x ordered(≤)\nprint x sort(≤)\nprint y subseq\nprint x thinL(≤)\n" ++
  "print ⟨Λ({(a,1),(a,5)}),Λ({(a,2),(a,3)})⟩merge(≤)\nprint ⟨{(a,0),(b,1)},x⟩loop(plus)\n" ++
  "print ⟨{(a,5)},Λ({(a,1),(a,2)})⟩tic\n")

-- `thinL(≤)` keeps a subsequence holding, for each element dropped, a lower one: here every one holding `1`
#guard (ok lists).prints == [
  "x inits = {(a, {{}, {3}, {3, 1}, {3, 1, 2}}), (b, {{}, {1}, {1, 5}})}",
  "x tails = {(a, {{3, 1, 2}, {1, 2}, {2}, {}}), (b, {{1, 5}, {5}, {}})}",
  "⟨x, y⟩ cat = {(a, {3, 1, 2, 7}), (b, {1, 5, 8, 9})}",
  "x cat° = {(a, ({}, {3, 1, 2})), (a, ({3}, {1, 2})), (a, ({3, 1}, {2})), (a, ({3, 1, 2}, {})), " ++
    "(b, ({}, {1, 5})), (b, ({1}, {5})), (b, ({1, 5}, {}))}",
  "⟨x, y⟩ zip = {(a, {(3, 7)}), (b, {(1, 8), (5, 9)})}",
  "⟨x, {(a, 4), (b, 6)}⟩ snoc = {(a, {3, 1, 2, 4}), (b, {1, 5, 6})}",
  "x snoc° = {(a, ({3, 1}, 2)), (b, ({1}, 5))}",
  "x init = {(a, {3, 1}), (b, {1})}",
  "x inits concat = {(a, {3, 3, 1, 3, 1, 2}), (b, {1, 1, 5})}",
  "y perm = {(a, {7}), (b, {8, 9}), (b, {9, 8})}",
  "z setify = {(a, {1, 2, 3})}",
  "z bagify = {(a, {1, 2, 3, 3})}",
  "x ordered(≤) = {(b, {1, 5})}",
  "x sort(≤) = {(a, {1, 2, 3}), (b, {1, 5})}",
  "y subseq = {(a, {}), (a, {7}), (b, {}), (b, {8}), (b, {8, 9}), (b, {9})}",
  "x thinL(≤) = {(a, {1}), (a, {1, 2}), (a, {3, 1}), (a, {3, 1, 2}), (b, {1}), (b, {1, 5})}",
  "⟨Λ({(a, 1), (a, 5)}), Λ({(a, 2), (a, 3)})⟩ merge(≤) = {(a, {1, 2, 3, 5})}",
  "⟨{(a, 0), (b, 1)}, x⟩ loop(plus) = {(a, 6), (b, 7)}",
  "⟨{(a, 5)}, Λ({(a, 1), (a, 2)})⟩ tic = {(a, {{5}, {5, 1}, {5, 1, 2}})}"]

/-- A list builtin in a lifted body takes the closed row (§e): at each key of a two-key family the fibre of the
    lifted body is the body on the fibre. -/
def listsLifted : Except Err Out := runText ("obj N = 0…9\nobj K = {a,b}\nobj J = {i,j}\n" ++
  "R₀ ≜ {(a,3),(a,1)}\nR₁ ≜ {(a,2),(b,5),(b,1)}\nFm ≜ {(i,i)}⊤(J,K)⟨𝟙,R₀⟩ ∪ ({(j,j)}⊤(J,K)⟨𝟙,R₁⟩)\n" ++
  "f(S : K ⟶ N) ≜ ⟨S,Λ(S)⟩cons inits ∪ (Λ(S)cat°π₁ tails)\nfF ≜ f(Fm)\n" ++
  "check {(i,i)}fF = {(i,i)}⊤(J,K)⟨𝟙,f(R₀)⟩\ncheck {(j,j)}fF = {(j,j)}⊤(J,K)⟨𝟙,f(R₁)⟩\n")

#guard listsLifted.isOk

/-! The kernel's value verbs of §b on pairs of numbers, each `Alg.arith` with its opcode: a result outside the
    declared object has no row (`minus` below `0`, as `succ` at the top), nor a zero divisor. -/

def arith : Except Err Out := runText ("obj N = 0…20\n" ++
  "w ≜ {((7,2),(7,2)),((2,7),(2,7)),((7,0),(7,0)),((3,5),(3,5))}\n" ++
  "print w plus\nprint w times\nprint w minus\nprint w div\nprint w mod\nprint w max\nprint w min\n" ++
  "D ≜ dom(𝟙(N×N) div)\ncheck D⟨⟨π₂,div⟩times,mod⟩plus = Dπ₁\ncheck D⟨mod,π₂⟩ = D⟨mod,π₂⟩(𝟙 ∩ (π₁ < π₂°))\n")

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
  "R₀ ≜ {(a,3),(b,1)}\nR₁ ≜ {(a,2),(b,5),(b,1)}\nFm ≜ {(i,i)}⊤(J,K)⟨𝟙,R₀⟩ ∪ ({(j,j)}⊤(J,K)⟨𝟙,R₁⟩)\n" ++
  "f(S : K ⟶ N) ≜ ⟨S,S⟩times ∪ (⟨S succ,S⟩mod)\nfF ≜ f(Fm)\n" ++
  "check {(i,i)}fF = {(i,i)}⊤(J,K)⟨𝟙,f(R₀)⟩\ncheck {(j,j)}fF = {(j,j)}⊤(J,K)⟨𝟙,f(R₁)⟩\nprint f(R₀)\n")

#guard arithLifted.isOk
#guard (ok arithLifted).prints == ["f(R₀) = {(a, 1), (a, 9), (b, 0), (b, 1)}"]

/-- B&dM's digits of a number (`val_converse_eq`): `op°`, the converse of `op(n,d) = 10n+d` on a digit `d`,
    taken from `x` once a round until it reaches `0`, each digit put on the front of the list. The rounds `K`
    hold no number of `N`, so a literal's words name one object (§c). -/
def digits : Except Err Out := runText ("obj N = 0…199\nobj K = 200…203\n" ++
  "ten ≜ ⊤(N,N){(10,10)}\ndg ≜ dom(<{(10,10)})\nop ≜ ⟨⟨π₁,π₁ ten⟩times,π₂ dg⟩plus\n" ++
  "x ≜ {(107,107)}\nr ≜ Λ(x⊤(N,K))\nnz ≜ 𝟙(N) − {(0,0)}\n" ++
  "step ≜ ⟨π₁{(0,0)},π₂⟩ ∪ ⟨π₁ nz op° π₁,⟨π₁ nz op° π₂,π₂⟩cons⟩\n" ++
  "ds ≜ r⦇ran(x⟨𝟙,nil⟩),π₂ step⦈π₂\nprint ds\n")

#guard (ok digits).prints == ["ds = {(107, {1, 0, 7})}"]

-- a parameterised list builtin given a family
#guard errAt "obj N = 0…3\nobj St = 𝒫(N×N)\nf(S : N ⟶ N) ≜ sort(S)\ng ≜ f(∋)\n" 3 "not liftable"

-- a nested literal (§c): each leaf position its own object, the side their product
#guard match runText "obj X = {A,B}\nobj N = 0…1\nL ≜ {((A,0),(1,B)),((B,1),(0,A))}\nprint L\n" with
  | .ok o => o.prints == ["L = {((A, 0), (1, B)), ((B, 1), (0, A))}"] &&
    (get o "L" (.prod .long .long) (.prod .long .long)).map (·.toList) == some [((0, 0), (1, 1)), ((1, 1), (0, 0))]
  | .error _ => false
#guard errAt "obj X = {A,B}\nL ≜ {((A,B),A),(A,B)}\n" 2 "nest alike"

/-! Signed numbers (§a, §c): a range `-3…3`, signed literal words, `succ ≤ <` and the value verbs on it, each
    against Lean's `Int` (`div` floors and `mod` takes the divisor's sign, as q's: `Int.fdiv`, `Int.fmod`); a print
    lists numbers by value. -/

def zs : List Int := (List.range 7).map fun k : Nat => (k : Int) - 3
def signed : Except Err Out := runText ("obj Z = -3…3\nobj K = {a,b}\n" ++
  "x ≜ {(a,-1),(b,2),(a,-3)} -- a comment, after a signed literal\nprint x\nprint Λ(x)\nprint x − {(a,-3)}\n" ++
  "print {(-1,-1)}−{(2,2)}\ns ≜ 𝟙(Z) succ\nle ≜ 𝟙(Z) ≤\nlt ≜ 𝟙(Z) <\nW ≜ 𝟙(Z×Z)\n" ++
  "pl ≜ W plus\ntm ≜ W times\nmi ≜ W minus\ndv ≜ W div\nmd ≜ W mod\nmx ≜ W max\nmn ≜ W min\n")

def sameSet {α : Type} [BEq α] (a b : List α) : Bool := a.all b.contains && b.all a.contains
def ints (R : Rel .long .long) : List (Int × Int) := R.toList.map fun (a, b) => (a.toInt, b.toInt)

#guard signed.isOk
#guard (ok signed).prints == ["x = {(a, -3), (a, -1), (b, 2)}", "Λ(x) = {(a, {-3, -1}), (b, {2})}",
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
#guard errAt "obj Z = -3…3\nR ≜ 𝟙(Z)\nf ≜ R -3\n" 3 "expected the end of the line, found '-'"
#guard errAt "obj Z = -3…3\nR ≜ 𝟙(Z)\nf ≜ R −3\n" 3 "expected a term, found '3'"
#guard ["{(A, -1)}", "{((-1, B), -20)}", "R − S"].all trip

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

/-! Terms on an object with no universe (§a): a converse pushed to the leaves, a division tested on the pairs a
    meet supplies, `R×S` as `⟨π₁R,π₂S⟩`; and what is still refused. Expected values by hand. -/

/-- The value printed by each `print` of `src`, after its ` = `. -/
def printed (src : String) : List String := (ok (runText src)).prints.map fun s => (s.splitOn " = ").getLastD ""

def chs : String := "obj 1 = {∗}\nobj Ch = {a,b}\nobj N = 0…3\ne ≜ nil(1,[Ch])\nx ≜ ⟨{(∗,a)}, ⟨{(∗,b)}, e⟩cons⟩cons\n" ++
  "y ≜ ⟨{(∗,a)}, ⟨{(∗,a)}, ⟨{(∗,b)}, e⟩cons⟩cons⟩cons\nns ≜ ⟨{(∗,2)}, ⟨{(∗,3)}, nil⟩cons⟩cons\n" ++
  "ms ≜ ⟨{(∗,3)}, ⟨{(∗,1)}, ⟨{(∗,2)}, nil⟩cons⟩cons⟩cons\nks ≜ ⟨{(∗,3)}, ⟨{(∗,1)}, ⟨{(∗,1)}, nil⟩cons⟩cons⟩cons\n" ++
  "ok ≜ dom(π₁(≤/∋) ∩ π₂)\n"

-- the converse: `(RS)° = S°R°`, `∩`, a pair with one side's converse, `R°° = R`, a coreflexive, `cons° = uncons`
#guard printed (chs ++ "print x cons° (perm cons°)°\nprint x (perm ∩ perm)° cons°\nprint x ⟨cons°π₁, perm⟩°° π₂\n" ++
  "print x (dom(π₁{(a,a)}) cons)°\nprint x (dom(π₁{(b,b)}) cons)°\n") ==
  ["{(∗, {a, b}), (∗, {b, a})}", "{(∗, (a, {b})), (∗, (b, {a}))}", "{(∗, {a, b}), (∗, {b, a})}",
   "{(∗, (a, {b}))}", "{}"]
-- refused at a leaf whose converse does not run on demand: `π₁` in `⟨π₁,π₂⟩°`, `∋` in `∈`
#guard errAt (chs ++ "print x (cons° ⟨π₁,π₂⟩ cons)°\n") 11 "the converse of π₁ does not run on demand"
#guard errAt (chs ++ "print {(∗,a)} ∈\n") 11 "the converse of ∋ does not run on demand"
-- a division tested on the pairs: `R/S`, `R\S`, `frac`, `∼`, `−`, each beside a term run on demand
#guard printed (chs ++ "print ⟨{(∗,1)},ns⟩ok\nprint ⟨{(∗,3)},ns⟩ok\nprint ⟨{(∗,2)},ns⟩ok\n" ++
  "print ms (∋ ∩ (cons\\(π₁ ≤)))\nprint ks (subseq ∩ frac(∋,∋))\n" ++
  "print ⟨{(∗,3)},ns⟩(π₂ ∩ (π₁∼(≤/∋)))\nprint ⟨{(∗,1)},ns⟩(π₂ ∩ (π₁∼(≤/∋)))\nprint ⟨{(∗,3)},ns⟩(π₂ − (π₁(≤/∋)))\n") ==
  ["{(∗, (1, {2, 3}))}", "{}", "{(∗, (2, {2, 3}))}", "{(∗, 3)}", "{(∗, {3, 1, 1}), (∗, {3, 1})}",
   "{(∗, {2, 3})}", "{}", "{(∗, {2, 3})}"]
-- refused: a division with no term on demand to test it against, and a meet of two
#guard errAt (chs ++ "print {(∗,1)}(≤/∋)\n") 11 "R/S reads its operands whole"
#guard errAt (chs ++ "print {(∗,1)}((≤/∋) ∩ (≤/∋))\n") 11 "R/S reads its operands whole"
-- `R×S` on demand as `⟨π₁R,π₂S⟩`; closed, as before
#guard printed (chs ++ "print ⟨{(1,1)},⟨{(1,2)},Λ({(1,1)})⟩⟩(𝟙×π₁)plus\nprint y cons°(𝟙×perm)\n" ++
  "print ⟨x,{(∗,b)}⟩(perm×𝟙)\nprint {(1,1)}×{(2,3)}\n") ==
  ["{(1, 3)}", "{(∗, (a, {a, b})), (∗, (a, {b, a}))}", "{(∗, ({a, b}, b)), (∗, ({b, a}, b))}", "{((1, 2), (1, 3))}"]
-- refused: an operand that does not run, named; the object printed as the program writes it, `[Ch]`
#guard errAt (chs ++ "print ⟨{(∗,a)},{(∗,b)}⟩(∈×𝟙)\n") 11 "the converse of ∋ does not run on demand"
#guard errAt (chs ++ "print ⟨{(∗,a)},{(∗,b)}⟩(∈×𝟙)\n") 11 "[Ch] has no universe"
-- `loop(F)` reads `F` whole: refused on an array state, and the message names `loop`, not a missing left context
#guard errAt (chs ++ "print x ⟨nil,𝟙⟩loop(snoc)\n") 11 "loop( ) reads its argument whole: [Ch]×Ch has no universe"

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
