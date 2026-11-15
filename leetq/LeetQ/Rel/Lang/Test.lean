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

/-- `X⦇e,S⦈` given a family (§e): at each key of a three-key family, the fibre of the lifted fold is the fold of
    the fibre. `p(R)` holds the pairs `(a,b)` with `b` at most two steps of `R` from `a`. -/
rel_program foldLaw after Programs.prelude where
    obj X = {A,B,C}
    obj K = 0…2
    obj L = 5…6
    ℓ : 1 ⟶ [L] ≜ Λ(⊤(1,L))
    p(R : X ⟶ X) : X×X ⟶ X×X ≜ ran(ℓ⦇ran⟨𝟙,𝟙⟩, π₂ ∪ (π₂(𝟙×R))⦈)
    R₀ : X ⟶ X ≜ {(A,B)}
    R₁ : X ⟶ X ≜ {(A,B),(B,C)}
    R₂ : X ⟶ X ≜ {(A,B),(B,C),(C,A)}
    Fm : K ⟶ X×X ≜ {(0,0)}⊤(K,X)⟨𝟙,R₀⟩ ∪ ({(1,1)}⊤(K,X)⟨𝟙,R₁⟩) ∪ ({(2,2)}⊤(K,X)⟨𝟙,R₂⟩)
    pF : K ⟶ (X×X)×(X×X) ≜ p(Fm)
    p₀ : X×X ⟶ X×X ≜ p(R₀)
    p₁ : X×X ⟶ X×X ≜ p(R₁)
    p₂ : X×X ⟶ X×X ≜ p(R₂)

/-- At each key `k` of `pF`, its fibre is the relation `pₖ`. -/
def fibres (gs : List (String × Gen.Gv)) : Bool :=
  [((0 : Int64), "p₀"), (1, "p₁"), (2, "p₂")].all fun (k, n) =>
    match get gs "pF" .long (.prod XX XX), get gs n XX XX with
    | some F, some R =>
      let f := (F.toList.filter (·.1 == k)).map (·.2)
      !R.toList.isEmpty && f.all R.toList.contains && R.toList.all f.contains
    | _, _ => false

#guard foldLaw.ok && fibres foldLaw.expanded

/-- A lifted fold whose step has closed parts (§e, cost of the keyed fold): `G`, `∼R ∩ G` (a complement, so
    `⊤`), `dom(R)`, `π₂⟨π₁,π₁⟩`, each keyed on the pairs a round meets; at every key the fibre is the fold of
    the fibre. -/
rel_program foldClosed after Programs.prelude where
    obj X = {A,B,C}
    obj K = 0…2
    obj L = 5…6
    ℓ : 1 ⟶ [L] ≜ Λ(⊤(1,L))
    G : X ⟶ X ≜ {(A,B),(C,C)}
    p(R : X ⟶ X) : X×X ⟶ X×X ≜ ran(ℓ⦇ran⟨𝟙,𝟙⟩, π₂(𝟙×G) ∪ (π₂(𝟙×(∼R ∩ G))) ∪ (π₂(𝟙×dom(R))) ∪ (π₂⟨π₁,π₁⟩)⦈)
    R₀ : X ⟶ X ≜ {(A,B)}
    R₁ : X ⟶ X ≜ {(A,B),(B,C)}
    R₂ : X ⟶ X ≜ {(A,B),(B,C),(C,A)}
    Fm : K ⟶ X×X ≜ {(0,0)}⊤(K,X)⟨𝟙,R₀⟩ ∪ ({(1,1)}⊤(K,X)⟨𝟙,R₁⟩) ∪ ({(2,2)}⊤(K,X)⟨𝟙,R₂⟩)
    pF : K ⟶ (X×X)×(X×X) ≜ p(Fm)
    p₀ : X×X ⟶ X×X ≜ p(R₀)
    p₁ : X×X ⟶ X×X ≜ p(R₁)
    p₂ : X×X ⟶ X×X ≜ p(R₂)

#guard foldClosed.ok && fibres foldClosed.expanded

/-- Object variables (§e): `uq : α ⟶ β` at `X ⟶ N` and at `N ⟶ X` against the ground copies `uX`, `uN`; and
    `d : α ⟶ α` given `Fm : K ⟶ X×X`, which `α ⟶ α` reads as a family, against `d` of each fibre. -/
rel_program objVars after Programs.prelude where
    obj X = {A,B,C}
    obj N = {x,y,z}
    obj K = 0…2
    uq(R : α ⟶ β) : α ⟶ β ≜ R ∩ (R°\𝟙)
    uX(R : X ⟶ N) : X ⟶ N ≜ R ∩ (R°\𝟙)
    uN(R : N ⟶ X) : N ⟶ X ≜ R ∩ (R°\𝟙)
    R₁ : X ⟶ N ≜ {(A,x),(A,y),(B,z)}
    R₂ : N ⟶ X ≜ {(x,A),(y,B),(y,C),(z,C)}
    a₁ : X ⟶ N ≜ uq(R₁)
    b₁ : X ⟶ N ≜ uX(R₁)
    a₂ : N ⟶ X ≜ uq(R₂)
    b₂ : N ⟶ X ≜ uN(R₂)
    d(R : α ⟶ α) : α ⟶ α ≜ R ∩ (R°\𝟙)
    F₀ : X ⟶ X ≜ {(A,B),(A,C)}
    F₁ : X ⟶ X ≜ {(A,B),(B,C)}
    F₂ : X ⟶ X ≜ {(A,A),(B,A),(B,B),(C,A)}
    Fm : K ⟶ X×X ≜ {(0,0)}⊤(K,X)⟨𝟙,F₀⟩ ∪ ({(1,1)}⊤(K,X)⟨𝟙,F₁⟩) ∪ ({(2,2)}⊤(K,X)⟨𝟙,F₂⟩)
    dF : K ⟶ X×X ≜ d(Fm)
    d₀ : X ⟶ X ≜ d(F₀)
    d₁ : X ⟶ X ≜ d(F₁)
    d₂ : X ⟶ X ≜ d(F₂)

#guard let o := objVars.expanded
  let g (n : String) := get o n .long .long
  objVars.ok && g "a₁" == g "b₁" && g "a₂" == g "b₂" && (g "a₁").map (·.toList) == some [(1, 2)] &&
    (g "a₂").map (·.n) == some 2 &&
    [((0 : Int64), "d₀"), (1, "d₁"), (2, "d₂")].all fun (k, n) =>
      match get o "dF" .long XX, g n with
      | some F, some R =>
        let f := (F.toList.filter (·.1 == k)).map (·.2)
        f.all R.toList.contains && R.toList.all f.contains && (k == 0 || !f.isEmpty)
      | _, _ => false

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

/-! The elaborated definitions, as sets, on the reachable states. -/

/-- The definition `n` of `given` or of the program it extends at `St ⟶ B` holds the rows `xs`, whatever their
    order and multiplicity. -/
def rowsAre {B : Obj} [BEq B.El] (n : String) (xs : List (St.El × B.El)) : Bool :=
  match get (given.expanded ++ Programs.blocks.expanded) n St B with
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

/-! One front-end error of each class, at its line: the text read after the prelude (`Expand.read`), nothing
    evaluated. -/

/-- The program `prog` read after the prelude: its error, if any. -/
def elabErr (prog : Except Err Program) : Option Err :=
  match prog >>= Expand.read (some Programs.prelude) [] with | .error e => some e | .ok _ => none

def errAt (src : String) (line : Nat) (what : String) : Bool :=
  match elabErr (Parse.parse src) with
  | some e => e.pos.line == line && (e.msg.splitOn what).length > 1
  | none => false

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
rel_program lists after Programs.prelude where
    obj N = 0…9
    obj K = {a,b}
    x : K ⟶ [N] ≜ ⟨{(a,3),(b,1)}, Λ({(a,1),(a,2),(b,5)})⟩cons
    y : K ⟶ [N] ≜ Λ({(a,7),(b,8),(b,9)})
    z : K ⟶ [N] ≜ ⟨{(a,3)}, x⟩cons
    print x inits
    print x tails
    print ⟨x,y⟩cat
    print x cat°
    print ⟨x,y⟩zip
    print ⟨x,{(a,4),(b,6)}⟩snoc
    print x snoc°
    print x init
    print x inits concat
    print y perm
    print z setify
    print z bagify
    print x ordered(≤)
    print x sort(≤)
    print y subseq
    print x thinL(≤)
    print ⟨Λ({(a,1),(a,5)}),Λ({(a,2),(a,3)})⟩merge(≤)
    print ⟨{(a,0),(b,1)},x⟩loop(plus)
    print ⟨{(a,5)},Λ({(a,1),(a,2)})⟩tic

-- `thinL(≤)` runs the one-pass thinning: each element bumped into the thinned rest keeps the lower of the two
#guard lists.ok && lists.prints == [
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
rel_program ats after Programs.prelude where
    obj N = 0…9
    obj K = {a,b}
    x : K ⟶ [N] ≜ ⟨{(a,3),(b,1)}, Λ({(a,1),(a,2),(b,5)})⟩cons
    print x at(0)
    print x at(1)
    print x at(2)
    print x at(3)
    check x at(0) = x head
    check x tail at(0) = x at(1)
    check x tail at(1) = x at(2)
    check x tail at(2) = x at(3)
    check x at(3) = 𝟘
#guard ats.ok && ats.prints == ["x at(0) = {(a, 3), (b, 1)}", "x at(1) = {(a, 1), (b, 5)}", "x at(2) = {(a, 2)}",
  "x at(3) = {}"]
#guard match elabErr (Parse.parse "obj N = 0…9\nf : [N] ⟶ N ≜ at(x)\n") with
  | some e => e.msg == "at( ) takes a position, a number from 0, found 'x'" | none => false
#guard match elabErr (Parse.parse "obj N = 0…9\nf : [N] ⟶ N ≜ at(-1)\n") with
  | some e => e.msg == "at( ) takes a position from 0 that fits a long, found -1" | none => false

/-- A list builtin in a lifted body takes the closed row (§e): at each key of a two-key family the fibre of the
    lifted body is the body on the fibre. -/
rel_program listsLifted after Programs.prelude where
    obj N = 0…9
    obj K = {a,b}
    obj J = {i,j}
    R₀ : K ⟶ N ≜ {(a,3),(a,1)}
    R₁ : K ⟶ N ≜ {(a,2),(b,5),(b,1)}
    Fm : J ⟶ K×N ≜ {(i,i)}⊤(J,K)⟨𝟙,R₀⟩ ∪ ({(j,j)}⊤(J,K)⟨𝟙,R₁⟩)
    f(S : K ⟶ N) : K ⟶ [[N]] ≜ ⟨S,Λ(S)⟩cons inits ∪ (Λ(S)cat°π₁ tails)
    fF : J ⟶ K×[[N]] ≜ f(Fm)
    check {(i,i)}fF = {(i,i)}⊤(J,K)⟨𝟙,f(R₀)⟩
    check {(j,j)}fF = {(j,j)}⊤(J,K)⟨𝟙,f(R₁)⟩

#guard listsLifted.ok

/-- Orders on demand (§a): each operator runs its order on the pairs it compares, here `R ≜ length ≤ length°` on
    `[N]`, which has no universe; a closed order as before; and `∼R`, tested as the complement of `R`'s test. -/
rel_program onDemand after Programs.prelude where
    obj N = 0…9
    obj K = {a,b}
    L : K ⟶ [[N]] ≜ {(a,[1 2] [3] [8]),(b,[5] [4 6 7] [9])}
    G : K ⟶ [[N]] ≜ Λ(L∋)
    R : [α] ⟶ [β] ≜ length ≤(N,N) length°
    p : [α] ⟶ [α] ≜ dom(length{(1,1)})
    print G est(R)
    print G thin(R)
    print L filter(p)
    print L takewhile(p)
    print {(a,[3] [1 2]),(b,[1 2] [3])} ordered(R)
    print L sort(R)
    print L thinL(R)
    print ⟨L sort(R),{(a,[[1 2]]),(b,[[5]])}⟩merge(R)
    print Λ({(a,3),(a,1),(b,5)})est(≤)
    print G est(∼R)

#guard onDemand.ok && onDemand.prints == [
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

rel_program arith after Programs.prelude where
    obj N = 0…20
    w : N×N ⟶ N×N ≜ {((7,2),(7,2)),((2,7),(2,7)),((7,0),(7,0)),((3,5),(3,5))}
    print w plus
    print w times
    print w minus
    print w div
    print w mod
    print w max
    print w min
    D : N×N ⟶ N×N ≜ dom(𝟙(N×N) div)
    check D⟨⟨π₂,div⟩times,mod⟩plus = Dπ₁
    check D⟨mod,π₂⟩ = D⟨mod,π₂⟩(𝟙 ∩ (π₁ < π₂°))

-- `a = b·div + mod` and `mod < b` on every pair of `N` with a divisor other than `0`
#guard arith.ok
#guard arith.prints == [
  "w plus = {((2, 7), 9), ((3, 5), 8), ((7, 0), 7), ((7, 2), 9)}",
  "w times = {((2, 7), 14), ((3, 5), 15), ((7, 0), 0), ((7, 2), 14)}",
  "w minus = {((7, 0), 7), ((7, 2), 5)}",
  "w div = {((2, 7), 0), ((3, 5), 0), ((7, 2), 3)}",
  "w mod = {((2, 7), 2), ((3, 5), 3), ((7, 2), 1)}",
  "w max = {((2, 7), 7), ((3, 5), 5), ((7, 0), 7), ((7, 2), 7)}",
  "w min = {((2, 7), 2), ((3, 5), 3), ((7, 0), 0), ((7, 2), 2)}"]

#guard ["plus", "times", "minus", "div", "mod", "max", "min", "⟨R, S⟩ times", "R mod°"].all trip

/-- A value verb in a lifted body takes the closed row (§e): at each key the fibre is the body on the fibre. -/
rel_program arithLifted after Programs.prelude where
    obj N = 0…9
    obj K = {a,b}
    obj J = {i,j}
    R₀ : K ⟶ N ≜ {(a,3),(b,1)}
    R₁ : K ⟶ N ≜ {(a,2),(b,5),(b,1)}
    Fm : J ⟶ K×N ≜ {(i,i)}⊤(J,K)⟨𝟙,R₀⟩ ∪ ({(j,j)}⊤(J,K)⟨𝟙,R₁⟩)
    f(S : K ⟶ N) : K ⟶ N ≜ ⟨S,S⟩times ∪ (⟨S succ,S⟩mod)
    fF : J ⟶ K×N ≜ f(Fm)
    check {(i,i)}fF = {(i,i)}⊤(J,K)⟨𝟙,f(R₀)⟩
    check {(j,j)}fF = {(j,j)}⊤(J,K)⟨𝟙,f(R₁)⟩
    print f(R₀)

#guard arithLifted.ok
#guard arithLifted.prints == ["f(R₀) = {(a, 1), (a, 9), (b, 0), (b, 1)}"]

/-- B&dM's digits of a number (`val_converse_eq`): `op°`, the converse of `op(n,d) = 10n+d` on a digit `d`,
    taken from `x` once a round until it reaches `0`, each digit put on the front of the list. The rounds `K`
    hold no number of `N`, so a literal's words name one object (§c). -/
rel_program digits after Programs.prelude where
    obj N = 0…199
    obj K = 200…203
    ten : N ⟶ N ≜ ⊤(N,N){(10,10)}
    dg : N ⟶ N ≜ dom(<{(10,10)})
    op : N×N ⟶ N ≜ ⟨⟨π₁,π₁ ten⟩times,π₂ dg⟩plus
    x : N ⟶ N ≜ {(107,107)}
    r : N ⟶ [K] ≜ Λ(x⊤(N,K))
    nz : N ⟶ N ≜ 𝟙(N) − {(0,0)}
    step : N×[N] ⟶ N×[N] ≜ ⟨π₁{(0,0)},π₂⟩ ∪ ⟨π₁ nz op° π₁,⟨π₁ nz op° π₂,π₂⟩cons⟩
    ds : N ⟶ [N] ≜ r⦇ran(x⟨𝟙,nil⟩),π₂ step⦈π₂
    print ds

#guard digits.ok && digits.prints == ["ds = {(107, 1 0 7)}"]

-- a prelude definition given a family through a typed parameter: the lifted body reaches `perm`, closed on `[N]`
#guard errAt "obj N = 0…3\nobj St = 𝒫(N×N)\nf(S : N ⟶ N) : [N] ⟶ [N] ≜ sort(S)\ng : St ⟶ [N]×[N] ≜ f(∋)\n" 3
  "a closed term in a lifted body: [N] has no universe"

-- a nested literal (§c): each leaf position its own object, the side their product
rel_program nested after Programs.prelude where
    obj X = {A,B}
    obj N = 0…1
    L : X×N ⟶ N×X ≜ {((A,0),(1,B)),((B,1),(0,A))}
    print L
#guard nested.ok && nested.prints == ["L = {((A, 0), (1, B)), ((B, 1), (0, A))}"] &&
  (get nested.expanded "L" (.prod .long .long) (.prod .long .long)).map (·.toList) ==
    some [((0, 0), (1, 1)), ((1, 1), (0, 0))]
#guard errAt "obj X = {A,B}\nL ≜ {((A,B),A),(A,B)}\n" 2 "nest alike"

/-! Declared types (§e). -/

-- a body that is not the declared type; a definition with none, told the type it has
#guard errAt "obj X = {A,B}\nobj N = 0…1\nf : X ⟶ N ≜ 𝟙(X)\n" 3 "`f` is declared X ⟶ N, but its body is X ⟶ X"
#guard errAt "obj X = {A,B}\nf ≜ 𝟙(X)\n" 2 "`f` has no type; it is f : X ⟶ X"
#guard errAt "obj X = {A,B}\nf(R : X ⟶ X) ≜ R°\n" 2 "`f` has no type; it is f(R : X ⟶ X) : X ⟶ X"
-- one generic definition at two objects in one program: its variables instantiated at each use
rel_program generic after Programs.prelude where
    obj X = {A,B}
    obj N = 0…1
    sw : α×β ⟶ β×α ≜ ⟨π₂,π₁⟩
    print {((A,0),(A,0))}sw
    print {((1,B),(1,B))}sw
#guard printed generic.prints == ["{((A, 0), (0, A))}", "{((1, B), (B, 1))}"]
-- the declared type determines an object the body leaves open: `nil`'s source and element
rel_program declNil after Programs.prelude where
    obj N = 0…3
    e : 1 ⟶ [N] ≜ nil
    print e
#guard printed declNil.prints == ["{(∗, [])}"]
-- `typesOf` prints each definition's head as it is declared
def heads : List String := ["f : X ⟶ X", "g(R : α ⟶ β) : β ⟶ α", "_≼_(R : α ⟶ β, S : β ⟶ γ) : α ⟶ γ"]
#guard match typesOf (some ("obj X = {A,B}\n" ++
    String.join ((heads.zip ["𝟙", "R°", "R S"]).map fun (h, b) => s!"{h} ≜ {b}\n"))) with
  | .ok ts => ts == heads
  | .error _ => false
-- a `where` item takes no type of its own, nor does a test
rel_program whereItem after Programs.prelude where
    obj B = 0…1
    f : B×B ⟶ B ≜ a where a ≜ π₂
    print {((0,1),(0,1))}f
#guard printed whereItem.prints == ["{((0, 1), 1)}"]
#guard errAt "obj B = 0…1\nf : B×B ⟶ B ≜ a where a : B×B ⟶ B ≜ π₂\n" 2
  "the `where` item `a` takes no type: make it a top-level definition to give it one"
#guard errAt "obj X = {A,B}\nh(S : X ⟶ X) : X ⟶ X ≜ 𝟙 ⊑ S\n" 2 "the test `h` has no type of its own"

/-! Array literals (§c): two or more items juxtaposed, or `[…]`; an element position is one object over the
    elements of all rows' arrays there, at any depth and on either side; printed as it is read. -/

rel_program arrs after Programs.prelude where
    obj N = -3…9
    obj K = {a,b}
    x : 1 ⟶ [N] ≜ {(∗,3 1 2)}
    xc : 1 ⟶ [N] ≜ ⟨{(∗,3)}, ⟨{(∗,1)}, ⟨{(∗,2)}, nil⟩cons⟩cons⟩cons
    check x = xc
    check {(∗,[3 1 2])} = xc
    check {(∗,[1])} = ⟨{(∗,1)},nil⟩cons
    check {(∗,[1] [2 3])} = ⟨{(∗,[1])},⟨{(∗,2 3)},nil⟩cons⟩cons
    check {(∗,(1,2) (3,4))} = ⟨{(∗,(1,2))},⟨{(∗,(3,4))},nil⟩cons⟩cons
    print x
    print {(a b,1)}
    print {(∗,(1,2) (3,4))}
    print {(∗,[1] [2 3])}
    print {((a,1 2),[3])}
    print {(a,-1 2),(b,[])}
    print {(∗,[1 2] [])}
    print {(3 1 2,a b)}
    print {(∗,[[]] [[1]])}

#guard arrs.ok && printed arrs.prints == ["{(∗, 3 1 2)}", "{(a b, 1)}", "{(∗, (1, 2) (3, 4))}", "{(∗, [1] [2 3])}",
  "{((a, 1 2), [3])}", "{(a, -1 2), (b, [])}", "{(∗, [1 2] [])}", "{(3 1 2, a b)}", "{(∗, [[]] [[1]])}"]
#guard (get arrs.expanded "x" .long (.arr .long)).map (·.toList) == some [((0 : Int64), [(3 : Int64), 1, 2])]
-- a printed literal reads back as itself
#guard ["{(∗, 3 1 2)}", "{(∗, [1] [2 3])}", "{((a, 1 2), [3])}", "{(b, [])}", "{(∗, (1, 2) (3, 4))}"].all trip
-- an element position whose arrays are all empty, a word in no object, rows nesting differently, a comma
def arrE : String := "obj N = 0…9\n"
def emptyErr : String := "the object of [] cannot be read off an empty array: write nil(A,[O])"
/-- `src` fails at `line`, `col` with `what` in the message. -/
def errAtCol (src : String) (line col : Nat) (what : String) : Bool :=
  match elabErr (Parse.parse src) with
  | some e => e.pos.line == line && e.pos.col == col && (e.msg.splitOn what).length > 1
  | none => false
-- nothing determines the object: the error at the literal
#guard errAtCol (arrE ++ "print {(∗,[])}\n") 2 7 emptyErr
#guard errAtCol (arrE ++ "print {(∗,[[]] [])}\n") 2 7 emptyErr
#guard errAtCol (arrE ++ "print {(∗,[])} ∪ {(∗,[])}\n") 2 7 emptyErr
-- an untyped definition names the type its body has, the object left open a variable
#guard errAt (arrE ++ "e ≜ {(∗,[])}\n") 2 "`e` has no type; it is e : 1 ⟶ [α]"
-- the context determines it (§c): the other side of a check, the other operand, the declared type, the
-- composition, the pair
rel_program arrCtx after Programs.prelude where
    obj N = 0…9
    obj K = {a,b}
    e : 1 ⟶ [N] ≜ nil
    x : 1 ⟶ [N] ≜ {(∗,1 2)}
    check e = {(∗,[])}
    check {(∗,[])} = e
    check e ⊑ {(∗,[])}
    check x ∪ {(∗,[])} = {(∗,1 2),(∗,[])}
    check x ∩ {(∗,[])} = 𝟘(1,[N])
    check x − {(∗,[])} = x
    d : 1 ⟶ [N] ≜ {(∗,[])}
    check d = e
    nn : 1 ⟶ [[N]] ≜ {(∗,[[]])}
    check nn = ⟨e,nil⟩cons
    c : 1 ⟶ N ≜ {(∗,[])}{([],3),([1],4)}
    check c = {(∗,3)}
    check ⟨{(∗,[])},{(∗,a)}⟩ = ⟨e,{(∗,a)}⟩
    check {(∗,[] [3])} = ⟨e,⟨{(∗,[3])},nil⟩cons⟩cons
    print d
    print nn
#guard arrCtx.ok && printed arrCtx.prints == ["{(∗, [])}", "{(∗, [[]])}"]
-- words two objects hold: open too, fixed by the context, else the error at the literal
def twoObjs : String := "obj A = {a,b}\nobj B = {a,c}\n"
rel_program twoObjsX after Programs.prelude where
    obj A = {a,b}
    obj B = {a,c}
    x : A ⟶ B ≜ {(a,a)}
    print x
#guard printed twoObjsX.prints == ["{(a, a)}"]
#guard errAtCol (twoObjs ++ "print {(a,c)}\n") 3 7 "the elements [a] are in [B, A]; write the literal after its object"
-- a wrong expectation is a failed check, not an object error
rel_program wrongCheck after Programs.prelude where
    obj N = 0…9
    x : 1 ⟶ [N] ≜ {(∗,1 2)}
    check x = {(∗,[])}
#guard wrongCheck.failures.any fun e => (e.msg.splitOn "check failed").length > 1
#guard errAt (arrE ++ "e ≜ {(∗,1 12)}\n") 2 "no declared object has the elements [1, 12]"
#guard errAt (arrE ++ "e ≜ {(∗,1 2),(∗,3)}\n") 2
  "the rows of a literal nest alike: found 3, expected the form of 1 2"
#guard errAt (arrE ++ "e ≜ {(∗,(1,2) 3)}\n") 2 "the rows of a literal nest alike: found 3, expected the form of (1, 2)"
#guard errAt (arrE ++ "e ≜ {(∗,[1,2])}\n") 2 "the elements of an array are separated by spaces, not ','"

/-! Signed numbers (§a, §c): a range `-3…3`, signed literal words, `succ ≤ <` and the value verbs on it, each
    against Lean's `Int` (`div` floors and `mod` takes the divisor's sign, as q's: `Int.fdiv`, `Int.fmod`); a print
    lists numbers by value. -/

def zs : List Int := (List.range 7).map fun k : Nat => (k : Int) - 3
rel_program signed after Programs.prelude where
    obj Z = -3…3
    obj K = {a,b}
    x : K ⟶ Z ≜ {(a,-1),(b,2),(a,-3)} -- a comment, after a signed literal
    print x
    print Λ(x)
    print x − {(a,-3)}
    print {(-1,-1)}−{(2,2)}
    s : Z ⟶ Z ≜ 𝟙(Z) succ
    le : Z ⟶ Z ≜ 𝟙(Z) ≤
    lt : Z ⟶ Z ≜ 𝟙(Z) <
    W : Z×Z ⟶ Z×Z ≜ 𝟙(Z×Z)
    pl : Z×Z ⟶ Z ≜ W plus
    tm : Z×Z ⟶ Z ≜ W times
    mi : Z×Z ⟶ Z ≜ W minus
    dv : Z×Z ⟶ Z ≜ W div
    md : Z×Z ⟶ Z ≜ W mod
    mx : Z×Z ⟶ Z ≜ W max
    mn : Z×Z ⟶ Z ≜ W min

def sameSet {α : Type} [BEq α] (a b : List α) : Bool := a.all b.contains && b.all a.contains
def ints (R : Rel .long .long) : List (Int × Int) := R.toList.map fun (a, b) => (a.toInt, b.toInt)

#guard signed.ok
#guard signed.prints == ["x = {(a, -3), (a, -1), (b, 2)}", "Λ(x) = {(a, -3 -1), (b, [2])}",
  "x − {(a, -3)} = {(a, -1), (b, 2)}", "{(-1, -1)} − {(2, 2)} = {(-1, -1)}"]
-- `succ` at `-1` gives `0`, at the top `3` nothing; `≤`, `<` the numeric order
#guard (get signed.expanded "s" .long .long).map ints == some ((zs.filter (· < 3)).map fun a => (a, a + 1))
#guard [("le", fun (a b : Int) => decide (a ≤ b)), ("lt", fun a b => decide (a < b))].all fun (n, f) =>
  match get signed.expanded n .long .long with
  | some R => sameSet (ints R) ((zs.flatMap fun a => zs.map (a, ·)).filter fun (a, b) => f a b)
  | none => false
-- each verb on every pair of `Z`: a row exactly where the result is in `Z` and the divisor is not `0`
#guard [("pl", fun (a b : Int) => some (a + b)), ("tm", fun a b => some (a * b)), ("mi", fun a b => some (a - b)),
    ("dv", fun a b => if b == 0 then none else some (a.fdiv b)),
    ("md", fun a b => if b == 0 then none else some (a.fmod b)),
    ("mx", fun a b => some (max a b)), ("mn", fun a b => some (min a b))].all fun (n, f) =>
  match get signed.expanded n (.prod .long .long) .long with
  | some R => sameSet (R.toList.map fun ((a, b), c) => ((a.toInt, b.toInt), c.toInt))
      ((zs.flatMap fun a => zs.map (a, ·)).filterMap fun (a, b) =>
        (f a b).bind fun c => if zs.contains c then some ((a, b), c) else none)
  | none => false
-- `-5…-1` is a range; `3…-3` is empty, refused at its last number; a word other than a number is no range bound
rel_program negRange after Programs.prelude where
    obj Z = -5…-1
    print 𝟙(Z) succ
#guard negRange.prints == ["𝟙(Z) succ = {(-5, -4), (-4, -3), (-3, -2), (-2, -1)}"]
#guard match elabErr (Parse.parse "obj X = {A}\nobj Z = 3…-3\n") with
  | some e => e.pos.line == 2 && e.pos.col == 11 && e.msg == "the range 3…-3 is empty: -3 is below 3"
  | none => false
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

rel_program chs after Programs.prelude where
    obj Ch = {a,b}
    obj N = 0…3
    x : 1 ⟶ [Ch] ≜ {(∗,a b)}
    y : 1 ⟶ [Ch] ≜ {(∗,a a b)}
    ns : 1 ⟶ [N] ≜ {(∗,2 3)}
    ms : 1 ⟶ [N] ≜ {(∗,3 1 2)}
    ks : 1 ⟶ [N] ≜ {(∗,3 1 1)}
    ok : α×[α] ⟶ α×[α] ≜ cor(≤/∋)

/-- The text `src` read after `chs`: its error, at its line in `src`. -/
def chsErr (src : String) (line : Nat) (what : String) : Bool :=
  match elabErr (extend chs src) with
  | some e => e.pos.line == line && (e.msg.splitOn what).length > 1
  | none => false

-- the converse: `(RS)° = S°R°`, `∩`, a pair with one side's converse, `R°° = R`, a coreflexive, `cons° = uncons`
rel_program chsConv after chs where
    print x cons° (perm cons°)°
    print x (perm ∩ perm)° cons°
    print x ⟨cons°π₁, perm⟩°° π₂
    print x (dom(π₁{(a,a)}) cons)°
    print x (dom(π₁{(b,b)}) cons)°
#guard printed chsConv.prints ==
  ["{(∗, a b), (∗, b a)}", "{(∗, (a, [b])), (∗, (b, [a]))}", "{(∗, a b), (∗, b a)}",
   "{(∗, (a, [b]))}", "{}"]
-- refused at a leaf whose converse does not run on demand: `π₁` in `⟨π₁,π₂⟩°`, `∋` in `∈`
#guard chsErr "print x (cons° ⟨π₁,π₂⟩ cons)°\n" 1 "the converse of π₁ does not run on demand"
#guard chsErr "print {(∗,a)} ∈\n" 1 "the converse of ∋ does not run on demand"
-- a division tested on the pairs: `R/S`, `R\S`, `frac`, `∼`, `−`, each beside a term run on demand
rel_program chsDiv after chs where
    print ⟨{(∗,1)},ns⟩ok
    print ⟨{(∗,3)},ns⟩ok
    print ⟨{(∗,2)},ns⟩ok
    print ms (∋ ∩ (cons\(π₁ ≤)))
    print ks (subseq ∩ frac(∋,∋))
    print ⟨{(∗,3)},ns⟩(π₂ ∩ (π₁∼(≤/∋)))
    print ⟨{(∗,1)},ns⟩(π₂ ∩ (π₁∼(≤/∋)))
    print ⟨{(∗,3)},ns⟩(π₂ − (π₁(≤/∋)))
#guard printed chsDiv.prints ==
  ["{(∗, (1, 2 3))}", "{}", "{(∗, (2, 2 3))}", "{(∗, 3)}", "{(∗, 3 1), (∗, 3 1 1)}",
   "{(∗, 2 3)}", "{}", "{(∗, 2 3)}"]
-- refused: a division with no term on demand to test it against, and a meet of two
#guard chsErr "print {(∗,1)}(≤/∋)\n" 1 "R/S reads its operands whole"
#guard chsErr "print {(∗,1)}((≤/∋) ∩ (≤/∋))\n" 1 "R/S reads its operands whole"
-- `R×S` on demand as `⟨π₁R,π₂S⟩`; closed, as before
rel_program chsProd after chs where
    print ⟨{(1,1)},⟨{(1,2)},Λ({(1,1)})⟩⟩(𝟙×π₁)plus
    print y cons°(𝟙×perm)
    print ⟨x,{(∗,b)}⟩(perm×𝟙)
    print {(1,1)}×{(2,3)}
#guard printed chsProd.prints ==
  ["{(1, 3)}", "{(∗, (a, a b)), (∗, (a, b a))}", "{(∗, (a b, b)), (∗, (b a, b))}", "{((1, 2), (1, 3))}"]
-- refused: an operand that does not run, named; the object printed as the program writes it, `[Ch]`
#guard chsErr "print ⟨{(∗,a)},{(∗,b)}⟩(∈×𝟙)\n" 1 "the converse of ∋ does not run on demand"
#guard chsErr "print ⟨{(∗,a)},{(∗,b)}⟩(∈×𝟙)\n" 1 "[Ch] has no universe"
-- `loop(F)` runs `F` on the pairs each round meets: a state that is an array (a copy, a reverse, the
-- subsequences), and a pair with an array (the copy with its length)
rel_program chsLoop after chs where
    print x ⟨nil,𝟙⟩loop(snoc)
    print y ⟨nil,𝟙⟩loop(⟨π₂,π₁⟩cons)
    print x ⟨nil,𝟙⟩loop(snoc ∪ π₁)
    print x ⟨⟨nil,⊤{(0,0)}⟩,𝟙⟩loop(⟨⟨π₁π₁,π₂⟩snoc,π₁π₂ succ⟩)
#guard printed chsLoop.prints ==
  ["{(∗, a b)}", "{(∗, b a a)}", "{(∗, []), (∗, [a]), (∗, a b), (∗, [b])}", "{(∗, (a b, 2))}"]
-- refused: an `F` that runs neither way, the leaf named
#guard chsErr "print x ⟨nil,𝟙⟩loop(snoc ran(snoc))\n" 1 "ran( ) reads its argument whole: [Ch]×Ch has no universe"

/-! The prelude (§c): each definition moved there against the builtin it replaced (`Alg.perm`, `Alg.ordered`, and
    `sort(Q) = perm ordered(Q)`), on a repeated element, the empty array, two element objects and arrays of arrays;
    the converses; the declared infix operators; the errors. -/

rel_program pre after Programs.prelude where
    obj N = 0…9
    obj K = {a,b,c,d}
    obj Ch = {p,q}
    x : K ⟶ [N] ≜ {(a,3 1 2),(b,2 1 2),(c,[]),(d,[5])}
    le : N ⟶ N ≜ 𝟙(N) ≤
    pm : K ⟶ [N] ≜ x perm
    od : K ⟶ [N] ≜ x ordered(≤)
    st : K ⟶ [N] ≜ x sort(≤)
    y : K ⟶ [Ch] ≜ {(a,p q p),(b,[])}
    py : K ⟶ [Ch] ≜ y perm
    z : K ⟶ [[N]] ≜ {(a,[1 2] [3] []),(b,[] [])}
    pz : K ⟶ [[N]] ≜ z perm

def same {A B : Obj} (R S : Rel A B) : Bool := R ⊑ S && S ⊑ R
def is {B : Obj} (gs : List (String × Gen.Gv)) (n : String) (R : Rel .long B) : Bool :=
  ((get gs n .long B).map (same · R)).getD false

#guard let o := pre.expanded
  match get o "x" .long (.arr .long), get o "le" .long .long with
  | some X, some Le =>
    let U := (Alg.ran X).val; let P := Alg.perm U
    is o "pm" (X ≫ P) && is o "od" (X ≫ Alg.ordered Le U) && is o "st" (X ≫ P ≫ Alg.ordered Le (Alg.ran P).val)
  | _, _ => false
#guard let o := pre.expanded
  match get o "y" .long (.arr .long), get o "z" .long (.arr (.arr .long)) with
  | some Y, some Z => is o "py" (Y ≫ Alg.perm (Alg.ran Y).val) && is o "pz" (Z ≫ Alg.perm (Alg.ran Z).val)
  | _, _ => false

-- the converses: `perm° = perm` (the one rule kept for a definition), `ordered(Q)` a coreflexive, and
-- `sort(Q)° = ordered(Q)° perm°` from them
rel_program converses after Programs.prelude where
    obj N = 0…9
    x : 1 ⟶ [N] ≜ {(∗,1 2 3)}
    print x perm°
    print x ordered(≤)°
    print x sort(≤)°
    print {(∗,3 1 2)} sort(≤)°
#guard printed converses.prints ==
  ["{(∗, 1 2 3), (∗, 1 3 2), (∗, 2 1 3), (∗, 2 3 1), (∗, 3 1 2), (∗, 3 2 1)}", "{(∗, 1 2 3)}",
   "{(∗, 1 2 3), (∗, 1 3 2), (∗, 2 1 3), (∗, 2 3 1), (∗, 3 1 2), (∗, 3 2 1)}", "{}"]

-- a declared infix operator: `R + S = ⟨R,S⟩plus`, the prelude's `⇒` and `⊕`, a program's own `_≼_`, each read at
-- the one level with `∩`, left to right
rel_program infixes after Programs.prelude where
    obj N = 0…9
    w : N×N ⟶ N×N ≜ {((2,3),(2,3)),((4,1),(4,1))}
    print w(π₁ + π₂)
    check w(π₁ + π₂) = w⟨π₁,π₂⟩plus
    _≼_(R : α ⟶ β, S : β ⟶ α) : α ⟶ β ≜ R ∩ S°
    print {(1,1),(2,2)}(≤ ≼ ≤)
    print {(1,1)}(≤ ≼ ≤ ∪ <)
    print {(1,1)}(< ∪ 𝟙(N) ≼ ≤)
    print {(1,1)}(𝟙(N) ∩ {(1,2)} ⇒ <)
    print {(1,1)}inl(N,N+N)(𝟙 ⊕ succ)
#guard infixes.ok && printed infixes.prints ==
  ["{((2, 3), 5), ((4, 1), 5)}", "{(1, 1), (2, 2)}",
   "{(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9)}", "{(1, 1)}",
   "{(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9)}", "{(1, inl 1)}"]
#guard ["R ⇒ S", "R ⊕ S", "R + S", "frac(R, S)", "∈", "perm", "ordered(R)", "sort(R)", "cor(R)"].all trip
-- `cor(R)`: the pairs of `R` as a coreflexive on `A×B`
rel_program corPairs after Programs.prelude where
    obj N = 0…3
    print {((1,2),(1,2)),((2,1),(2,1)),((3,3),(3,3))}cor(≤)
#guard printed corPairs.prints == ["{((1, 2), (1, 2)), ((3, 3), (3, 3))}"]
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
/-- The text `src` read after the prelude `pre`: its error. -/
def afterErr (pre : Except Err Program) (src : String) : Option Err :=
  match pre >>= fun p => Parse.parseIn (Parse.scope p) src >>= Expand.read (some p) [] with
  | .error e => some e | .ok _ => none
#guard match afterErr (Parse.parseIn { cs := #[] } "    f ≜ g\n") "obj X = {A}\n" with
  | some e => toString e == "in the prelude, line 1, col 9: unknown name 'g'"
  | none => false
#guard match afterErr (Parse.parseIn { cs := #[] } "    f(R : α ⟶ β) : α ⟶ β ≜ R g\n")
    "obj X = {A}\nx : X ⟶ X ≜ {(A,A)}\ny : X ⟶ X ≜ f(x)\n" with
  | some e => e.pos.line == 3 && e.msg == "in the prelude's `f` (its line 1): unknown name 'g'"
  | none => false

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
rel_program closure after Programs.prelude where
    obj N = 0…4
    R : N ⟶ N ≜ {(0,1),(1,2),(2,3)}
    c : N ⟶ N ≜ μX : 𝟙 ∪ (R X)
    check c = {(0,0),(1,1),(2,2),(3,3),(4,4),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)}
#guard closure.ok
-- the points with an infinite `R`-path: the rounds from `𝟙` written out, which stop changing at the second
rel_program infPath after Programs.prelude where
    obj N = 0…5
    R : N ⟶ N ≜ {(0,1),(1,2),(2,0),(3,4)}
    v : N ⟶ N ≜ νX : 𝟙(N) ∩ dom(R X)
    x₁ : N ⟶ N ≜ 𝟙(N) ∩ dom(R 𝟙(N))
    x₂ : N ⟶ N ≜ 𝟙(N) ∩ dom(R x₁)
    x₃ : N ⟶ N ≜ 𝟙(N) ∩ dom(R x₂)
    check v = x₂
    check x₃ = x₂
    check v = {(0,0),(1,1),(2,2)}
#guard infPath.ok
-- arc consistency on `y = x²` with both arcs, `x → y` by `sq` and `y → x` by `sq°`
rel_program square after Programs.prelude where
    obj V = {x,y}
    obj D = 0…9
    A : V ⟶ V ≜ {(x,y)}
    Ac : V ⟶ V ≜ A°
    sq : D ⟶ D ≜ {(0,0),(1,1),(2,4),(3,9)}
    sqc : D ⟶ D ≜ sq°
    uV : V ⟶ V ≜ 𝟙(V)
    uD : D ⟶ D ≜ 𝟙(D)
    revise(A : α ⟶ α, C : β ⟶ β, X : α ⟶ β) : α ⟶ β ≜ A\(X C)
    s : V ⟶ D ≜ ⊤(V,D)
    z : V ⟶ D ≜ νZ : s ∩ revise(A,sq,Z) ∩ revise(A°,sq°,Z)
    check z = {(x,0),(x,1),(x,2),(x,3),(y,0),(y,1),(y,4),(y,9)}
#guard square.ok
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

/-- An AC-3 body read from the definitions `gs`: the bound `s`, the arcs `(A, C)` by name, the universes `uv`,
    `ud`. -/
def acOf (gs : List (String × Gen.Gv)) (s uv ud : String) (arcs : List (String × String)) :
    Option ((V : Obj) × (D : Obj) × Rel V D × Rel V V × List (Revise V D)) := do
  let (_, ⟨V, D, sR⟩) ← gs.find? (·.1 == s)
  let UV ← get gs uv V V; let UD ← get gs ud D D
  let as ← arcs.mapM fun (a, c) => return (⟨← get gs a V V, ← get gs c D D, UV, UD⟩ : Revise V D)
  pure ⟨V, D, sR.rel, UV, as⟩

/-- The language's `z`, the delta rounds and the naive rounds give one relation. -/
def acAgree (gs : List (String × Gen.Gv)) (z s uv ud : String) (arcs : List (String × String)) : Bool :=
  match acOf gs s uv ud arcs with
  | some ⟨V, D, s, U, as⟩ =>
    let d := (acFix s as U).1; let n := (fixOn (s.n.toNat + 1) (acRound s as) s).1
    d == n && (get gs z V D).any (· == d)
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
def acTraces (gs : List (String × Gen.Gv)) (s uv ud : String) (arcs : List (String × String)) :
    List (Nat × Nat × Nat) × List (Nat × Nat × Nat) :=
  match acOf gs s uv ud arcs with
  | some ⟨_, _, s, U, as⟩ => (deltaTrace as (s.n.toNat + 1) s.nub U, naiveTrace s as U (s.n.toNat + 1) s.nub)
  | none => ([], [])

rel_program sudokuEx after Programs.sudokuac where
    uV : Cell ⟶ Cell ≜ 𝟙(Cell)
    uD : D ⟶ D ≜ 𝟙(D)
    ne : D ⟶ D ≜ ≠

/-- `sudokuac`'s definitions and the universes and order `sudokuEx` adds. -/
def sudokuGs : List (String × Gen.Gv) := sudokuEx.expanded ++ Programs.sudokuac.expanded

#guard acAgree sudokuGs "s" "s₀" "uV" "uD" [("peer", "ne")]
#guard acAgree square.expanded "z" "s" "uV" "uD" [("A", "sq"), ("Ac", "sqc")]
-- SudokuAC, both 11 rounds, 489 → 81 rows: the delta rounds join 39780 rows in all, the naive ones 148200
#guard acTraces sudokuGs "s₀" "uV" "uD" [("peer", "ne")] ==
  ([(81, 13980, 183), (81, 9100, 163), (81, 3140, 142), (80, 3640, 122), (80, 3120, 113), (68, 1520, 107),
    (71, 1020, 103), (42, 680, 93), (65, 1660, 83), (73, 1600, 81), (34, 320, 81)],
   [(81, 13980, 183), (81, 13900, 163), (81, 13800, 142), (81, 13660, 122), (81, 13540, 113), (81, 13440, 107),
    (81, 13380, 103), (81, 13340, 93), (81, 13200, 83), (81, 13000, 81), (81, 12960, 81)])

end LeetQ.Rel.Lang.Test
