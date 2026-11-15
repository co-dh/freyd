import LeetQ.Rel.Programs.Blocks
import LeetQ.Rel.Programs.SudokuAC
import LeetQ.Rel.AC3

/-! The Rel language on the blocks world of `doc/rel-lang-design.md` §g, the program `Programs.blocks`; its
    front-end errors; the round trip of `rel_program`'s grammar on every operator of §b. Every program runs as its
    expansion (`rel_program`, `Expand`): its definitions `n.expanded`, its prints `n.prints`, its checks and ok bits
    `n.failures`, `n.ok`; a front-end error is read off statements by `Expand.read`, which evaluates nothing. -/

namespace LeetQ.Rel.Lang.Test

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Alg QLean

-- the prelude's definitions type-check
#eval show Lean.Meta.MetaM Unit from do match ← (typesOf none).run with | .error e => throwError "{e}" | .ok _ => pure ()
#guard Programs.prelude.ok

abbrev CM := Lean.Elab.Command.CommandElabM

/-- The scope of a text read after the prelude outside any Lean scope: its names unqualified (`Parse.openAll`). -/
def preludeScope : Parse.S := { cs := #[], res := Parse.openAll [(`LeetQ.Rel.Programs.prelude, Programs.prelude)] }

/-- The statements `src` read as a `rel_program`'s (`Embed`, the one grammar) in the scope `s`, nothing elaborated;
    they start on the line of `where`, so a line of `src` is a line of the error. A Lean parse error has no line. -/
def readIn (s : Parse.S) (src : String) : CM (Except Err Program) := do
  let txt := "rel_program t where " ++ src
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command txt with
  | .ok stx => pure ((Embed.program (Lean.FileMap.ofString txt) s stx[4].getArgs).map (·.1))
  | .error e => pure (.error ⟨default, e⟩)

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

open LeetQ.Rel.Programs.prelude Programs.blocks in
rel_program given where
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

open LeetQ.Rel.Programs.prelude Programs.blocks in
/-- `Λ(S)est(P)`, `Λ(S)thin(P)` with the order `P` a family (the rows of §e on `S∋`) against the order closed
    (the closed row), on the reachable states — `est` of a map is the map — and on their complements, where a
    block has two values. -/
rel_program orders where
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

open LeetQ.Rel.Programs.prelude Programs.blocks in
/-- A body given families of two indices, `∋` at `St` and `ζ∋` at `N` (the `k`-th state's pairs), runs at
    `St×N`: the fibre at `(s,k)` is `s ∩ ζ(k)`. Against the same meet written by hand, and at `(s₀,0)`, `(s₀,1)`. -/
rel_program twoIdx where
    k(S : X ⟶ X, T : X ⟶ X) : X ⟶ X ≜ S ∩ T
    check (Q×𝟙(N))k(∋,ζ∋) = (Q×𝟙(N))⟨π₁∋,π₂ζ∋⟩cor(𝟙)π₁
    print (s₀×{(0,0)})k(∋,ζ∋)
    print (s₀×{(1,1)})k(∋,ζ∋)

open LeetQ.Rel.Programs.prelude in
/-- `X⦇e,S⦈` given a family (§e): at each key of a three-key family, the fibre of the lifted fold is the fold of
    the fibre. `p(R)` holds the pairs `(a,b)` with `b` at most two steps of `R` from `a`. -/
rel_program foldLaw where
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

open LeetQ.Rel.Programs.prelude in
/-- A lifted fold whose step has closed parts (§e, cost of the keyed fold): `G`, `∼R ∩ G` (a complement, so
    `⊤`), `dom(R)`, `π₂⟨π₁,π₁⟩`, each keyed on the pairs a round meets; at every key the fibre is the fold of
    the fibre. -/
rel_program foldClosed where
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

open LeetQ.Rel.Programs.prelude in
/-- Object variables (§e): `uq : α ⟶ β` at `X ⟶ N` and at `N ⟶ X` against the ground copies `uX`, `uN`; and
    `d : α ⟶ α` given `Fm : K ⟶ X×X`, which `α ⟶ α` reads as a family, against `d` of each fibre. -/
rel_program objVars where
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

open LeetQ.Rel.Programs.prelude in
/-- The order of `est thin thinL` given as a converse `Q°` against the converse written by hand: a builtin
    (`≤°`, `≥`), a parametrised definition applied then conversed (`R(rating)°`), and a monomorphic one (`R₀°`). -/
rel_program estConv where
    obj E = {a,b,c}
    obj N = 0…20
    rating : E ⟶ N ≜ {(a,3),(b,7),(c,2)}
    H : E ⟶ [E] ≜ {(a,a b),(a,b c),(a,a c),(b,b c),(b,a b)}
    Hn : N ⟶ N ≜ {(1,3),(1,5),(2,4),(2,9)}
    cost(r : α ⟶ β) : [α] ⟶ β ≜ F(r)sum
    R(r : α ⟶ β) : [α] ⟶ [α] ≜ cost(r) ≤ cost(r)°
    Rc(r : α ⟶ β) : [α] ⟶ [α] ≜ cost(r) ≥ cost(r)°
    c₀ : [E] ⟶ N ≜ F(rating)sum
    R₀ : [E] ⟶ [E] ≜ c₀ ≤ c₀°
    R₀c : [E] ⟶ [E] ≜ c₀ ≥ c₀°
    check Λ(Hn)est(≤°) = Λ(Hn)est(≥)
    check Λ(Hn)thin(≤°) = Λ(Hn)thin(≥)
    check Λ(H)est(R(rating)°) = Λ(H)est(Rc(rating))
    check Λ(H)thin(R(rating)°) = Λ(H)thin(Rc(rating))
    check Λ(H)est(R₀°) = Λ(H)est(R₀c)
    check Λ(H)thin(R₀°) = Λ(H)thin(R₀c)
    check Λ(H)thinL(R₀°) = Λ(H)thinL(R₀c)
    check Λ(H)est(R₀) = Λ(H)est(R(rating))
    print Λ(Hn)est(≤°)
    print Λ(H)est(R(rating)°)
    print Λ(H)est(R(rating))

-- `R°` picks the greatest cost (`a b`, 10), `R` the least (`a c`, 5)
#guard estConv.ok && estConv.prints == [
  "Λ(Hn) est(≤°) = {(1, 5), (2, 9)}", "Λ(H) est(R(rating)°) = {(a, a b), (b, a b)}",
  "Λ(H) est(R(rating)) = {(a, a c), (b, b c)}"]

open LeetQ.Rel.Programs.prelude Programs.blocks in
rel_program printPlan where
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
def elabErr (prog : Except Err Program) : Lean.Meta.MetaM (Option Err) := do
  match prog with
  | .error e => pure (some e)
  | .ok p => match ← (Expand.read (fun _ => none) [(`LeetQ.Rel.Programs.prelude, Programs.prelude)] p).run with
    | .error e => pure (some e)
    | .ok _ => pure none

/-- The statements `src` read after the prelude and `prog` fail at `line` (and `col`, when given) with `what` in the
    message. -/
def errAt (src : String) (line : Nat) (what : String) (col : Option Nat := none) (prog : Program := []) :
    CM Unit := do
  let r ← readIn (Parse.after (preludeScope) prog) src
  match ← Lean.Elab.Command.liftTermElabM (elabErr (r.map (prog ++ ·))) with
  | some e => unless e.pos.line == line && col.all (· == e.pos.col) && (e.msg.splitOn what).length > 1 do
      throwError "expected an error at line {line} with '{what}', got {e}"
  | none => throwError "expected an error at line {line} with '{what}', got none"

-- unknown name
#eval errAt "obj X = {A,B,C}\nf : X ⟶ X ≜ {(A,B)}\ng ≜ fh\n" 3 "unknown name 'h'"
-- type mismatch
#eval errAt "obj X = {A,B,C}\nobj N = 0…3\na : X ⟶ X ≜ {(A,B)}\nb : N ⟶ N ≜ {(1,2)}\nf ≜ ab\n" 5
  "found N, expected X"
-- a family given where the row is not liftable
#eval errAt "obj X = {A,B,C}\nobj St = 𝒫(X×X)\nL(S : X ⟶ X) : X ⟶ X ≜ ⦇S,S⦈\nf : St ⟶ X×X ≜ L(∋)\n" 3
  "not liftable"
-- a term that needs a universe its object does not have
#eval errAt "obj X = {A,B,C}\nobj St = 𝒫(X×X)\nprint ⊤(St,X)\n" 3 "has no universe"
-- a definition or parameter taking a builtin's name, or a name already defined or declared
#eval errAt "obj B = 0…1\nq : α×β ⟶ α ≜ π₁\nπ₂ ≜ π₁π₁\n" 3 "`π₂` is a builtin"
#eval errAt "obj B = 0…1\nf(S : B ⟶ B, E : B ⟶ B) : B ⟶ B ≜ S ∩ E\n" 2 "`E` is a builtin"
#eval errAt "obj B = 0…1\nK : α×β ⟶ α ≜ π₁\nq : α×β ⟶ α ≜ K\nK ≜ π₂\n" 4 "`K` is already defined at line 2"
#eval errAt "obj B = 0…1\nB ≜ π₁\n" 2 "`B` is already defined at line 1"
-- an object variable met at two objects, in one parameter's type or across two; a defined name is no variable
#eval errAt "obj X = {A,B,C}\nobj N = 0…3\nf(R : α ⟶ α) : α ⟶ α ≜ R\ng ≜ f({(A,1)})\n" 4
  "`α` in the type of 'R' is both X and N"
#eval errAt "obj X = {A,B,C}\nobj N = 0…3\nh(R : α ⟶ X, S : α ⟶ X) : α ⟶ X ≜ R\ng ≜ h({(A,B)},{(1,B)})\n" 4
  "`α` in the type of 'S' is both X and N"
#eval errAt "obj X = {A,B,C}\nπ : X ⟶ X ≜ 𝟙(X)\nf(R : π ⟶ π) ≜ R\n" 3 "expected an object, found 'π'"
-- a `where` item taking a defined name, a parameter's, an earlier item's or a builtin's; an item used outside
#eval errAt "obj B = 0…1\nK : α×β ⟶ α ≜ π₁\nf ≜ a where a ≜ π₂, K ≜ π₁\n" 3 "`K` is already defined at line 2"
#eval errAt "obj B = 0…1\nf(S : B ⟶ B) : B ⟶ B ≜ a where a ≜ S, S ≜ π₁\n" 2 "`S` is already a parameter of `f`"
#eval errAt "obj B = 0…1\nf : α×β ⟶ β ≜ a where a ≜ π₂, a ≜ π₁\n" 2 "`a` is already an item"
#eval errAt "obj B = 0…1\nf : α×β ⟶ β ≜ a where a ≜ π₂, π₁ ≜ a\n" 2 "`π₁` is a builtin"
#eval errAt "obj B = 0…1\nf : α×β ⟶ β ≜ a where a ≜ π₂\ng ≜ a\n" 3 "unknown name 'a'"

/-! The parser's round trip: each operator row of §b, printed as it was read. -/

/-- The term `s` read after the prelude with `R S p e` and the object `X` in scope, printed by `out`. -/
def parsed (s : String) (out : Expr → String) : CM String := do
  let sc := preludeScope
  match ← readIn { sc with known := [("R", 0), ("S", 0), ("p", 0), ("e", 0)] ++ sc.known, objs := "X" :: sc.objs }
      ("print " ++ s) with
  | .ok [.print _ e] => pure (out e)
  | .ok _ => throwError "'{s}' is no one term"
  | .error e => throwError "'{s}': {e}"
/-- Each `s` of `ss` reads back as itself. -/
def trips (ss : List String) : CM Unit := ss.forM fun s => do
  let r ← parsed s Expr.show
  unless r == s do throwError "'{s}' reads back as '{r}'"
/-- Each `s` reads as its `r`, every composite and infix term of `r` in parentheses (§c: one level, left to right). -/
def readsAll (ps : List (String × String)) : CM Unit := ps.forM fun (s, r) => do
  let q ← parsed s (·.render 0 true)
  unless q == r do throwError "'{s}' reads as '{q}', not '{r}'"

#eval trips ["R S", "R°", "R ∩ S", "R ∪ S", "R − S", "∼R", "R ⇒ S", "𝟘", "⊤", "𝟙", "⊤(X, X)", "𝟙(X)", "dom(R)",
  "ran(R)", "R \\ S", "R / S", "frac(R, S)", "⟨R, S⟩", "π₁", "π₂", "R × S", "[R, S]", "inl", "inr", "R + S",
  "Λ(R)", "∋", "∈", "E(R)", "P(R)", "τ", "nil", "α", "cons°", "⦇e, S⦈", "F(R)", "est(R)", "thin(R)",
  "filter(p)", "takewhile(p)", "length", "sum", "head", "tail", "suffix", "succ", "plus", "≤", "<",
  "{(A, B), (B, A)}", "R ∪ S R", "R S ∪ R", "R ∩ S ∪ R", "R ∪ S ∩ R", "R ∪ (S R)", "R (S p)", "∼(R S)°",
  "(∼R)°", "∼R S", "{((A, B), A), ((B, A), B)}", "{(A, (B, (A, B)))}"]
-- `prefix` is a Lean keyword, written in Lean's escape
#eval readsAll [("«prefix»", "prefix")]
-- and written bare
#eval readsAll [("prefix", "prefix"), ("suffix prefix", "(suffix prefix)")]

open LeetQ.Rel.Programs.prelude in
open LeetQ.Rel.Programs.prelude in
/-- Lean keywords as Rel names in a program, bare: one defined (`do`), one used (`prefix`); a Lean command that starts
    with a keyword (`example`) still ends the program. -/
rel_program kwNames where
    do : [α] ⟶ [α] ≜ suffix prefix
example : True := trivial
#guard kwNames.ok

#eval trips ["inits", "tails", "cat", "cat°", "zip", "snoc", "snoc°", "init", "concat", "perm", "setify", "asc", "distinct",
  "subseq", "tic", "ordered(R)", "sort(R)", "thinL(R)", "merge(R)", "loop(R)", "R inits concat", "⟨R, S⟩ merge(p)"]

/-! The list builtins of §b on arrays built by `Λ` and `cons`, each value as `Algebra.lean`'s guard of the op
    states it: `x` is `a ↦ [3 1 2]`, `b ↦ [1 5]`; `y` is `a ↦ [7]`, `b ↦ [8 9]`; `z` is `a ↦ [3 3 1 2]`. -/
open LeetQ.Rel.Programs.prelude in
rel_program lists where
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
    print z asc
    print z distinct
    print z distinct asc
    print ⟨{(a,b)}, Λ({(a,a),(a,b)})⟩cons asc
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
  "z asc = {(a, 1 2 3 3)}",
  "z distinct = {(a, 3 1 2)}",
  "z distinct asc = {(a, 1 2 3)}",
  "⟨{(a, b)}, Λ({(a, a), (a, b)})⟩ cons asc = {(a, a b b)}",
  "x ordered(≤) = {(b, 1 5)}",
  "x sort(≤) = {(a, 1 2 3), (b, 1 5)}",
  "y subseq = {(a, []), (a, [7]), (b, []), (b, [8]), (b, 8 9), (b, [9])}",
  "x thinL(≤) = {(a, [1]), (b, [1])}",
  "⟨Λ({(a, 1), (a, 5)}), Λ({(a, 2), (a, 3)})⟩ merge(≤) = {(a, 1 2 3 5), (b, [])}",
  "⟨{(a, 0), (b, 1)}, x⟩ loop(plus) = {(a, 6), (b, 7)}",
  "⟨{(a, 5)}, Λ({(a, 1), (a, 2)})⟩ tic = {(a, [5] [5 1] [5 1 2])}"]

/-! `at(i)`, positions from `0`, on the arrays `x` above: `at(0) = head`, `tail at(i) = at(i+1)`, and a position
    past every array's end the empty relation. -/
#eval trips ["at(0)", "at(12)", "R at(2) S"]
open LeetQ.Rel.Programs.prelude in
rel_program ats where
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
#eval errAt "obj N = 0…9\nf : [N] ⟶ N ≜ at(x)\n" 2 "at( ) takes a position, a number from 0, found 'x'"
#eval errAt "obj N = 0…9\nf : [N] ⟶ N ≜ at(-1)\n" 2 "at( ) takes a position from 0 that fits a long, found -1"

open LeetQ.Rel.Programs.prelude in
/-- A list builtin in a lifted body takes the closed row (§e): at each key of a two-key family the fibre of the
    lifted body is the body on the fibre. -/
rel_program listsLifted where
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

open LeetQ.Rel.Programs.prelude in
/-- Orders on demand (§a): each operator runs its order on the pairs it compares, here `R ≜ length ≤ length°` on
    `[N]`, which has no universe; a closed order as before; and `∼R`, tested as the complement of `R`'s test. -/
rel_program onDemand where
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
#eval errAt ("obj N = 0…9\nobj K = {a,b}\nL : K ⟶ [[N]] ≜ {(a,[1 2] [3])}\n" ++
  "S : [N] ⟶ [α] ≜ ran(𝟙([N])) length ≤(N,N) length°\nprint L sort(S)\n") 5
  "⊤'s target: [N] has no universe"

/-! The kernel's value verbs of §b on pairs of numbers, each `Alg.arith` with its opcode: a result outside the
    declared object has no row (`minus` below `0`, as `succ` at the top), nor a zero divisor. -/

open LeetQ.Rel.Programs.prelude in
rel_program arith where
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

#eval trips ["plus", "times", "minus", "div", "mod", "max", "min", "⟨R, S⟩ times", "R mod°"]

open LeetQ.Rel.Programs.prelude in
/-- A value verb in a lifted body takes the closed row (§e): at each key the fibre is the body on the fibre. -/
rel_program arithLifted where
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

open LeetQ.Rel.Programs.prelude in
/-- B&dM's digits of a number (`val_converse_eq`): `op°`, the converse of `op(n,d) = 10n+d` on a digit `d`,
    taken from `x` once a round until it reaches `0`, each digit put on the front of the list. The rounds `K`
    hold no number of `N`, so a literal's words name one object (§c). -/
rel_program digits where
    obj N = 0…199
    obj K = 200…203
    ten : N ⟶ N ≜ ⊤(N,N){(10,10)}
    dg : N ⟶ N ≜ dom(<{(10,10)})
    op : N×N ⟶ N ≜ ⟨⟨π₁,π₁ ten⟩times,π₂ dg⟩plus
    x : N ⟶ N ≜ {(107,107)}
    r : N ⟶ [K] ≜ xΛ(⊤(N,K))
    nz : N ⟶ N ≜ 𝟙(N) − {(0,0)}
    step : N×[N] ⟶ N×[N] ≜ ⟨π₁{(0,0)},π₂⟩ ∪ ⟨π₁ nz op° π₁,⟨π₁ nz op° π₂,π₂⟩cons⟩
    ds : N ⟶ [N] ≜ r⦇ran(x⟨𝟙,nil⟩),π₂ step⦈π₂
    print ds

#guard digits.ok && digits.prints == ["ds = {(107, 1 0 7)}"]

-- a prelude definition given a family through a typed parameter: the lifted body reaches `perm`, closed on `[N]`
#eval errAt "obj N = 0…3\nobj St = 𝒫(N×N)\nf(S : N ⟶ N) : [N] ⟶ [N] ≜ sort(S)\ng : St ⟶ [N]×[N] ≜ f(∋)\n" 3
  "a closed term in a lifted body: [N] has no universe"

-- a nested literal (§c): each leaf position its own object, the side their product
open LeetQ.Rel.Programs.prelude in
rel_program nested where
    obj X = {A,B}
    obj N = 0…1
    L : X×N ⟶ N×X ≜ {((A,0),(1,B)),((B,1),(0,A))}
    print L
#guard nested.ok && nested.prints == ["L = {((A, 0), (1, B)), ((B, 1), (0, A))}"] &&
  (get nested.expanded "L" (.prod .long .long) (.prod .long .long)).map (·.toList) ==
    some [((0, 0), (1, 1)), ((1, 1), (0, 0))]
#eval errAt "obj X = {A,B}\nL ≜ {((A,B),A),(A,B)}\n" 2 "nest alike"

/-! Declared types (§e). -/

-- a body that is not the declared type; a definition with none, told the type it has
#eval errAt "obj X = {A,B}\nobj N = 0…1\nf : X ⟶ N ≜ 𝟙(X)\n" 3 "`f` is declared X ⟶ N, but its body is X ⟶ X"
#eval errAt "obj X = {A,B}\nf ≜ 𝟙(X)\n" 2 "`f` has no type; it is f : X ⟶ X"
#eval errAt "obj X = {A,B}\nf(R : X ⟶ X) ≜ R°\n" 2 "`f` has no type; it is f(R : X ⟶ X) : X ⟶ X"
-- one generic definition at two objects in one program: its variables instantiated at each use
open LeetQ.Rel.Programs.prelude in
rel_program generic where
    obj X = {A,B}
    obj N = 0…1
    sw : α×β ⟶ β×α ≜ ⟨π₂,π₁⟩
    print {((A,0),(A,0))}sw
    print {((1,B),(1,B))}sw
#guard printed generic.prints == ["{((A, 0), (0, A))}", "{((1, B), (B, 1))}"]
-- the declared type determines an object the body leaves open: `nil`'s source and element
open LeetQ.Rel.Programs.prelude in
rel_program declNil where
    obj N = 0…3
    e : 1 ⟶ [N] ≜ nil
    print e
#guard printed declNil.prints == ["{(∗, [])}"]
-- `typesOf` prints each definition's head as it is declared
def heads : List String := ["f : X ⟶ X", "g(R : α ⟶ β) : β ⟶ α", "_≼_(R : α ⟶ β, S : β ⟶ γ) : α ⟶ γ"]
def headsSrc : String := "obj X = {A,B}\n" ++
  String.join ((heads.zip ["𝟙", "R°", "R S"]).map fun (h, b) => s!"{h} ≜ {b}\n")
#eval do
  let p ← match ← readIn (preludeScope) headsSrc with | .ok p => pure p | .error e => throwError "{e}"
  match ← Lean.Elab.Command.liftTermElabM (typesOf (some p)).run with
  | .ok ts => unless ts == heads do throwError "the heads print as {ts}"
  | .error e => throwError "{e}"
-- a `where` item; a test takes no type of its own
open LeetQ.Rel.Programs.prelude in
rel_program whereItem where
    obj B = 0…1
    f : B×B ⟶ B ≜ a where a ≜ π₂
    print {((0,1),(0,1))}f
#guard printed whereItem.prints == ["{((0, 1), 1)}"]
#eval errAt "obj X = {A,B}\nh(S : X ⟶ X) : X ⟶ X ≜ 𝟙 ⊑ S\n" 2 "the test `h` has no type of its own"

/-! Array literals (§c): two or more items juxtaposed, or `[…]`; an element position is one object over the
    elements of all rows' arrays there, at any depth and on either side; printed as it is read. -/

open LeetQ.Rel.Programs.prelude in
rel_program arrs where
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
#eval trips ["{(∗, 3 1 2)}", "{(∗, [1] [2 3])}", "{((a, 1 2), [3])}", "{(b, [])}", "{(∗, (1, 2) (3, 4))}"]
-- an element position whose arrays are all empty, a word in no object, rows nesting differently, a comma
def arrE : String := "obj N = 0…9\n"
def emptyErr : String := "the object of [] cannot be read off an empty array: write nil(A,[O])"
-- nothing determines the object: the error at the literal
#eval errAt (arrE ++ "print {(∗,[])}\n") 2 emptyErr (col := some 7)
#eval errAt (arrE ++ "print {(∗,[[]] [])}\n") 2 emptyErr (col := some 7)
#eval errAt (arrE ++ "print {(∗,[])} ∪ {(∗,[])}\n") 2 emptyErr (col := some 7)
-- an untyped definition names the type its body has, the object left open a variable
#eval errAt (arrE ++ "e ≜ {(∗,[])}\n") 2 "`e` has no type; it is e : LeetQ.Rel.Programs.prelude.«1» ⟶ [α]"
-- the context determines it (§c): the other side of a check, the other operand, the declared type, the
-- composition, the pair
open LeetQ.Rel.Programs.prelude in
rel_program arrCtx where
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
open LeetQ.Rel.Programs.prelude in
rel_program twoObjsX where
    obj A = {a,b}
    obj B = {a,c}
    x : A ⟶ B ≜ {(a,a)}
    print x
#guard printed twoObjsX.prints == ["{(a, a)}"]
#eval errAt (twoObjs ++ "print {(a,c)}\n") 3 "the elements [a] are in [B, A]; write the literal after its object" (col := some 7)
-- a wrong expectation is a failed check, not an object error
open LeetQ.Rel.Programs.prelude in
rel_program wrongCheck where
    obj N = 0…9
    x : 1 ⟶ [N] ≜ {(∗,1 2)}
    check x = {(∗,[])}
#guard wrongCheck.failures.any fun e => (e.msg.splitOn "check failed").length > 1
#eval errAt (arrE ++ "e ≜ {(∗,1 12)}\n") 2 "no declared object has the elements [1, 12]"
#eval errAt (arrE ++ "e ≜ {(∗,1 2),(∗,3)}\n") 2
  "the rows of a literal nest alike: found 3, expected the form of 1 2"
#eval errAt (arrE ++ "e ≜ {(∗,(1,2) 3)}\n") 2 "the rows of a literal nest alike: found 3, expected the form of (1, 2)"

/-! Signed numbers (§a, §c): a range `-3…3`, signed literal words, `succ ≤ <` and the value verbs on it, each
    against Lean's `Int` (`div` floors and `mod` takes the divisor's sign, as q's: `Int.fdiv`, `Int.fmod`); a print
    lists numbers by value. -/

def zs : List Int := (List.range 7).map fun k : Nat => (k : Int) - 3
open LeetQ.Rel.Programs.prelude in
rel_program signed where
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
open LeetQ.Rel.Programs.prelude in
rel_program negRange where
    obj Z = -5…-1
    print 𝟙(Z) succ
#guard negRange.prints == ["𝟙(Z) succ = {(-5, -4), (-4, -3), (-3, -2), (-2, -1)}"]
#eval errAt "obj X = {A}\nobj Z = 3…-3\n" 2 "the range 3…-3 is empty: -3 is below 3" (col := some 11)
#eval errAt "obj Z = -3…3\nf ≜ {(-4,0)}\n" 2 "no declared object has the elements [-4]"
#eval trips ["{(A, -1)}", "{((-1, B), -20)}", "R − S"]

#eval readsAll [("R ∪ S R", "((R ∪ S) R)"), ("R S ∪ R", "((R S) ∪ R)"), ("R ∩ S ∪ R", "((R ∩ S) ∪ R)"),
  ("R ∪ S ∩ R", "((R ∪ S) ∩ R)"), ("∼R S", "(∼R S)"), ("R ∪ (S R)", "(R ∪ (S R))")]

/-! The parser on each line of `Programs.blocks`: every composite and infix term in parentheses, as the note reads the
    formula (§c), not as the parser happens to print it. -/

def reading : Decl → Option (String × String)
  | .defn _ n _ (.rel e) _ => some (n, e.render 0 true)
  | .defn _ n _ (.test e f) _ => some (n, s!"{e.render 0 true} ⊑ {f.render 0 true}")
  | .print _ e => some ("print", e.render 0 true)
  | .check _ e f eq => some ("check", s!"{e.render 0 true} {if eq then "=" else "⊑"} {f.render 0 true}")
  | _ => none

-- a `where` item in place in the body and in the items after it (§c)
#eval do
  match ← readIn (preludeScope) "obj B = 0…1\nf(S) ≜ b ∪ S where a ≜ π₁, b ≜ a π₂ S\n" with
  | .ok p => unless p.filterMap reading == [("f", "(((π₁ π₂) S) ∪ S)")] do throwError "{p.filterMap reading}"
  | .error e => throwError "{e}"

/-! Terms on an object with no universe (§a): a converse pushed to the leaves, a division tested on the pairs a
    meet supplies, `R×S` as `⟨π₁R,π₂S⟩`; and what is still refused. Expected values by hand. -/

open LeetQ.Rel.Programs.prelude in
rel_program chs where
    obj Ch = {a,b}
    obj N = 0…3
    x : 1 ⟶ [Ch] ≜ {(∗,a b)}
    y : 1 ⟶ [Ch] ≜ {(∗,a a b)}
    ns : 1 ⟶ [N] ≜ {(∗,2 3)}
    ms : 1 ⟶ [N] ≜ {(∗,3 1 2)}
    ks : 1 ⟶ [N] ≜ {(∗,3 1 1)}
    ok : α×[α] ⟶ α×[α] ≜ cor(≤/∋)


-- the converse: `(RS)° = S°R°`, `∩`, a pair with one side's converse, `R°° = R`, a coreflexive, `cons° = uncons`
open LeetQ.Rel.Programs.prelude chs in
rel_program chsConv where
    print x cons° (perm cons°)°
    print x (perm ∩ perm)° cons°
    print x ⟨cons°π₁, perm⟩°° π₂
    print x (dom(π₁{(a,a)}) cons)°
    print x (dom(π₁{(b,b)}) cons)°
#guard printed chsConv.prints ==
  ["{(∗, a b), (∗, b a)}", "{(∗, (a, [b])), (∗, (b, [a]))}", "{(∗, a b), (∗, b a)}",
   "{(∗, (a, [b]))}", "{}"]
-- `⟨R,S⟩°` with each side read through one projection: `(P×Q)° = P°×Q°`, so the book's `join°` runs as
-- `cat°(snoc°×𝟙)`; `⟨π₁,π₂⟩° = 𝟙`; a product of converses `(cons×perm)° = uncons×perm`. Expected values by hand.
open LeetQ.Rel.Programs.prelude chs in
rel_program chsJoin where
    join : ([α]×α)×[α] ⟶ [α] ≜ (snoc×𝟙)cat
    print y join°
    print y cat°(snoc°×𝟙)
    print x (cons° ⟨π₁,π₂⟩ cons)°
    print ⟨y,x⟩(cons×perm)°
#guard printed chsJoin.prints ==
  ["{(∗, (([], a), a b)), (∗, (([a], a), [b])), (∗, ((a a, b), []))}",
   "{(∗, (([], a), a b)), (∗, (([a], a), [b])), (∗, ((a a, b), []))}",
   "{(∗, a b)}", "{(∗, ((a, a b), a b)), (∗, ((a, a b), b a))}"]
-- refused at a leaf whose converse does not run on demand: `π₁` in `⟨π₁,π₁⟩°` (both sides through `π₁`, the
-- second component unbounded), `∋` in `∈`
#eval errAt "print ⟨{(∗,a)},{(∗,a)}⟩(cons° ⟨π₁,π₁⟩)°\n" 1 "the converse of π₁ does not run on demand" (prog := chs)
#eval errAt "print {(∗,a)} ∈\n" 1 "the converse of ∋ does not run on demand" (prog := chs)
-- a division tested on the pairs: `R/S`, `R\S`, `frac`, `∼`, `−`, each beside a term run on demand
open LeetQ.Rel.Programs.prelude chs in
rel_program chsDiv where
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
#eval errAt "print {(∗,1)}(≤/∋)\n" 1 "R/S reads its operands whole" (prog := chs)
#eval errAt "print {(∗,1)}((≤/∋) ∩ (≤/∋))\n" 1 "R/S reads its operands whole" (prog := chs)
-- `R×S` on demand as `⟨π₁R,π₂S⟩`; closed, as before
open LeetQ.Rel.Programs.prelude chs in
rel_program chsProd where
    print ⟨{(1,1)},⟨{(1,2)},Λ({(1,1)})⟩⟩(𝟙×π₁)plus
    print y cons°(𝟙×perm)
    print ⟨x,{(∗,b)}⟩(perm×𝟙)
    print {(1,1)}×{(2,3)}
#guard printed chsProd.prints ==
  ["{(1, 3)}", "{(∗, (a, a b)), (∗, (a, b a))}", "{(∗, (a b, b)), (∗, (b a, b))}", "{((1, 2), (1, 3))}"]
-- refused: an operand that does not run, named; the object printed as the program writes it, `[Ch]`
#eval errAt "print ⟨{(∗,a)},{(∗,b)}⟩(∈×𝟙)\n" 1 "the converse of ∋ does not run on demand" (prog := chs)
#eval errAt "print ⟨{(∗,a)},{(∗,b)}⟩(∈×𝟙)\n" 1 "[Ch] has no universe" (prog := chs)
-- `loop(F)` runs `F` on the pairs each round meets: a state that is an array (a copy, a reverse, the
-- subsequences), and a pair with an array (the copy with its length)
open LeetQ.Rel.Programs.prelude chs in
rel_program chsLoop where
    print x ⟨nil,𝟙⟩loop(snoc)
    print y ⟨nil,𝟙⟩loop(⟨π₂,π₁⟩cons)
    print x ⟨nil,𝟙⟩loop(snoc ∪ π₁)
    print x ⟨⟨nil,⊤{(0,0)}⟩,𝟙⟩loop(⟨⟨π₁π₁,π₂⟩snoc,π₁π₂ succ⟩)
#guard printed chsLoop.prints ==
  ["{(∗, a b)}", "{(∗, b a a)}", "{(∗, []), (∗, [a]), (∗, a b), (∗, [b])}", "{(∗, (a b, 2))}"]
-- refused: an `F` that runs neither way, the leaf named
#eval errAt "print x ⟨nil,𝟙⟩loop(snoc ran(snoc))\n" 1 "ran( ) reads its argument whole: [Ch]×Ch has no universe" (prog := chs)

/-! The prelude (§c): each definition moved there against the builtin it replaced (`Alg.perm`, `Alg.ordered`, and
    `sort(Q) = perm ordered(Q)`), on a repeated element, the empty array, two element objects and arrays of arrays;
    the converses; the declared infix operators; the errors. -/

open LeetQ.Rel.Programs.prelude in
rel_program pre where
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
open LeetQ.Rel.Programs.prelude in
rel_program converses where
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
open LeetQ.Rel.Programs.prelude in
rel_program infixes where
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
#eval trips ["R ⇒ S", "R ⊕ S", "R + S", "frac(R, S)", "∈", "perm", "ordered(R)", "sort(R)", "cor(R)"]
-- `cor(R)`: the pairs of `R` as a coreflexive on `A×B`
open LeetQ.Rel.Programs.prelude in
rel_program corPairs where
    obj N = 0…3
    print {((1,2),(1,2)),((2,1),(2,1)),((3,3),(3,3))}cor(≤)
#guard printed corPairs.prints == ["{((1, 2), (1, 2)), ((3, 3), (3, 3))}"]
#eval readsAll [("R ∩ S ⇒ R", "((R ∩ S) ⇒ R)"), ("R ⇒ S ∩ R", "((R ⇒ S) ∩ R)"), ("R S + R", "((R S) + R)"),
  ("R + S R", "((R + S) R)")]
-- infix only: used before its arguments, alone, or declared with other than two parameters
#eval errAt "obj B = 0…1\nf ≜ ⇒(π₁,π₂)\n" 2 "`⇒` is an infix operator: write `R ⇒ S`, not `⇒(R, S)`"
#eval errAt "obj B = 0…1\nf ≜ π₁ ∪ ⇒\n" 2 "`⇒` is an infix operator: it stands between two terms, `R ⇒ S`"
#eval errAt "obj B = 0…1\n_≼_(R) ≜ R\n" 2 "the infix operator `≼` takes two parameters, `_≼_(R, S)`, found 1"
-- a prelude name taken again, as a definition, an infix operator's name or an object, is the program's own: the
-- local name wins over an opened one (module design §2.3)
#eval show CM Unit from do
  for src in ["obj N = 0…9\nperm : N ⟶ N ≜ 𝟙(N)\n", "obj N = 0…9\n⊕ : N ⟶ N ≜ 𝟙(N)\n",
      "obj N = 0…9\n_sort_(R : N ⟶ N, S : N ⟶ N) : N ⟶ N ≜ R ∩ S\n", "obj 1 = {∗}\nobj N = 0…9\n"] do
    if let .error e ← readIn preludeScope src then throwError "{e}"
-- an error of the prelude's own text, and one raised in a prelude body at a use: the prelude's line, the use's
/-- The text `src` read after the prelude `pre`: its error. -/
def afterErr (pre src : String) : CM Err := do
  let p ← match ← readIn { cs := #[] } pre with | .ok p => pure p | .error e => throwError "{e}"
  let q ← match ← readIn { cs := #[], res := Parse.openAll [(`pre, p)] } src with | .ok q => pure q | .error e => return e
  match ← Lean.Elab.Command.liftTermElabM (Expand.read (fun _ => none) [(`pre, p)] q).run with
  | .error e => pure e
  | .ok _ => throwError "expected an error, got none"
-- the prelude's line 1 starts after `rel_program t where `, 20 columns
#eval do
  let e ← afterErr "    f ≜ g\n" "obj X = {A}\n"
  unless toString e == "in the program `pre`, line 1, col 29: unknown name 'g'" do throwError "{e}"
#eval do
  let e ← afterErr "    f(R : α ⟶ β) : α ⟶ β ≜ R g\n" "obj X = {A}\nx : X ⟶ X ≜ {(A,A)}\ny : X ⟶ X ≜ f(x)\n"
  unless e.pos.line == 3 && e.msg == "in `pre.f` (its line 1): unknown name 'g'" do throwError "{e}"

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
    ("r", "(dom(s₀) Λ(⊤))"),
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

#eval trips ["νZ : R ∩ Z", "(μZ : 𝟙 ∪ (R Z)) S", "R° ∪ (νZ : R ∩ (S \\ (Z R)))", "⟨νZ : R ∩ Z, S⟩"]
-- `R*`, the least `X` with `𝟙 ∪ RX ⊑ X`, against the closure written out
open LeetQ.Rel.Programs.prelude in
rel_program closure where
    obj N = 0…4
    R : N ⟶ N ≜ {(0,1),(1,2),(2,3)}
    c : N ⟶ N ≜ μX : 𝟙 ∪ (R X)
    check c = {(0,0),(1,1),(2,2),(3,3),(4,4),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)}
#guard closure.ok
-- postfix `*`, at the level of `°`: `R*` reads as that `μ`, its variable primed past every name in scope (the object
-- `X` here) and in its operand (`X'` here); `°` and `*` chain either way
#eval readsAll [("R*", "(μX' : (𝟙 ∪ (R X')))"), ("R°*", "(μX' : (𝟙 ∪ (R° X')))"), ("R*°", "(μX' : (𝟙 ∪ (R X')))°"),
  ("R S*", "(R (μX' : (𝟙 ∪ (S X'))))"), ("(R X')*", "(μX'' : (𝟙 ∪ ((R X') X'')))")]
-- `R*` against the hand-written `μ` and its value; `R°*` and `R*°` against its converse; `X`, a name of the
-- program, is not captured by the `μ` of `(R X)*`
open LeetQ.Rel.Programs.prelude in
rel_program star where
    obj N = 0…4
    R : N ⟶ N ≜ {(0,1),(1,2),(2,3)}
    X : N ⟶ N ≜ {(3,4)}
    c : N ⟶ N ≜ μZ : 𝟙 ∪ (R Z)
    check R* = c
    check R* = {(0,0),(1,1),(2,2),(3,3),(4,4),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)}
    check R°* = c°
    check R*° = c°
    check (R X)* = μZ : 𝟙 ∪ (R X Z)
    check (R X)* = {(0,0),(1,1),(2,2),(3,3),(4,4),(2,4)}
#guard star.ok
-- `*` is no name
#eval errAt "obj B = 0…1\n* : B ⟶ B ≜ 𝟙(B)\n" 0 "expected"
-- the points with an infinite `R`-path: the rounds from `𝟙` written out, which stop changing at the second
open LeetQ.Rel.Programs.prelude in
rel_program infPath where
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
open LeetQ.Rel.Programs.prelude in
rel_program square where
    obj V = {x,y}
    obj D = 0…9
    A : V ⟶ V ≜ {(x,y)}
    Ac : V ⟶ V ≜ A°
    sq : D ⟶ D ≜ {(0,0),(1,1),(2,4),(3,9)}
    sqc : D ⟶ D ≜ sq°
    uV : V ⟶ V ≜ 𝟙(V)
    uD : D ⟶ D ≜ 𝟙(D)
    s : V ⟶ D ≜ ⊤(V,D)
    z : V ⟶ D ≜ νZ : s ∩ (A\(Z sq)) ∩ (A°\(Z sq°))
    check z = {(x,0),(x,1),(x,2),(x,3),(y,0),(y,1),(y,4),(y,9)}
#guard square.ok
-- `μ` on an array target, its values duplicate-free lists: the unions of the singletons `s`, which stop growing
-- once every set of three is reached; against the two levels of union written out
open LeetQ.Rel.Programs.prelude in
rel_program muArr where
    obj B = 0…2
    s : B ⟶ [B] ≜ Λ({(0,0)}) ∪ Λ({(0,1)}) ∪ Λ({(0,2)})
    f : B ⟶ [B] ≜ μX : s ∪ (⟨X, X⟩ cat setify)
    d : B ⟶ [B] ≜ ⟨s, s⟩ cat setify
    e : B ⟶ [B] ≜ ⟨d, s⟩ cat setify
    check f = s ∪ d ∪ e
    print f
#guard muArr.ok
#guard muArr.prints == ["f = {(0, [0]), (0, 0 1), (0, 0 1 2), (0, 0 2), (0, [1]), (0, 1 2), (0, [2]), (1, []), (2, [])}"]
-- a `μ` whose arrays grow every round: no fixed point, so its rounds reach `muCap` and the program reports it
open LeetQ.Rel.Programs.prelude in
rel_program muGrow where
    obj B = 0…1
    r : B ⟶ [B] ≜ {(0,[1])}
    g : B ⟶ [B] ≜ μX : r ∪ (⟨X, r⟩ cat)
#guard !muGrow.ok
#guard muGrow.failures.map (·.msg) == ["an op ran out of capacity (its twin's ok bit is false); in g, or the μ at " ++
  "line 1064, col 19 ran its cap of 1024 rounds without reaching a fixed point"]
-- `X` under an operator not monotonic in its argument, or in an antitone place; `ν` with no bound
#eval errAt "obj B = 0…1\nf : B ⟶ B ≜ νX : ⊤(B,B) ∩ (Λ(X)∋)\n" 2
  "νX: X occurs under Λ at 2:30; Λ is not monotonic in its argument, so the fixed point need not exist"
#eval errAt "obj B = 0…1\nr : B ⟶ B ≜ {(0,1)}\nf : B ⟶ B ≜ μX : r ∪ X\\r\n" 3
  "μX: X occurs in the left operand of \\ at 3:22 (antitone); X must occur only in monotonic positions"
#eval errAt "obj B = 0…1\nr : B ⟶ B ≜ {(0,1)}\nf : B ⟶ B ≜ νX : r X\n" 3
  "νX needs a bound: write S ∩ φ with S not mentioning X (⊤(A,B) for the whole object)"
#eval errAt "obj X = {A,B,C}\nobj St = 𝒫(X×X)\nL(S : X ⟶ X) : X ⟶ X ≜ νZ : S ∩ Z\nf : St ⟶ X×X ≜ L(∋)\n" 3
  "νZ given a family is not liftable"
#eval errAt "obj B = 0…1\nνx : B ⟶ B ≜ 𝟙(B)\n" 2 "the name 'νx' reads as a fixed point"

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

open LeetQ.Rel.Programs.prelude Programs.csp Programs.sudokuac in
rel_program sudokuEx where
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

/-! `concat` is `List.flatten` (`rep_concatC`): order and duplicates kept. `w` is `a ↦ [[3 1] [2] [1]]`;
    `d` is `a ↦ [[1] [] [1]]`, `b ↦ [[] [1] []]`; `e` is `a ↦ [[3 1]]`, `b ↦ []`, an empty outer array. -/
open LeetQ.Rel.Programs.prelude in
rel_program concats where
    obj N = 0…9
    obj K = {a,b}
    w : K ⟶ [[N]] ≜ ⟨⟨{(a,3)},Λ({(a,1)})⟩cons, ⟨Λ({(a,2)}), Λ(Λ({(a,1)}))⟩cons⟩cons
    d : K ⟶ [[N]] ≜ ⟨Λ({(a,1)}), ⟨Λ({(b,1)}), Λ(Λ({(a,1)}))⟩cons⟩cons
    e : K ⟶ [[N]] ≜ Λ(⟨{(a,3)},Λ({(a,1)})⟩cons)
    print w concat
    print d concat
    print e concat

#guard concats.ok && concats.prints == [
  "w concat = {(a, 3 1 2 1)}",
  "d concat = {(a, 1 1), (b, [1])}",
  "e concat = {(a, 3 1), (b, [])}"]

end LeetQ.Rel.Lang.Test
