/-
  `Label` — a term spelled the way the NOTE spells it, for every picture that writes one.

  ONE RULE, THREE USERS.  The string, the circuit and the commutative functor each have to write a
  factor on a bead, on a box or on an arrow, and each spelled it its own way: composition came out
  `F ∋ ≫ S` on a box where the note writes `F(∋)S`, and the same `≫` survived inside `⦇…⦈` and
  `E(…)` because the label there was the raw printer's.  The spelling is decided HERE, once, and
  every label of every picture goes through `label`.

  THE PRINTER IS THE DEFAULT.  Where a constant has a spelling of its own, the fix is an
  `app_unexpander` beside it — or in `diag/StrDiagNames.lean` when the constant lives in `AOP` —
  never a clause below.  The clauses are only what no notation can express: juxtaposition for
  composition, which has no symbol left to parse back; the bracketing that makes it readable; and
  the note's own spacing.
-/
import diag.tool.ExprReader
-- The tape and first-order layers' own operators (`⨟•`, `⊥`, the four generators): `labelTree` is one
-- rule over both towers, so it has to see both.
import diag.FO
import diag.Tape
import diag.S2_124
-- `est`, the one operator of the allegory layer that lives above `ExprReader`'s own import, and the
-- type functor, whose action on an arrow is spelled here rather than by a notation (no term prints
-- its own brackets, and `T(f)` is brackets).
import AOP.A7_1
import AOP.A5_5_TypeFunctor
-- The graph of a function, the one arrow whose content is a Lean TERM and not an operator: its
-- name is read off that term, here, so every picture writes the same one.
import AOP.A6_1_RelSet

open Lean

namespace Freyd.StrDiag

/-- How a label JOINS under a functor's name — the note's rule (CLAUDE.md), one copy for every
    picture that writes an object. -/
inductive Join where
  /-- ONE CHARACTER the reader cannot take for a composite (`A`, `𝟏`), or a chain of one-letter
      functors on one (`EA`, `FEA`): a ONE-LETTER functor juxtaposes with it.  A name of two
      characters or more is `.other` — `EWord` reads as `E` composed with `Word`. -/
  | name
  /-- SELF-DELIMITED by the printer's own brackets (`[A]`): any functor juxtaposes with it -/
  | bracket
  /-- everything else — an application under a longer name (`bag(Job)`), a label written INFIX from
      the parts (`A×[A]`) — and applying an operator to it takes parentheses -/
  | other
  deriving Inhabited, BEq

/-- The closer that MATES an opening token — `none` for a token that opens nothing.  A form is
    self-delimiting only when the printer closed it in a PAIR: `[A]` ends where its `]` says, while
    `[0,2¹⁶)` is an interval whose `[` and `)` are two different notations' tokens. -/
def mate : String → Option String
  | "(" => some ")" | "[" => some "]" | "{" => some "}" | "⦃" => some "⦄"
  | "⟨" => some "⟩" | "⟦" => some "⟧" | "⟪" => some "⟫" | "⦇" => some "⦈"
  | "‹" => some "›" | "«" => some "»" | "⌊" => some "⌋" | "⌈" => some "⌉"
  | _ => none

/-- ONE LETTER, PRIMES AND ALL: the test every juxtaposition rule below asks of a name.  A prime is
    a letter's DECORATION and not a second letter — the note writes `G'A` and `FA×F'A` exactly as it
    writes `GA` — so counting characters called `G'` a two-letter name and parenthesised it alone
    among its family.  One rule, so the functor's half and the operand's half can never disagree. -/
def oneChar (s : String) : Bool := !s.isEmpty && (s.drop 1).all (· == '\'')

/-- ONE TOKEN OF THE NOTE'S LANGUAGE: what a factor of a composite has to be, juxtaposition being
    invisible.  A name spelled out of name characters is one (`old`, `π₂`, `est`); so is one the
    printer's own brackets close (`⟨ceiling,ceiling−floor⟩`), `stxJoin`'s bracket rule read off a
    name.  A name with an OPERATOR inside it is neither — `R;H` juxtaposed reads as `R` composed
    with `H` — so it keeps the brackets its precedence asks for wherever it is a factor. -/
def oneToken (s : String) : Bool :=
  s.isEmpty || s.all (fun c => Lean.isIdFirst c || Lean.isIdRest c)
    || mate (String.singleton s.front) == some (String.singleton s.back)

/-- How the printer's own spelling of a term JOINS under a functor's name.  The SYNTAX decides, not
    the term: an unexpander is exactly what turns the two-argument `ConsList Unit A` into the single
    token `[A]`, so the term's argument count answers a different question, and the finished string
    answers none.  ONE TOKEN is one name, however long (`A`, `𝟏`, `Word`); a form the printer CLOSED
    IN ITS OWN BRACKETS — first child an atom and last child an atom, which is what a bracket is —
    delimits itself; and an APPLICATION the printer wrote by juxtaposition (`Bag Job`, `list⁺ A`) is
    neither, because juxtaposition is composition and closing a functor's name up against it would
    read as one more factor of a composite. -/
partial def stxJoin : Syntax → Join
  -- ONE CHARACTER is what a one-letter functor may close up against (`EA`, `E𝟏`, `FEA`).  A LONGER
  -- name closed up reads as two factors of a composite — `EDecimal` is `E` then `Decimal`, `treeA`
  -- is `tree` then `A` — so it takes parentheses exactly as an application does.  This is the
  -- length test: a functor name closes up only when it and its argument's head are each one
  -- character; only the functor's half of it lives here, in `applyJoin`.
  | .ident _ _ n _ => if oneChar n.toString then .name else .other
  | .atom _ s => if oneChar s then .name else .other
  | .node _ _ args =>
    match (args[0]? : Option Syntax), (args.back? : Option Syntax) with
    -- A BRACKET IS A MATCHING PAIR OF TOKENS WITH NO NAME IN THEM.  `bag(Job)` and `list⁺(A)` open
    -- with an atom and close with one just as `[A]` does, but their opening token CARRIES THE
    -- FUNCTOR'S NAME, so the next functor's would close up against it (`Ebag(Job)`) and read as two
    -- things composed; and `[0,2¹⁶)` opens with `[` and closes with `)`, so its own tokens do not
    -- say where it ends and `E[0,2¹⁶)` reads as a bracket left open.  Both tests are on the TOKENS,
    -- never on their length: a character a name can be spelled with disqualifies.
    | some (.atom _ o), some (.atom _ c) =>
      if o.any fun c => Lean.isIdFirst c || Lean.isIdRest c then .other
      else if mate o == some c then .bracket else .other
    | _, _ => .other
  | .missing => .other

/-- A functor's action on an OBJECT, by the repo's juxtaposition rule: juxtaposition is composition,
    so APPLYING takes parentheses (`bag(Job)`, `E(A×[A])`, `E(bag(Job))`) — `EA×[A]` would read as the
    product of `EA` with `[A]` and `E bag Job` as three things composed.  Two forms stay closed up: a
    CHAIN OF ONE-LETTER FUNCTORS on one name, which no reader can take for a composite (`EA`, `FEA`,
    `E𝟏`), and an argument the printer ALREADY DELIMITED with its own brackets (`E[A]`, `F[Char]`).

    THE ARGUMENT'S JOIN IS THE ARGUMENT'S, never re-read off the finished name. -/
def applyLabel (f : String) (a : String) (j : Join) : String :=
  if j == .bracket || (oneChar f && j == .name) then f ++ a
  else f ++ "(" ++ a ++ ")"

/-- The join of what `applyLabel f` builds, which is decided by the label's OWN HEAD and nothing
    else: a one-letter functor heads what it builds, so `E(bag(Job))` juxtaposes under the next one
    exactly as `EA` does (`EF(bag(Job))`), while a longer name heads an application the next functor
    parenthesises. -/
def applyJoin (f : String) : Join := if oneChar f then .name else .other

/-- A JUXTAPOSED application as THE PRINTER wrote it: the identifier it opens with and the operands
    beside it, `none` for everything else — a bare name, an infix, a notation that delimits its own
    operand.  The printer's operands, never the term's arguments: an unexpander that drops arguments
    (`H T h` printed `H`) dropped them from the picture too, and re-reading them off the term would
    put them back. -/
partial def appParts : Syntax → Option (Syntax × Array Syntax)
  | .node _ k args =>
    if k != ``Lean.Parser.Term.app then none else
    match (args[0]? : Option Syntax), (args[1]? : Option Syntax) with
    | some f, some (.node _ _ ops) =>
      -- A HEAD THE PRINTER PARENTHESISED IS A HEAD, never a factor to flatten into the operands:
      -- the note's curried `Vec(n)(R)` says the operator is `Vec(n)` and `R` is what it is applied
      -- to, where flattening would spell one application of three parts.
      if f matches .ident .. then some (f, ops)
      else if f.isOfKind ``Lean.Parser.Term.paren then some (f, ops)
      else (appParts f).map fun (h, prev) => (h, prev ++ ops)
    | _, _ => none
  | _ => none

/-- The parentheses the printer put round an operand to keep it out of the juxtaposition taken off,
    and its null wrappers with them — the brackets of `f(…)` already separate it, and
    `thin((prefix°×(⊤+⊤)))` doubles them.  ONE peel, because the string an operand is written as
    and the join it is read at must be the same syntax: reading the join off the unpeeled `(A × B)`
    calls it self-delimiting and juxtaposes `E` against the string the peel already opened. -/
partial def stxPeel (s : Syntax) : Syntax :=
  match s.getArgs with
  | #[.atom _ "(", inner, .atom _ ")"] => stxPeel inner
  | #[inner] => if s.isOfKind nullKind then stxPeel inner else s
  | _ => s

/-- One operand as the printer writes it, peeled. -/
def stxShow (s : Syntax) : MetaM String := do
  let t := (toString (← PrettyPrinter.ppTerm ⟨stxPeel s⟩)).replace "«" "" |>.replace "»" ""
  return " ".intercalate (t.splitOn "\n" |>.map fun u => u.trimAscii.toString)

/-- A HEAD IS WRITTEN BY ITS LAST COMPONENT.  A qualifier — the record it is a field of, the
    namespace it was declared in — is the PRINTER disambiguating, and the note draws no `TT`: what
    it writes beside the picture is `F(A)`, so `TT.F A` reading as a composite of `TT.F` and `A` is
    the qualifier leaking into the name.  This is `relatorName?`'s rule for a wire, kept for the
    heads a wire's name is built out of, so a lane and the label above it cannot be spelled two
    ways.  On the IDENT only: a head that is a notation delimits its own operand and has no name to
    shorten. -/
def appSpell (h : String) (ops : Array Syntax) : MetaM String := do
  match ops with
  | #[a] => return applyLabel h (← stxShow a) (stxJoin (stxPeel a))
  | _ => return h ++ "(" ++ String.intercalate "," (← ops.toList.mapM stxShow) ++ ")"

partial def headShown (h : Syntax) : MetaM String := do
  if h.isIdent then return h.getId.getString!
  -- A HEAD THAT IS ITSELF AN APPLICATION is spelled by this same rule applied again, which is what
  -- the note's curried `Vec(n)(R)` is: the operator `Vec(n)`, and `R` applied to it.  The
  -- application is looked for among the paren's OWN children — `Term.paren` carries the optional
  -- tuple tail beside the term, so the three-token peel `stxPeel` does never reaches it.
  if h.isOfKind ``Lean.Parser.Term.paren then
    if let some (f, ops) := h.getArgs.findSome? fun a => appParts (stxPeel a) then
      return ← appSpell (← headShown f) ops
  stxShow h

/-- The printer's spelling of a term, with a JUXTAPOSED application re-set by the note's own join
    rule: ONE operand goes through `applyLabel`, so a ONE-LETTER head juxtaposes with it (`TA`,
    `PA`, `E[A]`) and a longer name applies with parentheses (`thin(Q)`, `bag(Job)`, `list⁺(A)`),
    juxtaposition being composition and `thin Q` reading as a composite of two arrows.  The LENGTH
    and the operand's own join decide it, never a list of names — the next one-letter functor
    declared draws right with no line added here.  SEVERAL operands are the note's comma list, which
    no juxtaposition can be read as.  A head whose own notation already delimits its operands
    (`est(R)`, `⦇S⦈`, `F(f)`) has no juxtaposition to re-set and keeps what the printer wrote.

    THE HEAD IS `headShown`'s: the note writes a name's last component and no qualifier. -/
def appShow (e : Expr) : MetaM String := do
  match appParts (← PrettyPrinter.delab e) with
  | some (h, ops) => appSpell (← headShown h) ops
  | none => plain e

/-- The note's juxtaposition spacing, the same rule the note's own generator writes back with:
    a bracket already separates two factors, so `F(∋)S` and `π₂R°`
    close up where `prefix list(p)` and `S%∋ est(R°)` cannot.  A factor OPENING with `(` keeps its
    space — `pick (schedule×𝟙)snoc` closed up would read as an application of `pick`. -/
def juxt (a b : String) : String :=
  if a.isEmpty || b.isEmpty then a ++ b
  -- `°` is a POSTFIX: it terminates its operand exactly as a closer does, so `est(R∩S°S)` must not
  -- come out `est(R∩S° S)`.
  else if ")]⟩⦈}°".contains a.back || "[⟨⦇{".contains b.front then a ++ b
  else a ++ " " ++ b

/-- The heads the note sets TIGHT: the product and the fork.  Lean's formatter sets an INFIX off
    from its operands (`A × B`, `⟨f, g⟩`, `a + b`) where the note closes them up; the SPELLING is
    untouched — it is what the `app_unexpander` beside the constant already printed.

    AN APPLICATION IS NOT ONE OF THESE ANY MORE.  `P A` and `T A` are a functor's action written by
    juxtaposition, and `appShow` decides those by the head's own LENGTH — one letter closes up, a
    longer name takes parentheses — so the next one-letter functor draws right with no name added
    here.  What is left is infix, where the space to close is the formatter's around the operator's
    OWN ATOM and no length test can see it.

    A RELATOR'S ACTION ON AN OBJECT IS NOT ONE OF THESE.  Closing the whole application up welds the
    head's own spelling shut (`(RT.F A)([A] × [A])` came out `(RT.FA)([A]×[A])`), and whether it
    juxtaposes at all is the note's join rule, which needs head and operand apart: `applyLabel`.

    AN ACTION ON AN ARROW IS NOT ONE OF THESE, however tight its object action sets.  `E(R)` is an
    operator APPLIED to a term of the note's, so its operand is respelled here (the `existsImage`
    clause below) where a tight head hands the whole application to the printer and the operand
    keeps whatever Lean wrote — which is how `E(mssPre)` stood where the note opens the definition. -/
def tightHeads : Array Name :=
  #[``Freyd.HasBinaryProducts.prod, ``Freyd.HasBinaryProducts.pair,
    ``Freyd.Alg.RelProd.p, ``Freyd.Alg.RelProd.pair,
    -- A COPRODUCT OBJECT sets as tight as a product apex: the note writes `GA+G'A`.  The sum of two
    -- ARROWS is not here for the reason the paragraph above gives — it welded `F(R)+F'(R)` shut to
    -- `FR+F'R` — and is read off the type instead, beside the product map (`asSumMap?`).
    ``Freyd.Alg.PositiveAllegory.coprod]

/-- The ARROW arguments of an application, picked by their TYPE and not by their position:
    `I.cata f hf` carries the algebra AND the proof it is one, and taking the last argument wrote
    `⦇hf⦈` for `⦇f⦈`. -/
def homArgs (args : Array Expr) : MetaM (Array Expr) :=
  -- The region's `Cat` instance decides, not the `Cat.Hom` head (`homEnds?`): a concrete region's
  -- hom is a FUNCTION TYPE, and its arrows are terms of the note's like any other.
  args.filterM fun a => return (← homEnds? a).isSome

/-! ### A MAP, named from its own function

A relation given as the graph of a function has no operator inside it, so no clause of `labelTree`
can reach its content: its name is read off the FUNCTION'S BODY — a projection is a `π`, a
constructor fed the input's factors is the carrier's structure map, a body that ignores the input
is a discard.  One rule, so a map is named the same wherever it is spelled: on the box the circuit
draws for it, and inside the `E(…)` or `⦇…⦈` of a label. -/

/-- Which factor of a product a projection keeps, read off the function's own body. -/
def projIndex (body : Expr) : Option Nat :=
  match body with
  | .proj ``Prod i _ => some i
  | _ => match body.getAppFnArgs with
    | (``Prod.fst, _) => some 0
    | (``Prod.snd, _) => some 1
    | _ => none

/-- The last component of a declaration's name, for the places a picture writes a declaration by
    name and nothing else.  A namespace is what a resolver needs, and nothing inside a picture
    resolves a name, so `cat` is what the box says wherever `cat` is what was declared. -/
def declName? (e : Expr) : MetaM (Option String) := do
  let .const n _ := e.getAppFn | return none
  if ((← getEnv).find? n).isNone then return none
  -- THE PRINTER IS THE DEFAULT here too: a constant an `app_unexpander` gives a name of its own
  -- writes THAT name on the box, the way `relatorName?` takes the printer's.  A head that only
  -- drops the namespace chose nothing, so the constant's own last component stands.
  if let some h := stxHead (← PrettyPrinter.delab e) then
    if h.getString! != n.getString! then return some h.getString!
  return some n.getString!

/-- A HEAD WITH THE ARGUMENTS THE PICTURE ALREADY DRAWS TAKEN OUT, spelled from its EXPLICIT
    positions alone.  An implicit or instance argument is the elaborator's business and no factor of
    the note's name: taking the drawn arguments out of `x + c` left `HAdd.hAdd` carrying its
    `instHAdd`, which is a projection applied to an instance, and the printer wrote `instHAdd` into
    the label.  WHICH POSITIONS THOSE ARE IS THE HEAD'S OWN BINDER INFO, never a count, a position or
    a name; with no explicit argument left the head is written by its own declared name. -/
def headShow (f : Expr) (args : Array Expr) (keepArg : Expr → Bool) : MetaM String := do
  let fi ← Meta.getFunInfoNArgs f args.size
  let mut keep : Array Expr := #[]
  for i in [0 : args.size] do
    if ((fi.paramInfo[i]?.map (·.isExplicit)).getD true) && keepArg args[i]! then
      keep := keep.push args[i]!
  if keep.isEmpty then
    if let some n ← declName? f then return n
  plain (mkAppN f keep)

/-- THE STEPS a value computed FROM THE INPUT is made of, in diagram order: `p(π₁ s)` is `π₁`, `p` —
    first the projection, then the test.  The input itself is the identity and contributes nothing,
    and an argument that does not mention the input is a PARAMETER of the function, not a step of the
    computation, so it stays inside the function's own name.  `none` where the walk does not reach the
    input: the term is then no chain of steps and whoever asked prints it whole. -/
partial def valSteps (s : FVarId) (x : Expr) : MetaM (Option (Array String)) := do
  if x == .fvar s then return some #[]
  let step (st : Expr) (h : String) : MetaM (Option (Array String)) := do
    return (← valSteps s st).map (·.push h)
  match x with
  | .proj ``Prod i st => step st (if i == 0 then "π₁" else "π₂")
  | _ =>
    let args := x.getAppArgs
    match x.getAppFnArgs.1, args.back? with
    | ``Prod.fst, some st => step st "π₁"
    | ``Prod.snd, some st => step st "π₂"
    | _, _ =>
      let deps := args.filter fun a => a.containsFVar s
      if deps.size == 1 then
        step deps[0]! (← headShow x.getAppFn args fun a => !a.containsFVar s)
      else return none

/-- The factors an alternative's `n` bound variables come from: the summand's own product structure,
    peeled the way a tuple pattern binds it. -/
partial def tupleFactors (s ty : Expr) (n : Nat) : MetaM (Array Expr) := do
  if n == 0 then return #[]
  if n == 1 then return #[s]
  match (← Meta.whnfD ty).getAppFnArgs with
  | (``Prod, #[_, b]) => return #[.proj ``Prod 0 s] ++ (← tupleFactors (.proj ``Prod 1 s) b (n - 1))
  | _ => throwError "a branch binds {n} variables out of {← Meta.ppExpr ty}, which is not a \
      product of that many factors"

/-- One alternative as a map OUT OF ITS SUMMAND, which is what an arm of the junction is. -/
def armFun (alt ty : Expr) (n : Nat) : MetaM Expr :=
  Meta.withLocalDeclD `s ty fun s => do
    Meta.mkLambdaFVars #[s] (mkAppN alt (← tupleFactors s ty n)).headBeta

/-- The arms of a map given by a `match` ON ITS INPUT at a coproduct — the junction `[f,g]` the note
    writes, whether the picture opens it as a tape or a label names it.  `matchMatcherApp?` reads
    the discriminant, the alternatives and their arities off the elaborated term and the coproduct
    off the discriminant's TYPE, so any `match` written this way — at any coproduct, any arity — is
    the junction, and no `def`'s name appears here. -/
def sumArms (fw : Expr) : MetaM (Option (Array Expr)) := do
  unless fw.isLambda do return none
  Meta.lambdaBoundedTelescope fw 1 fun xs body => do
    let some u := xs[0]? | return none
    let some ma ← Meta.matchMatcherApp? body | return none
    unless ma.discrs.size == 1 && ma.discrs[0]! == u && ma.alts.size == 2
      && ma.altNumParams.size == 2 && ma.remaining.isEmpty do return none
    let (``Sum, #[a, b]) := (← Meta.whnfD (← Meta.inferType u)).getAppFnArgs | return none
    return some #[← armFun ma.alts[0]! a ma.altNumParams[0]!,
      ← armFun ma.alts[1]! b ma.altNumParams[1]!]

/-- Whether a map BRANCHES ON ITS INPUT: a lambda whose body is a matcher applied to a discriminant
    the input occurs in.  The two shapes the note writes out are both this — a coproduct match is
    the junction `[nil,snag]`, a boolean one the guard `(ok→glue,new)` — so one test finds both, and
    a match on anything else is found by the same test the day it is drawn. -/
def branchesOnInput (f : Expr) : MetaM Bool := do
  unless f.isLambda do return false
  Meta.lambdaBoundedTelescope f 1 fun xs body => do
    let some x := xs[0]? | return false
    let some ma ← Meta.matchMatcherApp? body | return false
    -- ONE ALTERNATIVE IS NO BRANCH.  A match on a single-constructor type is the elaborator's
    -- spelling of taking the input apart — `fun (a,v) => Fin.cases a v` — so there is no second arm
    -- to name and opening the map's name reaches a matcher that names no arrow at all (`cons`).  A
    -- junction and a guard both have two, which is what the two shapes above are.
    unless ma.alts.size ≥ 2 do return false
    return ma.discrs.any (·.containsFVar x.fvarId!)

/-- A MAP GIVEN BY A `match` ON ITS INPUT IS WRITTEN BY WHAT IT DOES, so a NAME standing for one is
    opened until the match is in view; `none` where no delta reaches a match, and the name then
    stands (`mapLabel`'s no-delta rule — that body is the implementation).  `CircuitDiagram` already
    draws the arms of such a map as a two-arm tape, so a name kept here made ONE arrow read as
    `[nil,snag]` in the picture and `bagAlgFn` in the box beside it.  A RECURSIVE map is not one:
    its body is its recursor, not a matcher, so `flatten` keeps its name. -/
partial def branchForm? (f : Expr) : MetaM (Option Expr) := do
  if ← branchesOnInput f then return some f
  if f.isLambda then return none
  match ← Meta.unfoldDefinition? f with
  | some v => branchForm? (← Meta.whnfCore v)
  | none => return none

/-- THE PROJECTION PATH a value is of the input, `none` where it is not one of its factors: `[]` is
    the input itself, `[0]` its first factor.  Read off the term, so `p.1`, `Prod.fst p` and the
    projection the elaborator compiled a pattern to all answer the same. -/
partial def projPath (s : FVarId) (x : Expr) : Option (List Nat) :=
  if x == .fvar s then some [] else
  match x with
  | .proj ``Prod i st => (projPath s st).map (· ++ [i])
  | _ => match x.getAppFnArgs with
    | (``Prod.fst, args) => (args.back?.bind (projPath s)).map (· ++ [0])
    | (``Prod.snd, args) => (args.back?.bind (projPath s)).map (· ++ [1])
    | _ => none

/-- Beta at the head, to a fixed point.  An alternative reconstructed from a `match` arrives as a
    lambda applied to the summand's factors, and the lambda it names may itself be one; nothing
    beyond beta is reduced, because a NUMERAL delta-reduces to a constructor and would then read as
    the carrier's empty structure map. -/
partial def betaHead (e : Expr) : Expr :=
  let e' := e.headBeta
  if e' == e then e else betaHead e'

/-- A RELATOR IS NAMED BY ITSELF.  Its arguments are the TYPES the picture already draws on the
    wires — the snoc-list's `F` at `L`,`E`, the tip-tree's at `A` — so writing them into the lane's
    name spells one thing twice, and the note writes the lane `F`.  The TYPE decides that this is a
    relator and the PRINTER gives the letter, so an unexpander's chosen name still wins. -/
def relatorName? (e : Expr) : MetaM (Option String) := do
  unless ← isLaneBundle e do return none
  if let some h := stxHead (← PrettyPrinter.delab e) then return some h.getString!
  let some c := e.getAppFn.constName? | return none
  return some c.getString!

/-- A FUNCTOR'S ACTION ON OBJECTS, as the things the note writes it from: the functor and EVERY
    object it is taken at.  Read off the field's own arguments — the bundle stands at the
    projection's parameters and the objects after it — so an unexpander that hides them cannot lose
    them, exactly as `functorMap?` reads the action on an arrow, and a BINARY relator's action
    stands at two (`F(A,C)`) with no clause of its own.  What makes it an action and not some other
    field is the TYPE: the bundle is one the picture draws a lane for (`relatorName?`) and both the
    arguments and the value are OBJECTS, which is what separates `obj` from `map`. -/
def functorObj? (e : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let .const n _ := e.getAppFn | return none
  let some pi := (← getEnv).getProjectionFnInfo? n | return none
  let args := e.getAppArgs
  unless args.size > pi.numParams + 1 do return none
  let f := args[pi.numParams]!
  unless (← relatorName? f).isSome do return none
  unless ← isObjType (← Meta.inferType e) do return none
  let xs := args.extract (pi.numParams + 1) args.size
  unless ← xs.allM (fun x => do isObjType (← Meta.inferType x)) do return none
  return some (f, xs)

/-- The NAME a functor writes on a label — the lane's own name where it has one, the printer's
    otherwise, so the object `FA` and the arrow `F(R)` are headed by the same letter. -/
def functorName (f : Expr) : MetaM String := do
  match ← relatorName? f with
  | some n => return n
  | none => plain f

/-- Whether the printer wrote the head constant AS ITSELF — its own name standing in the syntax it
    built — rather than through a rule of its own, a notation or an `app_unexpander`.  That is the
    test for "has this constant a spelling beside itself", and it is asked wherever a label may only
    be rewritten when one fired.

    THE HEAD'S NAME IS MATCHED AS A SUFFIX, never for equality: the printer writes a constant at
    whatever prefix the open namespaces leave it — `BiRelator.obj` for `Freyd.Alg.BiRelator.obj` —
    so an equality test calls its own default spelling a foreign notation and drops the whole label
    into the generic printer (`BiRelator.objFA(TA)` for `F(A,TA)`). -/
def printsItsName (e : Expr) : MetaM Bool := do
  let .const n _ := e.getAppFn | return false
  return ((← PrettyPrinter.delab e).raw.find? fun s =>
    s.isIdent && s.getId.eraseMacroScopes.isSuffixOf n).isSome

/-- Whether the printer wrote a field access AS ITSELF — `(Vec n).obj A`, `Functor.obj (Vec n) A` —
    with no notation of its own, read off the syntax it built: the field's identifier at a
    projection node, or the projection function's own name at the head.  Where a delaborator keyed
    on the field wrote the note's spelling instead (`A[n]`), neither appears in the syntax. -/
def printsAsField (e : Expr) : MetaM Bool := do
  let .const n _ := e.getAppFn | return false
  let fld := Name.mkSimple n.getString!
  if ((← PrettyPrinter.delab e).raw.find? fun s =>
      s.isOfKind ``Lean.Parser.Term.proj && s[2].isIdent
        && s[2].getId.eraseMacroScopes == fld).isSome then return true
  printsItsName e

/-- How an OBJECT's label joins under a functor's name.  A functor's action heads with THAT
    functor's name (`applyJoin`), whatever its operand was; everything else is the printer's own
    answer, read off the syntax it built. -/
def objJoin (e : Expr) : MetaM Join := do
  match ← functorObj? e with
  | some (f, _) => return applyJoin (← functorName f)
  | none => return stxJoin (← PrettyPrinter.delab e)

/-- The last component of the head's name WHEN THAT HEAD IS A CONSTRUCTOR — read off the
    environment, never off the printed string.  A constructor is qualified by the type it builds,
    and the picture draws that type as the wire the box sits on, so the qualification says nothing
    the reader cannot already see. -/
def ctorName? (e : Expr) : MetaM (Option String) := do
  let .const n _ := e.getAppFn | return none
  match (← getEnv).find? n with
  | some (.ctorInfo _) => return some n.getString!
  | _ => return none

/-- AN OBJECT OF THE GIVEN CATEGORY INSIDE AN ARGUMENT, at whatever depth it sits: the algebra of a
    parametrised initial algebra is written `(I A).α`, so the object the family is indexed by is
    inside the BUNDLE handed to the field, not beside it, and that bundle reaches the projection
    instance-implicitly.  `obj` is the category's own object type — the type of the endpoints of the
    hom the component IS — and it is what rules the other arguments out: the category `𝒜` is a
    `Type`, the relator `F` a `Relator 𝒜 𝒜`, and neither is an object however object-shaped it
    looks, where a position or an explicitness test lets both in or shuts the bundle out.  A
    compound argument is searched last-first, because a family is applied to its index last. -/
partial def objIn? (obj : Expr) (a : Expr) : MetaM (Option Expr) := do
  if ← Meta.isDefEq (← Meta.inferType a) obj then return some a
  let mut r : Option Expr := none
  for x in a.getAppArgs do
    if let some y ← objIn? obj x then r := some y
  return r

/-- A COMPONENT OF A DECLARED FAMILY, as the head's own spelling and the object it is taken at.
    A family tagged `@[diag_indexed]` wears a notation that writes its letter ALONE — `α` for the
    algebra of a parametrised initial algebra — so the object is missing from the label and goes
    BENEATH it: `α`#sub[`A`] and `α`#sub[`B`] are the two algebras of the one family, and nothing
    else in the square tells them apart.  The INDEX is the LAST argument holding an object OF THE
    CATEGORY THE COMPONENT IS AN ARROW IN, which is where a family is indexed — beside the head in
    `alphaT I A`, and inside the bundle in `(I A).α`, where every argument including the bundle
    arrives implicit.  A family over a bundle that is indexed by nothing, `I.α`, holds no such
    object anywhere and stays the bare `α` the note writes. -/
def indexedComponent? (e₀ : Expr) : MetaM (Option (String × Expr)) := do
  -- A FIELD LEAN LEFT AS A POSITION is the same component written another way, so it is normalised
  -- HERE too: otherwise the bundle the field is taken of never reaches the search for the index.
  let e := (← namedProj? e₀).getD e₀
  let .const c _ := e.getAppFn | return none
  unless (← Lean.labelled `diag_indexed).contains c do return none
  let some (src, _) := homObjs? (← Meta.inferType e) | return none
  -- THE CATEGORY'S OBJECT TYPE, taken from the hom the component IS: its endpoints are objects of
  -- the very category the index is drawn from, so nothing else has to say which category that is.
  let obj ← Meta.inferType src
  -- THE LETTER IS THE HEAD OF THE SPELLING, read off the SYNTAX and not off the constant's name:
  -- `alphaT I A` is the `α` its notation writes and the index it dropped is set beneath by this
  -- clause.  A FIELD is written under the field's own identifier, which the printer puts AFTER the
  -- dot and `stxHead` — whose business is an application's head — cannot reach; that the constant
  -- is a projection is read off the environment, never off its spelling.
  let head? : MetaM (Option Name) := do
    if ((← getEnv).getProjectionFnInfo? c).isSome then return some (Name.mkSimple c.getString!)
    return stxHead (← PrettyPrinter.delab e)
  let some h ← head? | return none
  let mut ix : Option Expr := none
  for a in e.getAppArgs do
    if let some x ← objIn? obj a then ix := some x
  match ix with
  | some a => return some (h.getString!, a)
  | none => return none

mutual

/-- The BODY of a map, named as an arrow out of the input `s`: a body that does not mention `s` is
    a constant, one that projects is a `π`, and a constructor fed the input's factors is the
    carrier's own structure map. -/
partial def bodyLabel (s : FVarId) (body₀ f : Expr) : MetaM String := do
  -- WHAT THE MAP DOES, not how it was written: an arm reconstructed from a `match` arrives as the
  -- alternative applied to the summand's factors.  The fallback still prints what was written.
  let body₁ := betaHead body₀
  -- A FUNCTION APPLIED TO A CONSTRUCTOR BUILT FROM THE INPUT IS THAT CASE OF IT, so the case is
  -- taken: `arm₂` restricts an algebra to `Sum.inr` and the arm the note names is what is left.
  -- Only a constructor built from the INPUT fires this, and only the head is unfolded, so a numeral
  -- — a constructor behind one delta, with no input in it — is untouched, as `betaHead` says.
  let isCtorApp (x : Expr) : MetaM Bool := do
    let .const n _ := x.getAppFn | return false
    match (← getEnv).find? n with
    | some (.ctorInfo _) => return true
    | _ => return false
  let body ←
    if ← body₁.getAppArgs.anyM (fun a => do return (← isCtorApp a) && a.containsFVar s) then
      match ← Meta.unfoldDefinition? body₁ with
      | some v => Meta.whnfCore v
      | none => pure body₁
    else pure body₁
  match projIndex body with
  | some 0 => return "π₁"
  | some _ => return "π₂"
  | none =>
    if let some g ← guardLabel s body then return g
    -- A `match` ON A COPRODUCT IS THE JUNCTION `[f,g]`, wherever it is spelled: the picture opens it
    -- as a tape and a label names it, and both read the arms off the same `sumArms`.  The brackets
    -- are `labelTree`'s own for `junc`, because it is the same arrow.
    if let some arms ← sumArms (← Meta.mkLambdaFVars #[.fvar s] body₀) then
      if arms.size == 2 then
        return "[" ++ (← mapLabel arms[0]! false) ++ "," ++ (← mapLabel arms[1]! false) ++ "]"
    -- The book's names for the two structure maps of a list-like carrier, read off the TERM:
    -- a CONSTRUCTOR fed both factors of the input pair is `cons`, and one fed nothing from the
    -- input is `nil`.  Nothing here knows `List`: the next carrier built the same way gets the
    -- same names without a line being added.
    let isCtor ← match body.getAppFn with
      | .const n _ => match (← getEnv).find? n with
        | some (.ctorInfo _) => pure true
        | _ => pure false
      | _ => pure false
    -- `nil` IS THE STRUCTURE MAP OUT OF `𝟏`, and whether the constructor was written with the unit
    -- value in it (`wrap s`) or without it is a spelling: `𝟏` carries no strand either way, which is
    -- the same test `mapLabel` asks before it writes a `⊸`.
    -- A SOURCE WITH NO STRANDS CARRIES NOTHING TO BUILD FROM, so every map out of it is the
    -- carrier's empty structure, whatever term writes it: a constructor (`wrap s`, `wrap ()` — the
    -- unit value in it or not is a spelling) or a quotient of one (`nilBag`), which is why the test
    -- is on the SOURCE and not on the body's head.
    if !(← hasStrands (← s.getType)) then return "nil"
    if isCtor && !body.containsFVar s then return "nil"
    if isCtor && (body.find? fun x => projIndex x == some 0).isSome
        && (body.find? fun x => projIndex x == some 1).isSome then
      -- WHICH FACTOR RECURSES NAMES THE MAP: the constructor is fed both factors of the input pair
      -- and one of them has the CARRIER's own type — the list being extended.  Second factor and the
      -- element goes on the front (`cons`), first and it goes on the end (`snoc`).  Read off the
      -- types, so the next carrier built either way is named without a line being added here.
      let t ← Meta.inferType body
      let recAt (i : Nat) : MetaM Bool := do
        match body.find? fun x => projIndex x == some i with
        | some p => Meta.isDefEq (← Meta.inferType p) t
        | none => return false
      -- BOTH FACTORS THE CARRIER IS NOT A LIST: there is no side an element goes on, so `cons` and
      -- `snoc` name nothing and the constructor keeps its own name (`bin`).  Read off the types,
      -- so every branching carrier is named without a line being added here.
      if (← recAt 0) && (← recAt 1) then
        if let some n ← ctorName? body then return n
      return if ← recAt 0 then "snoc" else "cons"
    -- A MAP THAT HANDS THE INPUT'S FACTORS STRAIGHT TO ONE ARROW IS THAT ARROW.  `fun p => snag p`
    -- and `fun p => cat p.1 p.2` are `snag` and `cat` η-expanded, and the lambda is what the
    -- elaborator wrote, not what the note draws.  The test is on the PATHS: every argument that
    -- mentions the input is a projection of it, and together they are its factors in order.
    let args := body.getAppArgs
    let deps := args.filter fun a => a.containsFVar s
    let paths := deps.toList.filterMap (projPath s)
    if !deps.isEmpty && paths.length == deps.size
        && (paths == [[]] || paths == (List.range deps.size).map ([·])) then
      -- A CONSTRUCTOR'S NAMESPACE IS ITS TYPE, which the wire beside the box already shows.
      if let some n ← ctorName? body then return n
      -- AND WHERE EVERY EXPLICIT ARGUMENT WAS THE INPUT'S OWN FACTORS the box writes a declaration
      -- by name and nothing else, so it writes the name the DECLARATION chose (`cat`): a namespace
      -- is what a resolver needs, and nothing inside a picture resolves a name.  The implicits are
      -- not printed either way, so they do not count as something left to write.
      let fi ← Meta.getFunInfoNArgs body.getAppFn args.size
      if (List.range args.size).all fun i =>
          !(fi.paramInfo[i]?.map (·.isExplicit) |>.getD true) || args[i]!.containsFVar s then
        if let some n ← declName? body then return n
      return ← headShow body.getAppFn args fun a => !a.containsFVar s
    -- A BODY THAT PIPES THE INPUT THROUGH ONE ARROW AFTER ANOTHER IS THEIR COMPOSITE, which the note
    -- writes by juxtaposition in diagram order: `fun s => wrap (wrap s)` is `wrap wrap`.
    if let some steps ← valSteps s body then
      if !steps.isEmpty then return " ".intercalate steps.toList
    if body₀.containsFVar s then plain f else plain body₀

/-- A `match` on a BOOLEAN test wires nothing — both arms leave on the same strands — so the note
    writes it into the box's own name: `(π₁p→cons,⊸ nil)`, the test, the arm taken when it holds,
    and the other.  The arms are read by REDUCING the matcher at each value of `Bool`, so nothing
    here depends on the order the alternatives were written in or on how the `match` compiled. -/
partial def guardLabel (s : FVarId) (body₀ : Expr) : MetaM (Option String) := do
  -- A step is a `def` around its own `match`, so the matcher is behind one delta; the ARMS are then
  -- taken by `whnfCore`, which fires the matcher without unfolding a numeral into a constructor.
  let some ma ← Meta.matchMatcherApp? (← Meta.whnfD body₀) | return none
  unless ma.discrs.size == 1 && ma.alts.size == 2 && ma.remaining.isEmpty do return none
  unless (← Meta.whnfD (← Meta.inferType ma.discrs[0]!)).isConstOf ``Bool do return none
  let hd := mkAppN (mkConst ma.matcherName ma.matcherLevels.toList) ma.params
  -- An ARM is a map like any other, and it is written INSIDE this label, so its discard is written
  -- too: one rule decides the `⊸`, and it is `mapLabel`'s.
  let arm (v : Name) : MetaM String := do
    let b ← Meta.whnfCore (mkAppN hd (#[ma.motive, mkConst v] ++ ma.alts))
    mapLabel (← Meta.mkLambdaFVars #[.fvar s] b) false
  -- The test is a value computed from the input and named as ONE word — it labels no wire of its
  -- own, so its steps are written with nothing between them (`π₁p`), where a composite wants a space.
  let discr ← match ← valSteps s ma.discrs[0]! with
    | some steps => pure (String.join steps.toList)
    | none => plain ma.discrs[0]!
  return some ("(" ++ discr ++ "→" ++ (← arm ``Bool.true) ++ ","
    ++ (← arm ``Bool.false) ++ ")")

/-- The label of a MAP given by its function.  A cons cell is `cons`, a projection its `π`, a
    constant the thing it creates — each read off the function's own body, so the next map built
    the same way gets the same name without anything being added here.

    `wired` is whether the PICTURE carries the map's discard: a box drawn for a constant map has no
    input port, and that missing port IS the `⊸`, so the box's own label does not write one.  The
    same map written inside another label — `E(…)`, `⦇…⦈`, the arm of a guard — has no port to say
    it, so there the `⊸` is written. -/
partial def mapLabel (f : Expr) (wired : Bool) : MetaM String := do
  -- NO DELTA: a map that has a NAME is written by that name (`graph`'s own unexpander says so), and
  -- how that name prints is its delaborator's business — one place, beside the declaration.  `whnfD`
  -- here opened every named map into its body and the label came back as the implementation:
  -- `moves` as `fun v k i => v ⟨…⟩`, `paths` as the function `⦇gen⦈concat` computes, because the
  -- walk went on through `Cat.comp` into the category instance's own `comp`.  `whnfCore` leaves a
  -- constant alone and still beta/eta-reduces and fires a matcher, which is all an anonymous
  -- `fun p => cat p.1 p.2` at a use site needs; a name the note draws OPENED says so with
  -- `@[diag_unfold]`, which `labelTree` has already applied wherever it is spelled.
  let f ← Meta.whnfCore f
  let f := (← branchForm? f).getD f
  if f.isLambda then
    return ← Meta.lambdaBoundedTelescope f 1 fun xs body => do
      let some x := xs[0]? | plain f
      let l ← bodyLabel x.fvarId! body f
      if wired || (betaHead body).containsFVar x.fvarId!
          || !(← hasStrands (← Meta.inferType x)) then return l
      return "⊸ " ++ l
  match f.getAppFnArgs with
  | (``Prod.fst, _) => return "π₁"
  | (``Prod.snd, _) => return "π₂"
  -- A CONSTRUCTOR HANDED THE INPUT WHOLE is the same box as one handed its factors, so it gets the
  -- same name: `tip`, never `Tree.tip`.  One rule, both spellings.
  | _ => do if let some n ← ctorName? f then return n else plain f

end

/-! ### The shape of a label

A `String` holds the note's SPELLING and none of its SHAPE: the note sets a family's index as a
SUBSCRIPT (`α`#sub[`A`]) and a symmetric division as a FRACTION, and either may stand inside another
operator's brackets (`⦇`$frac(F(∋)R, ∋)$`⦈`).  `labelTree` is the one spelling, and `Lbl.flat` is
what it looked like before — a box and a bead each get one string, and only the commutative panel,
which sets typst content, reads the tree.  Every clause of the labeller therefore builds an `Lbl`
and the two ways of writing it can never disagree. -/

/-- A label's shape.  `sub` is an index set under its head, `frac` the note's symmetric division,
    `seq` two parts written one after the other.

    A FRACTION'S BAR DELIMITS ITS NUMERATOR, so `num` is held at the LOOSEST precedence wherever the
    fraction stands — `⦇`$frac(F(∋)R, ∋)$`⦈` and not `⦇`$frac((F(∋)R), ∋)$`⦈`.  The inline spelling
    has no bar and needs the brackets precedence would have put there, and `tight` is whether it
    does: asked of the printer at both precedences, never of the spelling of the answer. -/
inductive Lbl where
  | text (s : String)
  | sub (base index : Lbl)
  | frac (num den : Lbl) (tight : Bool)
  | seq (parts : Array Lbl)
  deriving Inhabited, BEq

/-- THE FLAT SPELLING, which is what a string label always was: a division writes the note's inline
    `%` (`F(∋)R%∋`), and A COMPONENT'S INDEX IS DROPPED — it is the `sub` constructor and nothing
    else that says so, never a name or a slice of the string.  A COMMUTATIVE panel's arrow runs
    between two NAMED objects and the index is what tells `α`#sub[`A`] from `α`#sub[`B`]; every flat
    consumer is a string or circuit picture, where the bead IS the natural family and the object it
    is taken at is the wire it sits on, drawn and labelled beside it.  An index written there is the
    wire's own name spelled a second time. -/
partial def Lbl.flat : Lbl → String
  | .text s => s
  | .sub b _ => b.flat
  | .frac n d t => (if t then "(" ++ n.flat ++ ")" else n.flat) ++ "%" ++ d.flat
  | .seq ps => String.join (ps.toList.map Lbl.flat)

/-- Nested sequences opened out and adjacent text merged, so a tree with no shape in it is ONE
    `text` and is written exactly as the string label was. -/
partial def Lbl.norm (l : Lbl) : Lbl :=
  match go l with
  | #[x] => x
  | ps => .seq ps
where
  go : Lbl → Array Lbl
    | .text "" => #[]
    | .text s => #[.text s]
    | .seq ps => ps.foldl (fun acc p => (go p).foldl push acc) #[]
    | .sub b i => #[.sub b.norm i.norm]
    | .frac n d t => #[.frac n.norm d.norm t]
  push (acc : Array Lbl) (x : Lbl) : Array Lbl :=
    match acc.back?, x with
    | some (.text a), .text b => acc.pop.push (.text (a ++ b))
    | _, _ => acc.push x

instance : Coe String Lbl := ⟨Lbl.text⟩
instance : HAppend Lbl Lbl Lbl := ⟨fun a b => .seq #[a, b]⟩
instance : HAppend String Lbl Lbl := ⟨fun a b => .seq #[.text a, b]⟩
instance : HAppend Lbl String Lbl := ⟨fun a b => .seq #[a, .text b]⟩

/-- A term's printed spelling as a leaf of the tree — the printer's answer has no shape in it. -/
def txt (e : Expr) : MetaM Lbl := return .text (← plain e)

/-- The note's juxtaposition spacing between two labels, decided on their flat spelling (`juxt`), so
    one rule answers for the string and for the tree alike. -/
def juxtL (a b : Lbl) : Lbl :=
  if juxt a.flat b.flat == a.flat ++ b.flat then a ++ b else a ++ " " ++ b

/-- `sep` between the parts. -/
def Lbl.join (sep : String) (ps : Array Lbl) : Lbl :=
  ps.foldl (fun acc p => if acc == Lbl.text "" then p else acc ++ sep ++ p) (Lbl.text "")

/-- `applyLabel` with the operand already a tree: the join is the OPERAND's, read off its flat
    spelling exactly as the string rule reads it. -/
def applyLabelL (f : String) (a : Lbl) (j : Join) : Lbl :=
  if j == .bracket || (oneChar f && j == .name) then f ++ a else f ++ "(" ++ a ++ ")"

/-- A CONVERSE WITH A NAME OF ITS OWN (CLAUDE.md): the membership's is `∈`, and `∋°` makes the
    reader undo one level of indirection to get back to it.  Decided by the OPERAND's head constant,
    so every spelling of `∋` goes the same way — and read in TWO places, the labeller's `°` clause
    and the circuit exporter's, so the name a box carries and the box drawn cannot disagree. -/
def namedRecip (r : Expr) : Option String :=
  if r.isAppOf ``Freyd.Alg.PowerAllegory.eps then some "∈" else none

/-- The one FIELD of a one-field record IS that record (`ExprReader.unprojRecord?`) — EXCEPT where
    the record is an INSTANCE.  A class with one field is a one-field record, so `m + 1`, which is
    `HAdd.hAdd` at `instHAdd`, was read as its own instance and the label came out `instHAdd`, with
    the two operands dropped.  An instance argument is the elaborator's business and no factor of a
    name the note writes — the same rule `headShow` keeps — and the BINDER INFO of the projection's
    structure argument is what says so, never the head's name or the field's. -/
def unprojNoted? (e : Expr) : MetaM (Option Expr) := do
  if let .const n _ := e.getAppFn then
    if let some pi := (← getEnv).getProjectionFnInfo? n then
      let fi ← Meta.getFunInfoNArgs e.getAppFn (pi.numParams + 1)
      if (fi.paramInfo[pi.numParams]?.map (·.isInstImplicit)).getD false then return none
  unprojRecord? e

/-- THE CARRIER OF A COPRODUCT IS THE SUM ITSELF: an object that some `Coproduct s a b` in scope is
    the coproduct of is the note's `a+b`.  Read off the structure's TYPE and not by a delaborator,
    because the carrier is a BINDER and there is no application to delaborate — the mirror of
    `RelProd.p`, where the apex IS the application and its two objects stand in its type. -/
def coprodCarrier? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      let t ← Meta.whnf d.type
      let args := t.getAppArgs
      if t.isAppOf ``Freyd.Alg.Coproduct && args.size == 5 then
        if ← Meta.isDefEqGuarded args[2]! e then return some (args[3]!, args[4]!)
  return none

mutual

/-- A term, spelled the way the BOOK spells it — juxtaposition for composition, `°` for the converse
    — rather than left to the pretty printer, because it is read beside a picture, where
    `CartBicat.conv S` is noise and `S°` is the thing itself.  `°`, not the paper's `†`: these terms
    are read against Freyd throughout, and one symbol per idea beats matching two.

    PARENTHESISED BY PRECEDENCE, composition loosest and `°` tightest, so the bracketing is visible.
    That matters: several steps of a `calc` do nothing but re-bracket, and the term column is the
    only place a reader can see them happen — the picture, quite correctly, does not change.

    RECURSIVE THROUGH THE BRACKETING OPERATORS TOO.  `⦇…⦈`, `E(…)` and `…%∋` delimit their operand,
    so a composite inside one is still a composite of the note's: `⦇S%∋ est(R°)⦈`, never
    `⦇S%∋ ≫ est(R°)⦈`, which is what the raw printer hands back for the whole application. -/
partial def labelTree (prec : Nat) (e : Expr) : MetaM Lbl := do
  -- A NAME THE NOTE DRAWS OPENED is opened wherever it is SPELLED, not only where a factor of a
  -- composite is drawn: a case study's middle bead is ONE bead `⦇Salg⦈` whose whole content is the
  -- algebra, and `@[diag_unfold]` is the statement that the note writes that algebra out.
  let e' ← openNotedAll e
  if e' != e then return ← labelTree prec e'
  -- A ONE-FIELD RECORD IS ITS FIELD, the rule `plain` already prints by: the object `⟨X⟩` of a
  -- category of sets IS the set `X`, so the wrapper must come off HERE too or the clause below
  -- dispatches on `RelSet.mk` and the operator inside — a product, a sum — is never seen.
  if let some x ← unwrapRecord? e then return ← labelTree prec x
  -- …and its FIELD is that record, the same identification read the other way: `E[A].carrier` is
  -- the object `E[A]`, and a projection Lean wrote only because `×` is a type former is not a step
  -- of the algebra.  Each peel strictly shrinks the term, so the two cannot loop through each other.
  if let some x ← unprojNoted? e then return ← labelTree prec x
  -- A FIELD LEAN LEFT AS A POSITION is written through the field's own name, or the notation keyed
  -- on it — `RelProd.p`'s `a×b` — never fires and the label prints `inst✝.1`.
  if let some x ← namedProj? e then return ← labelTree prec x
  -- …and a field of a bundle with no name of its own is the field's DEFINITION at that bundle: the
  -- product relator's action is `G(R)×G'(R)`, where its head prints `prod` for every factor alike.
  if let some x ← openBuiltField? e then return ← labelTree prec x
  let wrap (p : Nat) (s : Lbl) : Lbl := if prec > p then "(" ++ s ++ ")" else s
  -- …and an object that is a COPRODUCT'S CARRIER is that coproduct: `A+B`, never the letter the
  -- statement bound it by, which names the sum to nobody.  `Prod`'s `a×b` read the other way round.
  if let some (a, b) ← coprodCarrier? e then
    return wrap 1 ((← labelTree 2 a) ++ "+" ++ (← labelTree 2 b))
  -- `cp` is the precedence the OPERANDS are set at, which is not always one above the operator's:
  -- composition is written by juxtaposition, so it has no symbol to separate its operands and every
  -- operand that is itself an operator has to carry brackets or `R (S ∩ T)` comes out reading as
  -- `(R S) ∩ T`.
  let arrows : Array Expr → MetaM (Array Expr) := homArgs
  let bin (p : Nat) (op : String) (args : Array Expr) (cp : Nat := p + 1) : MetaM Lbl := do
    match lastTwo (← arrows args) with
    | some (f, g) => return wrap p ((← labelTree cp f) ++ op ++ (← labelTree cp g))
    | none => txt e
  -- The one argument of a unary operator, at the precedence its operand is set at.
  let un (p cp : Nat) (pre post : String) (args : Array Expr) : MetaM Lbl := do
    match (← arrows args).back? with
    | some r => return wrap p (pre ++ (← labelTree cp r) ++ post)
    | none => txt e
  match e.getAppFnArgs with
  | (``Cat.id, _) => return "𝟙"
  -- THE INJECTIONS OF A COPRODUCT ARE THE NOTE'S `l` AND `r`: `u₁`/`u₂` are the structure's own
  -- field names and `u₁(Cop)` spells the bundle, which is a thing no picture draws.
  | (``Freyd.Alg.Coproduct.u₁, _) => return "l"
  | (``Freyd.Alg.Coproduct.u₂, _) => return "r"
  -- A MAP is named from its own function, wherever it is spelled: the box the circuit draws for it
  -- and the `E(…)` of a label are the same name, so the rule sits here and not beside the drawing.
  | (``Freyd.Alg.RelSet.graph, args) =>
    match args.back? with
    | some f => return .text (← mapLabel f false)
    | none => txt e
  | (``Freyd.Diag.CartBicat.Δ, _) => return "◁"
  | (``Freyd.Diag.CartBicat.«∇», _) => return "▷"
  | (``Freyd.Diag.CartBicat.«!», _) => return "⊸"
  | (``Freyd.Diag.CartBicat.«?», _) => return "⟜"
  -- BY THEIR DEFINITIONS, not by name.  `cap` and `cup` are `def`s over the four generators —
  -- `cap = ▷⊸`, `cup = ⟜◁` — and a term column that prints them as words introduces two more
  -- things to look up, in a note whose whole claim is that everything is built from those four.
  -- The pictures already draw them as the merge and the fork with their dot.
  | (``Freyd.Diag.CartBicat.cap, _) => return "▷⊸"
  | (``Freyd.Diag.CartBicat.cup, _) => return "⟜◁"
  | (``Freyd.Diag.top, _) | (``Freyd.Alg.topHom, _) => return "⊤"
  | (``Freyd.Diag.Biprod.bot, _) => return "⊥"
  -- The allegory's zero keeps the book's own `𝟘`; the tape layer's is `⊥` and they are different
  -- arrows of different towers, so they are not spelled alike.
  | (``Freyd.Alg.DistributiveAllegory.zero, _) => return "𝟘"
  | (``Freyd.Alg.PowerAllegory.eps, _) => return "∋"
  -- The union of a PAIR of sets, which the note writes `cup` on the box after a `⟨,⟩` fork.  Its
  -- `RelProd` argument is the product the fork lands in, already drawn as the two wires, so the
  -- label is the name alone — `cup (relProd …)` writes the picture's own geometry into it.
  | (``Freyd.Alg.cup, _) => return "cup"
  -- No `α`, `λ` or `ρ` cases: this branch's monoidal structure is STRICT, so the coherence arrows
  -- do not exist and no statement can mention one.
  | (``Freyd.Diag.SymMonCat.swap, _) => return "σ"
  -- Composition is JUXTAPOSITION, which is why it cannot be an unexpander: `f g` parses as an
  -- application, so only a labeller may write it.
  -- FLAT, because composition is associative and the picture cannot tell `(fg)h` from `f(gh)`: a
  -- composite operand re-bracketed by the reader's own printer (`S° (F(X)R)`) is one more thing to
  -- undo, so the whole run is written as the note writes it.
  | (``Cat.comp, args) =>
    -- COMPOSITION IS NOT A HEAD THE NOTE WRITES — juxtaposition is the absence of an operator — so a
    -- composite the note spells as ONE arrow is rewritten to it first: `F(X)[T,U]` is `[T,(X×𝟙)U]`,
    -- the relator slid into the bracket.  Every other head keeps the notation its clause writes,
    -- which is what keeps `Λ R` out of this and out of the loop through `singletonMap`.
    if let some r ← rewriteHead? e then return ← labelTree prec r
    if lastTwo args |>.isNone then txt e else do
      let mut s : Lbl := .text ""
      for t in (← labelRunT e) do s := juxtL s t
      -- JUXTAPOSITION BINDS TIGHTER THAN THE LATTICE OPERATORS:
      -- `⊸ nil ∪ (p×𝟙)cons` is a union of two composites and needs no brackets, where
      -- `old (R∩H)` does — so composition sits ABOVE `∩`/`∪` and below `°`.
      return wrap 1 s
  | (``Freyd.Diag.LinearBicat.bcomp, args) => bin 0 " ⨟• " args
  | (``Freyd.Diag.SymMonCat.tensHom, args) => bin 1 " ⊗ " args
  | (``Freyd.Alg.Allegory.inter, args) | (``Freyd.Diag.meet, args) => bin 0 "∩" args
  | (``Freyd.Diag.Biprod.union, args) | (``Freyd.Alg.DistributiveAllegory.union, args) =>
    bin 0 " ∪ " args
  | (``Freyd.Diag.ClosedLinearBicat.residual, args)
  | (``Freyd.Alg.DivisionAllegory.div, args) => bin 1 " / " args
  -- The note sets the left division TIGHT (`⦇S⦈°\X`, 11.6.4b) where `/` and `∪` keep their spaces.
  | (``Freyd.Alg.leftDiv, args) => bin 1 "\\" args
  | (``Freyd.Alg.symmDiv, args) => bin 1 " /ₛ " args
  | (``Freyd.Alg.impl, args) => bin 1 " ⇨ " args
  | (``Freyd.Alg.thenRel, args) => bin 1 " ⨾ " args
  -- A CONVERSE WITH A NAME OF ITS OWN IS WRITTEN BY THAT NAME (CLAUDE.md): the membership's is `∈`,
  -- and `∋°` makes the reader undo one level of indirection to get back to it.  Decided by the
  -- OPERAND's head constant, so every spelling of `∋` goes the same way.
  | (``Freyd.Alg.Allegory.recip, args) | (``Freyd.Diag.CartBicat.conv, args) => do
    match (← arrows args).back? with
    | some r => match namedRecip r with
      | some n => return n
      | none => un 3 3 "" "°" args
    | none => txt e
  | (``Freyd.Diag.ClosedLinearBicat.perp, args) => un 3 3 "" "⊥" args
  -- `∼` binds tighter than everything but `°`, so its operand is set at `°`'s precedence.
  | (``Freyd.Alg.neg, args) => un 3 3 "∼" "" args
  -- The BRACKETING operators: their own delimiters separate the operand, so it is set at the
  -- loosest precedence and carries no brackets of its own — and, being a term like any other, it
  -- is spelled by this same rule rather than by the printer.
  | (``Freyd.Alg.est, args) => un 4 0 "est(" ")" args
  -- The POWER RELATOR's action on an arrow, the note's `P(R)`.  A relator applied to an arrow takes
  -- the same brackets as `F(R)` and `T(R)`; its definition is an intersection of two divisions,
  -- which is the relator's PROOF and not its picture.
  | (``Freyd.Alg.powerRel, args) => un 4 0 "P(" ")" args
  | (``Freyd.Alg.relCata, args) | (``Freyd.Alg.InitialAlgebra.cata, args) => un 4 0 "⦇" "⦈" args
  -- The EXISTENTIAL IMAGE is a relator's action on an arrow, so it takes the brackets every applied
  -- operator takes and its operand is a term of the note's, respelled here — the same clause `P(R)`
  -- has, one line up, for the same reason.
  | (``Freyd.Alg.existsImage, args) => un 4 0 "E(" ")" args
  -- THE POWER OBJECT is that same `E` at an OBJECT, and its operand is a term of the note's for
  -- the same reason the arrow's is: the printer sets a product off from its factors (`E ([A] ×
  -- [A])`) where the note writes `E([A]×[A])`, and how the letter joins is the note's own rule —
  -- `E[A]` against the brackets the printer closed, `EA` against a name, parentheses otherwise.
  | (``Freyd.Alg.PowerAllegory.powerObj, args) =>
    match args.back? with
    | some x => return applyLabelL "E" (← labelTree 0 x) (← objJoin x)
    | none => txt e
  -- The TRANSPOSE IS A SYMMETRIC DIVISION, and INLINE the note writes it with its own `%`:
  -- `S%∋`, `(F(∋)S)%∋`, `𝟙%∋`.  The `%` binds tighter than composition, so the inline numerator
  -- carries brackets at juxtaposition's own precedence: `F(∋)S%∋ thin(Q)` would otherwise read as
  -- `F(∋)` composed with `S%∋`.  SET AS A FRACTION the bar delimits it and those brackets come off,
  -- so the tree holds the numerator loose and says whether the inline form wants them — which is
  -- the printer's own answer at the two precedences, not a test on the spelling it returned.
  -- The TWO-ARROW form `𝟙%∋ E(R)` is the PICTURE's, written by the spine rewrite before anything
  -- is labelled (`labelRunT`); a label has no picture to split.
  | (``Freyd.Alg.Λ, args) => do
    match (← arrows args).back? with
    | some r =>
      let loose ← labelTree 0 r
      return .frac loose (.text "∋") ((← labelTree 2 r) != loose)
    | none => txt e
  -- The junction's own brackets delimit its operands (`[nil,⊸ nil ∪ cons]`, 13.3.3b): loosest
  -- precedence inside, nothing after the comma, as the note sets it.
  | (``Freyd.Alg.junc, args) => do
    match lastTwo (← arrows args) with
    | some (f, g) => return "[" ++ (← labelTree 0 f) ++ "," ++ (← labelTree 0 g) ++ "]"
    | none => txt e
  -- The TYPE FUNCTOR's action on an arrow is a relator's action like any other, so it takes the same
  -- brackets as `F(R)`: `T(f)`, never `T f`, juxtaposition being composition and nothing else.  The
  -- letter is `typeRelator`'s own unexpander's (`diag/StrDiagNames.lean`), which the lane wears too.
  | (``Freyd.Alg.typeMap, args) => un 4 0 "T(" ")" args
  -- The RUBY TRIANGLE is an operator applied to an arrow, so it takes the brackets every applied
  -- operator takes (CLAUDE.md): `tri(f)`, never `tri f`, which reads as `tri` composed with `f`.
  | (``Freyd.Alg.tri, args) => un 4 0 "tri(" ")" args
  -- The LEAST FIXED POINT is the note's `(μX : S°F(X)R)`.  Its body is a term of the note's like any
  -- other — the binder is an arrow the picture draws a wire for — so its composition is
  -- juxtaposition, where the printer's own `≫` survived because the label was the raw printer's.
  | (``Freyd.Alg.mu, args) =>
    match args.back? with
    | some φ => Meta.lambdaBoundedTelescope φ 1 fun xs b => do
      match xs[0]? with
      | some x => return "(μ" ++ (← x.fvarId!.getUserName).toString ++ " : " ++ (← labelTree 0 b) ++ ")"
      | none => txt e
    | none => txt e
  -- A relator's action on an ARROW is the ONE bracket no term carries: `F(⦇R⦈)`, the note's way of
  -- saying the argument is applied and not composed.
  -- AN OBJECT'S PRODUCT is the note's `×` between its two factors, each spelled HERE: a factor the
  -- printer wrote with a space of its own (`Bag Job`) is welded shut by closing the whole
  -- application up, which is what a tight head would do.
  | (``Prod, #[a, b]) => return wrap 1 ((← labelTree 2 a) ++ "×" ++ (← labelTree 2 b))
  | (``Freyd.Functor.map, _) =>
    -- A RELATOR WHOSE ACTION THE NOTE WRITES OUT is rewritten to that spelling first, the same
    -- `diag_rewrite` step the composite takes and for the same reason: the note keeps the letter on
    -- the OBJECTS (`F([A]×[A])`) and spells the ARROW (`𝟙×list((R×R)°)`), and only an equation
    -- beside the relator can say so.  The right side is headed by the operator it spells out, never
    -- by `Functor.map`, so no rewrite reaches this clause twice.
    if let some r ← rewriteHead? e then return ← labelTree prec r else
    match functorMap? e with
    | some (f, r) =>
      let h : Lbl ← match ← relatorName? f with
        | some n => pure (.text n)
        | none => labelTree 4 f
      return h ++ "(" ++ (← labelTree 0 r) ++ ")"
    | none => txt e
  -- A BIFUNCTOR'S action takes the same bracket and BOTH its arrows: `F(𝟙,f)`, `F(f,T(f))`.  An
  -- unexpander cannot write it — `F(𝟙,f)` is no term — and the one beside the constant prints the
  -- second argument alone, so `F.map (𝟙 A) f` and `F.map g f` come out the same picture.
  | (``Freyd.Alg.BiRelator.map, args) => do
    match lastTwo (← arrows args) with
    | some (x, y) => do
      let fns ← args.filterM fun a => return (← Meta.inferType a).isAppOf ``Freyd.Alg.BiRelator
      match fns.back? with
      | some fn => return (← labelTree 4 fn) ++ "(" ++ (← labelTree 0 x) ++ "," ++ (← labelTree 0 y) ++ ")"
      | none => txt e
    | none => txt e
  | (c, args) =>
    -- A HEAD THE LABEL HAS NO SPELLING OF is rewritten along the note's own equations first, and
    -- ONLY here: `arm₂` of an algebra is the arm the note names, while every head with a clause
    -- above is already written as the note writes it — `Λ R` is the `𝟙%∋ E(R)` its clause writes,
    -- not the composite the PICTURE splits it into, and rewriting it here loops through
    -- `singletonMap` and back.
    if let some r ← rewriteHead? e then return ← labelTree prec r
    if tightHeads.contains c then return (← plain e).replace " " "" else do
    -- A FUNCTOR'S ACTION ON OBJECTS joins by the note's own rule (CLAUDE.md): a ONE-LETTER functor
    -- closes up against a name (`FA`, `EFA`) or an operand the printer already bracketed (`E[A]`),
    -- and every other application takes parentheses (`tree(A)`, `E(bag(Job))`, `F([A]×[A])`).  Head
    -- and operands are spelled APART, each by its own rule: an operand is an object of the note's,
    -- respelled here, and the head keeps the name its lane wears.  SEVERAL operands are the note's
    -- comma list inside that bracket (`F(A,C)`), which is `BiRelator.map`'s `F(𝟙,f)` on objects.
    -- AFTER the spellings above: a head the note writes ITSELF (`E A`, an unexpander's own
    -- notation) is that spelling, and the action rule answers where the printer wrote none.
    -- THE OPERANDS RESPELLED HERE AND HANDED BACK TO THE PRINTER as locals of their own labels: what
    -- turns the operand of a head with no clause from Lean's `≫` into juxtaposition, under whatever
    -- brackets the head already writes.  APPLYING TAKES PARENTHESES (`appShow`), because
    -- juxtaposition is composition.  Those brackets are what separates an operand from the head, so
    -- where they are coming the operand is respelled at the TOP of its own precedence:
    -- `thin(prefix°×(⊤+⊤))`, not a second pair inside.  SOMETHING ALREADY DELIMITS IT in two ways,
    -- and both count: the brackets `appShow` is about to write, and a head whose OWN NOTATION
    -- delimits its operand — which is exactly a syntax with no identifier head, `stxHead`'s test,
    -- since a notation opens with an atom.  THE HEAD'S OWN PRINTER TAKES A NAME, so an operand handed
    -- back to it is its FLAT spelling: a shape set inside a notation nobody here wrote has nowhere
    -- to be set.
    let stx ← PrettyPrinter.delab e
    let paren := (appParts stx).isSome || (stxHead stx).isNone
    let rec respell : List Expr → Expr → MetaM Lbl
      | [], t => return .text (← appShow t)
      | a :: rest, t => do
        let nm := Name.mkSimple (← labelTree (if paren then 0 else 4) a).flat
        Meta.withLocalDeclD nm (← Meta.inferType a) fun x =>
          respell rest (t.replace fun s => if s == a then some x else none)
    if let some (f, xs) ← functorObj? e then
      -- THE PRINTER'S OWN NOTATION FOR AN ACTION STANDS: a delaborator keyed on the field writes the
      -- note's spelling of the object (`A[n]` for `Vec(n)` at `A`), and only the bare field access
      -- `F.obj A`, the printer's default, is re-set by the join rule below.  Closed up like a tight
      -- head, and NOT respelled operand by operand: an operand handed back as a local is an
      -- identifier the notation cannot open, so `A[n][3]` came out `A[3][n]`, the indices reversed.
      -- …AND JUXTAPOSITION IS NOT SUCH A NOTATION.  Where the printer wrote the action by
      -- juxtaposition, the only brackets it set are Lean's own GROUPING of a nested operand, which
      -- say nothing about how the NOTE brackets it: cutting the spaces out of the printed string
      -- kept them, and `L (G A)` came out `L(GA)` where the note writes the chain `LGA`.  The join
      -- rule below answers for it, as it does for the field access.
      unless (← printsAsField e) || (appParts stx).isSome do return (← plain e).replace " " ""
      let parts ← xs.mapM (labelTree 0)
      let j ← if xs.size == 1 then objJoin xs[0]! else pure Join.other
      return applyLabelL (← functorName f) (Lbl.join "," parts) j
    -- A COMPONENT OF A FAMILY THE THEORY DECLARES is its letter with its index BENEATH.
    if let some (h, ix) ← indexedComponent? e then return .sub (.text h) (← labelTree 0 ix)
    -- A COMPONENT OF A FAMILY the statement BINDS is ONE NAME, head and index closed up: the note
    -- writes `φ`'s component at `A` as `φA` and `χ`'s at `GA` as `χGA`, because the letter is the
    -- statement's own and says nothing without the index the statement wrote beside it.  Its head is
    -- a free variable and has no constant for `tightHeads`, so the test is `isComponent`'s, on the
    -- TYPE.  A family with a NOTATION of its own is the clause below: there the letter stands alone
    -- and the index is what the notation dropped.
    if ← isComponent e then
      -- A BEAD'S INDEX IS THE OBJECT WIRE UNDER IT, so the string label writes the letter ALONE and
      -- the index goes BENEATH, the shape a family with a notation of its own gets above: a label
      -- that writes it too spells one object twice and lets the two drift (`est(R)` over `[m + 1]`,
      -- never `est(R(m+1))`).  The commutative panel, having no wire to read it off, keeps the
      -- subscript, which is what `Lbl.sub` is: the index is dropped by `flat` and by nothing else.
      let ix ← e.getAppArgs.toList.mapM (labelTree 0)
      return .sub (.text (← plain e.getAppFn)) (Lbl.join "," ix.toArray)
    else do
    -- A PRODUCT OF ARROWS is its two arrows and nothing else.  The head's own printer writes the
    -- OBJECT it is taken at too (`wrap × 𝟙 [[X]]`), and an object inside a bead's label is the wire
    -- under it spelled twice; read as a product map off the TYPE, so every spelling goes one way.
    if let some (x, _) := homObjs? (← Meta.inferType e) then
      if let some (φ, ψ) ← asProdMap? (← Meta.inferType x) e then
        return wrap 1 ((← labelTree 2 φ) ++ "×" ++ (← labelTree 2 ψ))
    -- A SUM OF ARROWS the same way, and for the same reason: the two coproducts `sumMap` runs
    -- between are the objects the picture already draws at the edge's ends.
    if let some (φ, ψ) ← asSumMap? e then
      return wrap 1 ((← labelTree 2 φ) ++ "+" ++ (← labelTree 2 ψ))
    -- EVERY OTHER HEAD KEEPS THE PRINTER'S SPELLING — a delimited notation (`thin(Q)`) is the
    -- constant's own business, and a clause here would be a second copy of it — but its ARROW
    -- arguments are terms of the note's like any other, so each is respelled HERE and handed back to
    -- the printer as a local of that name.  That is what turns the operand of a head with no clause
    -- from Lean's `≫` into juxtaposition, under whatever brackets the head already writes.
    -- A NAME THE PRINTER WROTE AN OPERATOR INSIDE keeps its brackets wherever it is a factor of a
    -- composite: `(new ∪ old)R;H` reads as `((new ∪ old)R);H` where the note means
    -- `(new ∪ old)(R;H)`.  ON THE IDENT ALONE, the one label built by no rule of this file —
    -- everything else is bracketed by whatever rule builds it.  At composition's own precedence,
    -- which is what every operator looser than juxtaposition is set at.
    let out ← respell (← arrows args).toList e
    match stxPeel stx with
    | .ident _ _ nm _ => return if oneToken nm.getString! then out else wrap 1 out
    | _ => return out

/-- THE FACTORS A LABEL WRITES, in diagram order, FLAT — composition's own factors, each spelled by
    the one rule above.

    NO TRANSPOSE IS OPENED HERE.  `Λ S` IS drawn as the unit bead `𝟙%∋` and `S` on the `E` lane, and
    the term the picture draws is rewritten to that shape along every SPINE it draws, at every lane
    depth, before anything is labelled (`StringDiagram.interp`, `ExprReader.rewriteSpine`,
    `Λ_eq_singleton_existsImage`) — which is the one place that rule belongs, because only a spine
    has the two beads to split into.  A second copy of it here fired where no spine goes, inside a
    fold's body and an `est(R)` argument, and wrote `⦇𝟙%∋ E(S)est(R°)⦈` for the note's `⦇S%∋ est(R°)⦈`.

    FLAT is the whole point of the array: juxtaposition is associative, so a bracket round the
    factors would say a grouping the note does not. -/
partial def labelRunT (e : Expr) : MetaM (Array Lbl) := do
  let e' ← openNotedAll e
  if e' != e then return ← labelRunT e'
  match e.getAppFnArgs with
  | (``Cat.comp, args) =>
    if (lastTwo args).isNone then return #[← labelTree 2 e]
    let mut out := #[]
    for f in factors e do out := out ++ (← labelRunT f)
    return out
  | _ => return #[← labelTree 2 e]

end

/-- A term's label as a TREE, at the top of its own picture or box: no outer parentheses. -/
def labelT (e : Expr) : MetaM Lbl := return (← labelTree 0 e).norm

/-- …and FLAT, which is every label a box, a bead or a wire carries. -/
def label (e : Expr) : MetaM String := return (← labelTree 0 e).flat

/-- The flat spelling at a given precedence, for the pictures that write one string. -/
def labelAt (prec : Nat) (e : Expr) : MetaM String := return (← labelTree prec e).flat

/-- The factors a label writes, flat. -/
def labelRun (e : Expr) : MetaM (Array String) :=
  return (← labelRunT e).map Lbl.flat

/-- A label in the PARTS the picture sets it in.  A SYMMETRIC DIVISION is the note's fraction, and a
    bar DELIMITS its numerator, so that part is spelled at the loosest precedence — `frac(F(∋)f, ∋)`,
    where the inline spelling has to write `(F(∋)f)%∋`.  Every other arrow is one part.  Dispatched
    on the HEAD CONSTANT, the same way the inline spelling above is, so no reader has to find the
    operator again by looking for a `%` in a string. -/
partial def labelPartsT (e : Expr) : MetaM (Array Lbl) := do
  let e' ← openNoted e
  if e' != e then return ← labelPartsT e'
  match e.getAppFnArgs with
  | (``Freyd.Alg.Λ, args) => do
    let arrows ← args.filterM fun a => return (homObjs? (← Meta.inferType a)).isSome
    match arrows.back? with
    | some r => return #[(← labelTree 0 r).norm, .text "∋"]
    | none => return #[← labelT e]
  | _ => return #[← labelT e]

/-- …and each part flat, for the pictures that write one string. -/
def labelParts (e : Expr) : MetaM (Array String) :=
  return (← labelPartsT e).map Lbl.flat

/-- A relator's own spelling as a LANE, in the NOTE's notation and not the pretty printer's.  A
    pairing, an identity, a composite and the product bifunctor have no name of their own, so they
    are written structurally — `⟨𝟙,T⟩`, `𝟙`, `list list`, `×` — and the length of that string is
    what reserves the lane's room, which is why it cannot be left to `Relator.comp list list`.
    Every head here is matched as an `Expr` head, so nothing rests on how a name prints.
    A composite is juxtaposition in DIAGRAM order — `comp F G` is `F` then `G` — and it is read off
    `wiresOf`, which is what drops the identity factors and flattens the nesting.

    EVERY OTHER LANE IS SPELLED BY THE ONE LABEL PRINTER — which is why this lives here and not
    beside the peel: a lane written with the raw printer came out `tree A`, `Op Char`, `TT.F A`,
    with the spacing of Lean's juxtaposition, beside an object wire the printer of this file had
    already set as `Op(Char)` in the SAME panel. -/
partial def relLabel (r : Expr) : MetaM String := do
  match r.getAppFnArgs with
  | (``Freyd.Alg.Relator.pair, args) =>
    match lastTwo args with
    | some (f, g) => return "⟨" ++ (← relLabel f) ++ "," ++ (← relLabel g) ++ "⟩"
    | none => label r
  | (``Freyd.Alg.Relator.prod, args) =>
    match lastTwo args with
    | some (f, g) => return (← relLabel f) ++ "×" ++ (← relLabel g)
    | none => label r
  | (``Freyd.Alg.Relator.comp, _) =>
    -- `wiresOf` is OUTERMOST first; juxtaposition is diagram order, so it is read back to front.
    let ws := wiresOf r
    if ws.isEmpty then return "𝟙"
    return " ".intercalate (← ws.toList.reverse.mapM relLabel)
  | (``Freyd.Alg.timesRel, _) => return "×"
  | (``Freyd.Alg.Relator.idRelator, _) => return "𝟙"
  | _ => label r

/-- A WIRE'S NAME, by the same printer as the object wire beside it. -/
def Wire.label : Wire → MetaM String
  | .rel r => relLabel r
  -- `(A×B)×−`, never `A×B×−`: a left factor that is itself a product must be bracketed or the
  -- label names a different lane.  The test is the product READER, not the printed string.
  | .timesL l => do
    let s ← _root_.Freyd.StrDiag.label l
    let par := (← splitTimes? (← Meta.inferType l) l).isSome
    return (if par then "(" ++ s ++ ")" else s) ++ "×−"

/-- Whether the local context carries a `Map` hypothesis for this arrow, exactly as the reader of
    the Lean statement reads it. -/
def hasMapHyp (e : Expr) : MetaM Bool := do
  unless e.isFVar do return false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    match d.type.getAppFnArgs with
    | (``Freyd.Alg.Map, args) => if args.back? == some e then return true
    | _ => pure ()
  return false

/-- Whether an arrow is a MAP — the circuit's chamfer decision, and the bead a string display lines
    up on next after a natural one (`Row.pin`).  Read off the term: a graph and an identity are maps,
    a transpose is a map, a composite and a product of maps are maps, and a hypothesis in scope says
    so for a variable.

    A NAMED map is a map.  `cons`, `nil`, `new`, the initial algebra `α` are `graph`s behind their
    own names, so stopping at the head constant draws every named FUNCTION as a relation; the last
    clause is one delta step — the same step `drawDecl` draws a def's body with — and the fuel is
    what a def spelled in terms of itself would otherwise cost. -/
partial def isMapOf (e : Expr) (fuel : Nat := 8) : MetaM Bool := do
  match e.getAppFnArgs with
  | (``Freyd.Alg.RelSet.graph, _) | (``Cat.id, _) | (``Freyd.Alg.Λ, _) => return true
  | (``Cat.comp, args) | (``Freyd.Alg.RelSet.rprodMap, args) =>
    match lastTwo args with
    | some (f, g) => return (← isMapOf f fuel) && (← isMapOf g fuel)
    | none => hasMapHyp e
  | _ =>
    if ← hasMapHyp e then return true
    if fuel == 0 then return false
    for n in [``Freyd.Alg.RelSet.graph, ``Cat.id, ``Freyd.Alg.Λ, ``Cat.comp,
              ``Freyd.Alg.RelSet.rprodMap] do
      if let some e' ← Meta.whnfUntil e n then return ← isMapOf e' (fuel - 1)
    -- AND AN EQUATION THE NOTE REWRITES ALONG answers this too: `arm₂` of a map is a map, and the
    -- label already writes the arm by its own name (`snoc`), so the box has to be that map's
    -- rectangle — the name and the shape are read off the same rewritten term or they disagree.
    if let some r ← rewriteHead? e then return ← isMapOf r (fuel - 1)
    return false

/-- ONE STEP OF THE SELECTOR CHAIN that goes inside a side: an operand of a binary operation, an arm
    of a junction, or the BODY of a least fixed point.  `.body` opens a BINDER, so the chain cannot
    be a list of operand indices: the bound arrow is a wire of the picture, and a number says
    nothing about where in the chain that wire is opened.

    It lives HERE, beside the label clause that opens the same binder, because BOTH routes walk a
    chain — the string route draws the bound arrow as a wire, the circuit route as a box — and a
    second spelling of the chain is what let one of them accept a selector the other refused. -/
inductive Sel where | inl | inr | body
  deriving Inhabited, DecidableEq

/-- The suffix the selector is written with — what `diag-export` parses and names the file by. -/
def Sel.suffix : Sel → String
  | .inl => ".inl" | .inr => ".inr" | .body => ".body"

/-- The function a least fixed point is taken of, `mu φ`, by the HEAD CONSTANT. -/
def muArg? (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``Freyd.Alg.mu, args) => args.back?
  | _ => none

end Freyd.StrDiag
