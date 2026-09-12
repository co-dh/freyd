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
-- The tape and first-order layers' own operators (`⨟•`, `⊥`, the four generators): `labelAt` is one
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
  -- length test `scripts/circuit`'s `lshow` writes as `len(e[1]) == 1 == len(head(e[2]))`; only
  -- the functor's half of it lived here, in `applyJoin`.
  | .ident _ _ n _ => if n.toString.length == 1 then .name else .other
  | .atom _ s => if s.length == 1 then .name else .other
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
  if j == .bracket || (f.length == 1 && j == .name) then f ++ a
  else f ++ "(" ++ a ++ ")"

/-- The join of what `applyLabel f` builds, which is decided by the label's OWN HEAD and nothing
    else: a one-letter functor heads what it builds, so `E(bag(Job))` juxtaposes under the next one
    exactly as `EA` does (`EF(bag(Job))`), while a longer name heads an application the next functor
    parenthesises. -/
def applyJoin (f : String) : Join := if f.length == 1 then .name else .other

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
      if f matches .ident .. then some (f, ops)
      else (appParts f).map fun (h, prev) => (h, prev ++ ops)
    | _, _ => none
  | _ => none

/-- One operand as the printer writes it, with the parentheses the printer put round it to keep it
    out of the juxtaposition dropped — the brackets of `f(…)` already separate it, and
    `thin((prefix°×(⊤+⊤)))` doubles them. -/
partial def stxShow (s : Syntax) : MetaM String := do
  match s.getArgs with
  | #[.atom _ "(", inner, .atom _ ")"] => stxShow inner
  | #[inner] => if s.isOfKind nullKind then stxShow inner else fmt s
  | _ => fmt s
where
  fmt (s : Syntax) : MetaM String := do
    let t := (toString (← PrettyPrinter.ppTerm ⟨s⟩)).replace "«" "" |>.replace "»" ""
    return " ".intercalate (t.splitOn "\n" |>.map fun u => u.trimAscii.toString)

/-- The printer's spelling of a term, with a JUXTAPOSED application re-set in the repo's brackets:
    `thin(Q)`, never `thin Q`, because juxtaposition is composition and the second reads as a
    composite of two arrows.  A head whose own notation already delimits its operands (`est(R)`,
    `⦇S⦈`, `F(f)`) has no juxtaposition to re-set and keeps what the printer wrote. -/
def appShow (e : Expr) : MetaM String := do
  match appParts (← PrettyPrinter.delab e) with
  | some (h, ops) =>
    return (← stxShow h) ++ "(" ++ String.intercalate "," (← ops.toList.mapM stxShow) ++ ")"
  | none => plain e

/-- The note's juxtaposition spacing (`scripts/relexpr.py`'s `spell`, the same rule the note's own
    generator writes back with): a bracket already separates two factors, so `F(∋)S` and `π₂R°`
    close up where `prefix list(p)` and `S%∋ est(R°)` cannot.  A factor OPENING with `(` keeps its
    space — `pick (schedule×𝟙)snoc` closed up would read as an application of `pick`. -/
def juxt (a b : String) : String :=
  if a.isEmpty || b.isEmpty then a ++ b
  -- `°` is a POSTFIX: it terminates its operand exactly as a closer does, so `est(R∩S°S)` must not
  -- come out `est(R∩S° S)`.
  else if ")]⟩⦈}°".contains a.back || "[⟨⦇{".contains b.front then a ++ b
  else a ++ " " ++ b

/-- The heads the note sets TIGHT: the power object, the initial type at an object, the product and
    the fork.  Lean's formatter always sets an application's argument off from its head (`P A`,
    `T A`) and an infix off from its operands (`A × B`, `⟨f, g⟩`) where the note closes them up; the
    SPELLING is untouched — it is what the `app_unexpander` beside the constant already printed.

    A RELATOR'S ACTION ON AN OBJECT IS NOT ONE OF THESE.  Closing the whole application up welds the
    head's own spelling shut (`(RT.F A)([A] × [A])` came out `(RT.FA)([A]×[A])`), and whether it
    juxtaposes at all is the note's join rule, which needs head and operand apart: `applyLabel`.

    AN ACTION ON AN ARROW IS NOT ONE OF THESE, however tight its object action sets.  `E(R)` is an
    operator APPLIED to a term of the note's, so its operand is respelled here (the `existsImage`
    clause below) where a tight head hands the whole application to the printer and the operand
    keeps whatever Lean wrote — which is how `E(mssPre)` stood where the note opens the definition. -/
def tightHeads : Array Name :=
  #[``Freyd.Alg.PowerAllegory.powerObj,
    ``Freyd.Alg.InitialAlgebra.t, ``Freyd.HasBinaryProducts.prod, ``Freyd.HasBinaryProducts.pair,
    ``Freyd.Alg.RelProd.p, ``Freyd.Alg.RelProd.pair,
    -- A COPRODUCT OBJECT sets as tight as a product apex: the note writes `GA+G'A`.  The sum of two
    -- ARROWS is not here for the reason the paragraph above gives — it welded `F(R)+F'(R)` shut to
    -- `FR+F'R` — and is read off the type instead, beside the product map (`asSumMap?`).
    ``Freyd.Alg.PositiveAllegory.coprod]

/-- The ARROW arguments of an application, picked by their TYPE and not by their position:
    `I.cata f hf` carries the algebra AND the proof it is one, and taking the last argument wrote
    `⦇hf⦈` for `⦇f⦈`. -/
def homArgs (args : Array Expr) : MetaM (Array Expr) :=
  args.filterM fun a => return (homObjs? (← Meta.inferType a)).isSome

/-! ### A MAP, named from its own function

A relation given as the graph of a function has no operator inside it, so no clause of `labelAt`
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

/-- The name of a value computed FROM THE INPUT, in diagram order: `p(π₁ s)` is `π₁p` — first the
    projection, then the test.  The input itself is the identity and contributes nothing, and an
    argument that does not mention the input is a PARAMETER of the function, not a step of the
    computation, so it stays inside the function's own name. -/
partial def valLabel (s : FVarId) (x : Expr) : MetaM String := do
  if x == .fvar s then return ""
  match x with
  | .proj ``Prod i st => return (← valLabel s st) ++ (if i == 0 then "π₁" else "π₂")
  | _ =>
    let args := x.getAppArgs
    match x.getAppFnArgs.1, args.back? with
    | ``Prod.fst, some st => return (← valLabel s st) ++ "π₁"
    | ``Prod.snd, some st => return (← valLabel s st) ++ "π₂"
    | _, _ =>
      let deps := args.filter fun a => a.containsFVar s
      if deps.size == 1 then
        let rest := args.filter fun a => !a.containsFVar s
        return (← valLabel s deps[0]!) ++ (← plain (mkAppN x.getAppFn rest))
      plain x

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

/-- The same answer for ANY declaration, for the one place a box writes a declaration by name and
    nothing else.  A namespace is what a resolver needs, and nothing inside a picture resolves a
    name, so `cat` is what the box says wherever `cat` is what was declared. -/
def declName? (e : Expr) : MetaM (Option String) := do
  let .const n _ := e.getAppFn | return none
  if ((← getEnv).find? n).isNone then return none
  -- THE PRINTER IS THE DEFAULT here too: a constant an `app_unexpander` gives a name of its own
  -- writes THAT name on the box, the way `relatorName?` takes the printer's.  A head that only
  -- drops the namespace chose nothing, so the constant's own last component stands.
  if let some h := stxHead (← PrettyPrinter.delab e) then
    if h.getString! != n.getString! then return some h.getString!
  return some n.getString!

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
    -- are `labelAt`'s own for `junc`, because it is the same arrow.
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
      return ← plain (mkAppN body.getAppFn (args.filter fun a => !a.containsFVar s))
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
  return some ("(" ++ (← valLabel s ma.discrs[0]!) ++ "→" ++ (← arm ``Bool.true) ++ ","
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
  -- `@[diag_unfold]`, which `labelAt` has already applied wherever it is spelled.
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

/-- A CONVERSE WITH A NAME OF ITS OWN (CLAUDE.md): the membership's is `∈`, and `∋°` makes the
    reader undo one level of indirection to get back to it.  Decided by the OPERAND's head constant,
    so every spelling of `∋` goes the same way — and read in TWO places, the labeller's `°` clause
    and the circuit exporter's, so the name a box carries and the box drawn cannot disagree. -/
def namedRecip (r : Expr) : Option String :=
  if r.isAppOf ``Freyd.Alg.PowerAllegory.eps then some "∈" else none

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
partial def labelAt (prec : Nat) (e : Expr) : MetaM String := do
  -- A NAME THE NOTE DRAWS OPENED is opened wherever it is SPELLED, not only where a factor of a
  -- composite is drawn: a case study's middle bead is ONE bead `⦇Salg⦈` whose whole content is the
  -- algebra, and `@[diag_unfold]` is the statement that the note writes that algebra out.
  let e' ← openNotedAll e
  if e' != e then return ← labelAt prec e'
  -- A ONE-FIELD RECORD IS ITS FIELD, the rule `plain` already prints by: the object `⟨X⟩` of a
  -- category of sets IS the set `X`, so the wrapper must come off HERE too or the clause below
  -- dispatches on `RelSet.mk` and the operator inside — a product, a sum — is never seen.
  if let some x ← unwrapRecord? e then return ← labelAt prec x
  -- …and its FIELD is that record, the same identification read the other way: `E[A].carrier` is
  -- the object `E[A]`, and a projection Lean wrote only because `×` is a type former is not a step
  -- of the algebra.  Each peel strictly shrinks the term, so the two cannot loop through each other.
  if let some x ← unprojRecord? e then return ← labelAt prec x
  -- A FIELD LEAN LEFT AS A POSITION is written through the field's own name, or the notation keyed
  -- on it — `RelProd.p`'s `a×b` — never fires and the label prints `inst✝.1`.
  if let some x ← namedProj? e then return ← labelAt prec x
  -- …and a field of a bundle with no name of its own is the field's DEFINITION at that bundle: the
  -- product relator's action is `G(R)×G'(R)`, where its head prints `prod` for every factor alike.
  if let some x ← openBuiltField? e then return ← labelAt prec x
  let wrap (p : Nat) (s : String) : String := if prec > p then "(" ++ s ++ ")" else s
  -- `cp` is the precedence the OPERANDS are set at, which is not always one above the operator's:
  -- composition is written by juxtaposition, so it has no symbol to separate its operands and every
  -- operand that is itself an operator has to carry brackets or `R (S ∩ T)` comes out reading as
  -- `(R S) ∩ T`.
  let arrows : Array Expr → MetaM (Array Expr) := homArgs
  let bin (p : Nat) (op : String) (args : Array Expr) (cp : Nat := p + 1) : MetaM String := do
    match lastTwo (← arrows args) with
    | some (f, g) => return wrap p ((← labelAt cp f) ++ op ++ (← labelAt cp g))
    | none => plain e
  -- The one argument of a unary operator, at the precedence its operand is set at.
  let un (p cp : Nat) (pre post : String) (args : Array Expr) : MetaM String := do
    match (← arrows args).back? with
    | some r => return wrap p (pre ++ (← labelAt cp r) ++ post)
    | none => plain e
  match e.getAppFnArgs with
  | (``Cat.id, _) => return "𝟙"
  -- A MAP is named from its own function, wherever it is spelled: the box the circuit draws for it
  -- and the `E(…)` of a label are the same name, so the rule sits here and not beside the drawing.
  | (``Freyd.Alg.RelSet.graph, args) =>
    match args.back? with
    | some f => mapLabel f false
    | none => plain e
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
    if let some r ← rewriteHead? e then return ← labelAt prec r
    if lastTwo args |>.isNone then plain e else do
      let mut s := ""
      for t in (← labelRun e) do s := juxt s t
      -- JUXTAPOSITION BINDS TIGHTER THAN THE LATTICE OPERATORS, as `relexpr.py`'s own `spell` sets
      -- them: `⊸ nil ∪ (p×𝟙)cons` is a union of two composites and needs no brackets, where
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
    | none => plain e
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
  -- The TRANSPOSE IS A SYMMETRIC DIVISION, and INLINE the note writes it with its own `%`:
  -- `⦇F(∋)R%∋⦈`, `𝟙%∋`, the numerator at composition's own precedence so a composite carries no
  -- brackets of its own.  The TWO-ARROW form `𝟙%∋ E(R)` is `labelRun`'s, because it is the two
  -- beads a PICTURE splits the transpose into and not a spelling of the term; a label nested inside
  -- another operator has no picture to split and takes the fraction, written flat.
  | (``Freyd.Alg.Λ, args) => un 1 1 "" "%∋" args
  -- The junction's own brackets delimit its operands (`[nil,⊸ nil ∪ cons]`, 13.3.3b): loosest
  -- precedence inside, nothing after the comma, as the note sets it.
  | (``Freyd.Alg.junc, args) => do
    match lastTwo (← arrows args) with
    | some (f, g) => return "[" ++ (← labelAt 0 f) ++ "," ++ (← labelAt 0 g) ++ "]"
    | none => plain e
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
      | some x => return "(μ" ++ (← x.fvarId!.getUserName).toString ++ " : " ++ (← labelAt 0 b) ++ ")"
      | none => plain e
    | none => plain e
  -- A relator's action on an ARROW is the ONE bracket no term carries: `F(⦇R⦈)`, the note's way of
  -- saying the argument is applied and not composed.
  -- AN OBJECT'S PRODUCT is the note's `×` between its two factors, each spelled HERE: a factor the
  -- printer wrote with a space of its own (`Bag Job`) is welded shut by closing the whole
  -- application up, which is what a tight head would do.
  | (``Prod, #[a, b]) => return wrap 1 ((← labelAt 2 a) ++ "×" ++ (← labelAt 2 b))
  | (``Freyd.Functor.map, _) =>
    -- A RELATOR WHOSE ACTION THE NOTE WRITES OUT is rewritten to that spelling first, the same
    -- `diag_rewrite` step the composite takes and for the same reason: the note keeps the letter on
    -- the OBJECTS (`F([A]×[A])`) and spells the ARROW (`𝟙×list((R×R)°)`), and only an equation
    -- beside the relator can say so.  The right side is headed by the operator it spells out, never
    -- by `Functor.map`, so no rewrite reaches this clause twice.
    if let some r ← rewriteHead? e then return ← labelAt prec r else
    match functorMap? e with
    | some (f, r) =>
      return ((← relatorName? f).getD (← labelAt 4 f)) ++ "(" ++ (← labelAt 0 r) ++ ")"
    | none => plain e
  -- A BIFUNCTOR'S action takes the same bracket and BOTH its arrows: `F(𝟙,f)`, `F(f,T(f))`.  An
  -- unexpander cannot write it — `F(𝟙,f)` is no term — and the one beside the constant prints the
  -- second argument alone, so `F.map (𝟙 A) f` and `F.map g f` come out the same picture.
  | (``Freyd.Alg.BiRelator.map, args) => do
    match lastTwo (← arrows args) with
    | some (x, y) => do
      let fns ← args.filterM fun a => return (← Meta.inferType a).isAppOf ``Freyd.Alg.BiRelator
      match fns.back? with
      | some fn => return (← labelAt 4 fn) ++ "(" ++ (← labelAt 0 x) ++ "," ++ (← labelAt 0 y) ++ ")"
      | none => plain e
    | none => plain e
  | (c, args) =>
    -- A HEAD THE LABEL HAS NO SPELLING OF is rewritten along the note's own equations first, and
    -- ONLY here: `arm₂` of an algebra is the arm the note names, while every head with a clause
    -- above is already written as the note writes it — `Λ R` is the `𝟙%∋ E(R)` its clause writes,
    -- not the composite the PICTURE splits it into, and rewriting it here loops through
    -- `singletonMap` and back.
    if let some r ← rewriteHead? e then return ← labelAt prec r
    if tightHeads.contains c then return (← plain e).replace " " "" else do
    -- A FUNCTOR'S ACTION ON OBJECTS joins by the note's own rule (CLAUDE.md): a ONE-LETTER functor
    -- closes up against a name (`FA`, `EFA`) or an operand the printer already bracketed (`E[A]`),
    -- and every other application takes parentheses (`tree(A)`, `E(bag(Job))`, `F([A]×[A])`).  Head
    -- and operands are spelled APART, each by its own rule: an operand is an object of the note's,
    -- respelled here, and the head keeps the name its lane wears.  SEVERAL operands are the note's
    -- comma list inside that bracket (`F(A,C)`), which is `BiRelator.map`'s `F(𝟙,f)` on objects.
    -- AFTER the spellings above: a head the note writes ITSELF (`E A`, an unexpander's own
    -- notation) is that spelling, and the action rule answers where the printer wrote none.
    if let some (f, xs) ← functorObj? e then
      let parts ← xs.mapM (labelAt 0)
      let j ← if xs.size == 1 then objJoin xs[0]! else pure Join.other
      return applyLabel (← functorName f) (",".intercalate parts.toList) j
    -- A COMPONENT OF A FAMILY the statement BINDS is set tight for the same reason a relator's
    -- action on an object is: the note writes `φ`'s component at `A` as `φA`, one name, where
    -- Lean's formatter sets the object off from the head.  Its head is a free variable and has no
    -- constant for `tightHeads`, so the test is `isComponent`'s, on the TYPE.
    if ← isComponent e then
      -- ONE NAME, built from the head and its indices and not from the printer's string: squeezing
      -- the spaces out of `χ (GA)` leaves the parentheses the formatter put round the index, where
      -- the note writes `χGA`.  Each index is an object of the note's, spelled by its own rule.
      return (← plain e.getAppFn) ++ String.join (← e.getAppArgs.mapM (labelAt 0)).toList
    else do
    -- A PRODUCT OF ARROWS is its two arrows and nothing else.  The head's own printer writes the
    -- OBJECT it is taken at too (`wrap × 𝟙 [[X]]`), and an object inside a bead's label is the wire
    -- under it spelled twice; read as a product map off the TYPE, so every spelling goes one way.
    if let some (x, _) := homObjs? (← Meta.inferType e) then
      if let some (φ, ψ) ← asProdMap? (← Meta.inferType x) e then
        return wrap 1 ((← labelAt 2 φ) ++ "×" ++ (← labelAt 2 ψ))
    -- A SUM OF ARROWS the same way, and for the same reason: the two coproducts `sumMap` runs
    -- between are the objects the picture already draws at the edge's ends.
    if let some (φ, ψ) ← asSumMap? e then
      return wrap 1 ((← labelAt 2 φ) ++ "+" ++ (← labelAt 2 ψ))
    -- EVERY OTHER HEAD KEEPS THE PRINTER'S SPELLING — a delimited notation (`thin(Q)`) is the
    -- constant's own business, and a clause here would be a second copy of it — but its ARROW
    -- arguments are terms of the note's like any other, so each is respelled HERE and handed back to
    -- the printer as a local of that name.  That is what turns the operand of a head with no clause
    -- from Lean's `≫` into juxtaposition, under whatever brackets the head already writes.
    let hom ← arrows args
    -- and then APPLYING TAKES PARENTHESES (`appShow`), because juxtaposition is composition.  Those
    -- brackets are what separates an operand from the head, so where they are coming the operand is
    -- respelled at the TOP of its own precedence: `thin(prefix°×(⊤+⊤))`, not a second pair inside.
    -- SOMETHING ALREADY DELIMITS IT in two ways, and both count: the brackets `appShow` is about to
    -- write, and a head whose OWN NOTATION delimits its operand — which is exactly a syntax with no
    -- identifier head, `stxHead`'s test, since a notation opens with an atom.
    let stx ← PrettyPrinter.delab e
    let paren := (appParts stx).isSome || (stxHead stx).isNone
    let rec go : List Expr → Expr → MetaM String
      | [], t => appShow t
      | a :: rest, t => do
        let nm := Name.mkSimple (← labelAt (if paren then 0 else 4) a)
        Meta.withLocalDeclD nm (← Meta.inferType a) fun x =>
          go rest (t.replace fun s => if s == a then some x else none)
    go hom.toList e

/-- THE FACTORS A LABEL WRITES, in diagram order, FLAT.  Composition's own factors, and the
    transpose opened into the two arrows the picture draws: `Λ R = 𝟙%∋ E(R)`
    (`Λ_eq_singleton_existsImage`), ONE fraction the statement writes and TWO arrows the note sets
    beside each other — the unit, then `E` outside `R`.  Fixed at `Λ 𝟙`, which IS the unit.

    FLAT is the whole point of the array: the split makes one factor of a run into two, and
    juxtaposition is associative, so a bracket round them would say a grouping the note does not. -/
partial def labelRun (e : Expr) : MetaM (Array String) := do
  let e' ← openNotedAll e
  if e' != e then return ← labelRun e'
  match e.getAppFnArgs with
  | (``Cat.comp, args) =>
    if (lastTwo args).isNone then return #[← labelAt 2 e]
    let mut out := #[]
    for f in factors e do out := out ++ (← labelRun f)
    return out
  | (``Freyd.Alg.Λ, args) =>
    match (← homArgs args).back? with
    | some r =>
      if r.isAppOf ``Cat.id then return #[(← labelAt 3 r) ++ "%∋"]
      return #["𝟙%∋", "E(" ++ (← labelAt 0 r) ++ ")"]
    | none => return #[← plain e]
  | _ => return #[← labelAt 2 e]

end

/-- A label at the top of its own picture or box: no outer parentheses. -/
def label (e : Expr) : MetaM String := labelAt 0 e

/-- A label in the PARTS the picture sets it in.  A SYMMETRIC DIVISION is the note's fraction, and a
    bar DELIMITS its numerator, so that part is spelled at the loosest precedence — `frac(F(∋)f, ∋)`,
    where the inline spelling has to write `(F(∋)f)%∋`.  Every other arrow is one part.  Dispatched
    on the HEAD CONSTANT, the same way the inline spelling above is, so no reader has to find the
    operator again by looking for a `%` in a string. -/
partial def labelParts (e : Expr) : MetaM (Array String) := do
  let e' ← openNoted e
  if e' != e then return ← labelParts e'
  match e.getAppFnArgs with
  | (``Freyd.Alg.Λ, args) => do
    let arrows ← args.filterM fun a => return (homObjs? (← Meta.inferType a)).isSome
    match arrows.back? with
    | some r => return #[← labelAt 0 r, "∋"]
    | none => return #[← label e]
  | _ => return #[← label e]

end Freyd.StrDiag
