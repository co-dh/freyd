import LeetQ.Run.Lang.Parse
import Lean

/-! The Rel language as a closed Lean syntax category, its one grammar: `rel_program n where` and the program's
    lines define `n : Program`; `Expand.emit` defines what it reads. The grammar has relation constructs only, and no
    production embeds Lean's `term`: `fun x => x`, `let`, `if`, a tuple or a numeral expression is an error
    (a keyword is read only as a name).
    Scope (which run of letters is which names, which name takes arguments) is `Parse`'s: a Lean identifier is read
    back by `Parse.name`/`Parse.word`/`Parse.object` in its scope. -/

namespace LeetQ.Rel.Lang.Embed

open Lean Parser Elab Command
open LeetQ.Rel.Lang
open LeetQ.Rel.Lang.Parse (P)

/-! ### The grammar -/

/-- Lean reads only declared tokens, so each one-character name of the text grammar (`Parse.isSym`) in the
    Unicode symbol blocks is declared; the ASCII ones are Lean tokens already. -/
def symToks : List Token :=
  [(0xA1, 0xFF), (0x2190, 0x2BFF), (0x1D7D8, 0x1D7E1)].flatMap fun (a, b) => (List.range (b + 1 - a)).filterMap
    fun k => let c := Char.ofNat (a + k)
      if Parse.isSym c && !isLetterLike c && !isSubScriptAlnum c then some c.toString else none

/-- The tokens of the Rel categories' own productions (`where`, `_`, `≜`, …), read from the parser tables. -/
def relGrammarTokens (env : Environment) : List Token :=
  let cats := [`relWord, `relHead, `relObj, `relType, `relLit, `rel, `relParam, `relItem, `relStep, `relStmt]
  cats.flatMap fun n => match (parserExtension.getState env).categories.find? n with
    | none => []
    | some c => let t := c.tables
      let ps := t.leadingParsers ++ t.trailingParsers ++ (t.leadingTable.toList ++ t.trailingTable.toList).flatMap (·.2)
      ps.flatMap fun (p, _) => p.info.collectTokens []

/-- A Lean keyword that is a Rel name, as `ident` never reads it: a word token (`prefix`, `at`, `fun`) that no
    production of the Rel grammar uses. -/
def kwName (env : Environment) (v : String) : Bool :=
  isIdFirst v.front && v.all isIdRest && !(relGrammarTokens env).contains v

/-- One token that `ok` accepts, else the error that `ex` was expected. Read by `tokenFn` alone, so no antiquotation
    is: `$x` is read only where a term is (the category's own), never in an operator's place, where it would make
    the term reach on to the operand after it, on the next line. -/
def tokWhereFn (ok : Environment → String → Bool) (ex : List String) : ParserFn := fun c s =>
  let (n, i) := (s.stackSize, s.pos)
  let s := tokenFn [] c s
  if s.hasError then s else match s.stxStack.back with
    | .atom _ v => if ok c.env v then s else (s.restore n i).mkErrorsAt ex i
    | _ => (s.restore n i).mkErrorsAt ex i

/-- A name Lean reads as a token: a one-character name (`⊤ ≤ ∧ ⇝`), a builtin of `Op.table`, or a Lean keyword
    (`kwName`). -/
def relSymFn : ParserFn := tokWhereFn (ex := ["a name"]) fun env v =>
  (v.length == 1 && Parse.isSym v.front) || (Parse.builtin v).isSome || kwName env v

/-- One of the tokens `ts`, an operator: the syntax DSL's `("∩" <|> "∪")` gives each string an antiquotation `$x`
    of its own (`token.«∩».antiquot`), which takes a juxtaposed `$x` for the operator (`tokWhereFn`). -/
def relOp (ts : List String) : Parser :=
  { fn := tokWhereFn (fun _ v => ts.contains v) (ts.map (s!"'{·}'")), info := { collectTokens := (ts ++ ·) } }

open PrettyPrinter in
@[combinator_formatter relOp] def relOp.formatter (_ : List String) : Formatter := Formatter.visitAtom .anonymous
open PrettyPrinter in
@[combinator_parenthesizer relOp] def relOp.parenthesizer (_ : List String) : Parenthesizer := Parenthesizer.visitToken

/-- An infix operator of `Bin.table`. -/
@[run_parser_attribute_hooks] def binOp : Parser := relOp (Bin.table.map (·.1.toString))

/-- The relation a check, a theorem or a step states. -/
@[run_parser_attribute_hooks] def cmpOp : Parser := relOp ["⊑", "="]

/-- `p`, undone when it fails on a statement that starts with a keyword name: the program ends there, since a Lean
    command after it (`example :`, `prefix:max`, `rel_program`) starts with the same token. -/
def kwBackFn (p : ParserFn) : ParserFn := fun c s =>
  let (n, i) := (s.stackSize, s.pos)
  let t := tokenFn [] c s
  let kw := !t.hasError && match t.stxStack.back with | .atom _ v => kwName c.env v | _ => false
  if kw then atomicFn p c (t.restore n i) else p c (t.restore n i)

def kwBack (p : Parser) : Parser := { p with fn := kwBackFn p.fn }

/-- The operator token of `s`, a node of one atom or the atom itself. -/
partial def atomIn (s : Syntax) : String := match s with
  | .atom _ v => v
  | _ => if s.getNumArgs == 1 then atomIn s[0] else ""

def relSym : Parser := { fn := relSymFn, info := { collectTokens := (symToks ++ ·) } }

/-- `p` read with the tokens the program's text has whatever namespaces are open: a token of more than one
    character that starts with a character of a name (`Parse.isSym`, letter-like) is dropped, so an opened
    notation's `Λ(`, `∋(` or `P(` does not swallow the name `Λ` and its parenthesis. The grammar's own tokens are
    one character each; a word (`end`, `def`) or one starting in ASCII other than a letter is a Lean keyword: a word
    is a Rel name (`kwName`), and a statement it starts that does not parse ends the program (`kwBack`). -/
def relTokenTable (tt : TokenTable) : TokenTable :=
  let keep (t : Token) := t.length == 1 || t.all isIdRest || (t.front.toNat < 128 && !t.front.isAlpha) ||
    !(Parse.isIdCont t.front || Parse.isSym t.front || isLetterLike t.front)
  tt.values.foldl (fun r t => if keep t then r.insert t t else r) {}

def relTokensFn (p : ParserFn) : ParserFn := adaptUncacheableContextFn (fun c => { c with tokens := relTokenTable c.tokens }) p

def relTokens (p : Parser) : Parser := { p with fn := relTokensFn p.fn }

/-- A declaration ends at its line (§c): juxtaposition never reaches the next line's name. -/
def sameLine : Parser := checkLineEq "the declaration's line"

open PrettyPrinter in
@[combinator_formatter relSym] def relSym.formatter : Formatter := Formatter.visitAtom .anonymous
open PrettyPrinter in
@[combinator_parenthesizer relSym] def relSym.parenthesizer : Parenthesizer := Parenthesizer.visitToken
open PrettyPrinter in
@[combinator_formatter sameLine] def sameLine.formatter : Formatter := pure ()
open PrettyPrinter in
@[combinator_parenthesizer sameLine] def sameLine.parenthesizer : Parenthesizer := pure ()
open PrettyPrinter in
@[combinator_formatter relTokens] def relTokens.formatter (p : Formatter) : Formatter := p
open PrettyPrinter in
@[combinator_parenthesizer relTokens] def relTokens.parenthesizer (p : Parenthesizer) : Parenthesizer := p
open PrettyPrinter in
@[combinator_formatter kwBack] def kwBack.formatter (p : Formatter) : Formatter := p
open PrettyPrinter in
@[combinator_parenthesizer kwBack] def kwBack.parenthesizer (p : Parenthesizer) : Parenthesizer := p

declare_syntax_cat relWord
declare_syntax_cat relHead
declare_syntax_cat relObj
declare_syntax_cat relType
declare_syntax_cat relLit
declare_syntax_cat rel
declare_syntax_cat relParam
declare_syntax_cat relItem
declare_syntax_cat relStep
declare_syntax_cat relStmt (behavior := both)

-- a word: a name, an element, a number
syntax (name := wId) ident : relWord
syntax (name := wNum) num : relWord
syntax (name := wSym) relSym : relWord
syntax (name := wNeg) "-" noWs num : relWord

syntax (name := hId) ident : relHead
syntax (name := hSym) relSym : relHead

syntax:max (name := oWord) relWord : relObj
syntax (name := oPow) "𝒫" relObj:max : relObj
syntax (name := oList) "[" relObj "]" : relObj
syntax (name := oParen) "(" relObj ")" : relObj
syntax:60 (name := oProd) relObj:60 "×" relObj:61 : relObj
syntax:60 (name := oSum) relObj:60 "+" relObj:61 : relObj

syntax (name := tyArrow) ":" relObj "⟶" relObj : relType

syntax (name := lWord) relWord : relLit
syntax (name := lRow) "(" relLit+ "," relLit+ ")" : relLit
syntax (name := lArr) "[" relLit* "]" : relLit

-- one level, left to right (§c): every infix form takes the level on its left and a primary on its right
syntax:max (name := rId) ident : rel
syntax:max (name := rSym) relSym : rel
-- `csp.≼`: Lean reads a qualified symbol name as three tokens (module design §2.3)
syntax:max (name := rQSym) ident noWs "." noWs relSym : rel
syntax:max (name := rApp) relHead noWs "(" rel,+ ")" : rel
syntax:max (name := rObjs) relHead noWs "(" relObj,+ ")" : rel
syntax:max (name := rAppPair) relHead noWs "⟨" rel "," rel "⟩" : rel
syntax (name := rParen) "(" rel ")" : rel
syntax (name := rPair) "⟨" rel "," rel "⟩" : rel
syntax (name := rJunc) "[" rel "," rel "]" : rel
-- the book's fold `⦇R⦈`, `R : 1 + E×V ⟶ V`: on arrays a program reads it from `inl R`, `inr R` (`elabE`)
syntax (name := rFold1) "⦇" rel "⦈" : rel
syntax (name := rLit) "{" relLit,+ "}" : rel
syntax:max (name := rCompl) "∼" rel:max : rel
syntax:max (name := rConv) rel:max "°" : rel
-- `R*`, at the level of `°`, so `R°*`, `R*°` need no parentheses; `*` is no name (`Parse.reserved`)
syntax:max (name := rStar) rel:max "*" : rel
syntax:60 (name := rComp) rel:60 sameLine rel:61 : rel
syntax:60 (name := rBin) rel:60 binOp rel:61 : rel
-- `μX : φ`, `νX : φ`, one identifier then the body to the end: below every operator, so an operand only in
-- parentheses
syntax:0 (name := rFix) ident ":" rel : rel

syntax (name := pDecl) relWord (relType)? : relParam
syntax (name := iDecl) relWord "≜" rel : relItem

syntax (name := sElems) &"obj" relWord "=" "{" relWord,+ "}" : relStmt
syntax (name := sRange) &"obj" relWord "=" relWord "…" relWord : relStmt
syntax (name := sAlias) &"obj" relWord "=" relObj : relStmt
syntax (name := sPrint) &"print" rel : relStmt
syntax (name := sCheck) &"check" rel cmpOp rel : relStmt
syntax (name := sDefn) relWord ("(" relParam,+ ")")? (relType)? "≜" rel ("⊑" rel)? ("where" relItem,+)? : relStmt
syntax (name := sInfix) "_" relWord "_" "(" relParam,+ ")" (relType)? "≜" rel ("⊑" rel)? ("where" relItem,+)? :
  relStmt
-- Lean's `theorem … := calc` (§3, §8): `theorem` and `calc` stay names (`kwName`), so a Lean `theorem` command
-- after a program still ends it (`kwBack`); each step on its own line, indented past the statement, read from its
-- own position so that juxtaposition reaches along its line (`sameLine`)
-- a step cites a theorem at its arguments, `:= estMap(zero, ≥)`, as a definition is applied (`rApp`)
syntax (name := cStep) "_" cmpOp rel " := " ("≜")? relWord (noWs "(" rel,+ ")")? : relStep
-- a hypothesis: `e = f`, `e ⊑ f`, or a test applied; above level 0, so `R : …` after it is no fixed point `μX : φ`
syntax relHyp := rel:1 (cmpOp rel:1)?
syntax (name := sTheorem) &"theorem " relWord ("(" relParam,+ ")")? (&" on " rel:max)? (&" if " relHyp,+)? ":"
  rel cmpOp rel (" := " &"calc" (colGt withPosition(relStep))+)? : relStmt

/-- A program's statements, each at its own position, read with the program's tokens (`relTokens`). -/
@[run_parser_attribute_hooks] def relStmts : Parser := relTokens (many (withPosition (kwBack (categoryParser `relStmt 0))))

-- one block, so the program's lines stay as they are (no per-line keyword) and its scope runs through them
syntax (name := relProgram) (docComment)? "rel_program " ident " where" relStmts : command
/-- A variant of a program: its definitions, the `where` ones in place of those of their names, its checks and
    theorems dropped (they state the base's own values), and only the declarations up to the definition `upto` names. -/
syntax (name := relVariant) (docComment)? "rel_program " ident &" from " ident (&" upto " relWord)? " where" relStmts :
  command

deriving instance ToExpr for OExp
deriving instance ToExpr for Op
deriving instance ToExpr for Bin
deriving instance ToExpr for Tup
deriving instance ToExpr for Lang.Expr
deriving instance ToExpr for Body
deriving instance ToExpr for Param
deriving instance ToExpr for ObjDef
deriving instance ToExpr for Why
deriving instance ToExpr for Decl

/-! ### From syntax to the AST, in the state of `Parse` -/

abbrev C := ReaderT FileMap P

def posOf (s : Syntax) : C Lang.Pos := do
  let p := (← read).toPosition (s.getPos?.getD 0); pure ⟨p.line, p.column + 1⟩

def failAt {α : Type} (s : Syntax) (m : String) : C α := do throw ⟨← posOf s, m⟩

/-- `p` run on `t`, the text of the token `s`, in the current scope, to its end. -/
def onText {α : Type} (s : Syntax) (t : String) (p : P α) : C α := do
  let q ← posOf s
  let whole : P α := do let a ← p; if (← Parse.peek).isSome then Parse.expected "the end of the token" else pure a
  match whole.run { (← get) with cs := t.toList.toArray, i := 0, line := q.line, col := q.col } with
  -- a token's reads leave only the constants they resolved (`used`); the rest is the token's own
  | .ok (a, t) => do modify ({ · with used := t.used }); pure a
  | .error e => throw e

/-- The source text of a token: an identifier as Lean reads it, a number, a symbol. A name that is a Lean keyword
    is written bare, `prefix`, and comes as its atom (`kwName`). -/
def tokText (s : Syntax) : String := match s with
  | .ident _ _ n _ => n.toString (escape := false)
  | .atom _ v => v
  | _ => if s.isOfKind numLitKind then s[0].getAtomVal else ""

def wordOf (s : Syntax) : C String := match s.getKind with
  | ``wNeg => do pure ("-" ++ (← onText s[1] (tokText s[1]) Parse.word))
  | _ => onText s (tokText s[0]) Parse.word

/-- The names a run of letters is, each where it starts: `Parse.name` to the end of the token. -/
partial def namesOf (s : Syntax) (t : String := tokText s) : C (List (Lang.Pos × String)) :=
  onText s t go
where go : P (List (Lang.Pos × String)) := do
  if (← Parse.peek).isNone then return []
  let p ← Parse.pos; let n ← Parse.name
  if n == "" then Parse.expected "a term"
  pure ((p, n) :: (← go))

partial def obj (s : Syntax) : C OExp := match s.getKind with
  | ``oWord => match s[0].getKind with
    | ``wNeg => failAt s "expected an object"
    | _ => onText s (tokText s[0][0]) Parse.object
  | ``oPow => do pure (.pow (← obj s[1]))
  | ``oList => do pure (.list (← obj s[1]))
  | ``oParen => obj s[1]
  | ``oProd => do pure (.prod (← obj s[0]) (← obj s[2]))
  | ``oSum => do pure (.sum (← obj s[0]) (← obj s[2]))
  | _ => failAt s "expected an object"

/-- `: A ⟶ B`, its objects possibly object variables (§e). -/
def typeOf (s : Syntax) : C (OExp × OExp) := do
  modify fun st => { st with vars := true }
  let t := (← obj s[1], ← obj s[3])
  modify fun st => { st with vars := false }; pure t

partial def litItem (s : Syntax) : C Tup := match s.getKind with
  | ``lWord => do pure (.leaf (← wordOf s[0]))
  | ``lRow => do pure (.pair (← tup s[1].getArgs) (← tup s[3].getArgs))
  | _ => do pure (.arr (← s[1].getArgs.toList.mapM litItem))
where tup (xs : Array Syntax) : C Tup := do
  match ← xs.toList.mapM litItem with | [t] => pure t | ts => pure (.arr ts)

/-- A side's item list, each item a primary and, unless juxtaposed, the builtin infix operator before it. -/
abbrev Items := List (Option (Lang.Pos × Bin) × Lang.Expr)

mutual

/-- A term: its items folded left to right, a declared infix name taking the primary after it (§c). -/
partial def expr (s : Syntax) : C Lang.Expr := do
  match ← items s with
  | (none, e) :: xs => do infixFree e; go e xs
  | _ => failAt s "expected a term"
where
  infixFree (e : Lang.Expr) : C Unit := do
    if let .name p n := e then if ← Parse.isInfix n then
      throw ⟨p, s!"`{n}` is an infix operator: it stands between two terms, `R {n} S`"⟩
  go (e : Lang.Expr) : Items → C Lang.Expr
  | [] => pure e
  | (some (p, o), b) :: xs => do infixFree b; go (.bin p o e b) xs
  | (none, b@(.name p n)) :: xs => do
    if !(← Parse.isInfix n) then go (.comp e b) xs else match xs with
      | (none, c) :: ys => do infixFree c; go (.inf p n e c) ys
      | _ => throw ⟨p, s!"`{n}` is an infix operator: it stands between two terms, `R {n} S`"⟩
  | (none, b) :: xs => go (.comp e b) xs

partial def items (s : Syntax) : C Items := do
  match s.getKind with
  | ``rComp => pure ((← items s[0]) ++ (← prim s.getArgs.back!).map (none, ·))
  | ``rBin =>
    let some o := Bin.table.lookup (atomIn s[1]).front | failAt s[1] "expected an operator"
    match ← prim s[2] with
    | b :: bs => pure ((← items s[0]) ++ (some (← posOf s[1], o), b) :: bs.map (none, ·))
    | [] => failAt s[2] "expected a term"
  | _ => do pure ((← prim s).map (none, ·))

/-- A primary: the terms a run of letters is, `∼` on the first and `°` on the last of them (§c). -/
partial def prim (s : Syntax) : C (List Lang.Expr) := do
  let p ← posOf s
  match s.getKind with
  | ``rId | ``rSym => do (← namesOf s[0]).flatMapM fun (p, n) => atomOf s p n none none none
  | ``rQSym => do (← namesOf s s!"{tokText s[0]}.{tokText s[2]}").flatMapM fun (p, n) => atomOf s p n none none none
  | ``rParen => pure [← expr s[1]]
  -- a fixed point: `X` in scope in the body only
  | ``rFix => do
    let (c, x) := match (tokText s[0]).toList with | c :: cs => (c, String.ofList cs) | [] => (' ', "")
    unless Parse.isFix c do failAt s "expected a term"
    Parse.fresh ⟨p.line, p.col + 1⟩ x (← get).taken
    let k := (← get).known
    modify fun st => { st with known := (x, 0) :: k }
    let b ← expr s[2]
    modify fun st => { st with known := k }
    pure [.fix p (c == 'μ') x b]
  | ``rPair => pure [.pair p (← expr s[1]) (← expr s[3])]
  | ``rJunc => pure [.junc p (← expr s[1]) (← expr s[3])]
  | ``rFold1 => pure [.fold p (← expr s[1])]
  | ``rLit => pure [.lit p (← s[1].getSepArgs.toList.mapM fun r => do match ← litItem r with
      | .pair a b => pure (a, b)
      | _ => failAt r "expected '('")]
  | ``rCompl => match ← prim s[1] with
    | e :: es => pure (.compl p e :: es)
    | [] => failAt s "expected a term"
  | ``rConv => match (← prim s[0]).reverse with
    | e :: es => pure ((.conv (← posOf s[1]) e :: es).reverse)
    | [] => failAt s "expected a term"
  -- `e*` on the last of the terms, as `°`: the closure `μX : 𝟙 ∪ e X`, no op of its own, so typed, checked and run
  -- as every `μ`; `X` primed past every name of `e` and of the scope, so it captures none
  | ``rStar => match (← prim s[0]).reverse with
    | e :: es => do
      let st ← get
      let used := e.names ++ st.known.map (·.1) ++ st.taken.map (·.1) ++ st.objs
      let xs := (List.range (used.length + 1)).map fun k => "X" ++ String.ofList (List.replicate k '\'')
      match xs.find? fun x => !used.contains x && (Parse.builtin x).isNone with
      | some x =>
        let q ← posOf s[1]
        pure ((.fix q true x (.bin q .join (.op q .id [] []) (.comp e (.name q x))) :: es).reverse)
      | none => failAt s "no variable for the μ of `*` is free of the names in scope"
    | [] => failAt s "expected a term"
  | k =>
    -- Lean gives every category `$x`, at any quotation depth: outside a quotation it is no term of the language
    if s.isAntiquot then failAt s "`$` is no term of the Rel language: an antiquotation has no place in a program"
    -- a head with its arguments; `⊤(X,X)` reads as terms and as objects, a `choice` of both
    let alts := if k == choiceKind then s.getArgs else #[s]
    let find (k : SyntaxNodeKind) := alts.find? (·.getKind == k)
    let some a := alts[0]? | failAt s "expected a term"
    unless [``rApp, ``rObjs, ``rAppPair].contains a.getKind do failAt s "expected a term"
    match (← namesOf a[0][0]).reverse with
    | (q, n) :: ns => do
      let init ← ns.reverse.flatMapM fun (p, m) => atomOf s p m none none none
      pure (init ++ (← atomOf s q n (find ``rApp) (find ``rObjs) (find ``rAppPair)))
    | [] => failAt s "expected a term"

/-- The name `n` at `p`: `app` its parenthesised terms, `objs` the same parentheses
    read as objects, `pair` a pair right after it; each `none` when not written so. -/
partial def atomOf (s : Syntax) (p : Lang.Pos) (n : String) (app objs pair : Option Syntax) : C (List Lang.Expr) := do
  -- what follows a name taking no arguments: a parenthesis or a pair is a term composed after it
  let after : C (List Lang.Expr) := match app, pair with
    | some a, _ => match a[2].getSepArgs with
      | #[e] => do pure [← expr e]
      | _ => failAt a "expected ')'"
    | _, some q => do pure [.pair (← posOf q[1]) (← expr q[2]) (← expr q[4])]
    | none, none => if objs.isSome then failAt s "expected a term" else pure []
  let args (a : Syntax) : C (List Lang.Expr) := a[2].getSepArgs.toList.mapM expr
  -- the program's names, then the kernel table, then the resolver's (§2.3)
  let st ← get
  let ar := (st.known.lookup n).orElse fun _ =>
    if (Parse.builtin n).isSome then none else (st.ext n).bind fun e => if e.isInfix || e.obj || e.thm then none else some e.arity
  match ar, Parse.builtin n with
  | some 0, _ => do pure (.name p n :: (← after))
  | some _, _ => match app with
    | some a => do pure [.app p n (← args a)]
    | none => failAt s "expected '('"
  | none, some (.index _, _) => match objs.map (·[2].getSepArgs) with
    | some #[o] => do
      -- a position is a number word read by `String.toInt?`, as every number word is, its sign included
      let w ← if o.getKind == ``oWord then wordOf o[0] else pure ""
      match w.toInt? with
      | some k => if 0 ≤ k ∧ k < 2^63 then pure [.op p (.index k.toNat) [] []]
                  else failAt o s!"at( ) takes a position from 0 that fits a long, found {w}"
      | none => failAt o s!"at( ) takes a position, a number from 0, found '{w}'"
    | _ => failAt s "at( ) takes a position, a number from 0"
  | none, some (o, 0) => match objs with
    -- the objects when they read as objects, else the parenthesis is a term
    | some os => do
      try pure [.op p o (← os[2].getSepArgs.toList.mapM obj) []]
      catch _ => pure (.op p o [] [] :: (← after))
    | none => do pure (.op p o [] [] :: (← after))
  | none, some (o, _) => match pair, app with
    | some q, _ => do pure [.op p o [] [.pair (← posOf q[1]) (← expr q[2]) (← expr q[4])]]
    | none, some a => do pure [.op p o [] (← args a)]
    | none, none => failAt s "expected '('"
  | none, none =>
    if (← get).thms.contains n || ((← get).ext n).any (·.thm) then throw ⟨p, s!"`{n}` is a theorem, not a relation"⟩
    if !(← Parse.isInfix n) then do pure (.name p n :: (← after))
    else if app.isSome || objs.isSome then failAt s s!"`{n}` is an infix operator: write `R {n} S`, not `{n}(R, S)`"
    else pure [.name p n]

end

end LeetQ.Rel.Lang.Embed
