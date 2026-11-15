import LeetQ.Run.Lang.Parse
import LeetQ.Run.Lang.Expand
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

/-- A name Lean reads as a token: a one-character name (`⊤ ≤ ∧ ⇝`), a builtin of `Op.table`, or a Lean keyword
    (`kwName`). -/
def relSymFn : ParserFn := fun c s =>
  let (n, i) := (s.stackSize, s.pos)
  let s := tokenFn [] c s
  if s.hasError then s else match s.stxStack.back with
    | .atom _ v => if (v.length == 1 && Parse.isSym v.front) || (Parse.builtin v).isSome || kwName c.env v then s
                   else (s.restore n i).mkErrorAt "a name" i
    | _ => (s.restore n i).mkErrorAt "a name" i

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
syntax (name := rFold) "⦇" rel "," rel "⦈" : rel
-- the book's fold of one algebra: `Calc` reads it, a program has no initial algebra to fold over
syntax (name := rFold1) "⦇" rel "⦈" : rel
syntax (name := rLit) "{" relLit,+ "}" : rel
syntax:max (name := rCompl) "∼" rel:max : rel
syntax:max (name := rConv) rel:max "°" : rel
-- `R*`, at the level of `°`, so `R°*`, `R*°` need no parentheses; `*` is no name (`Parse.reserved`)
syntax:max (name := rStar) rel:max "*" : rel
syntax:60 (name := rComp) rel:60 sameLine rel:61 : rel
syntax:60 (name := rBin) rel:60 ("∩" <|> "∪" <|> "−" <|> "/" <|> "\\" <|> "×") rel:61 : rel
-- `μX : φ`, `νX : φ`, one identifier then the body to the end: below every operator, so an operand only in
-- parentheses
syntax:0 (name := rFix) ident ":" rel : rel

syntax (name := pDecl) relWord (relType)? : relParam
syntax (name := iDecl) relWord "≜" rel : relItem

syntax (name := sElems) &"obj" relWord "=" "{" relWord,+ "}" : relStmt
syntax (name := sRange) &"obj" relWord "=" relWord "…" relWord : relStmt
syntax (name := sAlias) &"obj" relWord "=" relObj : relStmt
syntax (name := sPrint) &"print" rel : relStmt
syntax (name := sCheck) &"check" rel ("⊑" <|> "=") rel : relStmt
syntax (name := sDefn) relWord ("(" relParam,+ ")")? (relType)? "≜" rel ("⊑" rel)? ("where" relItem,+)? : relStmt
syntax (name := sInfix) "_" relWord "_" "(" relParam,+ ")" (relType)? "≜" rel ("⊑" rel)? ("where" relItem,+)? :
  relStmt
-- Lean's `theorem … := calc` (§3, §8): `theorem` and `calc` stay names (`kwName`), so a Lean `theorem` command
-- after a program still ends it (`kwBack`); each step on its own line, indented past the statement, read from its
-- own position so that juxtaposition reaches along its line (`sameLine`)
syntax (name := cStep) "_" ("⊑" <|> "=") rel " := " ("≜")? relWord : relStep
syntax (name := sTheorem) &"theorem " relWord ("(" relParam,+ ")")? (&" on " rel:max)? ":" rel ("⊑" <|> "=") rel
  (" := " &"calc" (colGt withPosition(relStep))+)? : relStmt

/-- A program's statements, each at its own position, read with the program's tokens (`relTokens`). -/
@[run_parser_attribute_hooks] def relStmts : Parser := relTokens (many (withPosition (kwBack (categoryParser `relStmt 0))))

-- one block, so the program's lines stay as they are (no per-line keyword) and its scope runs through them
syntax (name := relProgram) (docComment)? "rel_program " ident " where" relStmts : command
/-- A variant of a program: its definitions, the `where` ones in place of those of their names, its checks and
    theorems dropped (they state the base's own values), and only the declarations up to the definition `upto` names. -/
syntax (name := relVariant) (docComment)? "rel_program " ident &" from " ident (&" upto " relWord)? " where" relStmts :
  command

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
  | ``wNeg => onText s ("-" ++ tokText s[1]) Parse.word
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
  | ``rFold => pure [.fold p (← expr s[1]) (← expr s[3])]
  | ``rFold1 => failAt s "one-argument fold is for rel(…) proofs: a program folds a list with `⦇e,S⦈`"
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

/-- The parameters `ps` of the definition or theorem `w`, each a name no builtin takes, each once. -/
def params (s : Syntax) (w : String) (ps : Array Syntax) : C (List Param) := do
  let ps ← ps.toList.mapM fun q => do
    let n ← wordOf q[0]
    if (Parse.builtin n).isSome then failAt q s!"`{n}` is a builtin; choose another name"
    pure (⟨n, ← q[1].getOptional?.mapM typeOf⟩ : Param)
  let _ ← ps.foldlM (fun (seen : List String) q => do
    if seen.contains q.name then failAt s s!"`{q.name}` is already a parameter of `{w}`"
    pure (q.name :: seen)) []
  pure ps

/-- A definition: `w` its name, `key` it or its infix key `_w_`. -/
def defn (s : Syntax) (w key : String) (ps : Array Syntax) (ty body test wh : Syntax) : C Decl := do
  let p ← posOf s
  Parse.fresh p w (← get).taken
  let ps ← params s w ps
  if key != w && ps.length != 2 then
    failAt s s!"the infix operator `{w}` takes two parameters, `{key}(R, S)`, found {ps.length}"
  let ty ← ty.getOptional?.mapM typeOf
  let outer := (← get).known
  modify fun st => { st with known := ps.map (fun q => (q.name, 0)) ++ st.known }
  -- the `where` items first: each in scope in the items after it and in the body (§c)
  let σ ← (if wh.getNumArgs == 0 then #[] else wh[1].getSepArgs).foldlM (init := []) fun σ i => do
    let q ← posOf i
    let n ← wordOf i[0]
    Parse.fresh q n ((key, Parse.at_ p) :: (← get).taken)
    if ps.any (·.name == n) then failAt i s!"`{n}` is already a parameter of `{w}`"
    if σ.any (·.1 == n) then failAt i s!"`{n}` is already an item of this `where`"
    let σ := σ ++ [(n, (← expr i[2]).subst σ)]
    modify fun st => { st with known := (n, 0) :: st.known }
    pure σ
  let e := (← expr body).subst σ
  let b ← if test.getNumArgs == 0 then pure (Body.rel e) else do pure (Body.test e ((← expr test[1]).subst σ))
  if let (.test .., some t) := (b, ty) then
    failAt s s!"the test `{w}` has no type of its own: drop ': {OExp.arrow t}' (§e)"
  modify fun st => { st with known := outer }
  pure (.defn p key ps b ty)

def stmt (s : Syntax) : C Decl := do
  let p ← posOf s
  let objName : C String := do
    let n ← wordOf s[1]
    if let some r := (← get).taken.lookup n then failAt s[1] s!"`{n}` is already defined {r}"
    pure n
  let objDecl (d : C ObjDef) : C Decl := do let n ← objName; pure (.obj p n (← d))
  let num (w : Syntax) : C Int := do onText w[0] (← wordOf w) Parse.num
  let opt (o : Syntax) := if o.getNumArgs == 0 then #[] else o[1].getSepArgs
  match s.getKind with
  | ``sElems => objDecl do pure (.elems (← s[4].getSepArgs.toList.mapM wordOf))
  | ``sRange => objDecl do
    let lo ← num s[3]; let hi ← num s[5]
    if hi < lo then failAt s[5] s!"the range {lo}…{hi} is empty: {hi} is below {lo}"
    pure (.range lo hi)
  | ``sAlias => objDecl do pure (.alias (← obj s[3]))
  | ``sPrint => pure (.print p (← expr s[1]))
  | ``sCheck => pure (.check p (← expr s[1]) (← expr s[3]) (atomIn s[2] == "="))
  | ``sDefn =>
    -- `_on_` is one Lean identifier: its text read as a head, `_n_` the infix `n`
    let (w, key) ← onText s[0] (tokText s[0][0] ++ (if s[0].getKind == ``wNeg then tokText s[0][1] else "")) do
      let w ← Parse.word
      if w != "_" then pure (w, w) else do
        let n ← Parse.word
        if (← Parse.peek) != some '_' then Parse.expected s!"'_' closing the infix operator `_{n}_`"
        Parse.adv; pure (n, Parse.infixKey n)
    defn s w key (opt s[1]) s[2] s[4] s[5] s[6]
  | ``sInfix => do let n ← wordOf s[1]; defn s n (Parse.infixKey n) s[4].getSepArgs s[6] s[8] s[9] s[10]
  | ``sTheorem => do
    let n ← wordOf s[1]
    Parse.fresh p n (← get).taken
    let ps ← params s n (opt s[2])
    if s[3].getNumArgs != 0 && !ps.isEmpty then
      failAt s[3] s!"`on` evaluates a theorem with no parameters; `{n}` has {ps.length}"
    let outer := (← get).known
    modify fun st => { st with known := ps.map (fun q => (q.name, 0)) ++ st.known }
    let on ← if s[3].getNumArgs == 0 then pure none else some <$> expr s[3][1]
    let e ← expr s[5]; let f ← expr s[7]; let eq := atomIn s[6] == "="
    -- a reason is the program's theorem or definition, else the registry's one the resolver gives
    let steps ← (if s[8].getNumArgs == 0 then #[] else s[8][2].getArgs).toList.mapM fun t => do
      unless t.getKind == ``cStep do failAt t "expected a step `_ = e := n`"
      let q ← posOf t; let x ← expr t[2]; let r ← posOf t[5]; let m ← wordOf t[5]
      let st ← get
      -- a name not the program's is the registry's, through the resolver (§2.3)
      let own := st.known.any (fun k => k.1 == m || k.1 == Parse.infixKey m) || st.thms.contains m
      let ex := if own || ps.any (·.name == m) then none else st.ext m
      if let some e := ex then modify fun st => { st with used := e.const :: st.used }
      let isDef := (st.known.any (fun k => k.1 == m || k.1 == Parse.infixKey m) && !ps.any (·.name == m)) ||
        ex.any (fun e => !e.obj && !e.thm)
      let isThm := st.thms.contains m || ex.any (·.thm)
      let why ← if t[4].getNumArgs == 0 then
          if isThm then pure (Why.thm r m)
          else failAt t[5] (if isDef then s!"`{m}` is a definition; write `≜ {m}`" else s!"unknown theorem '{m}'")
        else if isDef then pure (Why.unfold r m)
          else failAt t[5] (if isThm then s!"`{m}` is a theorem, not a definition"
            else s!"unknown definition '{m}'")
      if eq && atomIn t[1] != "=" then failAt t s!"`{n}` states `=`: a step `⊑` proves only `⊑`"
      pure (q, atomIn t[1] == "=", x, why)
    -- the chain starts at the left side (`_`) and must end at the right one, compared as the parser reads both
    if let some (q, _, x, _) := steps.getLast? then
      if x.render 0 true != f.render 0 true then
        throw ⟨q, s!"the chain of `{n}` ends at {x.show}, not at its right side {f.show}"⟩
    modify fun st => { st with known := outer }
    pure (.«theorem» p n ps e f eq on steps)
  | _ => failAt s "expected a declaration"

/-- The program of the statements `ss`, read in the scope `s₀`, each statement in the scope those before it leave
    (`Parse.after`); and the scope it leaves. -/
def program (fm : FileMap) (s₀ : Parse.S) (ss : Array Syntax) : Except Err (Program × Parse.S) :=
  (ss.toList.mapM (fun x => do let d ← stmt x; modify (Parse.after · [d]); pure d) |>.run fm).run s₀

unsafe def programOfUnsafe (n : Name) : CommandElabM Program := do
  match (← getEnv).evalConstCheck Program (← getOptions) ``Program n with
  | .ok p => pure p
  | .error e => throwError "cannot read the program `{n}`: {e}"

/-- The value of the program `n`, a `rel_program` elaborated before. -/
@[implemented_by programOfUnsafe] opaque programOf (n : Name) : CommandElabM Program

def defConst (n : Name) (v : Lean.Expr) : CoreM Unit :=
  addAndCompile <| .defnDecl
    { name := n, levelParams := [], type := mkConst ``Program, value := v, hints := .abbrev, safety := .safe }

/-- The constant `c : Decl` of a declaration not built to a constant of its own (not yet elaborated once). -/
def declConst (c : Name) (d : Decl) : CoreM Unit :=
  addAndCompile <| .defnDecl
    { name := c, levelParams := [], type := mkConst ``Decl, value := toExpr d, hints := .abbrev, safety := .safe }

/-- The resolver in the namespace `ns` with the `open`s `opens` (module design §2.3): Lean's `resolveGlobalName`
    gives the candidates of a written name, the registry keeps its own; and whether a written prefix is a
    namespace. -/
def resolverAt (env : Environment) (opts : Options) (reg : Expand.Registry) (ns : Name) (opens : List OpenDecl) :
    (String → Found) × (String → Bool) :=
  let id (t : String) : Name := (Parse.parts t).foldl Name.str .anonymous
  let at_ (ns : Name) (t : String) : List Name := ((ResolveName.resolveGlobalName env opts ns opens (id t)).filterMap
    fun (c, fs) => if fs.isEmpty then some c else none).eraseDups
  -- Lean's resolution from the namespace `ns` outwards, where a constant that is no Rel definition shadows nothing:
  -- the first namespace level whose resolution has Rel definitions gives them
  let levels := (ns.components.length + 1 |> List.range).map fun k => ns.components.take (ns.components.length - k)
  (fun t =>
    let es := (levels.map fun c => (at_ (c.foldl (· ++ ·) .anonymous) t).filterMap (reg.exts[·]?)).find? (!·.isEmpty)
    match es with
    | some [(e, _)] => .ext e
    | some es => .bad true s!"ambiguous name `{t}`: it is {es.map (·.1.const)}"
    | none => match at_ ns t with
      | [] => .none
      | cs => .bad false s!"`{t}` is not a Rel definition: Lean resolves it to {cs}",
   fun t => !(ResolveName.resolveNamespace env ns opens (id t)).isEmpty)

/-- The scope of a program read here: the current namespace and `open`s. -/
def scopeHere : CommandElabM Parse.S := do
  let (res, ns) := resolverAt (← getEnv) (← getOptions) (Expand.relRegistry.getState (← getEnv)) (← getCurrNamespace) (← getOpenDecls)
  pure { cs := #[], res, ns }

/-- The programs the constants `used` reach, each after the programs its own names reach, in the order they were
    defined (an import's before the importer's). -/
def homesOf (reg : Expand.Registry) (used : List Name) : List Name :=
  let hs := used.filterMap fun c => (reg.exts[c]?).map (·.2)
  let all := hs.flatMap fun h => ((reg.chains.lookup h).getD []) ++ [h]
  (reg.progs.toList.map (·.1)).filter all.contains

/-- The program `n` named by `id`, read in the scope `s` that left `used`, what it reads (`Expand.emit`): each closed
    definition as the Lean definition `n.x`, its prints, its checks; then its definitions and objects registered,
    each a constant (`n.x : Decl`, its declaration, where it is not built once), with its scope and homes; the doc
    comment `stx[0]`, when written, is `n`'s. -/
def define (stx id : Syntax) (prog : Program) (used : List Name) (more : List Name := [])
    (scope : Option (Name × List OpenDecl) := none) : CommandElabM Unit := do
  let n := (← getCurrNamespace) ++ id.getId
  let (ns, os) := scope.getD (← getCurrNamespace, ← getOpenDecls)
  liftTermElabM do
    defConst n (toExpr (α := List Decl) prog)
    addDocString' n mkNullNode (stx[0].getOptional?.map (⟨·⟩))
    Term.addTermInfo' id (mkConst n) (isBinder := true)
  let env ← getEnv
  let opts ← getOptions
  let reg := Expand.relRegistry.getState env
  -- `nil` starts at the `1` in scope (`Env.one`) though no token names it, so its home is read too
  let one := match (resolverAt env opts reg ns os).1 "1" with | .ext e => [e.const] | _ => []
  let homes := (reg.progs.toList.map (·.1)).filter ((more ++ homesOf reg (one ++ used)).contains ·)
  let progs ← homes.mapM fun m => return (m, ← programOf m)
  let resOf (h : Name) : String → Found :=
    if h == n then (resolverAt env opts reg ns os).1 else
    match reg.progs.find? (·.1 == h) with
    | some (_, ns, os) => (resolverAt env opts reg ns os).1
    | none => fun _ => .none
  match Expand.read (reg.calls.lookup ·) progs prog n resOf with
  | .error e => throwErrorAt stx "{e}"
  | .ok r =>
    liftTermElabM (Expand.emit n r)
    for d in prog do
      if let some (_, e) := Parse.extOf n d then
        unless (← getEnv).contains e.const do
          liftCoreM (declConst e.const d)
        modifyEnv (Expand.relRegistry.addEntry · (.ext e n))
    modifyEnv (Expand.relRegistry.addEntry · (.prog n ns os))
    modifyEnv (Expand.relRegistry.addEntry · (.chain n homes))

/-- `rel_program n where …`, read in the current namespace and `open`s (module design §2.3): no program is in
    scope that is not `open`ed or written qualified. -/
@[command_elab relProgram] def elabRelProgram : CommandElab := fun stx => do
  match program (← getFileMap) (← scopeHere) stx[4].getArgs with
  | .error e => throwErrorAt stx "{e}"
  | .ok (prog, s) => define stx stx[2] prog s.used

/-- `rel_program n from base upto x where …`: the replacements read in `base`'s scope and objects. -/
@[command_elab relVariant] def elabRelVariant : CommandElab := fun stx => do
  let b ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[4])
  let base ← programOf b
  let reg := Expand.relRegistry.getState (← getEnv)
  let some (_, bns, bos) := reg.progs.find? (·.1 == b) | throwErrorAt stx[4] "`{b}` is no rel_program"
  let (res, ns) := resolverAt (← getEnv) (← getOptions) reg bns bos
  let s := Parse.after { cs := #[], res, ns } (base.filter fun | .obj .. => true | _ => false)
  let named : Decl → Option String := fun | .defn _ x .. => some x | _ => none
  match program (← getFileMap) s stx[7].getArgs with
  | .error e => throwErrorAt stx "{e}"
  | .ok (news, s') => do
    for d in news do
      match named d with
      | some x => unless base.any (named · == some x) do throwErrorAt stx "`{x}` is no definition of `{b}`"
      | none => throwErrorAt stx "a variant only replaces definitions"
    let kept := base.filter fun | .check .. | .«theorem» .. => false | _ => true
    let kept ← if stx[5].getNumArgs == 0 then pure kept else do
      let x ← match (wordOf stx[5][1]).run (← getFileMap) |>.run' s with
        | .ok x => pure x
        | .error e => throwErrorAt stx[5] "{e}"
      match kept.findIdx? (named · == some x) with
      | some k => pure (kept.take (k + 1))
      | none => throwErrorAt stx[5] "`{x}` is no definition of `{b}`"
    define stx stx[2] (kept.map fun d => ((named d).bind fun x => news.find? (named · == some x)).getD d) s'.used
      ((reg.chains.lookup b).getD []) (some (bns, bos))

end LeetQ.Rel.Lang.Embed
