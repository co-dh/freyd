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
syntax (name := rFold) "⦇" rel "," rel "⦈" : rel
-- the book's fold of one algebra: `Calc` reads it, a program has no initial algebra to fold over
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

end LeetQ.Rel.Lang.Embed
