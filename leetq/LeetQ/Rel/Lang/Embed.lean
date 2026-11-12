import LeetQ.Rel.Lang.Parse
import Lean

/-! The Rel language as a closed Lean syntax category: `rel_program n where` and the program's lines, unchanged,
    define `n : Program`, the AST `Parse` reads from the same text; `Eval.runProgram` runs it. The grammar has
    relation constructs only, and no production embeds Lean's `term`: `fun`, `let`, `do`, `if`, a tuple or a numeral
    expression is a parse error. Scope (which run of letters is which names, which name takes arguments) is the
    text parser's: a Lean identifier is read back by `Parse.name`/`Parse.word`/`Parse.object` in its scope. -/

namespace LeetQ.Rel.Lang.Embed

open Lean Parser Elab Command
open LeetQ.Rel.Lang
open LeetQ.Rel.Lang.Parse (P)

deriving instance ToExpr for Lang.Pos
deriving instance ToExpr for OExp
deriving instance ToExpr for Op
deriving instance ToExpr for Bin
deriving instance ToExpr for Tup
deriving instance ToExpr for Lang.Expr
deriving instance ToExpr for Body
deriving instance ToExpr for Param
deriving instance ToExpr for ObjDef
deriving instance ToExpr for Decl

/-! ### The grammar -/

/-- Lean reads only declared tokens, so each one-character name of the text grammar (`Parse.isSym`) in the
    Unicode symbol blocks is declared; the ASCII ones are Lean tokens already. -/
def symToks : List Token :=
  [(0xA1, 0xFF), (0x2190, 0x2BFF), (0x1D7D8, 0x1D7E1)].flatMap fun (a, b) => (List.range (b + 1 - a)).filterMap
    fun k => let c := Char.ofNat (a + k)
      if Parse.isSym c && !isLetterLike c && !isSubScriptAlnum c then some c.toString else none

/-- A name Lean reads as a token: a one-character name (`⊤ ≤ ∧ ⇝`), or a builtin of `Op.table` that is a Lean
    keyword (`at`). -/
def relSymFn : ParserFn := fun c s =>
  let (n, i) := (s.stackSize, s.pos)
  let s := tokenFn [] c s
  if s.hasError then s else match s.stxStack.back with
    | .atom _ v => if (v.length == 1 && Parse.isSym v.front) || (Parse.builtin v).isSome then s
                   else (s.restore n i).mkErrorAt "a name" i
    | _ => (s.restore n i).mkErrorAt "a name" i

/-- The operator token of `s`, a node of one atom or the atom itself. -/
partial def atomIn (s : Syntax) : String := match s with
  | .atom _ v => v
  | _ => if s.getNumArgs == 1 then atomIn s[0] else ""

def relSym : Parser := { fn := relSymFn, info := { collectTokens := (symToks ++ ·) } }

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

declare_syntax_cat relWord
declare_syntax_cat relHead
declare_syntax_cat relObj
declare_syntax_cat relType
declare_syntax_cat relLit
declare_syntax_cat rel
declare_syntax_cat relParam
declare_syntax_cat relItem
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
syntax:max (name := rApp) relHead noWs "(" rel,+ ")" : rel
syntax:max (name := rObjs) relHead noWs "(" relObj,+ ")" : rel
syntax:max (name := rAppPair) relHead noWs "⟨" rel "," rel "⟩" : rel
syntax (name := rParen) "(" rel ")" : rel
syntax (name := rPair) "⟨" rel "," rel "⟩" : rel
syntax (name := rJunc) "[" rel "," rel "]" : rel
syntax (name := rFold) "⦇" rel "," rel "⦈" : rel
syntax (name := rLit) "{" relLit,+ "}" : rel
syntax:max (name := rCompl) "∼" rel:max : rel
syntax:max (name := rConv) rel:max "°" : rel
syntax:60 (name := rComp) rel:60 sameLine rel:61 : rel
syntax:60 (name := rBin) rel:60 ("∩" <|> "∪" <|> "−" <|> "/" <|> "\\" <|> "×") rel:61 : rel

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

-- one block, so the program's lines stay as they are (no per-line keyword) and its scope runs through them
syntax (name := relProgram) "rel_program " ident " where" (withPosition(relStmt))* : command

/-! ### From syntax to the AST, in the text parser's state -/

abbrev C := ReaderT FileMap P

def posOf (s : Syntax) : C Lang.Pos := do
  let p := (← read).toPosition (s.getPos?.getD 0); pure ⟨p.line, p.column + 1⟩

def failAt {α : Type} (s : Syntax) (m : String) : C α := do throw ⟨← posOf s, m⟩

/-- `p` run on `t`, the text of the token `s`, in the current scope, to its end. -/
def onText {α : Type} (s : Syntax) (t : String) (p : P α) : C α := do
  let q ← posOf s
  let whole : P α := do let a ← p; if (← Parse.peek).isSome then Parse.expected "the end of the token" else pure a
  match whole.run { (← get) with cs := t.toList.toArray, i := 0, line := q.line, col := q.col } with
  | .ok (a, _) => pure a
  | .error e => throw e

/-- The source text of a token: an identifier as written, a number, a symbol. -/
def tokText (s : Syntax) : String := match s with
  | .ident _ raw _ _ => raw.toString
  | .atom _ v => v
  | _ => if s.isOfKind numLitKind then s[0].getAtomVal else ""

def wordOf (s : Syntax) : C String := match s.getKind with
  | ``wNeg => onText s ("-" ++ tokText s[1]) Parse.word
  | _ => onText s (tokText s[0]) Parse.word

/-- The names a run of letters is, each where it starts: `Parse.name` to the end of the token. -/
partial def namesOf (s : Syntax) : C (List (Lang.Pos × String)) :=
  onText s (tokText s) go
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
  | ``rParen => pure [← expr s[1]]
  | ``rPair => pure [.pair p (← expr s[1]) (← expr s[3])]
  | ``rJunc => pure [.junc p (← expr s[1]) (← expr s[3])]
  | ``rFold => pure [.fold p (← expr s[1]) (← expr s[3])]
  | ``rLit => pure [.lit p (← s[1].getSepArgs.toList.mapM fun r => do match ← litItem r with
      | .pair a b => pure (a, b)
      | _ => failAt r "expected '('")]
  | ``rCompl => match ← prim s[1] with
    | e :: es => pure (.compl p e :: es)
    | [] => failAt s "expected a term"
  | ``rConv => match (← prim s[0]).reverse with
    | e :: es => pure ((.conv (← posOf s[1]) e :: es).reverse)
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

/-- The name `n` at `p`, as `Parse.atom` reads it: `app` its parenthesised terms, `objs` the same parentheses
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
  match (← get).known.lookup n, Parse.builtin n with
  | some 0, _ => do pure (.name p n :: (← after))
  | some _, _ => match app with
    | some a => do pure [.app p n (← args a)]
    | none => failAt s "expected '('"
  | none, some (.index _, _) => match objs.map (·[2].getSepArgs) with
    | some #[o] => do
      let w := if o.getKind == ``oWord then tokText o[0][0] else ""
      match w.toInt? with
      | some k => if k < 2^63 then pure [.op p (.index k.toNat) [] []]
                  else failAt o s!"at( ) takes a position from 0 that fits a long, found {w}"
      | none => failAt o s!"at( ) takes a position, a number from 0, found '{w}'"
    | _ => failAt s "at( ) takes a position, a number from 0"
  | none, some (o, 0) => match objs with
    -- `Parse.constObjs`: the objects when they read as objects, else the parenthesis is a term
    | some os => do
      try pure [.op p o (← os[2].getSepArgs.toList.mapM obj) []]
      catch _ => pure (.op p o [] [] :: (← after))
    | none => do pure (.op p o [] [] :: (← after))
  | none, some (o, _) => match pair, app with
    | some q, _ => do pure [.op p o [] [.pair (← posOf q[1]) (← expr q[2]) (← expr q[4])]]
    | none, some a => do pure [.op p o [] (← args a)]
    | none, none => failAt s "expected '('"
  | none, none =>
    if !(← Parse.isInfix n) then do pure (.name p n :: (← after))
    else if app.isSome || objs.isSome then failAt s s!"`{n}` is an infix operator: write `R {n} S`, not `{n}(R, S)`"
    else pure [.name p n]

end

/-- A definition, as `Parse.decl` reads one: `w` its name, `key` it or its infix key `_w_`. -/
def defn (s : Syntax) (w key : String) (ps : Array Syntax) (ty body test wh : Syntax) : C Decl := do
  let p ← posOf s
  Parse.fresh p w (← get).taken
  let ps ← ps.toList.mapM fun q => do
    let n ← wordOf q[0]
    if (Parse.builtin n).isSome then failAt q s!"`{n}` is a builtin; choose another name"
    pure (⟨n, ← q[1].getOptional?.mapM typeOf⟩ : Param)
  if key != w && ps.length != 2 then
    failAt s s!"the infix operator `{w}` takes two parameters, `{key}(R, S)`, found {ps.length}"
  let _ ← ps.foldlM (fun (seen : List String) q => do
    if seen.contains q.name then failAt s s!"`{q.name}` is already a parameter of `{w}`"
    pure (q.name :: seen)) []
  modify fun st => { st with taken := (key, Parse.at_ p) :: st.taken }
  let ty ← ty.getOptional?.mapM typeOf
  let outer := (← get).known
  modify fun st => { st with known := ps.map (fun q => (q.name, 0)) ++ st.known }
  -- the `where` items first: each in scope in the items after it and in the body (§c)
  let σ ← (if wh.getNumArgs == 0 then #[] else wh[1].getSepArgs).foldlM (init := []) fun σ i => do
    let q ← posOf i
    let n ← wordOf i[0]
    Parse.fresh q n (← get).taken
    if ps.any (·.name == n) then failAt i s!"`{n}` is already a parameter of `{w}`"
    if σ.any (·.1 == n) then failAt i s!"`{n}` is already an item of this `where`"
    let σ := σ ++ [(n, (← expr i[2]).subst σ)]
    modify fun st => { st with known := (n, 0) :: st.known }
    pure σ
  let e := (← expr body).subst σ
  let b ← if test.getNumArgs == 0 then pure (Body.rel e) else do pure (Body.test e ((← expr test[1]).subst σ))
  if let (.test .., some t) := (b, ty) then
    failAt s s!"the test `{w}` has no type of its own: drop ': {OExp.arrow t}' (§e)"
  modify fun st => { st with known := (key, ps.length) :: outer }
  pure (.defn p key ps b ty)

def stmt (s : Syntax) : C Decl := do
  let p ← posOf s
  let objName : C String := do
    let n ← wordOf s[1]
    if let some r := (← get).taken.lookup n then failAt s[1] s!"`{n}` is already defined {r}"
    let q ← posOf s[1]; modify fun st => { st with taken := (n, Parse.at_ q) :: st.taken }; pure n
  let objDecl (d : C ObjDef) : C Decl := do
    let n ← objName; let d ← d; modify fun st => { st with objs := n :: st.objs }; pure (.obj p n d)
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
    -- `_on_` is one Lean identifier: its text read as `Parse.decl` reads a head
    let (w, key) ← onText s[0] (tokText s[0][0] ++ (if s[0].getKind == ``wNeg then tokText s[0][1] else "")) do
      let w ← Parse.word
      if w != "_" then pure (w, w) else do
        let n ← Parse.word
        if (← Parse.peek) != some '_' then Parse.expected s!"'_' closing the infix operator `_{n}_`"
        Parse.adv; pure (n, Parse.infixKey n)
    defn s w key (opt s[1]) s[2] s[4] s[5] s[6]
  | ``sInfix => do let n ← wordOf s[1]; defn s n (Parse.infixKey n) s[4].getSepArgs s[6] s[8] s[9] s[10]
  | _ => failAt s "expected a declaration"

/-- The program of the statements `ss`, read after the prelude in the scope `Parse.scope` leaves. -/
def program (fm : FileMap) (ss : Array Syntax) : Except Err Program := do
  let (_, s₀) ← Parse.scope Parse.prelude
  (ss.toList.mapM stmt |>.run fm).run' s₀

@[command_elab relProgram] def elabRelProgram : CommandElab := fun stx => do
  match program (← getFileMap) stx[3].getArgs with
  | .error e => throwErrorAt stx "{e}"
  | .ok prog => liftTermElabM do
    let n := (← getCurrNamespace) ++ stx[1].getId
    addAndCompile <| .defnDecl
      { name := n, levelParams := [], type := mkConst ``Program, value := toExpr (α := List Decl) prog,
        hints := .abbrev, safety := .safe }
    Term.addTermInfo' stx[1] (mkConst n) (isBinder := true)

end LeetQ.Rel.Lang.Embed
