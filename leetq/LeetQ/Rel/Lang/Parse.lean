import LeetQ.Rel.Lang.Syntax

/-! The parser of the Rel language: text to `Program`, recursive descent over the characters (§c).

    A run of letters is split at the longest prefix that is a name in scope (`Qc` is `Q` then `c`, `π₁B` is
    `π₁` then `B`), as the note writes composition by juxtaposition; a run no prefix of which is in scope is one
    name, which the elaborator reports. The descent is `partial`: it recurses on the input, never past its end. -/

namespace LeetQ.Rel.Lang.Parse

open LeetQ.Rel.Lang

structure S where
  cs : Array Char
  i : Nat := 0
  line : Nat := 1
  col : Nat := 1
  /-- The program's names in scope, with their arities: definitions so far and the parameters. -/
  known : List (String × Nat) := []
  /-- The declared objects. -/
  objs : List String := []

abbrev P := StateT S (Except Err)

instance {α : Type} : Inhabited (P α) := ⟨fun _ => .error default⟩

def pos : P Pos := do let s ← get; pure ⟨s.line, s.col⟩
def peekAt (k : Nat) : P (Option Char) := do let s ← get; pure s.cs[s.i + k]?
def peek : P (Option Char) := peekAt 0
def adv : P Unit := modify fun s => match s.cs[s.i]? with
  | some '\n' => { s with i := s.i + 1, line := s.line + 1, col := 1 }
  | _ => { s with i := s.i + 1, col := s.col + 1 }

def found : P String := do
  match ← peek with
  | none => pure "the end of the text"
  | some '\n' => pure "the end of the line"
  | some c => pure s!"'{c}'"

def expected {α : Type} (what : String) : P α := do throw ⟨← pos, s!"expected {what}, found {← found}"⟩

def isSub (c : Char) : Bool := 0x2080 ≤ c.val && c.val ≤ 0x2089
/-- A letter: Latin or Greek (`π`, `Λ`, `σ`, …). -/
def isLetter (c : Char) : Bool := c.isAlpha || (0x370 ≤ c.val && c.val ≤ 0x3FF)
def isIdCont (c : Char) : Bool := isLetter c || c.isDigit || isSub c || c == '\''
/-- The characters of the grammar itself; any other non-letter is a one-character name (`⊤ ≤ ≼ ∋`). -/
def reserved : List Char :=
  ['(', ')', ',', '⟨', '⟩', '[', ']', '⦇', '⦈', '{', '}', '°', '∼', '≜', '⊑', '=', ':', '⟶', '…', '-', '𝒫'] ++
    Bin.table.map (·.1)
def isSym (c : Char) : Bool := !(c.isWhitespace || isIdCont c || reserved.contains c)

/-- Spaces and a `--` comment, never the newline that ends a declaration. -/
partial def ws : P Unit := do
  match ← peek with
  | some ' ' | some '\t' | some '\r' => adv; ws
  | some '-' => if (← peekAt 1) == some '-' then skipLine else pure ()
  | _ => pure ()
where skipLine : P Unit := do
  match ← peek with
  | none | some '\n' => pure ()
  | _ => adv; skipLine

def tok (c : Char) : P Unit := do
  ws; if (← peek) == some c then adv else expected s!"'{c}'"

/-- The run of identifier characters at the cursor. -/
partial def run : P (List Char) := do
  match ← peek with
  | some c => if isIdCont c then do adv; pure (c :: (← run)) else pure []
  | none => pure []

/-- A word, whole: an object name, an element, a number, a defined name at its definition. -/
def word : P String := do
  ws
  match ← peek with
  | some c =>
    if isIdCont c then pure (String.ofList (← run))
    else if isSym c then (do adv; pure c.toString)
    else expected "a name"
  | none => expected "a name"

def builtin (n : String) : Option (Op × Nat) := (Op.table.find? (·.1 == n)).map (·.2)

/-- A name in a term: the longest prefix of the run that is in scope and ends where a letter starts. -/
def name : P String := do
  let s ← get
  match s.cs[s.i]? with
  | some c =>
    if isSym c then do adv; pure c.toString else
    let r := (List.range (s.cs.size - s.i)).takeWhile (fun k => isIdCont (s.cs[s.i + k]!)) |>.length
    let inScope (n : String) := s.known.any (·.1 == n) || (builtin n).isSome
    let cut := (List.range r).reverse.find? fun k =>
      inScope (String.ofList (s.cs.extract s.i (s.i + k + 1)).toList) &&
        (k + 1 == r || isLetter (s.cs[s.i + k + 1]!))
    let k := (cut.map (· + 1)).getD r
    for _ in List.range k do adv
    pure (String.ofList (s.cs.extract s.i (s.i + k)).toList)
  | none => expected "a name"

mutual

/-- `object := oprim (('×' | '+') oprim)*`, left to right. -/
partial def object : P OExp := do
  let mut o ← oprim
  repeat
    ws
    match ← peek with
    | some '×' => adv; o := .prod o (← oprim)
    | some '+' => adv; o := .sum o (← oprim)
    | _ => break
  pure o

partial def oprim : P OExp := do
  ws
  let p ← pos
  match ← peek with
  | some '𝒫' => adv; pure (.pow (← oprim))
  | some '[' => adv; let o ← object; tok ']'; pure (.list o)
  | some '(' => adv; let o ← object; tok ')'; pure o
  | _ =>
    let w ← word
    if (← get).objs.contains w then pure (.name p w) else throw ⟨p, s!"expected an object, found '{w}'"⟩

end

/-- `e₁, …, eₖ` up to the closing character. -/
partial def sepBy {α : Type} (item : P α) (close : Char) : P (List α) := do
  let a ← item
  ws
  if (← peek) == some ',' then do adv; pure (a :: (← sepBy item close)) else do tok close; pure [a]

/-- A constant's objects `(A, B)`, when what follows the constant reads as objects; else none, and the
    parenthesis is a term composed after it. -/
def constObjs : P (List OExp) := do
  if (← peek) != some '(' then return []
  let s ← get
  try adv; sepBy object ')' catch _ => do set s; pure []

def startsPrimary (c : Char) : Bool :=
  ['(', '⟨', '[', '⦇', '{', '∼'].contains c || isLetter c || isSym c

mutual

/-- `expr := primary (op? primary)*`: composition by juxtaposition and the infix operators, one level, left to
    right (§c). -/
partial def expr : P Expr := do
  let mut e ← primary
  repeat
    ws
    match ← peek with
    | some c => match Bin.table.lookup c with
      | some o => let p ← pos; adv; e := .bin p o e (← primary)
      | none => if startsPrimary c then e := .comp e (← primary) else break
    | none => break
  pure e

/-- `primary := '∼' primary | atom '°'*`. -/
partial def primary : P Expr := do
  ws
  let p ← pos
  if (← peek) == some '∼' then do adv; pure (.compl p (← primary)) else
  let mut a ← atom
  repeat
    if (← peek) == some '°' then do let q ← pos; adv; a := .conv q a else break
  pure a

partial def atom : P Expr := do
  ws
  let p ← pos
  match ← peek with
  | some '(' => adv; let e ← expr; tok ')'; pure e
  | some '⟨' => adv; let a ← expr; tok ','; let b ← expr; tok '⟩'; pure (.pair p a b)
  | some '[' => adv; let a ← expr; tok ','; let b ← expr; tok ']'; pure (.junc p a b)
  | some '⦇' => adv; let a ← expr; tok ','; let b ← expr; tok '⦈'; pure (.fold p a b)
  | some '{' => adv; pure (.lit p (← sepBy litPair '}'))
  | some c =>
    if !(isLetter c || isSym c) then expected "a term" else
    let n ← name
    match (← get).known.lookup n, builtin n with
    | some 0, _ => pure (.name p n)
    | some _, _ => do tok '('; pure (.app p n (← sepBy expr ')'))
    | none, some (o, 0) => pure (.op p o (← constObjs) [])
    | none, some (o, _) =>
      -- `ran⟨D,…⟩`: a pair is its own parentheses
      if (← peek) == some '⟨' then do pure (.op p o [] [← atom]) else do tok '('; pure (.op p o [] (← sepBy expr ')'))
    | none, none => pure (.name p n)
  | none => expected "a term"

partial def litPair : P (String × String) := do
  tok '('; let a ← word; tok ','; let b ← word; tok ')'; pure (a, b)

end

/-- A parameter: a name and, when it may be given a family, its type `A ⟶ B`. -/
def param : P Param := do
  let n ← word
  ws
  if (← peek) == some ':' then do adv; let a ← object; tok '⟶'; let b ← object; pure ⟨n, some (a, b)⟩
  else pure ⟨n, none⟩

def num : P Nat := do
  let p ← pos
  let w ← word
  match w.toNat? with | some k => pure k | none => throw ⟨p, s!"expected a number, found '{w}'"⟩

/-- The names a definition must not take: they read as `∪ ∩ ⊤ °`. -/
def banned : List String := ["U", "u", "n", "T", "o"]

/-- One declaration, up to the end of its line. -/
def decl (p : Pos) (w : String) : P Decl := do
  match w with
  | "obj" =>
    let n ← word
    tok '='
    ws
    let d ← match ← peek with
      | some '{' => do adv; pure (ObjDef.elems (← sepBy word '}'))
      | some c =>
        if c.isDigit then (do let lo ← num; tok '…'; pure (ObjDef.range lo (← num)))
        else (do pure (ObjDef.alias (← object)))
      | none => expected "an object"
    modify fun s => { s with objs := n :: s.objs }
    pure (.obj p n d)
  | "print" => pure (.print p (← expr))
  | "check" =>
    let e ← expr
    ws
    let eq ← match ← peek with
      | some '⊑' => do adv; pure false
      | some '=' => do adv; pure true
      | _ => expected "'⊑' or '='"
    pure (.check p e (← expr) eq)
  | _ =>
    if banned.contains w then throw ⟨p, s!"the name '{w}' reads as an operator; choose another"⟩
    ws
    let ps ← if (← peek) == some '(' then do adv; sepBy param ')' else pure []
    let outer := (← get).known
    modify fun s => { s with known := ps.map (fun q => (q.name, 0)) ++ s.known }
    tok '≜'
    let e ← expr
    ws
    let b ← if (← peek) == some '⊑' then do adv; pure (Body.test e (← expr)) else pure (Body.rel e)
    modify fun s => { s with known := (w, ps.length) :: outer }
    pure (.defn p w ps b)

partial def program : P Program := do
  ws
  match ← peek with
  | none => pure []
  | some '\n' => adv; program
  | some _ =>
    let p ← pos
    let d ← decl p (← word)
    ws
    match ← peek with
    | none => pure [d]
    | some '\n' => adv; pure (d :: (← program))
    | some _ => expected "the end of the line"

/-- Parse a program's text. -/
def parse (src : String) : Except Err Program := (program.run { cs := src.toList.toArray }).map (·.1)

/-- Parse one term with the given names in scope: the round-trip checks. -/
def parseExpr (src : String) (known : List (String × Nat) := []) (objs : List String := []) : Except Err Expr :=
  let p : P Expr := do let e ← expr; ws; if (← peek) == none then pure e else expected "the end of the term"
  (p.run { cs := src.toList.toArray, known, objs }).map (·.1)

end LeetQ.Rel.Lang.Parse
