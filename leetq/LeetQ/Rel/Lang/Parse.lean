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
  /-- Every name defined or declared, with where ("at line 3", "in the prelude"): a second definition of it is an
      error. -/
  taken : List (String × String) := []
  /-- Inside a parameter's type: an object may be an object variable (§e). -/
  vars : Bool := false

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
/-- The form of an object variable: one lowercase Greek letter `α`…`ω`, then only primes and subscript digits. -/
def isVar (w : String) : Bool := match w.toList with
  | c :: cs => 0x3B1 ≤ c.val && c.val ≤ 0x3C9 && cs.all fun d => isSub d || d == '\''
  | [] => false

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

/-- At the cursor an ASCII `-` with a digit right after it: the sign of a number word (§c). `--` is a comment and
    `−` (U+2212) the difference, so neither reads as a sign. -/
def atSign : P Bool := do pure ((← peek) == some '-' && ((← peekAt 1).map Char.isDigit).getD false)

/-- A word, whole: an object name, an element, a number (signed: `-3`), a defined name at its definition. -/
def word : P String := do
  ws
  if ← atSign then do adv; return "-" ++ String.ofList (← run)
  match ← peek with
  | some c =>
    if isIdCont c then pure (String.ofList (← run))
    else if isSym c then (do adv; pure c.toString)
    else expected "a name"
  | none => expected "a name"

def builtin (n : String) : Option (Op × Nat) := (Op.table.find? (·.1 == n)).map (·.2)

/-- The key of the infix operator `n`, as its declaration `_n_(R,S)` names it (§c). -/
def infixKey (n : String) : String := s!"_{n}_"

def isInfix (n : String) : P Bool := do pure ((← get).known.any (·.1 == infixKey n))

/-- A name in a term: the longest prefix of the run that is in scope and ends where a letter starts. -/
def name : P String := do
  let s ← get
  match s.cs[s.i]? with
  | some c =>
    if isSym c then do adv; pure c.toString else
    let r := (List.range (s.cs.size - s.i)).takeWhile (fun k => isIdCont (s.cs[s.i + k]!)) |>.length
    let inScope (n : String) := s.known.any (fun k => k.1 == n || k.1 == infixKey n) || (builtin n).isSome
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
    let s ← get
    -- a variable is not a declared object and not a definition in scope (§e)
    if s.objs.contains w then pure (.name p w)
    else if s.vars && isVar w && !s.known.any (·.1 == w) then pure (.var p w)
    else throw ⟨p, s!"expected an object, found '{w}'"⟩

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

/-- The word `where` at the cursor: the end of a definition's body (§c). -/
def atWhere : P Bool := do
  let cs ← [0, 1, 2, 3, 4, 5].mapM peekAt
  pure (cs.take 5 == "where".toList.map some && !((cs.getD 5 none).any isIdCont))

def startsPrimary (c : Char) : Bool :=
  ['(', '⟨', '[', '⦇', '{', '∼'].contains c || isLetter c || isSym c

mutual

/-- `expr := primary (op? primary)*`: composition by juxtaposition, the builtin infix operators and the declared
    ones (`_n_`), one level, left to right (§c). -/
partial def expr : P Expr := do
  let mut e ← primary
  repeat
    ws
    match ← peek with
    | some c => match Bin.table.lookup c with
      | some o => let p ← pos; adv; e := .bin p o e (← primary)
      | none =>
        if startsPrimary c && !(← atWhere) then
          let s ← get; let p ← pos; let n ← name
          if n != "" && (← isInfix n) then e := .inf p n e (← primary)
          else do set s; e := .comp e (← primary)
        else break
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
    | none, some (.index _, _) => do
      -- `at(i)`: its argument is a position, a number word read by `String.toInt?` as every number word is
      tok '('; ws; let q ← pos; let w ← word; tok ')'
      match w.toInt? with
      | some k => if 0 ≤ k ∧ k < 2^63 then pure (.op p (.index k.toNat) [] [])
                  else throw ⟨q, s!"at( ) takes a position from 0 that fits a long, found {w}"⟩
      | none => throw ⟨q, s!"at( ) takes a position, a number from 0, found '{w}'"⟩
    | none, some (o, 0) => pure (.op p o (← constObjs) [])
    | none, some (o, _) =>
      -- `ran⟨D,…⟩`: a pair is its own parentheses
      if (← peek) == some '⟨' then do pure (.op p o [] [← atom]) else do tok '('; pure (.op p o [] (← sepBy expr ')'))
    | none, none =>
      if !(← isInfix n) then pure (.name p n)
      else if (← peek) == some '(' then throw ⟨p, s!"`{n}` is an infix operator: write `R {n} S`, not `{n}(R, S)`"⟩
      else throw ⟨p, s!"`{n}` is an infix operator: it stands between two terms, `R {n} S`"⟩
  | none => expected "a term"

/-- A literal's row `(a, b)`, each side a word, a nested pair or an array. -/
partial def litPair : P (Tup × Tup) := do
  tok '('; let a ← tup; tok ','; let b ← tup; tok ')'; pure (a, b)

/-- A side: one item, or two or more juxtaposed, the array of them (`3 1 2`, `-1 2`, `[1 2] [3]`). -/
partial def tup : P Tup := do
  let a ← litItem
  let mut ts := #[a]
  repeat
    ws
    match ← peek with
    | some c => if c == '(' || c == '[' || isIdCont c || isSym c || (← atSign) then ts := ts.push (← litItem) else break
    | none => break
  pure (if ts.size == 1 then a else .arr ts.toList)

/-- An item: a word, a row, or `[` items `]`, always an array (`[]`, `[1]`). `[` here is never the case term
    `[R,S]`, which is read only at a term. -/
partial def litItem : P Tup := do
  ws
  match ← peek with
  | some '(' => let (a, b) ← litPair; pure (.pair a b)
  | some '[' => adv; pure (.arr (← bracket))
  | _ => pure (.leaf (← word))

/-- The items of a bracketed array up to its `]`, separated by spaces. -/
partial def bracket : P (List Tup) := do
  ws
  match ← peek with
  | some ']' => adv; pure []
  | some ',' => throw ⟨← pos, "the elements of an array are separated by spaces, not ','"⟩
  | _ => let a ← litItem; pure (a :: (← bracket))

end

/-- The names a definition must not take: they read as `∪ ∩ ⊤ °`. -/
def banned : List String := ["U", "u", "n", "T", "o"]

/-- `w` may be defined at `p`: not a builtin of the operator table, not read as an operator, and neither it nor
    its infix form `_w_` in `taken`, the names already defined or declared in its scope. -/
def fresh (p : Pos) (w : String) (taken : List (String × String)) : P Unit := do
  if banned.contains w then throw ⟨p, s!"the name '{w}' reads as an operator; choose another"⟩
  if (builtin w).isSome then throw ⟨p, s!"`{w}` is a builtin; choose another name"⟩
  for k in [w, infixKey w] do
    if let some q := taken.lookup k then throw ⟨p, s!"`{w}` is already defined {q}"⟩

def at_ (p : Pos) : String := s!"at line {p.line}"

/-- A type `: A ⟶ B` at the cursor, its objects possibly object variables (§e); none when no `:` follows. -/
def typeOpt : P (Option (OExp × OExp)) := do
  ws
  if (← peek) != some ':' then return none
  adv; modify fun s => { s with vars := true }
  let a ← object; tok '⟶'; let b ← object
  modify fun s => { s with vars := false }; pure (some (a, b))

/-- A parameter: a name and its type `A ⟶ B`. -/
def param : P Param := do
  ws
  let p ← pos
  let n ← word
  if (builtin n).isSome then throw ⟨p, s!"`{n}` is a builtin; choose another name"⟩
  pure ⟨n, ← typeOpt⟩

/-- A number word read by `String.toInt?`, the one reader every number word goes through (a literal's in
    `Elab.code`); a `long`, the type its elements are coded in. -/
def num : P Int := do
  let p ← pos
  let w ← word
  match w.toInt? with
  | some k => if -2^63 ≤ k ∧ k < 2^63 then pure k else throw ⟨p, s!"the number {w} does not fit a long"⟩
  | none => throw ⟨p, s!"expected a number, found '{w}'"⟩

/-- The items `x ≜ e, y ≜ f` of a `where`, each in scope in the items after it and, through `σ`, in the body;
    a name not yet defined, not a parameter of `w` and not an earlier item (§c). -/
partial def items (w : String) (ps : List Param) (taken : List (String × String)) (σ : List (String × Expr)) :
    P (List (String × Expr)) := do
  let q ← pos
  let n ← word
  fresh q n taken
  if ps.any (·.name == n) then throw ⟨q, s!"`{n}` is already a parameter of `{w}`"⟩
  if σ.any (·.1 == n) then throw ⟨q, s!"`{n}` is already an item of this `where`"⟩
  -- an item is typed by its place in the body; a type of its own needs a definition of its own (§e)
  ws
  if (← peek) == some ':' then
    throw ⟨q, s!"the `where` item `{n}` takes no type: make it a top-level definition to give it one (§e)"⟩
  tok '≜'
  let σ := σ ++ [(n, (← expr).subst σ)]
  -- in scope in the items after it, so a run of letters there is split with its name known (§c)
  modify fun s => { s with known := (n, 0) :: s.known }
  ws
  if (← peek) == some ',' then do adv; items w ps taken σ else pure σ

/-- One declaration, up to the end of its line. -/
def decl (p : Pos) (w : String) : P Decl := do
  match w with
  | "obj" =>
    ws
    let q ← pos
    let n ← word
    if let some r := (← get).taken.lookup n then throw ⟨q, s!"`{n}` is already defined {r}"⟩
    tok '='
    ws
    let d ← match ← peek with
      | some '{' => do adv; pure (ObjDef.elems (← sepBy word '}'))
      | some c =>
        if c.isDigit || (← atSign) then (do
          let lo ← num; tok '…'; ws; let r ← pos; let hi ← num
          if hi < lo then throw ⟨r, s!"the range {lo}…{hi} is empty: {hi} is below {lo}"⟩
          pure (ObjDef.range lo hi))
        else (do pure (ObjDef.alias (← object)))
      | none => expected "an object"
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
    -- `_n_(R,S) ≜ …` declares the infix operator `n`, keyed `_n_` (§c)
    let (w, key) ← if w != "_" then pure (w, w) else do
      let n ← word
      if (← peek) != some '_' then expected s!"'_' closing the infix operator `_{n}_`"
      adv; pure (n, infixKey n)
    fresh p w (← get).taken
    ws
    let ps ← if (← peek) == some '(' then do adv; sepBy param ')' else pure []
    if key != w && ps.length != 2 then
      throw ⟨p, s!"the infix operator `{w}` takes two parameters, `{key}(R, S)`, found {ps.length}"⟩
    -- a parameter may shadow a top-level definition (`on` in Chess), never another parameter
    let _ ← ps.foldlM (fun (seen : List String) q => do
      if seen.contains q.name then throw ⟨p, s!"`{q.name}` is already a parameter of `{w}`"⟩
      pure (q.name :: seen)) []
    let ty ← typeOpt
    let outer := (← get).known
    modify fun s => { s with known := ps.map (fun q => (q.name, 0)) ++ s.known }
    -- the body with the names `inBody` in scope as well, then its `where` items
    let rest (inBody : List (String × Nat)) : P (Body × List (String × Expr)) := do
      let k := (← get).known
      modify fun s => { s with known := inBody ++ k }
      tok '≜'
      let e ← expr
      ws
      let b ← if (← peek) == some '⊑' then do adv; pure (Body.test e (← expr)) else pure (Body.rel e)
      if let (.test .., some t) := (b, ty) then
        throw ⟨p, s!"the test `{w}` has no type of its own: drop ': {OExp.arrow t}' (§e)"⟩
      modify fun s => { s with known := k }
      ws
      -- an item takes no name the definition itself takes
      let σ ← if ← atWhere then do let _ ← word; items w ps ((key, at_ p) :: (← get).taken) [] else pure []
      pure (b, σ)
    -- a `where` item is in scope in the body (§c), so a run of letters there is split with its name known: the
    -- items' names are read after the body, which is then read again
    let s₀ ← get
    let (b, σ) ← rest []
    let (b, σ) ← if σ.isEmpty then pure (b, σ) else do set s₀; rest (σ.map fun (n, _) => (n, 0))
    let b := match b with | .rel e => Body.rel (e.subst σ) | .test e f => .test (e.subst σ) (f.subst σ)
    modify fun s => { s with known := outer }
    pure (.defn p key ps b ty)

/-- The scope the program `prog` leaves when read in the scope `s`: each definition known with its arity, each
    object declared, each name taken at its line. -/
def after (s : S) (prog : Program) : S := prog.foldl (init := s) fun s d => match d with
  | .defn p k ps _ _ => { s with known := (k, ps.length) :: s.known, taken := (k, at_ p) :: s.taken }
  | .obj p n _ => { s with objs := n :: s.objs, taken := (n, at_ p) :: s.taken }
  | _ => s

partial def program : P Program := do
  ws
  match ← peek with
  | none => pure []
  | some '\n' => adv; program
  | some _ =>
    let p ← pos
    let d ← decl p (← word)
    modify (after · [d])
    ws
    match ← peek with
    | none => pure [d]
    | some '\n' => adv; pure (d :: (← program))
    | some _ => expected "the end of the line"

/-- The scope a program is read in after the prelude `pre` (§c, `Programs.prelude`), itself read in the empty
    scope: its names and objects, each name taken "in the prelude". -/
def scope (pre : Program) : S :=
  let s := after { cs := #[] } pre
  { s with taken := s.taken.map fun (n, _) => (n, "in the prelude") }

/-- Parse a program's text in the scope `s`. -/
def parseIn (s : S) (src : String) : Except Err Program :=
  (program.run { s with cs := src.toList.toArray, i := 0, line := 1, col := 1 }).map (·.1)

/-- Parse one term in the scope `s`, with the given names in scope as well: the round-trip checks. -/
def parseExprIn (s : S) (src : String) (known : List (String × Nat) := []) (objs : List String := []) :
    Except Err Expr :=
  let p : P Expr := do let e ← expr; ws; if (← peek) == none then pure e else expected "the end of the term"
  let s' := { s with cs := src.toList.toArray, i := 0, line := 1, col := 1 }
  (p.run { s' with known := known ++ s.known, objs := objs ++ s.objs }).map (·.1)

end LeetQ.Rel.Lang.Parse
