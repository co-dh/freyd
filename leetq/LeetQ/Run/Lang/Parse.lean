import LeetQ.Run.Lang.Syntax

/-! The scope and the words of the Rel language, read by `Embed` from the tokens of a `rel_program` (§c).

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
  /-- The theorems so far: a `calc` step cites them, a term may not name them (§3). -/
  thms : List String := []
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
  ['(', ')', ',', '⟨', '⟩', '[', ']', '⦇', '⦈', '{', '}', '°', '*', '∼', '≜', '⊑', '=', ':', '⟶', '…', '-', '𝒫'] ++
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
    let r := (List.range (s.cs.size - s.i)).takeWhile (fun k => s.cs[s.i + k]?.any isIdCont) |>.length
    let inScope (n : String) := s.known.any (fun k => k.1 == n || k.1 == infixKey n) || (builtin n).isSome
    let cut := (List.range r).reverse.find? fun k =>
      inScope (String.ofList (s.cs.extract s.i (s.i + k + 1)).toList) &&
        (k + 1 == r || s.cs[s.i + k + 1]?.any isLetter)
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

/-- The names a definition must not take: they read as `∪ ∩ ⊤ °`. -/
def banned : List String := ["U", "u", "n", "T", "o"]

/-- `μ` and `ν` open a fixed point `μX : φ`, `νX : φ`, read at a term before any name. -/
def isFix (c : Char) : Bool := c == 'μ' || c == 'ν'

/-- `w` may be defined at `p`: not a builtin of the operator table, not read as an operator or a fixed point,
    and neither it nor its infix form `_w_` in `taken`, the names already defined or declared in its scope. -/
def fresh (p : Pos) (w : String) (taken : List (String × String)) : P Unit := do
  if banned.contains w then throw ⟨p, s!"the name '{w}' reads as an operator; choose another"⟩
  if w.toList.head?.any isFix then throw ⟨p, s!"the name '{w}' reads as a fixed point μX or νX; choose another"⟩
  if (builtin w).isSome then throw ⟨p, s!"`{w}` is a builtin; choose another name"⟩
  for k in [w, infixKey w] do
    if let some q := taken.lookup k then throw ⟨p, s!"`{w}` is already defined {q}"⟩

def at_ (p : Pos) : String := s!"at line {p.line}"

/-- A number word read by `String.toInt?`, the one reader every number word goes through (a literal's in
    `Elab.code`); a `long`, the type its elements are coded in. -/
def num : P Int := do
  let p ← pos
  let w ← word
  match w.toInt? with
  | some k => if -2^63 ≤ k ∧ k < 2^63 then pure k else throw ⟨p, s!"the number {w} does not fit a long"⟩
  | none => throw ⟨p, s!"expected a number, found '{w}'"⟩

/-- The scope the program `prog` leaves when read in the scope `s`: each definition known with its arity, each
    object declared, each name taken at its line. -/
def after (s : S) (prog : Program) : S := prog.foldl (init := s) fun s d => match d with
  | .defn p k ps _ _ => { s with known := (k, ps.length) :: s.known, taken := (k, at_ p) :: s.taken }
  | .obj p n _ => { s with objs := n :: s.objs, taken := (n, at_ p) :: s.taken }
  | .«theorem» p n .. => { s with thms := n :: s.thms, taken := (n, at_ p) :: s.taken }
  | _ => s

/-- The scope a program is read in after the prelude `pre` (§c, `Programs.prelude`), itself read in the empty
    scope: its names and objects, each name taken "in the prelude". -/
def scope (pre : Program) : S :=
  let s := after { cs := #[] } pre
  { s with taken := s.taken.map fun (n, _) => (n, "in the prelude") }

end LeetQ.Rel.Lang.Parse
