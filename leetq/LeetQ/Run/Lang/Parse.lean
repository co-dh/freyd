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
  /-- Every name the program defines or declares, with where ("at line 3"): a second definition of it is an
      error; a name another program gives is no clash (it is shadowed). -/
  taken : List (String × String) := []
  /-- The resolver (module design §2.3): a written name to another program's registered definition or object,
      by Lean's namespace and `open`s; `ns`, whether a written prefix (`csp`) is a namespace. -/
  res : String → Found := fun _ => .none
  ns : String → Bool := fun _ => false
  /-- The constants the resolver gave a name read so far: the program's names that reach other programs. -/
  used : List Lean.Name := []
  /-- The theorems so far: a `calc` step cites them, a term may not name them (§3). -/
  thms : List String := []
  /-- Inside a parameter's type: an object may be an object variable (§e). -/
  vars : Bool := false

abbrev P := StateT S (Except Err)

instance {α : Type} : Inhabited (P α) := ⟨fun _ => .error default⟩

def pos : P Pos := do let s ← get; pure ⟨s.line, s.col⟩
def peek : P (Option Char) := do let s ← get; pure s.cs[s.i]?
-- the text is one Lean token, so no newline: Lean's tokenizer has read the lines, spaces and comments
def adv : P Unit := modify fun s => { s with i := s.i + 1, col := s.col + 1 }

def advN (k : Nat) : P Unit := for _ in List.range k do adv

def found : P String := do
  match ← peek with
  | none => pure "the end of the text"
  | some c => pure s!"'{c}'"

def expected {α : Type} (what : String) : P α := do throw ⟨← pos, s!"expected {what}, found {← found}"⟩

def isSub (c : Char) : Bool := 0x2080 ≤ c.val && c.val ≤ 0x2089
/-- A letter: Latin or Greek (`π`, `Λ`, `σ`, …). -/
def isLetter (c : Char) : Bool := c.isAlpha || (0x370 ≤ c.val && c.val ≤ 0x3FF)
def isIdCont (c : Char) : Bool := isLetter c || c.isDigit || isSub c || c == '\''
/-- The characters of the grammar itself; any other non-letter is a one-character name (`⊤ ≤ ≼ ∋`). -/
def reserved : List Char :=
  ['(', ')', ',', '⟨', '⟩', '[', ']', '⦇', '⦈', '{', '}', '°', '*', '∼', '≜', '⊑', '=', ':', '⟶', '…', '-', '𝒫', '.'] ++
    Bin.table.map (·.1)
def isSym (c : Char) : Bool := !(c.isWhitespace || isIdCont c || reserved.contains c)
/-- The form of an object variable: one lowercase Greek letter `α`…`ω`, then only primes and subscript digits. -/
def isVar (w : String) : Bool := match w.toList with
  | c :: cs => 0x3B1 ≤ c.val && c.val ≤ 0x3C9 && cs.all fun d => isSub d || d == '\''
  | [] => false

def tok (c : Char) : P Unit := do
  if (← peek) == some c then adv else expected s!"'{c}'"

/-- The run of identifier characters at the cursor. -/
partial def run : P (List Char) := do
  match ← peek with
  | some c => if isIdCont c then do adv; pure (c :: (← run)) else pure []
  | none => pure []

/-- A word, whole: an object name, an element, a number, a defined name at its definition. The sign of `-3` is
    Lean's (`Embed.wNeg`). -/
def word : P String := do
  match ← peek with
  | some c =>
    if isIdCont c then pure (String.ofList (← run))
    else if isSym c then (do adv; pure c.toString)
    else expected "a name"
  | none => expected "a name"

def builtin (n : String) : Option (Op × Nat) := (Op.table.find? (·.1 == n)).map (·.2)

/-- The key of the infix operator `n`, as its declaration `_n_(R,S)` names it (§c). -/
def infixKey (n : String) : String := s!"_{n}_"

/-- The definition or object the resolver gives `n`, when one. -/
def S.ext (s : S) (n : String) : Option Ext := match s.res n with | .ext e => some e | _ => none

/-- `n` is an infix operator: the program's `_n_`, else, unless the program names `n`, a registered infix. -/
def isInfix (n : String) : P Bool := do
  let s ← get
  pure (s.known.any (·.1 == infixKey n) || (!s.known.any (·.1 == n) && (s.ext n).any (·.isInfix)))

/-- The program's name, a builtin, or one the resolver gives (§2.3): what a run of letters is cut at. -/
def S.inScope (s : S) (n : String) : Bool :=
  s.known.any (fun k => k.1 == n || k.1 == infixKey n) || (builtin n).isSome ||
    match s.res n with | .ext _ => true | .bad b _ => b | .none => false

/-- The length of the run of identifier characters at `i`. -/
def S.runLen (s : S) (i : Nat) : Nat := (List.range (s.cs.size - i)).takeWhile (fun k => s.cs[i + k]?.any isIdCont) |>.length

def S.text (s : S) (a b : Nat) : String := String.ofList (s.cs.extract a b).toList

/-- The name `n` read at `p`: in scope, or one the resolver refuses with a reason (ambiguous, no Rel definition),
    which is the error. -/
def resolved (p : Pos) (n : String) : P String := do
  let s ← get
  if !(s.known.any (fun k => k.1 == n || k.1 == infixKey n) || (builtin n).isSome) then
    match s.res n with
    | .bad _ m => throw ⟨p, m⟩
    | .ext e => set { s with used := e.const :: s.used }
    | .none => pure ()
  pure n

/-- The longest prefix `k` of the `r` characters at the cursor that `ok` holds of and that ends where a letter
    starts; the whole run when none. -/
def cutAt (s : S) (r : Nat) (ok : String → Bool) : Nat :=
  let cut := (List.range r).reverse.find? fun k => ok (s.text s.i (s.i + k + 1)) && (k + 1 == r || s.cs[s.i + k + 1]?.any isLetter)
  (cut.map (· + 1)).getD r

/-- After the namespace `m` and its `.`: the member, a one-character name or the longest prefix of the run the
    resolver knows as `m.x` (`csp.AC3peer` is `csp.AC3` then `peer`); a run that is a namespace again goes on. -/
partial def qual (p : Pos) (m : String) : P String := do
  adv
  let s ← get
  match s.cs[s.i]? with
  | some c =>
    if isSym c then do adv; resolved p s!"{m}.{c}" else
    let r := s.runLen s.i
    if r == 0 then expected "a name after '.'"
    let w := s!"{m}.{s.text s.i (s.i + r)}"
    if s.cs[s.i + r]? == some '.' && s.ns w then return ← (do advN r; qual p w)
    let k := cutAt s r fun x => match s.res s!"{m}.{x}" with | .ext _ | .bad true _ => true | _ => false
    advN k
    resolved p s!"{m}.{s.text s.i (s.i + k)}"
  | none => expected "a name after '.'"

/-- A name in a term: `m.x` where the run before `.` is a namespace (§2.3), else the longest prefix of the run
    that is in scope and ends where a letter starts. -/
def name : P String := do
  let s ← get
  let p ← pos
  match s.cs[s.i]? with
  | some c =>
    if isSym c then do adv; resolved p c.toString else
    let r := s.runLen s.i
    let w := s.text s.i (s.i + r)
    if s.cs[s.i + r]? == some '.' && s.ns w then return ← (do advN r; qual p w)
    let k := cutAt s r s.inScope
    advN k
    resolved p (s.text s.i (s.i + k))
  | none => expected "a name"

/-- A word, or `m.w` where `m` is a namespace (`board9.Cell`). -/
partial def qword : P String := do
  let w ← word
  if (← peek) == some '.' && (← get).ns w then do adv; let v ← qword; pure s!"{w}.{v}" else pure w

/-- The object word of `relObj`'s `oWord` (`Embed.obj`), whose `[ ]`, `( )`, `×`, `+` and `𝒫 (…)` are Lean's:
    `𝒫`s, since Lean reads `𝒫A` as one identifier, then a qualified word. -/
partial def object : P OExp := do
  let p ← pos
  if (← peek) == some '𝒫' then do adv; return .pow (← object)
  let w ← qword
  let s ← get
  -- a variable is not a declared object and not a definition in scope (§e)
  if s.objs.contains w then pure (.name p w)
  else if s.vars && isVar w && !s.known.any (·.1 == w) then pure (.var p w)
  else match s.res w with
    | .ext e => if e.obj then do set { s with used := e.const :: s.used }; pure (.name p w) else throw ⟨p, s!"expected an object, found '{w}'"⟩
    | .bad _ m => throw ⟨p, m⟩
    | .none => throw ⟨p, s!"expected an object, found '{w}'"⟩

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
def num (w : String) : P Int := do
  let p ← pos
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

/-- The operator `n` of an infix key `_n_`, read back by the reader that reads its declaration; none for a name. -/
def unInfix (k : String) : Option String :=
  match (do tok '_'; let n ← word; tok '_'; if (← peek).isSome then expected "the end" else pure n : P String).run'
    { cs := k.toList.toArray } with
  | .ok n => some n
  | .error _ => none

/-- The constant of the definition or object `k` (an infix key `_n_` is `n`, the infix bit kept in the registry)
    of the program `home`. -/
def constOf (home : Lean.Name) (k : String) : Lean.Name := home.str ((unInfix k).getD k)

/-- The entry of the program `home`'s declaration `d`, when it is a definition or an object. -/
def extOf (home : Lean.Name) : Decl → Option (String × Ext)
  | .defn _ k ps .. => some (k, { const := constOf home k, arity := ps.length, isInfix := (unInfix k).isSome })
  | .obj _ k _ => some (k, { const := home.str k, obj := true })
  | .«theorem» _ k .. => some (k, { const := home.str k, thm := true })
  | _ => none

/-- The parts of a written name `m.x` (`csp.AC3`, `csp.≼`), as `name` reads them: words between `.`s. -/
partial def parts (t : String) : List String :=
  match go.run' { cs := t.toList.toArray } with | .ok ps => ps | .error _ => [t]
where go : P (List String) := do
  let w ← word
  if (← peek) == some '.' then do adv; pure (w :: (← go)) else pure [w]

/-- The resolver of a text read outside any Lean scope (a test, `typesOf`): every name of the programs `homes`
    unqualified, a later one shadowing, as if each were `open`ed in order. -/
def openAll (homes : List (Lean.Name × Program)) (n : String) : Found :=
  match (homes.flatMap fun (h, prog) => (prog.filterMap (extOf h)).filter fun (k, _) => k == n || k == infixKey n).getLast? with
  | some (_, e) => .ext e
  | none => .none

end LeetQ.Rel.Lang.Parse
