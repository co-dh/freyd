/-! The Rel language's surface syntax (`doc/rel-lang-design.md` §c, §h): objects, terms, declarations, each node
    with its source line and column. The builtin operators are one table, `Op.table`, read by the parser (symbol,
    arity), the elaborator (typing, lifted row) and the evaluator (the `Alg` op), each by the `Op` constructor. -/

namespace LeetQ.Rel.Lang

/-- A source position: line and column, both from 1. -/
structure Pos where
  line : Nat := 0
  col : Nat := 0
  deriving Repr, BEq, Inhabited

instance : ToString Pos := ⟨fun p => s!"line {p.line}, col {p.col}"⟩

/-- A front-end error: where, and what was found against what was expected. -/
structure Err where
  pos : Pos
  msg : String
  deriving Repr, Inhabited

instance : ToString Err := ⟨fun e => s!"{e.pos}: {e.msg}"⟩

/-- An object as written: a declared name, `A×B`, `A+B`, `𝒫A`, `[A]`. -/
inductive OExp
  | name (p : Pos) (n : String)
  | prod (a b : OExp)
  | sum (a b : OExp)
  | pow (a : OExp)
  | list (a : OExp)
  deriving Repr, Inhabited

/-- The builtin operators of §b. A constant (arity 0) may take its objects, `⊤(A,B)`; the others take relations. -/
inductive Op
  | id | zero | top | mem | ni | outl | outr | inl | inr | leq | lt | succ | plus
  | union | tau | nil | alpha | cons | length | total | head | tail | pre | suf
  | dom | ran | lam | E | P | est | thin | filter | takewhile | map | frac
  deriving Repr, BEq, Inhabited

/-- The one table of builtins: symbol and arity. A program's definition of the same name shadows it. -/
def Op.table : List (String × Op × Nat) :=
  [("𝟙", .id, 0), ("𝟘", .zero, 0), ("⊤", .top, 0), ("∋", .mem, 0), ("∈", .ni, 0), ("π₁", .outl, 0),
   ("π₂", .outr, 0), ("inl", .inl, 0), ("inr", .inr, 0), ("≤", .leq, 0), ("<", .lt, 0), ("succ", .succ, 0),
   ("plus", .plus, 0), ("union", .union, 0), ("τ", .tau, 0), ("nil", .nil, 0), ("α", .alpha, 0),
   ("cons", .cons, 0), ("length", .length, 0), ("sum", .total, 0), ("head", .head, 0), ("tail", .tail, 0),
   ("prefix", .pre, 0), ("suffix", .suf, 0), ("dom", .dom, 1), ("ran", .ran, 1), ("Λ", .lam, 1), ("E", .E, 1),
   ("P", .P, 1), ("est", .est, 1), ("thin", .thin, 1), ("filter", .filter, 1), ("takewhile", .takewhile, 1),
   ("F", .map, 1), ("frac", .frac, 2)]

def Op.sym (o : Op) : String := ((Op.table.find? (·.2.1 == o)).map (·.1)).getD "?"

/-- The infix operators: `∩ ∪ − ⇒ / \ × +`, one level with composition, left to right (§c). -/
inductive Bin
  | meet | join | diff | imp | rdiv | ldiv | prod | sum
  deriving Repr, BEq, Inhabited

def Bin.table : List (Char × Bin) :=
  [('∩', .meet), ('∪', .join), ('−', .diff), ('⇒', .imp), ('/', .rdiv), ('\\', .ldiv), ('×', .prod), ('+', .sum)]

def Bin.sym (o : Bin) : String := ((Bin.table.find? (·.2 == o)).map (·.1.toString)).getD "?"

/-- A term of §c. `name` is a program's definition or parameter; `op` a builtin with its objects and arguments;
    `app` a program's operator applied. Composition is juxtaposition. -/
inductive Expr
  | name (p : Pos) (n : String)
  | op (p : Pos) (o : Op) (objs : List OExp) (args : List Expr)
  | app (p : Pos) (n : String) (args : List Expr)
  | comp (a b : Expr)
  | bin (p : Pos) (o : Bin) (a b : Expr)
  | conv (p : Pos) (a : Expr)
  | compl (p : Pos) (a : Expr)
  | pair (p : Pos) (a b : Expr)
  | junc (p : Pos) (a b : Expr)
  | fold (p : Pos) (e s : Expr)
  | lit (p : Pos) (ps : List (String × String))
  deriving Repr, Inhabited

/-- The position a term starts at. -/
def Expr.pos : Expr → Pos
  | .name p _ | .op p .. | .app p .. | .bin p .. | .conv p _ | .compl p _ | .pair p .. | .junc p .. | .fold p ..
  | .lit p _ => p
  | .comp a _ => a.pos

/-- A body: a relation, or a test `e ⊑ f` (§e). -/
inductive Body
  | rel (e : Expr)
  | test (e f : Expr)
  deriving Repr, Inhabited

/-- A parameter, with its declared type `S : A ⟶ B` when it may be given a family. -/
structure Param where
  name : String
  ty : Option (OExp × OExp)
  deriving Repr, Inhabited

/-- An object declaration's right side: named elements, a number range, or a derived object. -/
inductive ObjDef
  | elems (ws : List String)
  | range (lo hi : Nat)
  | alias (o : OExp)
  deriving Repr, Inhabited

inductive Decl
  | obj (p : Pos) (n : String) (d : ObjDef)
  | defn (p : Pos) (n : String) (ps : List Param) (b : Body)
  | print (p : Pos) (e : Expr)
  | check (p : Pos) (e f : Expr) (eq : Bool)
  deriving Repr, Inhabited

abbrev Program := List Decl

/-! ### Printing, in the syntax the parser reads: a composite on the right of an operator in parentheses -/

/-- `o` printed; `inner` parenthesises a product or sum, as an operand of `×`, `+`, `𝒫` needs. -/
def OExp.render (inner : Bool) : OExp → String
  | .name _ n => n
  | .prod a b => let s := s!"{a.render true}×{b.render true}"; if inner then s!"({s})" else s
  | .sum a b => let s := s!"{a.render true}+{b.render true}"; if inner then s!"({s})" else s
  | .pow a => s!"𝒫{a.render true}"
  | .list a => s!"[{a.render false}]"

def OExp.show (o : OExp) : String := o.render false

/-- `e` printed at the level `l`, parenthesised as §c's one level needs: `0` anywhere or the left operand of a
    composite or infix term, `1` its right operand or the operand of `∼` (a composite or infix term in
    parentheses), `2` under `°` (a complement too). `full` puts every composite and infix term in parentheses:
    the parser guards compare it with the reading written out. -/
def Expr.render (l : Nat) (full : Bool := false) : Expr → String
  | .name _ n => n
  | .op _ o objs args =>
    let os := if objs.isEmpty then "" else "(" ++ ", ".intercalate (objs.map OExp.show) ++ ")"
    let as := if args.isEmpty then "" else "(" ++ ", ".intercalate (args.map (Expr.render 0 full)) ++ ")"
    o.sym ++ os ++ as
  | .app _ n args => n ++ "(" ++ ", ".intercalate (args.map (Expr.render 0 full)) ++ ")"
  | .comp a b => let s := s!"{a.render 0 full} {b.render 1 full}"; if full || l ≥ 1 then s!"({s})" else s
  | .bin _ o a b => let s := s!"{a.render 0 full} {o.sym} {b.render 1 full}"; if full || l ≥ 1 then s!"({s})" else s
  | .conv _ a => s!"{a.render 2 full}°"
  | .compl _ a => let s := s!"∼{a.render 1 full}"; if l ≥ 2 then s!"({s})" else s
  | .pair _ a b => s!"⟨{a.render 0 full}, {b.render 0 full}⟩"
  | .junc _ a b => s!"[{a.render 0 full}, {b.render 0 full}]"
  | .fold _ a b => s!"⦇{a.render 0 full}, {b.render 0 full}⦈"
  | .lit _ ps => "{" ++ ", ".intercalate (ps.map fun (a, b) => s!"({a}, {b})") ++ "}"

def Expr.show (e : Expr) : String := e.render 0

end LeetQ.Rel.Lang
