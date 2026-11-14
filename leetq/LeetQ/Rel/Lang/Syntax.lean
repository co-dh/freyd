import QLean.Kernel.Elementwise

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

/-- Line 0 is no place in the program: an error of the prelude's own text says where in its message. -/
instance : ToString Err := ⟨fun e => if e.pos.line == 0 then e.msg else s!"{e.pos}: {e.msg}"⟩

/-- An error in the prelude's own text (§c), which is no place in the program. -/
def Err.inPrelude (e : Err) : Err := ⟨default, s!"in the prelude, {e.pos}: {e.msg}"⟩

/-- An object as written: a declared name, `A×B`, `A+B`, `𝒫A`, `[A]`; in a parameter's type also an object
    variable `α`, instantiated at each use (§e). -/
inductive OExp
  | name (p : Pos) (n : String)
  | var (p : Pos) (n : String)
  | prod (a b : OExp)
  | sum (a b : OExp)
  | pow (a : OExp)
  | list (a : OExp)
  deriving Repr, Inhabited

/-- The builtin operators of §b. A constant (arity 0) may take its objects, `⊤(A,B)`; the others take relations.
    `arith k` is the qlean kernel's integral value verb `k` on pairs of numbers (`Alg.arith`): one constructor, so
    every verb is typed, lifted and run by one path. -/
inductive Op
  | id | zero | top | mem | outl | outr | inl | inr | leq | lt | succ | arith (k : UInt8)
  | union | tau | nil | alpha | cons | length | total
  | dom | ran | lam | E | P | est | thin | map
  | inits | cat | zip | snoc | setify | bagify | tic
  | thinL | merge | loop
  /-- `at(i)`, the element at position `i` from `0`; `i` a number literal, read by the parser (`Parse.atom`). -/
  | index (i : Nat)
  deriving Repr, BEq, Inhabited

/-- The one table of builtins: symbol and arity. A program may not define or take as a parameter a name
    in it (§c). -/
def Op.table : List (String × Op × Nat) :=
  [("𝟙", .id, 0), ("𝟘", .zero, 0), ("⊤", .top, 0), ("∋", .mem, 0), ("π₁", .outl, 0),
   ("π₂", .outr, 0), ("inl", .inl, 0), ("inr", .inr, 0), ("≤", .leq, 0), ("<", .lt, 0), ("succ", .succ, 0),
   ("plus", .arith QLean.Kernel.Ew.add, 0), ("times", .arith QLean.Kernel.Ew.mul, 0),
   ("minus", .arith QLean.Kernel.Ew.sub, 0), ("div", .arith QLean.Kernel.Ew.idiv, 0),
   ("mod", .arith QLean.Kernel.Ew.imod, 0), ("max", .arith QLean.Kernel.Ew.greater, 0),
   ("min", .arith QLean.Kernel.Ew.lesser, 0), ("union", .union, 0), ("τ", .tau, 0), ("nil", .nil, 0), ("α", .alpha, 0),
   ("cons", .cons, 0), ("length", .length, 0), ("sum", .total, 0),
   ("dom", .dom, 1), ("ran", .ran, 1), ("Λ", .lam, 1), ("E", .E, 1),
   ("P", .P, 1), ("est", .est, 1), ("thin", .thin, 1),
   ("F", .map, 1), ("inits", .inits, 0), ("cat", .cat, 0),
   ("zip", .zip, 0), ("snoc", .snoc, 0),
   ("setify", .setify, 0), ("bagify", .bagify, 0), ("tic", .tic, 0),
   ("thinL", .thinL, 1), ("merge", .merge, 1), ("loop", .loop, 1),
   ("at", .index 0, 0)]

-- `at(i)` prints with its position, which no table row holds
def Op.sym : Op → String
  | .index i => s!"at({i})"
  | o => ((Op.table.find? (·.2.1 == o)).map (·.1)).getD "?"

/-- The builtin infix operators: `∩ ∪ − / \ ×`, one level with composition and the declared ones (`_⇒_`),
    left to right (§c). -/
inductive Bin
  | meet | join | diff | rdiv | ldiv | prod
  deriving Repr, BEq, Inhabited

def Bin.table : List (Char × Bin) :=
  [('∩', .meet), ('∪', .join), ('−', .diff), ('/', .rdiv), ('\\', .ldiv), ('×', .prod)]

def Bin.sym (o : Bin) : String := ((Bin.table.find? (·.2 == o)).map (·.1.toString)).getD "?"

/-- A side of a literal's row: a word, a pair of sides, or an array of sides, nested to any depth (§c). -/
inductive Tup
  | leaf (w : String)
  | pair (a b : Tup)
  | arr (ts : List Tup)
  deriving Repr, Inhabited

/-- The same kind of side, whatever is inside: the elaborator compares the parts position by position. -/
def Tup.like : Tup → Tup → Bool
  | .leaf _, .leaf _ | .pair .., .pair .. | .arr _, .arr _ => true
  | _, _ => false

/-- `t` as the parser reads it back: an array of two or more items juxtaposed, else bracketed; `item`: `t` stands
    next to others, so an array there is always bracketed. -/
def Tup.render (item : Bool) : Tup → String
  | .leaf w => w
  | .pair a b => s!"({a.render false}, {b.render false})"
  | .arr ts => let s := " ".intercalate (ts.map (Tup.render true)); if item || ts.length < 2 then s!"[{s}]" else s

def Tup.show (t : Tup) : String := t.render false

/-- A term of §c. `name` is a program's definition or parameter; `op` a builtin with its objects and arguments;
    `app` a program's operator applied. Composition is juxtaposition. -/
inductive Expr
  | name (p : Pos) (n : String)
  | op (p : Pos) (o : Op) (objs : List OExp) (args : List Expr)
  | app (p : Pos) (n : String) (args : List Expr)
  | comp (a b : Expr)
  | bin (p : Pos) (o : Bin) (a b : Expr)
  /-- `a n b`: the definition declared `_n_` (§c). -/
  | inf (p : Pos) (n : String) (a b : Expr)
  | conv (p : Pos) (a : Expr)
  | compl (p : Pos) (a : Expr)
  | pair (p : Pos) (a b : Expr)
  | junc (p : Pos) (a b : Expr)
  | fold (p : Pos) (e s : Expr)
  | lit (p : Pos) (ps : List (Tup × Tup))
  /-- `μX : φ` (`least`) or `νX : φ`: the least or the greatest `X` with `X = φ(X)`; the body reaches to the
      closing parenthesis or the end of the declaration. -/
  | fix (p : Pos) (least : Bool) (x : String) (body : Expr)
  deriving Repr, Inhabited

/-- The position a term starts at. -/
def Expr.pos : Expr → Pos
  | .name p _ | .op p .. | .app p .. | .bin p .. | .inf p .. | .conv p _ | .compl p _ | .pair p .. | .junc p .. | .fold p ..
  | .lit p _ | .fix p .. => p
  | .comp a _ => a.pos

/-- Each name of `σ` replaced by its term: a `where` item put in place in its body (§c). -/
partial def Expr.subst (σ : List (String × Expr)) : Expr → Expr
  | .name p n => (σ.lookup n).getD (.name p n)
  | .op p o os as => .op p o os (as.map (·.subst σ))
  | .app p n as => .app p n (as.map (·.subst σ))
  | .comp a b => .comp (a.subst σ) (b.subst σ)
  | .bin p o a b => .bin p o (a.subst σ) (b.subst σ)
  | .inf p n a b => .inf p n (a.subst σ) (b.subst σ)
  | .conv p a => .conv p (a.subst σ)
  | .compl p a => .compl p (a.subst σ)
  | .pair p a b => .pair p (a.subst σ) (b.subst σ)
  | .junc p a b => .junc p (a.subst σ) (b.subst σ)
  | .fold p a b => .fold p (a.subst σ) (b.subst σ)
  | .lit p ps => .lit p ps
  -- `x` is bound in the body, so an outer `x` is not replaced there
  | .fix p l x b => .fix p l x (b.subst (σ.filter (·.1 != x)))

/-- A body: a relation, or a test `e ⊑ f` (§e). -/
inductive Body
  | rel (e : Expr)
  | test (e f : Expr)
  deriving Repr, Inhabited

/-- A parameter and its declared type `S : A ⟶ B`, its objects possibly object variables (§e). Every parameter of
    a run program declares one (`none` is a parse that `run` refuses, naming the inferred type); a family given
    to it is lifted (§e). -/
structure Param where
  name : String
  ty : Option (OExp × OExp)
  deriving Repr, Inhabited

/-- An object declaration's right side: named elements, a signed number range `lo ≤ hi`, or a derived object. -/
inductive ObjDef
  | elems (ws : List String)
  | range (lo hi : Int)
  | alias (o : OExp)
  deriving Repr, Inhabited

inductive Decl
  | obj (p : Pos) (n : String) (d : ObjDef)
  /-- `ty`: the declared type `A ⟶ B`, required on a relation and absent on a test (§e). -/
  | defn (p : Pos) (n : String) (ps : List Param) (b : Body) (ty : Option (OExp × OExp))
  | print (p : Pos) (e : Expr)
  | check (p : Pos) (e f : Expr) (eq : Bool)
  deriving Repr, Inhabited

abbrev Program := List Decl

/-! ### Printing, in the syntax the parser reads: a composite on the right of an operator in parentheses -/

/-- `o` printed; `inner` parenthesises a product or sum, as an operand of `×`, `+`, `𝒫` needs. -/
def OExp.render (inner : Bool) : OExp → String
  | .name _ n | .var _ n => n
  | .prod a b => let s := s!"{a.render true}×{b.render true}"; if inner then s!"({s})" else s
  | .sum a b => let s := s!"{a.render true}+{b.render true}"; if inner then s!"({s})" else s
  | .pow a => s!"𝒫{a.render true}"
  | .list a => s!"[{a.render false}]"

def OExp.show (o : OExp) : String := o.render false

/-- The object variables of `o`, in order, each once. -/
def OExp.vars : OExp → List String
  | .var _ n => [n]
  | .name .. => []
  | .prod a b | .sum a b => (a.vars ++ b.vars).eraseDups
  | .pow a | .list a => a.vars

/-- A definition's head and type as `typesOf` prints it and the parser reads it back:
    `n(R : A ⟶ B, …) : C ⟶ D`, each type given as its text; a test has no type of its own (§e). -/
def sigText (n : String) (ps : List (String × Option String)) (ty : Option String) : String :=
  let h := if ps.isEmpty then n else
    n ++ "(" ++ ", ".intercalate (ps.map fun (q, t) => match t with | some t => s!"{q} : {t}" | none => q) ++ ")"
  match ty with | some t => s!"{h} : {t}" | none => h

def OExp.arrow (ty : OExp × OExp) : String := s!"{ty.1.show} ⟶ {ty.2.show}"

/-- A definition's declaration as written: `sigText` of its declared types. -/
def sigOf (n : String) (ps : List Param) (ty : Option (OExp × OExp)) : String :=
  sigText n (ps.map fun q => (q.name, q.ty.map OExp.arrow)) (ty.map OExp.arrow)

/-- The level a left operand prints at: `1` for a fixed point, whose body would read on past the operator. -/
def Expr.lhs : Expr → Nat
  | .fix .. => 1
  | _ => 0

/-- `e` printed at the level `l`,parenthesised as §c's one level needs: `0` anywhere or the left operand of a
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
  | .comp a b => let s := s!"{a.render a.lhs full} {b.render 1 full}"; if full || l ≥ 1 then s!"({s})" else s
  | .bin _ o a b => let s := s!"{a.render a.lhs full} {o.sym} {b.render 1 full}"; if full || l ≥ 1 then s!"({s})" else s
  | .inf _ n a b => let s := s!"{a.render a.lhs full} {n} {b.render 1 full}"; if full || l ≥ 1 then s!"({s})" else s
  | .conv _ a => s!"{a.render 2 full}°"
  | .compl _ a => let s := s!"∼{a.render 1 full}"; if l ≥ 2 then s!"({s})" else s
  | .pair _ a b => s!"⟨{a.render 0 full}, {b.render 0 full}⟩"
  | .junc _ a b => s!"[{a.render 0 full}, {b.render 0 full}]"
  | .fold _ a b => s!"⦇{a.render 0 full}, {b.render 0 full}⦈"
  | .lit _ ps => "{" ++ ", ".intercalate (ps.map fun (a, b) => (Tup.pair a b).show) ++ "}"
  | .fix _ least x b =>
    let s := s!"{if least then "μ" else "ν"}{x} : {b.render 0 full}"; if full || l ≥ 1 then s!"({s})" else s

def Expr.show (e : Expr) : String := e.render 0

end LeetQ.Rel.Lang
