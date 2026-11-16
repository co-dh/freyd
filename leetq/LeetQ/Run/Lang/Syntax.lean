import Lean
import QLean.Kernel.Elementwise
import LeetQ.Run.CRelDef
import LeetQ.Run.CRelArithDef
import LeetQ.Run.CRelRelDef
import LeetQ.Run.CRelListDef
import LeetQ.Run.CRelFoldDef
import LeetQ.Run.CRelPowerDef
import LeetQ.Run.CRelLoopDef

/-! The Rel language's surface syntax (`doc/rel-lang-design.md` §c, §h): objects, terms, declarations, each node
    with its source line and column. The builtin operators are one table, `Op.table`, read by the parser (symbol,
    arity), the elaborator (typing, lifted row) and the expander (the `Gen` op), each by the `Op` constructor; a
    builtin that takes no relation is a row of `prims`, its type read off its `CRel` constant (`prim%`). -/

namespace LeetQ.Rel.Lang

deriving instance DecidableEq for LeetQ.Rel.Obj

/-- A source position: line and column, both from 1. -/
structure Pos where
  line : Nat := 0
  col : Nat := 0
  deriving Repr, BEq, Inhabited, Lean.ToExpr

instance : ToString Pos := ⟨fun p => s!"line {p.line}, col {p.col}"⟩

/-- A front-end error: where, and what was found against what was expected. -/
structure Err where
  pos : Pos
  msg : String
  deriving Repr, Inhabited

/-- Line 0 is no place in the program: an error of the prelude's own text says where in its message. -/
instance : ToString Err := ⟨fun e => if e.pos.line == 0 then e.msg else s!"{e.pos}: {e.msg}"⟩

/-- An error raised re-reading the program `n` a program imports: where in `n` it is. -/
def Err.inProg (n : String) (e : Err) : Err := ⟨default, s!"in the program `{n}`, {e.pos}: {e.msg}"⟩

/-- A definition or object of a program, as the registry records it (`Expand.relRegistry`) and the resolver gives
    it: its constant `n.x`, its arity, whether it is an infix operator `_x_`, an object, a theorem. -/
structure Ext where
  const : Lean.Name
  arity : Nat := 0
  isInfix : Bool := false
  obj : Bool := false
  thm : Bool := false
  deriving Repr, Inhabited

/-- What a written name (`AC3`, `csp.AC3`, `≠`) resolves to in Lean's scope (the current namespace and `open`s),
    kept to the registry: one entry; or an error, `inScope` when the name is a Rel name all the same (several
    entries: ambiguous), not when Lean gives only constants that are no Rel definition; or nothing. -/
inductive Found
  | ext (e : Ext)
  | bad (inScope : Bool) (msg : String)
  | none
  deriving Inhabited

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

/-! ### The builtins that take no relation: one row each, typed by their `CRel` constant -/

section Prim
open Lean Elab Term Meta LeetQ.Rel.Alg

/-- The object `e` of a `CRel` constant's type as written: an `Obj` binder the variable of its name, `.long` the
    variable `ℕ` (each declared number object is stored as `.long`, F6, so `ℕ` is an object variable too). -/
partial def objSyn (c : Name) (e : Lean.Expr) : MetaM Term := do
  let e ← whnfR e
  if let .fvar f := e then return ← `(OExp.var {} $(quote (← f.getUserName).toString))
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Obj.prod, #[a, b] => `(OExp.prod $(← objSyn c a) $(← objSyn c b))
  | some ``Obj.sum, #[a, b] => `(OExp.sum $(← objSyn c a) $(← objSyn c b))
  | some ``Obj.arr, #[a] => `(OExp.list $(← objSyn c a))
  | some ``Obj.atom, #[t] =>
    if t.isConstOf ``QLean.QAtomicType.long then `(OExp.var {} "ℕ")
    else throwError "prim%: `{c}` names the atom `{t}`, which no declared object is stored as"
  | _, _ => throwError "prim%: `{c}` has the object `{e}`, not built by `Obj`'s constructors"

/-- A binder of a `CRel` constant that is no relation: an object or a size, solved by unification (`Expand.primE`). -/
def objOrSize (t : Lean.Expr) : MetaM Bool := return (← whnfR t).isConstOf ``Obj || (← whnfR t).isConstOf ``USize

/-- A binder of a `CRel` constant as a relation parameter `X ⟶ Y` and its form (`Form`'s first part): `CRel X Y` a
    relation run on the keys in demand; `CRel S S → CRel S T` one run on the keys `S` a round gives it, except that
    with `S = T = B×B` it is the pair test `τ(Q)` of an order `Q : B ⟶ B`, as every kernel taking an order takes it
    (§a). None: the binder is no relation. -/
def paramSyn (c : Name) (t : Lean.Expr) : MetaM (Option Term) := do
  let t ← whnfR t
  if let some (x, y) := t.app2? ``CRel then return some (← `((($(← objSyn c x), $(← objSyn c y)), some false)))
  let .forallE _ dom r _ := t | return none
  let (some (s, s'), some (s'', u)) := ((← whnfR dom).app2? ``CRel, (← whnfR r).app2? ``CRel) | return none
  unless !r.hasLooseBVars && s == s' && s == s'' do return none
  if let (true, some (b, b')) := (u == s, s.app2? ``Obj.prod) then
    if b == b' then return some (← `((($(← objSyn c b), $(← objSyn c b)), some true)))
  return some (← `((($(← objSyn c s), $(← objSyn c u)), some false)))

/-- `prim% c`: the `CRel` constant `c`, its relation parameters (`paramSyn`) and its type `A ⟶ B` as `OExp`s:
    `c : Vals A n → CRel A B` reads its source's values, `c : CRel K A → CRel K B` composes after the keys `K`
    (`Gen.ofVals`, `Gen.after`, and their forms with parameters); every other binder an object or a size. -/
elab "prim% " i:ident : term => do
  let c ← realizeGlobalConstNoOverloadWithInfo i
  let (ps, src, tgt) ← forallTelescope (← getConstInfo c).type fun xs r => do
    let some x := xs.back? | throwError "prim%: `{c}` takes no argument"
    let mut ps : Array Term := #[]
    for y in xs.pop do
      let t ← inferType y
      if ← objOrSize t then continue
      let some p ← paramSyn c t
        | throwError "prim%: `{c}` has the parameter `{y} : {t}`; a builtin's binders are objects, sizes and relations"
      ps := ps.push p
    let some (_, b) := r.app2? ``CRel | throwError "prim%: `{c}` is `{r}`, not a `CRel`"
    match (← inferType x).getAppFn.constName?, (← inferType x).getAppArgs with
    | some ``CRel, #[_, a] | some ``Vals, #[a, _] => pure (ps, ← objSyn c a, ← objSyn c b)
    | _, _ => throwError "prim%: `{c}` takes `{x} : {← inferType x}`, neither the values `Vals A n` nor a `CRel K A`"
  elabTerm (← `((($(quote c) : Lean.Name), ([$ps,*] : List ((OExp × OExp) × Option Bool)), ($src : OExp),
    ($tgt : OExp)))) none

end Prim

/-- A builtin run on the keys in demand: `sym` as written (`written`), or the prelude's definition `sym` run as it
    (`prelude`, `Expand.useDef`), or neither (a converse only, `convTm`); `sig` its `CRel` constant, that constant's
    relation parameters and type (`prim%`), which the elaborator instantiates and the expander applies; `conv` the
    row of its converse; `aop` its AOP reading (`Calc.builtins`) or why it has none; `mono`: it reads its parameters
    monotonically (§e's fixed points); `sound` its `GenSpec` lemma, named unchecked as `aop` is (`RelRep` checks). -/
structure Prim where
  sym : String
  sig : Lean.Name × List ((OExp × OExp) × Option Bool) × OExp × OExp
  conv : Option String := none
  written : Bool := true
  prelude : Bool := false
  aop : Except String Lean.Name := .error "it is not written"
  mono : Bool := true
  sound : Option Lean.Name := none
  deriving Inhabited

def consRow : Prim :=
  { sym := "cons", sig := prim% CRel.cons, sound := `LeetQ.Rel.Lang.Gen.cons_sound,
    conv := "uncons", aop := .ok `Freyd.Alg.RelSet.ListRel.cons }

def memRow : Prim :=
  { sym := "∋", sig := prim% CRel.mem, aop := .ok `Freyd.Alg.PowerAllegory.eps, sound := `LeetQ.Rel.Lang.Gen.mem_sound }

/-- Every builtin run as a kernel on the keys in demand: adding one is adding its row. -/
def prims : List Prim :=
  [{ sym := "τ", sig := prim% CRel.τ, sound := `LeetQ.Rel.Lang.Gen.τ_sound,
     aop := .ok `Freyd.Alg.singletonMap }, consRow, memRow,
   -- `filter(p)`, `takewhile(p)` given one relation run as their mask forms (`rep_filterC`, `rep_takewhileC`)
   { sym := "filter", sig := prim% CRel.filter, prelude := true },
   { sym := "takewhile", sig := prim% CRel.takewhile, prelude := true },
   { sym := "thinL", sig := prim% CRel.thinLOn, mono := false, aop := .ok `Freyd.Alg.RelSet.ListRel.thinL },
   { sym := "merge", sig := prim% CRel.mergeOn, sound := `LeetQ.Rel.Lang.Gen.merge_sound,
     mono := false, aop := .ok `Freyd.Alg.RelSet.ListRel.merge },
   { sym := "loop", sig := prim% CRel.loopOn, aop := .error "AOP declares no iteration to a fixed point from the left" },
   { sym := "uncons", sig := prim% CRel.uncons, sound := `LeetQ.Rel.Lang.Gen.uncons_sound,
     conv := "cons", written := false },
   { sym := "length", sig := prim% CRel.length, sound := `LeetQ.Rel.Lang.Gen.length_sound,
     aop := .ok `Freyd.Alg.RelSet.ListRel.length },
   { sym := "sum", sig := prim% CRel.Arr.sum, sound := `LeetQ.Rel.Lang.Gen.sum_sound,
     aop := .ok `Freyd.Alg.RelSet.ListRel.sum },
   { sym := "inits", sig := prim% CRel.inits, sound := `LeetQ.Rel.Lang.Gen.inits_sound,
     aop := .ok `Freyd.Alg.RelSet.ListRel.initsR },
   -- the prelude's folds run as their slice forms (`rep_tailsC`, `rep_prefixC`, `rep_suffixC`, `rep_concatC`)
   { sym := "tails", sig := prim% CRel.tails, sound := `LeetQ.Rel.Lang.Gen.tails_sound, prelude := true },
   { sym := "prefix", sig := prim% CRel.prefix, sound := `LeetQ.Rel.Lang.Gen.prefix_sound, prelude := true },
   { sym := "suffix", sig := prim% CRel.suffix, sound := `LeetQ.Rel.Lang.Gen.suffix_sound, prelude := true },
   { sym := "concat", sig := prim% CRel.concat, sound := `LeetQ.Rel.Lang.Gen.concat_sound, prelude := true },
   { sym := "cat", sig := prim% CRel.cat, sound := `LeetQ.Rel.Lang.Gen.cat_sound,
     conv := "uncat", aop := .ok `Freyd.Alg.RelSet.ListRel.cat },
   { sym := "uncat", sig := prim% CRel.uncat, sound := `LeetQ.Rel.Lang.Gen.uncat_sound,
     conv := "cat", written := false },
   { sym := "zip", sig := prim% CRel.zip, sound := `LeetQ.Rel.Lang.Gen.zip_sound,
     aop := .ok `Freyd.Alg.RelSet.Pointfree.zip },
   { sym := "snoc", sig := prim% CRel.snoc, sound := `LeetQ.Rel.Lang.Gen.snoc_sound, conv := "unsnoc",
     aop := .error "AOP's `snoc` is on snoc lists (`SL.snoc`), not on the cons lists `[α]` reads as" },
   { sym := "unsnoc", sig := prim% CRel.unsnoc, sound := `LeetQ.Rel.Lang.Gen.unsnoc_sound,
     conv := "snoc", written := false },
   { sym := "setify", sig := prim% CRel.setify, aop := .ok `Freyd.Alg.RelSet.ListRel.setify },
   { sym := "distinct", sig := prim% CRel.distinct, sound := `LeetQ.Rel.Lang.Gen.distinct_sound,
     aop := .error "AOP declares no first-occurrence removal of repeats from a list" },
   -- `asc` sorts each array by `Obj.lt` (`rep_asc`): B&dM's `bagify` with a bag kept as its ascending array
   { sym := "asc", sig := prim% CRel.asc,
     aop := .error "AOP's sorts take their order as a relation (`ISort.sortSpec R`); `asc` sorts by q's" },
   { sym := "tic", sig := prim% CRel.tic, sound := `LeetQ.Rel.Lang.Gen.tic_sound,
     aop := .error "AOP declares no non-empty prefixes of `a::xs`" }]

def Prim.find? (s : String) : Option Prim := prims.find? (·.sym == s)

/-- The builtin operators of §b. A constant (arity 0) may take its objects, `⊤(A,B)`; the others take relations.
    `arith k` is the qlean kernel's integral value verb `k` on pairs of numbers (`Alg.arith`): one constructor, so
    every verb is typed, lifted and run by one path; `prim s` the row `s` of `prims`. -/
inductive Op
  | id | zero | top | outl | outr | inl | inr | leq | lt | succ | arith (k : UInt8)
  | nil | alpha | prim (s : String)
  | dom | ran | lam | E | P | est | thin | map
  /-- `refold(c, S)`: an unfold by `c : A ⟶ G(A)` then a fold by `S : G(B) ⟶ B`, `μX : c G(X) S`; `fold` is a
      name programs define (Party), so the builtin is `refold`. -/
  | refold
  /-- `at(i)`, the element at position `i` from `0`; `i` a number literal, read by `Embed.atomOf`. -/
  | index (i : Nat)
  deriving Repr, BEq, Inhabited

/-- The one table of builtins: symbol and arity. A program may not define or take as a parameter a name
    in it (§c). -/
def Op.table : List (String × Op × Nat) :=
  [("𝟙", .id, 0), ("𝟘", .zero, 0), ("⊤", .top, 0), ("π₁", .outl, 0),
   ("π₂", .outr, 0), ("inl", .inl, 0), ("inr", .inr, 0), ("≤", .leq, 0), ("<", .lt, 0), ("succ", .succ, 0),
   ("plus", .arith QLean.Kernel.Ew.add, 0), ("times", .arith QLean.Kernel.Ew.mul, 0),
   ("minus", .arith QLean.Kernel.Ew.sub, 0), ("div", .arith QLean.Kernel.Ew.idiv, 0),
   ("mod", .arith QLean.Kernel.Ew.imod, 0), ("max", .arith QLean.Kernel.Ew.greater, 0),
   ("min", .arith QLean.Kernel.Ew.lesser, 0), ("nil", .nil, 0), ("α", .alpha, 0),
   ("dom", .dom, 1), ("ran", .ran, 1), ("Λ", .lam, 1), ("E", .E, 1),
   ("P", .P, 1), ("est", .est, 1), ("thin", .thin, 1), ("F", .map, 1),
   ("refold", .refold, 2),
   ("at", .index 0, 0)] ++
  (prims.filter fun r => r.written && !r.prelude).map fun r => (r.sym, .prim r.sym, r.sig.2.1.length)

-- `at(i)` prints with its position, which no table row holds
def Op.sym : Op → String
  | .index i => s!"at({i})"
  | .prim s => s
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

/-- Every name `e` mentions, bound or free, operators applied included: a variable not among them captures nothing
    in `e`. -/
partial def Expr.names : Expr → List String
  | .name _ n => [n]
  | .op _ _ _ as => as.flatMap (·.names)
  | .app _ n as => n :: as.flatMap (·.names)
  | .comp a b | .bin _ _ a b | .pair _ a b | .junc _ a b | .fold _ a b => a.names ++ b.names
  | .inf _ n a b => n :: (a.names ++ b.names)
  | .conv _ a | .compl _ a => a.names
  | .lit .. => []
  | .fix _ _ x b => x :: b.names

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

/-- A `calc` step's reason (`doc/rel-mss-proof-design.md` §3): `:= n(R, …)` cites the theorem `n` at the
    arguments `args` (none when it has no parameters), `:= ≜ n` unfolds or folds back the definition `n`. The
    cited theorem as the resolver found it: `c`, the registry's constant, or none for the program's own `n`. -/
inductive Why
  | thm (p : Pos) (n : String) (c : Option Lean.Name) (args : List Expr)
  | unfold (p : Pos) (n : String)
  deriving Repr, Inhabited

inductive Decl
  | obj (p : Pos) (n : String) (d : ObjDef)
  /-- `ty`: the declared type `A ⟶ B`, required on a relation and absent on a test (§e). -/
  | defn (p : Pos) (n : String) (ps : List Param) (b : Body) (ty : Option (OExp × OExp))
  | print (p : Pos) (e : Expr)
  | check (p : Pos) (e f : Expr) (eq : Bool)
  /-- `theorem n(ps) on A : e = f := calc` (`⊑` when `eq` is false), each step `_ = x := why` with its line; no
      steps: the proof is owed to Lean. `on A`: each step is also evaluated as `check A x = A y` (§3). -/
  | «theorem» (p : Pos) (n : String) (ps : List Param) (e f : Expr) (eq : Bool) (on : Option Expr)
      -- each hypothesis after `if`: `e = f` or `e ⊑ f` (`some (eq, f)`), or a test applied, `t(R)` (`none`)
      (hyps : List (Expr × Option (Bool × Expr))) (steps : List (Pos × Bool × Expr × Why))
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

/-- The object variables of a row's parameters and type, in order, each once. -/
def Prim.vars (r : Prim) : List String :=
  ((r.sig.2.1.flatMap fun ((x, y), _) => x.vars ++ y.vars) ++ r.sig.2.2.1.vars ++ r.sig.2.2.2.vars).eraseDups

/-- The row's name as a leaf of an error: `sym`, with `( )` when it takes relations. -/
def Prim.leaf (r : Prim) : String := if r.sig.2.1.isEmpty then r.sym else s!"{r.sym}( )"

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
