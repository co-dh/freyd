import LeetQ.Rel.Algebra
import LeetQ.Rel.Lang.Syntax

/-! The elaborator of the Rel language (`doc/rel-lang-design.md` §a, §e): names resolved, every term typed
    `A ⟶ B` over the declared objects, definitions expanded, a body whose declared parameter is given a family
    lifted by the rows of §e. Two passes: `elabE` types the surface term into `Pre` with object variables,
    unified as it goes; `build` reads the solved objects and gives `Tm`, the core term, indexed by its source,
    target and whether it runs on demand, so `Eval` has no error path. -/

namespace LeetQ.Rel.Lang

open LeetQ.Rel LeetQ.Rel.Alg

deriving instance DecidableEq for LeetQ.Rel.Obj

/-! ### The core term -/

/-- A core term `A ⟶ B` over `Alg`. `d` says it runs on DEMAND (§a): its value is read only at the keys the
    coreflexive its left context supplies. A term with `d = false` needs no keys: a closed term. -/
inductive Tm : Obj → Obj → Bool → Type where
  | val {A B : Obj} (R : Rel A B) : Tm A B false
  | uni {A : Obj} {m : Nat} (U : Vals A m) : Tm A A false
  | zero {A B : Obj} : Tm A B false
  | id {A : Obj} : Tm A A true
  /-- `⊤` onto the values of the closed coreflexive `V`. -/
  | top {A B : Obj} (V : Tm B B false) : Tm A B true
  | mem {B : Obj} : Tm (.arr B) B true
  | outl {A B : Obj} : Tm (.prod A B) A true
  | outr {A B : Obj} : Tm (.prod A B) B true
  | inl {A B : Obj} : Tm A (.sum A B) true
  | inr {A B : Obj} : Tm B (.sum A B) true
  | comp {A B C : Obj} {d e : Bool} (R : Tm A B d) (S : Tm B C e) : Tm A C d
  | conv {A B : Obj} (R : Tm A B false) : Tm B A false
  | meet {A B : Obj} {d e : Bool} (R : Tm A B d) (S : Tm A B e) : Tm A B (d || e)
  | join {A B : Obj} {d e : Bool} (R : Tm A B d) (S : Tm A B e) : Tm A B (d || e)
  | diff {A B : Obj} {d e : Bool} (R : Tm A B d) (S : Tm A B e) : Tm A B (d || e)
  | dom {A B : Obj} {d : Bool} (R : Tm A B d) : Tm A A d
  | ran {A B : Obj} (R : Tm A B false) : Tm B B false
  | ldiv {A B C : Obj} (R : Tm A B false) (S : Tm A C false) (UB : Tm B B false) (UC : Tm C C false) : Tm B C false
  | rdiv {A B C : Obj} (R : Tm A C false) (S : Tm B C false) (UA : Tm A A false) (UB : Tm B B false) : Tm A B false
  | pair {A B C : Obj} {d e : Bool} (R : Tm A B d) (S : Tm A C e) : Tm A (.prod B C) (d || e)
  | prod {A B C D : Obj} (R : Tm A B false) (S : Tm C D false) : Tm (.prod A C) (.prod B D) false
  | junc {A B C : Obj} (R : Tm A C false) (S : Tm B C false) : Tm (.sum A B) C false
  | lam {A B : Obj} {d : Bool} (R : Tm A B d) : Tm A (.arr B) d
  | E {A B : Obj} {d : Bool} (R : Tm A B d) : Tm (.arr A) (.arr B) true
  | map {A B : Obj} {d : Bool} (R : Tm A B d) : Tm (.arr A) (.arr B) true
  /-- An operator that takes an order `Q : B ⟶ B` (or a coreflexive `p`) holds it as its pair test
      `τ(Q) : B×B ⟶ B×B` (§a), run on demand on the pairs the operator compares. -/
  | est {B : Obj} (Q : Tm (.prod B B) (.prod B B) true) : Tm (.arr B) B true
  | thin {B : Obj} (Q : Tm (.prod B B) (.prod B B) true) : Tm (.arr B) (.arr B) true
  | union {A : Obj} : Tm (.arr (.arr A)) (.arr A) true
  | tau {A : Obj} : Tm A (.arr A) true
  | nil {A B : Obj} : Tm A (.arr B) true
  | cons {B : Obj} : Tm (.prod B (.arr B)) (.arr B) true
  | uncons {B : Obj} : Tm (.arr B) (.prod B (.arr B)) true
  | length {B : Obj} : Tm (.arr B) .long true
  | total : Tm (.arr .long) .long true
  | inits {B : Obj} : Tm (.arr B) (.arr (.arr B)) true
  | cat {B : Obj} : Tm (.prod (.arr B) (.arr B)) (.arr B) true
  | uncat {B : Obj} : Tm (.arr B) (.prod (.arr B) (.arr B)) true
  | zip {A B : Obj} : Tm (.prod (.arr A) (.arr B)) (.arr (.prod A B)) true
  | snoc {B : Obj} : Tm (.prod (.arr B) B) (.arr B) true
  | unsnoc {B : Obj} : Tm (.arr B) (.prod (.arr B) B) true
  /-- The prelude's `perm`, kept as its own converse (`convTm`): the one converse rule the language has for a
      definition, because `perm° = perm` is a theorem it cannot derive from the fold `perm` is. -/
  | own {A : Obj} {d : Bool} (R : Tm A A d) : Tm A A d
  | setify {B : Obj} : Tm (.arr B) (.arr B) true
  | bagify {B : Obj} : Tm (.arr B) (.arr B) true
  | tic {B : Obj} : Tm (.prod B (.arr B)) (.arr (.arr B)) true
  | thinL {B : Obj} (Q : Tm (.prod B B) (.prod B B) true) : Tm (.arr B) (.arr B) true
  | merge {B : Obj} (Q : Tm (.prod B B) (.prod B B) true) : Tm (.prod (.arr B) (.arr B)) (.arr B) true
  /-- `loop(F)` on the pairs (state, array) in demand, `F` run on the pairs (state, element) each round meets. -/
  | loop {X Y : Obj} {d : Bool} (F : Tm (.prod X Y) X d) : Tm (.prod X (.arr Y)) X true
  /-- `succ`, the kernel's value verb `k` (`plus`, `times`, …), `≤`, `<` on the declared number universe `U`. -/
  | succ {m : Nat} (U : Arr .long m) : Tm .long .long true
  | arith {m : Nat} (k : UInt8) (U : Arr .long m) : Tm (.prod .long .long) .long true
  | leq {m : Nat} (U : Arr .long m) : Tm .long .long false
  | lt {m : Nat} (U : Arr .long m) : Tm .long .long false
  /-- `⦇e,S⦈` on the arrays in demand, `S` run on the pairs each round meets. -/
  | fold {E V : Obj} {d : Bool} (e : Tm V V false) (S : Tm (.prod E V) V d) : Tm (.arr E) V true
  /-- `R`, whose identity among the program's sub-terms is `k` (`Eval.hoist`): equal sub-terms have one
      identity, and one evaluation runs each identity once per demand. -/
  | share {A B : Obj} {d : Bool} (k : Nat) (R : Tm A B d) : Tm A B d
  /-- `⦇e,S⦈` given a family (§e), on the pairs (key, array) in demand: one fold with carrier `I×V`, seeded at
      each key by the fibre of `e` there, its step `S` given `(x,(i,v))` and carrying the key `i`. -/
  | foldI {I E V : Obj} {d d' : Bool} (e : Tm I (.prod V V) d) (S : Tm (.prod E (.prod I V)) (.prod I V) d') :
      Tm (.prod I (.arr E)) V true
  /-- `Rᴵ`, the family `R : I ⟶ A×B` as one relation of the key and the source, on the pairs (key, source) in
      demand: `R` at their keys, each row `(i,(a,b))` re-keyed as `((i,a),b)`, then joined with the pairs. -/
  | flat {I A B : Obj} {d : Bool} (R : Tm I (.prod A B) d) : Tm (.prod I A) B true

/-- A built term with its objects. -/
abbrev Res := (A : Obj) × (B : Obj) × (d : Bool) × Tm A B d

/-! ### Objects as the program names them -/

/-- An object up to its declared names: `X` and `N` are both `long` and still different objects. `𝒫A` and
    `[A]` are both `arr`. `mv` is an object variable of the inference. -/
inductive OTy
  | base (n : String)
  | prod (a b : OTy)
  | sum (a b : OTy)
  | arr (a : OTy)
  | mv (k : Nat)
  deriving Repr, BEq, Inhabited

def OTy.render (inner : Bool) : OTy → String
  | .base n => n
  | .prod a b => let s := s!"{a.render true}×{b.render true}"; if inner then s!"({s})" else s
  | .sum a b => let s := s!"{a.render true}+{b.render true}"; if inner then s!"({s})" else s
  -- `𝒫A` and `[A]` are one object, an array; printed as the array the interpreter holds
  | .arr a => s!"[{a.render false}]"
  | .mv k => s!"?{k}"

instance : ToString OTy := ⟨OTy.render false⟩

/-- A declared object: what it stands for, and, for a base object, its elements and universe. -/
structure ObjInfo where
  ty : OTy
  elems : List String := []
  range : Option (Int × Int) := none
  uni : Option ((m : Nat) × Arr .long m) := none

abbrev Objs := List (String × ObjInfo)

/-- The universe of an object, when every base object in it has one (§a): `cross` of a product's, the two
    sides of a sum's; an `arr` has none. -/
def uniOf (objs : Objs) : OTy → Option ((A : Obj) × (m : Nat) × Vals A m)
  | .base n => do let ⟨m, U⟩ ← (← objs.lookup n).uni; pure ⟨.long, m, U⟩
  | .prod a b => do
    let ⟨_, _, Ua⟩ ← uniOf objs a; let ⟨_, _, Ub⟩ ← uniOf objs b
    let k := (Alg.prod (idU Ua) (idU Ub)).key
    pure ⟨_, _, k⟩
  | .sum a b => do let ⟨_, _, Ua⟩ ← uniOf objs a; let ⟨_, _, Ub⟩ ← uniOf objs b; pure ⟨_, _, sumVals Ua Ub⟩
  | _ => none

/-! ### The typed surface term -/

/-- A term typed but not yet built: the core operators, object variables on the constants. `close` marks a
    place whose term is read whole — no left context, or an operator that is not local (§a): its term runs on
    its source's universe when it needs keys, `why` naming that operator in the error when there is none.
    `tm` is a built term, a definition's. -/
inductive Pre
  | tm (r : Res)
  | zero (a b : OTy)
  | id (a : OTy)
  | top (p : Pos) (a b : OTy) (tgt : Option Pre)
  | mem (b : OTy)
  | outl (a b : OTy)
  | outr (a b : OTy)
  | inl (a b : OTy)
  | inr (a b : OTy)
  | comp (p q : Pre)
  | conv (p : Pre)
  | meet (p q : Pre)
  | join (p q : Pre)
  | diff (p q : Pre)
  | dom (p : Pre)
  | ran (p : Pre)
  | ldiv (pos : Pos) (p q : Pre) (b c : OTy)
  | rdiv (pos : Pos) (p q : Pre) (a b : OTy)
  | pair (p q : Pre)
  | prod (p q : Pre)
  | junc (p q : Pre)
  | lam (p : Pre)
  | E (p : Pre)
  | map (p : Pre)
  | est (p : Pre)
  | thin (p : Pre)
  | union (a : OTy)
  | tau (a : OTy)
  | nil (a b : OTy)
  | cons (b : OTy)
  | uncons (b : OTy)
  | length (b n : OTy)
  | total (n : OTy)
  | inits (b : OTy)
  | cat (b : OTy)
  | uncat (b : OTy)
  | zip (a b : OTy)
  | snoc (b : OTy)
  | unsnoc (b : OTy)
  | own (p : Pre)
  | setify (b : OTy)
  | bagify (b : OTy)
  | tic (b : OTy)
  | thinL (p : Pre)
  | merge (p : Pre)
  | loop (p : Pre)
  | succ (pos : Pos) (n : OTy)
  | arith (pos : Pos) (k : UInt8) (n : OTy)
  | leq (pos : Pos) (n : OTy)
  | lt (pos : Pos) (n : OTy)
  | fold (e s : Pre)
  | foldI (e s : Pre)
  | flat (p : Pre)
  | lit (pos : Pos) (a b : OTy) (ps : List (Tup × Tup))
  | close (pos : Pos) (p : Pre) (a : OTy) (why : String)

instance : Inhabited Pre := ⟨.id (.base "")⟩

/-- `x` with every position `p`: a prelude body at its use, so an error `build` raises in it is at the use (§c). -/
def Pre.at (p : Pos) : Pre → Pre
  | .top _ a b t => .top p a b (t.attach.map fun ⟨x, _⟩ => x.at p)
  | .comp x y => .comp (x.at p) (y.at p)
  | .conv x => .conv (x.at p)
  | .meet x y => .meet (x.at p) (y.at p)
  | .join x y => .join (x.at p) (y.at p)
  | .diff x y => .diff (x.at p) (y.at p)
  | .dom x => .dom (x.at p)
  | .ran x => .ran (x.at p)
  | .ldiv _ x y b c => .ldiv p (x.at p) (y.at p) b c
  | .rdiv _ x y a b => .rdiv p (x.at p) (y.at p) a b
  | .pair x y => .pair (x.at p) (y.at p)
  | .prod x y => .prod (x.at p) (y.at p)
  | .junc x y => .junc (x.at p) (y.at p)
  | .lam x => .lam (x.at p)
  | .E x => .E (x.at p)
  | .map x => .map (x.at p)
  | .est x => .est (x.at p)
  | .thin x => .thin (x.at p)
  | .own x => .own (x.at p)
  | .thinL x => .thinL (x.at p)
  | .merge x => .merge (x.at p)
  | .loop x => .loop (x.at p)
  | .succ _ n => .succ p n
  | .arith _ k n => .arith p k n
  | .leq _ n => .leq p n
  | .lt _ n => .lt p n
  | .fold e s => .fold (e.at p) (s.at p)
  | .foldI e s => .foldI (e.at p) (s.at p)
  | .flat x => .flat (x.at p)
  | .lit _ a b ps => .lit p a b ps
  | .close _ x a why => .close p (x.at p) a why
  -- no position and no part
  | x@(.tm _) | x@(.zero ..) | x@(.id _) | x@(.mem _) | x@(.outl ..) | x@(.outr ..) | x@(.inl ..) | x@(.inr ..)
  | x@(.union _) | x@(.tau _) | x@(.nil ..) | x@(.cons _) | x@(.uncons _) | x@(.length ..) | x@(.total _)
  | x@(.inits _) | x@(.cat _) | x@(.uncat _) | x@(.zip ..) | x@(.snoc _) | x@(.unsnoc _) | x@(.setify _)
  | x@(.bagify _) | x@(.tic _) => x

/-- The `why` of a top-level term's `close`. -/
def noLeft : String := "the term here needs keys and has no left context"

/-! ### Object variables -/

structure St where
  ms : Array (Option OTy) := #[]

abbrev M := StateT St (Except Err)

def fresh : M OTy := modifyGet fun s => (.mv s.ms.size, { s with ms := s.ms.push none })

/-- `o` with every solved variable replaced; `fuel` bounds the chain, which the occurs check keeps acyclic. -/
def zonkF (s : St) : Nat → OTy → OTy
  | 0, o => o
  | f + 1, .mv k => match s.ms[k]? with | some (some o) => zonkF s f o | _ => .mv k
  | f + 1, .prod a b => .prod (zonkF s (f + 1) a) (zonkF s (f + 1) b)
  | f + 1, .sum a b => .sum (zonkF s (f + 1) a) (zonkF s (f + 1) b)
  | f + 1, .arr a => .arr (zonkF s (f + 1) a)
  | _, o => o
termination_by f o => (f, sizeOf o)

def zonk (s : St) (o : OTy) : OTy := zonkF s (s.ms.size + 1) o

def OTy.size : OTy → Nat
  | .prod a b | .sum a b => a.size + b.size + 1
  | .arr a => a.size + 1
  | _ => 1

def occurs (k : Nat) : OTy → Bool
  | .mv j => j == k
  | .prod a b | .sum a b => occurs k a || occurs k b
  | .arr a => occurs k a
  | .base _ => false

/-- Unify `x` (found) with `y` (expected); the error names both as the program wrote them. -/
def unify (p : Pos) (what : String) (x y : OTy) : M Unit := do
  let s ← get
  let fx := zonk s x; let fy := zonk s y
  let rec go : Nat → OTy → OTy → M Unit
    | 0, _, _ => throw ⟨p, s!"{what}: the objects are too deep to compare"⟩
    | f + 1, a, b => do
      let s ← get
      match zonk s a, zonk s b with
      | .mv i, .mv j => if i == j then pure () else set { s with ms := s.ms.set! i (some (.mv j)) }
      | .mv i, t | t, .mv i =>
        if occurs i t then throw ⟨p, s!"{what}: found {fx}, expected {fy}: an object containing itself"⟩
        else set { s with ms := s.ms.set! i (some t) }
      | .base m, .base n => if m == n then pure () else throw ⟨p, s!"{what}: found {fx}, expected {fy}"⟩
      | .prod a b, .prod c d | .sum a b, .sum c d => do go f a c; go f b d
      | .arr a, .arr c => go f a c
      | _, _ => throw ⟨p, s!"{what}: found {fx}, expected {fy}"⟩
  go (s.ms.size + fx.size + fy.size + 1) fx fy

/-! ### Elaboration: environments and the lifted rows of §e -/

/-- An elaborated argument or result: one relation `s ⟶ t`, or a family `i ⟶ a×b` read as its fibres `a ⟶ b`. -/
inductive Arg
  | rel (p : Pre) (s t : OTy)
  | fam (p : Pre) (i a b : OTy)

instance : Inhabited Arg := ⟨.rel default default default⟩

/-- A definition: its arity, and its expansion at given arguments (§e: substituted, lifted when a declared
    parameter is given a family). -/
structure Def where
  arity : Nat
  apply : Pos → List Arg → M Arg

structure Env where
  objs : Objs := []
  defs : List (String × Def) := []
  params : List (String × Arg) := []

/-- `o` as the program wrote it, resolved: an alias stands for its definition, a variable for its object in `vs`,
    one use's instantiation (§e). -/
def oty (env : Env) (vs : List (String × OTy) := []) : OExp → M OTy
  | .name p n => match env.objs.lookup n with
    | some i => pure i.ty
    | none => throw ⟨p, s!"unknown object '{n}'"⟩
  | .var p n => match vs.lookup n with
    | some o => pure o
    | none => throw ⟨p, s!"the object variable '{n}' is not instantiated here"⟩
  | .prod a b => return .prod (← oty env vs a) (← oty env vs b)
  | .sum a b => return .sum (← oty env vs a) (← oty env vs b)
  | .pow a | .list a => return .arr (← oty env vs a)

section Rows

open Pre

variable (I : OTy) (p : Pos)

/-- A closed `C : a ⟶ b` as a family: `D⊤⟨𝟙,C⟩`, `⊤ : I ⟶ a` onto `dom(C)`; `⊤` itself is `D⊤`, `𝟙` is
    `D⊤⟨𝟙,𝟙⟩` (§e). -/
def liftConst (C : Pre) (a b : OTy) : Pre × OTy × OTy :=
  match C with
  | .top _ _ _ none => (.top p I (.prod a b) none, a, b)
  | .id _ => (.comp (.top p I a none) (.pair (.id a) (.id a)), a, b)
  | C => (.comp (.top p I a (some (.close p (.dom C) a "a closed term in a lifted body"))) (.pair (.id a) C), a, b)

/-- A result as a family over `I`. -/
def famOf : Arg → M (Pre × OTy × OTy)
  | .fam q i a b => do unify p "the index of a family" i I; pure (q, a, b)
  | .rel q s t => pure (liftConst I p q s t)

/-- `RS` lifted: `⟨R,S⟩dom(π₁π₂ ∩ π₂π₁)⟨π₁π₁,π₂π₂⟩`, the rows of one key whose middles agree. -/
def lComp : Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (R, a, b), (S, b', c) => do
    unify p "the middle object of a composition" b' b
    let ab := OTy.prod a b; let bc := OTy.prod b c
    let eq := dom (meet (comp (outl ab bc) (outr a b)) (comp (outr ab bc) (outl b c)))
    pure (comp (comp (pair R S) eq) (pair (comp (outl ab bc) (outl a b)) (comp (outr ab bc) (outr b c))), a, c)

/-- A family then a closed `C`: `F⟨π₁,π₂C⟩`, each row's value carried by `C`. -/
def lThen : Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (F, a, b), (C, s, t) => do
    unify p "the middle object of a composition" s b
    pure (comp F (pair (outl a b) (comp (outr a b) C)), a, t)

def lConv : Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b) => (comp R (pair (outr a b) (outl a b)), b, a)

def lDom : Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b) => (comp R (pair (outl a b) (outl a b)), a, a)

def lRan : Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b) => (comp R (pair (outr a b) (outr a b)), b, b)

/-- `∼R` lifted: `D⊤ − R`, `⊤ : I ⟶ a×b`. -/
def lCompl : Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b) => (diff (top p I (.prod a b) none) R, a, b)

/-- `∩ ∪ −` lifted: the same operator on the two families. -/
def lSame (op : Pre → Pre → Pre) : Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (R, a, b), (S, a', b') => do
    unify p "the source of the right operand" a' a; unify p "the target of the right operand" b' b
    pure (op R S, a, b)

def lLdiv (R S : Pre × OTy × OTy) : M (Pre × OTy × OTy) := do
  unify p "the source of `\\`'s right operand" S.2.1 R.2.1
  pure (lCompl I p (← lComp p (lConv R) (lCompl I p S)))

def lRdiv (R S : Pre × OTy × OTy) : M (Pre × OTy × OTy) := do
  unify p "the target of `/`'s right operand" S.2.2 R.2.2
  lComp p (lCompl I p R) (lConv S)

/-- `⟨R,S⟩` lifted: `⟨R,S⟩dom(π₁π₁ ∩ π₂π₁)⟨π₁π₁,⟨π₁π₂,π₂π₂⟩⟩`, pairs of rows of one source. -/
def lPair : Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (R, a, b), (S, a', c) => do
    unify p "the source of the pair's second part" a' a
    let ab := OTy.prod a b; let ac := OTy.prod a c
    let eq := dom (meet (comp (outl ab ac) (outl a b)) (comp (outr ab ac) (outl a c)))
    pure (comp (comp (pair R S) eq) (pair (comp (outl ab ac) (outl a b))
      (pair (comp (outl ab ac) (outr a b)) (comp (outr ab ac) (outr a c)))), a, .prod b c)

/-- `R×S` lifted: `⟨R,S⟩⟨⟨π₁π₁,π₂π₁⟩,⟨π₁π₂,π₂π₂⟩⟩`. -/
def lProd : Pre × OTy × OTy → Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b), (S, a', b') =>
    let ab := OTy.prod a b; let ab' := OTy.prod a' b'
    (comp (pair R S) (pair (pair (comp (outl ab ab') (outl a b)) (comp (outr ab ab') (outl a' b')))
      (pair (comp (outl ab ab') (outr a b)) (comp (outr ab ab') (outr a' b')))), .prod a a', .prod b b')

/-- `[R,S]` lifted: `R⟨π₁inl,π₂⟩ ∪ S⟨π₁inr,π₂⟩`, the row `R(inl×𝟙) ∪ S(inr×𝟙)` with no universe. -/
def lJunc : Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (R, a, c), (S, b, c') => do
    unify p "the target of the case's second part" c' c
    pure (join (comp R (pair (comp (outl a c) (inl a b)) (outr a c)))
      (comp S (pair (comp (outl b c) (inr a b)) (outr b c))), .sum a b, c)

/-- The family `R : I ⟶ a×b` as one relation of the key and the source, `Rᴵ : I×a ⟶ b`, run on the pairs
    (key, source) in demand (§e, cost of the keyed fold). A row whose fibre at a source reads only that source
    is keyed through its parts, so a closed part runs on the sources in demand, not on its domain at every key.
    Any other family is read whole at each key and cut to the source, `⟨π₁R,π₂⟩dom(π₁π₁ ∩ π₂)π₁π₂`: every part
    runs on the keys in demand, so `I` needs no universe (a converse or `ran` here would close over all of `I`). -/
def keyed : Pre → OTy → OTy → Pre
  | .join R S, a, b => join (keyed R a b) (keyed S a b)
  | .meet R S, a, b => meet (keyed R a b) (keyed S a b)
  | .diff R S, a, b => diff (keyed R a b) (keyed S a b)
  -- `D⊤`, `⊤ : I ⟶ a×b`: `D⊤`, `⊤ : I×a ⟶ b`
  | .top q _ (.prod _ _) none, a, b => top q (.prod I a) b none
  -- a closed `C` as a family, `D⊤⟨𝟙,C⟩` with `⊤` onto `V`: `π₂VC`, `C` run on the sources `π₂V` meets; onto
  -- `V = dom(C')`, `dom(π₂C')π₂C`, so `C'` too runs on the sources in demand, not on its universe
  | .comp (.top _ _ _ (some (.close _ (.dom C') _ _))) (.pair (.id _) C), a, _ =>
    comp (dom (comp (outr I a) C')) (comp (outr I a) C)
  | .comp (.top _ _ _ V) (.pair (.id _) C), a, _ => comp (match V with | some V => comp (outr I a) V | none => outr I a) C
  -- `RS` lifted: `⟨π₁,Rᴵ⟩Sᴵ`
  | .comp (.comp (.pair R S) (.dom (.meet (.comp (.outl _ _) (.outr a m)) (.comp (.outr _ _) (.outl _ c)))))
      (.pair (.comp (.outl _ _) (.outl _ _)) (.comp (.outr _ _) (.outr _ _))), _, _ =>
    comp (pair (outl I a) (keyed R a m)) (keyed S m c)
  -- `⟨R,S⟩` lifted: `⟨Rᴵ,Sᴵ⟩`
  | .comp (.comp (.pair R S) (.dom (.meet (.comp (.outl _ _) (.outl a b)) (.comp (.outr _ _) (.outl _ c)))))
      (.pair (.comp (.outl _ _) (.outl _ _)) (.pair (.comp (.outl _ _) (.outr _ _)) (.comp (.outr _ _) (.outr _ _)))),
      _, _ => pair (keyed R a b) (keyed S a c)
  -- `R×S` lifted: `⟨⟨π₁,π₂π₁⟩Rᴵ,⟨π₁,π₂π₂⟩Sᴵ⟩` on `I×(a×a')`
  | .comp (.pair R S) (.pair (.pair (.comp (.outl _ _) (.outl a b)) (.comp (.outr _ _) (.outl a' b')))
      (.pair (.comp (.outl _ _) (.outr _ _)) (.comp (.outr _ _) (.outr _ _)))), _, _ =>
    let s := OTy.prod a a'
    pair (comp (pair (outl I s) (comp (outr I s) (outl a a'))) (keyed R a b))
      (comp (pair (outl I s) (comp (outr I s) (outr a a'))) (keyed S a' b'))
  -- `F` then `C`, `F⟨π₁,π₂C⟩`: `FᴵC`
  | .comp F (.pair (.outl a b) (.comp (.outr _ _) C)), _, _ => comp (keyed F a b) C
  -- `dom(F)` lifted, `F⟨π₁,π₁⟩`: `dom(Fᴵ)π₂`
  | .comp F (.pair (.outl a b) (.outl _ _)), _, _ => comp (dom (keyed F a b)) (outr I a)
  | R, _, _ => flat R

/-- `Λ(R)` lifted: `⟨𝟙,Rπ₁⟩⟨π₂,Λ(Rᴵ)⟩`. -/
def lLam : Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b) => (comp (pair (id I) (comp R (outl a b))) (pair (outr I a) (lam (keyed I R a b))), a, .arr b)

/-- `X⦇e,S⦈` lifted, `X : I ⟶ a×[x]`, `e : I ⟶ v×v`, `S : I ⟶ (x×v)×v`: `⟨𝟙,X⟩⟨π₂π₁,⟨π₁,π₂π₂⟩⦇e,S'⦈ᴵ⟩`, where
    `⦇e,S'⦈ᴵ : I×[x] ⟶ v` folds each array at its key, carrier `I×v`, `S' ≜ ⟨π₂π₁,⟨π₁,π₂π₂⟩⟩⟨π₁,Sᴵ⟩`. -/
def lFold : Pre × OTy × OTy → Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (X, a, xs), (e, v, v'), (S, xv, w) => do
    unify p "the fold's start, a coreflexive" v' v
    let x ← fresh
    unify p "the source of the fold's step" xv (.prod x v)
    unify p "the target of the fold's step" w v
    unify p "the arrays a fold runs on" xs (.arr x)
    let iv := OTy.prod I v; let xv := OTy.prod x v; let ax := OTy.prod a (.arr x)
    let S' := comp (pair (comp (outr x iv) (outl I v)) (pair (outl x iv) (comp (outr x iv) (outr I v))))
      (pair (outl I xv) (keyed I S xv v))
    let f := foldI e S'
    pure (comp (pair (id I) X) (pair (comp (outr I ax) (outl a (.arr x)))
      (comp (pair (outl I ax) (comp (outr I ax) (outr a (.arr x)))) f)), a, v)

end Rows

/-- A row that has no lifting (§e). -/
def notLiftable {α : Type} (p : Pos) (what : String) : M α :=
  throw ⟨p, s!"{what} given a family is not liftable: it runs one relation on every array (§e)"⟩

/-- The front-end form of a result: a family outside its body is a relation `i ⟶ a×b`. -/
def Arg.plain : Arg → Pre × OTy × OTy
  | .rel q s t => (q, s, t)
  | .fam q i a b => (q, i, .prod a b)

def Arg.isFam : Arg → Bool
  | .fam .. => true
  | _ => false

/-- A constant: fresh objects for its type, the explicit ones `(A,B)` unified with source and target. -/
def constant (env : Env) (p : Pos) (o : Op) (objs : List OExp) : M Arg := do
  let a ← fresh; let b ← fresh
  let (q, s, t) : Pre × OTy × OTy := match o with
    | .id => (.id a, a, a)
    | .zero => (.zero a b, a, b)
    | .top => (.top p a b none, a, b)
    | .mem => (.mem b, .arr b, b)
    | .outl => (.outl a b, .prod a b, a)
    | .outr => (.outr a b, .prod a b, b)
    | .inl => (.inl a b, a, .sum a b)
    | .inr => (.inr a b, b, .sum a b)
    | .leq => (.leq p a, a, a)
    | .lt => (.lt p a, a, a)
    | .succ => (.succ p a, a, a)
    | .arith k => (.arith p k a, .prod a a, a)
    | .union => (.union a, .arr (.arr a), .arr a)
    | .tau => (.tau a, a, .arr a)
    | .nil => (.nil a b, a, .arr b)
    | .alpha => (.junc (.close p (.nil a b) a "α") (.close p (.cons b) (.prod b (.arr b)) "α"), .sum a (.prod b (.arr b)), .arr b)
    | .cons => (.cons b, .prod b (.arr b), .arr b)
    | .length => (.length b a, .arr b, a)
    | .total => (.total a, .arr a, a)
    | .inits => (.inits b, .arr b, .arr (.arr b))
    | .cat => (.cat b, .prod (.arr b) (.arr b), .arr b)
    | .zip => (.zip a b, .prod (.arr a) (.arr b), .arr (.prod a b))
    | .snoc => (.snoc b, .prod (.arr b) b, .arr b)
    | .setify => (.setify b, .arr b, .arr b)
    | .bagify => (.bagify b, .arr b, .arr b)
    | .tic => (.tic b, .prod b (.arr b), .arr (.arr b))
    | _ => (.id a, a, a)
  match objs with
  | [] => pure ()
  | [x] => unify p s!"the object of {o.sym}" s (← oty env [] x)
  | [x, y] => do unify p s!"the source of {o.sym}" s (← oty env [] x); unify p s!"the target of {o.sym}" t (← oty env [] y)
  | _ => throw ⟨p, s!"{o.sym} takes at most two objects, found {objs.length}"⟩
  pure (.rel q s t)

/-- The declared objects holding all the words `ws` (named elements, or numbers in their range). -/
def holders (objs : Objs) (ws : List String) : List String :=
  let holds (i : ObjInfo) (w : String) : Bool := i.elems.contains w ||
    match i.range, w.toInt? with | some (lo, hi), some k => lo ≤ k && k ≤ hi | _, _ => false
  (objs.filter fun (_, i) => ws.all (holds i)).map (·.1)

/-- Why the rows `ts` of a literal's position do not determine its object: they are none (an empty array's
    elements), or several declared objects hold their words. -/
def litOpen (objs : Objs) (p : Pos) (ts : List Tup) : Err :=
  let ws := ts.filterMap fun | .leaf w => some w | _ => none
  if ts.isEmpty then ⟨p, s!"the object of {(Tup.arr []).show} cannot be read off an empty array: write nil(A,[O])"⟩
  else ⟨p, s!"the elements {ws} are in {holders objs ws}; write the literal after its object"⟩

/-- The object of a literal's position, `ts` the sides there, one per row or array element (§c): a word's is the
    one declared object holding all the words, a pair's the product of its parts', an array's `[O]`, `O` the
    object of the elements of all its arrays together. Where the rows do not determine it (`litOpen`) it is an
    open object, which the context fixes as it fixes `nil`'s; `litCol` reports one still open at `build`. -/
partial def litTy (objs : Objs) (p : Pos) (ts : List Tup) : M OTy := do
  let t := ts.headD default
  if let some r := ts.find? (!·.like t) then
    throw ⟨p, s!"the rows of a literal nest alike: found {r.show}, expected the form of {t.show}"⟩
  match ts, t with
  | [], _ => fresh
  | _, .leaf _ =>
    let ws := ts.filterMap fun | .leaf w => some w | _ => none
    match holders objs ws with
    | [n] => pure (.base n)
    | [] => throw ⟨p, s!"no declared object has the elements {ws}"⟩
    | _ => fresh
  | _, .pair .. =>
    pure (.prod (← litTy objs p (ts.map fun | .pair a _ => a | r => r))
      (← litTy objs p (ts.map fun | .pair _ b => b | r => r)))
  | _, .arr _ => pure (.arr (← litTy objs p (ts.flatMap fun | .arr es => es | _ => [])))

/-- A builtin applied to relations, every argument one relation. -/
def applied (p : Pos) (o : Op) : List (Pre × OTy × OTy) → M Arg
  | [(q, s, t)] => do
    match o with
    | .dom => pure (.rel (.dom q) s s)
    | .ran => pure (.rel (.ran (.close p q s "ran( ) reads its argument whole")) t t)
    | .lam => pure (.rel (.lam q) s (.arr t))
    | .E => pure (.rel (.E q) (.arr s) (.arr t))
    | .map => pure (.rel (.map q) (.arr s) (.arr t))
    | .P => throw ⟨p, s!"P(R) : 𝒫{s} ⟶ 𝒫{t} has no universe on its target and no demand there (§a)"⟩
    | .est | .thin | .thinL | .merge => do
      unify p s!"the target of {o.sym}'s argument" t s
      -- the order is tested on the pairs the operator compares (`build`, `param`), not read whole
      let c := Pre.close p q s s!"{o.sym}( )"
      let a := OTy.arr s
      let (r, x, y) : Pre × OTy × OTy := match o with
        | .est => (.est c, a, s) | .thin => (.thin c, a, a) | .thinL => (.thinL c, a, a)
        | _ => (.merge c, .prod a a, a)
      pure (.rel r x y)
    | .loop => do
      let x ← fresh; let y ← fresh
      unify p "the source of loop's argument" s (.prod x y); unify p "the target of loop's argument" t x
      pure (.rel (.loop q) (.prod x (.arr y)) x)
    | _ => throw ⟨p, s!"{o.sym} takes {(Op.table.find? (·.2.1 == o)).map (·.2.2) |>.getD 0} arguments, found 1"⟩
  | as => throw ⟨p, s!"{o.sym}: wrong number of arguments, found {as.length}"⟩

/-- A builtin applied with a family among its arguments, by the rows of §e. -/
def appliedL (I : OTy) (p : Pos) (o : Op) (as : List Arg) : M Arg := do
  let fs ← as.mapM (famOf I p)
  let r ← match o, fs with
    | .dom, [R] => pure (lDom R)
    | .ran, [R] => pure (lRan R)
    | .lam, [R] => pure (lLam I R)
    | .E, [R] => do let b ← fresh; pure (lLam I (← lComp p (liftConst I p (.mem b) (.arr b) b) R))
    | .P, _ => notLiftable p "P(R)"
    | o, _ => notLiftable p s!"{o.sym}( )"
  pure (.fam r.1 I r.2.1 r.2.2)

/-- A binary operator on one relation each side. -/
def binary (p : Pos) (o : Bin) : Pre × OTy × OTy → Pre × OTy × OTy → M Arg
  | (q, s, t), (r, s', t') => do
    match o with
    | .meet | .join | .diff => do
      unify p s!"the source of {o.sym}'s right operand" s' s; unify p s!"the target of {o.sym}'s right operand" t' t
      let x := match o with
        | .meet => Pre.meet q r | .join => .join q r | _ => .diff q r
      pure (.rel x s t)
    | .rdiv => do
      unify p "the target of `/`'s right operand" t' t
      let w := "R/S reads its operands whole outside a meet with a term run on demand"
      pure (.rel (.rdiv p (.close p q s w) (.close p r s' w) s s') s s')
    | .ldiv => do
      unify p "the source of `\\`'s right operand" s' s
      let w := "R\\S reads its operands whole outside a meet with a term run on demand"
      pure (.rel (.ldiv p (.close p q s w) (.close p r s w) t t') t t')
    -- `R×S = ⟨π₁R,π₂S⟩`: `build` runs it as that pair when an operand runs on demand
    | .prod => pure (.rel (.prod (.close p q s "R×S") (.close p r s' "R×S")) (.prod s s') (.prod t t'))

/-- A binary operator with a family on a side, by the rows of §e. -/
def binaryL (I : OTy) (p : Pos) (o : Bin) (x y : Arg) : M Arg := do
  let R ← famOf I p x; let S ← famOf I p y
  let r ← match o with
    | .meet => lSame p Pre.meet R S
    | .join => lSame p Pre.join R S
    | .diff => lSame p Pre.diff R S
    | .rdiv => lRdiv I p R S
    | .ldiv => lLdiv I p R S
    | .prod => pure (lProd R S)
  pure (.fam r.1 I r.2.1 r.2.2)

/-- A defined operator's result where it is used: a family stays one inside a lifted body of the same index,
    and is a relation `i ⟶ a×b` outside. -/
def settle (m : Option OTy) (p : Pos) : Arg → M Arg
  | .fam q i a b => match m with
    | some I => do unify p "the index of a family" i I; pure (.fam q i a b)
    | none => pure (.rel q i (.prod a b))
  | r => pure r

mutual

/-- Elaborate `e` in the mode `m`: plain, or the body of a definition lifted to the index `I`. -/
def elabE (env : Env) (m : Option OTy) : Expr → M Arg
  | .name p n => do
    match env.params.lookup n with
    | some a => pure a
    | none => match env.defs.lookup n with
      | some d =>
        if d.arity == 0 then (do settle m p (← d.apply p []))
        else throw ⟨p, s!"'{n}' takes {d.arity} arguments, found none"⟩
      | none => throw ⟨p, s!"unknown name '{n}'"⟩
  | .op p o objs args => do
    let as ← elabArgs env m args
    if args.isEmpty then constant env p o objs
    else match m with
      | some I => if as.any Arg.isFam then appliedL I p o as else applied p o (as.map Arg.plain)
      | none => applied p o (as.map Arg.plain)
  | .app p n args => do
    let as ← elabArgs env m args
    match env.defs.lookup n with
    | some d =>
      if d.arity != as.length then throw ⟨p, s!"'{n}' takes {d.arity} arguments, found {as.length}"⟩
      settle m p (← d.apply p as)
    | none => throw ⟨p, s!"unknown name '{n}'"⟩
  -- `R n S`: the definition declared `_n_`, given `R` and `S` (§c)
  | .inf p n a b => do
    let x ← elabE env m a; let y ← elabE env m b
    match env.defs.lookup s!"_{n}_" with
    | some d => settle m p (← d.apply p [x, y])
    | none => throw ⟨p, s!"unknown infix operator '{n}'"⟩
  | .comp a b => do
    let x ← elabE env m a
    let p := b.pos
    -- `Xest(Q)`, `Xthin(Q)` with `Q` a family: `est`, `thin` run one `Q` on every array, so the rows of §e
    -- work on `G ≜ X∋`, the values of each key; a closed `Q` takes the closed row below
    let q? ← match m, b with
      | some _, .op _ .est [] [qe] | some _, .op _ .thin [] [qe] => do
        let y ← elabE env m qe; pure (if y.isFam then some y else none)
      | _, _ => pure none
    let est := match b with | .op _ .est _ _ => true | _ => false
    -- `X⦇e,S⦈` with `e` or `S` a family: the fold keyed by the index, on the arrays `X` gives each key (§e)
    let fold? ← match m, b with
      | some _, .fold _ ea sa => do
        let y ← elabE env m ea; let z ← elabE env m sa
        pure (if y.isFam || z.isFam then some (y, z) else none)
      | _, _ => pure none
    if let (some I, some (y, z)) := (m, fold?) then
      let r ← lFold I p (← famOf I p x) (← famOf I p y) (← famOf I p z)
      return .fam r.1 I r.2.1 r.2.2
    match m, q? with
    | some I, some q => do
      let e ← fresh
      let G ← lThen p (← famOf I p x) (.mem e, .arr e, e)
      let Q ← famOf I p q
      let r ← if est then do lSame p Pre.meet G (← lLdiv I p (lConv G) (lConv Q))
        else do pure (lLam I (← lSame p Pre.diff G (← lComp p G (← lSame p Pre.diff Q (lConv Q)))))
      pure (.fam r.1 I r.2.1 r.2.2)
    | _, _ =>
      let y ← elabE env m b
      match m, x.isFam || y.isFam with
      | some I, true =>
        let r ← match x, y with
          | .fam .., .rel q s t => lThen p (← famOf I p x) (q, s, t)
          | _, _ => do lComp p (← famOf I p x) (← famOf I p y)
        pure (.fam r.1 I r.2.1 r.2.2)
      | _, _ =>
        let (q, s, t) := x.plain; let (r, s', t') := y.plain
        unify p "the source of the right factor of a composition" s' t
        pure (.rel (.comp q r) s t')
  | .bin p o a b => do
    let x ← elabE env m a; let y ← elabE env m b
    match m, x.isFam || y.isFam with
    | some I, true => binaryL I p o x y
    | _, _ => binary p o x.plain y.plain
  | .conv p a => do
    -- `build` pushes the converse to the leaves when the term runs on demand (`convTm`)
    match ← elabE env m a with
    | .fam q i s t => let r := lConv (q, s, t); pure (.fam r.1 i r.2.1 r.2.2)
    | .rel q s t => pure (.rel (.conv (.close p q s "R°")) t s)
  | .compl p a => do
    match ← elabE env m a with
    | .fam q i s t => let r := lCompl i p (q, s, t); pure (.fam r.1 i r.2.1 r.2.2)
    | .rel q s t => pure (.rel (.diff (.top p s t none) q) s t)
  | .pair p a b => do
    let x ← elabE env m a; let y ← elabE env m b
    match m, x.isFam || y.isFam with
    | some I, true => let r ← lPair p (← famOf I p x) (← famOf I p y); pure (.fam r.1 I r.2.1 r.2.2)
    | _, _ =>
      let (q, s, t) := x.plain; let (r, s', t') := y.plain
      unify p "the source of the pair's second part" s' s
      pure (.rel (.pair q r) s (.prod t t'))
  | .junc p a b => do
    let x ← elabE env m a; let y ← elabE env m b
    match m, x.isFam || y.isFam with
    | some I, true => let r ← lJunc p (← famOf I p x) (← famOf I p y); pure (.fam r.1 I r.2.1 r.2.2)
    | _, _ =>
      let (q, s, t) := x.plain; let (r, s', t') := y.plain
      unify p "the target of the case's second part" t' t
      let w := "[R,S] reads its parts whole"
      pure (.rel (.junc (.close p q s w) (.close p r s' w)) (.sum s s') t)
  | .fold p a b => do
    let x ← elabE env m a; let y ← elabE env m b
    if x.isFam || y.isFam then
      throw ⟨p, "⦇e,S⦈ given a family is not liftable on its own: its arrays come from its left, X⦇e,S⦈ (§e)"⟩
    let (q, v, v') := x.plain; let (r, ev, w) := y.plain
    unify p "the fold's start, a coreflexive" v' v
    let e ← fresh
    unify p "the source of the fold's step" ev (.prod e v)
    unify p "the target of the fold's step" w v
    pure (.rel (.fold (.close p q v "the fold's start is read whole") r) (.arr e) v)
  | .lit p ps => do
    let a ← litTy env.objs p (ps.map (·.1)); let b ← litTy env.objs p (ps.map (·.2))
    pure (.rel (.lit p a b ps) a b)

def elabArgs (env : Env) (m : Option OTy) : List Expr → M (List Arg)
  | [] => pure []
  | e :: es => do let a ← elabE env m e; pure (a :: (← elabArgs env m es))

end

/-- A declared type matched against an argument's: the variables' objects so far, no match, or a variable met
    at two objects. -/
inductive Match
  | ok (vs : List (String × OTy))
  | no
  | clash (n : String) (o o' : OTy)

/-- `t` as `mk a b`, an unsolved variable solved to that form; none when `t` is another object. -/
def split (p : Pos) (mk : OTy → OTy → OTy) (t : OTy) : M (Option (OTy × OTy)) := do
  let a ← fresh; let b ← fresh
  let st ← get
  try unify p "" t (mk a b); let s ← get; pure (some (zonk s a, zonk s b)) catch _ => do set st; pure none

def Match.bind (r : Match) (k : List (String × OTy) → M Match) : M Match :=
  match r with | .ok vs => k vs | r => pure r

/-- First-order matching of the declared `o` against `t`, extending the instantiation `vs`: a variable takes
    the object it meets, once; a declared object unifies. -/
def pmatch (env : Env) (p : Pos) (vs : List (String × OTy)) : OExp → OTy → M Match
  | .var _ n, t => match vs.lookup n with
    | none => pure (.ok ((n, t) :: vs))
    | some o => do
      let st ← get
      try unify p "" t o; pure (.ok vs) catch _ => do set st; pure (.clash n (zonk st o) (zonk st t))
  | .prod x y, t => do match ← split p .prod t with
    | some (a, b) => (← pmatch env p vs x a).bind (pmatch env p · y b)
    | none => pure .no
  | .sum x y, t => do match ← split p .sum t with
    | some (a, b) => (← pmatch env p vs x a).bind (pmatch env p · y b)
    | none => pure .no
  | .pow x, t | .list x, t => do match ← split p (fun a _ => .arr a) t with
    | some (a, _) => pmatch env p vs x a
    | none => pure .no
  | o@(.name ..), t => do
    let O ← oty env [] o
    let st ← get
    try unify p "" t O; pure (.ok vs) catch _ => do set st; pure .no

/-- `x ⟶ y` matched against `s ⟶ t`. -/
def both (env : Env) (p : Pos) (vs : List (String × OTy)) (x y : OExp) (s t : OTy) : M Match := do
  (← pmatch env p vs x s).bind (pmatch env p · y t)

/-- Bind a parameter to its argument: one relation, or, for a declared `S : A ⟶ B` given `I ⟶ A×B`, a family
    with the index `I` (§e). `vs` is the use's instantiation of the object variables so far. -/
def bind (env : Env) (p : Pos) (P : Param) (a : Arg) (vs : List (String × OTy)) :
    M ((String × Arg) × Option OTy × List (String × OTy)) := do
  match P.ty, a with
  | none, .rel .. => pure ((P.name, a), none, vs)
  | none, .fam .. =>
    throw ⟨p, s!"parameter '{P.name}' is given a family but declares no type; write '{P.name} : A ⟶ B'"⟩
  | some (x, y), a => do
    let st ← get
    let decl := s!"'{P.name} : {x.show} ⟶ {y.show}'"
    let clash (r : Match) (s t : OTy) : M Unit := match r with
      | .clash n o o' => throw ⟨p, s!"`{n}` in the type of '{P.name}' is both {o} and {o'}: {decl} given {s} ⟶ {t}"⟩
      | _ => pure ()
    match a with
    | .fam q i s t =>
      match ← both env p vs x y s t with
      | .ok vs => pure ((P.name, .fam q i (← oty env vs x) (← oty env vs y)), some i, vs)
      | r => do set st; clash r (zonk st s) (zonk st t); throw ⟨p, s!"{decl} given a family of fibre {zonk st s} ⟶ {zonk st t}"⟩
    | .rel q s t =>
      -- one relation `A ⟶ B` first; failing that, a family `I ⟶ A×B` (§e)
      let r ← both env p vs x y s t
      if let .ok vs := r then return ((P.name, a), none, vs)
      set st
      let r' ← match ← split p .prod t with
        | some (u, v) => both env p vs x y u v
        | none => pure .no
      if let .ok vs := r' then return ((P.name, .fam q s (← oty env vs x) (← oty env vs y)), some s, vs)
      set st
      let s := zonk st s; let t := zonk st t
      clash r s t; clash r' s t
      throw ⟨p, s!"{decl} given {s} ⟶ {t}: neither {x.show} ⟶ {y.show} nor a family I ⟶ {x.render true}×{y.render true}"⟩

/-- The projection of `(I₀×I₁)×…×Iₙ`, left-nested over the factors `ix`, onto the factor `k`. -/
def proj (ix : Array OTy) (k : Nat) : Pre := go (ix.size - 1)
where
  pre (m : Nat) : OTy := (ix.toList.take (m + 1)).tail.foldl .prod (ix.toList.headD default)
  go : Nat → Pre
    | 0 => .id (pre 0)
    | m + 1 =>
      if m + 1 == k then .outr (pre m) (ix.toList.getD (m + 1) default)
      else if m + 1 > k then .comp (.outl (pre m) (ix.toList.getD (m + 1) default)) (go m)
      else .id (pre (m + 1))

/-! ### Declared types -/

def OTy.mvs : OTy → List Nat
  | .mv k => [k]
  | .prod a b | .sum a b => a.mvs ++ b.mvs
  | .arr a => a.mvs
  | .base _ => []

def OTy.bases : OTy → List String
  | .base n => [n]
  | .prod a b | .sum a b => a.bases ++ b.bases
  | .arr a => a.bases
  | .mv _ => []

/-- The letters an inferred type names its open objects by: `α`…`ω` without `ο` and `π`, which read as `o`, `π₁`. -/
def varNames : List String := ("αβγδεζηθικλμνξρστυφχψω".toList).map Char.toString

/-- `o` with each unsolved variable of `os` named an object variable, `α β …` by first occurrence, skipping the
    names `os` already holds: an inferred type as a declaration writes it. -/
def gen (os : List OTy) (o : OTy) (avoid : List String := []) : OTy :=
  let used := avoid ++ os.flatMap OTy.bases
  let σ := (os.flatMap OTy.mvs).eraseDups.zip (varNames.filter (!used.contains ·))
  let rec go : OTy → OTy
    | .mv k => match σ.lookup k with | some n => .base n | none => .mv k
    | .prod a b => .prod (go a) (go b)
    | .sum a b => .sum (go a) (go b)
    | .arr a => .arr (go a)
    | o => o
  go o

/-- The body's type `s ⟶ t` against the declared `ty` of `n`, its variables the parameters' at this use (`vs`)
    and fresh otherwise: the declared type determines the objects the body leaves open (§e). -/
def declared (env : Env) (p : Pos) (n : String) (vs : List (String × OTy)) (ty : OExp × OExp) (s t : OTy) :
    M Unit := do
  let vs ← (ty.1.vars ++ ty.2.vars).foldlM (fun vs v => do
    if (vs.lookup v).isSome then pure vs else pure ((v, ← fresh) :: vs)) vs
  let a ← oty env vs ty.1; let b ← oty env vs ty.2
  let st ← get
  try
    unify p "" s a
    unify p "" t b
  catch _ => do
    let s := zonk st s; let t := zonk st t
    throw ⟨p, s!"`{n}` is declared {OExp.arrow ty}, but its body is {gen [s, t] s} ⟶ {gen [s, t] t}"⟩

/-- The type of `n`, as `rel --types` prints it: each parameter's (declared, its variables kept as written, or
    inferred) and the body's, open objects named as variables; what a definition missing one should write. -/
def inferSig (env : Env) (n : String) (ps : List Param) (b : Body) : M String := do
  let bs ← ps.mapM fun P => do
    match P.ty with
    | some (x, y) =>
      let vs := (x.vars ++ y.vars).map fun v => (v, OTy.base v)
      pure (P.name, ← oty env vs x, ← oty env vs y)
    | none => pure (P.name, ← fresh, ← fresh)
  let env' := { env with params := bs.map fun (q, s, t) => (q, .rel (.zero s t) s t) }
  let r ← match b with
    | .rel e => do let (_, s, t) := (← elabE env' none e).plain; pure (some (s, t))
    | .test e f => do let _ ← elabE env' none e; let _ ← elabE env' none f; pure none
  let st ← get
  let os := (bs.flatMap fun (_, s, t) => [s, t]) ++ (match r with | some (s, t) => [s, t] | none => [])
  let os := os.map (zonk st)
  -- a variable is not a name in scope (§e), nor the one being defined
  let avoid := n :: env.defs.map (·.1)
  let arr (s t : OTy) := s!"{gen os (zonk st s) avoid} ⟶ {gen os (zonk st t) avoid}"
  pure (sigText n ((ps.zip bs).map fun (P, q, s, t) => (q, some ((P.ty.map OExp.arrow).getD (arr s t))))
    (r.map fun (s, t) => arr s t))

/-- A definition with parameters: its body elaborated at each use, lifted when a declared parameter is given
    a family, its result checked against the declared type `ty`; a test `e ⊑ f` is the coreflexive
    `D − dom(R − S)` of the keys whose fibres pass. -/
def mkDef (env : Env) (n : String) (dp : Pos) (ps : List Param) (body : Body) (ty : Option (OExp × OExp)) :
    Def where
  arity := ps.length
  apply p args := do
    -- one instantiation of the object variables per use, shared by the parameters left to right (§e)
    let (bs, vs) ← (ps.zip args).foldlM (fun (bs, vs) (P, a) => do
      let (b, j, vs) ← bind env p P a vs; pure (bs ++ [(b, j)], vs)) ([], [])
    let check (s t : OTy) : M Unit := match ty with
      | some ty => declared env p n vs ty s t
      | none => pure ()
    -- the distinct indices `I₀ … Iₙ` of the family arguments, and each family's place among them (§e, mixed terms)
    let mut ix : Array OTy := #[]
    let mut pl : List (Option Nat) := []
    for (_, j?) in bs do
      match j? with
      | none => pl := pl ++ [none]
      | some j =>
        let mut k? : Option Nat := none
        for (i, k) in ix.toList.zipIdx do
          if k?.isNone then
            let st ← get
            try unify p "" j i; k? := some k catch _ => set st
        match k? with
        | some k => pl := pl ++ [some k]
        | none => pl := pl ++ [some ix.size]; ix := ix.push j
    -- several indices: the body runs at `(I₀×I₁)×…`, each family re-keyed by its projection
    let idx := ix.toList.head?.map fun i => ix.toList.tail.foldl .prod i
    let bound := (bs.zip pl).map fun (((n, a), _), k?) => match a, k?, idx with
      | .fam q _ s t, some k, some P => if ix.size > 1 then (n, .fam (.comp (proj ix k) q) P s t) else (n, a)
      | _, _, _ => (n, a)
    let env' := { env with params := bound }
    match body, idx with
    | .rel e, none => do
      let r ← elabE env' none e
      let (_, s, t) := r.plain; check s t; pure r
    | .rel e, some I => do
      let r ← famOf I p (← elabE env' (some I) e)
      check r.2.1 r.2.2
      pure (.fam r.1 I r.2.1 r.2.2)
    | .test _ _, none => throw ⟨p, s!"the test defined at {dp} needs a family; write `check` for one relation"⟩
    | .test e f, some I => do
      let R ← famOf I p (← elabE env' (some I) e)
      let S ← famOf I p (← elabE env' (some I) f)
      let (d, _) ← lSame p Pre.diff R S
      pure (.rel (.diff (.id I) (.dom d)) I I)

/-! ### Build: the solved objects, the core term -/

/-- The swap `A×B ⟶ B×A`, `⟨π₂,π₁⟩`. -/
def swapTm {A B : Obj} : Tm (.prod A B) (.prod B A) true := .pair .outr .outl

/-- `τ(R) = dom(π₂ ∩ π₁R)` for `R` that runs: the pairs `(a,b)` in demand with `a R b`. -/
def pairTest {A B : Obj} {d : Bool} (t : Tm A B d) : Tm (.prod A B) (.prod A B) true :=
  .dom (.meet .outr (.comp .outl t))

/-- `R°` for `R` run on demand (§a), itself run on demand: pushed to the leaves by `(RS)° = S°R°`,
    `(R∩S)° = R°∩S°` (and `∪`, `−`), `⟨R,S⟩° = π₁R° ∩ π₂S°`, a coreflexive is its own converse, and a builtin
    by its named converse (`cons° = uncons`), and the prelude's `perm` as its own (`Tm.own`). A closed part is
    conversed whole. The error is the leaf whose converse does not run on demand. -/
def convTm {A B : Obj} {d : Bool} (t : Tm A B d) : Except String ((e : Bool) × Tm B A e) :=
  if h : d = false then pure ⟨false, .conv (h ▸ t)⟩ else
  match t with
  | .val R => pure ⟨false, .conv (.val R)⟩
  | .uni U => pure ⟨false, .uni U⟩
  | .zero => pure ⟨false, .zero⟩
  | .conv R => pure ⟨false, R⟩
  | .ran R => pure ⟨false, .ran R⟩
  | .ldiv R S U V => pure ⟨false, .conv (.ldiv R S U V)⟩
  | .rdiv R S U V => pure ⟨false, .conv (.rdiv R S U V)⟩
  | .prod R S => pure ⟨false, .conv (.prod R S)⟩
  | .junc R S => pure ⟨false, .conv (.junc R S)⟩
  | .leq U => pure ⟨false, .conv (.leq U)⟩
  | .lt U => pure ⟨false, .conv (.lt U)⟩
  | .id => pure ⟨_, .id⟩
  | .dom R => pure ⟨_, .dom R⟩
  | .own R => pure ⟨_, .own R⟩
  | .comp R S => do let ⟨_, s⟩ ← convTm S; let ⟨_, r⟩ ← convTm R; pure ⟨_, .comp s r⟩
  | .meet R S => do let ⟨_, r⟩ ← convTm R; let ⟨_, s⟩ ← convTm S; pure ⟨_, .meet r s⟩
  | .join R S => do let ⟨_, r⟩ ← convTm R; let ⟨_, s⟩ ← convTm S; pure ⟨_, .join r s⟩
  | .diff R S => do let ⟨_, r⟩ ← convTm R; let ⟨_, s⟩ ← convTm S; pure ⟨_, .diff r s⟩
  -- `⟨R,S⟩° = π₁R° ∩ π₂S°`; with one side's converse only, the other is tested on the pairs it gives:
  -- `⟨π₁R°,π₂⟩τ(S)π₁`, `⟨π₁,π₂S°⟩τ(R°)π₂`
  | .pair R S => match convTm R, convTm S with
    | .ok ⟨_, r⟩, .ok ⟨_, s⟩ => pure ⟨_, .meet (.comp .outl r) (.comp .outr s)⟩
    | .ok ⟨_, r⟩, .error _ => pure ⟨_, .comp (.pair (.comp .outl r) .outr) (.comp (pairTest S) .outl)⟩
    | .error _, .ok ⟨_, s⟩ =>
      pure ⟨_, .comp (.pair .outl (.comp .outr s)) (.comp swapTm (.comp (pairTest R) (.comp swapTm .outr)))⟩
    | .error l, .error _ => throw l
  | .share _ R => convTm R
  | .cons => pure ⟨_, .uncons⟩
  | .uncons => pure ⟨_, .cons⟩
  | .snoc => pure ⟨_, .unsnoc⟩
  | .unsnoc => pure ⟨_, .snoc⟩
  | .cat => pure ⟨_, .uncat⟩
  | .uncat => pure ⟨_, .cat⟩
  -- the number verbs are closed on their universe: their converse is read whole there
  | .succ U => pure ⟨false, .conv (.comp (.uni (A := .long) U) (.succ U))⟩
  | .arith k U => pure ⟨false, .conv (.comp (.uni (Alg.prod (idU U) (idU U)).key) (.arith k U))⟩
  | .top _ => throw "⊤"
  | .mem => throw "∋"
  | .outl => throw "π₁"
  | .outr => throw "π₂"
  | .inl => throw "inl"
  | .inr => throw "inr"
  | .lam _ => throw "Λ( )"
  | .E _ => throw "E( )"
  | .map _ => throw "F( )"
  | .est _ => throw "est( )"
  | .thin _ => throw "thin( )"
  | .union => throw "union"
  | .tau => throw "τ"
  | .nil => throw "nil"
  | .length => throw "length"
  | .total => throw "sum"
  | .inits => throw "inits"
  | .zip => throw "zip"
  | .setify => throw "setify"
  | .bagify => throw "bagify"
  | .tic => throw "tic"
  | .thinL _ => throw "thinL( )"
  | .merge _ => throw "merge( )"
  | .loop _ => throw "loop( )"
  | .fold .. => throw "⦇e,S⦈"
  | .foldI .. => throw "a lifted fold"
  | .flat _ => throw "a lifted family"

/-- A pair test: `τ(R) : A×B ⟶ A×B`, the coreflexive on the pairs `(a,b)` in demand with `a R b`. -/
abbrev Cor := (A : Obj) × (B : Obj) × Tm (.prod A B) (.prod A B) true

/-- `R ∩ S` with `S` run on demand and `R` tested: `⟨𝟙,S⟩τ(R)π₂`; `R − S` is this with `𝟙 − τ(S)`. -/
def onPairs {A B : Obj} {e : Bool} (s : Tm A B e) (c : Tm (.prod A B) (.prod A B) true) : Tm A B true :=
  .comp (.pair .id s) (.comp c .outr)

/-- `τ(R/S) = 𝟙 − dom(⟨π₁,π₂S⟩(𝟙 − τ(R)))`, `R : A ⟶ C`, `S : B ⟶ C`: no `c` with `b S c` and not `a R c`. -/
def divTest {A B C : Obj} {e : Bool} (c : Tm (.prod A C) (.prod A C) true) (s : Tm B C e) :
    Tm (.prod A B) (.prod A B) true :=
  .diff .id (.dom (.comp (.pair .outl (.comp .outr s)) (.diff .id c)))

section Build

variable (objs : Objs) (st : St) (dp : Pos)

/-- A solved object's `Obj`: every declared base object is `long`. -/
def objOf : OTy → Except Err Obj
  | .base _ => pure .long
  | .prod a b => return .prod (← objOf a) (← objOf b)
  | .sum a b => return .sum (← objOf a) (← objOf b)
  | .arr a => return .arr (← objOf a)
  | .mv _ => throw ⟨dp, "an object is not determined; write the constant's objects, as in ⊤(A,B) or 𝟙(A)"⟩

def toObj (o : OTy) : Except Err Obj := objOf dp (zonk st o)

def internal {α : Type} (what : String) : Except Err α := throw ⟨dp, s!"internal: {what}"⟩

/-- `t` at the objects `A ⟶ B`: the cast is the equality `build` decided. -/
def at? {A B : Obj} (r : Res) : Except Err ((d : Bool) × Tm A B d) :=
  match r with
  | ⟨A', B', d, t⟩ => if h : A' = A ∧ B' = B then pure ⟨d, h.1 ▸ h.2 ▸ t⟩ else internal dp "objects disagree"

def closed? {A B : Obj} (r : Res) : Except Err (Tm A B false) := do
  match ← at? dp (A := A) (B := B) r with
  | ⟨false, t⟩ => pure t
  | ⟨true, _⟩ => internal dp "a term that needs keys where none are supplied"

/-- `𝟙` on the universe of `o`, or the error that `o` has none. -/
def uniTm (p : Pos) (o : OTy) (A : Obj) (what : String) : Except Err (Tm A A false) :=
  match uniOf objs (zonk st o) with
  | some ⟨A', _, U⟩ => if h : A' = A then pure (.uni (h ▸ U)) else internal dp "universe objects disagree"
  | none => throw ⟨p, s!"{what}: {zonk st o} has no universe; compose a set of its elements before it (§a)"⟩

/-- The universe of a declared base object, for `succ`, the value verbs (`plus`, …), `≤`, `<`. -/
def numU (p : Pos) (o : OTy) (op : String) : Except Err ((m : Nat) × Arr .long m) :=
  match zonk st o with
  | .base n => match (objs.lookup n).bind (·.uni) with
    | some u => pure u
    | none => throw ⟨p, s!"{op} on {n}: no universe"⟩
  | o => throw ⟨p, s!"{op} runs on a declared object, found {o}"⟩

/-- The element `w` of the declared base object `o`: its position among the named elements, or the number. -/
def code (p : Pos) (o : OTy) (w : String) : Except Err Int64 :=
  match zonk st o with
  | .base n => match objs.lookup n with
    | some i => match i.range, i.elems.idxOf? w, w.toInt? with
      | some (lo, hi), _, some k => if lo ≤ k ∧ k ≤ hi then pure (Int64.ofInt k)
          else throw ⟨p, s!"{w} is not in {n} = {lo}…{hi}"⟩
      | none, some k, _ => pure (Int64.ofNat k)
      | _, _, _ => throw ⟨p, s!"'{w}' is not an element of {n}"⟩
    | none => throw ⟨p, s!"unknown object '{n}'"⟩
  | o => throw ⟨p, s!"a literal relates elements of declared objects, found {o}"⟩

/-- The column of a literal's side of object `o`, its `n` rows' sides `rows`: a long column of codes at a leaf,
    the pair of the two parts' columns at a product, at an array the column of all its elements row after row
    as the payload, row `i` the slice `[lo i, hi i)`. `o` is zonked. -/
def litCol (p : Pos) (n : Nat) (o : OTy) (rows : List Tup) : Except Err ((A : Obj) × Vals A n) :=
  match o with
  | .prod x y => do
    let ⟨A, u⟩ ← litCol p n x (rows.map fun | .pair r _ => r | r => r)
    let ⟨B, v⟩ ← litCol p n y (rows.map fun | .pair _ r => r | r => r)
    pure ⟨.prod A B, (u, v)⟩
  | .arr x => do
    let ts ← rows.mapM fun
      | .arr es => pure es
      | r => throw ⟨p, s!"a literal's element of {o} is an array, found {r.show}"⟩
    let es := ts.flatten
    let ⟨B, v⟩ ← litCol p es.length x es
    let ends := (ts.foldl (fun (k, acc) t => (k + t.length, (k + t.length) :: acc)) (0, ([] : List Nat))).2.reverse
    let hi := ends.map Int64.ofNat; let lo := (ends.zip ts).map fun (e, t) => Int64.ofNat (e - t.length)
    if h : lo.length = n ∧ hi.length = n then
      (let l : Arr .long n := h.1 ▸ col lo; let r : Arr .long n := h.2 ▸ col hi; pure ⟨.arr B, ⟨_, l, r, v⟩⟩)
    else internal dp "literal array rows"
  | .mv _ => throw (litOpen objs p rows)
  -- a sum only the context gives, to an empty array's elements: no rows to read
  | .sum x y =>
    if h : n = 0 ∧ rows.isEmpty then h.1 ▸ (do
      let ⟨A, u⟩ ← litCol p 0 x []; let ⟨B, v⟩ ← litCol p 0 y []
      pure ⟨.sum A B, ⟨0, 0, emptyArr .boolean, emptyArr .long, u, v⟩⟩ : Except Err ((A : Obj) × Vals A 0))
    else throw ⟨p, s!"a literal relates elements of declared objects, found {o}"⟩
  | o => do
    let cs ← rows.mapM fun
      | .leaf w => code objs st p o w
      | r => throw ⟨p, s!"a literal's element of {o} is a word, found {r.show}"⟩
    if h : cs.length = n then (let c : Arr .long n := h ▸ col cs; pure ⟨.long, c⟩) else internal dp "literal rows"

/-- A pair test at the objects `A×B`. -/
def corAt (A B : Obj) : Cor → Except Err (Tm (.prod A B) (.prod A B) true)
  | ⟨A', B', c⟩ => if h : A' = A ∧ B' = B then pure (h.1 ▸ h.2 ▸ c) else internal dp "pair-test objects disagree"

/-- The pair test of an order parameter at its object `B`, or the error naming the leaf that is not testable. -/
def paramOf (why : String) : Except Err Cor → Except Err ((B : Obj) × Tm (.prod B B) (.prod B B) true)
  | .ok ⟨A, B, c⟩ => if h : B = A then pure ⟨A, h ▸ c⟩ else internal dp s!"{why}'s order is not on one object"
  | .error e => throw ⟨e.pos,
    s!"{why} runs its order on the pairs it compares, and the order is not testable on pairs (§a): {e.msg}"⟩

mutual

/-- `Pre` to `Tm` at the solved objects. Every check here holds by `elabE`'s unification except the
    universes, whose absence is the error of §a. -/
def build : Pre → Except Err Res
  | .tm r => pure r
  | .zero a b => return ⟨← toObj st dp a, ← toObj st dp b, false, .zero⟩
  | .id a => return ⟨_, _, true, .id (A := ← toObj st dp a)⟩
  | .top p a b tgt => do
    let A ← toObj st dp a; let B ← toObj st dp b
    let V ← match tgt with
      | none => uniTm objs st dp p b B "⊤'s target"
      | some q => do closed? dp (← build q)
    pure ⟨A, B, true, .top V⟩
  | .mem b => return ⟨_, _, true, .mem (B := ← toObj st dp b)⟩
  | .outl a b => return ⟨_, _, true, .outl (A := ← toObj st dp a) (B := ← toObj st dp b)⟩
  | .outr a b => return ⟨_, _, true, .outr (A := ← toObj st dp a) (B := ← toObj st dp b)⟩
  | .inl a b => return ⟨_, _, true, .inl (A := ← toObj st dp a) (B := ← toObj st dp b)⟩
  | .inr a b => return ⟨_, _, true, .inr (A := ← toObj st dp a) (B := ← toObj st dp b)⟩
  | .comp p q => do
    let ⟨A, B, d, t⟩ ← build p; let ⟨B', C, _, u⟩ ← build q
    if h : B' = B then pure ⟨A, C, d, .comp t (h ▸ u)⟩ else internal dp "composition objects disagree"
  -- `R°`: closed, conversed whole; on demand, pushed to the leaves (`convTm`); a leaf whose converse does not
  -- run on demand reads `R` whole on its source's universe
  | .conv (.close _ (.conv (.close _ q _ _)) _ _) => build q
  | .conv (.close pos q a _) => do
    let ⟨A, B, _, t⟩ ← build q
    match convTm t with
    | .ok ⟨e, u⟩ => pure ⟨B, A, e, u⟩
    | .error leaf => do
      let U ← uniTm objs st dp pos a A s!"the converse of {leaf} does not run on demand, so R° reads R whole"
      pure ⟨B, A, false, .conv (.comp U t)⟩
  | .conv p => do let r ← build p; let ⟨A, B, _, _⟩ := r; pure ⟨B, A, false, .conv (← closed? dp (A := A) (B := B) r)⟩
  -- a side that cannot run is tested on the pairs the other side gives (`test`)
  | .meet p q => match build p, build q with
    | .ok ⟨A, B, _, t⟩, .ok s => do let ⟨_, u⟩ ← at? dp (A := A) (B := B) s; pure ⟨A, B, _, .meet t u⟩
    | .error err, .ok ⟨A, B, _, s⟩ => match test p with
      | .ok c => do pure ⟨A, B, true, onPairs s (← corAt dp A B c)⟩
      | .error _ => throw err
    | .ok ⟨A, B, _, s⟩, .error err => match test q with
      | .ok c => do pure ⟨A, B, true, onPairs s (← corAt dp A B c)⟩
      | .error _ => throw err
    | .error err, .error _ => throw err
  | .join p q => do let ⟨A, B, _, t⟩ ← build p; let ⟨_, u⟩ ← at? dp (A := A) (B := B) (← build q); pure ⟨A, B, _, .join t u⟩
  | .diff p q => match build p, build q with
    | .ok ⟨A, B, _, t⟩, .ok s => do let ⟨_, u⟩ ← at? dp (A := A) (B := B) s; pure ⟨A, B, _, .diff t u⟩
    | .ok ⟨A, B, _, s⟩, .error err => match test q with
      | .ok c => do pure ⟨A, B, true, onPairs s (.diff .id (← corAt dp A B c))⟩
      | .error _ => throw err
    | .error err, _ => throw err
  | .dom p => do let ⟨A, _, d, t⟩ ← build p; pure ⟨A, A, d, .dom t⟩
  | .ran p => do let r ← build p; let ⟨A, B, _, _⟩ := r; pure ⟨B, B, false, .ran (← closed? dp (A := A) (B := B) r)⟩
  | .ldiv pos p q b c => do
    let r ← build p; let s ← build q; let ⟨A, B, _, _⟩ := r; let ⟨_, C, _, _⟩ := s
    let R ← closed? dp (A := A) (B := B) r; let S ← closed? dp (A := A) (B := C) s
    pure ⟨B, C, false, .ldiv R S (← uniTm objs st dp pos b B "R\\S") (← uniTm objs st dp pos c C "R\\S")⟩
  | .rdiv pos p q a b => do
    let r ← build p; let s ← build q; let ⟨A, C, _, _⟩ := r; let ⟨B, _, _, _⟩ := s
    let R ← closed? dp (A := A) (B := C) r; let S ← closed? dp (A := B) (B := C) s
    pure ⟨A, B, false, .rdiv R S (← uniTm objs st dp pos a A "R/S") (← uniTm objs st dp pos b B "R/S")⟩
  | .pair p q => do
    let ⟨A, _, _, t⟩ ← build p; let s ← build q; let ⟨_, C, _, _⟩ := s
    let ⟨_, u⟩ ← at? dp (A := A) (B := C) s; pure ⟨A, _, _, .pair t u⟩
  -- `R×S`: both operands closed on their sources, `Alg.prod`; an operand whose source has no universe, the pair
  -- `⟨π₁R,π₂S⟩` on demand
  | .prod (.close pp p a w) (.close pq q b w') =>
    match build (.close pp p a w), build (.close pq q b w') with
    | .ok ⟨A, B, false, t⟩, .ok ⟨C, D, false, u⟩ => pure ⟨.prod A C, .prod B D, false, .prod t u⟩
    | _, _ => do
      let ⟨A, B, _, t⟩ ← build p; let ⟨C, D, _, u⟩ ← build q
      pure ⟨.prod A C, .prod B D, true, .pair (.comp .outl t) (.comp .outr u)⟩
  | .prod p q => do
    let ⟨A, B, _, t⟩ ← build p; let ⟨C, D, _, u⟩ ← build q
    pure ⟨.prod A C, .prod B D, true, .pair (.comp .outl t) (.comp .outr u)⟩
  | .junc p q => do
    let r ← build p; let s ← build q; let ⟨A, C, _, _⟩ := r; let ⟨B, _, _, _⟩ := s
    pure ⟨_, _, false, .junc (← closed? dp (A := A) (B := C) r) (← closed? dp (A := B) (B := C) s)⟩
  | .lam p => do let ⟨_, _, _, t⟩ ← build p; pure ⟨_, _, _, .lam t⟩
  | .E p => do let ⟨_, _, _, t⟩ ← build p; pure ⟨_, _, _, .E t⟩
  | .map p => do let ⟨_, _, _, t⟩ ← build p; pure ⟨_, _, _, .map t⟩
  | .est p => do let ⟨_, c⟩ ← param p; pure ⟨_, _, _, .est c⟩
  | .thin p => do let ⟨_, c⟩ ← param p; pure ⟨_, _, _, .thin c⟩
  | .union a => return ⟨_, _, true, .union (A := ← toObj st dp a)⟩
  | .tau a => return ⟨_, _, true, .tau (A := ← toObj st dp a)⟩
  | .nil a b => return ⟨_, _, true, .nil (A := ← toObj st dp a) (B := ← toObj st dp b)⟩
  | .cons b => return ⟨_, _, true, .cons (B := ← toObj st dp b)⟩
  | .uncons b => return ⟨_, _, true, .uncons (B := ← toObj st dp b)⟩
  | .length b n => do
    if (← toObj st dp n) != .long then internal dp "length's target"
    pure ⟨_, _, true, .length (B := ← toObj st dp b)⟩
  | .total n => do if (← toObj st dp n) != .long then internal dp "sum's target"
                   pure ⟨_, _, true, .total⟩
  | .inits b => return ⟨_, _, true, .inits (B := ← toObj st dp b)⟩
  | .cat b => return ⟨_, _, true, .cat (B := ← toObj st dp b)⟩
  | .uncat b => return ⟨_, _, true, .uncat (B := ← toObj st dp b)⟩
  | .zip a b => return ⟨_, _, true, .zip (A := ← toObj st dp a) (B := ← toObj st dp b)⟩
  | .snoc b => return ⟨_, _, true, .snoc (B := ← toObj st dp b)⟩
  | .unsnoc b => return ⟨_, _, true, .unsnoc (B := ← toObj st dp b)⟩
  | .own p => do
    let ⟨A, B, d, t⟩ ← build p
    if h : B = A then pure ⟨A, A, d, .own (h ▸ t)⟩ else internal dp "perm's objects"
  | .setify b => return ⟨_, _, true, .setify (B := ← toObj st dp b)⟩
  | .bagify b => return ⟨_, _, true, .bagify (B := ← toObj st dp b)⟩
  | .tic b => return ⟨_, _, true, .tic (B := ← toObj st dp b)⟩
  | .thinL p => do let ⟨_, c⟩ ← param p; pure ⟨_, _, _, .thinL c⟩
  | .merge p => do let ⟨_, c⟩ ← param p; pure ⟨_, _, _, .merge c⟩
  | .loop p => do
    match ← build p with
    | r@⟨.prod X Y, _, _, _⟩ => do let ⟨_, F⟩ ← at? dp (A := .prod X Y) (B := X) r; pure ⟨_, _, true, .loop F⟩
    | _ => internal dp "loop's argument"
  | .succ p n => do let ⟨_, U⟩ ← numU objs st p n "succ"; pure ⟨_, _, true, .succ U⟩
  | .arith p k n => do let ⟨_, U⟩ ← numU objs st p n (Op.arith k).sym; pure ⟨_, _, true, .arith k U⟩
  | .leq p n => do let ⟨_, U⟩ ← numU objs st p n "≤"; pure ⟨_, _, false, .leq U⟩
  | .lt p n => do let ⟨_, U⟩ ← numU objs st p n "<"; pure ⟨_, _, false, .lt U⟩
  | .fold e s => do
    let r ← build e; let ⟨V, _, _, _⟩ := r
    match ← build s with
    | ⟨.prod E V', V'', _, S⟩ =>
      if h : V' = V ∧ V'' = V then
        pure ⟨.arr E, V, true, .fold (← closed? dp (A := V) (B := V) r) (h.1 ▸ h.2 ▸ S)⟩
      else internal dp "the fold's objects"
    | _ => internal dp "the fold's step"
  | .foldI e s => do
    let r ← build e; let ⟨I, VV, _, _⟩ := r
    let sr ← build s
    match VV, sr with
    | .prod V _, ⟨.prod E _, _, _, _⟩ => do
      let ⟨_, et⟩ ← at? dp (A := I) (B := .prod V V) r
      let ⟨_, S⟩ ← at? dp (A := .prod E (.prod I V)) (B := .prod I V) sr
      pure ⟨_, _, _, .foldI et S⟩
    | _, _ => internal dp "the lifted fold's objects"
  | .flat p => do
    match ← build p with
    | ⟨I, .prod A B, _, t⟩ => pure ⟨.prod I A, B, true, .flat t⟩
    | _ => internal dp "a family's objects"
  | .lit p a b ps => do
    let ⟨A, k⟩ ← litCol objs st dp p ps.length (zonk st a) (ps.map (·.1))
    let ⟨B, v⟩ ← litCol objs st dp p ps.length (zonk st b) (ps.map (·.2))
    pure ⟨A, B, false, .val ⟨ps.length, k, v⟩⟩
  | .close p q a why => do
    let ⟨A, B, d, t⟩ ← build q
    match d with
    | false => pure ⟨A, B, false, t⟩
    | true => pure ⟨A, B, false, .comp (← uniTm objs st dp p a A why) t⟩
termination_by x => (sizeOf x, 0)

/-- `τ(R)`, the pair test of `R : A ⟶ B` (`Cor`), for `R` that cannot enumerate its targets: a term that
    builds is tested as `dom(π₂ ∩ π₁R)`; otherwise by its form — `R/S`, `R\S`, `frac`, `∼`, `−`, `∩`, `∪`, `°`,
    and a composite with a side that runs. The error is `p`'s own build error. -/
def test (p : Pre) : Except Err Cor :=
  match build p with
  | .ok ⟨A, B, _, t⟩ => pure ⟨A, B, pairTest t⟩
  | .error err => match p with
    | .close _ q _ _ => test q
    | .conv q => do let ⟨A, B, c⟩ ← test q; pure ⟨B, A, .comp swapTm (.comp c swapTm)⟩
    | .top _ a b none => do pure ⟨← toObj st dp a, ← toObj st dp b, .id⟩
    | .meet q r => do let c ← test q; let ⟨A, B, c₁⟩ := c; pure ⟨A, B, .meet c₁ (← corAt dp A B (← test r))⟩
    | .join q r => do let c ← test q; let ⟨A, B, c₁⟩ := c; pure ⟨A, B, .join c₁ (← corAt dp A B (← test r))⟩
    | .diff q r => do let c ← test q; let ⟨A, B, c₁⟩ := c; pure ⟨A, B, .diff c₁ (← corAt dp A B (← test r))⟩
    -- `τ(PT) = dom(⟨π₁P,π₂⟩τ(T))` with `P` run; `τ(TQ) = dom(⟨π₁,π₂Q°⟩τ(T))` with `Q°` run on demand
    | .comp q r => match build q with
      | .ok ⟨A, M, _, t⟩ => do
        let c ← test r; let ⟨_, B, _⟩ := c
        pure ⟨A, B, .dom (.comp (.pair (.comp .outl t) .outr) (← corAt dp M B c))⟩
      | .error _ => match build r with
        | .ok ⟨M, B, _, u⟩ => match convTm u with
          | .ok ⟨_, v⟩ => do
            let c ← test q; let ⟨A, _, _⟩ := c
            pure ⟨A, B, .dom (.comp (.pair .outl (.comp .outr v)) (← corAt dp A M c))⟩
          | .error _ => throw err
        | .error _ => throw err
    -- `R/S`, `R : A ⟶ C` tested, `S : B ⟶ C` run on the `b`s
    | .rdiv _ (.close _ q _ _) (.close _ r _ _) _ _ => do
      let c ← test q; let ⟨A, C, _⟩ := c
      let ⟨B, _, _, s⟩ ← build r
      let ⟨_, s⟩ ← at? dp (A := B) (B := C) ⟨B, _, _, s⟩
      pure ⟨A, B, divTest (← corAt dp A C c) s⟩
    -- `R\S`, `R : A ⟶ B` with `R°` run on the `b`s, `S : A ⟶ C` tested: `τ = 𝟙 − dom(⟨π₁R°,π₂⟩(𝟙 − τ(S)))`
    | .ldiv _ (.close _ q _ _) (.close _ r _ _) _ _ => do
      let ⟨A, B, _, t⟩ ← build q
      match convTm t with
      | .ok ⟨_, v⟩ => do
        let c ← test r; let ⟨_, C, _⟩ := c
        pure ⟨B, C, .diff .id (.dom (.comp (.pair (.comp .outl v) .outr) (.diff .id (← corAt dp A C c))))⟩
      | .error _ => throw err
    | _ => throw err
termination_by (sizeOf p, 1)

/-- The order (or coreflexive) parameter `Q : B ⟶ B` of `est thin filter takewhile thinL merge`
    as its pair test `τ(Q)` (§a), which the operator runs on the pairs it compares: a closed `Q` and a `Q` that
    runs on demand alike, and any `Q` testable on pairs. `why` names the operator; the error names the leaf. -/
def param : Pre → Except Err ((B : Obj) × Tm (.prod B B) (.prod B B) true)
  | .close _ q _ why => paramOf dp why (test q)
  | q => paramOf dp "an operator" (test q)
termination_by p => (sizeOf p, 2)

end

end Build

end LeetQ.Rel.Lang
