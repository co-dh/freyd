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
  | frac {A B C : Obj} (R : Tm A C false) (S : Tm B C false) (UA : Tm A A false) (UB : Tm B B false) : Tm A B false
  | pair {A B C : Obj} {d e : Bool} (R : Tm A B d) (S : Tm A C e) : Tm A (.prod B C) (d || e)
  | prod {A B C D : Obj} (R : Tm A B false) (S : Tm C D false) : Tm (.prod A C) (.prod B D) false
  | junc {A B C : Obj} (R : Tm A C false) (S : Tm B C false) : Tm (.sum A B) C false
  | sum {A B C D : Obj} (R : Tm A C false) (S : Tm B D false) : Tm (.sum A B) (.sum C D) false
  | lam {A B : Obj} {d : Bool} (R : Tm A B d) : Tm A (.arr B) d
  | E {A B : Obj} {d : Bool} (R : Tm A B d) : Tm (.arr A) (.arr B) true
  | map {A B : Obj} {d : Bool} (R : Tm A B d) : Tm (.arr A) (.arr B) true
  | est {B : Obj} (Q : Tm B B false) : Tm (.arr B) B true
  | thin {B : Obj} (Q : Tm B B false) : Tm (.arr B) (.arr B) true
  | filter {B : Obj} (p : Tm B B false) : Tm (.arr B) (.arr B) true
  | takewhile {B : Obj} (p : Tm B B false) : Tm (.arr B) (.arr B) true
  | union {A : Obj} : Tm (.arr (.arr A)) (.arr A) true
  | tau {A : Obj} : Tm A (.arr A) true
  | nil {A B : Obj} : Tm A (.arr B) true
  | cons {B : Obj} : Tm (.prod B (.arr B)) (.arr B) true
  | uncons {B : Obj} : Tm (.arr B) (.prod B (.arr B)) true
  | length {B : Obj} : Tm (.arr B) .long true
  | total : Tm (.arr .long) .long true
  | head {B : Obj} : Tm (.arr B) B true
  | tail {B : Obj} : Tm (.arr B) (.arr B) true
  | pre {B : Obj} : Tm (.arr B) (.arr B) true
  | suf {B : Obj} : Tm (.arr B) (.arr B) true
  /-- `succ`, `plus`, `≤`, `<` on the declared number universe `U`. -/
  | succ {m : Nat} (U : Arr .long m) : Tm .long .long true
  | plus {m : Nat} (U : Arr .long m) : Tm (.prod .long .long) .long true
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
  | .arr a => s!"𝒫{a.render true}"
  | .mv k => s!"?{k}"

instance : ToString OTy := ⟨OTy.render false⟩

/-- A declared object: what it stands for, and, for a base object, its elements and universe. -/
structure ObjInfo where
  ty : OTy
  elems : List String := []
  range : Option (Nat × Nat) := none
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
    place with no left context: its term runs on its source's universe when it needs keys. `tm` is a built
    term, a definition's. -/
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
  | frac (pos : Pos) (p q : Pre) (a b : OTy)
  | pair (p q : Pre)
  | prod (p q : Pre)
  | junc (p q : Pre)
  | sum (p q : Pre)
  | lam (p : Pre)
  | E (p : Pre)
  | map (p : Pre)
  | est (p : Pre)
  | thin (p : Pre)
  | filter (p : Pre)
  | takewhile (p : Pre)
  | union (a : OTy)
  | tau (a : OTy)
  | nil (a b : OTy)
  | cons (b : OTy)
  | uncons (b : OTy)
  | length (b n : OTy)
  | total (n : OTy)
  | head (b : OTy)
  | tail (b : OTy)
  | pre (b : OTy)
  | suf (b : OTy)
  | succ (pos : Pos) (n : OTy)
  | plus (pos : Pos) (n : OTy)
  | leq (pos : Pos) (n : OTy)
  | lt (pos : Pos) (n : OTy)
  | fold (e s : Pre)
  | foldI (e s : Pre)
  | lit (pos : Pos) (a b : OTy) (ps : List (String × String))
  | close (pos : Pos) (p : Pre) (a : OTy)

instance : Inhabited Pre := ⟨.id (.base "")⟩

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
  | C => (.comp (.top p I a (some (.close p (.dom C) a))) (.pair (.id a) C), a, b)

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

def lFrac (R S : Pre × OTy × OTy) : M (Pre × OTy × OTy) := do
  let rs ← lRdiv I p R S; let sr ← lRdiv I p S R
  pure (meet rs.1 (lConv sr).1, rs.2.1, rs.2.2)

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

/-- `R+S` lifted: `R⟨π₁inl,π₂inl⟩ ∪ S⟨π₁inr,π₂inr⟩`. -/
def lSum : Pre × OTy × OTy → Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, c), (S, b, d) =>
    (join (comp R (pair (comp (outl a c) (inl a b)) (comp (outr a c) (inl c d))))
      (comp S (pair (comp (outl b d) (inr a b)) (comp (outr b d) (inr c d)))), .sum a b, .sum c d)

/-- The family `R : I ⟶ a×b` as one relation of the key and the source, `Rᴵ ≜ ⟨π₁R,π₂⟩dom(π₁π₁ ∩ π₂)π₁π₂ :
    I×a ⟶ b`. Every part runs on the keys in demand, so `I` needs no universe (a converse or `ran` here would
    close over all of `I`). -/
def keyed (R : Pre) (a b : OTy) : Pre :=
  let ab := OTy.prod a b
  comp (comp (pair (comp (outl I a) R) (outr I a)) (dom (meet (comp (outl ab a) (outl a b)) (outr ab a))))
    (comp (outl ab a) (outr a b))

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
    | .ni => (.conv (.close p (.mem b) (.arr b)), b, .arr b)
    | .outl => (.outl a b, .prod a b, a)
    | .outr => (.outr a b, .prod a b, b)
    | .inl => (.inl a b, a, .sum a b)
    | .inr => (.inr a b, b, .sum a b)
    | .leq => (.leq p a, a, a)
    | .lt => (.lt p a, a, a)
    | .succ => (.succ p a, a, a)
    | .plus => (.plus p a, .prod a a, a)
    | .union => (.union a, .arr (.arr a), .arr a)
    | .tau => (.tau a, a, .arr a)
    | .nil => (.nil a b, a, .arr b)
    | .alpha => (.junc (.close p (.nil a b) a) (.close p (.cons b) (.prod b (.arr b))), .sum a (.prod b (.arr b)), .arr b)
    | .cons => (.cons b, .prod b (.arr b), .arr b)
    | .length => (.length b a, .arr b, a)
    | .total => (.total a, .arr a, a)
    | .head => (.head b, .arr b, b)
    | .tail => (.tail b, .arr b, .arr b)
    | .pre => (.pre b, .arr b, .arr b)
    | .suf => (.suf b, .arr b, .arr b)
    | _ => (.id a, a, a)
  match objs with
  | [] => pure ()
  | [x] => unify p s!"the object of {o.sym}" s (← oty env [] x)
  | [x, y] => do unify p s!"the source of {o.sym}" s (← oty env [] x); unify p s!"the target of {o.sym}" t (← oty env [] y)
  | _ => throw ⟨p, s!"{o.sym} takes at most two objects, found {objs.length}"⟩
  pure (.rel q s t)

/-- A builtin applied to relations, every argument one relation. -/
def applied (p : Pos) (o : Op) : List (Pre × OTy × OTy) → M Arg
  | [(q, s, t)] => do
    match o with
    | .dom => pure (.rel (.dom q) s s)
    | .ran => pure (.rel (.ran (.close p q s)) t t)
    | .lam => pure (.rel (.lam q) s (.arr t))
    | .E => pure (.rel (.E q) (.arr s) (.arr t))
    | .map => pure (.rel (.map q) (.arr s) (.arr t))
    | .P => throw ⟨p, s!"P(R) : 𝒫{s} ⟶ 𝒫{t} has no universe on its target and no demand there (§a)"⟩
    | .est | .thin | .filter | .takewhile => do
      unify p s!"the target of {o.sym}'s argument" t s
      let c := Pre.close p q s
      let r : Pre × OTy := match o with
        | .est => (.est c, s) | .thin => (.thin c, .arr s) | .filter => (.filter c, .arr s) | _ => (.takewhile c, .arr s)
      pure (.rel r.1 (.arr s) r.2)
    | _ => throw ⟨p, s!"{o.sym} takes {(Op.table.find? (·.2.1 == o)).map (·.2.2) |>.getD 0} arguments, found 1"⟩
  | [(q, a, c), (r, b, c')] => do
    match o with
    | .frac => do
      unify p "the target of frac's second argument" c' c
      pure (.rel (.frac p (.close p q a) (.close p r b) a b) a b)
    | _ => throw ⟨p, s!"{o.sym} takes 1 argument, found 2"⟩
  | as => throw ⟨p, s!"{o.sym}: wrong number of arguments, found {as.length}"⟩

/-- A builtin applied with a family among its arguments, by the rows of §e. -/
def appliedL (I : OTy) (p : Pos) (o : Op) (as : List Arg) : M Arg := do
  let fs ← as.mapM (famOf I p)
  let r ← match o, fs with
    | .dom, [R] => pure (lDom R)
    | .ran, [R] => pure (lRan R)
    | .lam, [R] => pure (lLam I R)
    | .E, [R] => do let b ← fresh; pure (lLam I (← lComp p (liftConst I p (.mem b) (.arr b) b) R))
    | .frac, [R, S] => lFrac I p R S
    | .P, _ => notLiftable p "P(R)"
    | o, _ => notLiftable p s!"{o.sym}( )"
  pure (.fam r.1 I r.2.1 r.2.2)

/-- A binary operator on one relation each side. -/
def binary (p : Pos) (o : Bin) : Pre × OTy × OTy → Pre × OTy × OTy → M Arg
  | (q, s, t), (r, s', t') => do
    match o with
    | .meet | .join | .diff | .imp => do
      unify p s!"the source of {o.sym}'s right operand" s' s; unify p s!"the target of {o.sym}'s right operand" t' t
      let x := match o with
        | .meet => Pre.meet q r | .join => .join q r | .diff => .diff q r
        | _ => .join (.diff (.top p s t none) q) r
      pure (.rel x s t)
    | .rdiv => do unify p "the target of `/`'s right operand" t' t; pure (.rel (.rdiv p (.close p q s) (.close p r s') s s') s s')
    | .ldiv => do unify p "the source of `\\`'s right operand" s' s; pure (.rel (.ldiv p (.close p q s) (.close p r s) t t') t t')
    | .prod => pure (.rel (.prod (.close p q s) (.close p r s')) (.prod s s') (.prod t t'))
    | .sum => pure (.rel (.sum (.close p q s) (.close p r s')) (.sum s s') (.sum t t'))

/-- A binary operator with a family on a side, by the rows of §e. -/
def binaryL (I : OTy) (p : Pos) (o : Bin) (x y : Arg) : M Arg := do
  let R ← famOf I p x; let S ← famOf I p y
  let r ← match o with
    | .meet => lSame p Pre.meet R S
    | .join => lSame p Pre.join R S
    | .diff => lSame p Pre.diff R S
    | .imp => lSame p Pre.join (lCompl I p R) S
    | .rdiv => lRdiv I p R S
    | .ldiv => lLdiv I p R S
    | .prod => pure (lProd R S)
    | .sum => pure (lSum R S)
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
    match a with
    | .op _ .cons [] [] => do let b ← fresh; pure (.rel (.uncons b) (.arr b) (.prod b (.arr b)))
    | _ =>
      match ← elabE env m a with
      | .fam q i s t => let r := lConv (q, s, t); pure (.fam r.1 i r.2.1 r.2.2)
      | .rel q s t => pure (.rel (.conv (.close p q s)) t s)
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
      pure (.rel (.junc (.close p q s) (.close p r s')) (.sum s s') t)
  | .fold p a b => do
    let x ← elabE env m a; let y ← elabE env m b
    if x.isFam || y.isFam then
      throw ⟨p, "⦇e,S⦈ given a family is not liftable on its own: its arrays come from its left, X⦇e,S⦈ (§e)"⟩
    let (q, v, v') := x.plain; let (r, ev, w) := y.plain
    unify p "the fold's start, a coreflexive" v' v
    let e ← fresh
    unify p "the source of the fold's step" ev (.prod e v)
    unify p "the target of the fold's step" w v
    pure (.rel (.fold (.close p q v) r) (.arr e) v)
  | .lit p ps => do
    -- a side is the one declared object holding all its words: named elements, or numbers in its range
    let holds (i : ObjInfo) (w : String) : Bool := i.elems.contains w ||
      match i.range, w.toNat? with | some (lo, hi), some k => lo ≤ k && k ≤ hi | _, _ => false
    let side (ws : List String) : M OTy := do
      match env.objs.filter (fun (_, i) => ws.all (holds i)) with
      | [(n, _)] => pure (.base n)
      | [] => throw ⟨p, s!"no declared object has the elements {ws}"⟩
      | os => throw ⟨p, s!"the elements {ws} are in {os.map (·.1)}; write the literal after its object"⟩
    let a ← side (ps.map (·.1)); let b ← side (ps.map (·.2))
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

/-- A definition with parameters: its body elaborated at each use, lifted when a declared parameter is given
    a family; a test `e ⊑ f` is the coreflexive `D − dom(R − S)` of the keys whose fibres pass. -/
def mkDef (env : Env) (dp : Pos) (ps : List Param) (body : Body) : Def where
  arity := ps.length
  apply p args := do
    -- one instantiation of the object variables per use, shared by the parameters left to right (§e)
    let (bs, _) ← (ps.zip args).foldlM (fun (bs, vs) (P, a) => do
      let (b, j, vs) ← bind env p P a vs; pure (bs ++ [(b, j)], vs)) ([], [])
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
    | .rel e, none => elabE env' none e
    | .rel e, some I => do
      let r ← famOf I p (← elabE env' (some I) e)
      pure (.fam r.1 I r.2.1 r.2.2)
    | .test _ _, none => throw ⟨p, s!"the test defined at {dp} needs a family; write `check` for one relation"⟩
    | .test e f, some I => do
      let R ← famOf I p (← elabE env' (some I) e)
      let S ← famOf I p (← elabE env' (some I) f)
      let (d, _) ← lSame p Pre.diff R S
      pure (.rel (.diff (.id I) (.dom d)) I I)

/-! ### Build: the solved objects, the core term -/

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

/-- The universe of a declared base object, for `succ plus ≤ <`. -/
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
    | some i => match i.range, i.elems.idxOf? w, w.toNat? with
      | some (lo, hi), _, some k => if lo ≤ k ∧ k ≤ hi then pure (Int64.ofNat k)
          else throw ⟨p, s!"{w} is not in {n} = {lo}…{hi}"⟩
      | none, some k, _ => pure (Int64.ofNat k)
      | _, _, _ => throw ⟨p, s!"'{w}' is not an element of {n}"⟩
    | none => throw ⟨p, s!"unknown object '{n}'"⟩
  | o => throw ⟨p, s!"a literal relates elements of declared objects, found {o}"⟩

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
  | .conv p => do let r ← build p; let ⟨A, B, _, _⟩ := r; pure ⟨B, A, false, .conv (← closed? dp (A := A) (B := B) r)⟩
  | .meet p q => do let ⟨A, B, _, t⟩ ← build p; let ⟨_, u⟩ ← at? dp (A := A) (B := B) (← build q); pure ⟨A, B, _, .meet t u⟩
  | .join p q => do let ⟨A, B, _, t⟩ ← build p; let ⟨_, u⟩ ← at? dp (A := A) (B := B) (← build q); pure ⟨A, B, _, .join t u⟩
  | .diff p q => do let ⟨A, B, _, t⟩ ← build p; let ⟨_, u⟩ ← at? dp (A := A) (B := B) (← build q); pure ⟨A, B, _, .diff t u⟩
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
  | .frac pos p q a b => do
    let r ← build p; let s ← build q; let ⟨A, C, _, _⟩ := r; let ⟨B, _, _, _⟩ := s
    let R ← closed? dp (A := A) (B := C) r; let S ← closed? dp (A := B) (B := C) s
    pure ⟨A, B, false, .frac R S (← uniTm objs st dp pos a A "frac") (← uniTm objs st dp pos b B "frac")⟩
  | .pair p q => do
    let ⟨A, _, _, t⟩ ← build p; let s ← build q; let ⟨_, C, _, _⟩ := s
    let ⟨_, u⟩ ← at? dp (A := A) (B := C) s; pure ⟨A, _, _, .pair t u⟩
  | .prod p q => do
    let r ← build p; let s ← build q; let ⟨A, B, _, _⟩ := r; let ⟨C, D, _, _⟩ := s
    pure ⟨_, _, false, .prod (← closed? dp (A := A) (B := B) r) (← closed? dp (A := C) (B := D) s)⟩
  | .junc p q => do
    let r ← build p; let s ← build q; let ⟨A, C, _, _⟩ := r; let ⟨B, _, _, _⟩ := s
    pure ⟨_, _, false, .junc (← closed? dp (A := A) (B := C) r) (← closed? dp (A := B) (B := C) s)⟩
  | .sum p q => do
    let r ← build p; let s ← build q; let ⟨A, C, _, _⟩ := r; let ⟨B, D, _, _⟩ := s
    pure ⟨_, _, false, .sum (← closed? dp (A := A) (B := C) r) (← closed? dp (A := B) (B := D) s)⟩
  | .lam p => do let ⟨_, _, _, t⟩ ← build p; pure ⟨_, _, _, .lam t⟩
  | .E p => do let ⟨_, _, _, t⟩ ← build p; pure ⟨_, _, _, .E t⟩
  | .map p => do let ⟨_, _, _, t⟩ ← build p; pure ⟨_, _, _, .map t⟩
  | .est p => do let r ← build p; let ⟨B, _, _, _⟩ := r; pure ⟨_, _, _, .est (← closed? dp (A := B) (B := B) r)⟩
  | .thin p => do let r ← build p; let ⟨B, _, _, _⟩ := r; pure ⟨_, _, _, .thin (← closed? dp (A := B) (B := B) r)⟩
  | .filter p => do let r ← build p; let ⟨B, _, _, _⟩ := r; pure ⟨_, _, _, .filter (← closed? dp (A := B) (B := B) r)⟩
  | .takewhile p => do
    let r ← build p; let ⟨B, _, _, _⟩ := r; pure ⟨_, _, _, .takewhile (← closed? dp (A := B) (B := B) r)⟩
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
  | .head b => return ⟨_, _, true, .head (B := ← toObj st dp b)⟩
  | .tail b => return ⟨_, _, true, .tail (B := ← toObj st dp b)⟩
  | .pre b => return ⟨_, _, true, .pre (B := ← toObj st dp b)⟩
  | .suf b => return ⟨_, _, true, .suf (B := ← toObj st dp b)⟩
  | .succ p n => do let ⟨_, U⟩ ← numU objs st p n "succ"; pure ⟨_, _, true, .succ U⟩
  | .plus p n => do let ⟨_, U⟩ ← numU objs st p n "plus"; pure ⟨_, _, true, .plus U⟩
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
  | .lit p a b ps => do
    let cs ← ps.mapM fun (x, y) => return (← code objs st p a x, ← code objs st p b y)
    pure ⟨.long, .long, false, .val (ofPairs cs)⟩
  | .close p q a => do
    let ⟨A, B, d, t⟩ ← build q
    match d with
    | false => pure ⟨A, B, false, t⟩
    | true => pure ⟨A, B, false, .comp (← uniTm objs st dp p a A "the term here needs keys and has no left context") t⟩

end Build

end LeetQ.Rel.Lang
