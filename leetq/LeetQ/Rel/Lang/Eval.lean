import Std.Data.HashMap
import LeetQ.Rel.Lang.Elab
import LeetQ.Rel.Lang.Parse

/-! The evaluator of the Rel language: a core term to a relation by `Alg`'s ops, and the program run
    declaration by declaration. `ev` has no error path: the term's indices are its objects, and a term that
    runs on demand (§a) receives its keys by its type, `Dem true A`. Equal sub-terms are evaluated once: `hoist`
    gives every sub-term an identity, structurally, and `ev` keeps each shared identity's value per demand. -/

namespace LeetQ.Rel.Lang

open LeetQ.Rel LeetQ.Rel.Alg

deriving instance Hashable for QLean.QAtomicType
deriving instance Hashable for LeetQ.Rel.Obj

/-- The keys a term reads: a coreflexive when it runs on demand, nothing when it is closed. -/
@[reducible] def Dem : Bool → Obj → Type
  | true, A => Rel A A
  | false, _ => Unit

def Dem.of {A : Obj} : (d : Bool) → Rel A A → Dem d A
  | true, D => D
  | false, _ => ()

def Dem.l {A : Obj} : (d e : Bool) → Dem (d || e) A → Dem d A
  | true, _, D => D
  | false, _, _ => ()

def Dem.r {A : Obj} : (d e : Bool) → Dem (d || e) A → Dem e A
  | _, false, _ => ()
  | true, true, D => D
  | false, true, D => D

/-- A relation with its objects. -/
abbrev Val := (A : Obj) × (B : Obj) × Rel A B

/-- The relation at the objects `A ⟶ B`, when those are its objects. -/
def Val.at? (A B : Obj) : Val → Option (Rel A B)
  | ⟨A', B', R⟩ => if h : A' = A ∧ B' = B then some (h.1 ▸ h.2 ▸ R) else none

/-- What one evaluation has computed of the shared sub-terms: per identity, each demand with its value. -/
abbrev Memo := Std.HashMap Nat (Array ((A : Obj) × Rel A A × Val))

abbrev EvM := StateM Memo

/-- `t` on the keys `D`: exact at every key of `D`; a closed term ignores `D`. In `RS`, `S` runs on `ran(R)`.
    A sub-term `.share k` whose identity occurs more than once (`cnt`) runs once per demand. -/
def ev (cnt : Array Nat) : {A B : Obj} → {d : Bool} → Tm A B d → Dem d A → EvM (Rel A B)
  | _, _, _, .val R, _ => pure R
  | _, _, _, .uni U, _ => pure (idU U)
  | _, _, _, .zero, _ => pure zero
  | _, _, _, .id, D => pure D
  | _, _, _, .top V, D => return top D.val (← ev cnt V ()).val
  | _, _, _, .mem, D => pure (mem D.val)
  | _, _, _, .outl, D => pure (outl D)
  | _, _, _, .outr, D => pure (outr D)
  | _, _, _, .inl, D => pure (inl D.val)
  | _, _, _, .inr, D => pure (inr D.val)
  | _, _, _, .comp (e := e) R S, D => do let r ← ev cnt R D; return r ≫ (← ev cnt S (Dem.of e (ran r)))
  | _, _, _, .conv R, _ => return (← ev cnt R ())°
  | _, _, _, .meet (d := d) (e := e) R S, D => return (← ev cnt R (Dem.l d e D)) ∩ (← ev cnt S (Dem.r d e D))
  | _, _, _, .join (d := d) (e := e) R S, D => return (← ev cnt R (Dem.l d e D)) ∪ (← ev cnt S (Dem.r d e D))
  | _, _, _, .diff (d := d) (e := e) R S, D => return (← ev cnt R (Dem.l d e D)) \ (← ev cnt S (Dem.r d e D))
  | _, _, _, .dom R, D => return dom (← ev cnt R D)
  | _, _, _, .ran R, _ => return ran (← ev cnt R ())
  | _, _, _, .ldiv R S UB UC, _ =>
    return leftDiv (← ev cnt R ()) (← ev cnt S ()) (← ev cnt UB ()).val (← ev cnt UC ()).val
  | _, _, _, .rdiv R S UA UB, _ =>
    return rightDiv (← ev cnt R ()) (← ev cnt S ()) (← ev cnt UA ()).val (← ev cnt UB ()).val
  | _, _, _, .pair (d := d) (e := e) R S, D => return pair (← ev cnt R (Dem.l d e D)) (← ev cnt S (Dem.r d e D))
  | _, _, _, .prod R S, _ => return Alg.prod (← ev cnt R ()) (← ev cnt S ())
  | _, _, _, .junc R S, _ => return junc (← ev cnt R ()) (← ev cnt S ())
  | _, _, _, .lam R, D => do let r ← ev cnt R D; pure Λ(r)
  | _, _, _, .E (d := d) R, D => return E (← ev cnt R (Dem.of d (ran (mem D.val)))) D.val
  | _, _, _, .map (d := d) R, D => return map (← ev cnt R (Dem.of d (ran (mem D.val)))) D.val
  -- an order is its pair test, run on the pairs the operator compares: each call one evaluation, as a fold step
  | _, _, _, .est Q, D => pure (estOn (fun P => Id.run ((ev cnt Q P).run' {})) (mem D.val))
  | _, _, _, .thin Q, D => do
    let T := thinOn (fun P => Id.run ((ev cnt Q P).run' {})) (mem D.val); pure (Λ(T) ∪ top (D \ dom T).key (nilVal _))
  | _, _, _, .union, D => pure (Arr.union D.val)
  | _, _, _, .tau, D => pure (τ D.val)
  | _, _, _, .nil, D => pure (top D.val (nilVal _))
  | _, _, _, .cons, D => pure (cons D)
  | _, _, _, .uncons, D => pure (uncons D.val)
  | _, _, _, .length, D => pure (length D.val)
  | _, _, _, .total, D => pure (Arr.sum D.val)
  | _, _, _, .inits, D => pure (Alg.inits D.val)
  | _, _, _, .cat, D => pure (Alg.cat D)
  | _, _, _, .uncat, D => pure (Alg.uncat D.val)
  | _, _, _, .zip, D => pure (Alg.zip D)
  | _, _, _, .snoc, D => pure (Alg.snoc D)
  | _, _, _, .unsnoc, D => pure (Alg.unsnoc D.val)
  | _, _, _, .own R, D => ev cnt R D
  | _, _, _, .setify, D => pure (Alg.setify D.val)
  | _, _, _, .bagify, D => pure (Alg.bagify D.val)
  | _, _, _, .tic, D => pure (Alg.tic D)
  -- the note's one-pass thinning, which refines the specification `Alg.thinL`
  | _, _, _, .thinL Q, D => pure (thinLOn (fun P => Id.run ((ev cnt Q P).run' {})) D.val)
  | _, _, _, .merge Q, D => pure (mergeOn (fun P => Id.run ((ev cnt Q P).run' {})) D)
  -- one loop round's `F` is one evaluation, as a fold step's
  | _, _, _, .loop (d := d) F, D => pure (loopOn (fun A => Id.run ((ev cnt F (Dem.of d A)).run' {})) D)
  | _, _, _, .succ U, D => pure (D ≫ succ U)
  -- a result outside the declared object has no row, as `succ` at its top
  | _, _, _, .arith k U, D => pure (arith k D.val ≫ idU U)
  | _, _, _, .leq U, _ => pure (leq U)
  | _, _, _, .lt U, _ => pure (lt U)
  -- one fold step is one evaluation: what it shares, it shares within the step
  | _, _, _, .fold (d := d) e S, D => do
    let v ← ev cnt e ()
    pure (foldOn v.val (fun A => Id.run ((ev cnt S (Dem.of d A)).run' {})) D.val)
  -- the pairs (i, xs) in demand: each key's seed `(i,v)` from `e`, one fold of the arrays on `I×V`, then each
  -- pair keeps the values its own key reached: `G : [E] ⟶ I×V` re-keyed by `(i,xs)`, a join, where pairing each
  -- pair with every key's values of its array grows as the keys squared
  | _, _, _, .foldI (d := d) (d' := d') e S, D => do
    let es ← ev cnt e (Dem.of d (ran (outl D)))
    let iv := pair (dom es) (es ≫ outl (ran es))
    let G := foldOn (ran iv).val (fun A => Id.run ((ev cnt S (Dem.of d' A)).run' {})) (ran (outr D)).val
    let U := ran G
    pure (D ≫ ((pair (outl U) G°)° ≫ outr U))
  -- `R` at the keys of the pairs, its rows `(i,(a,b))` re-keyed as `((i,a),b)`, a join with the pairs: no pair
  -- meets a row of another source
  | _, _, _, .flat (d := d) R, D => do
    let r ← ev cnt R (Dem.of d (ran (outl D)))
    let U := ran r
    pure (D ≫ ((pair r° (outl U))° ≫ outr U))
  | _, _, false, .share _ R, D => ev cnt R D
  | A, B, true, .share k R, D => do
    if cnt.getD k 0 < 2 then ev cnt R D else
    let hit := ((← get).getD k #[]).findSome? fun ⟨A', D', v⟩ =>
      if h : A' = A then (let D'' : Rel A A := h ▸ D'; if D''.n == D.n && D'' == D then v.at? A B else none)
      else none
    match hit with
    | some V => pure V
    | none => do
      let V ← ev cnt R D
      modify fun m => m.insert k ((m.getD k #[]).push ⟨A, D, ⟨A, B, V⟩⟩)
      pure V

/-! ### Sharing: every sub-term an identity, structurally -/

/-- A node's identity: its constructor, its objects, and the identities of its parts. -/
structure Key where
  tag : Nat
  src : Obj
  tgt : Obj
  parts : List Nat
  deriving BEq, Hashable

/-- The program's sub-terms: each identity, how often it occurs, the leaf values, the closed ones' values. -/
structure Share where
  ids : Std.HashMap Key Nat := {}
  cnt : Array Nat := #[]
  leaves : Array (Val × Nat) := #[]
  vals : Std.HashMap Nat Val := {}

abbrev HM := StateM Share

def intern (k : Key) : HM Nat := modifyGet fun s => match s.ids[k]? with
  | some i => (i, { s with cnt := s.cnt.modify i (· + 1) })
  | none => (s.cnt.size, { s with ids := s.ids.insert k s.cnt.size, cnt := s.cnt.push 1 })

/-- A value's identity: relations of one type and row count, equal as sets, are one leaf. -/
def leaf {A B : Obj} (R : Rel A B) : HM Nat := do
  let found := (← get).leaves.findSome? fun (v, i) =>
    (v.at? A B).bind fun S => if S.n == R.n && S == R then some i else none
  match found with
  | some i => pure i
  | none => modifyGet fun s => (s.leaves.size, { s with leaves := s.leaves.push (⟨A, B, R⟩, s.leaves.size) })

/-- The node `t` of parts `ps`, interned: a closed one becomes its value, computed once per identity; a composite
    one on demand is marked with its identity, so `ev` runs it once per demand. -/
def node {A B : Obj} {d : Bool} (tag : Nat) (t : Tm A B d) (ps : List Nat) : HM (Tm A B d × Nat) := do
  let k ← intern ⟨tag, A, B, ps⟩
  match d, t with
  | true, t => pure (if ps.isEmpty then t else .share k t, k)
  | false, .val R => pure (.val R, k)
  | false, t =>
    match ((← get).vals[k]?).bind (Val.at? A B) with
    | some R => pure (.val R, k)
    | none => do
      let R := Id.run ((ev (← get).cnt t ()).run' {})
      modify fun s => { s with vals := s.vals.insert k ⟨A, B, R⟩ }
      pure (.val R, k)

/-- Every sub-term interned bottom up: closed ones evaluated once per identity, so a fold's step recomputes only
    what reads the round's pairs, and equal sub-terms on demand marked to run once per demand. -/
def hoist : {A B : Obj} → {d : Bool} → Tm A B d → HM (Tm A B d × Nat)
  | _, _, _, .val R => do node 0 (.val R) [← leaf R]
  | _, _, _, .uni U => do node 1 (.uni U) [← leaf (idU U)]
  | _, _, _, .zero => node 2 .zero []
  | _, _, _, .id => node 3 .id []
  | _, _, _, .top V => do let (v, i) ← hoist V; node 4 (.top v) [i]
  | _, _, _, .mem => node 5 .mem []
  | _, _, _, .outl => node 6 .outl []
  | _, _, _, .outr => node 7 .outr []
  | _, _, _, .inl => node 8 .inl []
  | _, _, _, .inr => node 9 .inr []
  | _, _, _, .comp R S => do let (r, i) ← hoist R; let (s, j) ← hoist S; node 10 (.comp r s) [i, j]
  | _, _, _, .conv R => do let (r, i) ← hoist R; node 11 (.conv r) [i]
  | _, _, _, .meet R S => do let (r, i) ← hoist R; let (s, j) ← hoist S; node 12 (.meet r s) [i, j]
  | _, _, _, .join R S => do let (r, i) ← hoist R; let (s, j) ← hoist S; node 13 (.join r s) [i, j]
  | _, _, _, .diff R S => do let (r, i) ← hoist R; let (s, j) ← hoist S; node 14 (.diff r s) [i, j]
  | _, _, _, .dom R => do let (r, i) ← hoist R; node 15 (.dom r) [i]
  | _, _, _, .ran R => do let (r, i) ← hoist R; node 16 (.ran r) [i]
  | _, _, _, .ldiv R S U V => do
    let (r, i) ← hoist R; let (s, j) ← hoist S; let (u, k) ← hoist U; let (v, l) ← hoist V
    node 17 (.ldiv r s u v) [i, j, k, l]
  | _, _, _, .rdiv R S U V => do
    let (r, i) ← hoist R; let (s, j) ← hoist S; let (u, k) ← hoist U; let (v, l) ← hoist V
    node 18 (.rdiv r s u v) [i, j, k, l]
  | _, _, _, .pair R S => do let (r, i) ← hoist R; let (s, j) ← hoist S; node 20 (.pair r s) [i, j]
  | _, _, _, .prod R S => do let (r, i) ← hoist R; let (s, j) ← hoist S; node 21 (.prod r s) [i, j]
  | _, _, _, .junc R S => do let (r, i) ← hoist R; let (s, j) ← hoist S; node 22 (.junc r s) [i, j]
  | _, _, _, .lam R => do let (r, i) ← hoist R; node 24 (.lam r) [i]
  | _, _, _, .E R => do let (r, i) ← hoist R; node 25 (.E r) [i]
  | _, _, _, .map R => do let (r, i) ← hoist R; node 26 (.map r) [i]
  | _, _, _, .est Q => do let (q, i) ← hoist Q; node 27 (.est q) [i]
  | _, _, _, .thin Q => do let (q, i) ← hoist Q; node 28 (.thin q) [i]
  | _, _, _, .union => node 31 .union []
  | _, _, _, .tau => node 32 .tau []
  | _, _, _, .nil => node 33 .nil []
  | _, _, _, .cons => node 34 .cons []
  | _, _, _, .uncons => node 35 .uncons []
  | _, _, _, .length => node 36 .length []
  | _, _, _, .total => node 37 .total []
  | _, _, _, .succ U => do node 42 (.succ U) [← leaf (idU (t := .long) U)]
  -- the verb is a part, so `plus` and `times` on one universe are two identities
  | _, _, _, .arith k U => do node 43 (.arith k U) [← leaf (idU (t := .long) U), k.toNat]
  | _, _, _, .leq U => do node 44 (.leq U) [← leaf (idU (t := .long) U)]
  | _, _, _, .lt U => do node 45 (.lt U) [← leaf (idU (t := .long) U)]
  | _, _, _, .fold e S => do let (x, i) ← hoist e; let (s, j) ← hoist S; node 46 (.fold x s) [i, j]
  | _, _, _, .foldI e S => do let (x, i) ← hoist e; let (s, j) ← hoist S; node 47 (.foldI x s) [i, j]
  | _, _, _, .flat R => do let (r, i) ← hoist R; node 48 (.flat r) [i]
  | _, _, _, .inits => node 49 .inits []
  | _, _, _, .cat => node 51 .cat []
  | _, _, _, .uncat => node 52 .uncat []
  | _, _, _, .zip => node 53 .zip []
  | _, _, _, .snoc => node 54 .snoc []
  | _, _, _, .unsnoc => node 55 .unsnoc []
  | _, _, _, .own R => do let (r, i) ← hoist R; node 58 (.own r) [i]
  | _, _, _, .setify => node 59 .setify []
  | _, _, _, .bagify => node 60 .bagify []
  | _, _, _, .tic => node 62 .tic []
  | _, _, _, .thinL Q => do let (q, i) ← hoist Q; node 65 (.thinL q) [i]
  | _, _, _, .merge Q => do let (q, i) ← hoist Q; node 66 (.merge q) [i]
  | _, _, _, .loop F => do let (f, i) ← hoist F; node 67 (.loop f) [i]
  -- a definition's term, interned when the definition was
  | _, _, _, .share k R => pure (.share k R, k)

/-- A closed term's value: hoisted into the program's table, then evaluated. -/
def value {A B : Obj} (sh : Share) (t : Tm A B false) : Rel A B × Share :=
  let ((t, _), sh) := Id.run ((hoist t).run sh)
  (Id.run ((ev sh.cnt t ()).run' {}), sh)

/-! ### Running a program -/

/-- An array of the printed elements `xs`, as a literal's side reads it (§c): two or more juxtaposed, else
    bracketed; `item`: it stands next to others (in an array, after `inl`), so it is always bracketed. -/
def arrText (item : Bool) (xs : List String) : String :=
  let s := " ".intercalate xs; if item || xs.length < 2 then s!"[{s}]" else s

/-- An element printed with the program's names, as a literal's side reads it (§c): a named element by its name,
    a number as itself, an array by `arrText`, its elements as items. -/
def showEl (objs : Objs) (item : Bool) : OTy → (A : Obj) → A.El → String
  | .base n, .atom .long, x =>
    let v : Int64 := x
    match objs.lookup n with
    | some i => if i.range.isSome then toString v else (i.elems[v.toInt.toNat]?).getD (toString v)
    | none => toString v
  | .prod a b, .prod A B, (x, y) => s!"({showEl objs false a A x}, {showEl objs false b B y})"
  | .sum a _, .sum A _, .inl x => s!"inl {showEl objs true a A x}"
  | .sum _ b, .sum _ B, .inr y => s!"inr {showEl objs true b B y}"
  | .arr a, .arr A, xs => arrText item (xs.map (showEl objs true a A))
  | _, _, _ => "?"

/-- The order a print lists elements in: a number by its value (`-2` before `-1`, `2` before `10`), a named
    element by its name, a pair and an array lexicographically, `inl` before `inr`. -/
def cmpEl (objs : Objs) : OTy → (A : Obj) → A.El → A.El → Ordering
  | .base n, .atom .long, x, y =>
    let (v, w) : Int64 × Int64 := (x, y)
    if ((objs.lookup n).bind (·.range)).isSome then compare v.toInt w.toInt
    else compare (showEl objs false (.base n) (.atom .long) x) (showEl objs false (.base n) (.atom .long) y)
  | .prod a b, .prod A B, (x, y), (x', y') => (cmpEl objs a A x x').then (cmpEl objs b B y y')
  | .sum a _, .sum A _, .inl x, .inl y => cmpEl objs a A x y
  | .sum _ b, .sum _ B, .inr x, .inr y => cmpEl objs b B x y
  | .sum _ _, .sum _ _, .inl _, .inr _ => .lt
  | .sum _ _, .sum _ _, .inr _, .inl _ => .gt
  | .arr a, .arr A, xs, ys =>
    let (xs, ys) : List A.El × List A.El := (xs, ys)
    ((xs.zip ys).foldl (fun (o : Ordering) (x, y) => o.then (cmpEl objs a A x y)) Ordering.eq).then (compare xs.length ys.length)
  | s, A, x, y => compare (showEl objs false s A x) (showEl objs false s A y)

/-- A relation printed as its set of pairs, sorted by `cmpEl`. -/
def showRel (objs : Objs) (s t : OTy) {A B : Obj} (R : Rel A B) : String :=
  let ps := R.nub.toList.mergeSort fun (x, y) (x', y') => ((cmpEl objs s A x x').then (cmpEl objs t B y y')) != .gt
  "{" ++ ", ".intercalate (ps.map fun (x, y) => s!"({showEl objs false s A x}, {showEl objs false t B y})") ++ "}"

/-- An object with a variable left in it. -/
def OTy.poly : OTy → Bool
  | .mv _ => true
  | .prod a b | .sum a b => a.poly || b.poly
  | .arr a => a.poly
  | .base _ => false

structure Out where
  /-- Every closed definition's value, with its objects as the program names them. -/
  vals : List (String × Val × OTy × OTy) := []
  /-- The text of each `print`. -/
  prints : List String := []
  /-- Each definition's declaration, as `rel --types` prints it. -/
  sigs : List String := []
  objs : Objs := []

/-- A top-level term's value: on its source's universe when it needs keys. -/
def topVal (sh : Share) (env : Env) (p : Pos) (e : Expr) : Except Err ((Val × OTy × OTy) × Share) := do
  let (r, st) ← (elabE env none e).run {}
  let (q, s, t) := r.plain
  let ⟨A, B, d, tm⟩ ← build env.objs st p (.close p q s noLeft)
  match d, tm with
  | false, tm => let (R, sh) := value sh tm; pure ((⟨A, B, R⟩, zonk st s, zonk st t), sh)
  | true, _ => throw ⟨p, s!"{e.show}: {zonk st s} has no universe; compose a set of its elements before it (§a)"⟩

def objInfo (env : Env) (n : String) : ObjDef → Except Err ObjInfo
  | .elems ws => pure { ty := .base n, elems := ws, uni := some ⟨_, col ((List.range ws.length).map Int64.ofNat)⟩ }
  | .range lo hi =>
    pure { ty := .base n, range := some (lo, hi), uni := some ⟨_, col ((List.range (hi + 1 - lo).toNat).map fun k : Nat => Int64.ofInt (lo + k))⟩ }
  | .alias o => do let (t, _) ← (oty env [] o).run {}; pure { ty := t }

/-- Run a program: each declaration in order; a definition with no parameters is built once and, when it is
    closed or its source has a universe, evaluated once into a value its users share. One sharing table runs
    through the program, so a sub-term met in several definitions has one identity. `types`: only the
    definitions are checked, nothing is evaluated (`rel --types`). -/
def run (prog : Program) (start : Env × Out × Share := ({}, {}, {})) (wrap : String → Def → Def := fun _ d => d)
    (types : Bool := false) : Except Err (Env × Out × Share) := do
  let (env₀, out₀, sh₀) := start
  let mut env := env₀
  let mut out := out₀
  let mut sh := sh₀
  for d in prog do
    match d with
    | .obj _ n od => env := { env with objs := (n, ← objInfo env n od) :: env.objs }
    | .defn p n ps b ty =>
      -- a relation declares its type and every parameter its own (§e); a test has none of its own
      let missing := ps.any (·.ty.isNone) || match b with | .rel _ => ty.isNone | .test .. => false
      if missing then throw ⟨p, s!"`{n}` has no type; it is {← (inferSig env n ps b).run' {}}"⟩
      out := { out with sigs := out.sigs ++ [sigOf n ps ty] }
      match ps, b, ty with
      | [], .rel e, ty =>
        -- the declared type checked with its variables held apart (`α` matches only itself), so the body has it
        -- at every object a use gives them
        let rigid := match ty with | some (a, b) => (a.vars ++ b.vars).map fun v => (v, OTy.base v) | none => []
        let (r, st) ← (do
          let r ← elabE env none e
          if let some ty := ty then let (_, s, t) := r.plain; declared env p n rigid ty s t
          pure r).run {}
        let (q, s, t) := r.plain
        let s := zonk st s; let t := zonk st t
        let each := wrap n (mkDef env n p [] (.rel e) ty)
        -- a declared object variable, or objects its body leaves open (`≼` on any `A×B`), are fixed at each use,
        -- as a parameter's are
        if !rigid.isEmpty || s.poly || t.poly then env := { env with defs := (n, each) :: env.defs }; continue
        let q := if (uniOf env.objs s).isSome then Pre.close p q s noLeft else q
        -- a body that runs only as a pair test (`length ≤ length°`) is an order: elaborated again at each use
        let ⟨A, B, d, tm⟩ ← match build env.objs st p q, test env.objs st p q with
          | .ok r, _ => pure r
          | .error _, .ok _ => env := { env with defs := (n, each) :: env.defs }; continue
          | .error e, .error _ => throw e
        let ((tm, _), sh') := Id.run ((hoist tm).run sh)
        sh := sh'
        let res : Res := ⟨A, B, d, tm⟩
        env := { env with defs := (n, wrap n { arity := 0, apply := fun _ _ => pure (.rel (.tm res) s t) }) :: env.defs }
        match d, tm, types with
        | false, tm, false => out := { out with vals := (n, ⟨A, B, Id.run ((ev sh.cnt tm ()).run' {})⟩, s, t) :: out.vals }
        | _, _, _ => pure ()
      | ps, b, ty => env := { env with defs := (n, wrap n (mkDef env n p ps b ty)) :: env.defs }
    | .print p e =>
      if types then continue
      let ((⟨_, _, R⟩, s, t), sh') ← topVal sh env p e
      sh := sh'
      out := { out with prints := out.prints ++ [s!"{e.show} = {showRel env.objs s t R}"] }
    | .check p e f eq =>
      if types then continue
      let ((⟨A, B, R⟩, s, t), sh₁) ← topVal sh env p e
      let ((⟨A', B', S⟩, s', t'), sh₂) ← topVal sh₁ env p f
      sh := sh₂
      if h : A' = A ∧ B' = B then
        let S : Rel A B := h.2 ▸ h.1 ▸ S
        if !(R ⊑ S && (!eq || S ⊑ R)) then
          throw ⟨p, s!"check failed: {e.show} = {showRel env.objs s t R}, {f.show} = {showRel env.objs s t S}"⟩
      else throw ⟨p, s!"check: the sides have types {s} ⟶ {t} and {s'} ⟶ {t'}"⟩
  pure (env, { out with objs := env.objs }, sh)

/-- A prelude definition as a program sees it: an error raised in its body at a use names the definition and its
    line in the prelude, at the use; one about the arguments (at the use) passes as it is. `perm` is its own
    converse, the one converse rule kept for a definition (`Tm.own`): `perm° = perm` is a theorem the
    language cannot derive from the fold `perm` is. -/
def preludeDef (n : String) (d : Def) : Def :=
  { d with apply := fun p as => do
      let r ← tryCatch (d.apply p as) fun e =>
        throw (if e.pos == p then e else ⟨p, s!"in the prelude's `{n}` (its line {e.pos.line}): {e.msg}"⟩)
      -- the body's positions are the prelude's: at the use, so what `build` raises later is at the use
      match n, r with
      | "perm", .rel q s t => pure (.rel (.own (q.at p)) s t)
      | _, .rel q s t => pure (.rel (q.at p) s t)
      | _, .fam q i a b => pure (.fam (q.at p) i a b) }

/-- Run the program `prog` reads in the prelude `pre`'s scope, after `pre`: one environment and one sharing table
    through both. An error of the prelude's own text says it is in the prelude. -/
def runAfter (pre : String) (prog : Parse.S → Except Err Program) : Except Err Out := do
  let (pp, scope) ← Parse.scope pre
  let (env, out, sh) ← (run pp ({}, {}, {}) preludeDef).mapError Err.inPrelude
  let (_, out, _) ← run (← prog scope) (env, out, sh)
  pure out

/-- Parse and run a program's text after the prelude `pre`. -/
def runWith (pre src : String) : Except Err Out := runAfter pre (Parse.parseIn · src)

/-- Parse and run a program's text, after the prelude. -/
def runText (src : String) : Except Err Out := runWith Parse.prelude src

/-- `rel --types`: the declaration of each definition of the program `src`, in order, nothing evaluated; with no
    program, the prelude's. -/
def typesOf (src : Option String) : Except Err (List String) := do
  let (pp, scope) ← Parse.scope Parse.prelude
  let (env, out, sh) ← (run pp ({}, {}, {}) preludeDef (types := src.isNone)).mapError Err.inPrelude
  match src with
  | none => pure out.sigs
  | some s => do
    let (_, o, _) ← run (← Parse.parseIn scope s) (env, { out with sigs := [] }, sh) (types := true)
    pure o.sigs

/-- Run a parsed program (`Parse.parse`), after the prelude. -/
def runProgram (prog : Program) : Except Err Out := runAfter Parse.prelude fun _ => pure prog

end LeetQ.Rel.Lang
