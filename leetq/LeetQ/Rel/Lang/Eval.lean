import LeetQ.Rel.Lang.Elab
import LeetQ.Rel.Lang.Parse

/-! The evaluator of the Rel language: a core term to a relation by `Alg`'s ops, and the program run
    declaration by declaration. `ev` has no error path: the term's indices are its objects, and a term that
    runs on demand (§a) receives its keys by its type, `Dem true A`. -/

namespace LeetQ.Rel.Lang

open LeetQ.Rel LeetQ.Rel.Alg

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

/-- `t` on the keys `D`: exact at every key of `D`; a closed term ignores `D`. In `RS`, `S` runs on `ran(R)`. -/
def ev : {A B : Obj} → {d : Bool} → Tm A B d → Dem d A → Rel A B
  | _, _, _, .val R, _ => R
  | _, _, _, .uni U, _ => idU U
  | _, _, _, .zero, _ => zero
  | _, _, _, .id, D => D
  | _, _, _, .top V, D => top D.val (ev V ()).val
  | _, _, _, .mem, D => mem D.val
  | _, _, _, .outl, D => outl D
  | _, _, _, .outr, D => outr D
  | _, _, _, .inl, D => inl D.val
  | _, _, _, .inr, D => inr D.val
  | _, _, _, .comp (e := e) R S, D => let r := ev R D; r ≫ ev S (Dem.of e (ran r))
  | _, _, _, .conv R, _ => (ev R ())°
  | _, _, _, .meet (d := d) (e := e) R S, D => ev R (Dem.l d e D) ∩ ev S (Dem.r d e D)
  | _, _, _, .join (d := d) (e := e) R S, D => ev R (Dem.l d e D) ∪ ev S (Dem.r d e D)
  | _, _, _, .diff (d := d) (e := e) R S, D => ev R (Dem.l d e D) \ ev S (Dem.r d e D)
  | _, _, _, .dom R, D => dom (ev R D)
  | _, _, _, .ran R, _ => ran (ev R ())
  | _, _, _, .ldiv R S UB UC, _ => leftDiv (ev R ()) (ev S ()) (ev UB ()).val (ev UC ()).val
  | _, _, _, .rdiv R S UA UB, _ => rightDiv (ev R ()) (ev S ()) (ev UA ()).val (ev UB ()).val
  | _, _, _, .frac R S UA UB, _ => symDiv (ev R ()) (ev S ()) (ev UA ()).val (ev UB ()).val
  | _, _, _, .pair (d := d) (e := e) R S, D => pair (ev R (Dem.l d e D)) (ev S (Dem.r d e D))
  | _, _, _, .prod R S, _ => Alg.prod (ev R ()) (ev S ())
  | _, _, _, .junc R S, _ => junc (ev R ()) (ev S ())
  | _, _, _, .sum R S, _ => Alg.sum (ev R ()) (ev S ())
  | _, _, _, .lam R, D => Λ(ev R D)
  | _, _, _, .E (d := d) R, D => E (ev R (Dem.of d (ran (mem D.val)))) D.val
  | _, _, _, .map (d := d) R, D => map (ev R (Dem.of d (ran (mem D.val)))) D.val
  | _, _, _, .est Q, D => est (ev Q ()) (mem D.val)
  | _, _, _, .thin Q, D => let T := thin (ev Q ()) (mem D.val); Λ(T) ∪ top (D \ dom T).key (nilVal _)
  | _, _, _, .filter p, D => filter (ev p ()) D.val
  | _, _, _, .takewhile p, D => takewhile (ev p ()) D.val
  | _, _, _, .union, D => Arr.union D.val
  | _, _, _, .tau, D => τ D.val
  | _, _, _, .nil, D => top D.val (nilVal _)
  | _, _, _, .cons, D => cons D
  | _, _, _, .uncons, D => uncons D.val
  | _, _, _, .length, D => length D.val
  | _, _, _, .total, D => Arr.sum D.val
  | _, _, _, .head, D => head D.val
  | _, _, _, .tail, D => tail D.val
  | _, _, _, .pre, D => «prefix» D.val
  | _, _, _, .suf, D => suffix D.val
  | _, _, _, .succ U, D => D ≫ succ U
  | _, _, _, .plus U, D => plus D.val ≫ idU U
  | _, _, _, .leq U, _ => leq U
  | _, _, _, .lt U, _ => lt U
  | _, _, _, .fold (d := d) e S, D => foldOn (ev e ()).val (fun A => ev S (Dem.of d A)) D.val

/-- A closed term as its value, once; a term on demand as it is. -/
def fin {A B : Obj} : {d : Bool} → Tm A B d → Tm A B d
  | false, .val R => .val R
  | false, t => .val (ev t ())
  | true, t => t

/-- Every closed sub-term evaluated once, bottom up, so a fold's step recomputes only what reads the round's
    pairs: the closed parts of a term on demand become values before any round runs. -/
def hoist : {A B : Obj} → {d : Bool} → Tm A B d → Tm A B d
  | _, _, _, .comp R S => fin (.comp (hoist R) (hoist S))
  | _, _, _, .conv R => fin (.conv (hoist R))
  | _, _, _, .meet R S => fin (.meet (hoist R) (hoist S))
  | _, _, _, .join R S => fin (.join (hoist R) (hoist S))
  | _, _, _, .diff R S => fin (.diff (hoist R) (hoist S))
  | _, _, _, .dom R => fin (.dom (hoist R))
  | _, _, _, .ran R => fin (.ran (hoist R))
  | _, _, _, .ldiv R S U V => fin (.ldiv (hoist R) (hoist S) (hoist U) (hoist V))
  | _, _, _, .rdiv R S U V => fin (.rdiv (hoist R) (hoist S) (hoist U) (hoist V))
  | _, _, _, .frac R S U V => fin (.frac (hoist R) (hoist S) (hoist U) (hoist V))
  | _, _, _, .pair R S => fin (.pair (hoist R) (hoist S))
  | _, _, _, .prod R S => fin (.prod (hoist R) (hoist S))
  | _, _, _, .junc R S => fin (.junc (hoist R) (hoist S))
  | _, _, _, .sum R S => fin (.sum (hoist R) (hoist S))
  | _, _, _, .lam R => fin (.lam (hoist R))
  | _, _, _, .E R => .E (hoist R)
  | _, _, _, .map R => .map (hoist R)
  | _, _, _, .est Q => .est (hoist Q)
  | _, _, _, .thin Q => .thin (hoist Q)
  | _, _, _, .filter p => .filter (hoist p)
  | _, _, _, .takewhile p => .takewhile (hoist p)
  | _, _, _, .top V => .top (hoist V)
  | _, _, _, .fold e S => .fold (hoist e) (hoist S)
  | _, _, _, t => fin t

/-! ### Running a program -/

/-- An element printed with the program's names: a named element by its name, a number as itself. -/
def showEl (objs : Objs) : OTy → (A : Obj) → A.El → String
  | .base n, .atom .long, x =>
    let v : Int64 := x
    match objs.lookup n with
    | some i => if i.range.isSome then toString v else (i.elems[v.toInt.toNat]?).getD (toString v)
    | none => toString v
  | .prod a b, .prod A B, (x, y) => s!"({showEl objs a A x}, {showEl objs b B y})"
  | .sum a _, .sum A _, .inl x => s!"inl {showEl objs a A x}"
  | .sum _ b, .sum _ B, .inr y => s!"inr {showEl objs b B y}"
  | .arr a, .arr A, xs => "{" ++ ", ".intercalate (xs.map (showEl objs a A)) ++ "}"
  | _, _, _ => "?"

/-- A relation printed as its set of pairs, sorted. -/
def showRel (objs : Objs) (s t : OTy) {A B : Obj} (R : Rel A B) : String :=
  let ps := R.nub.toList.map fun (x, y) => s!"({showEl objs s A x}, {showEl objs t B y})"
  "{" ++ ", ".intercalate (ps.mergeSort fun a b => decide (a ≤ b)) ++ "}"

/-- An object with a variable left in it. -/
def OTy.poly : OTy → Bool
  | .mv _ => true
  | .prod a b | .sum a b => a.poly || b.poly
  | .arr a => a.poly
  | .base _ => false

/-- A relation with its objects. -/
abbrev Val := (A : Obj) × (B : Obj) × Rel A B

structure Out where
  /-- Every closed definition's value, with its objects as the program names them. -/
  vals : List (String × Val × OTy × OTy) := []
  /-- The text of each `print`. -/
  prints : List String := []
  objs : Objs := []

/-- A top-level term's value: on its source's universe when it needs keys. -/
def topVal (env : Env) (p : Pos) (e : Expr) : Except Err (Val × OTy × OTy) := do
  let (r, st) ← (elabE env none e).run {}
  let (q, s, t) := r.plain
  let ⟨A, B, d, tm⟩ ← build env.objs st p (.close p q s)
  match d, tm with
  | false, tm => pure (⟨A, B, ev (hoist tm) ()⟩, zonk st s, zonk st t)
  | true, _ => throw ⟨p, s!"{e.show}: {zonk st s} has no universe; compose a set of its elements before it (§a)"⟩

def objInfo (env : Env) (n : String) : ObjDef → Except Err ObjInfo
  | .elems ws => pure { ty := .base n, elems := ws, uni := some ⟨_, col ((List.range ws.length).map Int64.ofNat)⟩ }
  | .range lo hi =>
    pure { ty := .base n, range := some (lo, hi), uni := some ⟨_, col ((List.range (hi + 1 - lo)).map fun k => Int64.ofNat (k + lo))⟩ }
  | .alias o => do let (t, _) ← (oty env o).run {}; pure { ty := t }

/-- Run a program: each declaration in order; a definition with no parameters is built once and, when it is
    closed or its source has a universe, evaluated once into a value its users share. -/
def run (prog : Program) : Except Err Out := do
  let mut env : Env := {}
  let mut out : Out := {}
  for d in prog do
    match d with
    | .obj _ n od => env := { env with objs := (n, ← objInfo env n od) :: env.objs }
    | .defn p n [] (.rel e) =>
      let (r, st) ← (elabE env none e).run {}
      let (q, s, t) := r.plain
      let s := zonk st s; let t := zonk st t
      -- objects its body leaves open (`≼` on any `A×B`) are fixed at each use, as a parameter's are
      if s.poly || t.poly then env := { env with defs := (n, mkDef env p [] (.rel e)) :: env.defs }; continue
      let q := if (uniOf env.objs s).isSome then Pre.close p q s else q
      let ⟨A, B, d, tm⟩ ← build env.objs st p q
      let tm := hoist tm
      let res : Res := ⟨A, B, d, tm⟩
      env := { env with defs := (n, { arity := 0, apply := fun _ _ => pure (.rel (.tm res) s t) }) :: env.defs }
      match d, tm with
      | false, tm => out := { out with vals := (n, ⟨A, B, ev tm ()⟩, s, t) :: out.vals }
      | true, _ => pure ()
    | .defn p n ps b => env := { env with defs := (n, mkDef env p ps b) :: env.defs }
    | .print p e =>
      let (⟨_, _, R⟩, s, t) ← topVal env p e
      out := { out with prints := out.prints ++ [s!"{e.show} = {showRel env.objs s t R}"] }
    | .check p e f eq =>
      let (⟨A, B, R⟩, s, t) ← topVal env p e
      let (⟨A', B', S⟩, s', t') ← topVal env p f
      if h : A' = A ∧ B' = B then
        let S : Rel A B := h.2 ▸ h.1 ▸ S
        if !(R ⊑ S && (!eq || S ⊑ R)) then
          throw ⟨p, s!"check failed: {e.show} = {showRel env.objs s t R}, {f.show} = {showRel env.objs s t S}"⟩
      else throw ⟨p, s!"check: the sides have types {s} ⟶ {t} and {s'} ⟶ {t'}"⟩
  pure { out with objs := env.objs }

/-- Parse and run a program's text. -/
def runText (src : String) : Except Err Out := do run (← Parse.parse src)

end LeetQ.Rel.Lang
