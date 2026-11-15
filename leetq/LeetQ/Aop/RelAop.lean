import LeetQ.Aop.Calc
import AOP.A6_ConsList

/-! `rel_aop n model … proof …` (`doc/rel-mss-proof-design.md` §4, stage S5): the program `n` (a `rel_program`
    constant) read as Lean declarations about the AOP allegory, each under the book's model the `model` block gives.

    - A definition `x` the theorems reach becomes `m.x.aop`, `m` the program that declares it, its value
      `Calc.elabExpr` of its body at its declared type. A definition whose type has an object variable (`segment :
      [α] ⟶ [α]`) has no one Lean definition under a model: it is put in place at each use, its objects fixed there.
    - A theorem `t` of `n` becomes `n.t.aop`. Its proof is the `calc` its steps give (`Trans.trans` of one proof per
      step, as Lean's `calc` builds it), or, with no steps, the Lean term of its `proof` item. A theorem with
      neither is owed: `rel_aop` lists every such theorem and declares nothing.
    - A step `_ = x := ≜ y` is `rfl` (unfolding `y`'s `.aop` definition); `_ = x := t` cites `t`'s `.aop` theorem,
      of `n` or of a program `n` is read after, under congruence: as stated, rewritten either way, or rewritten
      after both sides are right-associated. A step that is no instance names its Rel line, the law, and Lean's error.

    The model: each item `x := v` (or `x : T := v`) is a `let` every term is elaborated under. It names what has no
    AOP reading of its own: an object (`N := (⟨Int⟩ : RelSet.{0})`), a definition read as a given declaration
    (a literal `zero`, the prelude's `suffix`), and a witness `rel(…)` never writes (a `RelProd`, a `Coproduct`).
    A composite object is read structurally in `Rel(Set)`: `A×B` the set of pairs, `A+B` the disjoint union, `𝒫A` the
    power object, `[A]` the cons lists of `A`, `1` the one-point set. -/

namespace LeetQ.Rel.Lang.RelAop

open Lean Elab Term Meta Command
open LeetQ.Rel.Lang
open Freyd Freyd.Alg Freyd.Alg.RelSet Freyd.Alg.RelSet.CL PowerAllegory

syntax relAopItem := ident (" : " term)? " := " term
syntax (name := relAop) "rel_aop " ident (&" model " sepBy1(relAopItem, ", "))? (" proof " sepBy1(relAopItem, ", "))?
  : command

/-- The items of an optional `model` or `proof` block: name, its syntax, the type if written, the value. -/
def items (s : Syntax) : List (String × Syntax × Option Syntax × Syntax) :=
  if s.getNumArgs == 0 then [] else s[1].getSepArgs.toList.map fun i =>
    (i[0].getId.toString (escape := false), i[0], if i[1].getNumArgs == 0 then none else some i[1][1], i[3])

/-- The names a term reads, each binder of a fixed point excluded. -/
partial def names : Lang.Expr → List String
  | .name _ n => [n]
  | .app _ n as => n :: as.flatMap names
  | .inf _ n a b => n :: (names a ++ names b)
  | .op _ _ _ as => as.flatMap names
  | .comp a b | .bin _ _ a b | .pair _ a b | .junc _ a b | .fold _ a b => names a ++ names b
  | .conv _ a | .compl _ a => names a
  | .lit .. => []
  | .fix _ _ x b => (names b).filter (· != x)

/-- A definition as `rel_aop` reads it: its program, name, parameters, body, declared type. -/
abbrev Def := Name × String × List Param × Lang.Expr × Option (OExp × OExp)

def aopName (m : Name) (x : String) : Name := (m.str x).str "aop"

/-- The type of `d` has an object variable: it is put in place at each use. -/
def Def.generic (d : Def) : Bool := match d.2.2.2.2 with
  | some (s, t) => !(s.vars ++ t.vars).isEmpty
  | none => false

/-- `e` with each generic definition it reads replaced by its body, read the same way; `model` names shadow. -/
partial def inline (defs : List Def) (model : List String) (e : Lang.Expr) : Lang.Expr :=
  e.subst ((names e).eraseDups.filterMap fun x =>
    if model.contains x then none else match defs.find? (·.2.1 == x) with
      | some d => if d.generic then some (x, inline defs model d.2.2.2.1) else none
      | none => none)

/-- The definitions `e` (already `inline`d) reads that become Lean definitions of their own. -/
def closed (defs : List Def) (model : List String) (e : Lang.Expr) : List String :=
  (names e).eraseDups.filter fun x => !model.contains x && (Calc.prelude.lookup x).isNone && defs.any (·.2.1 == x)

/-- `k` under the model's `let`s, given the names they bind. -/
def withModel {α : Type} : List (String × Syntax × Option Syntax × Syntax) → List String →
    (List String → TermElabM α) → TermElabM α
  -- a model `let` unfolds in unification (`zetaDelta`): an object `N := ⟨Int⟩` must reach the instances over `Int`
  | [], vs, k => withConfig (fun c => { c with zetaDelta := true }) (k vs)
  | (x, _, t?, v) :: ms, vs, k => do
    let ty ← match t? with | some t => elabType t | none => mkFreshTypeMVar
    let e ← elabTermEnsuringType v ty; synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    -- the written type, not `e`'s own: `sumCop _ _` is the coproduct the model says it is only at `T`
    withLetDecl (.mkSimple x) (← instantiateMVars ty) e fun _ => withModel ms (x :: vs) k

/-- `k` with each Lean definition `cs` names bound as a `let` under its Rel name. -/
def withDefs {α : Type} : List (String × Name) → List String → (List String → TermElabM α) → TermElabM α
  | [], vs, k => k vs
  | (x, c) :: cs, vs, k => do
    withLetDecl (.mkSimple x) (← inferType (mkConst c)) (mkConst c) fun _ => withDefs cs (x :: vs) k

/-- The object `o` read in `Rel(Set)`; a name, and an object variable, is the model's. -/
partial def obj (vs : List String) : OExp → TermElabM Term
  | .name p n | .var p n =>
    if vs.contains n then pure (mkIdent (.mkSimple n)) else if n == "1" then `(dL Unit) else
      throwError "{p}: the object `{n}` has no reading: the model names none"
  | .prod a b => do `((⟨($(← obj vs a)).carrier × ($(← obj vs b)).carrier⟩ : RelSet.{0}))
  | .sum a b => do `((⟨($(← obj vs a)).carrier ⊕ ($(← obj vs b)).carrier⟩ : RelSet.{0}))
  | .pow a => do `(P $(← obj vs a))
  | .list a => do `(dCL Unit ($(← obj vs a)).carrier)

/-- `Calc.elabExpr` of `e`; with no outer term to wait for, a hole still waiting is read again without waiting, so
    that it fails naming the witness it cannot choose. -/
def read (what : String) (vs : List String) (e : Lang.Expr) (ty? : Option Lean.Expr) : TermElabM Lean.Expr :=
  catchInternalId postponeExceptionId (Calc.elabExpr vs [] e ty?) fun _ =>
    withoutPostponing do
      try Calc.elabExpr vs [] e ty? catch ex => throwError "{what}: {ex.toMessageData}"

/-- `e` closed: every metavariable solved, every `let` of the model put in place. -/
def close (what : String) (e : Lean.Expr) : TermElabM Lean.Expr := do
  synthesizeSyntheticMVarsNoPostponing
  let e ← zetaReduce (← instantiateMVars e)
  if e.hasMVar || e.hasFVar then throwError "{what}: its AOP reading leaves `{e}` unfixed"
  pure e

/-- The Lean definition of `x`, declared first if it is not yet, with every definition it reads. -/
partial def ensure (defs : List Def) (model : List (String × Syntax × Option Syntax × Syntax)) (x : String) :
    CommandElabM Name := do
  let ms := model.map (·.1)
  let some (m, _, ps, b, ty) := defs.find? (·.2.1 == x) | throwError "`{x}` is no definition of the program"
  let c := aopName m x
  if (← getEnv).contains c then return c
  unless ps.isEmpty do throwError "`{x}` has parameters: rel_aop reads a definition with parameters once P3 types them"
  let b := inline defs ms b
  let cs ← (closed defs ms b).mapM fun y => return (y, ← ensure defs model y)
  let (t, v) ← liftTermElabM <| withModel model [] fun vs => withDefs cs vs fun vs => do
    let ty? ← ty.mapM fun (s, t) => do elabType (← `($(← obj vs s) ⟶ $(← obj vs t)))
    let v ← close s!"the definition `{x}`" (← read s!"the definition `{x}`" vs b ty?)
    pure (← inferType v, v)
  let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) v + 1)
  liftCoreM <| addDecl (.defnDecl { name := c, levelParams := [], type := t, value := v, hints, safety := .safe })
  return c

/-- The proof of the step `_ r x := why` at `p`, whose goal is `g`; `cite y` the `.aop` theorem `y` names. -/
def step (p : Lang.Pos) (eq : Bool) (x : Lang.Expr) (why : Why) (g : Lean.Expr) (cite : String → TermElabM Name) :
    TermElabM Lean.Expr := do
  let mv ← mkFreshExprMVar g
  let (tac, law) ← match why with
    | .unfold _ y => pure (← `(tactic| rfl), m!"`≜ {y}`")
    | .thm _ y => do
      let c ← cite y; let h := mkIdent c
      pure (← `(tactic| first
        | with_reducible exact $h
        | rw [$h:ident]
        | rw [← $h:ident]
        | (have h' := $h; simp only [Cat.assoc] at h' ⊢; first | exact h' | rw [h'] | rw [← h'])),
        m!"`{y}` : {← inferType (mkConst c)}")
  let r := if eq then "=" else "⊑"
  try
    let gs ← Tactic.run mv.mvarId! (Tactic.evalTactic tac)
    unless gs.isEmpty do throwError "goals remain: {gs.map (·.name)}"
  catch ex => throwError "{p}: the step `_ {r} {x.show}` is not an instance of {law}\n{ex.toMessageData}"
  instantiateMVars mv

/-- `e r f` for Rel's `=` (`eq`) or `⊑`. -/
def relation (eq : Bool) (e f : Lean.Expr) : TermElabM Lean.Expr := do
  if eq then mkEq e f else elabType (← `($(← exprToSyntax e) ⊑ $(← exprToSyntax f)))

@[command_elab relAop] def elabRelAop : CommandElab := fun stx => do
  let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[1])
  let model := items stx[2]
  let proofs := items stx[3]
  let ms := model.map (·.1)
  let chain := ((Expand.relRegistry.getState (← getEnv)).chains.lookup n).getD []
  let progs ← (chain ++ [n]).reverse.mapM fun m => return (m, ← Embed.programOf m)
  let defs : List Def := progs.flatMap fun (m, p) =>
    (p.filterMap fun | .defn _ x ps (.rel e) ty => some (m, x, ps, e, ty) | _ => none).reverse
  let thms := progs.flatMap fun (m, p) =>
    (p.filterMap fun | .«theorem» _ x .. => some (m, x) | _ => none).reverse
  let own := (← Embed.programOf n).filterMap fun
    | .«theorem» p x ps e f eq _ ss => some (p, x, ps, e, f, eq, ss) | _ => none
  -- the obligations are the theorems: each needs a chain or a `proof` item, never both
  for (x, i, _) in proofs do
    match own.find? (·.2.1 == x) with
    | some (_, _, _, _, _, _, []) => pure ()
    | some _ => throwErrorAt i "`{x}` has a calc: a `proof` item would be a second proof"
    | none => throwErrorAt i "`{x}` is no theorem of `{n}`"
  let owed := own.filter fun (_, x, _, _, _, _, ss) => ss.isEmpty && !proofs.any (·.1 == x)
  unless owed.isEmpty do
    throwError "owed: {owed.length} theorem(s) of `{n}` with no calc and no `proof` item:{String.join (owed.map
      fun (p, x, _, e, f, eq, _) => s!"\n  {p}: {x} : {e.show} {if eq then "=" else "⊑"} {f.show}")}"
  for (p, x, ps, e, f, eq, ss) in own do
    unless ps.isEmpty do throwError "{p}: `{x}` has parameters: rel_aop reads a theorem with parameters once P3 types them"
    let es := (e :: f :: ss.map (·.2.2.1)).map (inline defs ms)
    let cs ← (es.flatMap (closed defs ms)).eraseDups.mapM fun y => return (y, ← ensure defs model y)
    let env ← getEnv
    let cite (y : String) : TermElabM Name := do
      let some (m, _) := thms.find? (·.2 == y) | throwError "`{y}` is no theorem of `{n}` nor of a program it is read after"
      let c := aopName m y
      unless env.contains c do throwError "`{y}` has no Lean proof yet: rel_aop `{m}` declares it, before this step"
      pure c
    let (ty, pf) ← liftTermElabM <| withModel model [] fun vs => withDefs cs vs fun vs => do
      let (e', f') := (inline defs ms e, inline defs ms f)
      let l ← read s!"the left side of `{x}`" vs e' none
      let r ← read s!"the right side of `{x}`" vs f' (← inferType l)
      let ty ← relation eq l r
      let pf ← match ss, proofs.find? (·.1 == x) with
        | [], some (_, _, _, v) => elabTermEnsuringType v ty
        | _, _ => do
          let (_, pf) ← ss.foldlM (init := (l, none)) fun (prev, acc) (q, seq, t, why) => do
            let next ← read s!"{q}" vs (inline defs ms t) (← inferType l)
            let pf ← step q seq t why (← relation seq prev next) cite
            pure (next, some (← match acc with | none => pure pf | some a => mkAppM ``Trans.trans #[a, pf]))
          let some pf := pf | throwError "{p}: `{x}` has no steps"
          unless ← isDefEq (← inferType pf) ty do
            throwError "{p}: the calc of `{x}` proves {← inferType pf}, not {ty}"
          pure pf
      pure (← close s!"the statement of `{x}`" ty, ← close s!"the proof of `{x}`" pf)
    liftCoreM <| addDecl (.thmDecl { name := aopName n x, levelParams := [], type := ty, value := pf })

end LeetQ.Rel.Lang.RelAop
