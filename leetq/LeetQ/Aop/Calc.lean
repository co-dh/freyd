import LeetQ.Run.Lang.Grammar
import Freyd.S2_30
import AOP.A4_4
import AOP.A4_5
import AOP.A5_2
import AOP.A5_3
import Freyd.Junc
import AOP.A5_5
import AOP.A6_2
import AOP.A5_4_PowerRel
import AOP.A8_1
import AOP.A8_3
import AOP.A1_7_Pointfree

/-! `rel(t)`: the Rel term `t` read as a term of the AOP allegory, so that an ordinary Lean statement, and the steps
    of a plain `calc`, can be written in Rel. `t` is the `rel` category of `Embed`, read to `Lang.Expr` by
    `Embed.expr` in a scope whose names are the local variables; the AST is then written as Lean notation and
    elaborated with the ambient instance, so objects and types are Lean's, not the Rel elaborator's. The category
    embeds no `term`: a Lean term reaches a proof only as the justification of a `calc` step.

    The fragment, each with the same meaning in Rel and in AOP (`doc/rel-lean-mapping.md`): a local variable, `R S`,
    `R°`, `R ∩ S`, `R ∪ S`, `R / S`, `R \ S`, `𝟙`, `𝟘`, `⊤`, `dom(R)`, `ran(R)`; `⟨R,S⟩`, `R × S`, `π₁`, `π₂` over
    a `RelProd` instance; `[R,S]`, `inl`, `inr` over a `Coproduct` hypothesis; `∼R`, `R − S` in a
    `BooleanAllegory`; the book's fold `⦇R⦈` and `α` over an `InitialAlgebra` instance, `F(R)` over a `Relator`
    hypothesis; the power group `∋`, `∈`, `Λ(R)`, `E(R)`, `est(R)`, `thin(Q)`, `τ` as the book's
    power-object operators, each over the class AOP defines it in; the list and number builtins as their `Rel(Set)`
    declarations; the program fold `⦇e,S⦈` as the book's `⦇[e',S]⦈` (`toTerm`). `builtins` holds every builtin's
    reading or why it has none. `⊑` and `=` are Lean's, between `rel(…)` terms. Every other construct is an error
    naming it. The translation is `toTerm` and its elaboration `elabExpr`, functions of the Rel term, not of `rel(…)`.

    A product, a coproduct, an initial algebra, a relator, a power allegory or the Boolean instance is never
    written in the term: each is a metavariable that unification gives its objects, then `fill` takes from the
    statement's context. -/

namespace LeetQ.Rel.Lang.Calc

open Lean Elab Term Meta
open LeetQ.Rel.Lang
open Freyd Freyd.Alg

/-- A syntax node spanning the source position `p`, for an error at the construct it names. -/
def refAt (p : Lang.Pos) : TermElabM Syntax := do
  let i := (← getFileMap).ofPosition ⟨p.line, p.col - 1⟩; pure (.atom (.synthetic i i) "")

def outside {α : Type} (p : Lang.Pos) (what : String) (why : MessageData) : TermElabM α := do
  throwErrorAt (← refAt p) "{what} {why}"

/-- What the term does not write, each resolved after elaboration: a witness metavariable (`fill`) or `⊤` (`top`). -/
abbrev Holes := IO.Ref (Array (TermElabM Unit))

-- printed alone, so that the type never breaks across the message's line; `?_` for an object nothing fixed
def ppType (ty : Lean.Expr) : TermElabM String := do
  pure (toString (← withOptions (pp.mvars.set · false) (ppExpr ty)))

/-- `w` filled from the context: the one hypothesis of its type (local instances are the statement's hypotheses),
    for a class else instance search. Objects still unknown wait for the expected type unless one hypothesis fits
    already: knowing them only removes candidates, and a fold's relator is fixed by nothing else. Two hypotheses
    that both fit are an error naming them, never a pick. -/
def fill (w : Lean.Expr) (p : Lang.Pos) (what why : String) : TermElabM Unit := do
  if (← w.mvarId!.isAssigned) then return
  let ty ← instantiateMVars (← inferType w)
  let tys ← ppType ty
  let set (c : Lean.Expr) := do unless ← isDefEq w c do outside p what m!"cannot use `{c}` as `{tys}`"
  let cs ← (← getLCtx).foldlM (init := #[]) fun cs d => do
    if d.isImplementationDetail || (← whnfR d.type).getAppFn.constName? != ty.getAppFn.constName? then return cs
    return if ← withoutModifyingState (isDefEq d.type ty) then cs.push d.toExpr else cs
  if ty.hasExprMVar && cs.size != 1 then tryPostpone
  match cs with
  | #[c] => set c
  | #[] =>
    if (← isClass? ty).isNone then outside p what m!"needs a hypothesis `{tys}`: {why}"
    if ty.hasExprMVar then outside p what m!"needs `{tys}` with objects the statement fixes: {why}"
    match ← synthInstance? ty with
    | some c => set c
    | none => outside p what m!"needs an instance or hypothesis `{tys}`: {why}"
  | _ => outside p what m!"has several hypotheses `{tys}`, {", ".intercalate (← cs.toList.mapM fun c =>
      return toString (← ppExpr c))}: {why}"

/-- A natural metavariable of type `ty`, so that unification may fix its objects before `fill` finds it. -/
def hole (hs : Holes) (p : Lang.Pos) (what why : String) (ty : Term) : TermElabM Term := do
  let w ← mkFreshExprMVar (← elabType ty); hs.modify (·.push (fill w p what why)); exprToSyntax w

def prod (hs : Holes) (p : Lang.Pos) (what : String) : TermElabM Term := do
  hole hs p what "rel(…) never writes the product" (← `(Freyd.Alg.RelProd _ _))

def coprod (hs : Holes) (p : Lang.Pos) (what : String) : TermElabM Term := do
  hole hs p what "rel(…) never writes it, and a structure is found by no instance search"
    (← `(Freyd.Alg.Coproduct _ _ _))

def initial (hs : Holes) (p : Lang.Pos) (what : String) : TermElabM Term := do
  hole hs p what "rel(…) never writes the initial algebra, nor its relator" (← `(Freyd.Alg.InitialAlgebra _))

/-- The one table of builtin readings, a row per `Op.table` entry (`CalcTest` guards that none lacks one), keyed
    as `Op.table` keys it (`at(i)` by `.index 0`): `.ok none`, `toTerm`'s own clause, over any allegory; `.ok f`, the
    AOP declaration `f`, applied by `power` (the power group over its class, the list and number builtins in
    `Rel(Set)`, where `[α]` is a cons list and a set the power object); `.error why`, no AOP reading. -/
def builtins : List (Op × Except String (Option Name)) :=
  open QLean.Kernel.Ew in open Freyd.Alg.RelSet in
  let none' (why : String) : Except String (Option Name) := .error why
  [(.id, .ok none), (.zero, .ok none), (.top, .ok none), (.outl, .ok none), (.outr, .ok none), (.inl, .ok none),
   (.inr, .ok none), (.alpha, .ok none), (.map, .ok none), (.dom, .ok none), (.ran, .ok none),
   (.lam, .ok ``Freyd.Alg.Λ), (.E, .ok ``existsImage),
   (.est, .ok ``est), (.thin, .ok ``thinRel),
   (.leq, .ok ``ListRel.leq), (.succ, .ok ``ListRel.succ), (.arith add, .ok ``ListRel.plus),
   (.arith idiv, .error "Rel's div is Int division and ListRel.div is Nat division; \
    the Int reading is added when a proof first needs it"),
   (.nil, .ok ``ListRel.nilAtUnit),
   (.lt, none' "AOP declares no strict order on numbers"), (.arith mul, none' "AOP declares no product of numbers"),
   (.arith sub, none' "AOP declares no difference of numbers"),
   (.arith imod, none' "AOP declares no remainder of numbers"),
   (.arith greater, none' "AOP declares no maximum of two numbers"),
   (.arith lesser, none' "AOP declares no minimum of two numbers"),
   (.refold, none' "AOP's unfold-then-fold is `(relCata c°)° ≫ relCata S` over an initial algebra of G, \
    which rel(…) never writes"),
   (.index 0, none' "AOP declares no element at a position")] ++
  (prims.filter fun r => r.written && r.prelude.isNone).map fun r => (.prim r.sym, r.aop.map some)

-- `prims` names its AOP readings unchecked (Syntax cannot import AOP), so every row's is checked here, where they resolve
run_cmd do
  for (o, r) in builtins do
    if let .ok (some n) := r then
      unless (← getEnv).contains n do throwError "builtins: the AOP reading of `{o.sym}` is `{n}`, which is not declared"

/-- The prelude's names with a fixed AOP counterpart, each its prelude body in the fragment: `rel(…)` has no
    prelude, and AOP writes `∈` as `∋°`. -/
def prelude : List (String × (Lang.Pos → Lang.Expr)) := [("∈", fun p => .conv p (.op p (.prim memRow.sym) [] []))]

/-- The one allegory the statement's arrows `A ⟶ B` live in, if they agree on one. -/
def allegory : TermElabM (Option Lean.Expr) := do
  let cs ← (← getLCtx).foldlM (init := #[]) fun cs d => do
    let t ← instantiateMVars d.type
    pure <| match d.isImplementationDetail, t.isAppOf ``Cat.Hom, t.getAppArgs[0]? with
      | false, true, some c => if cs.contains c then cs else cs.push c
      | _, _, _ => cs
  pure (if cs.size == 1 then cs[0]? else none)

/-- `f` applied by its declared binders: the explicit ones take `args` in order, every other one, and an explicit
    one past `args` (an object), a metavariable unification fixes. An instance binder is found in the statement's
    allegory before elaboration, since a class projection in an arrow type does not unify through an unknown
    instance; with no one allegory it is `_`, which Lean synthesizes when unification reaches it. -/
def power (p : Lang.Pos) (what : String) (f : Name) (args : List Term) : TermElabM Term := do
  let (ms, bis, _) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels f))
  let c? ← allegory
  let (_, xs) ← (ms.zip bis).foldlM (init := (args, #[])) fun (as, xs) (m, bi) => do
    -- an instance binder over the allegory has an argument of the allegory's type; `[Add A]` is a plain instance
    let t ← inferType m
    let over ← match c?, bi.isInstImplicit && t.isApp with
      | some c, true => isDefEq (← inferType t.appArg!) (← inferType c)
      | _, _ => pure false
    match bi.isExplicit, bi.isInstImplicit && over, as, c? with
    | true, _, a :: as, _ => pure (as, xs.push a)
    | _, true, _, some c => do
      let ty ← inferType m
      unless ← isDefEq ty.appArg! c do outside p what m!"is over `{ty}`, not the statement's allegory `{c}`"
      let ty ← instantiateMVars ty
      let some i ← synthInstance? ty | outside p what m!"needs an instance `{ty}`: AOP defines `{f}` over it"
      pure (as, xs.push (← exprToSyntax i))
    | _, _, _, _ => do
      let s ← if bi.isInstImplicit then do withRef (← refAt p) `(_) else exprToSyntax m
      pure (as, xs.push s)
  `(@$(mkIdent f) $xs*)

/-- The two `⊤` of AOP, each with the class it is defined in: the instance found decides. -/
def tops : List (Name × Name) :=
  [(``LocallyCompleteDistributiveAllegory, ``topHom), (``TabularUnitaryDivisionAllegory, ``topMor)]

/-- Theorems `f A B = g A B` between `tops` entries: where both classes have instances, `⊤` is `g`. -/
def sames : List Name := [``topMor_eq_topHom]

/-- The heads `(f, g)` of the equation `f … = g …` that the theorem `t` concludes. -/
def same (t : Name) : TermElabM (Option (Name × Name)) := do
  forallTelescope (← getConstInfo t).type fun _ b => pure do
    let (_, l, r) ← b.eq?; pure (← l.getAppFn.constName?, ← r.getAppFn.constName?)

/-- `⊤` at `w`, once its type `A ⟶ B` is known: the `tops` entry whose class has an instance, and of several
    the one that `sames` rewrites every other into; none such is an error. -/
def top (w : Lean.Expr) (p : Lang.Pos) : TermElabM Unit := do
  if (← w.mvarId!.isAssigned) then return
  let ty ← instantiateMVars (← inferType w)
  if ty.hasExprMVar then tryPostpone
  unless ty.isApp && ty.appFn!.isApp do outside p "`⊤`" m!"has type `{ty}`, not an arrow"
  let (a, b) := (ty.appFn!.appArg!, ty.appArg!)
  let c ← exprToSyntax (← instantiateMVars (← inferType a))
  let found ← tops.filterM fun (k, _) => do return (← synthInstance? (← elabType (← `($(mkIdent k) $c)))).isSome
  let name (k : Name) := s!"`{k.getString!}`"
  let eqs ← sames.filterMapM same
  match found.find? fun (_, f) => found.all fun (_, g) => g == f || eqs.contains (g, f) with
  | some (_, f) =>
    let t ← elabTerm (← `($(mkIdent f) $(← exprToSyntax a) $(← exprToSyntax b))) ty
    unless ← isDefEq w t do outside p "`⊤`" m!"cannot use `{t}` as `{ty}`"
  | none =>
    if found.isEmpty then outside p "`⊤`" m!"needs an instance {" or ".intercalate (tops.map fun (k, f) =>
      s!"{name k} (AOP's {name f})")}: AOP's `⊤` is one of these"
    else outside p "`⊤`" m!"is {" and ".intercalate (found.map fun (k, f) => s!"{name f} (by {name k})")} here, and no theorem identifies them"

/-- `e` written as AOP notation; `vars` the local variables a name may be, `folds` the names `lift` gave the
    one-argument folds, `hs` what the term does not write. -/
partial def toTerm (vars : List String) (folds : List (String × Lang.Expr)) (hs : Holes) :
    Lang.Expr → TermElabM Term
  | .name p n => match folds.lookup n, prelude.lookup n with
    | some r, _ => do cata hs p "`⦇R⦈`" (← toTerm vars folds hs r)
    | none, some e => toTerm vars folds hs (e p)
    | none, none => if vars.contains n then pure (mkIdent (.mkSimple n)) else
      outside p s!"`{n}`" "is not a local variable: a name in rel(…) is a variable or hypothesis of the statement"
  | .comp a b => do `($(← toTerm vars folds hs a) ≫ $(← toTerm vars folds hs b))
  | .conv _ a => do `($(← toTerm vars folds hs a)°)
  | .compl p a => do let (c, _, a) ← boolean p "`∼R`" (← toTerm vars folds hs a); `(Freyd.Alg.neg (𝒜 := $c) $a)
  | .bin p o a b => do
    let (a, b) := (← toTerm vars folds hs a, ← toTerm vars folds hs b)
    match o with
    | .meet => `($a ∩ $b)
    | .join => `($a ∪ $b)
    -- the constants, not `/` `\`: core's `HDiv`, `SDiff` notations are ambiguous with them while objects are unknown
    | .rdiv => `(Freyd.Alg.DivisionAllegory.div $a $b)
    | .ldiv => `(Freyd.Alg.leftDiv $a $b)
    | .diff => do let (c, i, a) ← boolean p "`R − S`" a; `(@Freyd.Alg.sub $c $i _ _ $a $b)
    | .prod => `(Freyd.Alg.prodMap $(← prod hs p "`R × S`") $(← prod hs p "`R × S`") $a $b)
  | .pair p a b => do
    `(Freyd.Alg.RelProd.pair $(← prod hs p "`⟨R,S⟩`") $(← toTerm vars folds hs a) $(← toTerm vars folds hs b))
  | .junc p a b => do
    `(Freyd.Alg.junc $(← coprod hs p "`[R,S]`") $(← toTerm vars folds hs a) $(← toTerm vars folds hs b))
  | .op _ .id [] [] => `(𝟙 _)
  | .op _ .zero [] [] => `(𝟘)
  | .op p .top [] [] => do
    let w ← mkFreshExprMVar none; hs.modify (·.push (top w p)); exprToSyntax w
  | .op _ .dom [] [a] => do `(Freyd.Alg.dom $(← toTerm vars folds hs a))
  | .op _ .ran [] [a] => do `(Freyd.Alg.ran $(← toTerm vars folds hs a))
  | .op p .outl [] [] => do `(Freyd.Alg.RelProd.π₁ (self := $(← prod hs p "`π₁`")))
  | .op p .outr [] [] => do `(Freyd.Alg.RelProd.π₂ (self := $(← prod hs p "`π₂`")))
  | .op p .inl [] [] => do `(Freyd.Alg.Coproduct.u₁ $(← coprod hs p "`inl`"))
  | .op p .inr [] [] => do `(Freyd.Alg.Coproduct.u₂ $(← coprod hs p "`inr`"))
  | .op p .alpha [] [] => do `(Freyd.Alg.InitialAlgebra.α (self := $(← initial hs p "`α`")))
  | .op p .map [] [a] => do
    -- an endorelator, as Rel's `F` and the one an `InitialAlgebra` folds: its target allegory is its source
    let c ← exprToSyntax (← mkFreshTypeMVar)
    let f ← hole hs p "`F(R)`" "rel(…) never writes the relator" (← `(Freyd.Alg.Relator $c $c))
    `(Freyd.Functor.map (Freyd.Alg.Relator.toFunctor $f) $(← toTerm vars folds hs a))
  | .op p o (_ :: _) _ => outside p s!"`{o.sym}(…)`" "names Rel objects: rel(…) takes its objects from the Lean types"
  | .op p o [] as =>
    let what := s!"`{o.sym}{if as.isEmpty then "" else "(R)"}`"
    match builtins.lookup (match o with | .index _ => .index 0 | o => o) with
    | some (.ok (some f)) => do power p what f (← as.mapM (toTerm vars folds hs))
    | some (.error why) => outside p what s!"has no AOP reading: {why}"
    | _ => outside p what "has no row in `Calc.builtins` that toTerm can read"
  | .lit p _ => outside p "a literal `{…}`" "has no AOP counterpart"
  -- Rel folds from the values of the coreflexive seed `e`; the book's base is the `e' : 1 ⟶ V` with `ran(e') = e`:
  -- `b` where `e` is written `ran(b)` (the base's type fixes `b`'s source to `1`), else `⊤e`
  | .fold p e s => do
    let e' := match e with | .op _ .ran [] [b] => b | e => .comp (.op p .top [] []) e
    cata hs p "`⦇e,S⦈`" (← toTerm vars folds hs (.junc p e' s))
  | .app p n _ | .inf p n .. => outside p s!"`{n}`" "is a Rel definition, and rel(…) has none"
  | .fix p l x _ => outside p s!"`{if l then "μ" else "ν"}{x} : …`" "is outside the allegory fragment of rel(…)"
where
  /-- The book's fold of the algebra `r`, over the initial algebra the context holds. -/
  cata (hs : Holes) (p : Lang.Pos) (what : String) (r : Term) : TermElabM Term := do
    `(Freyd.Alg.relCata (I := $(← initial hs p what)) $r)
  /-- The operand `a` of a complement elaborated, its allegory `𝒜` (the type of its target) and the instance
      `BooleanAllegory 𝒜`, found before the complement is: AOP's `∼R` is the Heyting `R ⇨ 𝟘`, which is the
      complement Rel means only in a Boolean allegory. -/
  boolean (p : Lang.Pos) (what : String) (a : Term) : TermElabM (Term × Term × Term) := do
    let e ← elabTerm a none
    let t ← instantiateMVars (← inferType e)
    if !t.isApp then outside p what m!"has an operand of type `{t}`, not an arrow"
    let c ← instantiateMVars (← inferType t.appArg!)
    if c.hasExprMVar then tryPostpone; outside p what m!"has an operand `{t}` in no fixed allegory"
    let ty ← elabType (← `(Freyd.Alg.BooleanAllegory $(← exprToSyntax c)))
    let tys := toString (← ppExpr ty)
    let some i ← synthInstance? ty | outside p what (m!"needs an instance `{tys}`: AOP's `∼R` is the Heyting " ++
      m!"`R ⇨ 𝟘`, the complement only in a Boolean allegory")
    pure (← exprToSyntax c, ← exprToSyntax i, ← exprToSyntax e)

/-- The Rel term `e` elaborated as its AOP reading at the expected type `ty?`, each hole filled: the one entry for
    every caller of the translation (`rel(…)`, and any command or proof step that holds a `Lang.Expr`). -/
def elabExpr (vars : List String) (folds : List (String × Lang.Expr)) (e : Lang.Expr) (ty? : Option Lean.Expr) :
    TermElabM Lean.Expr := do
  let hs ← IO.mkRef #[]
  let r ← elabTermEnsuringType (← toTerm vars folds hs e) ty?
  synthesizeSyntheticMVars (postpone := .yes)
  -- each hole that fills fixes objects of the others (a coproduct, the relator of its fold): retry until none moves
  let mut todo ← hs.get
  repeat
    let n := todo.size
    todo ← todo.filterM fun h => catchInternalId postponeExceptionId (h *> pure false) fun _ => pure true
    if todo.size == n then break
  for h in todo do h
  pure r

/-- AOP's delimited notations make `est(`, `thin(` one Lean token where `rel` reads a name then `(`: each is
    a production here, read back (`lift`) as the builtin it spells. -/
syntax:max (name := rEst) "est(" rel ")" : rel
syntax:max (name := rThin) "thin(" rel ")" : rel

def delimited : List (SyntaxNodeKind × Op) := [(``rEst, .est), (``rThin, .thin)]

/-- `s` with each delimited notation read back and each one-argument fold `⦇R⦈` replaced by a fresh name not in `taken`, and `R` under that name: `Lang`
    has the program fold only, so the book's fold is read here, by syntax kind, before `Embed.expr` sees the term. -/
partial def lift (taken : List String) (s : Syntax) : StateM (Array (String × Syntax)) Syntax := do
  if let some o := delimited.lookup s.getKind then
    let h := mkNode ``Embed.hId #[mkIdentFrom s[0] (.mkSimple o.sym)]
    pure (mkNode ``Embed.rApp #[h, mkAtom "(", mkNullNode #[← lift taken s[1]], mkAtom ")"])
  else if s.getKind == ``Embed.rFold1 then
    let r ← lift taken s[1]
    let used := taken ++ (← get).toList.map (·.1)
    let n := ((List.range (used.length + 1)).map (s!"fold{·}")).find? (!used.contains ·) |>.getD "fold"
    modify (·.push (n, r)); pure (mkNode ``Embed.rId #[mkIdentFrom s (.mkSimple n)])
  else match s with
    | .node i k as => pure (.node i k (← as.mapM (lift taken)))
    | _ => pure s

-- `withoutPosition`: juxtaposition may cross a line here, the term ends at its `)`
syntax (name := relTerm) "rel(" withoutPosition(rel) ")" : term

@[term_elab relTerm] def elabRel : TermElab := fun stx ty? => do
  -- a builtin's name is the builtin (§c), so a local `F` or `α` is no relation of the term
  let vars := (← getLCtx).foldl (init := []) fun ns d =>
    let n := d.userName.toString false
    if d.isImplementationDetail || d.userName.hasMacroScopes || (Parse.builtin n).isSome || (prelude.lookup n).isSome
    then ns else n :: ns
  let (t, fs) := (lift vars stx[1]).run #[]
  let known := (vars ++ fs.toList.map (·.1)).map (·, 0)
  let read (s : Syntax) : TermElabM Lang.Expr := do
    match ((Embed.expr s).run (← getFileMap)).run' { cs := #[], known } with
    | .error e => throwErrorAt (← refAt e.pos) "{e.msg}"
    | .ok e => pure e
  let e ← read t
  let folds ← fs.toList.mapM fun (n, s) => do pure (n, ← read s)
  withRef stx do
    let r ← elabExpr vars folds e ty?
    -- the term names its locals by synthetic identifiers or by `fill`: a use the unused-variable linter cannot see
    for f in (collectFVars {} (← instantiateMVars r)).fvarIds do addTermInfo' stx (.fvar f)
    pure r

end LeetQ.Rel.Lang.Calc
