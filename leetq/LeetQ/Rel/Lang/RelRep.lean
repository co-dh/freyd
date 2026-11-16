import LeetQ.Run.Lang.Embed
import LeetQ.Rel.Lang.GenSpec

/-! `rel_rep n`: the proof that the code of the program `n` computes its terms. `rel_program n` emits only the
    program and records each definition's numbered term with the expansion's constants (`RegEntry.rep`); this
    command reads them back and assembles `n.rep_x : (n.x).ok = true → rep (n.x).rel = ⟦x⟧` from `GenSpec`'s
    lemmas, so a program's module imports no proof and only a module that wants the theorems imports this one. -/

namespace LeetQ.Rel.Lang

open LeetQ.Rel LeetQ.Rel.Alg

namespace Expand

open Lean Meta Elab Command

/-- The theorem of each shared constant (`n.c.c<i>.rep`), and the first combinator met with no lemma. -/
abbrev PM := StateT (Std.HashMap Name Name × Option Name) RM

/-- The lemma `n` at the proofs `hs` of its parts, its objects inferred from them; none where a part has none. -/
def lem (n : Name) (hs : List (Option Lean.Expr)) : PM (Option Lean.Expr) := do
  let some as := hs.mapM id | return none
  some <$> mkAppM n as.toArray

/-- A leaf lemma `n` whose objects only the term gives. -/
def lemO (n : Name) (as : Array (Option Lean.Expr)) : PM (Option Lean.Expr) := do some <$> mkAppOptM n as

mutual

/-- A proof of `Gen.Sound (code t) T`, `T` the allegory's term; a closed `t` cites its constant's theorem. -/
partial def prf (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) :
    PM (Option Lean.Expr) := do
  if !closed t then return ← prfNode pre ρ t
  let cd ← code pre ρ t
  let c := cd.appArg!.constName!
  if let some h := (← get).1[c]? then return some (mkConst h)
  let h := c ++ `rep
  -- under its number, `t`'s node: proving `.share k R` by `R`'s own `prf` would add `h` twice
  let some p ← (match t with | .share _ R => prfNode pre ρ R | t => prfNode pre ρ t) | return none
  -- `const_sound` at `c` itself, so the kernel meets `c =?= node(t) ()` and unfolds `c`, never the data
  let T := (← inferType p).appArg!
  let some (.defnInfo ci) := (← getEnv).find? c | throwError "rel_rep: internal: no definition `{c}`"
  let hb := g ``Gen.Sound.eq #[oE A, oE B, ci.value.appFn!, T, p]
  let ty := g ``Gen.Sound #[bE false, oE A, oE B, cd, T]
  addDecl (.thmDecl { name := h, levelParams := [], type := ty, value := g ``Gen.const_sound #[oE A, oE B, mkConst c, T, hb] })
  modify fun (m, g) => (m.insert c h, g)
  pure (some (mkConst h))

/-- A proof of `Gen.PSound (planOr t) T`, following `planOr`. -/
partial def pprf (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) :
    PM (Option Lean.Expr) := do
  let p {X Y : Obj} {e : Bool} (u : Tm X Y e) := prf pre ρ u
  let q {X Y : Obj} {e : Bool} (u : Tm X Y e) := pprf pre ρ u
  if closed t then return ← lem ``Gen.pleaf_sound [← p t]
  match A, B, d, t with
  | _, _, _, .val _ | _, _, _, .uni _ | _, _, _, .var _ => lem ``Gen.pleaf_sound [← prfNode pre ρ t]
  | _, _, _, .share _ R | _, _, _, .own R => q R
  | _, _, _, .comp R S => lem ``Gen.pcomp_sound [← q R, ← q S]
  | _, _, _, .conv R => lem ``Gen.pconv_sound [← q R]
  | _, _, _, .meet R S => lem ``Gen.pmeet_sound [← q R, ← q S]
  | _, _, _, .join R S => lem ``Gen.pjoin_sound [← q R, ← q S]
  | _, _, _, .diff R S => lem ``Gen.pdiff_sound [← q R, ← q S]
  | _, _, _, .ldiv R S UB UC => lem ``Gen.pldiv_sound [← q R, ← q S, ← p UB, ← p UC]
  | _, _, _, _ => lem ``Gen.pleaf_sound [← p t]

/-- A proof of `Gen.Sound (node t) T`, one `GenSpec` lemma per node, following `node`. -/
partial def prfNode (pre : Name) (ρ : List (Nat × Lean.Expr)) {A B : Obj} {d : Bool} (t : Tm A B d) :
    PM (Option Lean.Expr) := do
  let p {X Y : Obj} {e : Bool} (u : Tm X Y e) := prf pre ρ u
  let q {X Y : Obj} {e : Bool} (u : Tm X Y e) := pprf pre ρ u
  match A, B, d, t with
  | _, _, _, .val R => lem ``Gen.val_sound [some (← liftE (relE R))]
  | A, _, _, .uni (m := m) U => lemO ``Gen.uni_sound #[oE A, uE m, ← liftE (valsE A m U)]
  | A, B, _, .zero => lemO ``Gen.zero_sound #[oE A, oE B]
  | A, _, _, .id => lemO ``Gen.id_sound #[oE A]
  | A, _, _, .top V => match ← p V with
    | some h => lemO ``Gen.top_sound #[oE A, none, none, none, h]
    | none => pure none
  | _, B, _, .mem => lemO ``Gen.mem_sound #[oE B]
  | .prod A B, _, _, .outl => lemO ``Gen.outl_sound #[oE A, oE B]
  | .prod A B, _, _, .outr => lemO ``Gen.outr_sound #[oE A, oE B]
  | A, .sum _ B, _, .inl => lemO ``Gen.inl_sound #[oE A, oE B]
  | B, .sum A _, _, .inr => lemO ``Gen.inr_sound #[oE A, oE B]
  | _, _, true, .comp R S => lem ``Gen.comp_sound [← p R, ← p S]
  | _, _, false, .comp R S => lem ``Gen.compB_sound [← q R, ← q S]
  | _, _, _, .conv R => lem ``Gen.conv_sound [← p R]
  | _, _, _, .meet (d := false) (e := false) R S => lem ``Gen.meetB_sound [← q R, ← q S]
  | _, _, _, .diff (d := false) (e := false) R S => lem ``Gen.diffB_sound [← q R, ← q S]
  | _, _, _, .meet R S => lem ``Gen.meet_sound [← p R, ← p S]
  | _, _, _, .join R S => lem ``Gen.join_sound [← p R, ← p S]
  | _, _, _, .diff R S => lem ``Gen.diff_sound [← p R, ← p S]
  | _, _, _, .dom R => lem ``Gen.dom_sound [← p R]
  | _, _, _, .ran R => lem ``Gen.ran_sound [← p R]
  | _, _, _, .ldiv R S UB UC => lem ``Gen.ldivB_sound [← q R, ← q S, ← p UB, ← p UC]
  | _, _, _, .rdiv R S UA UB => lem ``Gen.rdiv_sound [← p R, ← p S, ← p UA, ← p UB]
  | _, _, _, .pair R S => lem ``Gen.pair_sound [← p R, ← p S]
  | _, _, _, .prod R S => lem ``Gen.prod_sound [← p R, ← p S]
  | _, _, _, .junc R S => lem ``Gen.junc_sound [← p R, ← p S]
  | _, _, _, .own R | _, _, _, .share _ R => p R
  | _, _, _, .prim r => modify (fun (m, g) => (m, g <|> some r.sig.1)); pure none
  | _, _, _, _ =>
    -- a call is named by its constant, not by the `Gen.ofPl` that runs its plan
    let e ← node pre ρ t
    let f := (if e.isAppOf ``Gen.ofPl then e.appArg! else e).getAppFn.constName?
    modify fun (m, g) => (m, g <|> f); pure none

end

/-- The theorems `n.rep_x` of the program `n`, from the terms and constants `emit` recorded, and `n.unproved`:
    the definitions with none, each with the first combinator `GenSpec` has no lemma for. -/
def rep (n : Name) : MetaM Unit := do
  let some (ds, shared, codes) := (relRegistry.getState (← getEnv)).reps[n]?
    | throwError "rel_rep: `{n}` is no rel_program"
  -- `emit`'s constants by value and by number, so `code` finds each one and adds none
  let st : Std.HashMap Lean.Expr Name × Std.HashMap Nat Lean.Expr := (.ofList shared.toList, .ofList codes.toList)
  let unproved ← (do
    let mut gaps : List (String × String) := []
    for (x, ⟨_, _, _, t⟩) in ds do
      let kc := mkConst (Parse.constOf n x)
      modify fun (m, _) => (m, none)
      let body : PM (Option String) := do
        match ← prf n [] t with
        | some p =>
          let ty ← mkArrow (← mkEq (← mkAppM ``CRel.ok #[kc]) (toExpr true))
            (← mkEq (← mkAppM ``LeetQ.Rel.Rep.rep #[← mkAppM ``CRel.rel #[kc]]) (← inferType p).appArg!)
          let pv ← mkAppM ``Gen.Sound.eq #[p]
          addDecl (.thmDecl { name := n ++ Name.mkSimple s!"rep_{x}", levelParams := [], type := ty, value := pv })
          pure none
        | none => pure (((← get).2.map toString).getD "?")
      -- a fresh heartbeat count per theorem, since the command has spent its own
      if let some c ← withCurrHeartbeats body then gaps := gaps ++ [(x, c)]
    pure gaps : PM (List (String × String))).run' ({}, none) |>.run' st
  let sty := pairT (mkConst ``String) (mkConst ``String)
  addConst (n ++ `unproved) (listT sty) (← mkListLit sty (unproved.map fun (x, c) =>
    mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``String) (toExpr x) (toExpr c)))

/-- `rel_rep n`: `n.rep_x` for each definition `x` of the program `n` the proofs reach, and `n.unproved` (`rep`). -/
syntax (name := relRep) "rel_rep " ident : command

@[command_elab relRep] def elabRelRep : CommandElab := fun stx => do
  let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[1])
  liftTermElabM (rep n)

end Expand

end LeetQ.Rel.Lang
