# Rel language review: duplicated knowledge, simpler design, dependencies

Read-only review of `leetq/LeetQ/Run/Lang/*` (Syntax, Parse, Embed, Elab, Bits, Gen, Expand, Plan),
`leetq/LeetQ/Rel/Lang/{GenSpec,EmitC}`, `leetq/LeetQ/Aop/{Calc,RelAop,Prelude}` and `Rel/Programs/Prelude` at
`20bb9fb`. Paths below are relative to `leetq/LeetQ/`. It does not repeat `doc/rel-architecture-review.md`,
`doc/rel-dry-audit.md`, `doc/rel-lean-mapping.md`, `duplicated.md`; a finding marked `open` is one of theirs that
the code still shows, with the old number.

Two limits on the evidence:

- The index `.lake/build/refactor-index.db` is older than `HEAD`: it predates rows 191 (`prims` table) and 204
  (`Route` deleted), has no `Aop.Prelude`, `Aop.Mss`, `Rel.RefoldSpec`, `Rel.Lang.PlanSpec`. Every `module_need`
  figure below was checked against the source; where the two disagree the source is quoted.
- A claim marked PLAUSIBLE was not carried through to a compiled change.

## Ranked table

| #  | finding                                      | kind   | survivor                 | lines  | risk | new/open   |
|----|----------------------------------------------|--------|--------------------------|--------|------|------------|
| 1  | `Tm` lives in the elaborator's module        | dep    | `Tm` in its own module   | 0      | low  | new        |
| 2  | every program imports `GenSpec`'s proof tree | dep    | proofs by their own cmd  | ≈ −10  | med  | new        |
| 3  | a non-`prims` builtin is written in 8 places | dup    | the `prims` row          | ≈ −150 | high | open #9    |
| 4  | hand traversals over `Pre` and over `Tm`     | dup    | `Pre.parts`, a child map | ≈ −40  | med  | open #10   |
| 5  | `Registry` beside Lean's environment         | design | the environment          | ≈ −40  | high | open #3 #4 |
| 6  | `pmatch`: a second unifier for signatures    | design | `oty` + `unify`          | ≈ −25  | med  | new        |
| 7  | `Gen`: literal/`F` pairs, 4 `ran(∋)` copies  | dup    | the `F` form, one helper | ≈ −20  | low  | new        |
| 8  | family-index classes computed twice          | dup    | one function in `Elab`   | ≈ −12  | low  | new        |
| 9  | a `prims` row's type is checked three ways   | dup    | `isDefEq` (`primE`)      | ≈ −10  | low  | new        |
| 10 | `useDef` picks kernel forms by constant name | design | the `Prim.prelude` row   | ≈ −10  | med  | open #18   |
| 11 | `Plan` imports `Expand`, uses nothing of it  | dep    | `Plan → Elab`            | 0      | low  | new        |
| 12 | `Aop.Calc` imports the compiler for grammar  | dep    | `Embed` split in two     | 0      | low  | new        |
| 13 | object grammar in `Embed` and in `Parse`     | dup    | the `relObj` kind        | ≈ −15  | low  | open #1    |
| 14 | `Once`, `Sig` are tuples read by position    | design | a structure (new type)   | ≈ +5   | low  | new        |

`kind`: `dep` is a dependency finding, `dup` duplicated knowledge, `design` a simpler design. `lines` is the net
line change. Rows 3, 6, 10, 13 are PLAUSIBLE in their estimate. Rows 1, 2, 12, 14 need a user decision (last section).

## Dependency graph

Import edges between the Rel language modules, from the `import` lines at `20bb9fb`. `Def*` stands for the
`Run.CRel*Def` modules.

Before:

```
Syntax   → QLean.Kernel.Elementwise, CRelDef, CRelArithDef, CRelRelDef, CRelListDef, CRelFoldDef, CRelPowerDef,
           CRelLoopDef
Parse    → Syntax
Elab     → Run.Algebra, Syntax
Bits     → Elab
Gen      → AC3Def, 8 Def*, Bits
Expand   → Gen, Elab, Parse
Embed    → Parse, Expand
Plan     → Expand, QLean.Db.Own
EmitC    → Plan
PlanSpec → EmitC
BitsSpec* (5 modules) → Bits, Rel.KernelWF.*, Rel.Rep*
GenSpec  → Gen, BitsSpecRun, Rel.CRelRel, Rel.CRelArith, Rel.CRelFold
RefoldSpec → GenSpec
Programs.Prelude → Embed, GenSpec
Aop.Calc → Embed, 12 Freyd/AOP modules
Aop.RelAop → Aop.Calc, AOP.A6_ConsList
Aop.Prelude → Aop.RelAop, Programs.Prelude, AOP.A4_6, AOP.A7_1
```

After rows 1, 2, 11, 12 (changed lines only):

```
Tm       → Run.Algebra, Syntax                    -- new module: lines 19–106 of Elab.lean
Elab     → Tm
Bits     → Tm                                     -- was Elab
Plan     → Tm, QLean.Db.Own                       -- was Expand
EmitC    → Plan, Expand                           -- it calls Expand.read (Rel/Lang/EmitC.lean:34)
Grammar  → Parse                                  -- new module: Embed's syntax categories and Syntax → Expr
Embed    → Grammar, Expand
Aop.Calc → Grammar, 12 Freyd/AOP modules          -- was Embed
Programs.Prelude → Embed                          -- GenSpec dropped
Rep (new command module) → Embed, GenSpec         -- imported by the modules that want `n.rep_x`
```

Transitive import counts from the index (stale for `Syntax`, which then imported no `Def*`):

| module             | imports | of them `LeetQ.*` | Freyd/AOP |
|--------------------|---------|-------------------|-----------|
| `Run.Lang.Elab`    | 31      | 9                 | 0         |
| `Run.Lang.Embed`   | 46      | 23                | 0         |
| `Run.Lang.Plan`    | 46      | 22                | 0         |
| `Rel.Lang.GenSpec` | 145     | 104               | 8         |
| `Programs.Prelude` | 149     | 108               | 8         |
| `Aop.Calc`         | 145     | 24                | 92        |

## 1. `Tm` lives in the elaborator's module (dependency, new)

- `Run/Lang/Elab.lean:19–106` declares `Tm`; the rest of the 1825-line file is the `MetaM` elaborator.
- `Run/Lang/Bits.lean:1` imports `Elab` and uses only `Tm` (`Tm.isVal` 33, `Tm.tableC` 44, `Tm.bits` 192).
  `Gen` imports `Bits` (`Pl` carries a `Tm`), `GenSpec` and the five `BitsSpec*` modules import those. So the
  generated runtime code and 1936 lines of bit-matrix proofs sit downstream of the elaborator.
- `Elab.lean` had 38 commits in the last 30 days, `Bits.lean` 3. Each of those 38 rebuilt `Bits`, `BitsSpec`,
  `BitsSpecCode`, `BitsSpecLdiv`, `BitsSpecPairs`, `BitsSpecRun`, `Gen`, `GenSpec`, `RefoldSpec`, `Plan`.
- Cut: move lines 19–106 to `Run/Lang/Tm.lean` (imports `Run.Algebra` and `Syntax`, for `Prim` in `Tm.prim`).
  `Bits` and `Plan` import it instead of `Elab`. No declaration changes name or namespace.
- Effect: an elaborator edit no longer rebuilds those 10 modules. `Syntax.lean:18`
  (`deriving instance DecidableEq for Obj`) is the one other thing `Bits` and `BitsSpec*` take from the front end;
  it belongs beside `Obj`, PLAUSIBLE.
- Risk: none on proofs. It is a new module, so it needs approval.

## 2. Every program imports the proof tree (dependency, new)

- `Rel/Programs/Prelude.lean:2` imports `Rel.Lang.GenSpec`; every program imports the prelude. A program's import
  closure is 149 modules where `Embed`'s is 46.
- The reason is in `Run/Lang/Expand.lean:783–791`: `emit` (979–992) builds `n.rep_x` during `rel_program`, and
  `prf`/`pprf`/`prfNode` (801–880) cite the `GenSpec` lemmas by a name built from a string
  (``gs `comp_sound``), looked up with `need`, because `Expand` must not import the proofs.
- `doc/rel-dry-audit.md` §2 took the proofs off the run path by splitting `CRel*` into `Def` modules. This edge
  puts 103 proof modules back on it: an edit in `Rel.KernelWF.*`, `Rel.Rep*`, `BitsSpec*` rebuilds and re-expands
  all 16 programs, `Aop.*` and the tests.
- Cut: `prf`, `pprf`, `prfNode` and the `rep_x` block of `emit` move to a module that imports `GenSpec` and are
  run by a command of their own (`rel_rep n`). There they name the lemmas as ``` ``Gen.comp_sound ```, checked when
  that module compiles; `need` and `gs` go (≈ −10 lines).
- Effect: a program imports 46 modules, not 149; a proof edit rebuilds only the modules that ask for `rep_x`.
- Risk: the prover needs the numbered `Tm`s and the `n.c.c<i>` constants `emit` made, so it either reads the
  program a second time (`Expand.read`) or `emit` keeps them. `n.unproved` moves with it; `Test.lean` and the
  programs that state theorems over `rep_x` (12 of 16 use `GenSpec` constants in the index) gain one command.

## 3. A builtin outside `prims` is written in 8 places (duplicate, open: dry-audit #9)

Row 191 moved 18 builtins to one row each. The others (`id`, `zero`, `top`, `mem`, `outl`, `outr`, `inl`, `inr`,
`leq`, `lt`, `succ`, `arith`, `nil`, `alpha`, `index`, `dom`, `ran`, `lam`, `E`, `P`, `est`, `thin`, …) are still
stated at each stage:

| stage                         | anchor                                              |
|-------------------------------|-----------------------------------------------------|
| symbol and arity              | `Run/Lang/Syntax.lean:155–180` (`Op`, `Op.table`)   |
| type                          | `Run/Lang/Elab.lean:771–801` (`constant`)           |
| untyped and typed constructor | `Elab.lean:209–272` (`Pre`), `19–106` (`Tm`)        |
| `Pre → Tm`                    | `Elab.lean:1571–1745` (`build`)                     |
| converse                      | `Elab.lean:1332–1416` (`convTm`)                    |
| runtime                       | `Run/Lang/Gen.lean` (one `def` per constructor)     |
| `Tm → Expr`                   | `Run/Lang/Expand.lean:693–774` (`node`)             |
| proof                         | `Expand.lean:840–878` (`prfNode`)                   |
| AOP reading                   | `Aop/Calc.lean:97–120` (`builtins`), `200–252`      |

- Survivor: the `prims` row (`Syntax.lean:112–148`), whose `sig` is read from the `CRel` constant and whose `aop`
  field already carries the AOP reading. A leaf builtin with a `CRel` constant (`outl`, `outr`, `inl`, `inr`,
  `mem`, `nil`, `succ`) fits the row as it is.
- Gap: a row has no parts. The combinators (`dom`, `ran`, `lam`, `E`, `est`, …) take relation arguments and a key
  demand; they stay constructors unless `Prim` gains an argument list, which is a wider type, not a new one.
- Net: ≈ −150 lines for the leaves alone, PLAUSIBLE. Risk: high. `GenSpec` has one `_sound` lemma per `Gen`
  definition (`outl_sound` … `mem_sound`, `Rel/Lang/GenSpec.lean:96–118`) that `prfNode` matches by constructor; a
  row needs its lemma named in the row. `Bits` and `Plan.ofTm` match on the same constructors.

## 4. Hand traversals over `Pre` and over `Tm` (duplicate, open: dry-audit #10)

- `Pre` (`Elab.lean:209–272`) repeats `Tm`'s constructor list with `OTy` in place of `Obj`. That part is unchanged
  since the audit and stays, because `Tm` is indexed by objects that `Pre` does not have yet.
- New here: the traversals that list every constructor again.
  - `Pre.parts` (`Elab.lean:410–426`) is already the children function. `Pre.nilSrcs` (382–391) returns the same
    children at every constructor (`.call` its alternative, `.fix` its body, `.refold` coalgebra and body, `.top`
    its target), so it is `| .nil a _ => [a] | x => x.parts.flatMap (·.1.nilSrcs)`: ≈ −8 lines, checked by
    reading both.
  - `Pre.at` (277–317, 41 lines) is a third list of the same children, PLAUSIBLE instance of `parts`.
  - Over `Tm`: `fv` (`Expand.lean:129–145`), `mus` (470–484), `number` (491–527). Each is a fold or a map over
    the children; one `Tm` child map, with the existential `Σ A B d, Tm A B d` as the child type, serves all
    three. ≈ −30 lines, PLAUSIBLE.
- Risk: medium. `number` rewrites `share` numbers in a `StateM`, so the child map has to be monadic; `fv` and
  `mus` are used by `emit` before `number` (`Expand.lean:936–937`), an order the refactor must keep.

## 5. `Registry` beside Lean's environment (design, open: dry-audit #3, #4, #6)

- `Expand.lean:892–919`: `RegEntry` has four cases and `Registry` four tables.
  - `.ext e home` maps a constant to its definition and program. The constant is already in the environment and
    `Embed.resolverAt` (`Embed.lean:563–579`) already resolves names with `resolveGlobalName`, then filters
    through `reg.exts`.
  - `.prog n ns opens` stores a namespace and `open` list, which the environment holds for the declaration.
  - `.chain n ns` is the import closure of programs.
  - `.call c s` maps an elaborated constant to its `Sig`; this one has no Lean counterpart.
- The program itself is a constant `n : Program` built with `ToExpr` and read back with `evalConstCheck`
  (`Embed.lean:543–549`).
- Survivor: the environment. Gap: `calls` needs an extension (a `Sig` is not a Lean type); `.ext`'s `home` is the
  constant's prefix. Net ≈ −40 lines, PLAUSIBLE. Risk: high — `Rel/Lang/ModuleTest.lean` (167 lines) pins the
  resolution order and the ambiguity errors.

## 6. `pmatch` is a second unifier for declared signatures (design, new)

- `Elab.lean:1098–1133`: `Match`, `split`, `pmatch` match a declared `OExp` against an `OTy`, binding type
  variables by hand and returning `.clash`.
- `Elab.lean:499–508` (`oty`) already turns an `OExp` into an `OTy` with a metavariable per variable, and
  `unify` (row 194) is Lean's `isDefEq`. Matching a signature is `unify (← oty sig) actual` with fresh
  metavariables for the declared variables.
- There is a third matcher of the same grammar, `Prim.fits` (row 9).
- Net ≈ −25 lines, PLAUSIBLE. Risk: medium — `pmatch` is one-sided (it binds only the declared variables) and the
  `.clash` message names both sides; tests in `Rel/Lang/Test.lean` pin that text.

## 7. `Gen`: literal and `F` variants, four `ran(∋)` copies (duplicate, new)

- `Run/Lang/Gen.lean:182–195`: `succ`/`succF`, `arith`/`arithF`, `leq`/`leqF`, `lt`/`ltF`. The first of each takes
  the universe as a literal, the second as a `Fn`; `Expand.lean:737–748` chooses with a `match … | none =>`.
  The literal is the `F` form at `Gen.uni`: ≈ −15 lines, PLAUSIBLE.
- `Gen.lean:148–155`: `E`, `filter`, `takewhile`, `map` are four copies of
  `let k := CRel.ran (CRel.mem D.val); also k.ok (CRel.<op> (R (Dem.of d k.rel)) D.val)`. One helper taking the
  `CRel` op: ≈ −5 lines.
- `Elab.lean:1725–1728` (`build`, `.call`) and `1775–1778` (`test`, `.call`) are the same four lines.
- Risk: low. `GenSpec` has no lemma for any of these definitions (its theorem list ends at the bit-plan lemmas),
  so no proof is redone. `meet`/`join`/`diff` and `pmeet`/`pjoin`/`pdiff` (`Gen.lean:129–134`, `279–284`) look
  alike too, but each has its own lemma (`GenSpec.lean:154–175`, `273–304`); leave them.

## 8. Family-index classes computed twice (duplicate, new)

- `Elab.lean:1264–1277` (`mkDef`) and `Expand.lean:259–273` (`callDef`) both number a definition's distinct
  family indices by first occurrence; the comment in `callDef` says "as `mkDef` numbers them".
- Survivor: one function in `Elab` returning the classes, called by both. ≈ −12 lines.
- Risk: low. The two must agree for a call to line up with its definition, which is the reason to have one.

## 9. A `prims` row's type is checked three ways (duplicate, new)

- `Elab.lean:765–768` (`Prim.inst`): the row's `sig` instantiated and unified at elaboration.
- `Syntax.lean:343–351` (`Prim.fits`): a hand matcher of `OExp` against `Obj`, used once, at `Elab.lean:1669`.
- `Expand.lean:607–620` (`primE`): the row's constant fitted to the node's objects by `isDefEq`.
- Survivor: `isDefEq` in `Prim.inst` and `primE`, which read the constant's own type. `Prim.fits` restates the
  object grammar and can only repeat what `primE` will decide; drop it and the `if` at 1669. ≈ −10 lines.
- Risk: low. A misfit is then reported by `primE` at expansion instead of by `build`; both are internal errors.

## 10. `useDef` picks kernel forms by constant name (design, open: dry-audit #18, grown)

- `Expand.lean:36–52`: `prelude.perm` becomes `.own`, `prelude.filter` and `prelude.takewhile` become their `Tm`
  constructors, by comparing the constant's name; `tails`, `prefix`, `suffix`, `concat` go through
  `Prim.prelude` rows. The audit had one name (`perm`); there are now three, and two mechanisms.
- Survivor: the `Prim.prelude` row (`Syntax.lean:109`: "a prelude definition `sym` run as it"). Gap: `filter` and
  `takewhile` take a relation parameter, which a row cannot hold today (same gap as row 3); `perm` needs a row
  flag for "its converse is itself".
- Net ≈ −10 lines, PLAUSIBLE. Risk: medium — `Programs/Prelude.lean:36–39` documents the `perm` rule.

## 11. `Plan` imports `Expand` and uses nothing of it (dependency, new)

- `Run/Lang/Plan.lean:1` imports `Run.Lang.Expand`. `module_need` records `Plan → Run.Core` and
  `Plan → Run.Lang.Elab` only (every `Tm` constructor, for `ofTm` at `Plan.lean:332`); the source has no
  `Expand.`, `Gen.`, `Parse.` or `Program`.
- Cut: `Plan` imports `Elab` (after row 1, `Tm`). `Rel/Lang/EmitC.lean` adds `import LeetQ.Run.Lang.Expand`,
  which it uses at line 34 (`Expand.read`).
- Effect: `Plan` (417 lines) stops rebuilding on edits to `Expand` (37 commits in 30 days), `Gen`, `Bits`,
  `Parse`. With row 1 its closure falls from 46 modules to about 31.
- `PlanSpec → EmitC`: whether `PlanSpec` needs the C printer or only `Plan` could not be read from the index
  (the module is newer than it). PLAUSIBLE second cut.

## 12. `Aop.Calc` imports the compiler for the grammar (dependency, new)

- `Aop/Calc.lean:1` imports `Run.Lang.Embed`. It uses `Embed.expr`, `Parse.P`, `Parse.S`, `Parse.builtin` and the
  `Syntax` types (`Expr`, `Op`, `Bin`, `Pos`), from `dep`; plus the `rel` syntax category.
- `Embed` imports `Expand`, so `Calc` and `CalcTest` also load `Elab`, `Bits`, `Gen`, `Expand`, `AC3Def`,
  `CRelEstDef`.
- Cut: `Embed.lean` splits at the command: the syntax categories and `Syntax → Expr` (`Embed.lean:134–270`, with
  `expr`) into a grammar module importing `Parse`; `stmt`, `program`, `define`, the registry writes stay.
- Effect: 6 fewer modules under `Calc`; `Calc` does not rebuild on `Elab`/`Expand` edits. `RelAop` still needs
  `Expand` (`relRegistry`, `Embed.programOf`), so the gain stops at `Calc` and `CalcTest`.
- Related, new since row 191: `Syntax.lean:1–9` imports `QLean.Kernel.Elementwise` and seven `Def*` modules for
  the `prims` table (`prim%` reads the constants, 77–104). Before that row `Syntax` imported 2 modules. `Parse`
  needs only a row's symbol. Moving `prims` after `Parse` would need `Op.table` (169–180) to take the symbols
  from elsewhere; not proposed, because every importer except `Parse` loads the runtime through `Elab` anyway.

## 13. Object grammar exists in `Embed` and in `Parse` (duplicate, open: remainder of dry-audit #1)

- `Embed.lean:154–159` declares `relObj` productions (`oWord`, `oPow`, `oList`, `oParen`, `oProd`, `oSum`) and
  `Embed.obj` (261–270) then hands the token text to `Parse.object` (`Parse.lean:182–213`), which parses the same
  grammar by hand.
- Survivor: the syntax category. Gap: `𝒫A` reaches `Embed` as one Lean identifier, so the `𝒫` prefix still has to
  be cut from the token (`Parse.oprim`).
- Net ≈ −15 lines, PLAUSIBLE. Risk: low; `Rel/Lang/EmbedTest.lean` covers object syntax.

## 14. `Once` and `Sig` are tuples read by position (design, new)

- `Elab.lean:327–338` defines `Form`, `Sig`, `Once` as nested tuples; `Expand.lean:234` reads a field as
  `o.1.2.2.2.2.2.1`, `Expand.lean:953` destructures seven components. Row 207 added an eighth (`kf`).
- A structure would name the fields; it is a new type, so it is listed for a decision, not proposed.

## Decisions for the user

- A. Row 1: approve the new module `Run/Lang/Tm.lean` (a file split, no new type).
- B. Row 2: move `rep_x` generation out of `rel_program` into its own command, so programs stop importing
  `GenSpec`. It changes where each program's theorems are produced.
- C. Row 12: approve splitting `Embed.lean` into a grammar module and the command.
- D. Row 14: `Once`/`Sig` as structures (new types), or leave the tuples.
- E. Rows 3 and 10: whether `Prim` may carry relation parameters, so that combinators and `filter`/`takewhile`
  become rows. Without it both findings stop at the leaf builtins.
