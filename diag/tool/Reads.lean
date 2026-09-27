/-
  WHAT A PICTURE READ OF THE ENVIRONMENT, so it is redrawn exactly when one of those reads would
  now answer differently.

  Every drawing reads the exporter's code, the definitions, the instances and the printing rules —
  `envPrint`'s `shared` — and a change there redraws everything.  THEOREMS are what one picture reads and the next does
  not: a candidate bucket, a statement a dot cites, the declaration drawn.  So a theorem is a read a
  drawing RECORDS (`noteRead`) at the one place it enumerates or opens it, memoised or not, and a
  picture keeps its file while every theorem it recorded hashes as it did.  Keying on the whole
  imported environment instead redrew every picture after any edit, since the exporter imports
  nearly the whole library.
-/
import Lean

open Lean

namespace Freyd.StrDiag

/-- The head of a statement's CONCLUSION, under whatever `∀` binders it carries. -/
partial def concHead : Expr → Name
  | .forallE _ _ b _ => concHead b
  | .mdata _ b => concHead b
  | t => (t.getAppFn.constName?).getD Name.anonymous

/-- A name as its COMPONENTS: `Name.toString`'s `«»` escapes are a second grammar to parse back. -/
def nameJson (n : Name) : Json :=
  .arr (n.components.toArray.map fun | .str _ s => .str s | .num _ k => toJson k | _ => .null)

def jsonName (j : Json) : Except String Name := do
  (← j.getArr?).foldlM (init := .anonymous) fun n c => match c with
    | .str s => pure (.str n s)
    | c => do pure (.num n (← c.getNat?))

/-- One read of the environment beyond `shared`. -/
inductive Read where
  /-- every constant concluding in `h`: a candidate bucket, a catalogue of lanes -/
  | head (h : Name)
  /-- every constant directly under the namespace `p` -/
  | pre (p : Name)
  /-- every theorem of the module `m` -/
  | module (m : Name)
  /-- every theorem -/
  | thms
  /-- `n`'s statement -/
  | stmt (n : Name)
  /-- `n`'s statement and value: a declaration the picture draws -/
  | decl (n : Name)
  deriving BEq, Hashable

def Read.json : Read → Json
  | .head h => .arr #["head", nameJson h]
  | .pre p => .arr #["pre", nameJson p]
  | .module m => .arr #["module", nameJson m]
  | .thms => .arr #["thms"]
  | .stmt n => .arr #["stmt", nameJson n]
  | .decl n => .arr #["decl", nameJson n]

def Read.ofJson (j : Json) : Except String Read := do
  match ← j.getArr? with
  | #[.str "head", n] => return .head (← jsonName n)
  | #[.str "pre", n] => return .pre (← jsonName n)
  | #[.str "module", n] => return .module (← jsonName n)
  | #[.str "thms"] => return .thms
  | #[.str "stmt", n] => return .stmt (← jsonName n)
  | #[.str "decl", n] => return .decl (← jsonName n)
  | _ => throw s!"no read: {j.compress}"

/-- The reads of the picture being drawn.  Pictures are drawn one after another in a process, and
    `takeReads` empties it for the next. -/
initialize readsRef : IO.Ref (Std.HashSet Read) ← IO.mkRef {}

def noteRead (r : Read) : BaseIO Unit := readsRef.modify (·.insert r)

/-- The reads so far, in one order a later process reads back and hashes in, and none left. -/
def takeReads : BaseIO (Array Read) :=
  readsRef.modifyGet fun s => ((s.toArray.qsort fun a b => a.json.compress < b.json.compress), {})

/-- The environment hashed ONCE per process, by what a `Read` asks of it.  Sums, not a chain: the
    constant table's order is no part of what it holds. -/
structure EnvPrint where
  shared : UInt64
  heads : Std.HashMap Name UInt64 := {}
  pres : Std.HashMap Name UInt64 := {}
  modules : Std.HashMap Name UInt64 := {}
  thms : UInt64 := 0

/-- The `(key, declaration)` pairs a keyed attribute holds: an unexpander or a delaborator is a
    definition, and which constant it prints is the attribute's, not the definition's. -/
def keyedDecls {γ : Type} (a : KeyedDeclsAttribute γ) (env : Environment) : UInt64 :=
  (a.ext.getState env).table.fold (init := 0) fun h k es =>
    es.foldl (fun h e => h + mixHash (hash k) (hash e.declName)) h

/-- THE EXPORTER'S OWN CODE: the `.olean.hash` Lake writes beside each `diag/tool` module, a hash
    of the olean's content.  Not the binary's: it relinks after any edit to the library it imports,
    which leaves the tool's code as it was.  The tool is no module of the drawn environment. -/
def codeKey : IO UInt64 := do
  let mut h : UInt64 := 13
  let fs := (← System.FilePath.readDir "diag/tool").map (·.path) |>.filter (·.extension == some "lean")
  for f in fs.qsort (·.toString < ·.toString) do
    let some stem := f.fileStem | throw <| IO.userError s!"diag-export: {f} has no file stem"
    let p := (← findOLean (Name.str `diag.tool stem)).addExtension "hash"
    let s ← try IO.FS.readFile p catch e =>
      throw <| IO.userError s!"diag-export: {p}: {e} — `lake build diag-export` writes it beside the olean"
    h := mixHash (mixHash h (hash stem)) (hash s)
  return h

initialize envPrintRef : IO.Ref (Option EnvPrint) ← IO.mkRef none

/-- `shared` is every constant that is NOT a theorem, by statement, value and reducibility, every
    instance by priority, and the printing attributes; the toolchain's constants by its version.
    The theorems are summed per `Read` instead.  `extra` is what only the caller can name — the
    simp sets it runs. -/
def envPrint (extra : UInt64) : CoreM EnvPrint := do
  if let some p ← envPrintRef.get then return p
  let env ← getEnv
  let toolchain := env.header.moduleNames.map fun m => [`Init, `Std, `Lean, `Lake].contains m.getRoot
  let add (m : Std.HashMap Name UInt64) (k : Name) (h : UInt64) := m.insert k (m.getD k 0 + h)
  let mut p : EnvPrint := { shared := mixHash (mixHash (hash Lean.versionString) extra) (← codeKey) }
  for (n, ci) in env.constants do
    -- A constant of no module is the drawing's own (an auxiliary lemma a simp call added), which a
    -- later process does not have.
    let some idx := env.getModuleIdxFor? n | continue
    if toolchain[idx.toNat]! then continue
    let h := mixHash (hash n) (hash ci.type)
    p := { p with heads := add p.heads (concHead ci.type) h, pres := add p.pres n.getPrefix h }
    match ci with
    | .thmInfo _ =>
      let m := env.header.moduleNames[idx.toNat]!
      p := { p with thms := p.thms + h, modules := add p.modules m h }
    | _ =>
      -- A `match` in a proof compiles to a matcher named under the theorem: part of the proof,
      -- which no picture reads but the theorem's own (`decl`).
      if (Meta.Match.Extension.getMatcherInfo? env n).isSome
        && (env.find? n.getPrefix).any (· matches .thmInfo _) then continue
      let v := (ci.value? (allowOpaque := true)).elim 0 hash
      let r := (getReducibilityStatusCore env n).ctorIdx.toUInt64
      p := { p with shared := p.shared + mixHash (mixHash h v) r }
  let insts := (Meta.instanceExtension.getState env).instanceNames.foldl (init := 0) fun h n e =>
    h + mixHash (hash n) e.priority.toUInt64
  let printers := mixHash (keyedDecls PrettyPrinter.Delaborator.appUnexpanderAttribute env)
    (keyedDecls PrettyPrinter.Delaborator.delabAttribute env)
  p := { p with shared := mixHash (mixHash p.shared insts) printers }
  envPrintRef.set (some p)
  return p

/-- What `r` reads now.  A declaration that is gone reads as `1`, so a picture citing a theorem
    since deleted is redrawn; the DRAWN declaration gone is the caller's error to raise. -/
def EnvPrint.of (p : EnvPrint) (env : Environment) : Read → UInt64
  | .head h => p.heads.getD h 0
  | .pre q => p.pres.getD q 0
  | .module m => p.modules.getD m 0
  | .thms => p.thms
  | .stmt n => (env.find? n).elim 1 fun ci => mixHash (hash n) (hash ci.type)
  | .decl n => (env.find? n).elim 1 fun ci =>
      mixHash (mixHash (hash n) (hash ci.type)) ((ci.value? (allowOpaque := true)).elim 0 hash)

end Freyd.StrDiag
