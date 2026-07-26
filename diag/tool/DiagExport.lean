/-
  `diag-export` — draw the STATEMENT of a Lean declaration as a string diagram.

  `./scripts/diag-export Freyd.Diag.dom_cd` writes `diag/generated/Freyd.Diag.dom_cd.typ`, a page
  that imports `../strdiag.typ` and draws the theorem's two sides joined by its relation symbol.
  The proof is not looked at; only `ConstantInfo.type`.

  WHY THIS IS A TERM WALK AND NOT A GRAPH LAYOUT.  A statement of this calculus is a composite of
  arrows, and a composite is a TREE, so its picture is built left to right by structural recursion —
  there is nothing to route.  Everything the walk does not recognise degrades to an opaque labelled
  box carrying the pretty-printed subterm, so an unknown operator costs one box, never a failure.

  WHAT IS RECOGNISED.  `Cat.comp` flattens into a run of cells; `Cat.id` is a bare wire;
  `Allegory.inter`/`Diag.meet` draw the `Δ;(R ⊗ S);∇` block; `Allegory.recip`/`Diag.conv` draw the
  bent wire.  At the top, `Alg.le` (`⊑`), `LE.le` (`≤`) and `Eq` split the statement into two
  pictures with the symbol between them.

  Operands of a meet or a converse are drawn as single boxes rather than as nested pictures:
  `strdiag.typ`'s `meet` and `conv` take a LABEL, not a sub-picture, and a nested layout would need
  the combinators to be re-cut for arbitrary depth.  A composite inside a meet therefore appears as
  one box reading `R ≫ S`.

  ONE ENVIRONMENT PER PROCESS — the `lean-refactor` OOM lesson (`Freyd/tool/LeanRefactor.lean`):
  `importModules` retains its environment for the life of the process, so this exe imports once and
  handles every declaration named on the command line from that one environment.
-/
import Lean
import diag.S2_124

open Lean

namespace Freyd.DiagExport

/-! ### Picture model

The measurements are `diag/strdiag.typ`'s own, and must move with it: `BW`/`LEAD` are its constants,
`meetW`/`convW` are its `meet-w`/`conv-w` at their default arguments. -/

def BW : Float := 0.92
def BH : Float := 0.60
def LEAD : Float := 0.34
def GAP : Float := 0.34
/-- `meet-w`/`conv-w` of `strdiag.typ` minus the box width, which the caller sizes to its label. -/
def meetPad : Float := 1.40
def convPad : Float := 2.40
def wireW : Float := 0.60

/-- One left-to-right slot of a picture.  `gen` is a generator `strdiag.typ` draws directly — it
    takes a single anchor and its own stubs, so its width is those stubs' total. -/
inductive Cell where
  | wire
  | box (label : String)
  | gen (fn : String) (width : Float)
  | meet (upper lower : String)
  | conv (label : String)
  deriving Inhabited

/-- A box has to hold its label.  `strdiag.typ`'s default `BW` fits about six characters at 10pt;
    anything longer widens the box rather than spilling out of it. -/
def boxWidth (l : String) : Float := max BW (0.20 * l.length.toFloat + 0.30)

def Cell.width : Cell → Float
  | .wire => wireW
  | .box l => boxWidth l
  | .gen _ w => w
  | .meet u l => meetPad + max (boxWidth u) (boxWidth l)
  | .conv l => convPad + boxWidth l

/-- Typst string literal: only `\` and `"` can end it early. -/
def typstString (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""

/-- Labels are set at 8pt monospace, which is what `boxWidth`'s per-character figure measures. -/
def labelContent (l : String) : String := s!"text(8pt, raw({typstString l}))"

/-- Two decimal places.  `toString` on a `Float` prints six, and cetz coordinates read as noise at
    that width. -/
def fmt (x : Float) : String :=
  let n := (x * 100.0).round
  let m := n.abs.toUInt64.toNat
  let frac := m % 100
  let s := s!"{m / 100}.{if frac < 10 then "0" else ""}{frac}"
  if n < 0.0 then "-" ++ s else s

def Cell.render (c : Cell) (x : Float) : String :=
  let p := s!"({fmt x}, 0)"
  match c with
  | .wire => s!"  wire({p}, ({fmt (x + wireW)}, 0))"
  | .box l => s!"  gbox({p}, {labelContent l}, w: {fmt (boxWidth l)}, h: {fmt BH})"
  | .gen fn _ => s!"  {fn}({p})"
  | .meet u l =>
    s!"  meet({p}, {labelContent u}, {labelContent l}, w: {fmt (max (boxWidth u) (boxWidth l))})"
  | .conv l => s!"  conv({p}, {labelContent l}, w: {fmt (boxWidth l)})"

/-- Lay the cells out at `y = 0` from `x0`, joining consecutive ones with a wire, and return the
    drawing plus the x it ends at. -/
def renderCells (cells : Array Cell) (x0 : Float) : String × Float := Id.run do
  let mut out := #[s!"  wire(({fmt x0}, 0), ({fmt (x0 + LEAD)}, 0))"]
  let mut x := x0 + LEAD
  for i in [0 : cells.size] do
    let c := cells[i]!
    out := out.push (c.render x)
    x := x + c.width
    if i + 1 < cells.size then
      out := out.push s!"  wire(({fmt x}, 0), ({fmt (x + GAP)}, 0))"
      x := x + GAP
  out := out.push s!"  wire(({fmt x}, 0), ({fmt (x + LEAD)}, 0))"
  return (String.intercalate "\n" out.toList, x + LEAD)

def cellsWidth (cells : Array Cell) : Float := Id.run do
  let mut w := 2.0 * LEAD
  for i in [0 : cells.size] do
    w := w + cells[i]!.width
    if i + 1 < cells.size then w := w + GAP
  return w

/-! ### The term walk -/

/-- The two arrow arguments of a binary operator applied with instance and object arguments. -/
def lastTwo (args : Array Expr) : Option (Expr × Expr) :=
  if h : args.size ≥ 2 then some (args[args.size - 2], args[args.size - 1]) else none

/-- Last resort: Lean's pretty printer, on one line.  The repo's namespaces carry no information
    inside a picture of the repo's own algebra, so they come off. -/
def plain (e : Expr) : MetaM String := do
  let s := toString (← Meta.ppExpr e)
  -- Both the fully qualified form and the form the printer shortens to under `open Freyd`.
  let s := s.replace "Freyd." "" |>.replace "Diag.CartBicat." "" |>.replace "Diag." ""
    |>.replace "Alg.Allegory." "" |>.replace "Alg." ""
  return " ".intercalate (s.splitOn "\n" |>.map fun t => t.trimAscii.toString)

/-- A box label.  The operators are spelled the way the papers spell them — `;` for composition,
    `†` for the converse — rather than left to the pretty printer, because a label is read inside a
    picture, where `CartBicat.conv S` is noise and `S†` is the thing itself. -/
partial def label (e : Expr) : MetaM String := do
  match e.getAppFnArgs with
  | (``Cat.id, _) => return "𝟙"
  | (``Freyd.Diag.CartBicat.delta, _) => return "Δ"
  | (``Freyd.Diag.CartBicat.nabla, _) => return "∇"
  | (``Freyd.Diag.CartBicat.bang, _) => return "!"
  | (``Freyd.Diag.CartBicat.unitR, _) => return "?"
  | (``Freyd.Diag.CartBicat.cap, _) => return "cap"
  | (``Freyd.Diag.CartBicat.cup, _) => return "cup"
  | (``Freyd.Diag.top, _) => return "⊤"
  | (``Freyd.Diag.SymMonCat.tensAssoc, _) => return "α"
  | (``Freyd.Diag.SymMonCat.tensAssocInv, _) => return "α⁻¹"
  | (``Freyd.Diag.SymMonCat.runit, _) => return "ρ"
  | (``Freyd.Diag.SymMonCat.runitInv, _) => return "ρ⁻¹"
  | (``Freyd.Diag.SymMonCat.lunit, _) => return "λ"
  | (``Freyd.Diag.SymMonCat.lunitInv, _) => return "λ⁻¹"
  | (``Freyd.Diag.SymMonCat.swap, _) => return "σ"
  | (``Freyd.Diag.SymMonCat.tensHom, args) =>
    match lastTwo args with
    | some (u, l) => return (← label u) ++ " ⊗ " ++ (← label l)
    | none => plain e
  | (``Cat.comp, args) =>
    match lastTwo args with
    | some (f, g) => return (← label f) ++ " ; " ++ (← label g)
    | none => plain e
  | (``Freyd.Alg.Allegory.recip, args)
  | (``Freyd.Diag.CartBicat.conv, args) =>
    match args.back? with
    | some r => return (← label r) ++ "†"
    | none => plain e
  | (``Freyd.Alg.Allegory.inter, args)
  | (``Freyd.Diag.meet, args) =>
    match lastTwo args with
    | some (u, l) => return (← label u) ++ " ∩ " ++ (← label l)
    | none => plain e
  | _ => plain e

mutual

/-- One cell for `e`, used where a sub-picture is not available (inside a meet or a converse). -/
partial def toCell (e : Expr) : MetaM Cell := do
  match e.getAppFnArgs with
  | (``Cat.id, _) => return .wire
  -- widths are the generators' own stub totals in `strdiag.typ` (`li + lo`, `li`, `lo`, `w`)
  | (``Freyd.Diag.CartBicat.delta, _) => return .gen "delta" 1.4
  | (``Freyd.Diag.CartBicat.nabla, _) => return .gen "nabla" 1.4
  | (``Freyd.Diag.CartBicat.bang, _) => return .gen "bang" 0.7
  | (``Freyd.Diag.CartBicat.unitR, _) => return .gen "unitR" 0.7
  | (``Freyd.Diag.SymMonCat.swap, _) => return .gen "swap" 0.55
  | (``Freyd.Alg.Allegory.inter, args)
  | (``Freyd.Diag.meet, args) =>
    match lastTwo args with
    | some (u, l) => return .meet (← label u) (← label l)
    | none => return .box (← label e)
  | (``Freyd.Alg.Allegory.recip, args)
  | (``Freyd.Diag.CartBicat.conv, args) =>
    match args.back? with
    | some r => return .conv (← label r)
    | none => return .box (← label e)
  | _ => return .box (← label e)

/-- The run of cells for `e`, flattening composition. -/
partial def toCells (e : Expr) : MetaM (Array Cell) := do
  match e.getAppFnArgs with
  | (``Cat.comp, args) =>
    match lastTwo args with
    | some (f, g) => return (← toCells f) ++ (← toCells g)
    | none => return #[← toCell e]
  | _ => return #[← toCell e]

end

/-- The relation between the two sides of a statement, and the sides. -/
def split (e : Expr) : Option (String × Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Freyd.Alg.le, args) => (lastTwo args).map fun (l, r) => ("⊑", l, r)
  | (``LE.le, args) => (lastTwo args).map fun (l, r) => ("≤", l, r)
  | (``Eq, args) => (lastTwo args).map fun (l, r) => ("=", l, r)
  | _ => none

/-! ### Emitting a page -/

def page (declName : Name) (doc : Option String) (body : String) : String :=
  let head :=
    "// GENERATED by `diag-export` — do not edit; regenerate with\n\
     //   ./scripts/diag-export " ++ declName.toString ++ "\n\
     #import \"../strdiag.typ\": cetz, d, wire, gbox, delta, nabla, bang, unitR, cap, cup, conv, meet\n\n\
     #set page(width: auto, height: auto, margin: 12pt)\n\
     #set text(size: 10pt)\n\n\
     #text(11pt)[*`" ++ declName.toString ++ "`*]\n\n"
  -- The docstring goes through `raw`: it is arbitrary prose, and `#`, `[`, `$`, `*` in it would
  -- otherwise be read as Typst markup.
  let doc := match doc with
    | some d => "#text(9pt, luma(90), raw(" ++ typstString d ++ "))\n\n"
    | none => ""
  head ++ doc ++ body

/-- Draw the statement of `declName`: the two sides side by side, the relation symbol between. -/
def draw (declName : Name) : MetaM String := do
  let env ← getEnv
  let some ci := env.find? declName
    | throwError "no such declaration: {declName}"
  Meta.forallTelescopeReducing ci.type fun _ body => do
    let doc := (← findDocString? env declName).map fun d =>
      (d.splitOn "\n").headD "" |>.replace "`" ""
    match split body with
    | some (sym, lhs, rhs) =>
      let lc ← toCells lhs
      let rc ← toCells rhs
      let (ld, lend) := renderCells lc 0.0
      let symX := lend + 0.45
      let (rd, _) := renderCells rc (symX + 0.45)
      let canvas := "#cetz.canvas({\n" ++ ld ++ "\n"
        ++ s!"  d.content(({fmt symX}, 0), [{sym}])\n" ++ rd ++ "\n})\n"
      return page declName doc canvas
    | none =>
      let (d, _) := renderCells (← toCells body) 0.0
      return page declName doc ("#cetz.canvas({\n" ++ d ++ "\n})\n")

/-! ### Driver -/

/-- Every `diag.*` module except this tool, so the exporter can name any declaration of the tower
    without the caller listing imports. -/
partial def diagModules (dir : System.FilePath) (pre : Name) : IO (Array Name) := do
  let mut out := #[]
  for e in (← dir.readDir) do
    if (← e.path.isDir) then
      if e.fileName != "tool" && e.fileName != "generated" then
        out := out ++ (← diagModules e.path (pre.str e.fileName))
    else if e.path.extension == some "lean" then
      out := out.push (pre.str (e.path.fileStem.getD ""))
  return out

def usage : String :=
  "usage: diag-export <declaration-name> [<declaration-name> ...]\n\
   writes diag/generated/<name>.typ per declaration and prints each path"

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then IO.eprintln usage; return 2
  Lean.initSearchPath (← Lean.findSysroot)
  let mods := #[`Freyd] ++ (← diagModules "diag" `diag)
  let env ← importModules (mods.map fun m => { module := m }) {} (trustLevel := 1024)
  IO.FS.createDirAll "diag/generated"
  -- `≫` and `⟶` are `scoped` in `Freyd`, so the delaborator only reaches them with that namespace
  -- opened; without this a fallthrough label prints `inst✝.comp R S`.
  -- Generalized field notation prints a class projection through its instance argument, so `Δ_a`
  -- comes out as `inst✝.delta a`.  The instance is anonymous inside a `forallTelescope`, so that is
  -- worse than useless in a picture; off, it prints `CartBicat.delta a` and the strip in `plain`
  -- takes the namespace.
  let opts : Options :=
    (Options.empty.setBool `pp.fieldNotation false).setBool `pp.fieldNotation.generalized false
  let ctx : Core.Context :=
    { fileName := "<diag-export>", fileMap := default,
      options := opts,
      -- `≫` and `⟶` live in `Freyd`, `⊗`/`⊗ₕ`/`𝕀` in `Freyd.Diag.SymMonCat`.
      openDecls := [.simple `Freyd [], .simple `Freyd.Diag.SymMonCat []] }
  let mut status : UInt32 := 0
  for arg in args do
    let run : CoreM String := Meta.MetaM.run' (draw arg.toName)
    match ← (do pure (some (← Prod.fst <$> run.toIO ctx { env }))) <|> pure none with
    | none =>
      IO.eprintln s!"diag-export: cannot draw `{arg}` — no such declaration in `Freyd` or `diag.*`"
      status := 1
    | some text =>
      let path := System.FilePath.mk s!"diag/generated/{arg}.typ"
      IO.FS.writeFile path text
      IO.println path.toString
  return status

end Freyd.DiagExport

def main (args : List String) : IO UInt32 := Freyd.DiagExport.main args
