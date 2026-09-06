/-
  `StringDiagram` — the STRING-DIAGRAM functor: source, the 2-category of allegories, relators and
  natural families as `ExprReader` reads it off a declaration's elaborated type; target, one
  `dpanel(...)` call of `diag/dpanel.typ`, which draws it unchanged.

  A WIRE IS A RELATOR, A BEAD A 2-CELL, A REGION AN ALLEGORY (Hinze–Marsden).  So the picture is
  decided by TYPES, not by a formula: a factor's source and target say which wires it eats and which
  it makes, and the environment says whether it has a dot.

  THE GEOMETRY IS `scripts/diagram`'s, ported.  Columns are `DX` apart, rows `DY`, a bead's legs a
  block centred on the arms it replaces, and a lane's own name reserves room west of it — the same
  arithmetic, so a panel drawn from Lean and a panel drawn from a formula land on the same page in
  the same place.  The numbers are IntroString's own (pp. 46/75/79), measured there and not chosen.
-/
import diag.tool.ExprReader

open Lean

namespace Freyd.StrDiag

/-! ### The book's geometry -/

/-- The margin the leftmost lane's NAME is written into. -/
def X0 : Float := 1.875
/-- One column: IntroString p. 46's 0.5cm in cetz's own `length: 0.8cm` unit. -/
def DX : Float := 0.625
/-- One row — the height that holds one label clear of the label a row below it. -/
def DY : Float := 1.1
/-- The clear margin east of the object wire. -/
def PAD : Float := 1.85
/-- A label box: `dpanel`'s own character width and the gap it is anchored back from its lane. -/
def LCW : Float := 0.2039 / 0.8
def LDX : Float := 0.12
/-- The half-steps a block of legs is slid by until it fits between the arms' own neighbours. -/
def SLIDE : Array Float := Id.run do
  let mut out := #[0.0]
  for i in [0:12] do
    out := out.push (0.5 * DX * ((i / 2 + 1).toFloat) * (if i % 2 == 1 then -1.0 else 1.0))
  return out

/-- Python's `round(x, n)`: half to EVEN, so a column landing exactly on a half unit rounds the
    same way in both generators and the two pictures stay one picture. -/
def roundTo (n : Nat) (x : Float) : Float :=
  let m := (10.0 : Float) ^ n.toFloat
  let y := x * m
  let f := y.floor
  let d := y - f
  let r := if d > 0.5 then f + 1.0 else if d < 0.5 then f
           else if (f / 2.0).floor * 2.0 == f then f else f + 1.0
  r / m

/-- `%g`: six significant digits, no trailing zeros — the spelling `scripts/diagram` emits. -/
def num (x : Float) : String :=
  let x := roundTo 4 x
  let neg := x < 0.0
  let a := if neg then -x else x
  let scaled := (a * 10000.0 + 0.5).floor
  let ip := (scaled / 10000.0).floor
  let fp := scaled - ip * 10000.0
  let digits := (toString (fp.toUInt64.toNat + 10000)).drop 1
  let digits := digits.dropEndWhile (· == '0')
  let s := toString ip.toUInt64.toNat ++ (if digits.isEmpty then "" else "." ++ digits)
  if neg then "-" ++ s else s

/-! ### The panel model -/

/-- One wire, from the bead that makes it to the bead that eats it.  `born = -1` is the top edge,
    `dies = rows.size` the bottom one. -/
structure Lane where
  label : String
  born  : Int
  dies  : Int
  x     : Float := 0.0
  pad   : Float := 0.0
  deriving Inhabited

/-- One bead: what it eats, what it makes, what the object wire carries below it, and whether a
    declaration says it is natural. -/
structure Row where
  label : String
  arms  : Array Nat
  legs  : Array Nat
  obj   : String
  nat   : Option String := none
  deriving Inhabited

structure Panel where
  lanes : Array Lane
  rows  : Array Row
  otop  : String
  obot  : String
  deriving Inhabited

/-! ### `columns` — how far apart the lanes sit -/

def minA (xs : Array Float) (dflt : Float) : Float := xs.foldl (fun a b => if b < a then b else a) dflt
def maxA (xs : Array Float) (dflt : Float) : Float := xs.foldl (fun a b => if b > a then b else a) dflt

/-- A column per lane.  The top-born lanes take the grid; a bead's legs are a contiguous `DX` block
    CENTRED on the arms it replaces, slid by half steps until it fits between the arms' own
    neighbours, so a lane west of the arms stays west of the legs. -/
def columns (p : Panel) : Array Lane := Id.run do
  let n := p.rows.size
  let mut xs : Array (Option Float) := p.lanes.map (fun _ => none)
  let mut k := 0
  for i in [0 : p.lanes.size] do
    if p.lanes[i]!.born < 0 then
      xs := xs.set! i (some (k.toFloat * DX)); k := k + 1
  for i in [0 : n] do
    let r := p.rows[i]!
    if r.legs.isEmpty then continue
    let live := (List.range p.lanes.size).filter fun j =>
      (xs[j]!).isSome && p.lanes[j]!.born < (i : Int) && (i : Int) < p.lanes[j]!.dies
    let arms := r.arms.filterMap (fun a => xs[a]!)
    -- A bead with no arms of its own opens its wire east of every lane already live: born west, it
    -- would cross each of them on the way out.
    let c := if arms.isEmpty then
        (maxA (Array.mk (live.map (fun j => (xs[j]!).get!))) (-DX)) + DX
      else (minA arms 1e9 + maxA arms (-1e9)) / 2.0
    -- A bead that gives back as many wires as it takes moves nothing sideways, so its legs KEEP the
    -- arms' columns and a swap is two straight lines crossing, not a staircase of knees.
    if !arms.isEmpty && r.legs.size == r.arms.size && arms.size == r.arms.size then
      let sorted := arms.qsort (· < ·)
      for j in [0 : r.legs.size] do xs := xs.set! r.legs[j]! (some sorted[j]!)
      continue
    let oth := live.filter fun j => !r.arms.contains j
    let othx := Array.mk (oth.map (fun j => (xs[j]!).get!))
    let lo := maxA (othx.filter (· < minA arms c)) (-1e9)
    let hi := minA (othx.filter (· > maxA arms c)) 1e9
    let mut got : Array Float := #[]
    for d in SLIDE do
      got := Array.mk ((List.range r.legs.size).map fun j =>
        c + d + (j.toFloat - (r.legs.size.toFloat - 1.0) / 2.0) * DX)
      if lo + 1e-6 < got[0]! && got[got.size - 1]! < hi - 1e-6 then break
    for j in [0 : r.legs.size] do xs := xs.set! r.legs[j]! (some got[j]!)
  -- A lane OPENED at the bead that eats it has no row of legs to space it: it takes the free column
  -- beside the neighbour creation order already puts it next to.
  for i in [0 : p.lanes.size] do
    if (xs[i]!).isNone then
      let nxt := (List.range' (i + 1) (p.lanes.size - i - 1)).findSome? (fun j => xs[j]!)
      let prv := ((List.range i).reverse).findSome? (fun j => xs[j]!)
      xs := xs.set! i (some (match nxt, prv with
        | some v, _ => v - DX | none, some v => v + DX | none, none => 0.0))
  let mut ls : Array Lane := p.lanes.mapIdx fun i l => { l with x := (xs[i]!).get! }
  -- A lane's own NAME is written west of it, and a strand through that box is a collision.  One
  -- column holds two characters; a wider name moves every lane west of it west by the deficit,
  -- leaving the relative order — and the dots computed from it — untouched.
  for _ in [0 : ls.size] do
    let mut moved := false
    for i in [0 : ls.size] do
      if moved then continue
      let l := ls[i]!
      if l.label.isEmpty then continue
      let w := LDX + LCW * l.label.length.toFloat + 0.002 + l.pad
      let west := ls.filter fun o =>
        o.x < l.x - 1e-6 && o.born < l.dies && l.born < o.dies
      if west.isEmpty then continue
      let mx := maxA (west.map (·.x)) (-1e9)
      if l.x - mx >= w - 1e-6 then continue
      let d := w - (l.x - mx)
      ls := ls.map fun o => if o.x < l.x - 1e-6 then { o with x := o.x - d } else o
      moved := true
    if !moved then break
  -- The leftmost lane's own name is written into the margin, so the margin holds the wider of a
  -- column and that name.
  if ls.isEmpty then return ls
  let lo := ls.foldl (fun a b => if b.x < a.x then b else a) ls[0]!
  let gap := if lo.label.length > 1 then
      max DX (LDX + LCW * lo.label.length.toFloat + 0.002 + lo.pad) else DX
  let off := X0 + gap - minA (ls.map (·.x)) 0.0
  return ls.map fun l => { l with x := roundTo 3 (l.x + off) }

/-! ### `place` — one panel of the many the book calls equal -/

/-- The `dpanel(...)` call this panel is.  `frame` and `top` are ROW COUNTS, the two halves of
    lining a short panel up with a tall one: the frame gives them one box, the top one bead
    height.  Left off, the frame is one row deeper than the panel and the first bead sits at the
    top of it. -/
def emit (p : Panel) (declName : String) (frame topRow scale : Option Nat) : String := Id.run do
  let n := p.rows.size
  let ls := columns p
  let hh := (frame.getD (max n 1 + 1)).toFloat * DY
  let t0 := (topRow.getD n).toFloat
  let ys : Array Float := Array.mk ((List.range n).map fun i => (t0 - i.toFloat) * DY)
  let xo := roundTo 2 (maxA (ls.map (·.x)) X0 + DX)
  let cell (s : String) : String := "[`" ++ s ++ "`]"
  let mut beads : Array String := #[]
  let mut objs : Array String := #[]
  for i in [0 : n] do
    let r := p.rows[i]!
    let idx := if r.arms.isEmpty then r.legs else r.arms
    let xsr := idx.map fun j => ls[j]!.x
    let reach : Option Float := if xsr.isEmpty then none else some (minA xsr 1e9)
    let dot : Option Float :=
      if xsr.isEmpty || r.nat.isNone then none
      else some (roundTo 4 ((minA xsr 1e9 + maxA xsr (-1e9)) / 2.0))
    let lax := if r.nat == some "lax" then ", \"lax\"" else ""
    beads := beads.push <| match reach, dot with
      | none, _ => "(" ++ num ys[i]! ++ ", " ++ cell r.label ++ ")"
      | some rc, none => "(" ++ num ys[i]! ++ ", " ++ cell r.label ++ ", black, " ++ num rc ++ ")"
      | some rc, some d =>
        "(" ++ num ys[i]! ++ ", " ++ cell r.label ++ ", black, " ++ num rc ++ ", " ++ num d
          ++ lax ++ ")"
    objs := objs.push ("(" ++ num ys[i]! ++ ", " ++ cell r.obj ++ ")")
  let lanecode : Lane → String := fun l =>
    let birth := if l.born < 0 then "\"top\"" else num ys[l.born.toNat]!
    let death := if l.dies >= (n : Int) then "\"bot\"" else num ys[l.dies.toNat]!
    let nm := if l.born < 0 || l.dies >= (n : Int) then "none" else cell l.label
    "(" ++ num l.x ++ ", " ++ birth ++ ", " ++ death ++ ", " ++ nm ++ ", none)"
  let tup (xs : Array String) : String :=
    "(" ++ String.intercalate ", " xs.toList ++ (if xs.size == 1 then "," else "") ++ ")"
  let top := (ls.filter (·.born < 0)).map (fun l => "(" ++ num l.x ++ ", " ++ cell l.label ++ ")")
    |>.push ("(" ++ num xo ++ ", " ++ cell p.otop ++ ")")
  let bot := (ls.filter (·.dies >= (n : Int))).map (fun l => "(" ++ num l.x ++ ", " ++ cell l.label ++ ")")
    |>.push ("(" ++ num xo ++ ", " ++ cell p.obot ++ ")")
  "// GENERATED by `diag-export --string` — do not edit; regenerate with\n\
   //   ./scripts/diag-export --string " ++ declName ++ "\n\
   #import \"../../dpanel.typ\": *\n\n\
   #let pic = dpanel(" ++ num hh ++ ", " ++ num (roundTo 2 (xo + PAD)) ++ ", " ++ num xo ++ ",\n  "
    ++ tup (ls.map lanecode) ++ ",\n  " ++ tup beads ++ ",\n  " ++ tup top ++ ",\n  " ++ tup bot
    ++ ",\n  obj: " ++ tup objs ++ ",\n  cert: (lean: \"" ++ declName ++ "\")"
    ++ (match scale with | some v => ", s: " ++ toString v ++ "%" | none => "") ++ ")\n"

/-! ### The functor: an arrow of the allegory as a panel

  A factor is read by its TYPE.  Strip the relators it runs under (`F.map R` is `R` with `F`'s wire
  running past), then its own source and target say which wires it eats and which it makes: the
  stack they share below the change is untouched, everything above it dies and is reborn. -/

/-- Still live: a lane the walk has not yet seen eaten. -/
private def LIVE : Int := -2

/-- Whether this factor is a FAMILY in the region's object, and so a candidate 2-cell at all: its
    two ends stand over the SAME object and it varies with that object.  `α : F(T)⟶T` at an initial
    algebra's carrier does not vary — `T` is one object, not a parameter — and `⦇R⦈ : T⟶A` does not
    even stand over one, so both are 2-cells between CONSTANT 1-cells `𝟏 → 𝒜`, which is the object
    wire.  `αᴀ : F(⟨𝟙,T⟩(A))⟶T(A)` does, which is why the two come out different by construction. -/
def familyVar (core oX : Expr) (objVars : Array Expr) : Option Expr :=
  objVars.find? fun v => core.containsFVar v.fvarId! && oX.containsFVar v.fvarId!

/-- A lane as a RELATOR: `A×−` is the product of the constant `A` with the identity, which is the
    relator the note's label names and the one a naturality statement has to be about. -/
def wireRelator (regionTy : Expr) : Wire → MetaM Expr
  | .rel r => return r
  | .timesL l => do
    let inst ← allegoryInst regionTy
    Meta.mkAppM ``Freyd.Alg.Relator.prod
      #[← Meta.mkAppOptM ``Freyd.Alg.Relator.const
          #[some regionTy, some regionTy, some inst, some inst, some l],
        ← idRelatorOf regionTy]

/-- The composite relator a wire stack is, outermost first: `[W₀,W₁]` is `comp W₁ W₀`, whose object
    map is `W₀.obj ∘ W₁.obj`. -/
def stackRelator (regionTy : Expr) (ws : Array Wire) : MetaM Expr := do
  if ws.isEmpty then return ← idRelatorOf regionTy
  let mut acc ← wireRelator regionTy ws[ws.size - 1]!
  for i in [0 : ws.size - 1] do
    acc ← Meta.mkAppM ``Freyd.Alg.Relator.comp #[acc, ← wireRelator regionTy ws[ws.size - 2 - i]!]
  return acc

/-- The bead's verdict, from the ENVIRONMENT.  `StrictNatural F G φ` is a solid dot, `LaxNatural`
    a hollow one, a refuted `LaxNatural` the object wire; nothing found is an error naming the
    three statements it looked for, because no declaration means no dot. -/
def verdict (regionTy : Expr) (armsW legsW : Array Wire) (core v : Expr) (label : String) :
    MetaM (Option String) := do
  let φ ← Meta.mkLambdaFVars #[v] core
  -- The three statements have to be BUILDABLE before they can be searched for: a wire that is not
  -- a `Relator` — a bifunctor applied to two arrows, say — has no `StrictNatural` to state, and
  -- saying so names the bead instead of leaving an elaboration error to stand for it.
  let some G ← (some <$> stackRelator regionTy armsW) <|> pure none
    | throwError "the bead `{label}` runs under wires that are not relators, so there is no \
      naturality statement to look for: {← armsW.mapM (Meta.ppExpr ·.expr)}"
  let some F ← (some <$> stackRelator regionTy legsW) <|> pure none
    | throwError "the bead `{label}` makes wires that are not relators, so there is no \
      naturality statement to look for: {← legsW.mapM (Meta.ppExpr ·.expr)}"
  -- A wire is a relator of the WHOLE region, so it cannot mention the object the bead is a family
  -- in.  `α : F(A,TA) ⟶ TA` peels its source to `F(A,−)`, which does: read that way the bead has
  -- no naturality statement at all, and the stack has to be `⟨𝟙,T⟩` then `F` before it has one.
  for w in armsW ++ legsW do
    if (w.expr.containsFVar v.fvarId!) then
      throwError "the bead `{label}` runs on the wire `{← Meta.ppExpr w.expr}`, which mentions the \
        object `{← Meta.ppExpr v}` it is a family in — that stack is not a relator of the region, \
        so it states no naturality"
  let must := consts core
  let strict ← Meta.mkAppM ``Freyd.Alg.StrictNatural #[F, G, φ]
  if (← findProof strict ``Freyd.Alg.StrictNatural must).isSome then return some "strict"
  let lax ← Meta.mkAppM ``Freyd.Alg.LaxNatural #[F, G, φ]
  if (← findProof lax ``Freyd.Alg.LaxNatural must).isSome then return some "lax"
  let nolax ← Meta.mkAppM ``Not #[← Meta.mkAppM ``Freyd.Alg.LaxNatural #[G, F, φ]]
  if (← findProof nolax ``Not must).isSome then return none
  throwError "the bead `{label}` is a family in the object but no declaration says whether it is \
    natural — looked for `{← Meta.ppExpr strict}`, `{← Meta.ppExpr lax}` and \
    `{← Meta.ppExpr nolax}`"

/-- What one factor does to the stack: how many lanes run past it on the OUTSIDE, the lanes it
    eats, the lanes it makes, and the arrow itself. -/
structure RowSpec where
  pass  : Array Wire
  arms  : Array Wire
  legs  : Array Wire
  core  : Expr
  deriving Inhabited

/-- The rows a factor is.  A factor is taken apart until what is left acts on ONE contiguous block
    of lanes, and the parts that are identities are what runs past:

    * `F.map R` is `R` with `F`'s wires running past OUTSIDE it — the rule that was already here;
    * a product map `φ×𝟙` is `φ` on the left factor's lanes with the rest of the stack running
      past, and `𝟙×ψ` is `ψ` on the rest with the left factor's lanes running past;
    * a composite inside either of those is still a composite, so `(cons secure)×𝟙` is two beads.

    Comparing the two ends' wire STACKS cannot do this: `cons : [A]×[[A]] ⟶ [[A]]` and
    `secure×𝟙` both leave `list list` below them, and the first eats those wires while the second
    does not.  What separates them is the factor's own form, which is what is read here.  A factor
    whose two ends are DIFFERENT objects with the SAME stack is a re-bracketing of a product —
    `assocl` — and a picture has no bracketing to redraw, so it is no row at all. -/
partial def rowsOf (regionTy : Expr) (cat : Array Name) (pass : Array Wire) (inLeft : Bool)
    (e : Expr) : MetaM (Array RowSpec) := do
  let fs := factors e
  if fs.size > 1 then
    let mut out : Array RowSpec := #[]
    for f in fs do out := out ++ (← rowsOf regionTy cat pass inLeft f)
    return out
  match e.getAppFnArgs with
  | (``Freyd.Functor.map, args) =>
    if args.size ≥ 6 then
      return ← rowsOf regionTy cat (pass ++ (wiresOf args[4]!).map Wire.rel) inLeft
        args[args.size - 1]!
  | _ => pure ()
  if let some (φ, ψ) ← asProdMap? regionTy e then
    if ← isIdArrow ψ then return ← rowsOf regionTy cat pass true φ
    if ← isIdArrow φ then
      let (x, _) ← homEnds φ
      return ← rowsOf regionTy cat (pass ++ (← peelLefts regionTy x)) inLeft ψ
  let (x, y) ← homEnds e
  let (ax, ox) ← peelObj regionTy cat x
  let (ay, oy) ← peelObj regionTy cat y
  let arms ← if inLeft then peelLefts regionTy x else pure ax
  let legs ← if inLeft then peelLefts regionTy y else pure ay
  -- A re-bracketing is the ONE factor a picture does not show: the same lanes over the same object
  -- at both ends.  The object has to be compared too — `⦇R⦈ : t F ⟶ c` has no lanes at either end
  -- and is not invisible.
  if (← Meta.isDefEq ox oy) && arms.size == legs.size && !(← Meta.isDefEq x y) then
    let mut same := true
    for i in [0 : arms.size] do
      unless ← Wire.beq arms[i]! legs[i]! do same := false
    if same then return #[]
  return #[{ pass, arms, legs, core := e }]

/-- One side of a statement, as a panel. -/
def panelOf (regionTy : Expr) (cat : Array Name) (side : Expr) (objVars : Array Expr) :
    MetaM Panel := do
  let (src, tgt) ← homEnds side
  let (ws0, o0) ← peelObj regionTy cat src
  let mut lanes : Array Lane := #[]
  let mut stack : Array Nat := #[]
  for w in ws0 do
    lanes := lanes.push { label := ← w.label, born := -1, dies := LIVE }
    stack := stack.push (lanes.size - 1)
  let mut rows : Array Row := #[]
  for f in factors side do
    let (_, fy) ← homEnds f
    let obj ← plain (← peelObj regionTy cat fy).2
    for r in ← rowsOf regionTy cat #[] false f do
      let p := r.pass.size
      if p + r.arms.size > stack.size then
        throwError "the factor `{← plain r.core}` eats {r.arms.size} wires under {p}, and \
          only {stack.size} are live"
      let i : Int := rows.size
      let arms := stack.extract p (p + r.arms.size)
      for a in arms do lanes := lanes.set! a { lanes[a]! with dies := i }
      let mut legs : Array Nat := #[]
      for w in r.legs do
        lanes := lanes.push { label := ← w.label, born := i, dies := LIVE }
        legs := legs.push (lanes.size - 1)
      stack := stack.extract 0 p ++ legs ++ stack.extract (p + r.arms.size) stack.size
      let label ← plain r.core
      let (cx, cy) ← homEnds r.core
      let (_, ox) ← peelObj regionTy cat cx
      let (_, oy) ← peelObj regionTy cat cy
      let nat ← match (if ← Meta.isDefEq ox oy then familyVar r.core ox objVars else none) with
        | none => pure none
        | some v => verdict regionTy (r.pass ++ r.arms) (r.pass ++ r.legs) r.core v label
      rows := rows.push { label, arms, legs, obj, nat }
  let n : Int := rows.size
  lanes := lanes.map fun l => if l.dies == LIVE then { l with dies := n } else l
  -- The two edges' own objects: the source's tail at the top, the target's at the bottom.
  return { lanes, rows, otop := ← plain o0, obot := ← plain (← peelObj regionTy cat tgt).2 }

/-- A declaration is read in ITS OWN namespaces.  `Freyd.Alg` keeps its allegory instances and its
    `≫`/`°`/`⦇⦈` notations scoped, so outside them the region has no product to split an object on
    and every label prints as `Cat.comp` — the picture then comes out with no lanes at all and no
    error to say why.  Every prefix of the name is opened, which is exactly the scope the
    declaration itself was elaborated in. -/
def withDeclScope (declName : Name) (k : MetaM α) : MetaM α := do
  let mut ns : List OpenDecl := []
  let mut pre := declName
  while !pre.isAnonymous do
    pre := pre.getPrefix
    unless pre.isAnonymous do ns := .simple pre [] :: ns
  withTheReader Core.Context (fun c => { c with openDecls := c.openDecls ++ ns }) k

/-- `--string <Name>[.lhs|.rhs]`.  A `def` is drawn by its BODY unfolded one level; a statement
    with two sides is drawn one side at a time. -/
def drawString (declName : Name) (side : Option String) (frame topRow scale : Option Nat) :
    MetaM String := withDeclScope declName do
  let env ← getEnv
  let some ci := env.find? declName | throwError "no such declaration: {declName}"
  Meta.forallTelescopeReducing ci.type fun xs body => do
    let isDef := match ci with | .defnInfo _ => true | _ => false
    let body := if isDef then
        match ci.value? with
        | some v => (mkAppN v xs).headBeta
        | none => body
      else body
    let arrow ← match side, body.getAppFnArgs with
      | none, _ => pure body
      | some s, (``Eq, #[_, l, r]) | some s, (``Freyd.Alg.le, #[_, _, _, _, l, r]) =>
        pure (if s == "lhs" then l else r)
      | some _, _ => throwError "{declName} has no two sides to draw one of"
    -- The OBJECT VARIABLES of the statement: a factor mentioning one is a family, and only a
    -- family can carry a dot.
    let (src, _) ← homEnds arrow
    let regionTy ← Meta.inferType src
    let cat ← relatorCatalogue regionTy
    let mut objVars : Array Expr := #[]
    for x in xs do
      if ← Meta.isDefEq (← Meta.inferType x) regionTy then objVars := objVars.push x
    let p ← panelOf regionTy cat arrow objVars
    let nm := declName.toString ++ (match side with | some s => "." ++ s | none => "")
    return emit p nm frame topRow scale

end Freyd.StrDiag
