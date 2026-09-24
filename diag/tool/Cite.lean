import diag.tool.ExprReader
/-!
# `cite-check` and `cite-cover` — the notes' citations, read in Lean against the index

A `lean:<decl>@<key>` marker is a HUMAN's certificate: he read the display and the Lean statement
side by side once and copied the statement's key down.  The key is `decl_info.stmt_key`, which the
indexer computes from the alpha- and universe-normalised statement, so ANY later edit to that
statement fails this check and sends him back to re-read the pair.  Nothing here checks that the
display says what Lean says — no tool can; it checks that the thing he certified has not moved.

`--cover` is the other half: for every labelled display it ranks the index's statements against the
display's formulas, so a display with no marker gets a READING TASK — never a proposed marker, which
would be an uncertified claim wearing a certificate's clothes.

Both read `.lake/build/refactor-index.db` through `StrDiag.indexRows`, the one db reader in the exe.
-/

namespace Freyd.Cite

open Lean Freyd.StrDiag

/-- Anything that cannot be read — a file, a marker, a chapter number, a row — ends the run naming
    it.  A citation gate that skipped what it could not parse would exit 0 over an unchecked note. -/
def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

def readFileOr (p : String) : IO String := do
  try IO.FS.readFile p
  catch e => die s!"cite-check: {p}: {e}"

/-! ## The marker's grammar, read by a scanner

`(?<![\w.])lean:([^\s\[\];,@`]+)(?:@([0-9a-f]+)(?:#[^\s\[\];,@`"!()]+)?)?` — the lookbehind keeps a
comment's `AOP/A4_2.lean:223` from reading as a marker; the `#name` after the key names a BINDER of
the declaration, which `hm-check --verify-sigs` resolves and this gate only has to not choke on. -/

def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '' || c == ''
  || c == ' ' || c == ' ' || c == ' ' || c == ' ' || c == ' '
  || c == ' ' || c == '　'

/-- A word character for the lookbehind.  Non-ASCII counts as a separator: a marker glued to `⦇`
    must still be READ (missing it would check fewer markers and exit 0), where a marker glued to a
    letter is stray text that this gate then reports rather than skips. -/
def isWordChar (c : Char) : Bool := (c.isAlphanum && c.toNat < 128) || c == '_'

def nameStop (c : Char) : Bool :=
  isSpace c || c == '[' || c == ']' || c == ';' || c == ',' || c == '@' || c == '`'

def binderStop (c : Char) : Bool :=
  nameStop c || c == '"' || c == '!' || c == '(' || c == ')'

def isHexDigit (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

partial def runWhile (cs : Array Char) (p : Char → Bool) (i : Nat) : Nat :=
  if i < cs.size && p cs[i]! then runWhile cs p (i + 1) else i

def slice (cs : Array Char) (a b : Nat) : String := String.ofList (cs.extract a b).toList

/-- Every marker of one line, in order, as the regex finds them: `(declaration, key?)`. -/
partial def scanFrom (cs : Array Char) (i : Nat) (acc : Array (String × Option String)) :
    Array (String × Option String) :=
  if i ≥ cs.size then acc
  else
    let isLean := i + 5 ≤ cs.size && cs[i]! == 'l' && cs[i+1]! == 'e' && cs[i+2]! == 'a'
      && cs[i+3]! == 'n' && cs[i+4]! == ':'
    let behind := i == 0 || !(isWordChar cs[i-1]! || cs[i-1]! == '.')
    if !(isLean && behind) then scanFrom cs (i + 1) acc
    else
      let ne := runWhile cs (fun c => !nameStop c) (i + 5)
      if ne == i + 5 then scanFrom cs (i + 1) acc      -- the name is `+`: no name, no match
      else
        let nm := slice cs (i + 5) ne
        -- `@` with no hex after it is no key at all, and the `@` is not consumed — the optional
        -- group simply fails, exactly as the regex's does.
        if ne < cs.size && cs[ne]! == '@' then
          let he := runWhile cs isHexDigit (ne + 1)
          if he == ne + 1 then scanFrom cs ne (acc.push (nm, none))
          else
            let after :=
              if he < cs.size && cs[he]! == '#' then
                let be := runWhile cs (fun c => !binderStop c) (he + 1)
                if be == he + 1 then he else be
              else he
            scanFrom cs after (acc.push (nm, some (slice cs (ne + 1) he)))
        else scanFrom cs ne (acc.push (nm, none))

def marksOf (line : String) : Array (String × Option String) :=
  scanFrom line.toList.toArray 0 #[]

/-! ## The index -/

/-- 32 bits of the 64-bit `stmt_key`: 8 hex digits stay readable in the rendered `#src`, and a
    changed statement keeping the low half is a 1-in-4-billion coincidence. -/
def keyHex (k : Int) : String :=
  let u : Nat := (((k % 4294967296) + 4294967296) % 4294967296).toNat
  let s := String.ofList (Nat.toDigits 16 u)
  "".pushn '0' (8 - s.length) ++ s

def sqlLit (s : String) : String := "'" ++ s.replace "'" "''" ++ "'"

def Q : String :=
  "select i.user_name, i.module, m.source, r.sl1, i.stmt_key from decl_info i"
  ++ " join module m on m.name = i.module"
  ++ " left join decl_range r on r.name = i.name and r.module = i.module"
  ++ " where i.internal = 0 and "

structure Row where
  user : String
  mod : String
  src : String
  line : Option Int
  key : Int
deriving Inhabited, BEq

def numCell (row : Json) (k : String) : IO (Option Int) :=
  match row.getObjVal? k with
  | .error e => die s!"cite-check: {INDEX}: row {row.compress} has no cell `{k}`: {e}"
  | .ok .null => pure none
  | .ok (.num n) =>
    if n.exponent == 0 then pure (some n.mantissa)
    else die s!"cite-check: {INDEX}: cell `{k}` of {row.compress} is not an integer"
  | .ok _ => die s!"cite-check: {INDEX}: cell `{k}` of {row.compress} is not a number"

def toRow (j : Json) : IO Row := do
  pure { user := ← cell j "user_name", mod := ← cell j "module", src := ← cell j "source",
         line := ← numCell j "sl1", key := (← numCell j "stmt_key").getD 0 }

def rowsOf (sql : String) : IO (Array Row) := do
  (← indexRows sql).mapM toRow

/-- SQL `like '%.<rest>'`, as sqlite means it: `%` eats any prefix and `_` any ONE character, so the
    match is pinned at `user_name`'s tail with a `.` in front of it. -/
def likeSuffix (rest user : String) : Bool :=
  let r := rest.toList.toArray
  let u := user.toList.toArray
  if u.size < r.size + 1 then false
  else
    let off := u.size - r.size
    u[off - 1]! == '.' && (List.range r.size).all fun i => r[i]! == '_' || r[i]! == u[off + i]!

def lastComp (s : String) : String := (s.splitOn ".").getLast!

/-- `AOP.A6_2.mu` is the MODULE plus the name as its file writes it (`Freyd.Alg.mu` in full).  A full
    Lean name works too, so the full name comes first and then every module/suffix split. -/
def resolve (rows : Array Row) (mark : String) : Array Row := Id.run do
  let parts := mark.splitOn "."
  let mut hits : Array Row := rows.filter (·.user == mark)
  for k in (List.range (parts.length - 1)).reverse.map (· + 1) do
    let md := ".".intercalate (parts.take k)
    let rest := ".".intercalate (parts.drop k)
    hits := hits ++ rows.filter fun r => r.mod == md && (r.user == rest || likeSuffix rest r.user)
  let mut out : Array Row := #[]
  for r in hits do
    unless out.any (fun s => s.user == r.user && s.mod == r.mod) do out := out.push r
  return out

/-- The names a marker could have meant: everything a `resolve` might select, in ONE query. -/
def candidateSql (marks : Array String) : String := Id.run do
  let mut names : Array String := #[]
  let mut mods : Array String := #[]
  for m in marks do
    unless names.contains m do names := names.push m
    let parts := m.splitOn "."
    for k in (List.range (parts.length - 1)).map (· + 1) do
      let md := ".".intercalate (parts.take k)
      let rest := ".".intercalate (parts.drop k)
      unless names.contains rest do names := names.push rest
      unless mods.contains md do mods := mods.push md
  let inList (xs : Array String) := ", ".intercalate (xs.map sqlLit).toList
  return Q ++ s!"(i.user_name in ({inList names}) or i.module in ({inList mods}))"

def commonPrefixLen (a b : String) : Nat := Id.run do
  let x := a.toList.toArray
  let y := b.toList.toArray
  let mut n := 0
  while n < x.size && n < y.size && x[n]! == y[n]! do n := n + 1
  return n

/-- What the author probably meant.  A marker goes wrong two ways — the declaration was renamed or
    moved, and it was mistyped — so look for the same last component anywhere, then for the closest
    spellings inside the module he named. -/
def near (mark : String) : IO (Array String) := do
  let parts := mark.splitOn "."
  let last := parts.getLast!
  let moved ← indexRows <|
    s!"select module, user_name from decl_info where internal = 0 and (user_name = {sqlLit last}"
    ++ s!" or user_name like {sqlLit ("%." ++ last)}) limit 4"
  let mut hits : Array (String × String) := #[]
  for j in moved do hits := hits.push (← cell j "module", ← cell j "user_name")
  if hits.isEmpty then
    let md := ".".intercalate parts.dropLast
    let rows ← indexRows <|
      s!"select user_name from decl_info where internal = 0 and module = {sqlLit md}"
    let mut us : Array String := #[]
    for j in rows do us := us.push (← cell j "user_name")
    let shared (u : String) := commonPrefixLen (lastComp u) last
    -- Stable, as Python's `sorted` is: equal scores keep the order the index returned them in.
    let sorted := us.toList.mergeSort (fun a b => shared a ≥ shared b)
    hits := (sorted.take 3).filter (fun u => shared u ≥ 3) |>.map (fun u => (md, u)) |>.toArray
  return hits.map fun (m, u) => s!"{m}.{lastComp u}"

/-- One marker: the message says what to do, not merely that something is wrong. -/
def check (rows : Array Row) (mark : String) (want : Option String) (loc : String) :
    IO (Option String) := do
  let hits := resolve rows mark
  if hits.isEmpty then
    let also ← near mark
    let hint := if also.isEmpty then
        "no declaration of that name in the index; re-run ./scripts/lean-refactor index if it is new"
      else s!"did you mean {", ".intercalate also.toList}?"
    return some s!"{loc}: {mark}: no such declaration — {hint}"
  if hits.size > 1 then
    let names := ", ".intercalate (hits.map (fun r => s!"{r.user} ({r.mod})")).toList
    return some s!"{loc}: {mark}: ambiguous — {names}; write the full Lean name"
  let r := hits[0]!
  let site := match r.line with | some l => s!"{r.src}:{l + 1}" | none => r.src
  match want with
  | none =>
    return some s!"{loc}: {mark}: uncertified — read {r.user} at {site} against the display, then \
      write lean:{mark}@{keyHex r.key}"
  | some w =>
    if w != keyHex r.key then
      return some s!"{loc}: {mark}: statement changed, key {w} → {keyHex r.key}; re-verify the \
        display against {r.user} at {site} and update the marker"
    return none

/-! ## The note's files

`CH` is the ONE variable every gate honours: `--ch N` off the command line, else `$CH`.  Narrowing to
a chapter means reading that chapter's file and nothing outside it. -/

def NOTE : String := "diag/allegory-axioms.typ"
def ROOT_MARK : String :=
  "// note-split: root — written by scripts/note-split and stripped by scripts/note-join"

def noteDie (msg : String) : IO α := die ("note-split: " ++ msg)

/-- The first string literal on a typst line, read as a literal: an escaped quote or a second
    literal on the line cannot make a `split('"')[1]` return something plausible and wrong. -/
partial def typstString (line : String) : Option String :=
  let cs := line.toList.toArray
  let rec go (i : Nat) (out : String) : Option String :=
    if i ≥ cs.size then none
    else if cs[i]! == '\\' && i + 1 < cs.size then go (i + 2) (out.push cs[i+1]!)
    else if cs[i]! == '"' then some out
    else go (i + 1) (out.push cs[i]!)
  match cs.findIdx? (· == '"') with
  | none => none
  | some i => go (i + 1) ""

def dirName (p : String) : String :=
  match (p.splitOn "/").dropLast with
  | [] => "."
  | ps => "/".intercalate ps

def joinPath (dir p : String) : String :=
  if p.startsWith "/" then p else if dir == "" then p else dir ++ "/" ++ p

/-- The files this one `#include`s, in order — the ONE place an include is recognised. -/
def includesOf (path : String) : IO (Array String) := do
  let here := dirName path
  let mut out : Array String := #[]
  for ln in (← readFileOr path).splitOn "\n" do
    if ln.startsWith "#include " then
      match typstString ln with
      | none => noteDie s!"{path}: `#include` with no file name: {ln}"
      | some inc => out := out.push (joinPath here inc)
  return out

/-- Chapter N's file: the N-th file the root includes, which is the N-th level-1 heading. -/
def chapterFile (root : String) (n : Nat) : IO String := do
  unless (← readFileOr root).startsWith ROOT_MARK do
    noteDie s!"CH={n}, but {NOTE} is not split into chapters: run ./scripts/note-split first"
  let chs ← includesOf root
  if n < 1 || n > chs.size then
    let list := "\n  ".intercalate
      (chs.mapIdx (fun i p => s!"{i + 1} {p}")).toList
    noteDie s!"no chapter {n}: {NOTE} includes {chs.size} chapters —\n  {list}"
  return chs[n - 1]!

/-- The root and every file it `#include`s, in order; a chapter named narrows it to that chapter. -/
partial def noteFiles (rootDir : String) (ch : Option Nat) (arg : String) : IO (Array String) := do
  let path := joinPath rootDir arg
  match ch with
  | some n => if path == joinPath rootDir NOTE then return #[← chapterFile path n]
  | none => pure ()
  let mut out : Array String := #[path]
  for inc in ← includesOf path do
    out := out ++ (← noteFiles rootDir none inc)
  return out

/-- `--ch N` off the arguments, else `$CH`; anything that is not a number stops the run. -/
def takeChapter (args : List String) : IO (Option Nat × List String) := do
  let readCh (s : String) : IO (Option Nat) :=
    if s.trimAscii.isEmpty then pure none
    else match s.trimAscii.toString.toNat? with
      | some n => pure (some n)
      | none => noteDie s!"CH={s} is no chapter: give its number among the note's level-1 headings, \
          e.g. CH=13 (./scripts/note-files lists the chapters in order)"
  match args.findIdx? (· == "--ch") with
  | some i =>
    if i + 1 ≥ args.length then noteDie "--ch takes the chapter's number, e.g. --ch 13"
    return (← readCh args[i+1]!, args.take i ++ args.drop (i + 2))
  | none => return (← readCh ((← IO.getEnv "CH").getD ""), args)

def relPath (cwd p : String) : String :=
  let ap := joinPath cwd p
  if ap.startsWith (cwd ++ "/") then (ap.drop (cwd.length + 1)).toString else ap

/-! ## `--cite` -/

def citeMain (args : List String) : IO UInt32 := do
  let cwd := (← IO.currentDir).toString
  let (ch, rest) ← takeChapter args
  let mut paths : Array String := #[]
  for a in rest do
    -- One entry per argument's expansion, NOT a set: naming a chapter beside the root it is
    -- included from checks it twice, and the count says so.
    for f in ← noteFiles cwd ch a do paths := paths.push (relPath cwd f)
  unless ← System.FilePath.pathExists INDEX do
    die s!"cite-check: {INDEX}: unable to open database file — run ./scripts/cap lake build && \
      ./scripts/lean-refactor index"
  -- Every marker first, then ONE query: 369 markers' worth of round trips against a 337MB db is
  -- what the Python cache existed to skip, and a single query does not need skipping.
  let mut found : Array (String × String × Option String) := #[]
  for p in paths do
    let mut i := 0
    for line in (← readFileOr p).splitOn "\n" do
      i := i + 1
      for (m, w) in marksOf line do
        found := found.push (s!"{p}:{i}", (m.dropEndWhile (· == '.')).toString, w)
  let marks := found.foldl (fun (acc : Array String) (_, m, _) =>
    if acc.contains m then acc else acc.push m) #[]
  let rows ← if marks.isEmpty then pure #[] else rowsOf (candidateSql marks)
  let mut bad : Array String := #[]
  for (loc, m, w) in found do
    if let some b ← check rows m w loc then bad := bad.push b
  if bad.isEmpty then
    IO.println s!"cite-check: {found.size} markers verified"
    return 0
  IO.eprintln ("\n".intercalate bad.toList)
  IO.eprintln s!"cite-check: {bad.size} of {found.size} markers failed"
  return 1

/-! ## `--cover` — for every labelled display, the Lean statement worth reading against it

`--cite` guards markers that already exist; this finds the displays that have none.  It does NOT
propose a marker and it cannot: a key pasted from a search is an uncertified claim wearing a
certificate's clothes.  So the output is a READING TASK — the note's formula and the candidate's
Lean statement on adjacent lines, so the two can be compared term by term and then certified by
hand. -/

/-- A display states something only if one of these stands between two terms.  `≜` and `:=`
    included: a definition IS a statement Lean can carry, it just cannot be a theorem. -/
def RELS : List Char := "=⊑⊒⟺⟹≜≤≥⊆⊇↔⇒⊣∼≅".toList

/-- The note explains AOP. -/
def libWeight (m : String) : Float :=
  match (m.splitOn ".").head! with
  | "AOP" => 1.0 | "rel" => 0.75 | "leet" => 0.7 | "diag" => 0.5 | "Freyd" => 0.5 | _ => 0.5

structure Spans where
  raws : Array (Nat × Nat)
  maths : Array (Nat × Nat)
  skip : Array (Nat × Nat)
  pairs : Array (Nat × Nat)          -- (close, open)

/-- One pass over the source: comment/raw/math spans, and the `[`…`]` pairs outside them.

    Brackets are counted everywhere else, string literals included — the notes put no `[` inside a
    `"…"`, and pretending otherwise costs a second failure mode.  Math is skipped whole. -/
def spansOf (cs : Array Char) : Spans := Id.run do
  let n := cs.size
  let has (i : Nat) (c : Char) := i < n && cs[i]! == c
  let find (pat : Array Char) (from_ : Nat) : Option Nat := Id.run do
    let mut i := from_
    while i + pat.size ≤ n do
      if (List.range pat.size).all (fun k => cs[i + k]! == pat[k]!) then return some i
      i := i + 1
    return none
  let mut raws : Array (Nat × Nat) := #[]
  let mut maths : Array (Nat × Nat) := #[]
  let mut skip : Array (Nat × Nat) := #[]
  let mut pairs : Array (Nat × Nat) := #[]
  let mut stack : Array Nat := #[]
  let mut i := 0
  while i < n do
    let c := cs[i]!
    if c == '/' && has (i+1) '/' then
      let j := (find #['\n'] i).getD n
      skip := skip.push (i, j); i := j
    else if c == '/' && has (i+1) '*' then
      let j := match find #['*', '/'] (i+2) with | some j => j + 2 | none => n
      skip := skip.push (i, j); i := j
    else if c == '`' then
      let k := runWhile cs (· == '`') i - i           -- a ``` block closes on its own fence width
      let fence := cs.extract i (i + k)
      let j := match find fence (i + k) with | some j => j + k | none => n
      raws := raws.push (i, j); i := j
    else if c == '$' then
      let j := match find #['$'] (i+1) with | some j => j + 1 | none => n
      maths := maths.push (i, j); i := j
    else
      if c == '[' then stack := stack.push i
      else if c == ']' && !stack.isEmpty then
        pairs := pairs.push (i, stack.back!); stack := stack.pop
      i := i + 1
  return { raws, maths, skip, pairs }

structure Note where
  path : String
  cs : Array Char
  sp : Spans
  nl : Array Nat                      -- the offset of every newline
  heads : Array (Nat × String × String)

def inAny (spans : Array (Nat × Nat)) (i : Nat) : Bool := spans.any fun (a, b) => a ≤ i && i < b

def Note.line (nt : Note) (i : Nat) : Nat := (nt.nl.filter (· < i)).size + 1

/-- The section heading the display sits under, with its level. -/
def Note.head (nt : Note) (i : Nat) : String × String :=
  match (nt.heads.filter (fun h => h.1 < i)).back? with
  | some (_, lvl, t) => (lvl, t)
  | none => ("=", "(front matter)")

def isWordStart (c : Char) : Bool := c.isAlpha && c.toNat < 128

/-- `(?m)^(=+) (.*)$` — a level-1 heading is `=`, a level-2 `==`. -/
def headsOf (cs : Array Char) : Array (Nat × String × String) := Id.run do
  let mut out := #[]
  let mut i := 0
  while i < cs.size do
    if (i == 0 || cs[i-1]! == '\n') && cs[i]! == '=' then
      let e := runWhile cs (· == '=') i
      if e < cs.size && cs[e]! == ' ' then
        let le := runWhile cs (· != '\n') (e + 1)
        out := out.push (i, slice cs i e, (slice cs (e+1) le).trimAscii.toString)
    i := i + 1
  return out

def mkNote (path : String) (src : String) : Note :=
  let cs := src.toList.toArray
  { path, cs, sp := spansOf cs,
    nl := (List.range cs.size).filter (fun i => cs[i]! == '\n') |>.toArray,
    heads := headsOf cs }

/-- `#disp[…]<label>`, found from the LABEL backwards: a label is unambiguous where a scan for
    `#disp[` would also have to decide what closes it. -/
def Note.displays (nt : Note) : Array (String × Nat × Nat) := Id.run do
  let cs := nt.cs
  let mut out := #[]
  let mut i := 0
  while i + 2 < cs.size do
    if cs[i]! == ']' && cs[i+1]! == '<' then
      let e := runWhile cs (fun c => (c.isAlphanum && c.toNat < 128) || c == '_' || c == '-') (i+2)
      if e > i + 2 && e < cs.size && cs[e]! == '>' then
        match (nt.sp.pairs.find? (fun p => p.1 == i)).map Prod.snd with
        | none => pure ()
        | some o =>
          unless inAny nt.sp.skip i do
            let head := slice cs (max 24 o - 24) o
            -- `#disp\s*$`, `#disp\[[^\]]*$`, or a `#disp` anywhere in the 24 characters before it.
            if (head.splitOn "#disp").length > 1 then out := out.push (slice cs (i+2) e, o, i)
      i := i + 1
    else i := i + 1
  return out

/-- The formula-bearing atoms in `[a,b)`: raw spans and math, minus anything inside `drop`. -/
def Note.atoms (nt : Note) (a b : Nat) (drop : Array (Nat × Nat)) : Array (Nat × Nat × String) :=
  let keep := (nt.sp.raws ++ nt.sp.maths).filter fun (lo, _) =>
    a ≤ lo && lo < b && !inAny drop lo && !inAny nt.sp.skip lo
  (keep.map fun (lo, hi) => (lo, hi, slice nt.cs lo hi)).qsort (fun x y => x.1 < y.1)

/-- `#src[…]` regions — the reason column.  Its formulas are citations, not the claim. -/
def Note.srcSpans (nt : Note) (a b : Nat) : Array (Nat × Nat) := Id.run do
  let cs := nt.cs
  let mut out := #[]
  let mut i := a
  while i + 5 ≤ b do
    if slice cs i (i+5) == "#src[" then
      match (nt.sp.pairs.find? (fun p => p.2 == i + 4)).map Prod.fst with
      | some c => out := out.push (i + 4, c + 1)
      | none => pure ()
    i := i + 1
  return out

/-- `re.sub(r"\s+", " ", s)`: a run of whitespace becomes ONE space and the ends keep theirs — the
    space between two atoms is part of the formula (`P=E on maps`, not `P=Eon maps`). -/
def squash (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < cs.size do
    if isSpace cs[i]! then out := out.push ' '; i := runWhile cs isSpace i
    else out := out.push cs[i]!; i := i + 1
  return out

/-- Whitespace runs collapsed, as `" ".join(s.split())` does it. -/
def flat (s : String) : String :=
  " ".intercalate ((s.toList.map (fun c => if isSpace c then ' ' else c) |> String.ofList
    |>.splitOn " ").filter (· != ""))

def unraw (s : String) : String := (s.dropWhile (· == '`') |>.dropEndWhile (· == '`')).toString

/-- One atom as the reader sees it.  `$frac(#[`S`], ∋)$` keeps its own shape — the note's division
    bar is not `S/∋` (it is `Λ S`), and rewriting it here would hide which of the two it wrote. -/
def render (text : String) : String :=
  if text.startsWith "$" then
    let inner := slice (text.toList.toArray) 1 (text.length - 1)
    -- `frac(#[`x`], y)` → `frac(x, y)`, then every `#[`, `]` and backtick dropped.
    let t := Id.run do
      let cs := inner.toList.toArray
      let mut out := ""
      let mut i := 0
      while i < cs.size do
        if i + 5 ≤ cs.size && slice cs i (i+5) == "frac(" then
          let a := runWhile cs isSpace (i+5)
          if a + 2 ≤ cs.size && slice cs a (a+2) == "#[" then
            -- the shortest `]` closing the first argument, then the rest up to the matching `)`
            let mut j := a + 2
            while j < cs.size && cs[j]! != ']' do j := j + 1
            let lhs := (slice cs (a+2) j).trimAscii.toString
            let mut k := runWhile cs isSpace (j + 1)
            if k < cs.size && cs[k]! == ',' then
              k := k + 1
              let mut d := 0
              let mut e := k
              while e < cs.size && !(d == 0 && cs[e]! == ')') do
                if cs[e]! == '(' then d := d + 1 else if cs[e]! == ')' then d := d - 1
                e := e + 1
              out := out ++ s!"frac({unraw lhs}, {(slice cs k e).trimAscii.toString})"
              i := e + 1
            else out := out ++ "frac("; i := i + 5
          else out := out ++ "frac("; i := i + 5
        else out := out.push cs[i]!; i := i + 1
      return out
    flat (t.replace "#[" "" |>.replace "]" "" |>.replace "`" "")
  else (unraw text).trimAscii.toString

/-! ### The tokenizer, shared by the note's formulas and the index's statements -/

def SYMS : List Char := "⊑⊒∩∪°∋∈⟶≫×⦇⊔⊓↔∀∃⊤𝟙Λμ\\".toList

/-- The note's glyph for a thing Lean spells with letters.  Only where the two really are the same
    thing: `E(-)` is the power object, `frac(x, ∋)` is `Λ x`, `⦇…⦈` is the reduce. -/
def GLYPH : List (String × String × Bool) :=
  [("E(", " powerObj ", true), ("P(", " powerRel ", true), ("⦇", " relCata cata ", false),
   ("⦈", " relCata cata ", false), ("frac(", " Λ ", true), ("𝟙", " id ", false),
   ("⊤", " top ", false), ("μ", " mu ", false), ("Dom", " dom ", true), ("Ran", " ran ", true),
   ("union", " bigUnion union ", true)]

/-- `\b` before the letter-initial patterns: `Dom` inside `RanDom` is not the operator. -/
def applyGlyphs (s : String) : String := Id.run do
  let mut text := s
  for (pat, rep, word) in GLYPH do
    let cs := text.toList.toArray
    let p := pat.toList.toArray
    let mut out := ""
    let mut i := 0
    while i < cs.size do
      let hit := i + p.size ≤ cs.size && (List.range p.size).all (fun k => cs[i+k]! == p[k]!)
        && (!word || i == 0 || !isWordChar cs[i-1]!)
        && (!word || !(isWordStart p[0]!) || i + p.size ≥ cs.size || !isWordChar cs[i + p.size]!
            || !isWordStart p[p.size - 1]!)
      if hit then out := out ++ rep; i := i + p.size
      else out := out.push cs[i]!; i := i + 1
    text := out
  return text

/-- `[A-Za-z][A-Za-z0-9_']*` over the text with `.` and `_` blanked, each word cut into its camel
    parts (`[A-Z]?[a-z0-9']+|[A-Z]+(?![a-z])`), lowercased, parts of one character dropped. -/
def toks (text : String) : Array String := Id.run do
  let cs := (applyGlyphs text).toList.toArray
  let mut out : Array String := #[]
  for c in cs do
    if SYMS.contains c then out := out.push c.toString
  let blanked := (cs.map fun c => if c == '.' || c == '_' then ' ' else c)
  let isW (c : Char) := (c.isAlphanum && c.toNat < 128) || c == '\''
  let mut i := 0
  while i < blanked.size do
    if isWordStart blanked[i]! then
      let e := runWhile blanked isW i
      -- the camel parts of one word
      let w := blanked.extract i e
      let mut j := 0
      while j < w.size do
        let s :=
          if w[j]!.isUpper then
            let k := runWhile w (fun c => c.isLower || c.isDigit || c == '\'') (j+1)
            if k > j + 1 then (j, k)                        -- `[A-Z]?[a-z0-9']+`
            else
              -- `[A-Z]+(?![a-z])`: greedy, then backtracked off a capital that starts the next
              -- word — `ABCdef` is `AB` and `Cdef`, never `ABC` and `def`.
              let e := runWhile w (fun c => c.isUpper) j
              (j, if e < w.size && w[e]!.isLower then e - 1 else e)
          else (j, runWhile w (fun c => c.isLower || c.isDigit || c == '\'') j)
        let (a, b) := s
        let b := if b ≤ a then a + 1 else b
        if b - a > 1 then out := out.push (String.ofList (w.extract a b).toList).toLower
        j := b
      i := e
    else i := i + 1
  return out

/-! ### The corpus, scored by how much INFORMATION a formula shares with a statement

Weight is inverse document frequency, so `est`, `hylo` and `⦇` decide a match and `⊑`, which 2000
statements carry, decides nothing.  A hit in the declaration's NAME counts double: names are chosen,
statements accumulate. -/

structure Cand where
  user : String
  mod : String
  src : String
  line : Option Int
  stmt : String
  key : Int
deriving Inhabited

structure Index where
  rows : Array Cand
  post : Std.HashMap String (Array (Nat × Float))
  size : Array Float
  idf : Std.HashMap String Float

/-- A bag in INSERTION order, so the float sum that ranks a candidate is accumulated in the order
    Python's dict accumulated it and the two agree bit for bit. -/
def bagOf (ts : Array String) (w : Float) (init : Array (String × Float)) :
    Array (String × Float) := Id.run do
  let mut bag := init
  for t in ts do
    match bag.findIdx? (fun p => p.1 == t) with
    | some i => bag := bag.set! i (t, bag[i]!.2 + w)
    | none => bag := bag.push (t, w)
  return bag

def mkIndex (rows : Array Cand) : Index := Id.run do
  let mut post : Std.HashMap String (Array (Nat × Float)) := {}
  let mut size : Array Float := #[]
  for n in List.range rows.size do
    let r := rows[n]!
    let bag := bagOf (toks r.user) 2.0 (bagOf (toks r.stmt) 1.0 #[])
    size := size.push (bag.foldl (fun a p => a + p.2) 0.0)
    for (t, c) in bag do
      post := post.insert t ((post.getD t #[]).push (n, c))
  let idf := post.fold (fun m t p =>
    m.insert t (Float.log (rows.size.toFloat / p.size.toFloat))) {}
  return { rows, post, size, idf }

def Index.rank (idx : Index) (formula context : String) (k : Nat) : Array (Cand × Float) := Id.run do
  let q := bagOf (toks context) 0.5 (bagOf (toks formula) 1.0 #[])
  let mut score : Array (Nat × Float) := #[]      -- insertion order, as Python's defaultdict
  for (t, w) in q do
    let i := idx.idf.getD t 0.0
    if i < 0.7 then continue                      -- in a fifth of all statements: says nothing
    for (n, c) in idx.post.getD t #[] do
      let add := w * i * (min c 3.0) / (1.0 + 0.35 * Float.log (1.0 + idx.size[n]!))
      match score.findIdx? (fun p => p.1 == n) with
      | some j => score := score.set! j (n, score[j]!.2 + add)
      | none => score := score.push (n, add)
  let weighted := score.map fun (n, s) => (n, s * libWeight idx.rows[n]!.mod)
  let best := weighted.toList.mergeSort (fun a b => a.2 ≥ b.2)
  return (best.take k).toArray.map fun (n, s) => (idx.rows[n]!, s)

def Cand.where_ (c : Cand) : String :=
  match c.line with | some l => s!"{c.src}:{l + 1}" | none => c.src

/-- `{:g}`: the trailing zeros of a decimal fraction dropped, and with them a bare point. -/
def fmtG (x : Float) : String :=
  let s := toString x
  if (s.splitOn ".").length == 2 then ((s.dropEndWhile (· == '0')).dropEndWhile (· == '.')).toString
  else s

/-- Two decimals the way Python's `{:.1f}`/`{:.1f}` print one. -/
def fmt1 (x : Float) : String :=
  let n := (x * 10.0 + 0.5).floor.toUInt64.toNat
  s!"{n / 10}.{n % 10}"

structure CoverArgs where
  n : Nat := 2
  thresh : Float := 6.0
  label : Option String := none
  unmarked : Bool := false
  all : Bool := false
  quiet : Bool := false
  summary : Bool := false

/-- The source between two atoms, as it reads.  `α`#sub[`T`]`⦈` is ONE term: the subscript call is
    spelled `_` and its `]` is swallowed, so the formula is not cut into three at every `α_T`. -/
def gapText (text : String) (sub : Nat) : String × Nat := Id.run do
  -- `#h(-3.5pt)` is a kern, not a break between two formulas.
  let cs := (Id.run do
    let a := text.toList.toArray
    let mut o := ""
    let mut i := 0
    while i < a.size do
      if i + 3 ≤ a.size && slice a i (i+3) == "#h(" then
        let e := runWhile a (fun c => c.isDigit || c == '.' || c == '-' ) (i+3)
        if e + 3 ≤ a.size && slice a e (e+3) == "pt)" then o := o ++ " "; i := e + 3
        else o := o ++ "#h("; i := i + 3
      else o := o.push a[i]!; i := i + 1
    return o).toList.toArray
  let mut out := ""
  let mut k := 0
  let mut s := sub
  while k < cs.size do
    if k + 5 ≤ cs.size && slice cs k (k+5) == "#sub[" then
      s := s + 1; out := out ++ "_"; k := k + 5
    else if k + 7 ≤ cs.size && slice cs k (k+7) == "#super[" then
      s := s + 1; out := out ++ "^"; k := k + 7
    else if s > 0 && cs[k]! == ']' then s := s - 1; k := k + 1
    else out := out.push cs[k]!; k := k + 1
  return (out, s)

/-- What the display STATES, as strings.

    Atoms written flush against each other are one formula — an equation the author broke to typeset
    a fraction — and a gap of any kind starts a new one.  A `zsqc(x, y)` box is the note's
    rule-between-two-rows, i.e. `x ⊑ y` (`eq: true` makes it `=`), so it is assembled first and its
    parts are then spent. -/
def formulas (nt : Note) (a b : Nat) : Array (Nat × String) := Id.run do
  let cs := nt.cs
  let drop := nt.srcSpans a b
  let mut out : Array (Nat × String) := #[]
  let mut spent : Array Nat := #[]
  let mut i := a
  while i < b do
    let isZ := (i + 4 ≤ cs.size && slice cs i (i+4) == "zsq(")
      || (i + 5 ≤ cs.size && slice cs i (i+5) == "zsqc(")
    if isZ && (i == a || !isWordChar cs[i-1]!) then
      let o := runWhile cs (· != '(') i
      let mut d := 0
      let mut j := o
      while j < b do
        if cs[j]! == '(' then d := d + 1
        else if cs[j]! == ')' then
          d := d - 1
          if d == 0 then break
        j := j + 1
      let body := slice cs (o+1) j
      let mut args : Array (Nat × Nat) := #[]
      let mut dd := 0
      let mut last := o + 1
      for k in List.range (j - (o + 1)) do
        let p := o + 1 + k
        if cs[p]! == '(' || cs[p]! == '[' then dd := dd + 1
        else if cs[p]! == ')' || cs[p]! == ']' then dd := dd - 1
        else if cs[p]! == ',' && dd == 0 then args := args.push (last, p); last := p + 1
      args := args.push (last, j)
      let pos := args.filter fun (x, y) => !((slice cs x y).splitOn "`").head!.any (· == ':')
      let rel := if (body.splitOn "eq:").length > 1
        && ((body.splitOn "eq:").getD 1 "").trimAscii.toString.startsWith "true" then " = "
        else " ⊑ "
      if pos.size ≥ 2 then
        let mut sides : Array String := #[]
        for (x, y) in pos.extract 0 2 do
          let ats := nt.atoms x y drop
          spent := spent ++ ats.map (·.1)
          sides := sides.push (String.join (ats.map (fun t => render t.2.2)).toList)
        if sides.all (· != "") then out := out.push (nt.line o, rel.intercalate sides.toList)
      i := j + 1
    else i := i + 1
  -- the loose atoms, glued into runs
  let mut run := ""
  let mut endPos : Option Nat := none
  let mut start := 0
  let mut sub := 0
  for (lo, hi, txt) in nt.atoms a b drop do
    if spent.contains lo then continue
    let (glue, sub') : Option String × Nat := match endPos with
      | none => (none, 0)
      | some e => let (g, s) := gapText (slice cs e lo) sub; (some g, s)
    sub := sub'
    -- GLUE: `[^#\[\]()$\n]{0,26}` or `\s*\\?\s*`; TAIL: the leading run of those same characters.
    let ok (g : String) : Bool :=
      let g2 := g.replace "\\\n" " "
      let plain := g2.toList.all fun c =>
        c != '#' && c != '[' && c != ']' && c != '(' && c != ')' && c != '$' && c != '\n'
      (plain && g2.length ≤ 26)
        || (g2.toList.all fun c => isSpace c || c == '\\')
    let mut g := glue
    match g with
    | some gg =>
      if !ok gg then
        let tail := gg.toList.takeWhile fun c =>
          c != '#' && c != '[' && c != ']' && c != '(' && c != ')' && c != '$' && c != '\n'
        out := out.push (nt.line start, run ++ squash (String.ofList tail))
        run := ""; g := none; sub := 0
    | none => pure ()
    if run == "" then start := lo
    run := run ++ (match g with | some gg => squash gg | none => "") ++ render txt
    endPos := some hi
  if run != "" then out := out.push (nt.line start, run)
  let mut seen : Array String := #[]
  let mut keep : Array (Nat × String) := #[]
  for (ln, f) in out do
    let f := flat f
    if f.length > 2 && f.toList.any (fun c => RELS.contains c) && !seen.contains f then
      seen := seen.push f; keep := keep.push (ln, f)
  return keep

def coverOne (nt : Note) (rows : Array Row) (idx : Index) (ar : CoverArgs) :
    IO (Array String × Nat × Nat × Nat × Nat × Array (String × String)) := do
  let mut marked := 0
  let mut plausible := 0
  let mut unmatched : Array (String × String) := #[]
  let mut silent := 0
  let mut lines : Array String := #[]
  for (label, a, b) in nt.displays do
    if let some ls := ar.label then
      unless (ls.splitOn ",").contains label do continue
    let (lvl, title) := nt.head a
    let text := slice nt.cs a b
    let marks := (text.splitOn "\n").foldl (fun acc l => acc ++ marksOf l) #[]
    let fs := formulas nt a b
    let head := s!"\n[{label}] {nt.path}:{nt.line a}  {lvl} {flat title}"
    if !marks.isEmpty then
      marked := marked + 1
      unless ar.unmarked do
        lines := lines.push head
        for (name, want) in marks do
          let hits := resolve rows ((name.dropEndWhile (· == '.')).toString)
          let site := match hits[0]? with
            | some r => s!" — {r.user} at " ++
                (match r.line with | some l => s!"{r.src}:{l+1}" | none => r.src)
            | none => " — UNRESOLVED"
          lines := lines.push s!"  certified  lean:{name}@{want.getD ""}{site}"
      continue
    if fs.isEmpty then
      silent := silent + 1
      unless ar.unmarked || ar.quiet do
        lines := lines.push head
        lines := lines.push "  no statement — picture, drawing step, or prose only"
      continue
    let ranked := fs.map fun (ln, f) => (ln, f, idx.rank f title ar.n)
    let top := ranked.foldl (fun m (_, _, cs) => cs.foldl (fun m' (_, s) => max m' s) m) 0.0
    if top ≥ ar.thresh then plausible := plausible + 1
    else unmatched := unmatched.push (label, title)
    lines := lines.push (head ++ s!"   UNMARKED, {fs.size} formula(s), best {fmt1 top}")
    let shown := if ar.all then ranked else ranked.extract 0 (min 8 ranked.size)
    for (ln, f, cands) in shown do
      lines := lines.push s!"  {nt.path}:{ln}"
      lines := lines.push s!"    note ┃ {f}"
      for (r, s) in cands do
        lines := lines.push s!"    lean ┃ {flat r.stmt}"
        lines := lines.push s!"         ┗━ {r.user}  ({r.mod}, {r.where_})  score {fmt1 s}  \
          lean:{r.mod}.{lastComp r.user}@{keyHex r.key}"
      if cands.isEmpty then
        lines := lines.push "    lean ┃ (nothing in the index shares a symbol with it)"
    if ranked.size > shown.size then
      lines := lines.push s!"  … {ranked.size - shown.size} more formulas (--all)"
  return (lines, marked, plausible, silent, unmatched.size, unmatched)

def coverMain (args : List String) : IO UInt32 := do
  let cwd := (← IO.currentDir).toString
  let (ch, rest) ← takeChapter args
  let mut ar : CoverArgs := {}
  let mut paths : Array String := #[]
  let mut it := rest
  while !it.isEmpty do
    let a := it.head!
    it := it.tail!
    if a == "-n" then
      let some v := it.head?.bind (·.toNat?) | die "cite-cover: -n takes a number"
      ar := { ar with n := v }; it := it.tail!
    else if a == "--thresh" then
      let some v := it.head? | die "cite-cover: --thresh takes a number"
      let some f := Json.parse v |>.toOption.bind (·.getNum?.toOption) |
        die s!"cite-cover: --thresh {v} is no number"
      ar := { ar with thresh := f.toFloat }; it := it.tail!
    else if a == "--label" then
      let some v := it.head? | die "cite-cover: --label takes a label"
      ar := { ar with label := some v }; it := it.tail!
    else if a == "--unmarked" then ar := { ar with unmarked := true }
    else if a == "--all" then ar := { ar with all := true }
    else if a == "--quiet" then ar := { ar with quiet := true }
    else if a == "--summary" then ar := { ar with summary := true }
    else if a.startsWith "-" then die s!"cite-cover: no such option {a}"
    else paths := paths.push a
  -- THE .typ EVERY GATE READS: the chapter when `CH`/`--ch` names one, else the note; and a split
  -- root is a preamble, so it stands for the chapters it includes rather than being swept empty.
  if paths.isEmpty then
    paths := (← noteFiles cwd ch NOTE).map (relPath cwd)
  else
    paths := (← paths.toList.flatMapM (fun a => do pure (← noteFiles cwd ch a).toList)).toArray.map
      (relPath cwd)
  unless ← System.FilePath.pathExists INDEX do
    die s!"cite-cover: {INDEX}: unable to open database file — run ./scripts/cap lake build && \
      ./scripts/lean-refactor index"
  let corpus ← indexRows
    ("select i.user_name, i.module, m.source, r.sl1, i.stmt, i.stmt_key from decl_info i"
     ++ " join module m on m.name = i.module"
     ++ " left join decl_range r on r.name = i.name and r.module = i.module"
     ++ " where i.internal = 0 and i.stmt is not null and i.stmt != ''"
     ++ " and i.user_name not like '%«%'")
  let cands ← corpus.mapM fun j => do
    pure { user := ← cell j "user_name", mod := ← cell j "module", src := ← cell j "source",
           line := ← numCell j "sl1", stmt := ← cell j "stmt",
           key := (← numCell j "stmt_key").getD 0 : Cand }
  let idx := mkIndex cands
  let rows := cands.map fun c =>
    ({ user := c.user, mod := c.mod, src := c.src, line := c.line, key := c.key } : Row)
  for p in paths do
    let nt := mkNote p (← readFileOr p)
    let (lines, marked, plausible, silent, nUn, unmatched) ← coverOne nt rows idx ar
    unless ar.summary do IO.println ("\n".intercalate lines.toList)
    -- Counted directly, line by line: a marker is loose when its line is in no display's line range.
    let spans := nt.displays.map fun (_, a, b) => (nt.line a, nt.line b)
    let loose := (((← readFileOr p).splitOn "\n").foldl (fun (n, ln) l =>
      (if spans.any (fun (lo, hi) => lo ≤ ln && ln ≤ hi) then n else n + (marksOf l).size, ln + 1))
      (0, 1)).1
    IO.println s!"\n{p}: {marked + plausible + nUn + silent} labelled displays — {marked} \
      certified, {plausible} unmarked with a candidate to read, {nUn} unmarked with nothing above \
      {fmtG ar.thresh}, {silent} stating no formula.  {loose} markers outside a display."
    if nUn > 0 && !ar.summary then
      IO.println ("  nothing found for: " ++ ", ".intercalate
        ((unmatched.extract 0 (min 12 unmatched.size)).map (fun (l, t) => s!"{l} ({flat t})")).toList)
  return 0

end Freyd.Cite
