import LeetQ.Rel.Lang.Eval

/-! `rel FILE`: parse, elaborate and run a Rel program; print each `print`, or the front-end error and exit 1.

    Every run is capped in RESIDENT memory: `main` re-executes this binary once as a child that does the work, and
    stays to poll the child's resident set (`/proc/<pid>/statm`) every `pollMs`; past `REL_MEM_MB` (default 10240)
    it terminates the child and exits 3 naming the cap. Not an rlimit: `RLIMIT_RSS` is a no-op on Linux, and
    `RLIMIT_AS`/`RLIMIT_DATA` count address space, which here runs 6–35× the resident set (the chess program peaks at
    11.5 GB of address space and 1.7 GB resident, an empty program at 1.2 GB and 0.02 GB), so a 4 GB `ulimit -v`
    kills a program that needs 1.7 GB; cgroups need a user bus the sandbox denies (`scripts/cap`). -/

open LeetQ.Rel.Lang

/-- The work: run the program `f`, a `.rel.md` file (`Parse.programText`); `--types f` prints the declaration of each of its definitions, `--types` alone
    the prelude's. -/
def body : List String → IO UInt32
  | ["--types"] => do
    match typesOf none with
    | .ok ls => ls.forM IO.println; pure 0
    | .error e => IO.eprintln s!"prelude: {e}"; pure 1
  | ["--types", f] => do
    match Parse.programText f (← IO.FS.readFile f) >>= (typesOf ∘ some) with
    | .ok ls => ls.forM IO.println; pure 0
    | .error e => IO.eprintln s!"{f}: {e}"; pure 1
  | [f] => do
    match Parse.programText f (← IO.FS.readFile f) >>= runText with
    | .ok o => o.prints.forM IO.println; pure 0
    | .error e => IO.eprintln s!"{f}: {e}"; pure 1
  | _ => do IO.eprintln "usage: rel FILE | rel --types [FILE], FILE a `.rel.md` program"; pure 2

/-- Set in the watched child: the child does the work, the parent only launches and watches it. -/
def childVar : String := "REL_MEM_CHILD"

def pollMs : UInt32 := 20

/-- The cap in MB: `REL_MEM_MB`, else 10240. -/
def limitMB : IO (Except String Nat) := do
  match ← IO.getEnv "REL_MEM_MB" with
  | none => pure (.ok 10240)
  | some s => pure <| match s.toNat? with
    | some n => if n > 0 then .ok n else .error s!"REL_MEM_MB={s} is not a positive number of MB; unset it for 10240"
    | none => .error s!"REL_MEM_MB={s} is not a positive number of MB; unset it for 10240"

/-- The page size in bytes, which `statm` counts in: `getconf PAGESIZE`. -/
def pageBytes : IO (Except String Nat) := do
  match ← (IO.Process.output { cmd := "getconf", args := #["PAGESIZE"] }).toBaseIO with
  | .error e => pure (.error s!"cannot run `getconf PAGESIZE`: {e}")
  | .ok o => pure <| match o.exitCode, o.stdout.trimAscii.toString.toNat? with
    | 0, some n => .ok n
    | c, _ => .error s!"`getconf PAGESIZE` exited {c} with output '{o.stdout}', not a number"

/-- The resident pages of `pid`: the second of `statm`'s space-separated counts (proc(5)). -/
def residentPages (pid : UInt32) : IO (Except String Nat) := do
  let f := s!"/proc/{pid}/statm"
  match ← (IO.FS.readFile f).toBaseIO with
  | .error e => pure (.error s!"cannot read {f}: {e}")
  | .ok t => pure <| match (t.splitOn " ")[1]?.bind (·.toNat?) with
    | some n => .ok n
    | none => .error s!"{f} holds '{t.trimAscii}', with no resident count in its second field"

/-- Wait for `c`, polling its resident pages against `cap`: `.ok` its status, or `.error` why it was stopped. -/
partial def watch {cfg : IO.Process.StdioConfig} (c : IO.Process.Child cfg) (cap : Nat) : IO (Except (Option Nat × String) UInt32) := do
  if let some s ← c.tryWait then return .ok s
  match ← residentPages c.pid with
  | .error m => return .error (none, m)
  | .ok p => if p > cap then return .error (some p, "") else IO.sleep pollMs; watch c cap

def main (args : List String) : IO UInt32 := do
  if (← IO.getEnv childVar).isSome then return ← body args
  let mb ← match ← limitMB with
    | .ok mb => pure mb
    | .error m => IO.eprintln s!"rel: {m}"; return 2
  let page ← match ← pageBytes with
    | .ok n => pure n
    | .error m => IO.eprintln s!"rel: cannot cap memory at {m}; rel needs `getconf` (glibc) and /proc"; return 3
  let self ← IO.appPath
  let child ← match ← (IO.Process.spawn { cmd := self.toString, args := args.toArray, env := #[(childVar, some "1")] }).toBaseIO with
    | .ok c => pure c
    | .error e => IO.eprintln s!"rel: cannot start {self} as the watched child: {e}"; return 3
  match ← watch child (mb * 1024 * 1024 / page) with
  | .ok s => return s
  | .error (p, m) =>
    child.kill
    let s ← child.wait
    match p with
    | some p => IO.eprintln s!"rel: {" ".intercalate args}: stopped at {p * page / 1048576} MB resident, past the cap of {mb} MB (REL_MEM_MB); child status {s}; to allow more, rerun with REL_MEM_MB={2 * mb}"
    | none => IO.eprintln s!"rel: {" ".intercalate args}: stopped, its memory could no longer be watched: {m}; child status {s}"
    return 3
