/-
  Always-on profiling of `diag-export`: every run appends its phase times to ONE log shared by all
  worktrees, so the runs other agents make anyway are the sample, and nobody has to re-run a route
  under a profiler to learn where the CPU goes.

  A PHASE IS TIMED EXCLUSIVELY, per thread: entering one pauses the phase it runs inside, so a
  label printed during a search is charged to `label` and not to both, and a recursive phase is
  charged once.  Every drawing task runs on one pool thread from start to end, so keying the stack
  by thread id is what attributes a phase to its panel; the task drains its thread's totals itself.

  Log: `$HOME/.cache/diag-export/prof.tsv`, beside the repo's other `~/.cache` state
  (`freyd-note.lock`, `book-index`).  Columns:
    ts_ms  sha  cwd  pid  selector  phase  ms  extra
  `ts_ms` is the run's start (Unix epoch ms), `sha` the tree's HEAD, `selector` `-` for a
  process-level line; `extra` is `k=v` pairs (heartbeats `hb`, `calls`, the route `kind`, …).
-/
import Lean

namespace Freyd.Prof

/-- A phase's running totals on one thread: nanoseconds, heartbeats, outermost entries. -/
structure Acc where
  ns : Nat := 0
  hb : Nat := 0
  calls : Nat := 0

/-- A phase open on a thread, and the clock and heartbeat count at which it last resumed. -/
structure Frame where
  name : String
  ns : Nat
  hb : Nat

structure Thread where
  stack : List Frame := []
  acc : Std.HashMap String Acc := {}

initialize threads : IO.Ref (Std.HashMap UInt64 Thread) ← IO.mkRef {}

/-- Charge the time since the top frame resumed to its phase, and resume it now. -/
def Thread.charge (t : Thread) (ns hb : Nat) : Thread :=
  match t.stack with
  | [] => t
  | f :: r =>
    let a := t.acc.getD f.name {}
    { acc := t.acc.insert f.name { a with ns := a.ns + (ns - f.ns), hb := a.hb + (hb - f.hb) }
      stack := { f with ns, hb } :: r }

def enter (name : String) : BaseIO Unit := do
  let tid ← IO.getTID; let ns ← IO.monoNanosNow; let hb ← IO.getNumHeartbeats
  threads.modify fun m =>
    let t := (m.getD tid {}).charge ns hb
    -- A recursive entry continues its own phase, so only a fresh one counts as a call.
    let a := t.acc.getD name {}
    let calls := a.calls + if t.stack.head?.map (·.name) == some name then 0 else 1
    m.insert tid { acc := t.acc.insert name { a with calls }, stack := { name, ns, hb } :: t.stack }

def exit : BaseIO Unit := do
  let tid ← IO.getTID; let ns ← IO.monoNanosNow; let hb ← IO.getNumHeartbeats
  threads.modify fun m =>
    let t := (m.getD tid {}).charge ns hb
    let stack := match t.stack.drop 1 with
      | f :: r => { f with ns, hb } :: r
      | [] => []
    m.insert tid { t with stack }

/-- Run `x` as the phase `name` of the current thread. -/
@[inline] def phase {m : Type → Type} {α : Type} [Monad m] [MonadLiftT BaseIO m] [MonadFinally m]
    (name : String) (x : m α) : m α := do
  enter name
  try x finally exit

/-- Remove and return the current thread's phase totals — the task calling it owns them. -/
def drain : BaseIO (Array (String × Acc)) := do
  let tid ← IO.getTID
  threads.modifyGet fun m => ((m.getD tid {}).acc.toArray, m.erase tid)

/-- One line of the log. -/
structure Line where
  sel : String := "-"
  phase : String
  ns : Nat
  extra : String := ""

def ms (ns : Nat) : String :=
  let us := ns / 1000
  s!"{us / 1000}.{toString (1000 + us % 1000) |>.drop 1}"

/-- A `/proc` file, or an error naming it. -/
def readProc (path : String) : IO String := IO.FS.readFile path

/-- The fields of `/proc/self/stat` after the command name, which proc(5) delimits by the LAST `)`
    because the name itself may hold spaces and parentheses. -/
def statFields : IO (Array String) := do
  let s ← readProc "/proc/self/stat"
  let rest := (s.splitOn ")").getLast!
  return (rest.splitOn " ").filter (· != "") |>.toArray

/-- `user_ms sys_ms rss_peak_kb` of this process, all threads.  `/proc` counts CPU in USER_HZ,
    which the Linux ABI fixes at 100 whatever the kernel's HZ. -/
def processExtra : IO String := do
  let f ← statFields
  -- `utime` and `stime` are fields 14 and 15; `f` starts at field 3.
  let tick (i : Nat) : IO Nat := match f[i - 3]? >>= String.toNat? with
    | some n => pure (n * 10)
    | none => throw (.userError s!"/proc/self/stat: field {i} is not a number in {f}")
  let hwm := (← readProc "/proc/self/status").splitOn "\n" |>.find? (·.startsWith "VmHWM:")
  let some hwm := hwm.bind fun l => ((l.drop 6).trimAscii.toString.splitOn " ").head?
    | throw (.userError "/proc/self/status: no VmHWM line")
  return s!"user_ms={← tick 14} sys_ms={← tick 15} rss_peak_kb={hwm}"

/-- Unix epoch in ms: `/proc/stat`'s boot time plus `/proc/uptime`, since core Lean reads only a
    monotonic clock. -/
def epochMs : IO Nat := do
  let btime := (← readProc "/proc/stat").splitOn "\n" |>.find? (·.startsWith "btime ")
  let some b := btime.bind fun l => (l.drop 6).trimAscii.toString.toNat?
    | throw (.userError "/proc/stat: no btime line")
  let up := ((← readProc "/proc/uptime").splitOn " ").head!.splitOn "."
  let some s := up.head!.toNat? | throw (.userError s!"/proc/uptime: not seconds.centis: {up}")
  let cs := (up[1]?.bind String.toNat?).getD 0
  return (b + s) * 1000 + cs * 10

def sha : IO String := do
  let o ← IO.Process.output { cmd := "git", args := #["rev-parse", "--short=12", "HEAD"] }
  if o.exitCode != 0 then throw (.userError s!"git rev-parse HEAD: {o.stderr.trimAscii}")
  return o.stdout.trimAscii.toString

def logPath : IO System.FilePath := do
  let some home ← IO.getEnv "HOME" | throw (.userError "HOME is unset")
  return home / ".cache" / "diag-export" / "prof.tsv"

/-- Append `lines` to the shared log, one flushed write per line on an `O_APPEND` handle, so
    concurrent runs interleave whole lines.  A failure is WARNED, naming the path, and the run goes
    on: the drawing is the deliverable, the log is not. -/
def write (t0 : Nat) -- the run's start on the monotonic clock
    (lines : Array Line) : IO Unit := do
  let r ← (do
    let path ← logPath
    try
      if let some d := path.parent then IO.FS.createDirAll d
      let ts := (← epochMs) - ((← IO.monoNanosNow) - t0) / 1000000
      let pre := s!"{ts}\t{← sha}\t{← IO.currentDir}\t{← IO.Process.getPID}\t"
      let h ← IO.FS.Handle.mk path .append
      for l in lines do
        h.putStr s!"{pre}{l.sel}\t{l.phase}\t{ms l.ns}\t{l.extra}\n"
        h.flush
    catch e => throw (IO.userError s!"{path}: {e}") : IO Unit).toBaseIO
  if let .error e := r then IO.eprintln s!"diag-export: profiling log not written: {e}"

end Freyd.Prof
