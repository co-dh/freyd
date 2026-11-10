import LeetQ.Rel.Lang.Eval

/-! `rel FILE`: parse, elaborate and run a Rel program; print each `print`, or the front-end error and exit 1. -/

open LeetQ.Rel.Lang

def main : List String → IO UInt32
  | [f] => do
    match runText (← IO.FS.readFile f) with
    | .ok o => o.prints.forM IO.println; pure 0
    | .error e => IO.eprintln s!"{f}: {e}"; pure 1
  | _ => do IO.eprintln "usage: rel FILE"; pure 2
