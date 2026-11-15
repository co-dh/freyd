import LeetQ.Rel.Lang.EmitC
import LeetQ.Run.Lang.Embed
import LeetQ.Rel.Lang.GenSpec

/-! Stage 1a of the native backend (`doc/rel-native-design.md` §13): `x ≜ {…}°`, `output x to "out"`. Its plan is
    literals and `qlean_own_write` calls only: the converse is a register rename. `main` is the `relc-1a` exe:
    `c FILE` prints the plan as C, `lean DIR` writes `DIR/out` from the value Lean computed (`writeRel`), `plan DIR`
    runs the plan in `DIR` (`Plan.run`). The language has no `output` declaration yet (stage 2), so the output is
    stated here, as `planOf`'s arguments. -/

namespace LeetQ.Rel.Lang.TestNative

open LeetQ.Rel LeetQ.Rel.Lang LeetQ.Rel.Lang.Plan

rel_program native1a where
    obj X = {A,B,C}
    obj N = 0…9
    x : X ⟶ N ≜ {(1,A),(2,B),(5,C),(5,A)}°

/-- `output x to "out"`. -/
def plan : Except String Plan := planOf [] native1a "x" "out"

-- two columns, each six `lit`s, a path `lit` and one `qlean_own_write`; nothing else is called
#guard match plan with
  | .ok p => p.main.size == 16 && p.main.all fun | .call s _ => s == "qlean_own_write" | .fail .. => false | _ => true
  | .error _ => false

end LeetQ.Rel.Lang.TestNative

open LeetQ.Rel.Lang.Plan LeetQ.Rel.Lang.TestNative in
/-- The `relc-1a` exe (`lakefile.lean`): `c FILE`, `lean DIR`, `plan DIR`, as the module doc says. -/
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["c", file] => IO.FS.writeFile file (← IO.ofExcept (plan >>= relc abiOf))
    | ["lean", dir] =>
      unless native1a.x.ok do throw (IO.userError "x: an op ran out of capacity")
      writeRel (System.FilePath.mk dir / "out").toString native1a.x.rel
    | ["plan", dir] => IO.Process.setCurrentDir dir; discard <| (← IO.ofExcept plan).run abiOf
    | _ => throw (IO.userError "usage: relc-1a c FILE | lean DIR | plan DIR")
    pure 0
  catch e => IO.eprintln e; pure 1
