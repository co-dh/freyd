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
  | .ok p => p.main.length == 16 && p.main.all fun | .call s _ => s == "qlean_own_write" | .fail .. => false | _ => true
  | .error _ => false

/-! Stage 1b, `Code.groupIds` (`groupIdsF`): one code per kind of lane, so every branch of its `if`s runs. -/

/-- A code's four registers, as `lit`s. -/
def codeRegs (c : Alg.Code) : Bld (Array Nat) :=
  #[Val.size c.w.toUSize, .size c.n, .size c.card.toUSize, .bytes c.b].mapM lit

/-- `groupIdsF` applied to each of `cs`; `main`'s last two registers are the last code's answer. -/
def gplan (cs : List Alg.Code) : Except String Plan := Bld.plan do
  let f ← groupIdsF
  for c in cs do discard <| apply f (← codeRegs c) 2

/-- A bitmap, bytes, longs, and ids at `2` bits (`idGroups`). -/
def codes : List Alg.Code :=
  [⟨1, 10, 2, ⟨#[0b1011001, 0b10]⟩⟩, ⟨8, 5, 256, ⟨#[3, 1, 3, 2, 1]⟩⟩,
   Alg.Code.ofLongs ⟨#[5, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0]⟩,
   ⟨2, 4, 3, ⟨#[0b10000100]⟩⟩]

/-- `Plan.run` of `gplan [c]` answers `c.groupIds`. -/
def agrees (c : Alg.Code) : IO Bool := do
  let rs ← (← IO.ofExcept (gplan [c])).run abiOf
  match rs[rs.size - 2]?, rs[rs.size - 1]? with
  | some (.bytes a), some (.bytes b) => pure (a.data == c.groupIds.1.data && b.data == c.groupIds.2.data)
  | _, _ => pure false

#eval show IO Unit from do for c in codes do unless ← agrees c do throw (IO.userError s!"groupIds plan differs at w = {c.w}")

end LeetQ.Rel.Lang.TestNative

open LeetQ.Rel.Lang.Plan LeetQ.Rel.Lang.TestNative in
/-- The `relc-1a` exe (`lakefile.lean`): `c FILE`, `lean DIR`, `plan DIR`, as the module doc says. -/
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["c", file] => IO.FS.writeFile file (← IO.ofExcept (plan >>= relc abiOf))
    | ["lean", dir] =>
      unless native1a.rel.x.ok do throw (IO.userError "x: an op ran out of capacity")
      writeRel (System.FilePath.mk dir / "out").toString native1a.rel.x.rel
    | ["plan", dir] => IO.Process.setCurrentDir dir; discard <| (← IO.ofExcept plan).run abiOf
    | ["g", file] => IO.FS.writeFile file (← IO.ofExcept (gplan codes >>= relc abiOf))
    | _ => throw (IO.userError "usage: relc-1a c FILE | lean DIR | plan DIR | g FILE")
    pure 0
  catch e => IO.eprintln e; pure 1
