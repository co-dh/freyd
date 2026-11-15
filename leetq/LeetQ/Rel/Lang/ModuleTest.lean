import LeetQ.Rel.Programs.CSP

/-! Rel's module system (`doc/rel-module-design.md` §4): a program's definitions are Lean constants `n.x`, a name
    not the program's own is resolved by Lean (`open`, the namespace, `m.x`) and must be a registered Rel
    definition, and which constants exist never changes how a run of letters is cut. -/

namespace LeetQ.Rel.Programs

open Lean Elab Command LeetQ.Rel.Lang

/-- The `print` terms of the statements `src` read here (the current namespace and `open`s), each composite and
    infix term in parentheses; nothing elaborated. -/
elab "#rel_read " s:str : command => do
  let txt := "rel_program t where " ++ s.getString
  match Parser.runParserCategory (← getEnv) `command txt with
  | .error e => logInfo e
  | .ok stx => match Embed.program (FileMap.ofString txt) (← Embed.scopeHere) stx[4].getArgs with
    | .ok (ds, _) => ds.forM fun | .print _ e => logInfo (e.render 0 true) | _ => pure ()
    | .error e => logInfo s!"{e}"

/-- Fails unless the constant `c` exists. -/
elab "#has " c:ident : command => do
  discard <| resolveGlobalConstNoOverload c

open LeetQ.Rel.Programs.prelude in
rel_program mh where
    obj A = 0…2
    f : A ⟶ A ≜ succ
    peer : A ⟶ A ≜ ≠
    ≺ : α ⟶ α ≜ <

open LeetQ.Rel.Programs.prelude in
rel_program mk where
    obj A = 0…2
    peer : A ⟶ A ≜ 𝟙

/-! Each definition is the constant `n.x`; a symbol's is `n.«≠»`. -/
#has csp.AC3
#has mh.f
#has mh.«≺»
#has prelude.«≠»

/-! Qualified names do not collide: a program defines its own `AC3` beside `csp.AC3` and uses both. -/
open LeetQ.Rel.Programs.prelude in
rel_program qual where
    obj A = 0…2
    obj D = 1…3
    s₀ : A ⟶ D ≜ ⊤
    AC3(X : A ⟶ D) : A ⟶ D ≜ X
    s : A ⟶ D ≜ csp.AC3(≠, ≠, s₀)
    t : A ⟶ D ≜ AC3(s₀)
    check s ⊑ t
#guard qual.ok

/-! Selective: `open csp (AC3)` brings `AC3`; without it `AC3` is unknown. -/
section
open LeetQ.Rel.Programs.prelude
open csp (AC3)
rel_program sel where
    obj A = 0…2
    s : A ⟶ A ≜ AC3(≠, ≠, 𝟙)
#guard sel.ok
end

/-- error: line 70, col 17: expected ')' -/
#guard_msgs in
open LeetQ.Rel.Programs.prelude in
rel_program selNo where
    obj A = 0…2
    s : A ⟶ A ≜ AC3(≠, ≠, 𝟙)

/-! Two `open`s that give one name: ambiguous. -/
/-- error: line 78, col 17: ambiguous name `peer`: it is [LeetQ.Rel.Programs.mh.peer, LeetQ.Rel.Programs.mk.peer] -/
#guard_msgs in
open mh mk in
rel_program amb where
    obj A = 0…2
    s : A ⟶ A ≜ peer

/-! Without `open prelude`, `≠` is unknown; `prelude.«≠»` exists (above). -/
/-- error: line 85, col 17: unknown name '≠' -/
#guard_msgs in
rel_program noPrelude where
    obj A = 0…2
    s : A ⟶ A ≜ ≠

/-! Closedness: a Lean constant that is not a Rel definition is an error, qualified or opened, whatever its
    type; a kernel name stays the kernel's. -/
/-- error: line 93, col 17: `Nat.add` is not a Rel definition: Lean resolves it to [Nat.add] -/
#guard_msgs in
rel_program closedQ where
    obj A = 0…2
    s : A ⟶ A ≜ Nat.add

/-- error: line 100, col 17: unknown name 'add' -/
#guard_msgs in
open Nat in
rel_program closedOpen where
    obj A = 0…2
    s : A ⟶ A ≜ add

/-- info: succ -/
#guard_msgs in
open Nat in
#rel_read "print succ"

def fake : CRel .long .long := default

/-- error: line 113, col 17: `fake` is not a Rel definition: Lean resolves it to [LeetQ.Rel.Programs.fake] -/
#guard_msgs in
rel_program closedType where
    obj A = 0…2
    s : A ⟶ A ≜ fake

/-! Cutting a run of letters reads only the program's own names, the kernel's and the Rel definitions in scope:
    `open Nat` (which has `Nat.add`) leaves `add` the program's `ad` then `d`. -/
/-- info: (ad d) -/
#guard_msgs in
#rel_read "obj A = 0…2\nad : A ⟶ A ≜ 𝟙\nd : A ⟶ A ≜ 𝟙\nprint add"

/-- info: (ad d) -/
#guard_msgs in
open Nat in
#rel_read "obj A = 0…2\nad : A ⟶ A ≜ 𝟙\nd : A ⟶ A ≜ 𝟙\nprint add"

/-! Symbol names: `open mh («≺»)` makes `≺` readable; `mh.≺` reads unopened. -/
section
open mh («≺»)
/-- info: ≺ -/
#guard_msgs in
#rel_read "print ≺"
end

/-- info: mh.≺ -/
#guard_msgs in
#rel_read "print mh.≺"

/-! A run of letters with a qualified name in it: `mh.fpeer` is `mh.f` then `peer`, `Rmh.f` is `R` then `mh.f`. -/
/--
info: (mh.f peer)
---
info: (R mh.f)
-/
#guard_msgs in
#rel_read "obj A = 0…2\npeer : A ⟶ A ≜ 𝟙\nR : A ⟶ A ≜ 𝟙\nprint mh.fpeer\nprint Rmh.f"

end LeetQ.Rel.Programs
