import Lake
open Lake DSL

/-!
A package of its own so that neither freyd's nor qlean's lakefile names the other: freyd's default
`lake build` never elaborates qlean's lakefile, and `Freyd/`/`AOP/` stay dependency-free. Path
dependencies build in their own directories, so freyd's and qlean's `.lake/build` are reused.

Lean rather than TOML for one reason: qlean's path. `../../qlean` is qlean's checkout beside freyd's;
a freyd worktree sits deeper, and `lake -K qlean=<dir>` points it there instead.
-/

package leetq where
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩]

require freyd from ".."
require qlean from (get_config? qlean |>.getD "../../qlean")

@[default_target]
lean_lib LeetQ where
  globs := #[.submodules `LeetQ]

/-- `doc/qrel-total-plan.md` §6's end check: red by design while an offender remains, so not a default target. -/
lean_lib Check

/-- `bench <op> <n>…`: the Rel operators timed. -/
lean_exe bench where
  root := `Bench.Main
