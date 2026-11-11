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

/-- The `.rel` programs that `Parse` (the prelude) and the `Test*` modules read with `include_str`. Lake does not
trace an `include_str` file, so the library `needs` this directory: its hash enters every module's trace. -/
input_dir programs where
  text := true
  filter := .extension "rel"

/-- `needs` is per library; there is no per-module dependency, and a separate library for the readers would
own the same modules as the `LeetQ` glob, so the whole library is rebuilt on a `.rel` edit. -/
@[default_target]
lean_lib LeetQ where
  globs := #[.submodules `LeetQ]
  needs := #[programs]

/-- `rel FILE`: run a Rel program, printing each `print`. -/
lean_exe rel where
  root := `LeetQ.Rel.Lang.Main
