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

/-- What `rel_program` runs at elaboration time, `LeetQ.Run`: the expander, the code it emits and their imports,
    none of them a proof module. -/
@[default_target]
lean_lib LeetQRun where
  -- one root named like the lib makes its shared library a plugin, loaded after qlean's, whose symbols it needs
  roots := #[`LeetQ.Run]
  libName := "leetq_LeetQ_Run"
  globs := #[.andSubmodules `LeetQ.Run]
  -- two libs, disjoint by directory: a precompiled module puts every module it imports into native code, so
  -- only the run path is precompiled, and an edit to a proof rebuilds no shared library
  precompileModules := true

/-- The proofs, the prelude and the programs (`LeetQ.Rel.Programs`), interpreted; they call `LeetQRun`'s native
    code, and `lake build LeetQ` builds it too, since they import it. -/
@[default_target]
lean_lib LeetQ where
  globs := #[.submodules `LeetQ.Rel]

-- The only lib that imports AOP: the Rel→AOP bridge. `LeetQ` and `LeetQRun` stay AOP-free,
-- and `LeetQ.Rel` no longer claims these modules, so AOP is built only when this lib is.
@[default_target]
lean_lib LeetQAop where
  globs := #[.submodules `LeetQ.Aop]
