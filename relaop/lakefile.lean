import Lake
open Lake DSL

/-!
The Rel→AOP bridge: the only package that imports both `rel` and freyd's `AOP`, so neither lakefile names the other.
`../../rel` is rel's checkout beside freyd's; a freyd worktree sits deeper, and `lake -K rel=<dir>` points it there.
-/

package relaop where
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩]

require freyd from ".."
require rel from (get_config? rel |>.getD "../../rel")

@[default_target]
lean_lib RelAop where
  globs := #[.submodules `RelAop]
