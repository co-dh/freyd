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
  globs := #[.submodules `LeetQ.Core, .submodules `LeetQ.Rel]

/-- Stage 1a of the native backend (`doc/rel-native-design.md` §13): `TestNative`'s `main`, which prints its plan as C
    (`relc-1a c FILE`) and writes the Lean side's column directory (`lean DIR`, `plan DIR`). -/
lean_exe «relc-1a» where
  root := `LeetQ.Rel.Lang.TestNative

/-- The C `relc-1a` prints, linked with qlean's `libqleankernel.a` and `c/rt.c` and nothing of Lean's: the static
    library contributes only the objects the program calls, and `rt.c` the runtime symbols those reach. -/
target «rel-native-1a» pkg : System.FilePath := do
  let some q ← findPackageByName? `qlean | error "rel-native-1a: the package `qlean` is not in the workspace"
  let dir := pkg.buildDir / "native"
  let inc := (← getLeanIncludeDir).toString
  let relc ← «relc-1a».fetch
  -- `relc-1a` elaborates the program, which reads the modules `lake env` puts on `LEAN_PATH` (`TestNative.planIO`)
  let env ← getAugmentedEnv
  let cJob ← relc.mapM fun exe => do
    let c := dir / "rel-native-1a.c"
    IO.FS.createDirAll dir
    let out ← IO.Process.output { cmd := exe.toString, args := #["c", c.toString], env }
    unless out.exitCode == 0 do error s!"{exe} c {c}: exit {out.exitCode}: {out.stderr}"
    return c
  let rtO ← buildO (dir / "rt.o") (← inputTextFile (q.dir / "c" / "rt.c")) #["-I", inc] #["-O2", "-fPIC"]
  let mainO ← buildO (dir / "rel-native-1a.o") cJob #["-I", inc] #["-O2"]
  let kern := q.staticLibDir / nameToStaticLib "qleankernel"
  mainO.bindM fun m => rtO.mapM fun r => do
    let exe := dir / "rel-native-1a"
    proc { cmd := "cc", args := #["-o", exe.toString, m.toString, r.toString, kern.toString, "-lm"] }
    return exe

-- The only lib that imports AOP: the Rel→AOP bridge. `LeetQ` and `LeetQRun` stay AOP-free,
-- and `LeetQ.Rel` no longer claims these modules, so AOP is built only when this lib is.
@[default_target]
lean_lib LeetQAop where
  globs := #[.submodules `LeetQ.Aop]
