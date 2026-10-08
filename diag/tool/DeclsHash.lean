/-
  `declsHash`, alone in a module because it runs in both phases: `StringDiagram`'s `verdict_code%`
  elaborator calls it at build time (a `meta import`) and the exporter calls it at run time.
-/
module

public import Lean
public section

open Lean

namespace Freyd.StrDiag

/-- The hash of every declaration `roots` reach — a type, a definition's value, an `implemented_by`
    or `partial` body, an `initialize` action; a theorem by its statement alone — outside the
    toolchain, which the keys name by version.  A name with macro scopes (an `initialize`'s) is left
    out, since its scope moves with any edit above. -/
def declsHash (roots : Array Name) : CoreM UInt64 := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo := roots
  let mut hs : Array UInt64 := #[]
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "diag-export: {n}, reached from {roots}, names no constant"
    if let some i := env.getModuleIdxFor? n then
      if [`Init, `Std, `Lean, `Lake].contains env.header.moduleNames[i.toNat]!.getRoot then continue
    let (es, more) : Array Expr × Array Name := match ci with
      | .defnInfo d => (#[d.type, d.value], #[])
      | .opaqueInfo d => (#[d.type, d.value], #[])
      | .inductInfo d => (#[d.type], d.ctors.toArray)
      | .ctorInfo d => (#[d.type], #[d.induct])
      | c => (#[c.type], #[])
    hs := hs.push (es.foldl (fun a e => mixHash a (hash e)) (if n.hasMacroScopes then 0 else hash n))
    let impl := [Compiler.implementedByAttr.getParam? env n, some (n ++ `_unsafe_rec), getInitFnNameFor? env n]
    todo := todo ++ more ++ ((impl.filterMap id).filter env.contains).toArray
    unless ci matches .thmInfo _ do todo := todo ++ es.flatMap (·.getUsedConstants)
  return (hs.qsort (· < ·)).foldl mixHash 7

end Freyd.StrDiag
