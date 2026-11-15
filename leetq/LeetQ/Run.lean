/-! # What `rel_program` runs at elaboration time

The modules under `LeetQ/Run/`: the expander (`Lang.Expand`), the code it emits (`Lang.Gen`) and every module they
import, none of them a proof. The lakefile precompiles exactly this directory. This module is the library's root,
so its shared library loads as a Lean plugin, after qlean's plugin whose symbols it needs; it imports nothing. -/
