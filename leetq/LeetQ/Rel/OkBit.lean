/-
  The simp set `okbit`: the lemmas reading a twin's run-time bit as its read-back theorem's premises (a `fitsN` bit
  as `PickFits`, a codes bit as `CodesFit`/`oneOK`, `&&` and `decide` as `∧` and the decided Prop). Its own module
  because a simp attribute is usable only in the modules importing the one that registers it.
-/
import Lean

register_simp_attr okbit
