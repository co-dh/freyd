import LeetQ.Run.Algebra
import LeetQ.Run.Lang.Syntax

/-! The core term `Tm` of the Rel language, indexed by its source, target and whether it runs on demand; the
    elaborator (`Elab`) builds it and `Expand` reads it (`doc/rel-lang-design.md` §a, §e). -/

namespace LeetQ.Rel.Lang

open LeetQ.Rel LeetQ.Rel.Alg

/-! ### The core term -/

/-- A core term `A ⟶ B` over `Alg`. `d` says it runs on DEMAND (§a): its value is read only at the keys the
    coreflexive its left context supplies. A term with `d = false` needs no keys: a closed term. -/
inductive Tm : Obj → Obj → Bool → Type where
  | val {A B : Obj} (R : Rel A B) : Tm A B false
  | uni {A : Obj} {m : USize} (U : Vals A m) : Tm A A false
  | zero {A B : Obj} : Tm A B false
  | id {A : Obj} : Tm A A true
  /-- `⊤` onto the values of the closed coreflexive `V`. -/
  | top {A B : Obj} (V : Tm B B false) : Tm A B true
  | outl {A B : Obj} : Tm (.prod A B) A true
  | outr {A B : Obj} : Tm (.prod A B) B true
  | inl {A B : Obj} : Tm A (.sum A B) true
  | inr {A B : Obj} : Tm B (.sum A B) true
  | comp {A B C : Obj} {d e : Bool} (R : Tm A B d) (S : Tm B C e) : Tm A C d
  | conv {A B : Obj} (R : Tm A B false) : Tm B A false
  | meet {A B : Obj} {d e : Bool} (R : Tm A B d) (S : Tm A B e) : Tm A B (d || e)
  | join {A B : Obj} {d e : Bool} (R : Tm A B d) (S : Tm A B e) : Tm A B (d || e)
  | diff {A B : Obj} {d e : Bool} (R : Tm A B d) (S : Tm A B e) : Tm A B (d || e)
  | dom {A B : Obj} {d : Bool} (R : Tm A B d) : Tm A A d
  | ran {A B : Obj} (R : Tm A B false) : Tm B B false
  | ldiv {A B C : Obj} (R : Tm A B false) (S : Tm A C false) (UB : Tm B B false) (UC : Tm C C false) : Tm B C false
  | rdiv {A B C : Obj} (R : Tm A C false) (S : Tm B C false) (UA : Tm A A false) (UB : Tm B B false) : Tm A B false
  | pair {A B C : Obj} {d e : Bool} (R : Tm A B d) (S : Tm A C e) : Tm A (.prod B C) (d || e)
  | prod {A B C D : Obj} (R : Tm A B false) (S : Tm C D false) : Tm (.prod A C) (.prod B D) false
  | junc {A B C : Obj} (R : Tm A C false) (S : Tm B C false) : Tm (.sum A B) C false
  /-- `[R,S]` on the keys in demand, a part with no universe to be read whole on: each part run on the values of
      its side the demand holds. -/
  | juncD {A B C : Obj} {d e : Bool} (R : Tm A C d) (S : Tm B C e) : Tm (.sum A B) C true
  /-- `Λ(R)`, a map: total on the keys in demand, `[]` where `R` has no image, so it always runs on demand and a
      closed use reads its source's universe (`closeRes`). -/
  | lam {A B : Obj} {d : Bool} (R : Tm A B d) : Tm A (.arr B) true
  | E {A B : Obj} {d : Bool} (R : Tm A B d) : Tm (.arr A) (.arr B) true
  | map {A B : Obj} {d : Bool} (R : Tm A B d) : Tm (.arr A) (.arr B) true
  /-- An operator that takes an order `Q : B ⟶ B` (or a coreflexive `p`) holds it as its pair test
      `τ(Q) : B×B ⟶ B×B` (§a), run on demand on the pairs the operator compares. -/
  | est {B : Obj} (Q : Tm (.prod B B) (.prod B B) true) : Tm (.arr B) B true
  | thin {B : Obj} (Q : Tm (.prod B B) (.prod B B) true) : Tm (.arr B) (.arr B) true
  | nil {A B : Obj} : Tm A (.arr B) true
  /-- The row `r` of `prims` at `A ⟶ B`, an instance of its constant's type; its relations given by `arg`. -/
  | prim {A B : Obj} (r : Prim) : Tm A B true
  /-- `at(k)`, the element at position `k` from `0`, on the arrays in demand. -/
  | atPos {B : Obj} (k : Nat) : Tm (.arr B) B true
  /-- The prelude's `perm`, kept as its own converse (`convTm`): the one converse rule the language has for a
      definition, because `perm° = perm` is a theorem it cannot derive from the fold `perm` is. -/
  | own {A : Obj} {d : Bool} (R : Tm A A d) : Tm A A d
  /-- `succ`, the kernel's value verb `k` (`plus`, `times`, …), `≤`, `<` on the number universe `U`: a declared
      object's (`uni`), or the one a constant is given for an object variable (`var`). -/
  | succ (U : Tm .long .long false) : Tm .long .long true
  | arith (k : UInt8) (U : Tm .long .long false) : Tm (.prod .long .long) .long true
  | leq (U : Tm .long .long false) : Tm .long .long false
  | lt (U : Tm .long .long false) : Tm .long .long false
  /-- `⦇e,S⦈` on the arrays in demand, `S` run on the pairs each round meets. -/
  | fold {E V : Obj} {d : Bool} (e : Tm V V false) (S : Tm (.prod E V) V d) : Tm (.arr E) V true
  /-- `R`, closed, numbered `k` among the expansion's sub-terms (`Expand.number`): its code is built once
      (`Expand.code`). -/
  | share {A B : Obj} {d : Bool} (k : Nat) (R : Tm A B d) : Tm A B d
  /-- `⦇e,S⦈` given a family (§e), on the pairs (key, array) in demand: one fold with carrier `I×V`, seeded at
      each key by the fibre of `e` there, its step `S` given `(x,(i,v))` and carrying the key `i`. -/
  | foldI {I E V : Obj} {d d' : Bool} (e : Tm I (.prod V V) d) (S : Tm (.prod E (.prod I V)) (.prod I V) d') :
      Tm (.prod I (.arr E)) V true
  /-- `Rᴵ`, the family `R : I ⟶ A×B` as one relation of the key and the source, on the pairs (key, source) in
      demand: `R` at their keys, each row `(i,(a,b))` re-keyed as `((i,a),b)`, then joined with the pairs. -/
  | flat {I A B : Obj} {d : Bool} (R : Tm I (.prod A B) d) : Tm (.prod I A) B true
  /-- The variable `k` of the fixed point that binds it: its value in the round being run; or a constant's
      parameter, on the keys in demand when its argument is a pair test (`Form`). -/
  | var {A B : Obj} {d : Bool} (k : Nat) : Tm A B d
  /-- The constant `c` a parametric definition was elaborated once to, before its arguments (`arg`): called, its
      body not expanded; its plan runs on the keys in demand when `d`. `os`: the objects of the object variables it
      is generic over; `cv`: its converse's constant and demand bit, when its body has a converse (`convTm`). -/
  | call {A B : Obj} (d : Bool) (c : Lean.Name) (os : List Obj) (cv : Option (Lean.Name × Bool)) : Tm A B d
  /-- `f` given one more argument `x`: a relation, a pair test, or the universe of one of its object variables. -/
  | arg {A B C D : Obj} {d e : Bool} (f : Tm A B d) (x : Tm C D e) : Tm A B d
  /-- `νX : φ`, `X` the variable `k`: rounds of `body` from `S`, the conjuncts of `φ` without `X`, down to the
      greatest fixed point. -/
  | nu {A B : Obj} (k : Nat) (S body : Tm A B false) : Tm A B false
  /-- `μX : φ`: rounds of `body` from `𝟘` up to the least fixed point, at most `cap`; `what` names the `μ` in the
      failure a run that reaches `cap` first reports. -/
  | mu {A B : Obj} (k : Nat) (what : String) (cap : Nat) (body : Tm A B false) : Tm A B false
  /-- `refold(c, S)` = `μX : c G(X) S`, `X` the variable `k`, on the keys in demand: bottom-up over the nodes `ch`
      (`c` then `G`'s membership) reaches from them, each node's value `body` run once its children have theirs;
      `what` names the coalgebra `c`, where the failure a cycle of `ch` reports is. -/
  | refold {A B : Obj} {d e : Bool} (k : Nat) (what : String) (ch : Tm A A d) (body : Tm A B e) : Tm A B true

/-- A built term with its objects. -/
abbrev Res := (A : Obj) × (B : Obj) × (d : Bool) × Tm A B d

end LeetQ.Rel.Lang
