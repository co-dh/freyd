## What RelRep is
- The core: a relation is a pair of typed arrays of one length, `Rel k v = {n, key : Arr k n, val : Arr v n}`.
  An `Arr` is a qlean `Column` of one `QAtomicType`, `general` (q's type 0, each element boxed) included. The key
  is a plain `Arr`, as in q.
- `Arr` is the implementation and Lean's `List` is for proofs only: every compiled op builds and reads arrays,
  and a `List` appears only in a statement or a `#guard` (`toList`, `El`), because Lean has the lemmas for `List`
  and not for arrays. `Obj.arr` is the side whose cell is an array (`lo`, `hi` into one flat payload); it is not
  Lean's `List`.
- The algebra on it: composition `≫`, converse `°`, `∩`, `∪`, `⊑`, `𝟘`, `⊤`, `𝟙`, left/right/symmetric
  division, `Λ` and `∋`, pair `⟨R,S⟩` and product, sum `[R,S]`, fold `⦇e,f⦈`, hylo, functors `F(R)`, natural
  and lax natural transformations (`∋`, `est`, `thin`), maps on positions, and `enum` (a set of positions as the list in
  position order, the one place row order enters).

## Goal
Test how useful Rel is as a programming language, by implementing k in it:
- Every k verb is a program written in the algebra above — a composition of a few executable Rel primitives —
  and runs as written; where it cannot be written, or only awkwardly, that is the finding to record.
- Only the primitives are qlean C kernels. A fused kernel for a pattern of primitives is an optimisation, tied
  to the pattern by a theorem.
- Execution is compute-on-compression (qlean's encoded columns), so it is also efficient: memory IO is the
  speed limit.
- No serialization: the in-memory structure is the on-disk structure, so loading an array is an mmap.
