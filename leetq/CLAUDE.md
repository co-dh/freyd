## What RelRep is
- The core: a relation is a pair of typed arrays of one length, `Rel k v = {n, key : Arr k n, val : Arr v n}`.
  An `Arr` is a qlean `Column` of one `QAtomicType`, `general` (q's type 0, each element boxed) included. The key
  is a plain `Arr`, as in q.
- The algebra on it: composition `≫`, converse `°`, `∩`, `∪`, `⊑`, `𝟘`, `⊤`, `𝟙`, left/right/symmetric
  division, `Λ` and `∋`, pair `⟨R,S⟩` and product, sum `[R,S]`, fold `⦇e,f⦈`, hylo, functors `F(R)`, natural
  and lax natural transformations (`∋`, `est`, `thin`), maps on positions, and `enum` (a set of positions as the list in
  position order, the one place row order enters).

## Goal
Use RelRep to implement k's operations, to show that the relation algebra is concise and powerful:
- Every k verb's spec is built only from that algebra.
- The qlean kernel that executes the verb is an optimisation, tied to the spec by a `kernel = spec` theorem.
- Execution is compute-on-compression (qlean's encoded columns), so it is also efficient: memory IO is the
  speed limit.
- No serialization: the in-memory structure is the on-disk structure, so loading an array is an mmap.
