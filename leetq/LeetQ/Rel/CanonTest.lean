/-
  Canonical form at run time: every `CRel` op answers its rows sorted by `Obj.lt` on `(key, val)` with no row
  twice, so equal relations are equal data. The laws are proved in `CRelRel` (`comp_assoc`, `id_comp`, `comp_id`,
  `inter_self`, `union_self`); these checks run them on tables.
-/
import LeetQ.Run.CRelRelDef

namespace LeetQ.Rel.CanonTest

open LeetQ.Rel

/-- A table of pairs, through `ofC` like every op's answer. -/
def mk (ps : List (Int64 × Int64)) : CRel .long .long := CRel.ofC (Alg.ofPairs ps, true)

/-- A pseudo-random relation on `0..m-1` with `n` pairs. -/
def rnd (seed n m : Nat) : List (Int64 × Int64) :=
  (List.range n).map fun i => let x := (seed * 7919 + i * 104729) % 1000003
    (Int64.ofNat (x % m), Int64.ofNat ((x / m) % m))

def assoc (R S T : CRel .long .long) : Bool := ((R.comp S).comp T).rel.toList == (R.comp (S.comp T)).rel.toList

#guard assoc (mk [(1,10),(2,20),(1,20)]) (mk [(10,5),(20,5),(20,6)]) (mk [(5,100),(6,100),(5,200)])
#guard assoc (mk (rnd 1 40 12)) (mk (rnd 2 40 12)) (mk (rnd 3 40 12))
#guard assoc (mk (rnd 4 300 50)) (mk (rnd 5 300 50)) (mk (rnd 6 300 50))

/-- `𝟙` on `{1, 2}`: the coreflexive on the keys of `[(1,1),(2,2)]`. -/
def I : CRel .long .long := CRel.distinctCorefl .long (Alg.ofPairs [(1,1),(2,2)]).key
def R : CRel .long .long := mk [(2,7),(1,7),(2,8)]

#guard R.rel.toList == [(1,7),(2,7),(2,8)]
#guard (I.comp R).rel.toList == R.rel.toList
#guard (R.comp (CRel.distinctCorefl .long (Alg.ofPairs [(7,7),(8,8)]).key)).rel.toList == R.rel.toList
#guard (R.union R).rel.toList == R.rel.toList
#guard (R.inter R).rel.toList == R.rel.toList
-- `compC` alone repeats `(1,100)` three times; through `ofC` it is one row
#guard ((mk [(1,10),(1,20),(1,30)]).comp (mk [(10,100),(20,100),(30,100)])).rel.toList == [(1,100)]
-- negative keys sort below positive ones: `Obj.lt` is the atom's own order
#guard (mk [(3,0),(-1,0),(0,0)]).rel.toList == [(-1,0),(0,0),(3,0)]

end LeetQ.Rel.CanonTest
