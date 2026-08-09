module

/-
  A mathlib-free hash map / hash set on `Int` keys, backed by an `Array` of collision
  buckets (each bucket a `List (Int × V)`).  Pure Lean 4 core (`Array`, `Int`, `List`);
  NO `import Mathlib` / `Std` / `Batteries`, NO `require`.

  Complexity (INFORMAL — not proven in Lean): with a good spread of `k.emod size`, each
  `find?` / `insert` touches one bucket of expected `O(1)` length, so both are `O(1)`
  EXPECTED.  Worst case (all keys colliding into one bucket) is `O(n)` per op — the honest
  bound for a chaining hash map.  The bucket count is fixed at construction (NO resize), so
  the load factor is not bounded and the proofs stay about a single `Array.set`.

  This backs the `O(n)`-expected re-derivations of Two Sum / Contains Duplicate /
  Longest Consecutive / Isomorphic Strings.

  Proven here (functional behaviour only):
    find?_mkHashMap, find?_insert_self, find?_insert_other, contains_iff, and the
    hash-set mirror mem_mk / mem_insert_self / mem_insert_other.
-/

namespace Freyd.HashMap

/-- An `Array`-of-buckets hash map with `Int` keys.  `hpos` fixes `size ≥ 1` so the hash
    index is always in range (no mod-by-zero, no resize). -/
public structure AHashMap (V : Type) where
  buckets : Array (List (Int × V))
  hpos : 0 < buckets.size

variable {V : Type}

/-- Empty map with `n+1` buckets (the `+1` guarantees `size ≥ 1`). -/
@[expose] public def mkHashMap (V : Type) (n : Nat) : AHashMap V :=
  ⟨Array.replicate (n + 1) [], by rw [Array.size_replicate]; exact Nat.succ_pos n⟩

/-- Bucket index of a key: `k mod size`, nonneg because `Int.emod` is nonneg for a positive
    modulus and `size ≥ 1`. -/
@[expose] public def hash (m : AHashMap V) (k : Int) : Nat := (k.emod (m.buckets.size : Int)).toNat

public theorem hash_lt (m : AHashMap V) (k : Int) : hash m k < m.buckets.size := by
  have hpos : (0 : Int) < (m.buckets.size : Int) := by have := m.hpos; omega
  have hne : (m.buckets.size : Int) ≠ 0 := by have := m.hpos; omega
  have h1 : 0 ≤ k.emod (m.buckets.size : Int) := Int.emod_nonneg k hne
  have h2 : k.emod (m.buckets.size : Int) < (m.buckets.size : Int) := Int.emod_lt_of_pos k hpos
  unfold hash
  omega

/-- Look up `k`: scan its bucket front-to-back for the first `(k, _)` pair (newest wins,
    since `insert` prepends). -/
@[expose] public def find? (m : AHashMap V) (k : Int) : Option V :=
  ((m.buckets[hash m k]?).getD []).find? (fun p => p.1 == k) |>.map (fun p => p.2)

/-- Insert `(k, v)`: prepend it to `k`'s bucket (last-write-wins; older `(k, _)` entries are
    shadowed, never scanned). -/
@[expose] public def insert (m : AHashMap V) (k : Int) (v : V) : AHashMap V :=
  ⟨m.buckets.set (hash m k) ((k, v) :: (m.buckets[hash m k]?).getD []) (hash_lt m k),
   by rw [Array.size_set]; exact m.hpos⟩

@[expose] public def contains (m : AHashMap V) (k : Int) : Bool := (find? m k).isSome

/-! ### Behaviour lemmas -/

/-- `insert` keeps the bucket count, hence keeps every hash index. -/
public theorem hash_insert (m : AHashMap V) (k : Int) (v : V) (k' : Int) :
    hash (insert m k v) k' = hash m k' := by
  unfold hash insert
  rw [Array.size_set]

/-- `(insert m k v).buckets` is `m.buckets` with `k`'s bucket replaced by the prepended list.
    Definitional; stated so it can be used as a rewrite. -/
public theorem insert_buckets (m : AHashMap V) (k : Int) (v : V) :
    (insert m k v).buckets
      = m.buckets.set (hash m k) ((k, v) :: (m.buckets[hash m k]?).getD []) (hash_lt m k) :=
  rfl

public theorem find?_mkHashMap (n : Nat) (k : Int) : find? (mkHashMap V n) k = none := by
  unfold find?
  rw [Array.getElem?_eq_getElem (hash_lt (mkHashMap V n) k)]
  simp [mkHashMap, Array.getElem_replicate]

public theorem find?_insert_self (m : AHashMap V) (k : Int) (v : V) :
    find? (insert m k v) k = some v := by
  unfold find?
  -- `beq_iff_eq` (not `beq_self_eq_true`): the latter's `ReflBEq Int` instance drags in
  -- `Classical.choice`; `beq_iff_eq` goes through `LawfulBEq` and stays constructive.
  rw [hash_insert, insert_buckets, Array.getElem?_set (hash_lt m k), if_pos rfl, Option.getD_some,
      List.find?_cons, show ((k, v).fst == k) = true from beq_iff_eq.mpr rfl]
  rfl

public theorem find?_insert_other (m : AHashMap V) (k : Int) (v : V) (k' : Int) (h : k' ≠ k) :
    find? (insert m k v) k' = find? m k' := by
  unfold find?
  rw [hash_insert, insert_buckets, Array.getElem?_set (hash_lt m k)]
  split
  · rename_i heq
    simp only [Option.getD_some]
    rw [List.find?_cons_of_neg (by simp only [beq_iff_eq]; exact fun e => h e.symm), heq]
  · rfl

theorem contains_iff (m : AHashMap V) (k : Int) :
    contains m k = true ↔ ∃ v, find? m k = some v := by
  unfold contains
  exact Option.isSome_iff_exists

/-! ### Hash set (chaining map with trivial values) -/

@[expose] public abbrev AHashSet := AHashMap Unit

@[expose] public def insert' (m : AHashSet) (k : Int) : AHashSet := insert m k ()

@[expose] public def mem (m : AHashSet) (k : Int) : Bool := contains m k

public theorem mem_mk (n : Nat) (k : Int) : mem (mkHashMap Unit n) k = false := by
  unfold mem contains
  rw [find?_mkHashMap]
  rfl

public theorem mem_insert_self (m : AHashSet) (k : Int) : mem (insert' m k) k = true := by
  unfold mem insert' contains
  rw [find?_insert_self]
  rfl

public theorem mem_insert_other (m : AHashSet) (k k' : Int) (h : k' ≠ k) :
    mem (insert' m k) k' = mem m k' := by
  unfold mem insert' contains
  rw [find?_insert_other _ _ _ _ h]

/-! ### Sanity checks -/

-- a 4-bucket map; keys 3 and 7 both hash to bucket 3 (collision), 5 to bucket 1.
private def t : AHashMap Nat := insert (insert (insert (mkHashMap Nat 3) 3 30) 7 70) 5 50

example : find? t 3 = some 30 := by decide
example : find? t 7 = some 70 := by decide
example : find? t 5 = some 50 := by decide
example : find? t 4 = none := by decide
-- last-write-wins on the same key
example : find? (insert (insert (mkHashMap Nat 3) 3 30) 3 99) 3 = some 99 := by decide
-- negative keys hash fine (emod is nonneg)
example : find? (insert (mkHashMap Nat 3) (-7) 1) (-7) = some 1 := by decide

private def s : AHashSet := insert' (insert' (mkHashMap Unit 3) 3) 7
example : mem s 3 = true := by decide
example : mem s 4 = false := by decide

#eval find? t 3   -- some 30
#eval mem s 7     -- true

end Freyd.HashMap
