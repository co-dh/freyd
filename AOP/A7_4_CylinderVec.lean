/-
  The note's §13.5.4 beads of `gen` on `Vec`, as arrows of `setCat` (§1.241: objects are types,
  arrows are functions) together with their naturality squares.  Naturality is STRICT here because
  every bead is a function; the list versions in `AOP.A7_4_CylinderBeads` are relations, hence lax.
-/
module

public import Freyd.S1_18
public import Freyd.S1_241

namespace Freyd.Alg

open Freyd

variable {n m p : Nat} {A B X Y : Type}

/-- **`Vec(n) : X ↦ X[n]`**, the note's vector functor: an object goes to its `n`-tuples and a
    function acts on every entry. -/
@[expose] public def Vec (n : Nat) : Functor (Type) (Type) where
  obj X := Fin n → X
  map f := fun v => f ∘ v
  map_id _ := rfl
  map_comp _ _ := rfl

namespace Vec

/-! ## The beads -/

/-- **`moves : X[n]⟶X[3][n]`** — every entry beside its two neighbours, the ends glued:
    `moves(5 6 7 8) = (6 7 8 5) (5 6 7 8) (8 5 6 7)`, the input moved down, unmoved and up. -/
@[expose] public def moves : (Vec n).obj X ⟶ (Vec 3).obj ((Vec n).obj X) :=
  fun v k i =>
    -- One formula for the three rows: `k = 0,1,2` reads entry `i+1`, `i`, `i-1` mod `n`.  `n > 0`
    -- comes from `i : Fin n` existing, so no `NeZero` hypothesis is needed.
    v ⟨(i.val + n + 1 - k.val) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

/-- **`trans : X[3][n]⟶X[n][3]`** — the transpose: entry `i` of row `k` becomes entry `k` of
    row `i`. -/
@[expose] public def trans : (Vec 3).obj ((Vec n).obj X) ⟶ (Vec n).obj ((Vec 3).obj X) :=
  fun v i k => v k i

/-- **`concat : X[3][p]⟶X[3p]`** — the three rows laid end to end, row-major: entry `i` of the
    result is entry `i % p` of row `i / p`. -/
@[expose] public def concat : (Vec 3).obj ((Vec p).obj X) ⟶ (Vec (3 * p)).obj X :=
  fun v i =>
    -- Core has no `Fin.divNat`/`Fin.modNat`; both bounds and `p > 0` come from `i.isLt`.
    have hi : i.val < 3 * p := i.isLt
    have hp : 0 < p := by omega
    v ⟨i.val / p, Nat.div_lt_of_lt_mul (by omega)⟩ ⟨i.val % p, Nat.mod_lt _ hp⟩

/-- **`zip : F(A[n],X[n])⟶F(A,X)[n]`** at `F(A,X) = A×X` — a tuple of `A`s and a tuple of `X`s
    become the tuple of pairs taken entry by entry. -/
@[expose] public def zip : (Vec n).obj A × (Vec n).obj X ⟶ (Vec n).obj (A × X) :=
  fun (v, w) i => (v i, w i)

/-- **`cp : A×X[k]⟶(A×X)[k]`** — the square paired with each candidate: the one `A` is copied
    into every entry. -/
@[expose] public def cp {k : Nat} : A × (Vec k).obj X ⟶ (Vec k).obj (A × X) :=
  fun (a, w) i => (a, w i)

/-- **`cons : X×X[m]⟶X[m+1]`** — a head in front of a tuple.  The note DEFINES `A[m+1] ≜ A×A[m]`,
    so there `cons = 𝟙`; in Lean the two sides are only isomorphic and `cons` is that iso. -/
@[expose] public def cons : X × (Vec m).obj X ⟶ (Vec (m + 1)).obj X :=
  fun (a, v) => Fin.cases a v

/-- **`uncons : X[m+1]⟶X×X[m]`** — the head split off from the tail, the inverse of `cons`. -/
@[expose] public def uncons : (Vec (m + 1)).obj X ⟶ X × (Vec m).obj X :=
  fun w => (w 0, fun i => w i.succ)

/-- **`cons uncons = 𝟙`** — splitting off a head just put on returns the pair unchanged. -/
public theorem cons_uncons : (cons : X × (Vec m).obj X ⟶ _) ≫ uncons = 𝟙 _ := rfl

/-- **`uncons cons = 𝟙`** — putting back the head just split off returns the tuple unchanged; the
    entries are checked one `Fin.cases` apart. -/
public theorem uncons_cons : (uncons : (Vec (m + 1)).obj X ⟶ _) ≫ cons = 𝟙 _ := by
  funext w i
  induction i using Fin.cases with
  | zero => rfl
  | succ j => rfl

/-! ## Naturality -/

/-- **`moves` is natural**: `Vec(n)(f) moves = moves Vec(3)(Vec(n)(f))`.  Rearranging entries and
    acting on every entry commute, because the rearrangement does not look at the entries. -/
public theorem moves_natural (f : X ⟶ Y) :
    (Vec n).map f ≫ moves = moves ≫ (Vec 3).map ((Vec n).map f) := rfl

/-- **`trans` is natural**: `Vec(3)(Vec(n)(f)) trans = trans Vec(n)(Vec(3)(f))`.  Transposing moves
    entries between rows without touching them. -/
public theorem trans_natural (f : X ⟶ Y) :
    (Vec 3).map ((Vec n).map f) ≫ trans = trans ≫ (Vec n).map ((Vec 3).map f) := rfl

/-- **`concat` is natural**: `Vec(3)(Vec(p)(f)) concat = concat Vec(3p)(f)`.  The index arithmetic
    that flattens the rows is independent of the entries. -/
public theorem concat_natural (f : X ⟶ Y) :
    (Vec 3).map ((Vec p).map f) ≫ concat = concat ≫ (Vec (3 * p)).map f := rfl

/-- **`zip` is natural**: `F(Vec(n)(f),Vec(n)(g)) zip = zip Vec(n)(F(f,g))`.  Entry `i` of both
    sides is `(f(v i), g(w i))`. -/
public theorem zip_natural (f : A ⟶ B) (g : X ⟶ Y) :
    Prod.map ((Vec n).map f) ((Vec n).map g) ≫ zip = zip ≫ (Vec n).map (Prod.map f g) := rfl

/-- **`cp` is natural**: `F(f,Vec(k)(g)) cp = cp Vec(k)(F(f,g))`.  The copied `A` meets `f` once
    per entry either way. -/
public theorem cp_natural {k : Nat} (f : A ⟶ B) (g : X ⟶ Y) :
    Prod.map f ((Vec k).map g) ≫ cp = cp ≫ (Vec k).map (Prod.map f g) := rfl

/-- **`cons` is natural**: `F(f,Vec(m)(f)) cons = cons Vec(m+1)(f)`.  Entry `0` is the head and
    entry `j+1` the tail's entry `j`, and `f` acts on each. -/
public theorem cons_natural (f : X ⟶ Y) :
    Prod.map f ((Vec m).map f) ≫ cons = cons ≫ (Vec (m + 1)).map f := by
  funext q i
  induction i using Fin.cases with
  | zero => rfl
  | succ j => rfl

end Vec

end Freyd.Alg
