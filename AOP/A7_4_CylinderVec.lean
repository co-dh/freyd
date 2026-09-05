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

/-- **`concat : X[j][p]⟶X[jp]`** — the `j` rows laid end to end, row-major: entry `i` of the
    result is entry `i % p` of row `i / p`.  `j` is `3` at every use in `gen`, but `paths`
    flattens the `n` columns too, so the row count is a parameter. -/
@[expose] public def concat {j p : Nat} : (Vec j).obj ((Vec p).obj X) ⟶ (Vec (j * p)).obj X :=
  fun v i =>
    -- Core has no `Fin.divNat`/`Fin.modNat`; both bounds and `p > 0` come from `i.isLt`.
    have hi : i.val < j * p := i.isLt
    have hp : 0 < p := Nat.pos_of_ne_zero fun h => by simp [h] at hi
    v ⟨i.val / p, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le hi (Nat.le_of_eq (Nat.mul_comm j p)))⟩
      ⟨i.val % p, Nat.mod_lt _ hp⟩

/-- Entry `i` of row `r` sits at flat index `r·p+i`, which is in range. -/
public theorem concat_lt {j p : Nat} (r : Fin j) (i : Fin p) : r.val * p + i.val < j * p :=
  calc r.val * p + i.val < r.val * p + p := Nat.add_lt_add_left i.isLt _
    _ = (r.val + 1) * p := (Nat.succ_mul r.val p).symm
    _ ≤ j * p := Nat.mul_le_mul r.isLt (Nat.le_refl p)

/-- **`concat(v)[r·p+i] = v[r][i]`** — the flattening read backwards, the one place `concat`'s
    index arithmetic is unfolded. -/
public theorem concat_mk {j p : Nat} (v : (Vec j).obj ((Vec p).obj X)) (r : Fin j) (i : Fin p) :
    concat v ⟨r.val * p + i.val, concat_lt r i⟩ = v r i := by
  have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hdiv : (r.val * p + i.val) / p = r.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp]
    have h0 : i.val / p = 0 := Nat.div_eq_of_lt i.isLt
    omega
  have hmod : (r.val * p + i.val) % p = i.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
  show v ⟨(r.val * p + i.val) / p, _⟩ ⟨(r.val * p + i.val) % p, _⟩ = v r i
  simp only [hdiv, hmod]

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

/-- **`concat` is natural**: `Vec(j)(Vec(p)(f)) concat = concat Vec(jp)(f)`.  The index arithmetic
    that flattens the rows is independent of the entries. -/
public theorem concat_natural {j : Nat} (f : X ⟶ Y) :
    (Vec j).map ((Vec p).map f) ≫ concat = concat ≫ (Vec (j * p)).map f := rfl

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

/-! ## The generator and its fold -/

/-- **`3^m`**, the number of paths through `m+1` columns from a fixed square.  Written so that
    `pow3(m+1)` IS `3·pow3(m)`, the index `concat` produces. -/
@[expose] public def pow3 : Nat → Nat
  | 0 => 1
  | m + 1 => 3 * pow3 m

/-- **`gen ≜ F(𝟙,moves trans Vec(n)(concat)) zip Vec(n)(cp Vec(3p)(cons))`** — one more column:
    each square's `p` paths are offered to its three neighbours (`moves trans`), the `3p` of them
    flattened (`concat`), and the new square put in front of each (`cp` then `cons`).
    `F(A,X) = A×X`. -/
@[expose] public def gen {n p m : Nat} :
    (Vec n).obj A × (Vec n).obj ((Vec p).obj ((Vec m).obj A))
      ⟶ (Vec n).obj ((Vec (3 * p)).obj ((Vec (m + 1)).obj A)) :=
  Prod.map id (moves ≫ trans ≫ (Vec n).map concat)
    ≫ zip ≫ (Vec n).map (cp ≫ (Vec (3 * p)).map cons)

/-- **`⦇gen⦈`** — all `3^m` paths through the `m+1` columns, per starting square.  At one column
    the only path from a square is that square (`v 0 i`); at `m+2` the fold splits off the first
    column (`uncons`) and hands the rest's paths to `gen`. -/
@[expose] public def genFold {n : Nat} {A : Type} : (m : Nat) →
    (Vec (m + 1)).obj ((Vec n).obj A)
      ⟶ (Vec n).obj ((Vec (pow3 m)).obj ((Vec (m + 1)).obj A))
  | 0 => fun v i _ _ => v 0 i
  | m + 1 => uncons ≫ Prod.map id (genFold m) ≫ gen

/-- **`α⦇gen⦈ = F(𝟙,⦇gen⦈)gen`** at `α = cons` — the fold's defining equation, which holds
    because `cons uncons = 𝟙`. -/
public theorem cons_genFold {n m : Nat} {A : Type} :
    (cons ≫ genFold (m + 1) : (Vec n).obj A × (Vec (m + 1)).obj ((Vec n).obj A) ⟶ _)
      = Prod.map id (genFold m) ≫ gen := rfl

/-- **`paths ≜ ⦇gen⦈ concat`** — the `n·3^m` paths of the whole cylinder in one row, the note's
    `A[m+1][n]⟶A[m+1][n3^m]`. -/
@[expose] public def paths {n m : Nat} {A : Type} :
    (Vec (m + 1)).obj ((Vec n).obj A)
      ⟶ (Vec (n * pow3 m)).obj ((Vec (m + 1)).obj A) :=
  genFold m ≫ concat

/-- **`gen` is natural**: acting on the squares before generating is acting on them after.  Only
    `cons` needs an argument — every other bead of `gen` is natural by `rfl`. -/
public theorem gen_natural {n p m : Nat} (f : A ⟶ B) :
    Prod.map ((Vec n).map f) ((Vec n).map ((Vec p).map ((Vec m).map f))) ≫ gen
      = gen ≫ (Vec n).map ((Vec (3 * p)).map ((Vec (m + 1)).map f)) := by
  funext q i k
  exact congrFun (cons_natural (m := m) f) (q.1 i, concat (trans (moves q.2) i) k)

/-- **`⦇gen⦈` is natural**: `Vec(m+1)(Vec(n)(f)) ⦇gen⦈ = ⦇gen⦈ Vec(n)(Vec(3^m)(Vec(m+1)(f)))`.
    The fold of a natural algebra is natural, by induction on the number of columns. -/
public theorem genFold_natural {n : Nat} (f : A ⟶ B) : ∀ m : Nat,
    (Vec (m + 1)).map ((Vec n).map f) ≫ genFold m
      = genFold m ≫ (Vec n).map ((Vec (pow3 m)).map ((Vec (m + 1)).map f))
  | 0 => rfl
  | m + 1 => by
      have ih : ∀ w, genFold m ((Vec (m + 1)).map ((Vec n).map f) w)
          = (Vec n).map ((Vec (pow3 m)).map ((Vec (m + 1)).map f)) (genFold m w) :=
        fun w => congrFun (genFold_natural f m) w
      funext q
      calc ((Vec (m + 1 + 1)).map ((Vec n).map f) ≫ genFold (m + 1)) q
          = gen ((Vec n).map f (q 0),
              genFold m ((Vec (m + 1)).map ((Vec n).map f) (fun l => q l.succ))) := rfl
        _ = gen ((Vec n).map f (q 0),
              (Vec n).map ((Vec (pow3 m)).map ((Vec (m + 1)).map f))
                (genFold m (fun l => q l.succ))) := by rw [ih]
        _ = (genFold (m + 1)
              ≫ (Vec n).map ((Vec (pow3 (m + 1))).map ((Vec (m + 1 + 1)).map f))) q :=
              congrFun (gen_natural (n := n) (p := pow3 m) (m := m + 1) f)
                (q 0, genFold m (fun l => q l.succ))

/-- The note's run `gen((1,2,3,4),([5],[6],[7],[8]))` at `n=4`, `p=1`, `m=1`: row `k` is square
    `k` in front of squares `k+1`, `k`, `k-1` of the next column — up, unmoved, down. -/
public theorem gen_run :
    ([0, 1, 2, 3] : List (Fin 4)).map (fun i => ([0, 1, 2] : List (Fin 3)).map (fun k =>
      ([0, 1] : List (Fin 2)).map (gen (n := 4) (p := 1) (m := 1)
        (fun i : Fin 4 => i.val + 1, fun (i : Fin 4) (_ _ : Fin 1) => i.val + 5) i k)))
    = [[[1, 6], [1, 5], [1, 8]], [[2, 7], [2, 6], [2, 5]],
       [[3, 8], [3, 7], [3, 6]], [[4, 5], [4, 8], [4, 7]]] := by decide

end Vec

end Freyd.Alg
