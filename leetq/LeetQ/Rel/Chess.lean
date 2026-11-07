import LeetQ.Rel.Algebra

/-! Mate in one for the two-rook ladder, as relations over bitboards. A square is the long `0 … 63`
    (a1 = 0, b1 = 1, …, h8 = 63), a bitboard the long whose bit `s` says square `s`. A position is one row
    of three bitboards `(R, K, k)`: white rooks, white king, black king. A move is `(piece, from, to)`,
    the black king staying put the move `e8 → e8`. A context is a pair of moves, white's then black's;
    every position below is one row per context, computed for all contexts at once by `Ew.bitwise`. -/

namespace LeetQ.Rel.Chess

open Alg QLean

abbrev Sq : Obj := .long
abbrev BB : Obj := .long
abbrev Pc : Obj := .long
abbrev Sq2 : Obj := .prod Sq Sq
/-- `(piece, from, to)`. -/
abbrev Move : Obj := .prod Pc Sq2
/-- `(R, K, k)`. -/
abbrev Pos : Obj := .prod BB (.prod BB BB)
/-- `(white move, black move)`. -/
abbrev Ctx : Obj := .prod Move Move

/-- The piece kinds, in `Pos`'s column order. -/
def pR : Int64 := 0
def pK : Int64 := 1
def pk : Int64 := 2

/-- A literal long column; `Arr.ofPart` checks the count. -/
def col (n : Nat) (xs : List Int64) : Except String (Arr .long n) := Arr.ofPart .long n (longs (packLongs xs)) "col"

/-- A relation from its pairs of longs. -/
def ofPairs (ps : List (Int64 × Int64)) : Except String (Rel Sq Sq) := do
  pure ⟨ps.length, ← col ps.length (ps.map (·.1)), ← col ps.length (ps.map (·.2))⟩

/-- The bitboard of the squares `ss`. -/
def board (ss : List Nat) : Int64 := (ss.foldl (fun b s => b ||| (1 : UInt64) <<< s.toUInt64) 0).toInt64

/-- `a ≠ b` on a common rank or file, and the squares strictly between them. -/
def onLine (a b : Nat) : Bool := a != b && (a % 8 == b % 8 || a / 8 == b / 8)
def btw (a b : Nat) : List Nat :=
  (List.range 64).filter fun s => (s % 8 == a % 8 && a % 8 == b % 8 || s / 8 == a / 8 && a / 8 == b / 8) &&
    min a b < s && s < max a b

/-! ## The tables, built in Lean -/

/-- `bit : Sq ⟶ BB`, `s ↦ 2^s`. -/
def bit : Except String (Rel Sq BB) := ofPairs ((List.range 64).map fun s => (Int64.ofNat s, board [s]))

/-- `between : Sq² ⟶ BB`, `Λ` of "strictly between": every `a ≠ b` on a rank or file, `0` when adjacent. -/
def between : Except String (Rel Sq2 BB) := do
  let ps := (List.range 64).flatMap fun a => ((List.range 64).filter (onLine a)).map (a, ·)
  let n := ps.length
  pure ⟨n, (← col n (ps.map (Int64.ofNat ·.1)), ← col n (ps.map (Int64.ofNat ·.2))), ← col n (ps.map fun (a, b) => board (btw a b))⟩

/-- `kAdj : Sq ⟶ Sq`, a king step. -/
def kAdj : Except String (Rel Sq Sq) :=
  ofPairs ((List.range 64).flatMap fun a => ((List.range 64).filter fun b => a != b &&
    a % 8 ≤ b % 8 + 1 && b % 8 ≤ a % 8 + 1 && a / 8 ≤ b / 8 + 1 && b / 8 ≤ a / 8 + 1).map
    fun b => (Int64.ofNat a, Int64.ofNat b))

/-- `sel : Pc ⟶ Pos`, the kind's column as all ones and the others `0`: which bitboard a move moves. -/
def sel : Except String (Rel Pc Pos) := do
  pure ⟨3, ← col 3 [pR, pK, pk], (← col 3 [-1, 0, 0], ← col 3 [0, -1, 0], ← col 3 [0, 0, -1])⟩

/-- `{0}` as a coreflexive: `≫ zero` keeps the rows whose value is `0`, `antiJoin · zero` the others. -/
def zero : Except String (Rel BB BB) := do let z ← col 1 [0]; pure (idU z)

/-! ## The relations -/

section
variable {X : Obj}

/-- The squares of a bitboard: `s` with `bit(s) & B ≠ 0`, each of the 64 squares tried against each row. -/
def squares (B : Rel X BB) : Except String (Rel X Sq) := do
  let b ← bit
  let T : Rel X (.prod Sq BB) ← top (B := .prod Sq BB) B.key (b.key, b.val)
  let Z : Rel X (.prod (.prod Sq BB) BB) ← pair T B
  let W : Rel (.prod X Sq) BB := ⟨Z.n, (Z.key, Z.val.1.1), ← Ew.bitwise Kernel.Ew.band Z.val.1.2 Z.val.2⟩
  let S ← antiJoin W (← zero)
  pure ⟨S.n, S.key.1, S.key.2⟩

/-- `R | K | k`, row by row. -/
def occ (P : Rel X Pos) : Except String (Rel X BB) := do
  pure ⟨P.n, P.key, ← Ew.bitwise Kernel.Ew.bor (← Ew.bitwise Kernel.Ew.bor P.val.1 P.val.2.1) P.val.2.2⟩

/-- A move applied to its row's position: with `s` the moved kind's mask (`sel`), `f`, `t` the bits of
    the squares, each bitboard `c` becomes `(c & ~(f&s) & ~(t&~s)) | (t&s)` — the mover leaves `f` and
    lands on `t`, every other kind loses `t` (a capture). `P`, `m` one row per key. -/
def apply (P : Rel X Pos) (m : Rel X Move) : Except String (Rel X Pos) := do
  let b ← bit
  let Z ← pair P (← pair (← comp ⟨m.n, m.key, m.val.1⟩ (← sel))
    (← pair (← comp ⟨m.n, m.key, m.val.2.1⟩ b) (← comp ⟨m.n, m.key, m.val.2.2⟩ b)))
  let (f, t) := Z.val.2.2
  let kind (c s : Arr .long Z.n) : Except String (Arr .long Z.n) := do
    Ew.bitwise Kernel.Ew.bor (← Ew.bitwise Kernel.Ew.bandnot (← Ew.bitwise Kernel.Ew.bandnot c (← Ew.bitwise Kernel.Ew.band f s))
      (← Ew.bitwise Kernel.Ew.bandnot t s)) (← Ew.bitwise Kernel.Ew.band t s)
  let (c, s) := (Z.val.1, Z.val.2.1)
  pure ⟨Z.n, Z.key, (← kind c.1 s.1, ← kind c.2.1 s.2.1, ← kind c.2.2 s.2.2)⟩

/-- The rows `(x, (a, b))` of `A : X ⟶ Sq² × BB` whose mask meets nothing of `occ(x)`. -/
def clear (A : Rel X (.prod Sq2 BB)) (o : Rel X BB) : Except String (Rel X Sq2) := do
  let Z ← pair A o
  let W ← comp (⟨Z.n, (Z.key, Z.val.1.1), ← Ew.bitwise Kernel.Ew.band Z.val.1.2 Z.val.2⟩ : Rel (.prod X Sq2) BB) (← zero)
  pure ⟨W.n, W.key.1, W.key.2⟩

/-- `between` with each key copied into the value: `r ↦ ((r, t), mask)`. -/
def lines (mask : Rel Sq2 BB) : Rel Sq (.prod Sq2 BB) := ⟨mask.n, mask.key.1, (mask.key, mask.val)⟩

/-- White's rook moves `(r, t)`: `t` on a line with `r`, nothing strictly between, `t` itself empty — the
    mask `between(r,t) | bit(t)` meets no occupied square. -/
def rookMoves (P : Rel X Pos) : Except String (Rel X Sq2) := do
  let bw ← between
  let T ← pair bw (← comp ⟨bw.n, bw.key, bw.key.2⟩ (← bit))
  let path : Rel Sq2 BB := ⟨T.n, T.key, ← Ew.bitwise Kernel.Ew.bor T.val.1 T.val.2⟩
  clear (← comp (← squares ⟨P.n, P.key, P.val.1⟩) (lines path)) (← occ P)

/-- The rows whose square `ks` is attacked: a white rook with nothing between it and `ks`, or the white
    king a step away. -/
def attacked (P : Rel X Pos) (ks : Rel X Sq) : Except String (Rel X X) := do
  let bw ← between
  let rook ← clear (← comp (← pair (← squares ⟨P.n, P.key, P.val.1⟩) ks) (⟨bw.n, bw.key, (bw.key, bw.val)⟩ : Rel Sq2 (.prod Sq2 BB))) (← occ P)
  let N ← pair (← comp (← comp ks (← kAdj)) (← bit)) (⟨P.n, P.key, P.val.2.1⟩ : Rel X BB)
  let king ← antiJoin (⟨N.n, N.key, ← Ew.bitwise Kernel.Ew.band N.val.1 N.val.2⟩ : Rel X BB) (← zero)
  union (← dom rook) (← dom king)

end

/-- The moves `(p, from, to)` of the piece `p` along the pairs `M : X ⟶ Sq²`, as a coreflexive. -/
def moves {X : Obj} (p : Int64) (M : Rel X Sq2) : Except String (Rel Move Move) := do
  let T ← top (← ran M).val (← col 1 [p])
  pure (idU ((T.val, T.key) : Vals Move T.n))

/-- The mate-in-one moves of white from the one-row position `P0`: the white moves none of whose
    contexts (a black king move after it) leaves the king unattacked. -/
def mateIn1 (P0 : Rel Sq Pos) : Except String (Rel Move Move) := do
  let ks ← squares ⟨P0.n, P0.key, P0.val.2.2⟩
  let wm ← moves pR (← rookMoves P0)
  let bm ← moves pk (← pair ks (← comp ks (← union (← kAdj) (idU (← bit).key))))
  let C ← top wm.key bm.key
  let U : Vals Ctx C.n := (C.key, C.val)
  let P2 ← apply (← apply (← top U P0.val) ⟨C.n, U, U.1⟩) ⟨C.n, U, U.2⟩
  let free ← diff (idU U) (← attacked P2 ⟨C.n, U, U.2.2.2⟩)
  diff wm (← ran (← comp free ⟨C.n, U, U.1⟩))

/-- The position: white rooks, white king, black king, by squares. -/
def pos (rooks : List Nat) (wk bk : Nat) : Except String (Rel Sq Pos) := do
  pure ⟨1, ← col 1 [0], (← col 1 [board rooks], ← col 1 [board [wk]], ← col 1 [board [bk]])⟩

section Checks

private def name (s : Int64) : String := ["a", "b", "c", "d", "e", "f", "g", "h"][s.toInt.toNat % 8]! ++ toString (s.toInt.toNat / 8 + 1)

private def answer (rooks : List Nat) (wk bk : Nat) : Option (List (List Int64)) :=
  (do mateIn1 (← pos rooks wk bk)).toOption.map fun (R : Rel Move Move) =>
    (R.toList.map fun (m : (Int64 × Int64 × Int64) × (Int64 × Int64 × Int64)) => [m.1.1, m.1.2.1, m.1.2.2]).mergeSort fun a b => decide (a ≤ b)

-- W Kg1 Ra7 Rb1, B Ke8: Rb1-b8 mates
#guard answer [48, 1] 6 60 == some [[pR, 1, 57]]
-- B Kc8: Rb8+ fails to Kxb8, Ra8+ leaves c7
#guard answer [48, 1] 6 58 == some []

#eval (answer [48, 1] 6 60).map (·.map fun m => name m[1]! ++ name m[2]!)

end Checks

end LeetQ.Rel.Chess
