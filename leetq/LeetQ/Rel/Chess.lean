import LeetQ.Rel.Algebra

/-! Mate in one as relation algebra on the squares. A square is the long `0 … 63` (a1 = 0, b1 = 1, …, h8 = 63),
    a piece the long `colour*6 + kind` (kind 0 P, 1 N, 2 B, 3 R, 4 Q, 5 K; white `0 … 5`, black `6 … 11`). The
    board is one relation `on : Sq ⟶ Pc`, one row per piece, so pieces enter only as data and a position with
    other pieces is other rows, never other code. Every relation below is `Sq ⟶ Sq`: constant step tables,
    coreflexives read off `on`, and `W`, `B`, `P` composed from them. -/

namespace LeetQ.Rel.Chess

open Alg QLean

abbrev Sq : Obj := .long
abbrev Pc : Obj := .long
/-- A board: `s ⟶ p`, the square `s` holds `p`. -/
abbrev Board := Rel Sq Pc
abbrev V := Rel Sq Sq

/-- The 64 squares. -/
def U := col ((List.range 64).map Int64.ofNat)
/-- `𝟙 : Sq ⟶ Sq` on the 64 squares. -/
def one : V := idU U
/-- `⊤ : Sq ⟶ Sq`, every pair of squares. -/
def T : V := top U U

/-- `R₁R₂…Rₙ`, composition in diagram order. -/
def seq : List V → V
  | [] => one
  | r :: rs => rs.foldl comp r

/-- `⋃ Rᵢ`. -/
def unions (rs : List V) : V := rs.foldl union zero

/-- `R*`, the union of the powers `R⁰ … R⁷`: no step on the board repeats more than 7 times, so `R⁸` adds
    nothing for the step tables `R` is built from. -/
def star (R : V) : V := Id.run do
  let mut p := one; let mut a := p
  for _ in [0:7] do p := comp p R; a := union a p
  return a

/-! ## Constant tables -/

/-- `a ⟶ b` with `b` the square `(df, dr)` files and ranks from `a`, for each step of `ds`. -/
def step (ds : List (Int × Int)) : V :=
  ofPairs <| (List.range 64).flatMap fun a => ds.filterMap fun (df, dr) =>
    let x := (a % 8 : Nat) + df; let y := (a / 8 : Nat) + dr
    if 0 ≤ x && x < 8 && 0 ≤ y && y < 8 then some (Int64.ofNat a, Int64.ofInt (8 * y + x)) else none

/-- The 8 directions `(file, rank)`. -/
def dirs : List (Int × Int) := [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1)]

/-- `D`: one step along the direction `d`. -/
def D (d : Int × Int) : V := step [d]

/-- `K ≜ ⋃_D D`: king steps. -/
def K : V := unions (dirs.map D)

/-- `N`: knight steps. -/
def N : V := step [(1, 2), (2, 1), (-1, 2), (-2, 1), (1, -2), (2, -1), (-1, -2), (-2, -1)]

/-- Colour `c`'s pawn: one step forward `F` (white up, black down), its two forward diagonals `X`, and the
    coreflexive `S` on its start rank. -/
def F (c : Int64) : V := D (0, 1 - 2 * c.toInt)
def X (c : Int64) : V := step [(1, 1 - 2 * c.toInt), (-1, 1 - 2 * c.toInt)]
def S (c : Int64) : V :=
  let r := 1 + 5 * c.toInt.toNat; idU (col ((List.range 8).map fun i => Int64.ofNat (8 * r + i)))

/-! ## Coreflexives read off the board -/

/-- The squares holding one of the pieces `cs`. -/
def sq (cs : List Int64) (on : Board) : V := dom (comp on (idU (col cs)))

/-- `e`: the empty squares; the black king's square is not empty. -/
def e (on : Board) : V := antiJoin one (dom on)
/-- `k`: the black king's square. -/
def k : Board → V := sq [11]
/-- `f`: the squares holding no black piece. -/
def f (on : Board) : V := antiJoin one (sq [6, 7, 8, 9, 10, 11] on)

/-- `s_D`: colour `c`'s pieces that slide along `d`, rook and queen orthogonally, bishop and queen diagonally. -/
def s (c : Int64) (d : Int × Int) : Board → V :=
  sq (if d.1 * d.2 == 0 then [6 * c + 3, 6 * c + 4] else [6 * c + 2, 6 * c + 4])

/-! ## `W`, `B`, `P` -/

/-- `⋃_D s_D D(ED)*`: colour `c`'s slider rays, on through the squares of `E`, up to and including the first
    square off `E`. -/
def rays (c : Int64) (E : V) (on : Board) : V :=
  unions (dirs.map fun d => let t := D d; seq [s c d on, t, star (comp E t)])

/-- Colour `c`'s pawn moves: forward onto `e`, two forward from the start rank across `e`, diagonally forward
    onto `o`. -/
def pawn (c : Int64) (o : V) (on : Board) : V :=
  let e := e on; let t := F c
  unions [comp t e, seq [S c, t, e, t, e], comp (X c) o]

/-- `W`: the squares white attacks, the black king removed, so a ray runs on through `k`; a ray ends on the first
    occupied square, so a defended white piece counts as attacked. -/
def W (on : Board) : V :=
  unions [rays 0 (union (e on) (k on)) on, comp (sq [1] on) N, comp (sq [0] on) (X 0), comp (sq [5] on) K]

/-- `B`: black's moves but the king's, pins ignored: knight and slider moves onto `f`, pawn moves. -/
def B (on : Board) : V :=
  unions [comp (union (rays 1 (e on) on) (comp (sq [7] on) N)) (f on),
    comp (sq [6] on) (pawn 1 (sq [0, 1, 2, 3, 4, 5] on) on)]

/-- `P ≜ ⋃_D s_D (De)* D d_D`, `d_D ≜ dom((De)*Dk)`: a white slider to each square strictly between it and the
    black king on a `D`-line whose other between squares are empty; an occupied such square is pinned. -/
def P (on : Board) : V :=
  let e := e on; let k := k on
  unions (dirs.map fun d =>
    let t := D d; let R := star (comp t e)
    seq [s 0 d on, R, t, dom (seq [R, t, k])])

/-! ## Mate -/

/-- Mate, single check only, `⊤` (Lean `T`) the full relation on the squares:
    `k(𝟙 ∪ Kf) ⊑ ⊤W` — the king is attacked, and so is each king step onto a square with no black piece;
    `B(𝟙 ∪ P°)Wk ⊑ P°⊤` — each black move capturing the checker or landing between it and the king starts on
    a pinned square. -/
def isMate (on : Board) : Bool :=
  let W := W on; let k := k on; let P' := conv (P on)
  le (comp k (union one (comp K (f on)))) (comp T W) && le (seq [B on, union one P', W, k]) (comp P' T)

/-- `M`: white's moves, pins and checks on white ignored: slider, knight and king moves onto a square with neither
    a white piece nor the black king, and pawn moves capturing any black piece but the king. -/
def M (on : Board) : V :=
  let g := antiJoin one (sq [0, 1, 2, 3, 4, 5, 11] on)
  unions [comp (unions [rays 0 (e on) on, comp (sq [1] on) N, comp (sq [5] on) K]) g,
    comp (sq [0] on) (pawn 0 (sq [6, 7, 8, 9, 10] on) on)]

/-- The mate-in-one moves `(p, s, t)` of white on `on`: for each move `s ⟶ t` of `M`, the board without the rows
    on `s` and `t`, with `t ⟶ p` for each row `tp` of the piece on `s`, rebuilt and tested by `isMate`. A move
    from an empty square has no such row, so it contributes nothing. -/
def mateIn1 (on : Board) : List (Int64 × Int64 × Int64) :=
  (M on).toList.eraseDups.flatMap fun (a, b) =>
    let tp := comp (ofPairs [(b, a)]) on
    let on1 := union (conv (antiJoin (conv on) (idU (col [a, b])))) tp
    tp.toList.filterMap fun (_, p) => if isMate on1 then some (p, a, b) else none

/-- The board from its `(square, piece)` rows. -/
def pos (ps : List (Nat × Int64)) : Board := ofPairs (ps.map fun (s, p) => (Int64.ofNat s, p))

section Checks

private def answer (ps : List (Nat × Int64)) : List (List Int64) :=
  ((mateIn1 (pos ps)).map fun (p, s, t) => [p, s, t]).mergeSort fun a b => decide (a ≤ b)

private def mate (ps : List (Nat × Int64)) : Bool := isMate (pos ps)

-- W Kg1 Ra7 Rb1, B Ke8: Rb1-b8 mates
#guard answer [(6, 5), (48, 3), (1, 3), (60, 11)] == [[3, 1, 57]]
-- B Kc8: Rb8+ fails to Kxb8, Ra8+ leaves c7
#guard answer [(6, 5), (48, 3), (1, 3), (58, 11)] == []
-- a third rook, no new code: Rb1-b8 and Rh2-h8
#guard answer [(6, 5), (48, 3), (1, 3), (15, 3), (60, 11)] == [[3, 1, 57], [3, 15, 63]]
-- W Kg1 Ra7 Rb8, B Ke8 mated; with B Kc8, Kxb8 takes the undefended rook
#guard mate [(6, 5), (48, 3), (57, 3), (60, 11)]
#guard !mate [(6, 5), (48, 3), (57, 3), (58, 11)]
-- 1. B Rc6 interposes on c8
#guard !mate [(6, 5), (48, 3), (57, 3), (60, 11), (42, 9)]
-- 2. B Nc6 takes b8 (or interposes on d8)
#guard !mate [(6, 5), (48, 3), (57, 3), (60, 11), (42, 7)]
-- 3. as 2, W Bb5 pins the knight to e8
#guard mate [(6, 5), (48, 3), (57, 3), (60, 11), (42, 7), (33, 2)]
-- 4. as 1, W Bb5 pins the rook to e8
#guard mate [(6, 5), (48, 3), (57, 3), (60, 11), (42, 9), (33, 2)]
-- W Ka1 Ra5 Rg1 Nf3 Nf7, B Kh5: mated along rank 5
#guard mate [(0, 5), (32, 3), (6, 3), (21, 1), (53, 1), (39, 11)]
-- 5. B pd6 steps to d5
#guard !mate [(0, 5), (32, 3), (6, 3), (21, 1), (53, 1), (39, 11), (43, 6)]
-- 6. B ph6 reaches the empty g5 only diagonally, and h5 holds its king
#guard mate [(0, 5), (32, 3), (6, 3), (21, 1), (53, 1), (39, 11), (47, 6)]
-- W Kg1 Ra7 Rd8 Rd1, B Ke8: Kxd8 fails, d8 is defended by Rd1
#guard mate [(6, 5), (48, 3), (59, 3), (3, 3), (60, 11)]
-- 7. as above, B Nc6 takes d8
#guard !mate [(6, 5), (48, 3), (59, 3), (3, 3), (60, 11), (42, 7)]
-- 8. W Kg1 Ra7 Rb8, B Kd8: Ke8 steps back along the checking line, still attacked
#guard mate [(6, 5), (48, 3), (57, 3), (59, 11)]

end Checks

end LeetQ.Rel.Chess
