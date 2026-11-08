import LeetQ.Rel.Algebra

/-! Mate in one for the two-rook ladder, as relations over bitboards. A square is the long `0 … 63`
    (a1 = 0, b1 = 1, …, h8 = 63), a bitboard the long whose bit `s` says square `s`. A position is one row
    of three bitboards `(R, K, k)`: white rooks, white king, black king. A move is `(piece, from, to)`.
    The mate test is relation algebra on two base relations, `att` and `nxt`, each keyed by the position
    `x` it is read in: a piece is `(x, (p, s))`, a square `(x, t)`. -/

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
/-- A piece in the position `x`: `(x, (p, s))`. -/
abbrev Pce (X : Obj) : Obj := .prod X (.prod Pc Sq)
/-- A square in the position `x`: `(x, t)`. -/
abbrev At (X : Obj) : Obj := .prod X Sq

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

/-! ## Building `on`, `att`, `nxt` -/

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

/-- The white pieces `R | K`, and every piece `R | K | k`, row by row. -/
def white (P : Rel X Pos) : Except String (Rel X BB) := do
  pure ⟨P.n, P.key, ← Ew.bitwise Kernel.Ew.bor P.val.1 P.val.2.1⟩
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

/-- The rows `(x, (s, t))` of `M` whose mask (one per row) meets nothing of `o(x)`. -/
def clear (M : Rel X Sq2) (mask : Rel (.prod X Sq2) BB) (o : Rel X BB) : Except String (Rel X Sq2) := do
  let Z ← pair mask (← comp (⟨M.n, (M.key, M.val), M.key⟩ : Rel (.prod X Sq2) X) o)
  let W ← comp (⟨Z.n, Z.key, ← Ew.bitwise Kernel.Ew.band Z.val.1 Z.val.2⟩ : Rel (.prod X Sq2) BB) (← zero)
  pure ⟨W.n, W.key.1, W.key.2⟩

/-- From the squares `S`, a rook's line cut at the first piece of `o`: `t` on a rank or file with `s`,
    nothing of `o` strictly between. -/
def reach (S : Rel X Sq) (o : Rel X BB) : Except String (Rel X Sq2) := do
  let bw ← between
  let M ← comp S ⟨bw.n, bw.key.1, bw.key⟩
  clear M (← comp ⟨M.n, (M.key, M.val), M.val⟩ bw) o

/-- From the squares `S`, a king step. -/
def step (S : Rel X Sq) : Except String (Rel X Sq2) := do
  let a ← kAdj; comp S ⟨a.n, a.key, (a.key, a.val)⟩

/-- The rows `(x, (s, t))` of `M` whose `t` holds nothing of `o`. -/
def vacant (M : Rel X Sq2) (o : Rel X BB) : Except String (Rel X Sq2) := do
  clear M (← comp ⟨M.n, (M.key, M.val), M.val.2⟩ (← bit)) o

/-- The rows `(x, (s, t))` of the kind `p` as the pairs `(x, (p, s)) ⟶ (x, t)`. -/
def tag (p : Int64) (M : Rel X Sq2) : Except String (Rel (Pce X) (At X)) := do
  pure ⟨M.n, (M.key, (← col M.n (List.replicate M.n p), M.val.1)), (M.key, M.val.2)⟩

/-- The pieces of kind `p` on the bitboard `B`: `x ⟶ (x, (p, s))`. -/
def piece (p : Int64) (B : Rel X BB) : Except String (Rel X (Pce X)) := do
  let S ← squares B; pure ⟨S.n, S.key, (S.key, (← col S.n (List.replicate S.n p), S.val))⟩

variable (P : Rel X Pos)

/-- `onʷ, onᵏ, on : X ⟶ X×(Pc×Sq)`: the white pieces, the black king, all pieces of each position. -/
def onW : Except String (Rel X (Pce X)) := do
  union (← piece pR ⟨P.n, P.key, P.val.1⟩) (← piece pK ⟨P.n, P.key, P.val.2.1⟩)
def onK : Except String (Rel X (Pce X)) := piece pk ⟨P.n, P.key, P.val.2.2⟩
def on : Except String (Rel X (Pce X)) := do union (← onW P) (← onK P)

/-- `att : X×(Pc×Sq) ⟶ X×Sq`, piece `p` on `s` attacks `t` (`t` may hold a piece of either colour). The
    lines are cut by white's pieces only — the board without the black king, the one board white's
    attacks are asked on — so the square behind a checked king counts as attacked. -/
def att : Except String (Rel (Pce X) (At X)) := do
  let K ← squares ⟨P.n, P.key, P.val.2.1⟩; let k ← squares ⟨P.n, P.key, P.val.2.2⟩
  union (← tag pR (← reach (← squares ⟨P.n, P.key, P.val.1⟩) (← white P)))
    (← union (← tag pK (← step K)) (← tag pk (← step k)))

/-- `nxt : X×(Pc×Sq) ⟶ X×Sq`, piece `p` on `s` can move to `t`: not onto its own colour, a capture
    allowed; whether the mover's king is left in check is not asked. -/
def nxt : Except String (Rel (Pce X) (At X)) := do
  let w ← white P; let b : Rel X BB := ⟨P.n, P.key, P.val.2.2⟩
  let K ← squares ⟨P.n, P.key, P.val.2.1⟩; let k ← squares ⟨P.n, P.key, P.val.2.2⟩
  union (← tag pR (← vacant (← reach (← squares ⟨P.n, P.key, P.val.1⟩) (← occ P)) w))
    (← union (← tag pK (← vacant (← step K) w)) (← tag pk (← vacant (← step k) b)))

/-- `π₂ : X×(Pc×Sq) ⟶ X×Sq` on the pieces `O`, `(x, (p, s)) ↦ (x, s)`. -/
def π₂ (O : Rel X (Pce X)) : Rel (Pce X) (At X) := ⟨O.n, O.val, (O.val.1, O.val.2.2)⟩

end

/-! ## Mate -/

section
variable {X : Obj} (P : Rel X Pos)

/-- `Aʷ ≜ onʷ att : X ⟶ X×Sq`, the squares white attacks. -/
def Aw : Except String (Rel X (At X)) := do comp (← onW P) (← att P)

/-- `D ≜ Aʷ / nxt : X ⟶ X×(Pc×Sq)`, `Z ⊑ D ⟺ Z nxt ⊑ Aʷ`: the pieces all of whose next squares are
    attacked. The universes: the positions, and the pieces of `on`. -/
def D : Except String (Rel X (Pce X)) := do rightDiv (← Aw P) (← nxt P) P.key (← ran (← on P)).key

/-- `Aʷ π₂° : X ⟶ X×(Pc×Sq)`, the pieces standing on an attacked square. -/
def onA : Except String (Rel X (Pce X)) := do comp (← Aw P) (← conv (π₂ (← on P)))

/-- `Mate ≜ onᵏ ∩ Aʷ π₂° ∩ D`: the black king, attacked, all of whose next squares are attacked. -/
def Mate : Except String (Rel X (Pce X)) := do inter (← onK P) (← inter (← onA P) (← D P))

end

/-- `onᵏ ⊑ D ∩ Aʷ π₂°` for the one position `P0`. -/
def isMate (P0 : Vals Pos 1) : Except String Bool := do
  let P := idU P0; le (← onK P) (← inter (← D P) (← onA P))

/-- The mate-in-one moves of white from the position `P0`: each white rook move (`onʷ`'s rooks, `nxt`)
    applied to `P0`, `dom Mate` over the positions reached, read back to the moves leading there. -/
def mateIn1 (P0 : Vals Pos 1) : Except String (Rel Move Move) := do
  let P := idU P0
  let N ← comp (← ran (← piece pR ⟨P.n, P.key, P.val.1⟩)) (← nxt P)
  let W : Vals Move N.n := (N.key.2.1, N.key.2.2, N.val.2)
  let P1 ← apply (← top W P0) (idU W)
  dom (← comp P1 (← dom (← Mate (← ran P1))))

/-- The position: white rooks, white king, black king, by squares. -/
def pos (rooks : List Nat) (wk bk : Nat) : Except String (Vals Pos 1) := do
  pure (← col 1 [board rooks], ← col 1 [board [wk]], ← col 1 [board [bk]])

section Checks

private def name (s : Int64) : String := ["a", "b", "c", "d", "e", "f", "g", "h"][s.toInt.toNat % 8]! ++ toString (s.toInt.toNat / 8 + 1)

private def answer (rooks : List Nat) (wk bk : Nat) : Option (List (List Int64)) :=
  (do mateIn1 (← pos rooks wk bk)).toOption.map fun (R : Rel Move Move) =>
    (R.toList.map fun (m : (Int64 × Int64 × Int64) × (Int64 × Int64 × Int64)) => [m.1.1, m.1.2.1, m.1.2.2]).mergeSort fun a b => decide (a ≤ b)

-- W Kg1 Ra7 Rb1, B Ke8: Rb1-b8 mates
#guard answer [48, 1] 6 60 == some [[pR, 1, 57]]
-- B Kc8: Rb8+ fails to Kxb8, Ra8+ leaves c7
#guard answer [48, 1] 6 58 == some []
-- W Kg1 Ra7 Rb8: Ke8 is mated (f8 is behind the king on b8's line); Kc8 takes the undefended b8
#guard (do isMate (← pos [48, 57] 6 60)).toOption == some true
#guard (do isMate (← pos [48, 57] 6 58)).toOption == some false

#eval (answer [48, 1] 6 60).map (·.map fun m => name m[1]! ++ name m[2]!)

end Checks

end LeetQ.Rel.Chess
