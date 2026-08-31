/-
  Bird & de Moor, *Algebra of Programming* §10.2  The detab–entab problem (book pp. 246-247) —
  a worked program in the Set model, over snoc-lists of characters.

  `detab` replaces tabs by the right number of blanks to reach the next tab stop (every `n`
  columns).  Naively `detab = ⦇[nil, expand]⦈`, but `expand` needs the current column, so B&dM
  TUPLE `detab` with `col` (the column counter): `(detab, col·detab) = ⦇[base, step]⦈`, a single
  snoc-list catamorphism carrying `(output, column)`, implemented as a loop.  We build that tupled
  catamorphism concretely (over `SnocList Unit Char` from `AOP.A6_SnocList`) and give its loop
  recursion; `detab` is the first component.
-/
module

public import AOP.A10_1
public import AOP.A6_SnocList

namespace Freyd.Alg.RelSet.Detab

open Freyd Freyd.Alg.RelSet Freyd.Alg.RelSet.SL

-- Tab width `n`, and the tab / newline / blank characters.
variable (n : Nat) (tb nl blank : Char)

/-- The accumulator: `(output so far, current column)`. -/
@[expose] public abbrev St : RelSet.{0} := ⟨List Char × Nat⟩

/-- The tupled algebra `[base, step]` (B&dM p.247): `base = ([], 0)`, and `step` appends a
    character, resetting the column on a newline, padding with blanks to the next tab stop on a
    tab, and advancing the column by one otherwise. -/
def stepFn : (Fobj Unit Char (St)).carrier → (List Char × Nat)
  | Sum.inl _ => ([], 0)
  | Sum.inr ((x, c), a) =>
      if a = nl then (x ++ [nl], 0)
      else if a = tb then (x ++ List.replicate (n - c % n) blank, c + (n - c % n))
      else (x ++ [a], c + 1)

/-- `[base, step] : F(output×col) → (output×col)`, a map (graph of `stepFn`). -/
def detabAlg : Fobj Unit Char (St) ⟶ St := graph (stepFn n tb nl blank)

/-- **The tupled catamorphism** `(detab, col·detab) = ⦇[base, step]⦈`, carrying `(output, column)`
    through the input in one left-to-right pass (the loop of B&dM p.247). -/
def detabTupled : dSL Unit Char ⟶ St := cataR (detabAlg n tb nl blank)

/-- **§10.2 loop, base case**: on the empty input the accumulator is `([], 0)`. -/
theorem detab_wrap (r : List Char × Nat) :
    detabTupled n tb nl blank (SnocList.wrap ()) r ↔ r = ([], 0) := Iff.rfl

/-- **§10.2 loop, step case**: `⦇[base,step]⦈ (x `snoc` a) = step (⦇[base,step]⦈ x, a)` — the
    iterative loop, appending each character to the running `(output, column)`. -/
theorem detab_snoc (x : SnocList Unit Char) (a : Char) (r : List Char × Nat) :
    detabTupled n tb nl blank (SnocList.snoc x a) r ↔
      ∃ r', detabTupled n tb nl blank x r' ∧ r = stepFn n tb nl blank (Sum.inr (r', a)) :=
  Iff.rfl

/-- `detab` itself is the first component of the tupled catamorphism. -/
def detab : dSL Unit Char ⟶ (⟨List Char⟩ : RelSet.{0}) :=
  detabTupled n tb nl blank ≫ graph Prod.fst


/-! ## §10.2's SPECIFICATION side (`entab-defn`), over snoc-lists of characters

  Everything above is the derived PROGRAM (B&dM p.247): `detab` tupled with the column counter
  and run as a loop, carrying the output as a plain `List Char`.  What follows is the other end
  of the derivation — `detab ≜ ⦇[nil,expand]⦈` as a snoc-list catamorphism, the order
  `R ≜ length ≤ length°`, and the greedy data `U`, `V`, `Q` the note's `entab-defn` names.  The
  two are different objects: the loop's accumulator is a plain list because a running column is
  not part of the specification.

  `TB`, `NL`, `BL` stay the abstract `tb`, `nl`, `blank` of the program above; the refutation at
  the end instantiates them at the real tab, newline and blank. -/

/-- **entab-defn**: `String=[Char]` over snoc-lists. -/
@[expose] public abbrev Str : Type := SnocList Unit Char

/-- `x⧺blanks k`. -/
@[expose] public def pad (blank : Char) : Str → Nat → Str
  | x, 0 => x
  | x, k + 1 => SnocList.snoc (pad blank x k) blank

/-- The length of a string. -/
@[expose] public def slen : Str → Nat
  | SnocList.wrap _ => 0
  | SnocList.snoc x _ => slen x + 1

/-- **entab-defn**: `col≜⦇[zero,count]⦈`, `count (c,a)=(a=NL→0,c+1)`. -/
@[expose] public def colFn (nl : Char) : Str → Nat
  | SnocList.wrap _ => 0
  | SnocList.snoc x a => if a = nl then 0 else colFn nl x + 1

/-- **entab-defn**: `fill xs=xs⧺blanks (n−(col xs) mod n)`. -/
@[expose] public def fillFn (n : Nat) (nl blank : Char) (x : Str) : Str :=
  pad blank x (n - colFn nl x % n)

/-- **entab-defn**: `expand (xs,a)=(a=TB→fill xs,xs⧺[a])`. -/
@[expose] public def expandFn (n : Nat) (tb nl blank : Char) (x : Str) (a : Char) : Str :=
  if a = tb then fillFn n nl blank x else SnocList.snoc x a

/-- **entab-defn**: `detab≜⦇[nil,expand]⦈ : String⟶String`, read as the function it is. -/
@[expose] public def detabFn (n : Nat) (tb nl blank : Char) : Str → Str
  | SnocList.wrap _ => SnocList.wrap ()
  | SnocList.snoc x a => expandFn n tb nl blank (detabFn n tb nl blank x) a

/-- **entab-defn**: the algebra `[nil,expand] : F(String)⟶String`. -/
@[expose] public def expandAlgFn (n : Nat) (tb nl blank : Char) :
    (Fobj Unit Char (dSL Unit Char)).carrier → Str
  | Sum.inl _ => SnocList.wrap ()
  | Sum.inr (x, a) => expandFn n tb nl blank x a

/-- **entab-defn**: the catamorphism of `[nil,expand]` IS `detabFn`. -/
public theorem detab_cata (n : Nat) (tb nl blank : Char) :
    cataR (graph (expandAlgFn n tb nl blank))
      = (graph (detabFn n tb nl blank) : dSL Unit Char ⟶ dSL Unit Char) := by
  apply hom_ext; intro x
  induction x with
  | wrap _ => exact fun y => Iff.rfl
  | snoc x a ih =>
    intro y
    constructor
    · rintro ⟨y', hy', hstep⟩
      obtain rfl : y' = detabFn n tb nl blank x := (ih y').mp hy'
      exact hstep
    · intro (h : y = expandFn n tb nl blank (detabFn n tb nl blank x) a)
      exact ⟨detabFn n tb nl blank x, (ih _).mpr rfl, h⟩

/-- **entab-defn**: `x` is a prefix of `y`. -/
@[expose] public def prefixS : Str → Str → Prop
  | x, SnocList.wrap _ => x = SnocList.wrap ()
  | x, SnocList.snoc y c => x = SnocList.snoc y c ∨ prefixS x y

/-- `w` carries no newline, so its column IS its length. -/
@[expose] public def noNL (nl : Char) : Str → Prop
  | SnocList.wrap _ => True
  | SnocList.snoc x a => a ≠ nl ∧ noNL nl x

/-- **entab-defn**: `R≜length≤length°`. -/
@[expose] public def R : dSL Unit Char ⟶ dSL Unit Char := fun u v => slen u ≤ slen v

/-- **entab-defn**: `detab` as a morphism. -/
@[expose] public def detabR (n : Nat) (tb nl blank : Char) : dSL Unit Char ⟶ dSL Unit Char :=
  graph (detabFn n tb nl blank)

/-- **entab-defn**: `prefix`, mirrored to diagram order — `prefixR x ys` reads "`ys` is a
    prefix of `x`". -/
@[expose] public def prefixR : dSL Unit Char ⟶ dSL Unit Char := fun x ys => prefixS ys x

/-! ## Elementary facts about `pad`, `slen`, `col` and `prefixS` -/

public theorem slen_pad (blank : Char) (x : Str) : ∀ k, slen (pad blank x k) = slen x + k
  | 0 => rfl
  | k + 1 => by show slen (pad blank x k) + 1 = slen x + (k + 1); rw [slen_pad blank x k]; omega

public theorem col_pad (nl blank : Char) (hb : blank ≠ nl) (x : Str) :
    ∀ k, colFn nl (pad blank x k) = colFn nl x + k
  | 0 => rfl
  | k + 1 => by
    show (if blank = nl then 0 else colFn nl (pad blank x k) + 1) = colFn nl x + (k + 1)
    rw [if_neg hb, col_pad nl blank hb x k]
    omega

public theorem col_eq_slen (nl : Char) : ∀ {w : Str}, noNL nl w → colFn nl w = slen w
  | SnocList.wrap _, _ => rfl
  | SnocList.snoc x a, h => by
    show (if a = nl then 0 else colFn nl x + 1) = slen x + 1
    rw [if_neg h.1, col_eq_slen nl h.2]

public theorem prefixS_slen_le : ∀ {x y : Str}, prefixS x y → slen x ≤ slen y
  | x, SnocList.wrap _, h => by rw [(h : x = SnocList.wrap ())]; exact Nat.zero_le _
  | x, SnocList.snoc y c, h => by
    rcases (h : x = SnocList.snoc y c ∨ prefixS x y) with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (prefixS_slen_le h)

/-- If two padded strings are equal and the first base is no longer, the second base is the
    first one padded — the only structural fact the `V` calculations need. -/
public theorem pad_eq_pad (blank : Char) (x y : Str) :
    ∀ j k, slen x ≤ slen y → pad blank x j = pad blank y k → ∃ m, y = pad blank x m ∧ j = m + k
  | j, 0, _, h => ⟨j, h.symm, rfl⟩
  | 0, k + 1, hle, h => by
    exfalso
    have hl : slen x = slen y + (k + 1) := by
      rw [← slen_pad blank y (k + 1), ← h]; rfl
    omega
  | j + 1, k + 1, hle, h => by
    have h' : pad blank x j = pad blank y k := by
      injection h
    obtain ⟨m, hm, hjk⟩ := pad_eq_pad blank x y j k hle h'
    exact ⟨m, hm, by omega⟩

/-! ## The note's FALSE row, refuted

  `detab prefix⊑R° detab` is marked FALSE in the note, with the witness printed there: at
  `n=8`, `detab [a,b,c,d,e,TB]=[a,b,c,d,e,BL,BL,BL]`, whose prefix `[a,b,c,d,e,BL,BL]` is
  longer than any input giving it.  The lemma behind "longer than any input" is
  `detab_len_of_short`: on a newline-free output SHORTER than one tab stop, `detab` cannot have
  used a tab at all, so input and output have the same length. -/

/-- A newline-free output shorter than a tab stop is produced letter by letter: no step of
    `detab` can have been a tab, since a tab lands the column on a multiple of `n`. -/
public theorem detab_len_of_short (n : Nat) (tb nl blank : Char) (hn : 0 < n)
    (hb : blank ≠ nl) :
    ∀ (v w : Str), noNL nl w → slen w < n → detabFn n tb nl blank v = w → slen v = slen w
  | SnocList.wrap _, w, _, _, h => by subst h; rfl
  | SnocList.snoc s c, w, hnn, hlt, h => by
    by_cases hc : c = tb
    · exfalso
      have hw : w = pad blank (detabFn n tb nl blank s)
          (n - colFn nl (detabFn n tb nl blank s) % n) := by
        rw [← h]; simp only [detabFn, expandFn, if_pos hc, fillFn]
      have hcol : colFn nl w = slen w := col_eq_slen nl hnn
      have hcol' : colFn nl w
          = colFn nl (detabFn n tb nl blank s)
            + (n - colFn nl (detabFn n tb nl blank s) % n) := by
        rw [hw, col_pad nl blank hb]
      have hmod : colFn nl (detabFn n tb nl blank s) % n
          ≤ colFn nl (detabFn n tb nl blank s) := Nat.mod_le _ _
      omega
    · have hw : w = SnocList.snoc (detabFn n tb nl blank s) c := by
        rw [← h]; simp only [detabFn, expandFn, if_neg hc]
      subst hw
      have hlt' : slen (detabFn n tb nl blank s) < n := by
        have : slen (SnocList.snoc (detabFn n tb nl blank s) c)
            = slen (detabFn n tb nl blank s) + 1 := rfl
        omega
      have hlen := detab_len_of_short n tb nl blank hn hb s (detabFn n tb nl blank s)
        hnn.2 hlt' rfl
      show slen s + 1 = slen (detabFn n tb nl blank s) + 1
      rw [hlen]

/-- Five ordinary characters and a tab: the note's `[a,b,c,d,e,TB]` at `n=8`. -/
@[expose] public def ofChars (l : List Char) : Str :=
  l.foldl (fun x a => SnocList.snoc x a) (SnocList.wrap ())

/-- **entab-laws**, the note's FALSE row certified: `detab prefix⊑R° detab` fails at `n=8`.
    `detab [x,x,x,x,x,TB]=[x,x,x,x,x,BL,BL,BL]`, and its prefix `[x,x,x,x,x,BL,BL]` needs SEVEN
    input characters (`detab_len_of_short`), one more than the six the original had — a prefix
    of the expansion can be longer than any input producing it, once it stops short of a tab
    stop.  This is why the note replaces `prefix°` by `V≜prefix°∩(fill fill°)`. -/
public theorem detab_prefix_false :
    ¬ (detabR 8 '\t' '\n' ' ' ≫ prefixR ⊑ R° ≫ detabR 8 '\t' '\n' ' ') := by
  intro hle
  have hpre : prefixS (ofChars ['x', 'x', 'x', 'x', 'x', ' ', ' '])
      (detabFn 8 '\t' '\n' ' ' (ofChars ['x', 'x', 'x', 'x', 'x', '\t'])) :=
    Or.inr (Or.inl rfl)
  obtain ⟨v, hR, hdv⟩ := le_iff.mp hle (ofChars ['x', 'x', 'x', 'x', 'x', '\t'])
    (ofChars ['x', 'x', 'x', 'x', 'x', ' ', ' '])
    ⟨detabFn 8 '\t' '\n' ' ' (ofChars ['x', 'x', 'x', 'x', 'x', '\t']), rfl, hpre⟩
  have hnn : noNL '\n' (ofChars ['x', 'x', 'x', 'x', 'x', ' ', ' ']) :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, trivial⟩
  have hv7 := detab_len_of_short 8 '\t' '\n' ' ' (by decide) (by decide) v
    (ofChars ['x', 'x', 'x', 'x', 'x', ' ', ' ']) hnn (by decide)
    (hdv : ofChars ['x', 'x', 'x', 'x', 'x', ' ', ' '] = detabFn 8 '\t' '\n' ' ' v).symm
  have h6 : slen v ≤ slen (ofChars ['x', 'x', 'x', 'x', 'x', '\t']) := hR
  have e6 : slen (ofChars ['x', 'x', 'x', 'x', 'x', '\t']) = 6 := rfl
  have e7 : slen (ofChars ['x', 'x', 'x', 'x', 'x', ' ', ' ']) = 7 := rfl
  omega

end Freyd.Alg.RelSet.Detab
