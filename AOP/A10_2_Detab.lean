/-
  Bird & de Moor, *Algebra of Programming* §10.2  The detab–entab problem (book pp. 246-247) —
  a worked program in the Set model, over snoc-lists of characters.

  `detab` replaces tabs by the right number of blanks to reach the next tab stop (every `n`
  columns).  Naively `detab = ⦇[nil, expand]⦈`, but `expand` needs the current column, so B&dM
  TUPLE `detab` with `col` (the column counter): `(detab, col·detab) = ⦇[base, step]⦈`, a single
  snoc-list catamorphism carrying `(output, column)`, implemented as a loop (`detab_tupled`,
  `detab_loop`, Exercise 10.1's `outl_loop`).  `entab` is the greedy converse (pp.248-252).
-/
module

import AOP.CalcSteps
public import AOP.A10_1
public import AOP.A6_SnocList
public import AOP.A7_2_RelSet

namespace Freyd.Alg.RelSet.Detab

open Freyd Freyd.Alg.RelSet Freyd.Alg.RelSet.SL

/-! ## §10.2's SPECIFICATION side (`entab-defn`), over snoc-lists of characters

  `detab ≜ ⦇[nil,expand]⦈` as a snoc-list catamorphism, the order
  `R ≜ length ≤ length°`, and the greedy data `U`, `V`, `Q` the note's `entab-defn` names.

  The functions take `TB`, `NL`, `BL` as parameters; a theorem that needs them distinct uses the
  characters B&dM p.246 fixes, `tb`, `nl`, `blank` below. -/

/-- **entab-defn**: `String=[Char]` over snoc-lists. -/
@[expose] public abbrev Str : Type := SnocList Unit Char

/-- B&dM p.246: `TB` is the tab character. -/
@[expose] public def tb : Char := '\t'
/-- B&dM p.246: `NL` is the newline character. -/
@[expose] public def nl : Char := '\n'
/-- B&dM p.246: `BL` is the blank character. -/
@[expose] public def blank : Char := ' '

/-- `x⧺blanks k`. -/
@[expose] public def pad (blank : Char) : Str → Nat → Str
  | x, 0 => x
  | x, k + 1 => SnocList.snoc (pad blank x k) blank

/-- The length of a string. -/
@[expose] public def length : Str → Nat
  | SnocList.wrap _ => 0
  | SnocList.snoc x _ => length x + 1

/-- **entab-defn**: `col≜⦇[zero,count]⦈`, `count (c,a)=(a=NL→0,c+1)`. -/
@[expose] public def colFn (nl : Char) : Str → Nat
  | SnocList.wrap _ => 0
  | SnocList.snoc xs a => if a = nl then 0 else colFn nl xs + 1

/-- **entab-defn**: `fill xs=xs⧺blanks (n−(col xs) mod n)`. -/
@[expose] public def fillFn (n : Nat) (nl blank : Char) (xs : Str) : Str :=
  pad blank xs (n - colFn nl xs % n)

/-- **entab-defn**: `expand (xs,a)=(a=TB→fill xs,xs⧺[a])`. -/
@[expose] public def expandFn (n : Nat) (tb nl blank : Char) (xs : Str) (a : Char) : Str :=
  if a = tb then fillFn n nl blank xs else SnocList.snoc xs a

/-- **entab-defn**: `detab≜⦇[nil,expand]⦈ : String⟶String`, read as the function it is. -/
@[expose] public def detabFn (n : Nat) (tb nl blank : Char) : Str → Str
  | SnocList.wrap _ => SnocList.wrap ()
  | SnocList.snoc xs a => expandFn n tb nl blank (detabFn n tb nl blank xs) a

/-- **entab-defn**: the algebra `[nil,expand] : F(String)⟶String`. -/
@[expose] public def expandAlgFn (n : Nat) (tb nl blank : Char) :
    (Fobj Unit Char (dSL Unit Char)).carrier → Str
  | Sum.inl _ => SnocList.wrap ()
  | Sum.inr (x, a) => expandFn n tb nl blank x a

/-- **entab-defn**: `expand : String×Char⟶String` as an arrow of its own — the note's box, and the
    second arm of `[nil,expand]`. -/
@[expose] public def expand (n : Nat) (tb nl blank : Char) :
    (⟨Str × Char⟩ : RelSet.{0}) ⟶ dSL Unit Char :=
  graph (fun p => expandFn n tb nl blank p.1 p.2)

/-- **entab-defn**: the algebra IS the junction `[nil,expand]` the note writes. -/
public theorem expandAlg_eq_junc (n : Nat) (tb nl blank : Char) :
    graph (expandAlgFn n tb nl blank) = junc (sumCop _ _) nil (expand n tb nl blank) := by
  apply hom_ext; intro u r
  constructor
  · intro h
    cases u with
    | inl d => exact Or.inl ⟨d, rfl, h⟩
    | inr p => exact Or.inr ⟨p, rfl, h⟩
  · intro h
    cases h with
    | inl h => obtain ⟨d, h1, h2⟩ := h; subst h1; exact h2
    | inr h => obtain ⟨p, h1, h2⟩ := h; subst h1; exact h2

/-- The fold of a graph is the graph of the function satisfying the fold's two equations. -/
public theorem cataR_graph {C : RelSet.{0}} (φ : (Fobj Unit Char C).carrier → C.carrier)
    (h : Str → C.carrier) (h0 : ∀ u, h (SnocList.wrap u) = φ (Sum.inl u))
    (h1 : ∀ x a, h (SnocList.snoc x a) = φ (Sum.inr (h x, a))) :
    cataR (graph φ) = graph h := by
  apply hom_ext; intro x
  induction x with
  | wrap u => intro y; show y = φ (Sum.inl u) ↔ y = h (SnocList.wrap u); rw [h0]
  | snoc x a ih =>
    intro y
    constructor
    · rintro ⟨y', hy', hstep⟩
      obtain rfl : y' = h x := (ih y').mp hy'
      exact hstep.trans (h1 x a).symm
    · intro (hy : y = h (SnocList.snoc x a))
      exact ⟨h x, (ih _).mpr rfl, hy.trans (h1 x a)⟩

/-- `⟨f,g⟩` of two graphs is the graph of the paired function. -/
public theorem rpair_graph {C A B : RelSet.{0}} (f : C.carrier → A.carrier)
    (g : C.carrier → B.carrier) :
    rpair (graph f) (graph g) = graph (B := ⟨A.carrier × B.carrier⟩) (fun x => (f x, g x)) :=
  hom_ext fun _ _ => ⟨fun ⟨h1, h2⟩ => Prod.ext h1 h2,
    fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

/-- `𝟙×g` of a graph is the graph of the product function. -/
public theorem rprodMap_id_graph {A B b' : RelSet.{0}} (g : B.carrier → b'.carrier) :
    rprodMap (𝟙 A) (graph g)
      = graph (A := ⟨A.carrier × B.carrier⟩) (B := ⟨A.carrier × b'.carrier⟩) (fun p => (p.1, g p.2)) :=
  hom_ext fun _ _ => ⟨fun ⟨h1, h2⟩ => Prod.ext h1.symm h2,
    fun h => ⟨(congrArg Prod.fst h).symm, congrArg Prod.snd h⟩⟩

/-- **entab-defn**: the catamorphism of `[nil,expand]` IS `detabFn`. -/
public theorem detab_cata (n : Nat) (tb nl blank : Char) :
    cataR (graph (expandAlgFn n tb nl blank))
      = (graph (detabFn n tb nl blank) : dSL Unit Char ⟶ dSL Unit Char) :=
  cataR_graph _ _ (fun _ => rfl) (fun _ _ => rfl)

/-- **entab-defn**: `x` is a prefix of `y`. -/
@[expose] public def prefixS : Str → Str → Prop
  | x, SnocList.wrap _ => x = SnocList.wrap ()
  | x, SnocList.snoc y c => x = SnocList.snoc y c ∨ prefixS x y

/-- `w` carries no newline, so its column IS its length. -/
@[expose] public def noNL (nl : Char) : Str → Prop
  | SnocList.wrap _ => True
  | SnocList.snoc x a => a ≠ nl ∧ noNL nl x

/-- **entab-defn**: `R≜length≤length°`. -/
@[expose] public def R : dSL Unit Char ⟶ dSL Unit Char := fun xs ys => length xs ≤ length ys

/-- **entab-defn**: `detab` as a morphism. -/
@[expose] public def detabR (n : Nat) (tb nl blank : Char) : dSL Unit Char ⟶ dSL Unit Char :=
  graph (detabFn n tb nl blank)

/-- **entab-defn**: `prefix`, mirrored to diagram order — `prefixR x ys` reads "`ys` is a
    prefix of `x`". -/
@[expose] public def prefixR : dSL Unit Char ⟶ dSL Unit Char := fun x ys => prefixS ys x

/-! ## Elementary facts about `pad`, `slen`, `col` and `prefixS` -/

public theorem slen_pad (blank : Char) (x : Str) : ∀ k, length (pad blank x k) = length x + k
  | 0 => rfl
  | k + 1 => by show length (pad blank x k) + 1 = length x + (k + 1); rw [slen_pad blank x k]; omega

public theorem col_pad (nl blank : Char) (hb : blank ≠ nl) (x : Str) :
    ∀ k, colFn nl (pad blank x k) = colFn nl x + k
  | 0 => rfl
  | k + 1 => by
    show (if blank = nl then 0 else colFn nl (pad blank x k) + 1) = colFn nl x + (k + 1)
    rw [if_neg hb, col_pad nl blank hb x k]
    omega

public theorem col_eq_slen (nl : Char) : ∀ {w : Str}, noNL nl w → colFn nl w = length w
  | SnocList.wrap _, _ => rfl
  | SnocList.snoc x a, h => by
    show (if a = nl then 0 else colFn nl x + 1) = length x + 1
    rw [if_neg h.1, col_eq_slen nl h.2]

public theorem prefixS_slen_le : ∀ {x y : Str}, prefixS x y → length x ≤ length y
  | x, SnocList.wrap _, h => by rw [(h : x = SnocList.wrap ())]; exact Nat.zero_le _
  | x, SnocList.snoc y c, h => by
    rcases (h : x = SnocList.snoc y c ∨ prefixS x y) with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (prefixS_slen_le h)

/-- If two padded strings are equal and the first base is no longer, the second base is the
    first one padded — the only structural fact the `V` calculations need. -/
public theorem pad_eq_pad (blank : Char) (x y : Str) :
    ∀ j k, length x ≤ length y → pad blank x j = pad blank y k → ∃ m, y = pad blank x m ∧ j = m + k
  | j, 0, _, h => ⟨j, h.symm, rfl⟩
  | 0, k + 1, hle, h => by
    exfalso
    have hl : length x = length y + (k + 1) := by
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
public theorem detab_len_of_short (n : Nat) (tb nl blank : Char)
    (hb : blank ≠ nl) :
    ∀ (v w : Str), noNL nl w → length w < n → detabFn n tb nl blank v = w → length v = length w
  | SnocList.wrap _, w, _, _, h => by subst h; rfl
  | SnocList.snoc s c, w, hnn, hlt, h => by
    by_cases hc : c = tb
    · exfalso
      have hw : w = pad blank (detabFn n tb nl blank s)
          (n - colFn nl (detabFn n tb nl blank s) % n) := by
        rw [← h]; simp only [detabFn, expandFn, if_pos hc, fillFn]
      have hcol : colFn nl w = length w := col_eq_slen nl hnn
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
      have hlt' : length (detabFn n tb nl blank s) < n := by
        have : length (SnocList.snoc (detabFn n tb nl blank s) c)
            = length (detabFn n tb nl blank s) + 1 := rfl
        omega
      have hlen := detab_len_of_short n tb nl blank hb s (detabFn n tb nl blank s)
        hnn.2 hlt' rfl
      show length s + 1 = length (detabFn n tb nl blank s) + 1
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
    ¬ (detabR 8 tb nl blank ≫ prefixR ⊑ R° ≫ detabR 8 tb nl blank) := by
  intro hle
  have hpre : prefixS (ofChars ['x', 'x', 'x', 'x', 'x', ' ', ' '])
      (detabFn 8 tb nl blank (ofChars ['x', 'x', 'x', 'x', 'x', '\t'])) :=
    Or.inr (Or.inl rfl)
  obtain ⟨v, hR, hdv⟩ := le_iff.mp hle (ofChars ['x', 'x', 'x', 'x', 'x', '\t'])
    (ofChars ['x', 'x', 'x', 'x', 'x', ' ', ' '])
    ⟨detabFn 8 tb nl blank (ofChars ['x', 'x', 'x', 'x', 'x', '\t']), rfl, hpre⟩
  have hnn : noNL nl (ofChars ['x', 'x', 'x', 'x', 'x', ' ', ' ']) :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, trivial⟩
  have hv7 := detab_len_of_short 8 tb nl blank (by decide) v
    (ofChars ['x', 'x', 'x', 'x', 'x', ' ', ' ']) hnn (by decide)
    (hdv : ofChars ['x', 'x', 'x', 'x', 'x', ' ', ' '] = detabFn 8 tb nl blank v).symm
  have h6 : length v ≤ length (ofChars ['x', 'x', 'x', 'x', 'x', '\t']) := hR
  have e6 : length (ofChars ['x', 'x', 'x', 'x', 'x', '\t']) = 6 := rfl
  have e7 : length (ofChars ['x', 'x', 'x', 'x', 'x', ' ', ' ']) = 7 := rfl
  omega

/-! ## `entab-defn`: `U`, `V`, `Q`, and the greedy condition

  `detab prefix⊑R° detab` being false, the note replaces `prefix°` by
  `V≜prefix°∩(fill fill°)` — only the prefixes that do not cross a tab stop.  `expand_V_step`
  is the note's ladder (`nil V°=nil`, `fill V°=fill`, `snoc V°⊑snoc∪(π₁V°)`,
  `expand V°⊑expand∪(π₁V°)`) in one statement: shortening the output of one `expand` step to a
  `V`-smaller string either leaves the step alone or discards it. -/

/-- **entab-defn**: `U` the preorder with `a U b⟺a=TB∨a=b` — `TB` below every character, so
    `est` prefers a tab to a blank. -/
@[expose] public def U (tb : Char) : (⟨Char⟩ : RelSet.{0}) ⟶ ⟨Char⟩ := fun a b => a = tb ∨ a = b

/-- **entab-defn**: `V≜prefix°∩(fill fill°)` — a prefix that fills to the same string, i.e. one
    that does not cross a tab stop. -/
@[expose] public def V (n : Nat) (nl blank : Char) : dSL Unit Char ⟶ dSL Unit Char :=
  fun xs ys => prefixS xs ys ∧ fillFn n nl blank xs = fillFn n nl blank ys

/-- **entab-defn**: `Q≜𝟙+(V×U)`. -/
@[expose] public def Q (n : Nat) (tb nl blank : Char) :
    (F Unit Char).obj (dSL Unit Char) ⟶ (F Unit Char).obj (dSL Unit Char) :=
  fun u v => match u, v with
    | Sum.inl _, Sum.inl _ => True
    | Sum.inr p, Sum.inr q => V n nl blank p.1 q.1 ∧ U tb p.2 q.2
    | _, _ => False

/-- **entab-defn**, point-free: `Q=𝟙+(V×U)`. -/
public theorem Q_eq (n : Nat) (tb nl blank : Char) :
    Q n tb nl blank = sumMap (sumCop (dL Unit) ⟨Str × Char⟩) (sumCop (dL Unit) ⟨Str × Char⟩)
      (𝟙 (dL Unit)) (rprodMap (V n nl blank) (U tb)) := by
  apply hom_ext; intro u v
  constructor
  · intro h
    cases u with
    | inl d => cases v with
      | inl d' => exact Or.inl ⟨d, rfl, d', rfl, rfl⟩
      | inr _ => exact h.elim
    | inr p => cases v with
      | inl _ => exact h.elim
      | inr q => exact Or.inr ⟨p, rfl, q, h, rfl⟩
  · rintro (⟨_, rfl, _, _, rfl⟩ | ⟨_, rfl, _, h, rfl⟩)
    · trivial
    · exact h

public theorem pad_add (blank : Char) (x : Str) (j : Nat) :
    ∀ k, pad blank (pad blank x j) k = pad blank x (j + k)
  | 0 => rfl
  | k + 1 => by
    show SnocList.snoc (pad blank (pad blank x j) k) blank
      = SnocList.snoc (pad blank x (j + k)) blank
    rw [pad_add blank x j k]

/-- Adding `j` to `a` adds `j` to `a mod n`, as long as the sum stays inside one period. -/
public theorem mod_add_of_lt (n a j : Nat) (h : a % n + j < n) : (a + j) % n = a % n + j := by
  have hd : n * (a / n) + a % n = a := Nat.div_add_mod a n
  have he : a + j = n * (a / n) + (a % n + j) := by omega
  rw [he, Nat.mul_add_mod, Nat.mod_eq_of_lt h]

/-- `fill : String⟶String` as an arrow. -/
@[expose] public def fill (n : Nat) (nl blank : Char) : dSL Unit Char ⟶ dSL Unit Char :=
  graph (fillFn n nl blank)

/-- `π₁ : String×Char⟶String`, B&dM's `outl`. -/
@[expose] public def outl : (⟨Str × Char⟩ : RelSet.{0}) ⟶ dSL Unit Char := graph Prod.fst

/-- The coreflexive `istab outr`: the pairs whose character is `TB` — the guard of `expand`'s
    conditional, written as the union of its two guarded arms. -/
@[expose] public def istab (tb : Char) : (⟨Str × Char⟩ : RelSet.{0}) ⟶ ⟨Str × Char⟩ :=
  fun p q => p = q ∧ p.2 = tb

/-- The complementary coreflexive: the pairs whose character is not `TB`. -/
@[expose] public def nottab (tb : Char) : (⟨Str × Char⟩ : RelSet.{0}) ⟶ ⟨Str × Char⟩ :=
  fun p q => p = q ∧ p.2 ≠ tb

public theorem prefixS_refl : ∀ x : Str, prefixS x x
  | SnocList.wrap () => rfl
  | SnocList.snoc _ _ => Or.inl rfl

/-- Exercise 10.4, first claim: `nil V°=nil` — the empty string has no other prefix. -/
public theorem nil_V (n : Nat) (nl blank : Char) :
    (nil : dL Unit ⟶ dSL Unit Char) ≫ (V n nl blank)° = nil :=
  hom_ext fun _ x => ⟨fun ⟨_, hy, hpre, _⟩ => by subst hy; exact hpre,
    fun h => ⟨SnocList.wrap (), rfl, h, by rw [h]⟩⟩

/-- A filled string ends on a tab stop. -/
public theorem col_fill_mod (n : Nat) (nl blank : Char) (hn : 0 < n) (hb : blank ≠ nl) (z : Str) :
    colFn nl (fillFn n nl blank z) % n = 0 := by
  have hrz : colFn nl z % n < n := Nat.mod_lt _ hn
  have hdz : n * (colFn nl z / n) + colFn nl z % n = colFn nl z := Nat.div_add_mod _ _
  have hcoly : colFn nl (fillFn n nl blank z) = n * (colFn nl z / n + 1) := by
    show colFn nl (pad blank z (n - colFn nl z % n)) = _
    rw [col_pad nl blank hb, Nat.mul_succ]
    omega
  rw [hcoly]; exact Nat.mul_mod_right _ _

/-- A prefix `x` of `z⧺[c]` short of it that fills to the same string: then `c` is a blank inside
    the tab period, and `x` already fills to `fill z`. -/
public theorem prefix_fill_snoc (n : Nat) (nl blank : Char) (hn : 0 < n) (hb : blank ≠ nl)
    {x z : Str} {c : Char} (hpz : prefixS x z)
    (hfill : fillFn n nl blank x = fillFn n nl blank (SnocList.snoc z c)) :
    c = blank ∧ fillFn n nl blank x = fillFn n nl blank z
      ∧ colFn nl (SnocList.snoc z c) % n ≠ 0 := by
  have hlx : length x ≤ length z := prefixS_slen_le hpz
  obtain ⟨m, hm, hjk⟩ := pad_eq_pad blank x (SnocList.snoc z c) (n - colFn nl x % n)
    (n - colFn nl (SnocList.snoc z c) % n) (by show length x ≤ length z + 1; omega) hfill
  have hslen : length z + 1 = length x + m := by
    show length (SnocList.snoc z c) = length x + m
    rw [hm, slen_pad]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hsplit : SnocList.snoc z c = SnocList.snoc (pad blank x m') blank := hm
  obtain ⟨hz, hcb⟩ : z = pad blank x m' ∧ c = blank := by
    injection hsplit with h1 h2; exact ⟨h1, h2⟩
  have hcne : c ≠ nl := by rw [hcb]; exact hb
  have hcolz : colFn nl z = colFn nl x + m' := by rw [hz, col_pad nl blank hb]
  have hcol_snoc : colFn nl (SnocList.snoc z c) = colFn nl x + m' + 1 := by
    show (if c = nl then 0 else colFn nl z + 1) = colFn nl x + m' + 1
    rw [if_neg hcne, hcolz]
  rw [hcol_snoc] at hjk
  have hrx : colFn nl x % n < n := Nat.mod_lt _ hn
  have hsb : (colFn nl x + m' + 1) % n < n := Nat.mod_lt _ hn
  have hlt : colFn nl x % n + m' < n := by omega
  have hmodz : colFn nl z % n = colFn nl x % n + m' := by
    rw [hcolz]; exact mod_add_of_lt n (colFn nl x) m' hlt
  refine ⟨hcb, ?_, by rw [hcol_snoc]; omega⟩
  show pad blank x (n - colFn nl x % n) = pad blank z (n - colFn nl z % n)
  rw [hmodz, hz, pad_add]
  congr 1
  omega

/-- Exercise 10.4, second claim: `fill V°=fill` — a filled string sits on a tab stop, so its own
    `fill` is a whole `n` blanks long, which no shorter prefix can match. -/
public theorem fill_V (n : Nat) (nl blank : Char) (hn : 0 < n) (hb : blank ≠ nl) :
    fill n nl blank ≫ (V n nl blank)° = fill n nl blank :=
  hom_ext fun z x => by
    refine ⟨fun ⟨y, hy, hpre, hfill⟩ => ?_, fun h => ⟨x, h, prefixS_refl x, rfl⟩⟩
    obtain rfl : y = fillFn n nl blank z := hy
    show x = fillFn n nl blank z
    have hmod0 := col_fill_mod n nl blank hn hb z
    have hfy : fillFn n nl blank (fillFn n nl blank z) = pad blank (fillFn n nl blank z) n := by
      show pad blank (fillFn n nl blank z) (n - colFn nl (fillFn n nl blank z) % n) = _
      rw [hmod0, Nat.sub_zero]
    have hfill' : pad blank x (n - colFn nl x % n) = pad blank (fillFn n nl blank z) n :=
      hfill.trans hfy
    obtain ⟨m, hm, hjk⟩ := pad_eq_pad blank x (fillFn n nl blank z)
      (n - colFn nl x % n) n (prefixS_slen_le hpre) hfill'
    have hkx : n - colFn nl x % n ≤ n := Nat.sub_le _ _
    obtain rfl : m = 0 := by omega
    exact hm.symm

/-- Exercise 10.4, third claim: `snoc V°⊑snoc∪(π₁V°)` — a prefix of `xs⧺[a]` is the whole of it or
    a prefix of `xs`; in the second case the two fills agree only when `a` is a blank and `xs` is
    the prefix padded with blanks inside one tab period. -/
public theorem snoc_V (n : Nat) (nl blank : Char) (hn : 0 < n) (hb : blank ≠ nl) :
    snocR ≫ (V n nl blank)° ⊑ snocR ∪ outl ≫ (V n nl blank)° :=
  le_iff.mpr fun ⟨z, c⟩ x ⟨y, hy, hpre, hfill⟩ => by
    obtain rfl : y = SnocList.snoc z c := hy
    rcases (hpre : x = SnocList.snoc z c ∨ prefixS x z) with rfl | hpz
    · exact Or.inl rfl
    · exact Or.inr ⟨z, rfl, hpz, (prefix_fill_snoc n nl blank hn hb hpz hfill).2.1⟩

/-- `expand` is the conditional `(istab outr→fill outl,snoc)`, written as its two guarded arms. -/
public theorem expand_eq_cond (n : Nat) (tb nl blank : Char) :
    expand n tb nl blank = istab tb ≫ outl ≫ fill n nl blank ∪ nottab tb ≫ snocR :=
  hom_ext fun ⟨z, c⟩ y => by
    by_cases hc : c = tb
    · have e : expandFn n tb nl blank z c = fillFn n nl blank z := if_pos hc
      refine ⟨fun h => Or.inl ⟨(z, c), ⟨rfl, hc⟩, z, rfl, h.trans e⟩, fun h => ?_⟩
      rcases h with ⟨_, ⟨rfl, _⟩, _, rfl, hy⟩ | ⟨_, ⟨rfl, hq⟩, _⟩
      · exact hy.trans e.symm
      · exact absurd hc hq
    · have e : expandFn n tb nl blank z c = SnocList.snoc z c := if_neg hc
      refine ⟨fun h => Or.inr ⟨(z, c), ⟨rfl, hc⟩, h.trans e⟩, fun h => ?_⟩
      rcases h with ⟨_, ⟨rfl, hq⟩, _⟩ | ⟨_, ⟨rfl, _⟩, hy⟩
      · exact absurd hq hc
      · exact hy.trans e.symm

/-- The definition of `expand`, with the guard on the second arm dropped:
    `istab outl fill∪nottab(snoc∪X)⊑expand∪X`. -/
public theorem expand_guard_drop (n : Nat) (tb nl blank : Char) {X : _ ⟶ dSL Unit Char} :
    istab tb ≫ outl ≫ fill n nl blank ∪ nottab tb ≫ (snocR ∪ X) ⊑ expand n tb nl blank ∪ X := by
  rw [expand_eq_cond]
  refine le_iff.mpr fun p y h => ?_
  rcases h with h | ⟨_, ⟨rfl, hq⟩, hs | hw⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr ⟨p, ⟨rfl, hq⟩, hs⟩)
  · exact Or.inr hw

/-- **B&dM p.249–250, the claim** `expand V°⊑expand∪(π₁V°)`: shortening the output of one
    `expand` step to a `V`-smaller string either leaves the step alone or discards it.  One `calc`
    step per hint: the definition of `expand`, conditionals distribute, `fill V°=fill` and
    `snoc V°⊑snoc∪(π₁V°)` (Exercise 10.4), the guard dropped. -/
public theorem expand_V (n : Nat) (hn : 0 < n) :
    expand n tb nl blank ≫ (V n nl blank)° ⊑ expand n tb nl blank ∪ outl ≫ (V n nl blank)° :=
  calc expand n tb nl blank ≫ (V n nl blank)°
      = (istab tb ≫ outl ≫ fill n nl blank ∪ nottab tb ≫ snocR) ≫ (V n nl blank)° := by
        rw [expand_eq_cond]
    _ = istab tb ≫ outl ≫ fill n nl blank ≫ (V n nl blank)°
        ∪ nottab tb ≫ snocR ≫ (V n nl blank)° := by
        simpa only [Cat.assoc] using (union_comp_distrib _ _ _ :
          (istab tb ≫ outl ≫ fill n nl blank ∪ nottab tb ≫ snocR) ≫ (V n nl blank)° = _)
    _ = istab tb ≫ outl ≫ fill n nl blank ∪ nottab tb ≫ snocR ≫ (V n nl blank)° := by
        rw [fill_V n nl blank hn (by decide)]
    _ ⊑ istab tb ≫ outl ≫ fill n nl blank ∪ nottab tb ≫ (snocR ∪ outl ≫ (V n nl blank)°) :=
        union_mono (le_refl _) (comp_mono_left _ (snoc_V n nl blank hn (by decide)))
    _ ⊑ expand n tb nl blank ∪ outl ≫ (V n nl blank)° := expand_guard_drop n tb nl blank

calc_steps expand_V

/-- **entab-laws**: `detab V°⊑R° detab` read on points — shortening the output to a `V`-smaller
    string is matched by an input no longer than the original.  Induction on the input,
    `expand_V` at each step. -/
public theorem detab_V (n : Nat) (hn : 0 < n) :
    ∀ (t x : Str), V n nl blank x (detabFn n tb nl blank t) →
      ∃ t₀, detabFn n tb nl blank t₀ = x ∧ length t₀ ≤ length t
  | SnocList.wrap _, x, h => by
    obtain rfl : x = SnocList.wrap () := h.1
    exact ⟨SnocList.wrap (), rfl, Nat.le_refl _⟩
  | SnocList.snoc s c, x, h => by
    rcases le_iff.mp (expand_V n hn) (detabFn n tb nl blank s, c) x
      ⟨_, rfl, h⟩ with hx | ⟨_, rfl, hV⟩
    · exact ⟨SnocList.snoc s c, hx.symm, Nat.le_refl _⟩
    · obtain ⟨t₀, ht₀, hlen⟩ := detab_V n hn s x hV
      exact ⟨t₀, ht₀, Nat.le_succ_of_le hlen⟩

/-- `α°α=𝟙`: every snoc-list is `nil` or a `snoc`, in exactly one way. -/
public theorem con_recip_con :
    (graph (con (L := Unit) (E := Char)))° ≫ graph con = 𝟙 (dSL Unit Char) :=
  hom_ext fun t t' => ⟨fun ⟨_, h1, h2⟩ => h1.trans h2.symm, fun h => by
    subst h
    cases t with
    | wrap d => exact ⟨Sum.inl d, rfl, rfl⟩
    | snoc x a => exact ⟨Sum.inr (x, a), rfl, rfl⟩⟩

/-- `detab` is a fold, so it is the unique solution of its recursion equation:
    `detab=α°F(detab)[nil,expand]`. -/
public theorem detab_unfold (n : Nat) (tb nl blank : Char) :
    detabR n tb nl blank
      = (junc (sumCop _ _) nil snocR : (F Unit Char).obj (dSL Unit Char) ⟶ dSL Unit Char)°
        ≫ (F Unit Char).map (detabR n tb nl blank) ≫ junc (sumCop _ _) nil (expand n tb nl blank) := by
  have hc : detabR n tb nl blank = cataR (graph (expandAlgFn n tb nl blank)) :=
    (detab_cata n tb nl blank).symm
  have hcomm : (F Unit Char).map (cataR (graph (expandAlgFn n tb nl blank)))
        ≫ graph (expandAlgFn n tb nl blank)
      = graph con ≫ cataR (graph (expandAlgFn n tb nl blank)) :=
    (cataFold_comm (graph (expandAlgFn n tb nl blank))).symm
  rw [← con_eq_junc, ← expandAlg_eq_junc, hc, hcomm, ← Cat.assoc, con_recip_con, Cat.id_comp]

/-- Distributing `∪`; the fold again, and the definition of `F`:
    `α°F(detab)[nil,expand∪X]=detab∪snoc°(detab×𝟙)X`. -/
public theorem detab_unfold_union (n : Nat) (tb nl blank : Char) {X : _ ⟶ dSL Unit Char} :
    (junc (sumCop _ _) nil snocR : (F Unit Char).obj (dSL Unit Char) ⟶ dSL Unit Char)°
        ≫ (F Unit Char).map (detabR n tb nl blank)
        ≫ junc (sumCop _ _) nil (expand n tb nl blank ∪ X)
      = detabR n tb nl blank
        ∪ snocR° ≫ rprodMap (detabR n tb nl blank) (𝟙 (⟨Char⟩ : RelSet.{0})) ≫ X :=
  hom_ext fun t x => by
    constructor
    · rintro ⟨u, hα, v, hF, hj⟩
      rcases hα with ⟨d, rfl, hn⟩ | ⟨p, rfl, hs⟩
      · cases v with
        | inr _ => exact hF.elim
        | inl _ =>
          rcases hj with ⟨_, _, hn'⟩ | ⟨_, hq, _⟩
          · subst hn; subst hn'; exact Or.inl rfl
          · cases hq
      · cases v with
        | inl _ => exact hF.elim
        | inr q =>
          rcases hj with ⟨_, hq, _⟩ | ⟨q', hq', hEW⟩
          · cases hq
          · obtain rfl : q = q' := Sum.inr.inj hq'
            obtain ⟨h1, h2⟩ := hF
            rcases hEW with hx | hX
            · subst hs
              refine Or.inl ?_
              show x = expandFn n tb nl blank (detabFn n tb nl blank p.1) p.2
              rw [hx, ← h1, h2]
            · exact Or.inr ⟨p, hs, q, ⟨h1, h2⟩, hX⟩
    · rintro (h | ⟨p, hs, q, ⟨h1, h2⟩, hX⟩)
      · cases t with
        | wrap d =>
          cases d
          exact ⟨Sum.inl (), Or.inl ⟨(), rfl, rfl⟩, Sum.inl (), rfl, Or.inl ⟨(), rfl, h⟩⟩
        | snoc s a =>
          exact ⟨Sum.inr (s, a), Or.inr ⟨(s, a), rfl, rfl⟩, Sum.inr (detabFn n tb nl blank s, a),
            ⟨rfl, rfl⟩, Or.inr ⟨(detabFn n tb nl blank s, a), rfl, Or.inl h⟩⟩
      · exact ⟨Sum.inr p, Or.inr ⟨p, rfl, hs⟩, Sum.inr q, ⟨h1, h2⟩,
          Or.inr ⟨q, rfl, Or.inr hX⟩⟩

/-- Naturality of `π₁`, `(detab×𝟙)π₁=π₁ detab`, after `snoc°`. -/
public theorem detab_init_natural (n : Nat) (tb nl blank : Char)
    {Y : dSL Unit Char ⟶ dSL Unit Char} :
    snocR° ≫ rprodMap (detabR n tb nl blank) (𝟙 (⟨Char⟩ : RelSet.{0})) ≫ outl ≫ Y
      = snocR° ≫ outl ≫ detabR n tb nl blank ≫ Y :=
  hom_ext fun _ _ =>
    ⟨fun ⟨p, hs, _, ⟨h1, _⟩, w, hw, hV⟩ => ⟨p, hs, p.1, rfl, w, hw.trans h1, hV⟩,
     fun ⟨p, hs, w, hw, y, hy, hV⟩ =>
      ⟨p, hs, (y, p.2), ⟨by show y = detabFn n tb nl blank p.1; rw [hy, hw], rfl⟩, y, rfl, hV⟩⟩

/-- `X≜detab V°` solves `X⊑detab∪(init X)`; `init` is inductive, so every solution lies below the
    greatest, `prefix detab` — induction on the input, `detab_V` — and a prefix is no longer:
    `prefix⊑R°`. -/
public theorem detab_V_induction (n : Nat) (hn : 0 < n) :
    detabR n tb nl blank ∪ snocR° ≫ outl ≫ detabR n tb nl blank ≫ (V n nl blank)°
      ⊑ R° ≫ detabR n tb nl blank :=
  le_iff.mpr fun t x h => by
    rcases h with h | ⟨p, hs, _, rfl, _, rfl, hV⟩
    · exact ⟨t, Nat.le_refl _, h⟩
    · obtain ⟨t₀, ht₀, hlen⟩ := detab_V n hn p.1 x hV
      subst hs
      exact ⟨t₀, Nat.le_succ_of_le hlen, ht₀.symm⟩

/-- **B&dM p.249** `V detab⊑detab R`, mirrored: `detab V°⊑R° detab` — the book's chain, one `calc`
    step per hint. -/
public theorem detab_V_R (n : Nat) (hn : 0 < n) :
    detabR n tb nl blank ≫ (V n nl blank)° ⊑ R° ≫ detabR n tb nl blank :=
  calc detabR n tb nl blank ≫ (V n nl blank)°
      = (junc (sumCop _ _) nil snocR : (F Unit Char).obj (dSL Unit Char) ⟶ dSL Unit Char)°
        ≫ (F Unit Char).map (detabR n tb nl blank)
        ≫ junc (sumCop _ _) nil (expand n tb nl blank) ≫ (V n nl blank)° := by
        simpa only [Cat.assoc] using congrArg (· ≫ (V n nl blank)°) (detab_unfold n tb nl blank)
    _ = (junc (sumCop _ _) nil snocR : (F Unit Char).obj (dSL Unit Char) ⟶ dSL Unit Char)°
        ≫ (F Unit Char).map (detabR n tb nl blank)
        ≫ junc (sumCop _ _) (nil ≫ (V n nl blank)°) (expand n tb nl blank ≫ (V n nl blank)°) := by
        rw [junc_comp]
    _ = (junc (sumCop _ _) nil snocR : (F Unit Char).obj (dSL Unit Char) ⟶ dSL Unit Char)°
        ≫ (F Unit Char).map (detabR n tb nl blank)
        ≫ junc (sumCop _ _) nil (expand n tb nl blank ≫ (V n nl blank)°) := by
        rw [nil_V]
    _ ⊑ (junc (sumCop _ _) nil snocR : (F Unit Char).obj (dSL Unit Char) ⟶ dSL Unit Char)°
        ≫ (F Unit Char).map (detabR n tb nl blank)
        ≫ junc (sumCop _ _) nil (expand n tb nl blank ∪ outl ≫ (V n nl blank)°) :=
        comp_mono_left _ (comp_mono_left _
          (union_mono (le_refl _) (comp_mono_left _ (expand_V n hn))))
    _ = detabR n tb nl blank
        ∪ snocR° ≫ rprodMap (detabR n tb nl blank) (𝟙 (⟨Char⟩ : RelSet.{0}))
          ≫ outl ≫ (V n nl blank)° := detab_unfold_union n tb nl blank
    _ = detabR n tb nl blank ∪ snocR° ≫ outl ≫ detabR n tb nl blank ≫ (V n nl blank)° := by
        rw [detab_init_natural]
    _ ⊑ R° ≫ detabR n tb nl blank := detab_V_induction n hn

calc_steps detab_V_R

/-- **entab-laws**: Proposition 9.4's `hV`, `V detab°⊑detab° R` — `detab_V_R` conversed. -/
public theorem entab_V (n : Nat) (hn : 0 < n) :
    V n nl blank ≫ (detabR n tb nl blank)° ⊑ (detabR n tb nl blank)° ≫ R :=
  le_iff.mpr fun x t ⟨y, hV, hy⟩ =>
    let ⟨t₀, hR, hd⟩ := le_iff.mp (detab_V_R n hn) t x ⟨y, hy, hV⟩
    ⟨t₀, hd, hR⟩

/-- **entab-laws**, second row: `F(⊤,R)α⊑αR`, the note's exercise — `snoc` adds one character
    to both sides, so it never reverses `≤` on lengths, whatever the two characters are. -/
public theorem entab_mono : Freyd.Alg.Pres (F := F Unit Char) (graph con) R :=
  le_iff.mpr fun u out h => by
    obtain ⟨v, hFv, hout⟩ := h
    obtain rfl : out = con v := hout
    cases u with
    | inl _ =>
      cases v with
      | inl _ => exact ⟨SnocList.wrap (), rfl, Nat.le_refl _⟩
      | inr _ => exact hFv.elim
    | inr p =>
      cases v with
      | inl _ => exact hFv.elim
      | inr q =>
        refine ⟨SnocList.snoc p.1 p.2, rfl, ?_⟩
        show length p.1 + 1 ≤ length q.1 + 1
        exact Nat.succ_le_succ (hFv.1 : length p.1 ≤ length q.1)

public theorem R_trans : R ≫ R ⊑ R :=
  le_iff.mpr fun u w h => by
    obtain ⟨v, h1, h2⟩ := h
    exact Nat.le_trans (h1 : length u ≤ length v) (h2 : length v ≤ length w)

/-- **entab-laws**, second row: Theorem 10.1's greedy condition, Proposition 9.4 at `U` and
    `V≜prefix°∩(fill fill°)`.  `U` leaves the character free — `entab_V` supplies the shorter
    input for the `V`-smaller output, and `snoc` lengthens both sides by one. -/
public theorem entab_thin_condition (n : Nat) (hn : 0 < n) :
    Q n tb nl blank ≫ (F Unit Char).map ((detabR n tb nl blank)°) ≫ graph con
      ⊑ (F Unit Char).map ((detabR n tb nl blank)°) ≫ graph con ≫ R :=
  le_iff.mpr fun u out h => by
    obtain ⟨v, hQ, w, hFw, hout⟩ := h
    cases u with
    | inl _ =>
      cases v with
      | inr _ => exact hQ.elim
      | inl _ =>
        cases w with
        | inr _ => exact hFw.elim
        | inl _ =>
          obtain rfl : out = SnocList.wrap () := hout
          exact ⟨Sum.inl (), rfl, SnocList.wrap (), rfl, Nat.le_refl _⟩
    | inr p =>
      cases v with
      | inl _ => exact hQ.elim
      | inr q =>
        cases w with
        | inl _ => exact hFw.elim
        | inr r =>
          obtain rfl : out = SnocList.snoc r.1 r.2 := hout
          obtain ⟨t₀, ht₀, hlen⟩ := le_iff.mp (entab_V n hn) p.1 r.1
            ⟨q.1, hQ.1, (hFw.1 : q.1 = detabFn n tb nl blank r.1)⟩
          refine ⟨Sum.inr (t₀, p.2), ⟨ht₀, rfl⟩, SnocList.snoc t₀ p.2, rfl, ?_⟩
          show length t₀ + 1 ≤ length r.1 + 1
          exact Nat.succ_le_succ hlen

/-- `H = ⦇α⦈·⦇[nil,expand]⦈°` collapses to `detab°` by reflection (`AOP.A6_SnocList.cataR_con`). -/
public theorem entab_H (n : Nat) (tb nl blank : Char) :
    (relCata (F := F Unit Char) (graph (expandAlgFn n tb nl blank)))°
        ≫ relCata (F := F Unit Char) (I := initial Unit Char)
            (graph (con (L := Unit) (E := Char)))
      = Allegory.recip (detabR n tb nl blank) := by
  rw [← cataR_eq_relCata, ← cataR_eq_relCata, cataR_con, detab_cata]
  exact Cat.comp_id _

/-- **entab-laws**, the prefixed point (Theorem 10.1 at `Q≜𝟙+(V×U)`): at `X≜Λ(detab°) est(R)` the
    greedy body is below `X`, so the least fixed point `entab_laws` is too. -/
public theorem entab_laws_prefixed (n : Nat) (hn : 0 < n)
    {X : dSL Unit Char ⟶ dSL Unit Char}
    (hX : X = Λ (Allegory.recip (detabR n tb nl blank)) ≫ est R) :
    Λ ((junc (sumCop _ _) nil (expand n tb nl blank)
        : (F Unit Char).obj (dSL Unit Char) ⟶ dSL Unit Char)°)
      ≫ est (Q n tb nl blank) ≫ (F Unit Char).map X ≫ junc (sumCop _ _) nil snocR
      ⊑ Λ (Allegory.recip (detabR n tb nl blank)) ≫ est R := by
  subst hX
  rw [← expandAlg_eq_junc, ← con_eq_junc]
  have e : _root_.Freyd.Alg.H (F := F Unit Char) (graph (expandAlgFn n tb nl blank))
      (graph (con (L := Unit) (E := Char))) = (detabR n tb nl blank)° := entab_H n tb nl blank
  rw [← e]
  exact greedy_dp_prefixed (graph_map con) entab_mono R_trans
    (by unfold ThinCondition; rw [e]; exact entab_thin_condition n hn)

/-- **entab-laws**, second row (B&dM p.247): the shortest input `detab` expands to the given
    output is the least fixed point of `(μX : [nil,expand]° est(Q)(𝟙+(X×𝟙))[nil,snoc])` —
    Theorem 10.1 at `Q≜𝟙+(V×U)`, one character of input decided at each step.
    `H = ⦇α⦈·⦇[nil,expand]⦈°` collapses to `detab°` by reflection
    (`AOP.A6_SnocList.cataR_con`). -/
public theorem entab_laws (n : Nat) (hn : 0 < n) :
    mu (fun X : dSL Unit Char ⟶ dSL Unit Char =>
        Λ ((junc (sumCop _ _) nil (expand n tb nl blank)
            : (F Unit Char).obj (dSL Unit Char) ⟶ dSL Unit Char)°)
          ≫ est (Q n tb nl blank) ≫ (F Unit Char).map X ≫ junc (sumCop _ _) nil snocR)
      ⊑ Λ (Allegory.recip (detabR n tb nl blank)) ≫ est R :=
  mu_le (entab_laws_prefixed n hn rfl)

/-- `expand` never returns the empty string: on a tab it fills at least one blank (the column is
    `< n` after `%`), on any other character it snocs.  This is B&dM's Proposition 10.1
    hypothesis `nil` and `expand` have disjoint ranges. -/
public theorem expand_ne_nil (n : Nat) (tb nl blank : Char) (hn : 0 < n) (x : Str) (a : Char) :
    expandFn n tb nl blank x a ≠ SnocList.wrap () := by
  unfold expandFn
  split
  · unfold fillFn
    obtain ⟨k, hk⟩ : ∃ k, n - colFn nl x % n = k + 1 :=
      ⟨n - colFn nl x % n - 1, by have := Nat.mod_lt (colFn nl x) hn; omega⟩
    rw [hk]
    show SnocList.snoc (pad blank x k) blank ≠ SnocList.wrap ()
    intro h; cases h
  · intro h; cases h

/-- **entab-laws**, third row (Proposition 10.1): with `nil` and `expand` of disjoint ranges the
    branch `(expand°)%∋ est(V×U)(X×𝟙)snoc` refines `entab_laws`' body
    `([nil,expand]°)%∋ est(Q)[nil,(X×𝟙)snoc]` — `AOP.A9_1.est_arm₂_le` at `[nil,expand]`, whose
    `Q₂` at `Q≜𝟙+(V×U)` is `V×U`. -/
public theorem entab_branch (n : Nat) (hn : 0 < n)
    (X : dSL Unit Char ⟶ dSL Unit Char) :
    Λ ((expand n tb nl blank)°) ≫ est (rprodMap (V n nl blank) (U tb))
        ≫ rprodMap X (𝟙 (⟨Char⟩ : RelSet.{0})) ≫ snocR
      ⊑ Λ ((junc (sumCop _ _) nil (expand n tb nl blank)
            : (F Unit Char).obj (dSL Unit Char) ⟶ dSL Unit Char)°) ≫ est (Q n tb nl blank)
          ≫ (F Unit Char).map X ≫ junc (sumCop _ _) nil snocR := by
  rw [← expandAlg_eq_junc, ← con_eq_junc]
  exact est_arm₂_le (X := X) (Q := Q n tb nl blank)
    (T := graph (expandAlgFn n tb nl blank)) (U := graph (con (L := Unit) (E := Char)))
    fun _d p y h1 h2 =>
      expand_ne_nil n tb nl blank hn p.1 p.2 (Eq.trans (Eq.symm (h2 : y = _)) (h1 : y = _))

/-! ## The `detab` program (B&dM p.247): tupling with `col`, and the loop -/

/-- `col : String⟶ℕ` as an arrow. -/
@[expose] public def colR (nl : Char) : dSL Unit Char ⟶ (⟨Nat⟩ : RelSet.{0}) := graph (colFn nl)

-- The tupled carrier `(output so far, current column)`.

/-- `step((x,c),a)`: append `a`, resetting the column on a newline and padding to the next tab
    stop on a tab. -/
@[expose] public def step (n : Nat) (tb nl blank : Char) : (Str × Nat) × Char → Str × Nat
  | ((x, c), a) =>
      if a = nl then (SnocList.snoc x nl, 0)
      else if a = tb then (pad blank x (n - c % n), c + (n - c % n))
      else (SnocList.snoc x a, c + 1)

/-- `[base,step]` with `base=([],0)`. -/
@[expose] public def stepFn (n : Nat) (tb nl blank : Char) :
    (Fobj Unit Char (⟨Str × Nat⟩ : RelSet.{0})).carrier → Str × Nat
  | Sum.inl _ => (SnocList.wrap (), 0)
  | Sum.inr p => step n tb nl blank p

/-- `[base,step] : F(String×ℕ)⟶String×ℕ` as an arrow. -/
@[expose] public def detabAlg (n : Nat) (tb nl blank : Char) : Fobj Unit Char (⟨Str × Nat⟩ : RelSet.{0}) ⟶ (⟨Str × Nat⟩ : RelSet.{0}) :=
  graph (stepFn n tb nl blank)

/-- `step` on `(detab x, col(detab x))` is `(detab, col·detab)` one character further. -/
public theorem stepFn_detab (n : Nat) (tb nl blank : Char) (hb : blank ≠ nl) (htb : tb ≠ nl)
    (d : Str) (a : Char) :
    stepFn n tb nl blank (Sum.inr ((d, colFn nl d), a))
      = (expandFn n tb nl blank d a, colFn nl (expandFn n tb nl blank d a)) := by
  by_cases h1 : a = nl
  · have e : expandFn n tb nl blank d a = SnocList.snoc d a := if_neg fun h => htb (h.symm.trans h1)
    rw [e]
    show (if a = nl then (SnocList.snoc d nl, 0) else _) = (SnocList.snoc d a, if a = nl then 0 else colFn nl d + 1)
    rw [if_pos h1, if_pos h1, h1]
  · by_cases h2 : a = tb
    · have e : expandFn n tb nl blank d a = pad blank d (n - colFn nl d % n) := if_pos h2
      rw [e, col_pad nl blank hb]
      show (if a = nl then _ else if a = tb then
        (pad blank d (n - colFn nl d % n), colFn nl d + (n - colFn nl d % n)) else _) = _
      rw [if_neg h1, if_pos h2]
    · have e : expandFn n tb nl blank d a = SnocList.snoc d a := if_neg h2
      rw [e]
      show (if a = nl then _ else if a = tb then _ else (SnocList.snoc d a, colFn nl d + 1))
        = (SnocList.snoc d a, if a = nl then 0 else colFn nl d + 1)
      rw [if_neg h1, if_neg h2, if_neg h1]

/-- The tupled function `(detab, col·detab)`. -/
@[expose] public def detabColFn (n : Nat) (tb nl blank : Char) (t : Str) : Str × Nat :=
  (detabFn n tb nl blank t, colFn nl (detabFn n tb nl blank t))

public theorem detabAlg_cata (n : Nat) (tb nl blank : Char) (hb : blank ≠ nl) (htb : tb ≠ nl) :
    cataR (detabAlg n tb nl blank) = (graph (detabColFn n tb nl blank) : dSL Unit Char ⟶ (⟨Str × Nat⟩ : RelSet.{0})) :=
  cataR_graph _ _ (fun _ => rfl) (fun _ a => (stepFn_detab n tb nl blank hb htb _ a).symm)

/-- **B&dM p.247**, tupling: `(detab, col·detab)=⦇[base,step]⦈`, in diagram order. -/
public theorem detab_tupled (n : Nat) :
    rpair (detabR n tb nl blank) (detabR n tb nl blank ≫ colR nl) = cataR (detabAlg n tb nl blank) := by
  rw [detabAlg_cata n tb nl blank (by decide) (by decide), detabR, colR, graph_comp]
  exact rpair_graph _ _

/-- B&dM p.247's `loop`: `loop f (s,[])=s`, `loop f (s,a:x)=loop f (f(s,a),x)` — a left fold. -/
@[expose] public def loop {S A : Type} (f : S × A → S) (p : S × List A) : S :=
  p.2.foldl (fun s a => f (s, a)) p.1

public theorem detabCol_foldl (n : Nat) (tb nl blank : Char) (hb : blank ≠ nl) (htb : tb ≠ nl) :
    ∀ (l : List Char) (t : Str),
      detabColFn n tb nl blank (l.foldl (fun x a => SnocList.snoc x a) t)
        = loop (step n tb nl blank) (detabColFn n tb nl blank t, l)
  | [], _ => rfl
  | a :: l, t => by
    rw [List.foldl_cons, detabCol_foldl n tb nl blank hb htb l]
    exact congrArg (fun s => loop (step n tb nl blank) (s, l))
      (stepFn_detab n tb nl blank hb htb (detabFn n tb nl blank t) a).symm

/-- **B&dM p.247**: `⦇[base,step]⦈ convert=loop step (base,id)` — `ofChars` is `convert`. -/
public theorem detab_loop (n : Nat)
    (xs : List Char) (r : Str × Nat) :
    cataR (detabAlg n tb nl blank) (ofChars xs) r
      ↔ r = loop (step n tb nl blank) ((SnocList.wrap (), 0), xs) := by
  rw [detabAlg_cata n tb nl blank (by decide) (by decide)]
  show r = detabColFn n tb nl blank (ofChars xs) ↔ _
  rw [ofChars, detabCol_foldl n tb nl blank (by decide) (by decide)]
  exact Iff.rfl

/-- B&dM p.247's `loop'`: `loop'(f,g)(c,[])=[]`, `loop'(f,g)(c,a:x)=f(c,a)⧺loop'(f,g)(g(c,a),x)`. -/
@[expose] public def loop' {C A B : Type} (f : C × A → List B) (g : C × A → C) :
    C × List A → List B
  | (_, []) => []
  | (c, a :: x) => f (c, a) ++ loop' f g (g (c, a), x)

/-- Exercise 10.1's `step((y,c),a)=(y⧺f(c,a),g(c,a))`. -/
@[expose] public def loopStep {C A B : Type} (f : C × A → List B) (g : C × A → C) :
    (List B × C) × A → List B × C
  | ((y, c), a) => (y ++ f (c, a), g (c, a))

public theorem outl_loop_append {C A B : Type} (f : C × A → List B) (g : C × A → C) :
    ∀ (x : List A) (y : List B) (c : C),
      (loop (loopStep f g) ((y, c), x)).1 = y ++ loop' f g (c, x)
  | [], y, c => by
    show y = y ++ loop' f g (c, [])
    rw [loop'.eq_1, List.append_nil]
  | a :: x, y, c => by
    show (loop (loopStep f g) ((y ++ f (c, a), g (c, a)), x)).1 = y ++ loop' f g (c, a :: x)
    rw [loop'.eq_2, outl_loop_append f g x, List.append_assoc]

/-- **Exercise 10.1**: `outl·loop step (base,id)=loop'(f,g)(c₀,id)` when `base=(nil,c₀)` and
    `step((x,c),a)=(x⧺f(c,a),g(c,a))`. -/
public theorem outl_loop {C A B : Type} (f : C × A → List B) (g : C × A → C) (c₀ : C) (xs : List A) :
    (loop (loopStep f g) (([], c₀), xs)).1 = loop' f g (c₀, xs) :=
  (outl_loop_append f g xs [] c₀).trans (List.nil_append _)

/-! ## `entab` (B&dM pp.250–252): the greedy step, `unfill`, `tbc`, and the loop -/

public theorem prefixS_pad (blank : Char) (y : Str) : ∀ k, prefixS y (pad blank y k)
  | 0 => prefixS_refl y
  | k + 1 => Or.inr (prefixS_pad blank y k)

public theorem prefixS_eq_of_le : ∀ {x y : Str}, prefixS x y → length y ≤ length x → x = y
  | _, SnocList.wrap (), h, _ => h
  | x, SnocList.snoc y c, h, hl => by
    rcases (h : x = SnocList.snoc y c ∨ prefixS x y) with h | h
    · exact h
    · have := prefixS_slen_le h
      have : length (SnocList.snoc y c) = length y + 1 := rfl
      omega

public theorem prefixS_antisymm {x y : Str} (h1 : prefixS x y) (h2 : prefixS y x) : x = y :=
  prefixS_eq_of_le h1 (prefixS_slen_le h2)

/-- **B&dM p.250** `Λexpand°(xs⧺[a])={(ys,TB)∣fill ys=xs⧺[a]}∪{(xs,a)}`, for `a≠TB` (on `xs⧺[TB]` the
    left side is empty). -/
public theorem expand_recip_snoc (n : Nat) (tb nl blank : Char) (xs : Str) (a : Char) (ha : a ≠ tb)
    (ys : Str) (b : Char) :
    expandFn n tb nl blank ys b = SnocList.snoc xs a
      ↔ (fillFn n nl blank ys = SnocList.snoc xs a ∧ b = tb) ∨ (ys, b) = (xs, a) := by
  unfold expandFn
  by_cases hb : b = tb
  · rw [if_pos hb]
    exact ⟨fun h => Or.inl ⟨h, hb⟩,
      fun h => h.elim And.left fun h => absurd (hb.symm.trans (Prod.mk.inj h).2).symm ha⟩
  · rw [if_neg hb]
    constructor
    · intro h; injection h with h1 h2; subst h1; subst h2; exact Or.inr rfl
    · rintro (⟨_, h⟩ | h)
      · exact absurd h hb
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; rfl

/-- `fill y=x⧺[a]` puts a blank last, and `y` is a prefix of `x`. -/
public theorem fill_eq_snoc (n : Nat) (nl blank : Char) (hn : 0 < n) {y x : Str} {a : Char}
    (hy : fillFn n nl blank y = SnocList.snoc x a) : a = blank ∧ prefixS y x := by
  obtain ⟨k, hk⟩ : ∃ k, n - colFn nl y % n = k + 1 :=
    ⟨n - colFn nl y % n - 1, by have := Nat.mod_lt (colFn nl y) hn; omega⟩
  have hy' : SnocList.snoc (pad blank y k) blank = SnocList.snoc x a := by
    rw [← hy]; show _ = pad blank y (n - colFn nl y % n); rw [hk]; rfl
  injection hy' with h1 h2
  exact ⟨h2.symm, by rw [← h1]; exact prefixS_pad blank y k⟩

/-- On a tab stop, `fill x=x⧺[BL]`. -/
public theorem fill_eq_snoc_blank (n : Nat) (nl blank : Char) (hn : 0 < n) (hb : blank ≠ nl)
    (x : Str) (h0 : colFn nl (SnocList.snoc x blank) % n = 0) :
    fillFn n nl blank x = SnocList.snoc x blank := by
  have hc : colFn nl (SnocList.snoc x blank) = colFn nl x + 1 := if_neg hb
  rw [hc] at h0
  have hr := Nat.mod_lt (colFn nl x) hn
  have h1 : n - colFn nl x % n = 1 := by
    rcases Nat.lt_or_ge (colFn nl x % n + 1) n with hlt | hge
    · rw [mod_add_of_lt n _ 1 hlt] at h0; omega
    · omega
  show pad blank x (n - colFn nl x % n) = _
  rw [h1]; rfl

/-- Off a tab stop, a trailing blank does not change `fill`. -/
public theorem fill_snoc_blank (n : Nat) (nl blank : Char) (hn : 0 < n) (hb : blank ≠ nl)
    (x : Str) (h : colFn nl (SnocList.snoc x blank) % n ≠ 0) :
    fillFn n nl blank (SnocList.snoc x blank) = fillFn n nl blank x := by
  have hc : colFn nl (SnocList.snoc x blank) = colFn nl x + 1 := if_neg hb
  have hr := Nat.mod_lt (colFn nl x) hn
  have hlt : colFn nl x % n + 1 < n := by
    rcases Nat.lt_or_ge (colFn nl x % n + 1) n with h1 | h1
    · exact h1
    · exfalso; apply h; rw [hc]
      have hd := Nat.div_add_mod (colFn nl x) n
      have e : colFn nl x + 1 = n * (colFn nl x / n + 1) := by rw [Nat.mul_succ]; omega
      rw [e]; exact Nat.mul_mod_right _ _
  have hm : colFn nl (SnocList.snoc x blank) % n = colFn nl x % n + 1 := by
    rw [hc]; exact mod_add_of_lt n _ 1 hlt
  show pad blank (SnocList.snoc x blank) (n - colFn nl (SnocList.snoc x blank) % n)
    = pad blank x (n - colFn nl x % n)
  have e : n - colFn nl x % n = 1 + (n - (colFn nl x % n + 1)) := by omega
  rw [hm, e, ← pad_add]; rfl

/-- **B&dM p.250** `(∃ys: fill ys=xs⧺[a]) ≡ a=BL ∧ col(xs⧺[a]) mod n=0`. -/
public theorem fill_exists_iff (n : Nat) (hn : 0 < n)
    (xs : Str) (a : Char) :
    (∃ ys, fillFn n nl blank ys = SnocList.snoc xs a) ↔ a = blank ∧ colFn nl (SnocList.snoc xs a) % n = 0 := by
  constructor
  · rintro ⟨ys, hy⟩
    exact ⟨(fill_eq_snoc n nl blank hn hy).1, by rw [← hy]; exact col_fill_mod n nl blank hn (by decide) ys⟩
  · rintro ⟨ha, h0⟩
    rw [ha] at h0 ⊢
    exact ⟨xs, fill_eq_snoc_blank n nl blank hn (by decide) xs h0⟩

/-- **B&dM p.250** `unfill`: `unfill[]=[]`, `unfill(xs⧺[a])=unfill xs` on a blank off a tab stop,
    `xs⧺[a]` otherwise — the shortest prefix with the same `fill`. -/
@[expose] public def unfillFn (n : Nat) (nl blank : Char) : Str → Str
  | SnocList.wrap _ => SnocList.wrap ()
  | SnocList.snoc xs a =>
      if a = blank ∧ colFn nl (SnocList.snoc xs a) % n ≠ 0 then unfillFn n nl blank xs
      else SnocList.snoc xs a

public theorem unfill_prefix (n : Nat) (nl blank : Char) : ∀ x : Str, prefixS (unfillFn n nl blank x) x
  | SnocList.wrap () => rfl
  | SnocList.snoc x a => by
    by_cases h : a = blank ∧ colFn nl (SnocList.snoc x a) % n ≠ 0
    · have e : unfillFn n nl blank (SnocList.snoc x a) = unfillFn n nl blank x := if_pos h
      rw [e]; exact Or.inr (unfill_prefix n nl blank x)
    · have e : unfillFn n nl blank (SnocList.snoc x a) = SnocList.snoc x a := if_neg h
      rw [e]; exact prefixS_refl _

public theorem fill_unfill (n : Nat) (nl blank : Char) (hn : 0 < n) (hb : blank ≠ nl) :
    ∀ x : Str, fillFn n nl blank (unfillFn n nl blank x) = fillFn n nl blank x
  | SnocList.wrap () => rfl
  | SnocList.snoc x a => by
    by_cases h : a = blank ∧ colFn nl (SnocList.snoc x a) % n ≠ 0
    · have e : unfillFn n nl blank (SnocList.snoc x a) = unfillFn n nl blank x := if_pos h
      have h2 : colFn nl (SnocList.snoc x blank) % n ≠ 0 := by rw [← h.1]; exact h.2
      rw [e, fill_unfill n nl blank hn hb x, h.1, fill_snoc_blank n nl blank hn hb x h2]
    · have e : unfillFn n nl blank (SnocList.snoc x a) = SnocList.snoc x a := if_neg h
      rw [e]

/-- `unfill x` is below every prefix of `x` with the same `fill`. -/
public theorem unfill_least (n : Nat) (nl blank : Char) (hn : 0 < n) (hb : blank ≠ nl) :
    ∀ (x y : Str), prefixS y x → fillFn n nl blank y = fillFn n nl blank x →
      prefixS (unfillFn n nl blank x) y
  | SnocList.wrap (), y, hp, _ => by rw [(hp : y = SnocList.wrap ())]; exact rfl
  | SnocList.snoc z c, y, hp, hf => by
    rcases (hp : y = SnocList.snoc z c ∨ prefixS y z) with rfl | hpz
    · exact unfill_prefix n nl blank _
    · obtain ⟨hc, hfz, hne⟩ := prefix_fill_snoc n nl blank hn hb hpz hf
      have e : unfillFn n nl blank (SnocList.snoc z c) = unfillFn n nl blank z := if_pos ⟨hc, hne⟩
      rw [e]; exact unfill_least n nl blank hn hb z y hpz hfz

/-- **B&dM p.250** `min V{y∣fill y=x⧺[BL]}=unfill x` on a tab stop (the set's pairs all carry
    `TB`, so their `V×U`-least is this one's). -/
public theorem unfill_est (n : Nat) (nl blank : Char) (hn : 0 < n) (hb : blank ≠ nl) (x : Str)
    (h0 : colFn nl (SnocList.snoc x blank) % n = 0) (w : Str) :
    (Λ ((fill n nl blank)°) ≫ est (V n nl blank)) (SnocList.snoc x blank) w
      ↔ w = unfillFn n nl blank x := by
  rw [Λ_comp_est_apply]
  have hfx := fill_eq_snoc_blank n nl blank hn hb x h0
  have hmemU : SnocList.snoc x blank = fillFn n nl blank (unfillFn n nl blank x) :=
    ((fill_unfill n nl blank hn hb x).trans hfx).symm
  have below : ∀ z, SnocList.snoc x blank = fillFn n nl blank z → V n nl blank (unfillFn n nl blank x) z :=
    fun z hz => ⟨unfill_least n nl blank hn hb x z (fill_eq_snoc n nl blank hn hz.symm).2
      (hz.symm.trans hfx.symm), hmemU.symm.trans hz⟩
  constructor
  · rintro ⟨hw, hmin⟩
    exact prefixS_antisymm (hmin _ hmemU).1 (below w hw).1
  · rintro rfl; exact ⟨hmemU, below⟩

/-- **B&dM pp.250–251** `contract`: the greedy choice for the last character. -/
@[expose] public def contractFn (n : Nat) (tb nl blank : Char) (x : Str) (a : Char) : Str × Char :=
  if a = blank ∧ colFn nl (SnocList.snoc x a) % n = 0 then (unfillFn n nl blank x, tb) else (x, a)

/-- **B&dM p.250**, the case split: `min(V×U)Λexpand°(x⧺[a])` is `(unfill x,TB)` when `a=BL` and
    `col(x⧺[a]) mod n=0`, and `(x,a)` otherwise (for `a≠TB`). -/
public theorem entab_step (n : Nat) (hn : 0 < n)
    (x : Str) (a : Char) (ha : a ≠ tb) (p : Str × Char) :
    (Λ ((expand n tb nl blank)°) ≫ est (rprodMap (V n nl blank) (U tb))) (SnocList.snoc x a) p
      ↔ p = contractFn n tb nl blank x a := by
  rw [Λ_comp_est_apply]
  have mem : ∀ q : Str × Char, (expand n tb nl blank)° (SnocList.snoc x a) q ↔
      (fillFn n nl blank q.1 = SnocList.snoc x a ∧ q.2 = tb) ∨ q = (x, a) :=
    fun q => eq_comm.trans (expand_recip_snoc n tb nl blank x a ha q.1 q.2)
  unfold contractFn
  by_cases hc : a = blank ∧ colFn nl (SnocList.snoc x a) % n = 0
  · rw [if_pos hc]
    have hfx : fillFn n nl blank x = SnocList.snoc x a := by
      have h0 := hc.2; rw [hc.1] at h0 ⊢; exact fill_eq_snoc_blank n nl blank hn (by decide) x h0
    have hmemU : fillFn n nl blank (unfillFn n nl blank x) = SnocList.snoc x a :=
      (fill_unfill n nl blank hn (by decide) x).trans hfx
    have below : ∀ q : Str × Char, ((fillFn n nl blank q.1 = SnocList.snoc x a ∧ q.2 = tb) ∨ q = (x, a))
        → V n nl blank (unfillFn n nl blank x) q.1 ∧ U tb tb q.2 := by
      rintro q (⟨hq, _⟩ | rfl)
      · exact ⟨⟨unfill_least n nl blank hn (by decide) x q.1 (fill_eq_snoc n nl blank hn hq).2
          (hq.trans hfx.symm), hmemU.trans hq.symm⟩, Or.inl rfl⟩
      · exact ⟨⟨unfill_prefix n nl blank x, fill_unfill n nl blank hn (by decide) x⟩, Or.inl rfl⟩
    constructor
    · rintro ⟨hp, hmin⟩
      have h1 := hmin (unfillFn n nl blank x, tb) ((mem _).mpr (Or.inl ⟨hmemU, rfl⟩))
      have hp2 : p.2 = tb := h1.2.elim id id
      rcases (mem p).mp hp with ⟨hq, _⟩ | hpx
      · exact Prod.ext (prefixS_antisymm h1.1.1 (below p (Or.inl ⟨hq, hp2⟩)).1.1) hp2
      · subst hpx; exact absurd hp2 ha
    · rintro rfl
      exact ⟨(mem _).mpr (Or.inl ⟨hmemU, rfl⟩), fun q hq => below q ((mem q).mp hq)⟩
  · rw [if_neg hc]
    have hno : ∀ q : Str × Char, ¬ (fillFn n nl blank q.1 = SnocList.snoc x a ∧ q.2 = tb) :=
      fun q ⟨hq, _⟩ => hc ((fill_exists_iff n hn x a).mp ⟨q.1, hq⟩)
    constructor
    · rintro ⟨hp, _⟩; exact ((mem p).mp hp).resolve_left (hno p)
    · rintro rfl
      refine ⟨(mem _).mpr (Or.inr rfl), fun q hq => ?_⟩
      obtain rfl := ((mem q).mp hq).resolve_left (hno q)
      exact ⟨⟨prefixS_refl x, rfl⟩, Or.inr rfl⟩

public theorem contract_slen_le (n : Nat) (tb nl blank : Char) (x : Str) (a : Char) :
    length (contractFn n tb nl blank x a).1 ≤ length x := by
  unfold contractFn; split
  · exact prefixS_slen_le (unfill_prefix n nl blank x)
  · exact Nat.le_refl _

/-- **B&dM p.251** the greedy program: `entab[]=[]`, `entab(x⧺[a])=entab y⧺[b]` where
    `(y,b)=contract(x,a)`. -/
@[expose] public def entabFn (n : Nat) (tb nl blank : Char) : Str → Str
  | SnocList.wrap _ => SnocList.wrap ()
  | SnocList.snoc x a =>
      SnocList.snoc (entabFn n tb nl blank (contractFn n tb nl blank x a).1)
        (contractFn n tb nl blank x a).2
termination_by x => length x
decreasing_by
  show length (contractFn n tb nl blank x a).1 < length x + 1
  exact Nat.lt_succ_of_le (contract_slen_le n tb nl blank x a)

/-- **B&dM p.251** `tbc`, the trailing blank count. -/
@[expose] public def tbcFn (n : Nat) (nl blank : Char) : Str → Nat
  | SnocList.wrap _ => 0
  | SnocList.snoc xs a =>
      if a = blank ∧ colFn nl (SnocList.snoc xs a) % n ≠ 0 then tbcFn n nl blank xs + 1 else 0

/-- **B&dM p.251**: `tbc[]=0`. -/
public theorem tbc_nil (n : Nat) (nl blank : Char) : tbcFn n nl blank (SnocList.wrap ()) = 0 := rfl

/-- **B&dM p.251**: `tbc(xs⧺[a])=tbc xs+1` on a blank off a tab stop, `0` otherwise. -/
public theorem tbc_snoc (n : Nat) (nl blank : Char) (xs : Str) (a : Char) :
    tbcFn n nl blank (SnocList.snoc xs a)
      = if a = blank ∧ colFn nl (SnocList.snoc xs a) % n ≠ 0 then tbcFn n nl blank xs + 1 else 0 := rfl

/-- **(10.1)**, B&dM p.251: `entab xs=entab(unfill xs)⧺blanks(tbc xs)`. -/
public theorem entab_unfill (n : Nat) (tb nl blank : Char) : ∀ xs : Str,
    entabFn n tb nl blank xs = pad blank (entabFn n tb nl blank (unfillFn n nl blank xs)) (tbcFn n nl blank xs)
  | SnocList.wrap () => rfl
  | SnocList.snoc z a => by
    by_cases h : a = blank ∧ colFn nl (SnocList.snoc z a) % n ≠ 0
    · have eu : unfillFn n nl blank (SnocList.snoc z a) = unfillFn n nl blank z := if_pos h
      have et : tbcFn n nl blank (SnocList.snoc z a) = tbcFn n nl blank z + 1 := if_pos h
      have ec : contractFn n tb nl blank z a = (z, a) := if_neg fun h' => h.2 h'.2
      rw [eu, et, entabFn.eq_2, ec]
      show SnocList.snoc (entabFn n tb nl blank z) a
        = SnocList.snoc (pad blank (entabFn n tb nl blank (unfillFn n nl blank z)) (tbcFn n nl blank z)) blank
      rw [← entab_unfill n tb nl blank z, h.1]
    · have eu : unfillFn n nl blank (SnocList.snoc z a) = SnocList.snoc z a := if_neg h
      have et : tbcFn n nl blank (SnocList.snoc z a) = 0 := if_neg h
      show _ = pad blank (entabFn n tb nl blank (unfillFn n nl blank (SnocList.snoc z a)))
        (tbcFn n nl blank (SnocList.snoc z a))
      rw [eu, et]
      try rfl

/-- `tbc : String⟶ℕ`, `unfill`, `entab : String⟶String` as arrows. -/
@[expose] public def tbcR (n : Nat) (nl blank : Char) : dSL Unit Char ⟶ (⟨Nat⟩ : RelSet.{0}) :=
  graph (tbcFn n nl blank)
@[expose] public def unfillR (n : Nat) (nl blank : Char) : dSL Unit Char ⟶ dSL Unit Char :=
  graph (unfillFn n nl blank)
@[expose] public def entabR (n : Nat) (tb nl blank : Char) : dSL Unit Char ⟶ dSL Unit Char :=
  graph (entabFn n tb nl blank)

/-- `[base,op]` for `⟨tbc,col⟩`: `base=(0,0)`. -/
@[expose] public def tcOpFn (n : Nat) (nl blank : Char) :
    (Fobj Unit Char (⟨Nat × Nat⟩ : RelSet.{0})).carrier → Nat × Nat
  | Sum.inl _ => (0, 0)
  | Sum.inr ((t, c), a) =>
      if a = blank ∧ (c + 1) % n ≠ 0 then (t + 1, c + 1)
      else if a = blank then (0, c + 1)
      else if a = nl then (0, 0) else (0, c + 1)

@[expose] public def tcAlg (n : Nat) (nl blank : Char) :
    Fobj Unit Char (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ (⟨Nat × Nat⟩ : RelSet.{0}) := graph (tcOpFn n nl blank)

public theorem tcOp_step (n : Nat) (nl blank : Char) (hb : blank ≠ nl) (x : Str) (a : Char) :
    tcOpFn n nl blank (Sum.inr ((tbcFn n nl blank x, colFn nl x), a))
      = (tbcFn n nl blank (SnocList.snoc x a), colFn nl (SnocList.snoc x a)) := by
  by_cases ha : a = nl
  · have hab : a ≠ blank := fun h => hb (h.symm.trans ha)
    have hc : colFn nl (SnocList.snoc x a) = 0 := if_pos ha
    have ht : tbcFn n nl blank (SnocList.snoc x a) = 0 := if_neg fun h => hab h.1
    rw [hc, ht]
    show (if a = blank ∧ (colFn nl x + 1) % n ≠ 0 then _ else if a = blank then _
      else if a = nl then ((0 : Nat), (0 : Nat)) else _) = _
    rw [if_neg (fun h => hab h.1), if_neg hab, if_pos ha]
  · have hc : colFn nl (SnocList.snoc x a) = colFn nl x + 1 := if_neg ha
    by_cases h : a = blank ∧ (colFn nl x + 1) % n ≠ 0
    · have ht : tbcFn n nl blank (SnocList.snoc x a) = tbcFn n nl blank x + 1 :=
        if_pos (by rw [hc]; exact h)
      rw [hc, ht]
      show (if a = blank ∧ (colFn nl x + 1) % n ≠ 0 then (tbcFn n nl blank x + 1, colFn nl x + 1)
        else _) = _
      rw [if_pos h]
    · have ht : tbcFn n nl blank (SnocList.snoc x a) = 0 := if_neg (by rw [hc]; exact h)
      rw [hc, ht]
      show (if a = blank ∧ (colFn nl x + 1) % n ≠ 0 then _ else if a = blank then ((0 : Nat), colFn nl x + 1)
        else if a = nl then _ else ((0 : Nat), colFn nl x + 1)) = _
      rw [if_neg h]
      by_cases hab : a = blank
      · rw [if_pos hab]
      · rw [if_neg hab, if_neg ha]

/-- **B&dM p.251**: `⟨tbc,col⟩=⦇[base,op]⦈`. -/
public theorem tbc_col_fold (n : Nat) :
    rpair (tbcR n nl blank) (colR nl) = cataR (tcAlg n nl blank) := by
  rw [tcAlg, cataR_graph _ (fun x => (tbcFn n nl blank x, colFn nl x)) (fun _ => rfl)
    (fun x a => (tcOp_step n nl blank (by decide) x a).symm), tbcR, colR]
  exact rpair_graph _ _

-- The carrier of `triple`: `(entab (unfill x), (tbc x, col x))`.

/-- `[base,op]` for `triple`: `base=([],(0,0))`; the string grows only when the held blanks are
    cashed in — for a tab on a tab stop, or `blanks t⧺[a]` otherwise. -/
@[expose] public def tripleOpFn (n : Nat) (tb nl blank : Char) : (Fobj Unit Char (⟨Str × (Nat × Nat)⟩ : RelSet.{0})).carrier → Str × (Nat × Nat)
  | Sum.inl _ => (SnocList.wrap (), (0, 0))
  | Sum.inr ((x, (t, c)), a) =>
      (if a = blank ∧ (c + 1) % n ≠ 0 then x
       else if a = blank then SnocList.snoc x tb
       else SnocList.snoc (pad blank x t) a,
       tcOpFn n nl blank (Sum.inr ((t, c), a)))

@[expose] public def tripleAlg (n : Nat) (tb nl blank : Char) : Fobj Unit Char (⟨Str × (Nat × Nat)⟩ : RelSet.{0}) ⟶ (⟨Str × (Nat × Nat)⟩ : RelSet.{0}) :=
  graph (tripleOpFn n tb nl blank)

/-- `triple≜⟨unfill entab,⟨tbc,col⟩⟩`. -/
@[expose] public def tripleR (n : Nat) (tb nl blank : Char) : dSL Unit Char ⟶ (⟨Str × (Nat × Nat)⟩ : RelSet.{0}) :=
  rpair (unfillR n nl blank ≫ entabR n tb nl blank) (rpair (tbcR n nl blank) (colR nl))

public theorem tripleOp_step (n : Nat) (tb nl blank : Char) (hb : blank ≠ nl) (x : Str) (a : Char) :
    tripleOpFn n tb nl blank
        (Sum.inr ((entabFn n tb nl blank (unfillFn n nl blank x), (tbcFn n nl blank x, colFn nl x)), a))
      = (entabFn n tb nl blank (unfillFn n nl blank (SnocList.snoc x a)),
          (tbcFn n nl blank (SnocList.snoc x a), colFn nl (SnocList.snoc x a))) := by
  refine Prod.ext ?_ (tcOp_step n nl blank hb x a)
  show (if a = blank ∧ (colFn nl x + 1) % n ≠ 0 then _ else if a = blank then _ else _)
    = entabFn n tb nl blank (unfillFn n nl blank (SnocList.snoc x a))
  by_cases ha : a = blank
  · have hc : colFn nl (SnocList.snoc x a) = colFn nl x + 1 := if_neg fun h => hb (ha.symm.trans h)
    by_cases h : (colFn nl x + 1) % n = 0
    · rw [if_neg (fun h' => h'.2 h), if_pos ha]
      have eu : unfillFn n nl blank (SnocList.snoc x a) = SnocList.snoc x a :=
        if_neg fun h' => h'.2 (by rw [hc]; exact h)
      have ec : contractFn n tb nl blank x a = (unfillFn n nl blank x, tb) :=
        if_pos ⟨ha, by rw [hc]; exact h⟩
      rw [eu, entabFn.eq_2, ec]
    · rw [if_pos ⟨ha, h⟩]
      have eu : unfillFn n nl blank (SnocList.snoc x a) = unfillFn n nl blank x :=
        if_pos ⟨ha, by rw [hc]; exact h⟩
      rw [eu]
  · rw [if_neg (fun h' => ha h'.1), if_neg ha]
    have eu : unfillFn n nl blank (SnocList.snoc x a) = SnocList.snoc x a := if_neg fun h' => ha h'.1
    have ec : contractFn n tb nl blank x a = (x, a) := if_neg fun h' => ha h'.1
    rw [eu, entabFn.eq_2, ec]
    exact congrArg (fun e => SnocList.snoc e a) (entab_unfill n tb nl blank x).symm

/-- `triple` read as the function it is. -/
public theorem tripleR_graph (n : Nat) (tb nl blank : Char) :
    tripleR n tb nl blank = (graph (fun x => (entabFn n tb nl blank (unfillFn n nl blank x),
      (tbcFn n nl blank x, colFn nl x))) : dSL Unit Char ⟶ (⟨Str × (Nat × Nat)⟩ : RelSet.{0})) := by
  rw [tripleR, unfillR, entabR, tbcR, colR, graph_comp, rpair_graph, rpair_graph]

/-- **B&dM pp.251–252**: `triple=⦇[base,op]⦈`. -/
public theorem triple_fold (n : Nat) :
    tripleR n tb nl blank = cataR (tripleAlg n tb nl blank) := by
  rw [tripleR_graph, tripleAlg, cataR_graph (tripleOpFn n tb nl blank) (fun x => (entabFn n tb nl blank (unfillFn n nl blank x),
      (tbcFn n nl blank x, colFn nl x)))
    (fun u => congrArg (fun e => (e, ((0 : Nat), (0 : Nat)))) (entabFn.eq_1 n tb nl blank u))
    (fun x a => (tripleOp_step n tb nl blank (by decide) x a).symm)]

/-- Snoc-list concatenation `x⧺y`. -/
@[expose] public def catFn : Str → Str → Str
  | x, SnocList.wrap _ => x
  | x, SnocList.snoc y a => SnocList.snoc (catFn x y) a

@[expose] public def catR : (⟨Str × Str⟩ : RelSet.{0}) ⟶ dSL Unit Char := graph fun p => catFn p.1 p.2
@[expose] public def blanksR (blank : Char) : (⟨Nat⟩ : RelSet.{0}) ⟶ dSL Unit Char :=
  graph (pad blank (SnocList.wrap ()))
@[expose] public def assoclR : (⟨Str × (Nat × Nat)⟩ : RelSet.{0}) ⟶ (⟨(Str × Nat) × Nat⟩ : RelSet.{0}) :=
  graph fun p => ((p.1, p.2.1), p.2.2)
@[expose] public def outlR : (⟨(Str × Nat) × Nat⟩ : RelSet.{0}) ⟶ (⟨Str × Nat⟩ : RelSet.{0}) := graph Prod.fst

public theorem cat_blanks (blank : Char) (x : Str) :
    ∀ k, catFn x (pad blank (SnocList.wrap ()) k) = pad blank x k
  | 0 => rfl
  | k + 1 => congrArg (fun y => SnocList.snoc y blank) (cat_blanks blank x k)

/-- **B&dM p.252**: `entab=triple assocl π₁ (𝟙×blanks) cat`, from (10.1). -/
public theorem entab_triple (n : Nat) (tb nl blank : Char) :
    entabR n tb nl blank
      = tripleR n tb nl blank ≫ assoclR ≫ outlR ≫ rprodMap (𝟙 (dSL Unit Char)) (blanksR blank) ≫ catR := by
  rw [tripleR_graph, assoclR, outlR, blanksR, rprodMap_id_graph, catR, graph_comp,
    graph_comp, graph_comp, graph_comp, entabR]
  exact congrArg graph (funext fun x => (entab_unfill n tb nl blank x).trans (cat_blanks blank _ _).symm)

-- printing-only unexpanders: the two tupled algebras print as the book's `[base,step]`, `[base,op]`.
open Lean PrettyPrinter in
@[app_unexpander detabAlg] public meta def unexpandDetabAlg : Unexpander
  | `($_ $_ $_ $_ $_) => `($(mkIdent (Name.mkSimple "[base,step]")))
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander tcAlg] public meta def unexpandTcAlg : Unexpander
  | `($_ $_ $_ $_) => `($(mkIdent (Name.mkSimple "[base,op]")))
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander tripleAlg] public meta def unexpandTripleAlg : Unexpander
  | `($_ $_ $_ $_ $_) => `($(mkIdent (Name.mkSimple "[base,op]")))
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander outlR] public meta def unexpandOutlR : Unexpander
  | `($_:ident) => `($(mkIdent `π₁))
  | _ => throw ()

-- printing-only unexpanders: the program's arrows print under the book's names, parameters dropped.
open Lean PrettyPrinter in
@[app_unexpander colR] public meta def unexpandColR : Unexpander
  | `($_ $_*) => `($(mkIdent `col)) | `($_:ident) => `($(mkIdent `col)) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander tbcR] public meta def unexpandTbcR : Unexpander
  | `($_ $_*) => `($(mkIdent `tbc)) | `($_:ident) => `($(mkIdent `tbc)) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander entabR] public meta def unexpandEntabR : Unexpander
  | `($_ $_*) => `($(mkIdent `entab)) | `($_:ident) => `($(mkIdent `entab)) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander tripleR] public meta def unexpandTripleR : Unexpander
  | `($_ $_*) => `($(mkIdent `triple)) | `($_:ident) => `($(mkIdent `triple)) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander unfillR] public meta def unexpandUnfillR : Unexpander
  | `($_ $_*) => `($(mkIdent `unfill)) | `($_:ident) => `($(mkIdent `unfill)) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander blanksR] public meta def unexpandBlanksR : Unexpander
  | `($_ $_*) => `($(mkIdent `blanks)) | `($_:ident) => `($(mkIdent `blanks)) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander catR] public meta def unexpandCatR : Unexpander
  | `($_ $_*) => `($(mkIdent `cat)) | `($_:ident) => `($(mkIdent `cat)) | _ => throw ()

-- The pointwise functions print under the book's names applied to their points; the tab width and
-- the three characters are the section's, not part of the name.
open Lean PrettyPrinter in
@[app_unexpander entabFn] public meta def unexpandEntabFn : Unexpander
  | `($_ $_ $_ $_ $_ $xs*) => `($(mkIdent `entab) $xs*) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander tbcFn] public meta def unexpandTbcFn : Unexpander
  | `($_ $_ $_ $_ $xs*) => `($(mkIdent `tbc) $xs*) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander colFn] public meta def unexpandColFn : Unexpander
  | `($_ $_ $xs*) => `($(mkIdent `col) $xs*) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander fillFn] public meta def unexpandFillFn : Unexpander
  | `($_ $_ $_ $_ $xs*) => `($(mkIdent `fill) $xs*) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander unfillFn] public meta def unexpandUnfillFn : Unexpander
  | `($_ $_ $_ $_ $xs*) => `($(mkIdent `unfill) $xs*) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander expandFn] public meta def unexpandExpandFn : Unexpander
  | `($_ $_ $_ $_ $_ $y $a) => `($(mkIdent `expand) $y $a) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander contractFn] public meta def unexpandContractFn : Unexpander
  | `($_ $_ $_ $_ $_ $y $a) => `($(mkIdent `contract) $y $a) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander step] public meta def unexpandStep : Unexpander
  | `($_ $_ $_ $_ $_ $x $xs*) => `($(mkIdent `step) $x $xs*) | `($_ $_ $_ $_ $_) => `($(mkIdent `step)) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander loopStep] public meta def unexpandLoopStep : Unexpander
  | `($_ $_ $_ $x $xs*) => `($(mkIdent `step) $x $xs*) | `($_ $_ $_) => `($(mkIdent `step)) | _ => throw ()

-- `ofChars` is B&dM's `convert` from a cons-list to a snoc-list.
open Lean PrettyPrinter in
@[app_unexpander ofChars] public meta def unexpandOfChars : Unexpander
  | `($_ $xs*) => `($(mkIdent `convert) $xs*) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander SnocList.snoc] public meta def unexpandSnoc : Unexpander
  | `($_ $x $a) => `($(mkIdent `snoc) $x $a) | _ => throw ()

-- `pad blank y k` appends `k` blanks: the book's `y⧺blanks(k)`.
open Lean PrettyPrinter in
@[app_unexpander pad] public meta def unexpandPad : Unexpander
  | `($_ $_ $y $k) => `($y ++ $(mkIdent `blanks) $k) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander loop] public meta def unexpandLoop : Unexpander
  | `($_ $xs*) => `($(mkIdent `loop) $xs*) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander loop'] public meta def unexpandLoop' : Unexpander
  | `($_ $f $g $xs*) => `($(mkIdent `loop') ($f, $g) $xs*) | _ => throw ()

-- A first component is the note's `π₁` (B&dM's `outl`), applied pointwise as well.
open Lean PrettyPrinter in
@[app_unexpander Prod.fst] public meta def unexpandProdFst : Unexpander
  | `($_ $xs*) => `($(mkIdent `π₁) $xs*) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander assoclR] public meta def unexpandAssoclR : Unexpander
  | `($_ $_*) => `($(mkIdent `assocl)) | `($_:ident) => `($(mkIdent `assocl)) | _ => throw ()

-- printing-only unexpander: the note's `prefix` (a Lean keyword; the label emitter unescapes it).
open Lean PrettyPrinter in
@[app_unexpander prefixR] public meta def unexpandPrefixR : Unexpander
  | `($_:ident) => `($(mkIdent `prefix))
  | _ => throw ()

-- printing-only unexpanders: B&dM's `outl` is the note's `π₁`; the two guards keep their names.
open Lean PrettyPrinter in
@[app_unexpander outl] public meta def unexpandDetabOutl : Unexpander
  | `($_:ident) => `($(mkIdent `π₁))
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander fill] public meta def unexpandFill : Unexpander
  | `($_ $_ $_ $_) => `($(mkIdent `fill))
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander istab] public meta def unexpandIstab : Unexpander
  | `($_ $_) => `($(mkIdent `istab))
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander nottab] public meta def unexpandNottab : Unexpander
  | `($_ $_) => `($(mkIdent `nottab))
  | _ => throw ()

/-- `α°=[nil,snoc]°` is natural in the element type: `snocAlg_recip_strictNatural` with `α` spelled
    as the junction the §10 pictures carry. -/
public theorem alpha_recip_strictNatural :
    StrictNatural
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod (snocRelator Unit) (Relator.idRelator RelSet.{0})))
      (snocRelator Unit)
      (fun A => (junc (sumCop _ _) nil snocR
        : Fobj Unit A.carrier (dSL Unit A.carrier) ⟶ dSL Unit A.carrier)°) := by
  intro A B R
  have h := snocAlg_recip_strictNatural (L := Unit) R
  dsimp only at h ⊢
  rw [con_eq_junc, con_eq_junc] at h
  exact h

-- printing-only unexpanders: `detab` with its tab data dropped, and `String` for the carrier.
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Detab.detabFn] public meta def unexpandDetabFn : Unexpander
  | `($_ $_ $_ $_ $_ $x $args*) => `($(mkIdent `detab) $x $args*)
  | _ => `($(mkIdent `detab))

open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Detab.Str] public meta def unexpandDetabStr : Unexpander
  | _ => `($(mkIdent `String))

end Freyd.Alg.RelSet.Detab

-- printing-only (B&dM p.246): the thinning preorder `Q`, its two orders `V` (output string) and `U`
-- (character), and the arrows `expand`, `detab`, `prefix` are stated over the section's tab width
-- and its three characters, which are the section's context and not part of the name.
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Detab.Q] public meta def Freyd.Alg.RelSet.Detab.unexpandDetabQ : Unexpander
  | _ => `($(mkIdent `Q))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Detab.V] public meta def Freyd.Alg.RelSet.Detab.unexpandDetabV : Unexpander
  | _ => `($(mkIdent `V))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Detab.U] public meta def Freyd.Alg.RelSet.Detab.unexpandDetabU : Unexpander
  | _ => `($(mkIdent `U))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Detab.expand] public meta def Freyd.Alg.RelSet.Detab.unexpandDetabExpand : Unexpander
  | _ => `($(mkIdent `expand))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Detab.expandFn] public meta def Freyd.Alg.RelSet.Detab.unexpandDetabExpandFn : Unexpander
  | `($_ $_ $_ $_ $_ $x $a) => `($(mkIdent `expand) $x $a)
  | `($_ $_ $_ $_ $_ $x) => `($(mkIdent `expand) $x)
  | _ => `($(mkIdent `expand))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Detab.detabR] public meta def Freyd.Alg.RelSet.Detab.unexpandDetabFn : Unexpander
  | _ => `($(mkIdent `detab))
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Detab.prefixS] public meta def Freyd.Alg.RelSet.Detab.unexpandDetabPrefix : Unexpander
  | `($_ $x $y) => `($(mkIdent `prefix) $x $y)
  | _ => `($(mkIdent `prefix))
