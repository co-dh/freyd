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

public import AOP.A6_SnocList
public import AOP.A7_1
public import AOP.A7_2_Pres
public import AOP.A6_FinRel
import AOP.A10_1
import AOP.A7_2_RelSet
-- Spec-only derivations on abstract types: the unhashed scan fallback is opted into here and in no executed code.
attribute [local instance low] Freyd.Alg.RelSet.FibreIndex.scan


/-- B&dM p.246: the section's fixed data — the tab width `n`, and `TB`, `NL`, `BL` the tab, newline
    and blank characters.  Every definition below reads them from the one instance in scope, so the
    printer, which hides instance arguments, shows the book's `detab`, not `detab n TB NL BL`.  The
    class is named after the section's namespace, so its fields are the bare names `n`, `tb`, … -/
public class Freyd.Alg.RelSet.Detab where
  n : Nat
  tb : Char
  nl : Char
  blank : Char
  /-- The book's `TB`, `NL`, `BL` are different characters: the two inequalities the proofs use. -/
  blank_ne_nl : blank ≠ nl
  tb_ne_nl : tb ≠ nl

namespace Freyd.Alg.RelSet.Detab

open Freyd Freyd.Alg.RelSet Freyd.Alg.RelSet.SL

/-! ## §10.2's SPECIFICATION side (`entab-defn`), over snoc-lists of characters

  `detab ≜ ⦇[nil,expand]⦈` as a snoc-list catamorphism, the order
  `R ≜ length ≤ length°`, and the greedy data `U`, `V`, `Q` the note's `entab-defn` names. -/

/-- **entab-defn**: `String=[Char]` over snoc-lists. -/
@[expose] public abbrev Str : Type := SnocList Unit Char

/-- `x⧺blanks k`. -/
@[expose] public def pad [Detab] : Str → Nat → Str
  | x, 0 => x
  | x, k + 1 => SnocList.snoc (pad x k) blank

/-- The length of a string. -/
@[expose] public def length : Str → Nat
  | SnocList.wrap _ => 0
  | SnocList.snoc x _ => length x + 1

/-- **entab-defn**: `col≜⦇[zero,count]⦈`, `count (c,a)=(a=NL→0,c+1)`. -/
@[expose] public def colFn [Detab] : Str → Nat
  | SnocList.wrap _ => 0
  | SnocList.snoc xs a => if a = nl then 0 else colFn xs + 1

/-- **entab-defn**: `fill xs=xs⧺blanks (n−(col xs) mod n)`. -/
@[expose] public def fillFn [Detab] (xs : Str) : Str :=
  pad xs (n - colFn xs % n)

/-- **entab-defn**: `expand (xs,a)=(a=TB→fill xs,xs⧺[a])`. -/
@[expose] public def expandFn [Detab] (xs : Str) (a : Char) : Str :=
  if a = tb then fillFn xs else SnocList.snoc xs a

/-- **entab-defn**: `detab≜⦇[nil,expand]⦈ : String⟶String`, read as the function it is. -/
@[expose] public def detabFn [Detab] : Str → Str
  | SnocList.wrap _ => SnocList.wrap ()
  | SnocList.snoc xs a => expandFn (detabFn xs) a

/-- **entab-defn**: the algebra `[nil,expand] : F(String)⟶String`. -/
@[expose] public def expandAlgFn [Detab] :
    (Fobj Unit Char (dSL Unit Char)).carrier → Str
  | Sum.inl _ => SnocList.wrap ()
  | Sum.inr (x, a) => expandFn x a

/-- **entab-defn**: `expand : String×Char⟶String` as an arrow of its own — the note's box, and the
    second arm of `[nil,expand]`. -/
@[expose] public def expand [Detab] :
    (⟨Str × Char⟩ : RelSet.{0}) ⟶ dSL Unit Char :=
  graph (fun p => expandFn p.1 p.2)

/-- **entab-defn**: the algebra IS the junction `[nil,expand]` the note writes. -/
public theorem expandAlg_eq_junc [Detab] :
    graph expandAlgFn = junc (sumCop _ _) nil expand := by
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

/-- `𝟙×g` of a graph is the graph of the product function. -/
public theorem rprodMap_id_graph {A B b' : RelSet.{0}} (g : B.carrier → b'.carrier) :
    rprodMap (𝟙 A) (graph g)
      = graph (A := ⟨A.carrier × B.carrier⟩) (B := ⟨A.carrier × b'.carrier⟩) (fun p => (p.1, g p.2)) :=
  hom_ext fun _ _ => ⟨fun ⟨h1, h2⟩ => Prod.ext h1.symm h2,
    fun h => ⟨(congrArg Prod.fst h).symm, congrArg Prod.snd h⟩⟩

/-- **entab-defn**: the catamorphism of `[nil,expand]` IS `detabFn`. -/
public theorem detab_cata [Detab] :
    cataR (graph expandAlgFn)
      = (graph detabFn : dSL Unit Char ⟶ dSL Unit Char) :=
  cataR_graph _ _ (fun _ => rfl) (fun _ _ => rfl)

/-- **entab-defn**: `x` is a prefix of `y`. -/
@[expose] public def prefixS : Str → Str → Prop
  | x, SnocList.wrap _ => x = SnocList.wrap ()
  | x, SnocList.snoc y c => x = SnocList.snoc y c ∨ prefixS x y

/-- `w` carries no newline, so its column IS its length. -/
@[expose] public def noNL [Detab] : Str → Prop
  | SnocList.wrap _ => True
  | SnocList.snoc x a => a ≠ nl ∧ noNL x

/-- **entab-defn**: `R≜length≤length°`. -/
@[expose] public def R : dSL Unit Char ⟶ dSL Unit Char := fun xs ys => length xs ≤ length ys

/-- **entab-defn**: `detab` as a morphism. -/
@[expose] public def detab [Detab] : dSL Unit Char ⟶ dSL Unit Char :=
  graph detabFn

/-- **entab-defn**: `prefix`, mirrored to diagram order — `prefixR x ys` reads "`ys` is a
    prefix of `x`". -/
@[expose] public def «prefix» : dSL Unit Char ⟶ dSL Unit Char := fun x ys => prefixS ys x

/-! ## Elementary facts about `pad`, `slen`, `col` and `prefixS` -/

public theorem slen_pad [Detab] (x : Str) : ∀ k, length (pad x k) = length x + k
  | 0 => rfl
  | k + 1 => by show length (pad x k) + 1 = length x + (k + 1); rw [slen_pad x k]; omega

public theorem col_pad [Detab] (hb : blank ≠ nl) (x : Str) :
    ∀ k, colFn (pad x k) = colFn x + k
  | 0 => rfl
  | k + 1 => by
    show (if blank = nl then 0 else colFn (pad x k) + 1) = colFn x + (k + 1)
    rw [if_neg hb, col_pad hb x k]
    omega

public theorem col_eq_slen [Detab] : ∀ {w : Str}, noNL w → colFn w = length w
  | SnocList.wrap _, _ => rfl
  | SnocList.snoc x a, h => by
    show (if a = nl then 0 else colFn x + 1) = length x + 1
    rw [if_neg h.1, col_eq_slen h.2]

public theorem prefixS_slen_le : ∀ {x y : Str}, prefixS x y → length x ≤ length y
  | x, SnocList.wrap _, h => by rw [(h : x = SnocList.wrap ())]; exact Nat.zero_le _
  | x, SnocList.snoc y c, h => by
    rcases (h : x = SnocList.snoc y c ∨ prefixS x y) with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (prefixS_slen_le h)

/-- If two padded strings are equal and the first base is no longer, the second base is the
    first one padded — the only structural fact the `V` calculations need. -/
public theorem pad_eq_pad [Detab] (x y : Str) :
    ∀ j k, length x ≤ length y → pad x j = pad y k → ∃ m, y = pad x m ∧ j = m + k
  | j, 0, _, h => ⟨j, h.symm, rfl⟩
  | 0, k + 1, hle, h => by
    exfalso
    have hl : length x = length y + (k + 1) := by
      rw [← slen_pad y (k + 1), ← h]; rfl
    omega
  | j + 1, k + 1, hle, h => by
    have h' : pad x j = pad y k := by
      injection h
    obtain ⟨m, hm, hjk⟩ := pad_eq_pad x y j k hle h'
    exact ⟨m, hm, by omega⟩

/-! ## The note's FALSE row, refuted

  `detab prefix⊑R° detab` is marked FALSE in the note, with the witness printed there: at
  `n=8`, `detab [a,b,c,d,e,TB]=[a,b,c,d,e,BL,BL,BL]`, whose prefix `[a,b,c,d,e,BL,BL]` is
  longer than any input giving it.  The lemma behind "longer than any input" is
  `detab_len_of_short`: on a newline-free output SHORTER than one tab stop, `detab` cannot have
  used a tab at all, so input and output have the same length. -/

/-- A newline-free output shorter than a tab stop is produced letter by letter: no step of
    `detab` can have been a tab, since a tab lands the column on a multiple of `n`. -/
public theorem detab_len_of_short [Detab] (hb : blank ≠ nl) :
    ∀ (v w : Str), noNL w → length w < n → detabFn v = w → length v = length w
  | SnocList.wrap _, w, _, _, h => by subst h; rfl
  | SnocList.snoc s c, w, hnn, hlt, h => by
    by_cases hc : c = tb
    · exfalso
      have hw : w = pad (detabFn s) (n - colFn (detabFn s) % n) := by
        rw [← h]; simp only [detabFn, expandFn, if_pos hc, fillFn]
      have hcol : colFn w = length w := col_eq_slen hnn
      have hcol' : colFn w = colFn (detabFn s) + (n - colFn (detabFn s) % n) := by
        rw [hw, col_pad hb]
      have hmod : colFn (detabFn s) % n ≤ colFn (detabFn s) := Nat.mod_le _ _
      omega
    · have hw : w = SnocList.snoc (detabFn s) c := by
        rw [← h]; simp only [detabFn, expandFn, if_neg hc]
      subst hw
      have hlt' : length (detabFn s) < n := by
        have : length (SnocList.snoc (detabFn s) c) = length (detabFn s) + 1 := rfl
        omega
      have hlen := detab_len_of_short hb s (detabFn s) hnn.2 hlt' rfl
      show length s + 1 = length (detabFn s) + 1
      rw [hlen]

/-- Five ordinary characters and a tab: the note's `[a,b,c,d,e,TB]` at `n=8`. -/
@[expose] public def convert (l : List Char) : Str :=
  l.foldl (fun x a => SnocList.snoc x a) (SnocList.wrap ())

/-- B&dM p.246's characters at tab width `8`: the setting of the note's FALSE-row witness. -/
@[expose] public def book8 : Detab := ⟨8, '\t', '\n', ' ', by decide, by decide⟩

section
attribute [local instance] book8

/-- **entab-laws**, the note's FALSE row certified: `detab prefix⊑R° detab` fails at `n=8`.
    `detab [x,x,x,x,x,TB]=[x,x,x,x,x,BL,BL,BL]`, and its prefix `[x,x,x,x,x,BL,BL]` needs SEVEN
    input characters (`detab_len_of_short`), one more than the six the original had — a prefix
    of the expansion can be longer than any input producing it, once it stops short of a tab
    stop.  This is why the note replaces `prefix°` by `V≜prefix°∩(fill fill°)`. -/
public theorem detab_prefix_false : ¬ (detab ≫ «prefix» ⊑ R° ≫ detab) := by
  intro hle
  have hpre : prefixS (convert ['x', 'x', 'x', 'x', 'x', ' ', ' '])
      (detabFn (convert ['x', 'x', 'x', 'x', 'x', '\t'])) :=
    Or.inr (Or.inl rfl)
  obtain ⟨v, hR, hdv⟩ := le_iff.mp hle (convert ['x', 'x', 'x', 'x', 'x', '\t'])
    (convert ['x', 'x', 'x', 'x', 'x', ' ', ' '])
    ⟨detabFn (convert ['x', 'x', 'x', 'x', 'x', '\t']), rfl, hpre⟩
  have hnn : noNL (convert ['x', 'x', 'x', 'x', 'x', ' ', ' ']) :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, trivial⟩
  have hv7 := detab_len_of_short (by decide) v
    (convert ['x', 'x', 'x', 'x', 'x', ' ', ' ']) hnn (by decide)
    (hdv : convert ['x', 'x', 'x', 'x', 'x', ' ', ' '] = detabFn v).symm
  have h6 : length v ≤ length (convert ['x', 'x', 'x', 'x', 'x', '\t']) := hR
  have e6 : length (convert ['x', 'x', 'x', 'x', 'x', '\t']) = 6 := rfl
  have e7 : length (convert ['x', 'x', 'x', 'x', 'x', ' ', ' ']) = 7 := rfl
  omega

end

/-! ## `entab-defn`: `U`, `V`, `Q`, and the greedy condition

  `detab prefix⊑R° detab` being false, the note replaces `prefix°` by
  `V≜prefix°∩(fill fill°)` — only the prefixes that do not cross a tab stop.  `expand_V_step`
  is the note's ladder (`nil V°=nil`, `fill V°=fill`, `snoc V°⊑snoc∪(π₁V°)`,
  `expand V°⊑expand∪(π₁V°)`) in one statement: shortening the output of one `expand` step to a
  `V`-smaller string either leaves the step alone or discards it. -/

/-- **entab-defn**: `U` the preorder with `a U b⟺a=TB∨a=b` — `TB` below every character, so
    `est` prefers a tab to a blank. -/
@[expose] public def U [Detab] : (⟨Char⟩ : RelSet.{0}) ⟶ ⟨Char⟩ := fun a b => a = tb ∨ a = b

/-- **entab-defn**: `V≜prefix°∩(fill fill°)` — a prefix that fills to the same string, i.e. one
    that does not cross a tab stop. -/
@[expose] public def V [Detab] : dSL Unit Char ⟶ dSL Unit Char :=
  fun xs ys => prefixS xs ys ∧ fillFn xs = fillFn ys

/-- **entab-defn**: `Q≜𝟙+(V×U)`. -/
@[expose] public def Q [Detab] :
    (F Unit Char).obj (dSL Unit Char) ⟶ (F Unit Char).obj (dSL Unit Char) :=
  fun u v => match u, v with
    | Sum.inl _, Sum.inl _ => True
    | Sum.inr p, Sum.inr q => V p.1 q.1 ∧ U p.2 q.2
    | _, _ => False

/-- **entab-defn**, point-free: `Q=𝟙+(V×U)`. -/
public theorem Q_eq [Detab] :
    Q = sumMap (sumCop (dL Unit) ⟨Str × Char⟩) (sumCop (dL Unit) ⟨Str × Char⟩)
      (𝟙 (dL Unit)) (rprodMap V U) := by
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

public theorem pad_add [Detab] (x : Str) (j : Nat) :
    ∀ k, pad (pad x j) k = pad x (j + k)
  | 0 => rfl
  | k + 1 => by
    show SnocList.snoc (pad (pad x j) k) blank = SnocList.snoc (pad x (j + k)) blank
    rw [pad_add x j k]

/-- Adding `j` to `a` adds `j` to `a mod n`, as long as the sum stays inside one period. -/
public theorem mod_add_of_lt (n a j : Nat) (h : a % n + j < n) : (a + j) % n = a % n + j := by
  have hd : n * (a / n) + a % n = a := Nat.div_add_mod a n
  have he : a + j = n * (a / n) + (a % n + j) := by omega
  rw [he, Nat.mul_add_mod, Nat.mod_eq_of_lt h]

/-- `fill : String⟶String` as an arrow. -/
@[expose] public def fill [Detab] : dSL Unit Char ⟶ dSL Unit Char :=
  graph fillFn

/-- The coreflexive `istab outr`: the pairs whose character is `TB` — the guard of `expand`'s
    conditional, written as the union of its two guarded arms. -/
@[expose] public def istab [Detab] : (⟨Str × Char⟩ : RelSet.{0}) ⟶ ⟨Str × Char⟩ :=
  fun p q => p = q ∧ p.2 = tb

/-- The complementary coreflexive: the pairs whose character is not `TB`. -/
@[expose] public def nottab [Detab] : (⟨Str × Char⟩ : RelSet.{0}) ⟶ ⟨Str × Char⟩ :=
  fun p q => p = q ∧ p.2 ≠ tb

public theorem prefixS_refl : ∀ x : Str, prefixS x x
  | SnocList.wrap () => rfl
  | SnocList.snoc _ _ => Or.inl rfl

/-- Exercise 10.4, first claim: `nil V°=nil` — the empty string has no other prefix. -/
public theorem nil_V [Detab] :
    (nil : dL Unit ⟶ dSL Unit Char) ≫ V° = nil :=
  hom_ext fun _ x => ⟨fun ⟨_, hy, hpre, _⟩ => by subst hy; exact hpre,
    fun h => ⟨SnocList.wrap (), rfl, h, by rw [h]⟩⟩

/-- A filled string ends on a tab stop. -/
public theorem col_fill_mod [Detab] (hn : 0 < n) (hb : blank ≠ nl) (z : Str) :
    colFn (fillFn z) % n = 0 := by
  have hrz : colFn z % n < n := Nat.mod_lt _ hn
  have hdz : n * (colFn z / n) + colFn z % n = colFn z := Nat.div_add_mod _ _
  have hcoly : colFn (fillFn z) = n * (colFn z / n + 1) := by
    show colFn (pad z (n - colFn z % n)) = _
    rw [col_pad hb, Nat.mul_succ]
    omega
  rw [hcoly]; exact Nat.mul_mod_right _ _

/-- A prefix `x` of `z⧺[c]` short of it that fills to the same string: then `c` is a blank inside
    the tab period, and `x` already fills to `fill z`. -/
public theorem prefix_fill_snoc [Detab] (hn : 0 < n) (hb : blank ≠ nl)
    {x z : Str} {c : Char} (hpz : prefixS x z)
    (hfill : fillFn x = fillFn (SnocList.snoc z c)) :
    c = blank ∧ fillFn x = fillFn z ∧ colFn (SnocList.snoc z c) % n ≠ 0 := by
  have hlx : length x ≤ length z := prefixS_slen_le hpz
  obtain ⟨m, hm, hjk⟩ := pad_eq_pad x (SnocList.snoc z c) (n - colFn x % n)
    (n - colFn (SnocList.snoc z c) % n) (by show length x ≤ length z + 1; omega) hfill
  have hslen : length z + 1 = length x + m := by
    show length (SnocList.snoc z c) = length x + m
    rw [hm, slen_pad]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hsplit : SnocList.snoc z c = SnocList.snoc (pad x m') blank := hm
  obtain ⟨hz, hcb⟩ : z = pad x m' ∧ c = blank := by
    injection hsplit with h1 h2; exact ⟨h1, h2⟩
  have hcne : c ≠ nl := by rw [hcb]; exact hb
  have hcolz : colFn z = colFn x + m' := by rw [hz, col_pad hb]
  have hcol_snoc : colFn (SnocList.snoc z c) = colFn x + m' + 1 := by
    show (if c = nl then 0 else colFn z + 1) = colFn x + m' + 1
    rw [if_neg hcne, hcolz]
  rw [hcol_snoc] at hjk
  have hrx : colFn x % n < n := Nat.mod_lt _ hn
  have hsb : (colFn x + m' + 1) % n < n := Nat.mod_lt _ hn
  have hlt : colFn x % n + m' < n := by omega
  have hmodz : colFn z % n = colFn x % n + m' := by
    rw [hcolz]; exact mod_add_of_lt n (colFn x) m' hlt
  refine ⟨hcb, ?_, by rw [hcol_snoc]; omega⟩
  show pad x (n - colFn x % n) = pad z (n - colFn z % n)
  rw [hmodz, hz, pad_add]
  congr 1
  omega

/-- Exercise 10.4, second claim: `fill V°=fill` — a filled string sits on a tab stop, so its own
    `fill` is a whole `n` blanks long, which no shorter prefix can match. -/
public theorem fill_V [Detab] (hn : 0 < n) (hb : blank ≠ nl) :
    fill ≫ V° = fill :=
  hom_ext fun z x => by
    refine ⟨fun ⟨y, hy, hpre, hfill⟩ => ?_, fun h => ⟨x, h, prefixS_refl x, rfl⟩⟩
    obtain rfl : y = fillFn z := hy
    show x = fillFn z
    have hmod0 := col_fill_mod hn hb z
    have hfy : fillFn (fillFn z) = pad (fillFn z) n := by
      show pad (fillFn z) (n - colFn (fillFn z) % n) = _
      rw [hmod0, Nat.sub_zero]
    have hfill' : pad x (n - colFn x % n) = pad (fillFn z) n :=
      hfill.trans hfy
    obtain ⟨m, hm, hjk⟩ := pad_eq_pad x (fillFn z)
      (n - colFn x % n) n (prefixS_slen_le hpre) hfill'
    have hkx : n - colFn x % n ≤ n := Nat.sub_le _ _
    obtain rfl : m = 0 := by omega
    exact hm.symm

/-- Exercise 10.4, third claim: `snoc V°⊑snoc∪(π₁V°)` — a prefix of `xs⧺[a]` is the whole of it or
    a prefix of `xs`; in the second case the two fills agree only when `a` is a blank and `xs` is
    the prefix padded with blanks inside one tab period. -/
public theorem snoc_V [Detab] (hn : 0 < n) (hb : blank ≠ nl) :
    snoc ≫ V° ⊑ snoc ∪ (relProd (dSL Unit Char) ⟨Char⟩).π₁ ≫ V° :=
  le_iff.mpr fun ⟨z, c⟩ x ⟨y, hy, hpre, hfill⟩ => by
    obtain rfl : y = SnocList.snoc z c := hy
    rcases (hpre : x = SnocList.snoc z c ∨ prefixS x z) with rfl | hpz
    · exact Or.inl rfl
    · exact Or.inr ⟨z, rfl, hpz, (prefix_fill_snoc hn hb hpz hfill).2.1⟩

/-- `expand` is the conditional `(istab outr→fill outl,snoc)`, written as its two guarded arms. -/
public theorem expand_eq_cond [Detab] :
    expand = istab ≫ (relProd (dSL Unit Char) ⟨Char⟩).π₁ ≫ fill ∪ nottab ≫ snoc :=
  hom_ext fun ⟨z, c⟩ y => by
    by_cases hc : c = tb
    · have e : expandFn z c = fillFn z := if_pos hc
      refine ⟨fun h => Or.inl ⟨(z, c), ⟨rfl, hc⟩, z, rfl, h.trans e⟩, fun h => ?_⟩
      rcases h with ⟨_, ⟨rfl, _⟩, _, rfl, hy⟩ | ⟨_, ⟨rfl, hq⟩, _⟩
      · exact hy.trans e.symm
      · exact absurd hc hq
    · have e : expandFn z c = SnocList.snoc z c := if_neg hc
      refine ⟨fun h => Or.inr ⟨(z, c), ⟨rfl, hc⟩, h.trans e⟩, fun h => ?_⟩
      rcases h with ⟨_, ⟨rfl, hq⟩, _⟩ | ⟨_, ⟨rfl, _⟩, hy⟩
      · exact absurd hq hc
      · exact hy.trans e.symm

/-- The definition of `expand`, with the guard on the second arm dropped:
    `istab outl fill∪nottab(snoc∪X)⊑expand∪X`. -/
public theorem expand_guard_drop [Detab] {X : _ ⟶ dSL Unit Char} :
    istab ≫ (relProd (dSL Unit Char) ⟨Char⟩).π₁ ≫ fill ∪ nottab ≫ (snoc ∪ X) ⊑ expand ∪ X := by
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
public theorem expand_V [Detab] (hn : 0 < n) :
    expand ≫ V° ⊑ expand ∪ (relProd (dSL Unit Char) ⟨Char⟩).π₁ ≫ V° :=
  calc expand ≫ V°
      = (istab ≫ (relProd (dSL Unit Char) ⟨Char⟩).π₁ ≫ fill ∪ nottab ≫ snoc) ≫ V° := by
        rw [expand_eq_cond]
    _ = istab ≫ (relProd (dSL Unit Char) ⟨Char⟩).π₁ ≫ fill ≫ V° ∪ nottab ≫ snoc ≫ V° := by
        simpa only [Cat.assoc] using (union_comp_distrib _ _ _ :
          (istab ≫ (relProd (dSL Unit Char) ⟨Char⟩).π₁ ≫ fill ∪ nottab ≫ snoc) ≫ V° = _)
    _ = istab ≫ (relProd (dSL Unit Char) ⟨Char⟩).π₁ ≫ fill ∪ nottab ≫ snoc ≫ V° := by
        rw [fill_V hn blank_ne_nl]
    _ ⊑ istab ≫ (relProd (dSL Unit Char) ⟨Char⟩).π₁ ≫ fill ∪ nottab ≫ (snoc ∪ (relProd (dSL Unit Char) ⟨Char⟩).π₁ ≫ V°) :=
        union_mono (le_refl _) (comp_mono_left _ (snoc_V hn blank_ne_nl))
    _ ⊑ expand ∪ (relProd (dSL Unit Char) ⟨Char⟩).π₁ ≫ V° := expand_guard_drop

calc_steps expand_V

/-- **entab-laws**: `detab V°⊑R° detab` read on points — shortening the output to a `V`-smaller
    string is matched by an input no longer than the original.  Induction on the input,
    `expand_V` at each step. -/
public theorem detab_V [Detab] (hn : 0 < n) :
    ∀ (t x : Str), V x (detabFn t) → ∃ t₀, detabFn t₀ = x ∧ length t₀ ≤ length t
  | SnocList.wrap _, x, h => by
    obtain rfl : x = SnocList.wrap () := h.1
    exact ⟨SnocList.wrap (), rfl, Nat.le_refl _⟩
  | SnocList.snoc s c, x, h => by
    rcases le_iff.mp (expand_V hn) (detabFn s, c) x
      ⟨_, rfl, h⟩ with hx | ⟨_, rfl, hV⟩
    · exact ⟨SnocList.snoc s c, hx.symm, Nat.le_refl _⟩
    · obtain ⟨t₀, ht₀, hlen⟩ := detab_V hn s x hV
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
public theorem detab_unfold [Detab] :
    detab
      = (junc (sumCop _ _) nil snoc : Alg (F Unit Char) (dSL Unit Char))°
        ≫ (F Unit Char).map detab ≫ junc (sumCop _ _) nil expand := by
  have hc : detab = cataR (graph expandAlgFn) := detab_cata.symm
  have hcomm : (F Unit Char).map (cataR (graph expandAlgFn)) ≫ graph expandAlgFn
      = graph con ≫ cataR (graph expandAlgFn) :=
    (cataFold_comm (graph expandAlgFn)).symm
  rw [← con_eq_junc, ← expandAlg_eq_junc, hc, hcomm, ← Cat.assoc, con_recip_con, Cat.id_comp]

/-- Distributing `∪`; the fold again, and the definition of `F`:
    `α°F(detab)[nil,expand∪X]=detab∪snoc°(detab×𝟙)X`. -/
public theorem detab_unfold_union [Detab] {X : _ ⟶ dSL Unit Char} :
    (junc (sumCop _ _) nil snoc : Alg (F Unit Char) (dSL Unit Char))°
        ≫ (F Unit Char).map detab
        ≫ junc (sumCop _ _) nil (expand ∪ X)
      = detab ∪ snoc° ≫ rprodMap detab (𝟙 (⟨Char⟩ : RelSet.{0})) ≫ X :=
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
              show x = expandFn (detabFn p.1) p.2
              rw [hx, ← h1, h2]
            · exact Or.inr ⟨p, hs, q, ⟨h1, h2⟩, hX⟩
    · rintro (h | ⟨p, hs, q, ⟨h1, h2⟩, hX⟩)
      · cases t with
        | wrap d =>
          cases d
          exact ⟨Sum.inl (), Or.inl ⟨(), rfl, rfl⟩, Sum.inl (), rfl, Or.inl ⟨(), rfl, h⟩⟩
        | snoc s a =>
          exact ⟨Sum.inr (s, a), Or.inr ⟨(s, a), rfl, rfl⟩, Sum.inr (detabFn s, a),
            ⟨rfl, rfl⟩, Or.inr ⟨(detabFn s, a), rfl, Or.inl h⟩⟩
      · exact ⟨Sum.inr p, Or.inr ⟨p, rfl, hs⟩, Sum.inr q, ⟨h1, h2⟩,
          Or.inr ⟨q, rfl, Or.inr hX⟩⟩

/-- Naturality of `π₁`, `(detab×𝟙)π₁=π₁ detab`, after `snoc°`. -/
public theorem detab_init_natural [Detab] {Y : dSL Unit Char ⟶ dSL Unit Char} :
    snoc° ≫ rprodMap detab (𝟙 (⟨Char⟩ : RelSet.{0})) ≫ (relProd (dSL Unit Char) ⟨Char⟩).π₁ ≫ Y
      = snoc° ≫ (relProd (dSL Unit Char) ⟨Char⟩).π₁ ≫ detab ≫ Y :=
  hom_ext fun _ _ =>
    ⟨fun ⟨p, hs, _, ⟨h1, _⟩, w, hw, hV⟩ => ⟨p, hs, p.1, rfl, w, hw.trans h1, hV⟩,
     fun ⟨p, hs, w, hw, y, hy, hV⟩ =>
      ⟨p, hs, (y, p.2), ⟨by show y = detabFn p.1; rw [hy, hw], rfl⟩, y, rfl, hV⟩⟩

/-- `X≜detab V°` solves `X⊑detab∪(init X)`; `init` is inductive, so every solution lies below the
    greatest, `prefix detab` — induction on the input, `detab_V` — and a prefix is no longer:
    `prefix⊑R°`. -/
public theorem detab_V_induction [Detab] (hn : 0 < n) :
    detab ∪ snoc° ≫ (relProd (dSL Unit Char) ⟨Char⟩).π₁ ≫ detab ≫ V° ⊑ R° ≫ detab :=
  le_iff.mpr fun t x h => by
    rcases h with h | ⟨p, hs, _, rfl, _, rfl, hV⟩
    · exact ⟨t, Nat.le_refl _, h⟩
    · obtain ⟨t₀, ht₀, hlen⟩ := detab_V hn p.1 x hV
      subst hs
      exact ⟨t₀, Nat.le_succ_of_le hlen, ht₀.symm⟩

/-- **B&dM p.249** `V detab⊑detab R`, mirrored: `detab V°⊑R° detab` — the book's chain, one `calc`
    step per hint. -/
public theorem detab_V_R [Detab] (hn : 0 < n) :
    detab ≫ V° ⊑ R° ≫ detab :=
  calc detab ≫ V°
      = (junc (sumCop _ _) nil snoc : Alg (F Unit Char) (dSL Unit Char))°
        ≫ (F Unit Char).map detab
        ≫ junc (sumCop _ _) nil expand ≫ V° := by
        simpa only [Cat.assoc] using congrArg (· ≫ V°) detab_unfold
    _ = (junc (sumCop _ _) nil snoc : Alg (F Unit Char) (dSL Unit Char))°
        ≫ (F Unit Char).map detab
        ≫ junc (sumCop _ _) (nil ≫ V°) (expand ≫ V°) := by
        rw [junc_comp]
    _ = (junc (sumCop _ _) nil snoc : Alg (F Unit Char) (dSL Unit Char))°
        ≫ (F Unit Char).map detab
        ≫ junc (sumCop _ _) nil (expand ≫ V°) := by
        rw [nil_V]
    _ ⊑ (junc (sumCop _ _) nil snoc : Alg (F Unit Char) (dSL Unit Char))°
        ≫ (F Unit Char).map detab
        ≫ junc (sumCop _ _) nil (expand ∪ (relProd (dSL Unit Char) ⟨Char⟩).π₁ ≫ V°) :=
        comp_mono_left _ (comp_mono_left _
          (union_mono (le_refl _) (comp_mono_left _ (expand_V hn))))
    _ = detab ∪ snoc° ≫ rprodMap detab (𝟙 (⟨Char⟩ : RelSet.{0})) ≫ (relProd (dSL Unit Char) ⟨Char⟩).π₁ ≫ V° :=
        detab_unfold_union
    _ = detab ∪ snoc° ≫ (relProd (dSL Unit Char) ⟨Char⟩).π₁ ≫ detab ≫ V° := by
        rw [detab_init_natural]
    _ ⊑ R° ≫ detab := detab_V_induction hn

calc_steps detab_V_R

/-- **entab-laws**: Proposition 9.4's `hV`, `V detab°⊑detab° R` — `detab_V_R` conversed. -/
public theorem entab_V [Detab] (hn : 0 < n) :
    V ≫ detab° ⊑ detab° ≫ R :=
  le_iff.mpr fun x t ⟨y, hV, hy⟩ =>
    let ⟨t₀, hR, hd⟩ := le_iff.mp (detab_V_R hn) t x ⟨y, hy, hV⟩
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
public theorem entab_thin_condition [Detab] (hn : 0 < n) :
    Q ≫ (F Unit Char).map (detab°) ≫ graph con
      ⊑ (F Unit Char).map (detab°) ≫ graph con ≫ R :=
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
          obtain ⟨t₀, ht₀, hlen⟩ := le_iff.mp (entab_V hn) p.1 r.1
            ⟨q.1, hQ.1, (hFw.1 : q.1 = detabFn r.1)⟩
          refine ⟨Sum.inr (t₀, p.2), ⟨ht₀, rfl⟩, SnocList.snoc t₀ p.2, rfl, ?_⟩
          show length t₀ + 1 ≤ length r.1 + 1
          exact Nat.succ_le_succ hlen

/-- `H = ⦇α⦈·⦇[nil,expand]⦈°` collapses to `detab°` by reflection (`AOP.A6_SnocList.cataR_con`). -/
public theorem entab_H [Detab] :
    (relCata (F := F Unit Char) (graph expandAlgFn))°
        ≫ relCata (F := F Unit Char) (I := initial Unit Char)
            (graph (con (L := Unit) (E := Char)))
      = Allegory.recip detab := by
  rw [← cataR_eq_relCata, ← cataR_eq_relCata, cataR_con, detab_cata]
  exact Cat.comp_id _

/-- **entab-laws**, the prefixed point (Theorem 10.1 at `Q≜𝟙+(V×U)`): at `X≜Λ(detab°) est(R)` the
    greedy body is below `X`, so the least fixed point `entab_laws` is too. -/
public theorem entab_laws_prefixed [Detab] (hn : 0 < n)
    {X : dSL Unit Char ⟶ dSL Unit Char}
    (hX : X = Λ (Allegory.recip detab) ≫ est R) :
    Λ ((junc (sumCop _ _) nil expand
        : Alg (F Unit Char) (dSL Unit Char))°)
      ≫ est Q ≫ (F Unit Char).map X ≫ junc (sumCop _ _) nil snoc
      ⊑ Λ (Allegory.recip detab) ≫ est R := by
  subst hX
  rw [← expandAlg_eq_junc, ← con_eq_junc]
  have e : _root_.Freyd.Alg.H (F := F Unit Char) (graph expandAlgFn)
      (graph (con (L := Unit) (E := Char))) = detab° := entab_H
  rw [← e]
  exact greedy_dp_prefixed (graph_map con) entab_mono R_trans
    (by unfold ThinCondition; rw [e]; exact entab_thin_condition hn)

/-- **entab-laws**, second row (B&dM p.247): the shortest input `detab` expands to the given
    output is the least fixed point of `(μX : [nil,expand]° est(Q)(𝟙+(X×𝟙))[nil,snoc])` —
    Theorem 10.1 at `Q≜𝟙+(V×U)`, one character of input decided at each step.
    `H = ⦇α⦈·⦇[nil,expand]⦈°` collapses to `detab°` by reflection
    (`AOP.A6_SnocList.cataR_con`). -/
public theorem entab_laws [Detab] (hn : 0 < n) :
    mu (fun X : dSL Unit Char ⟶ dSL Unit Char =>
        Λ ((junc (sumCop _ _) nil expand
            : Alg (F Unit Char) (dSL Unit Char))°)
          ≫ est Q ≫ (F Unit Char).map X ≫ junc (sumCop _ _) nil snoc)
      ⊑ Λ (Allegory.recip detab) ≫ est R :=
  mu_le (entab_laws_prefixed hn rfl)

/-- `expand` never returns the empty string: on a tab it fills at least one blank (the column is
    `< n` after `%`), on any other character it snocs.  This is B&dM's Proposition 10.1
    hypothesis `nil` and `expand` have disjoint ranges. -/
public theorem expand_ne_nil [Detab] (hn : 0 < n) (x : Str) (a : Char) :
    expandFn x a ≠ SnocList.wrap () := by
  unfold expandFn
  split
  · unfold fillFn
    obtain ⟨k, hk⟩ : ∃ k, n - colFn x % n = k + 1 :=
      ⟨n - colFn x % n - 1, by have := Nat.mod_lt (colFn x) hn; omega⟩
    rw [hk]
    show SnocList.snoc (pad x k) blank ≠ SnocList.wrap ()
    intro h; cases h
  · intro h; cases h

/-- **entab-laws**, third row (Proposition 10.1): with `nil` and `expand` of disjoint ranges the
    branch `(expand°)%∋ est(V×U)(X×𝟙)snoc` refines `entab_laws`' body
    `([nil,expand]°)%∋ est(Q)[nil,(X×𝟙)snoc]` — `AOP.A9_1.est_arm₂_le` at `[nil,expand]`, whose
    `Q₂` at `Q≜𝟙+(V×U)` is `V×U`. -/
public theorem entab_branch [Detab] (hn : 0 < n)
    (X : dSL Unit Char ⟶ dSL Unit Char) :
    Λ (expand°) ≫ est (rprodMap V U)
        ≫ rprodMap X (𝟙 (⟨Char⟩ : RelSet.{0})) ≫ snoc
      ⊑ Λ ((junc (sumCop _ _) nil expand
            : Alg (F Unit Char) (dSL Unit Char))°) ≫ est Q
          ≫ (F Unit Char).map X ≫ junc (sumCop _ _) nil snoc := by
  rw [← expandAlg_eq_junc, ← con_eq_junc]
  exact est_arm₂_le (X := X) (Q := Q)
    (T := graph expandAlgFn) (U := graph (con (L := Unit) (E := Char)))
    fun _d p y h1 h2 =>
      expand_ne_nil hn p.1 p.2 (Eq.trans (Eq.symm (h2 : y = _)) (h1 : y = _))

/-! ## The `detab` program (B&dM p.247): tupling with `col`, and the loop -/

/-- `col : String⟶ℕ` as an arrow. -/
@[expose] public def col [Detab] : dSL Unit Char ⟶ (⟨Nat⟩ : RelSet.{0}) := graph colFn

-- The tupled carrier `(output so far, current column)`.

/-- `step((x,c),a)`: append `a`, resetting the column on a newline and padding to the next tab
    stop on a tab. -/
@[expose] public def step [Detab] : (Str × Nat) × Char → Str × Nat
  | ((x, c), a) =>
      if a = nl then (SnocList.snoc x nl, 0)
      else if a = tb then (pad x (n - c % n), c + (n - c % n))
      else (SnocList.snoc x a, c + 1)

/-- `[base,step]` with `base=([],0)`. -/
@[expose] public def stepFn [Detab] :
    (Fobj Unit Char (⟨Str × Nat⟩ : RelSet.{0})).carrier → Str × Nat
  | Sum.inl _ => (SnocList.wrap (), 0)
  | Sum.inr p => step p

/-- `[base,step] : F(String×ℕ)⟶String×ℕ` as an arrow. -/
@[expose] public def detabAlg [Detab] : Fobj Unit Char (⟨Str × Nat⟩ : RelSet.{0}) ⟶ (⟨Str × Nat⟩ : RelSet.{0}) :=
  graph stepFn

/-- `step` on `(detab x, col(detab x))` is `(detab, col·detab)` one character further. -/
public theorem stepFn_detab [Detab] (hb : blank ≠ nl) (htb : tb ≠ nl)
    (d : Str) (a : Char) :
    stepFn (Sum.inr ((d, colFn d), a)) = (expandFn d a, colFn (expandFn d a)) := by
  by_cases h1 : a = nl
  · have e : expandFn d a = SnocList.snoc d a := if_neg fun h => htb (h.symm.trans h1)
    rw [e]
    show (if a = nl then (SnocList.snoc d nl, 0) else _) = (SnocList.snoc d a, if a = nl then 0 else colFn d + 1)
    rw [if_pos h1, if_pos h1, h1]
  · by_cases h2 : a = tb
    · have e : expandFn d a = pad d (n - colFn d % n) := if_pos h2
      rw [e, col_pad hb]
      show (if a = nl then _ else if a = tb then
        (pad d (n - colFn d % n), colFn d + (n - colFn d % n)) else _) = _
      rw [if_neg h1, if_pos h2]
    · have e : expandFn d a = SnocList.snoc d a := if_neg h2
      rw [e]
      show (if a = nl then _ else if a = tb then _ else (SnocList.snoc d a, colFn d + 1))
        = (SnocList.snoc d a, if a = nl then 0 else colFn d + 1)
      rw [if_neg h1, if_neg h2, if_neg h1]

/-- The tupled function `(detab, col·detab)`. -/
@[expose] public def detabColFn [Detab] (t : Str) : Str × Nat :=
  (detabFn t, colFn (detabFn t))

public theorem detabAlg_cata [Detab] (hb : blank ≠ nl) (htb : tb ≠ nl) :
    cataR detabAlg = (graph detabColFn : dSL Unit Char ⟶ (⟨Str × Nat⟩ : RelSet.{0})) :=
  cataR_graph _ _ (fun _ => rfl) (fun _ a => (stepFn_detab hb htb _ a).symm)

/-- **B&dM p.247**, tupling: `(detab, col·detab)=⦇[base,step]⦈`, in diagram order. -/
public theorem detab_tupled [Detab] :
    rpair detab (detab ≫ col) = cataR detabAlg := by
  rw [detabAlg_cata blank_ne_nl tb_ne_nl, detab, col, graph_comp]
  exact rpair_graph _ _

/-- B&dM p.247's `loop`: `loop f (s,[])=s`, `loop f (s,a:x)=loop f (f(s,a),x)` — a left fold. -/
@[expose] public def loop {S A : Type} (f : S × A → S) (p : S × List A) : S :=
  p.2.foldl (fun s a => f (s, a)) p.1

public theorem detabCol_foldl [Detab] (hb : blank ≠ nl) (htb : tb ≠ nl) :
    ∀ (l : List Char) (t : Str),
      detabColFn (l.foldl (fun x a => SnocList.snoc x a) t) = loop step (detabColFn t, l)
  | [], _ => rfl
  | a :: l, t => by
    rw [List.foldl_cons, detabCol_foldl hb htb l]
    exact congrArg (fun s => loop step (s, l)) (stepFn_detab hb htb (detabFn t) a).symm

/-- **B&dM p.247**: `⦇[base,step]⦈ convert=loop step (base,id)` — `ofChars` is `convert`. -/
public theorem detab_loop [Detab]
    (xs : List Char) (r : Str × Nat) :
    cataR detabAlg (convert xs) r ↔ r = loop step ((SnocList.wrap (), 0), xs) := by
  rw [detabAlg_cata blank_ne_nl tb_ne_nl]
  show r = detabColFn (convert xs) ↔ _
  rw [convert, detabCol_foldl blank_ne_nl tb_ne_nl]
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

public theorem prefixS_pad [Detab] (y : Str) : ∀ k, prefixS y (pad y k)
  | 0 => prefixS_refl y
  | k + 1 => Or.inr (prefixS_pad y k)

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
public theorem expand_recip_snoc [Detab] (xs : Str) (a : Char) (ha : a ≠ tb)
    (ys : Str) (b : Char) :
    expandFn ys b = SnocList.snoc xs a
      ↔ (fillFn ys = SnocList.snoc xs a ∧ b = tb) ∨ (ys, b) = (xs, a) := by
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
public theorem fill_eq_snoc [Detab] (hn : 0 < n) {y x : Str} {a : Char}
    (hy : fillFn y = SnocList.snoc x a) : a = blank ∧ prefixS y x := by
  obtain ⟨k, hk⟩ : ∃ k, n - colFn y % n = k + 1 :=
    ⟨n - colFn y % n - 1, by have := Nat.mod_lt (colFn y) hn; omega⟩
  have hy' : SnocList.snoc (pad y k) blank = SnocList.snoc x a := by
    rw [← hy]; show _ = pad y (n - colFn y % n); rw [hk]; rfl
  injection hy' with h1 h2
  exact ⟨h2.symm, by rw [← h1]; exact prefixS_pad y k⟩

/-- On a tab stop, `fill x=x⧺[BL]`. -/
public theorem fill_eq_snoc_blank [Detab] (hn : 0 < n) (hb : blank ≠ nl)
    (x : Str) (h0 : colFn (SnocList.snoc x blank) % n = 0) :
    fillFn x = SnocList.snoc x blank := by
  have hc : colFn (SnocList.snoc x blank) = colFn x + 1 := if_neg hb
  rw [hc] at h0
  have hr := Nat.mod_lt (colFn x) hn
  have h1 : n - colFn x % n = 1 := by
    rcases Nat.lt_or_ge (colFn x % n + 1) n with hlt | hge
    · rw [mod_add_of_lt n _ 1 hlt] at h0; omega
    · omega
  show pad x (n - colFn x % n) = _
  rw [h1]; rfl

/-- Off a tab stop, a trailing blank does not change `fill`. -/
public theorem fill_snoc_blank [Detab] (hn : 0 < n) (hb : blank ≠ nl)
    (x : Str) (h : colFn (SnocList.snoc x blank) % n ≠ 0) :
    fillFn (SnocList.snoc x blank) = fillFn x := by
  have hc : colFn (SnocList.snoc x blank) = colFn x + 1 := if_neg hb
  have hr := Nat.mod_lt (colFn x) hn
  have hlt : colFn x % n + 1 < n := by
    rcases Nat.lt_or_ge (colFn x % n + 1) n with h1 | h1
    · exact h1
    · exfalso; apply h; rw [hc]
      have hd := Nat.div_add_mod (colFn x) n
      have e : colFn x + 1 = n * (colFn x / n + 1) := by rw [Nat.mul_succ]; omega
      rw [e]; exact Nat.mul_mod_right _ _
  have hm : colFn (SnocList.snoc x blank) % n = colFn x % n + 1 := by
    rw [hc]; exact mod_add_of_lt n _ 1 hlt
  show pad (SnocList.snoc x blank) (n - colFn (SnocList.snoc x blank) % n)
    = pad x (n - colFn x % n)
  have e : n - colFn x % n = 1 + (n - (colFn x % n + 1)) := by omega
  rw [hm, e, ← pad_add]; rfl

/-- **B&dM p.250** `(∃ys: fill ys=xs⧺[a]) ≡ a=BL ∧ col(xs⧺[a]) mod n=0`. -/
public theorem fill_exists_iff [Detab] (hn : 0 < n)
    (xs : Str) (a : Char) :
    (∃ ys, fillFn ys = SnocList.snoc xs a) ↔ a = blank ∧ colFn (SnocList.snoc xs a) % n = 0 := by
  constructor
  · rintro ⟨ys, hy⟩
    exact ⟨(fill_eq_snoc hn hy).1, by rw [← hy]; exact col_fill_mod hn blank_ne_nl ys⟩
  · rintro ⟨ha, h0⟩
    rw [ha] at h0 ⊢
    exact ⟨xs, fill_eq_snoc_blank hn blank_ne_nl xs h0⟩

/-- **B&dM p.250** `unfill`: `unfill[]=[]`, `unfill(xs⧺[a])=unfill xs` on a blank off a tab stop,
    `xs⧺[a]` otherwise — the shortest prefix with the same `fill`. -/
@[expose] public def unfillFn [Detab] : Str → Str
  | SnocList.wrap _ => SnocList.wrap ()
  | SnocList.snoc xs a =>
      if a = blank ∧ colFn (SnocList.snoc xs a) % n ≠ 0 then unfillFn xs
      else SnocList.snoc xs a

public theorem unfill_prefix [Detab] : ∀ x : Str, prefixS (unfillFn x) x
  | SnocList.wrap () => rfl
  | SnocList.snoc x a => by
    by_cases h : a = blank ∧ colFn (SnocList.snoc x a) % n ≠ 0
    · have e : unfillFn (SnocList.snoc x a) = unfillFn x := if_pos h
      rw [e]; exact Or.inr (unfill_prefix x)
    · have e : unfillFn (SnocList.snoc x a) = SnocList.snoc x a := if_neg h
      rw [e]; exact prefixS_refl _

public theorem fill_unfill [Detab] (hn : 0 < n) (hb : blank ≠ nl) :
    ∀ x : Str, fillFn (unfillFn x) = fillFn x
  | SnocList.wrap () => rfl
  | SnocList.snoc x a => by
    by_cases h : a = blank ∧ colFn (SnocList.snoc x a) % n ≠ 0
    · have e : unfillFn (SnocList.snoc x a) = unfillFn x := if_pos h
      have h2 : colFn (SnocList.snoc x blank) % n ≠ 0 := by rw [← h.1]; exact h.2
      rw [e, fill_unfill hn hb x, h.1, fill_snoc_blank hn hb x h2]
    · have e : unfillFn (SnocList.snoc x a) = SnocList.snoc x a := if_neg h
      rw [e]

/-- `unfill x` is below every prefix of `x` with the same `fill`. -/
public theorem unfill_least [Detab] (hn : 0 < n) (hb : blank ≠ nl) :
    ∀ (x y : Str), prefixS y x → fillFn y = fillFn x → prefixS (unfillFn x) y
  | SnocList.wrap (), y, hp, _ => by rw [(hp : y = SnocList.wrap ())]; exact rfl
  | SnocList.snoc z c, y, hp, hf => by
    rcases (hp : y = SnocList.snoc z c ∨ prefixS y z) with rfl | hpz
    · exact unfill_prefix _
    · obtain ⟨hc, hfz, hne⟩ := prefix_fill_snoc hn hb hpz hf
      have e : unfillFn (SnocList.snoc z c) = unfillFn z := if_pos ⟨hc, hne⟩
      rw [e]; exact unfill_least hn hb z y hpz hfz

/-- **B&dM p.250** `min V{y∣fill y=x⧺[BL]}=unfill x` on a tab stop (the set's pairs all carry
    `TB`, so their `V×U`-least is this one's). -/
public theorem unfill_est [Detab] (hn : 0 < n) (hb : blank ≠ nl) (x : Str)
    (h0 : colFn (SnocList.snoc x blank) % n = 0) (w : Str) :
    (Λ (fill°) ≫ est V) (SnocList.snoc x blank) w ↔ w = unfillFn x := by
  rw [Λ_comp_est_apply]
  have hfx := fill_eq_snoc_blank hn hb x h0
  have hmemU : SnocList.snoc x blank = fillFn (unfillFn x) :=
    ((fill_unfill hn hb x).trans hfx).symm
  have below : ∀ z, SnocList.snoc x blank = fillFn z → V (unfillFn x) z :=
    fun z hz => ⟨unfill_least hn hb x z (fill_eq_snoc hn hz.symm).2
      (hz.symm.trans hfx.symm), hmemU.symm.trans hz⟩
  constructor
  · rintro ⟨hw, hmin⟩
    exact prefixS_antisymm (hmin _ hmemU).1 (below w hw).1
  · rintro rfl; exact ⟨hmemU, below⟩

/-- **B&dM pp.250–251** `contract`: the greedy choice for the last character. -/
@[expose] public def contract [Detab] (x : Str) (a : Char) : Str × Char :=
  if a = blank ∧ colFn (SnocList.snoc x a) % n = 0 then (unfillFn x, tb) else (x, a)

/-- **B&dM p.250**, the case split: `min(V×U)Λexpand°(x⧺[a])` is `(unfill x,TB)` when `a=BL` and
    `col(x⧺[a]) mod n=0`, and `(x,a)` otherwise (for `a≠TB`). -/
public theorem entab_step [Detab] (hn : 0 < n)
    (x : Str) (a : Char) (ha : a ≠ tb) (p : Str × Char) :
    (Λ (expand°) ≫ est (rprodMap V U)) (SnocList.snoc x a) p ↔ p = contract x a := by
  rw [Λ_comp_est_apply]
  have hb : blank ≠ nl := blank_ne_nl
  have mem : ∀ q : Str × Char, expand° (SnocList.snoc x a) q ↔
      (fillFn q.1 = SnocList.snoc x a ∧ q.2 = tb) ∨ q = (x, a) :=
    fun q => eq_comm.trans (expand_recip_snoc x a ha q.1 q.2)
  unfold contract
  by_cases hc : a = blank ∧ colFn (SnocList.snoc x a) % n = 0
  · rw [if_pos hc]
    have hfx : fillFn x = SnocList.snoc x a := by
      have h0 := hc.2; rw [hc.1] at h0 ⊢; exact fill_eq_snoc_blank hn hb x h0
    have hmemU : fillFn (unfillFn x) = SnocList.snoc x a :=
      (fill_unfill hn hb x).trans hfx
    have below : ∀ q : Str × Char, ((fillFn q.1 = SnocList.snoc x a ∧ q.2 = tb) ∨ q = (x, a))
        → V (unfillFn x) q.1 ∧ U tb q.2 := by
      rintro q (⟨hq, _⟩ | rfl)
      · exact ⟨⟨unfill_least hn hb x q.1 (fill_eq_snoc hn hq).2
          (hq.trans hfx.symm), hmemU.trans hq.symm⟩, Or.inl rfl⟩
      · exact ⟨⟨unfill_prefix x, fill_unfill hn hb x⟩, Or.inl rfl⟩
    constructor
    · rintro ⟨hp, hmin⟩
      have h1 := hmin (unfillFn x, tb) ((mem _).mpr (Or.inl ⟨hmemU, rfl⟩))
      have hp2 : p.2 = tb := h1.2.elim id id
      rcases (mem p).mp hp with ⟨hq, _⟩ | hpx
      · exact Prod.ext (prefixS_antisymm h1.1.1 (below p (Or.inl ⟨hq, hp2⟩)).1.1) hp2
      · subst hpx; exact absurd hp2 ha
    · rintro rfl
      exact ⟨(mem _).mpr (Or.inl ⟨hmemU, rfl⟩), fun q hq => below q ((mem q).mp hq)⟩
  · rw [if_neg hc]
    have hno : ∀ q : Str × Char, ¬ (fillFn q.1 = SnocList.snoc x a ∧ q.2 = tb) :=
      fun q ⟨hq, _⟩ => hc ((fill_exists_iff hn x a).mp ⟨q.1, hq⟩)
    constructor
    · rintro ⟨hp, _⟩; exact ((mem p).mp hp).resolve_left (hno p)
    · rintro rfl
      refine ⟨(mem _).mpr (Or.inr rfl), fun q hq => ?_⟩
      obtain rfl := ((mem q).mp hq).resolve_left (hno q)
      exact ⟨⟨prefixS_refl x, rfl⟩, Or.inr rfl⟩

public theorem contract_slen_le [Detab] (x : Str) (a : Char) :
    length (contract x a).1 ≤ length x := by
  unfold contract; split
  · exact prefixS_slen_le (unfill_prefix x)
  · exact Nat.le_refl _

/-- **B&dM p.251** the greedy program: `entab[]=[]`, `entab(x⧺[a])=entab y⧺[b]` where
    `(y,b)=contract(x,a)`. -/
@[expose] public def entabFn [Detab] : Str → Str
  | SnocList.wrap _ => SnocList.wrap ()
  | SnocList.snoc x a => SnocList.snoc (entabFn (contract x a).1) (contract x a).2
termination_by x => length x
decreasing_by
  show length (contract x a).1 < length x + 1
  exact Nat.lt_succ_of_le (contract_slen_le x a)

/-- **B&dM p.251** `tbc`, the trailing blank count. -/
@[expose] public def tbcFn [Detab] : Str → Nat
  | SnocList.wrap _ => 0
  | SnocList.snoc xs a =>
      if a = blank ∧ colFn (SnocList.snoc xs a) % n ≠ 0 then tbcFn xs + 1 else 0

/-- **B&dM p.251**: `tbc[]=0`. -/
public theorem tbc_nil [Detab] : tbcFn (SnocList.wrap ()) = 0 := rfl

/-- **B&dM p.251**: `tbc(xs⧺[a])=tbc xs+1` on a blank off a tab stop, `0` otherwise. -/
public theorem tbc_snoc [Detab] (xs : Str) (a : Char) :
    tbcFn (SnocList.snoc xs a)
      = if a = blank ∧ colFn (SnocList.snoc xs a) % n ≠ 0 then tbcFn xs + 1 else 0 := rfl

/-- **(10.1)**, B&dM p.251: `entab xs=entab(unfill xs)⧺blanks(tbc xs)`. -/
public theorem entab_unfill [Detab] : ∀ xs : Str,
    entabFn xs = pad (entabFn (unfillFn xs)) (tbcFn xs)
  | SnocList.wrap () => rfl
  | SnocList.snoc z a => by
    by_cases h : a = blank ∧ colFn (SnocList.snoc z a) % n ≠ 0
    · have eu : unfillFn (SnocList.snoc z a) = unfillFn z := if_pos h
      have et : tbcFn (SnocList.snoc z a) = tbcFn z + 1 := if_pos h
      have ec : contract z a = (z, a) := if_neg fun h' => h.2 h'.2
      rw [eu, et, entabFn.eq_2, ec]
      show SnocList.snoc (entabFn z) a
        = SnocList.snoc (pad (entabFn (unfillFn z)) (tbcFn z)) blank
      rw [← entab_unfill z, h.1]
    · have eu : unfillFn (SnocList.snoc z a) = SnocList.snoc z a := if_neg h
      have et : tbcFn (SnocList.snoc z a) = 0 := if_neg h
      show _ = pad (entabFn (unfillFn (SnocList.snoc z a))) (tbcFn (SnocList.snoc z a))
      rw [eu, et]
      try rfl

/-- `tbc : String⟶ℕ`, `unfill`, `entab : String⟶String` as arrows. -/
@[expose] public def tbc [Detab] : dSL Unit Char ⟶ (⟨Nat⟩ : RelSet.{0}) := graph tbcFn
@[expose] public def unfill [Detab] : dSL Unit Char ⟶ dSL Unit Char := graph unfillFn
@[expose] public def entab [Detab] : dSL Unit Char ⟶ dSL Unit Char := graph entabFn

/-- `[base,op]` for `⟨tbc,col⟩`: `base=(0,0)`. -/
@[expose] public def tcOpFn [Detab] :
    (Fobj Unit Char (⟨Nat × Nat⟩ : RelSet.{0})).carrier → Nat × Nat
  | Sum.inl _ => (0, 0)
  | Sum.inr ((t, c), a) =>
      if a = blank ∧ (c + 1) % n ≠ 0 then (t + 1, c + 1)
      else if a = blank then (0, c + 1)
      else if a = nl then (0, 0) else (0, c + 1)

@[expose] public def tcAlg [Detab] :
    Fobj Unit Char (⟨Nat × Nat⟩ : RelSet.{0}) ⟶ (⟨Nat × Nat⟩ : RelSet.{0}) := graph tcOpFn

public theorem tcOp_step [Detab] (hb : blank ≠ nl) (x : Str) (a : Char) :
    tcOpFn (Sum.inr ((tbcFn x, colFn x), a))
      = (tbcFn (SnocList.snoc x a), colFn (SnocList.snoc x a)) := by
  by_cases ha : a = nl
  · have hab : a ≠ blank := fun h => hb (h.symm.trans ha)
    have hc : colFn (SnocList.snoc x a) = 0 := if_pos ha
    have ht : tbcFn (SnocList.snoc x a) = 0 := if_neg fun h => hab h.1
    rw [hc, ht]
    show (if a = blank ∧ (colFn x + 1) % n ≠ 0 then _ else if a = blank then _
      else if a = nl then ((0 : Nat), (0 : Nat)) else _) = _
    rw [if_neg (fun h => hab h.1), if_neg hab, if_pos ha]
  · have hc : colFn (SnocList.snoc x a) = colFn x + 1 := if_neg ha
    by_cases h : a = blank ∧ (colFn x + 1) % n ≠ 0
    · have ht : tbcFn (SnocList.snoc x a) = tbcFn x + 1 :=
        if_pos (by rw [hc]; exact h)
      rw [hc, ht]
      show (if a = blank ∧ (colFn x + 1) % n ≠ 0 then (tbcFn x + 1, colFn x + 1)
        else _) = _
      rw [if_pos h]
    · have ht : tbcFn (SnocList.snoc x a) = 0 := if_neg (by rw [hc]; exact h)
      rw [hc, ht]
      show (if a = blank ∧ (colFn x + 1) % n ≠ 0 then _ else if a = blank then ((0 : Nat), colFn x + 1)
        else if a = nl then _ else ((0 : Nat), colFn x + 1)) = _
      rw [if_neg h]
      by_cases hab : a = blank
      · rw [if_pos hab]
      · rw [if_neg hab, if_neg ha]

/-- **B&dM p.251**: `⟨tbc,col⟩=⦇[base,op]⦈`. -/
public theorem tbc_col_fold [Detab] :
    rpair tbc col = cataR tcAlg := by
  rw [tcAlg, cataR_graph _ (fun x => (tbcFn x, colFn x)) (fun _ => rfl)
    (fun x a => (tcOp_step blank_ne_nl x a).symm), tbc, col]
  exact rpair_graph _ _

-- The carrier of `triple`: `(entab (unfill x), (tbc x, col x))`.

/-- `[base,op]` for `triple`: `base=([],(0,0))`; the string grows only when the held blanks are
    cashed in — for a tab on a tab stop, or `blanks t⧺[a]` otherwise. -/
@[expose] public def tripleOpFn [Detab] : (Fobj Unit Char (⟨Str × (Nat × Nat)⟩ : RelSet.{0})).carrier → Str × (Nat × Nat)
  | Sum.inl _ => (SnocList.wrap (), (0, 0))
  | Sum.inr ((x, (t, c)), a) =>
      (if a = blank ∧ (c + 1) % n ≠ 0 then x
       else if a = blank then SnocList.snoc x tb
       else SnocList.snoc (pad x t) a,
       tcOpFn (Sum.inr ((t, c), a)))

@[expose] public def tripleAlg [Detab] : Fobj Unit Char (⟨Str × (Nat × Nat)⟩ : RelSet.{0}) ⟶ (⟨Str × (Nat × Nat)⟩ : RelSet.{0}) :=
  graph tripleOpFn

/-- `triple≜⟨unfill entab,⟨tbc,col⟩⟩`. -/
@[expose] public def triple [Detab] : dSL Unit Char ⟶ (⟨Str × (Nat × Nat)⟩ : RelSet.{0}) :=
  rpair (unfill ≫ entab) (rpair tbc col)

public theorem tripleOp_step [Detab] (hb : blank ≠ nl) (x : Str) (a : Char) :
    tripleOpFn (Sum.inr ((entabFn (unfillFn x), (tbcFn x, colFn x)), a))
      = (entabFn (unfillFn (SnocList.snoc x a)),
          (tbcFn (SnocList.snoc x a), colFn (SnocList.snoc x a))) := by
  refine Prod.ext ?_ (tcOp_step hb x a)
  show (if a = blank ∧ (colFn x + 1) % n ≠ 0 then _ else if a = blank then _ else _)
    = entabFn (unfillFn (SnocList.snoc x a))
  by_cases ha : a = blank
  · have hc : colFn (SnocList.snoc x a) = colFn x + 1 := if_neg fun h => hb (ha.symm.trans h)
    by_cases h : (colFn x + 1) % n = 0
    · rw [if_neg (fun h' => h'.2 h), if_pos ha]
      have eu : unfillFn (SnocList.snoc x a) = SnocList.snoc x a :=
        if_neg fun h' => h'.2 (by rw [hc]; exact h)
      have ec : contract x a = (unfillFn x, tb) :=
        if_pos ⟨ha, by rw [hc]; exact h⟩
      rw [eu, entabFn.eq_2, ec]
    · rw [if_pos ⟨ha, h⟩]
      have eu : unfillFn (SnocList.snoc x a) = unfillFn x :=
        if_pos ⟨ha, by rw [hc]; exact h⟩
      rw [eu]
  · rw [if_neg (fun h' => ha h'.1), if_neg ha]
    have eu : unfillFn (SnocList.snoc x a) = SnocList.snoc x a := if_neg fun h' => ha h'.1
    have ec : contract x a = (x, a) := if_neg fun h' => ha h'.1
    rw [eu, entabFn.eq_2, ec]
    exact congrArg (fun e => SnocList.snoc e a) (entab_unfill x).symm

/-- `triple` read as the function it is. -/
public theorem triple_graph [Detab] :
    triple = (graph (fun x => (entabFn (unfillFn x), (tbcFn x, colFn x)))
      : dSL Unit Char ⟶ (⟨Str × (Nat × Nat)⟩ : RelSet.{0})) := by
  rw [triple, unfill, entab, tbc, col, graph_comp, rpair_graph, rpair_graph]

/-- **B&dM pp.251–252**: `triple=⦇[base,op]⦈`. -/
public theorem triple_fold [Detab] :
    triple = cataR tripleAlg := by
  rw [triple_graph, tripleAlg, cataR_graph tripleOpFn
    (fun x => (entabFn (unfillFn x), (tbcFn x, colFn x)))
    (fun u => congrArg (fun e => (e, ((0 : Nat), (0 : Nat)))) (entabFn.eq_1 u))
    (fun x a => (tripleOp_step blank_ne_nl x a).symm)]

/-- Snoc-list concatenation `x⧺y`. -/
@[expose] public def catFn : Str → Str → Str
  | x, SnocList.wrap _ => x
  | x, SnocList.snoc y a => SnocList.snoc (catFn x y) a

@[expose] public def cat : (⟨Str × Str⟩ : RelSet.{0}) ⟶ dSL Unit Char := graph fun p => catFn p.1 p.2
@[expose] public def blanks [Detab] : (⟨Nat⟩ : RelSet.{0}) ⟶ dSL Unit Char :=
  graph (pad (SnocList.wrap ()))
@[expose] public def assocl : (⟨Str × (Nat × Nat)⟩ : RelSet.{0}) ⟶ (⟨(Str × Nat) × Nat⟩ : RelSet.{0}) :=
  graph fun p => ((p.1, p.2.1), p.2.2)

public theorem cat_blanks [Detab] (x : Str) :
    ∀ k, catFn x (pad (SnocList.wrap ()) k) = pad x k
  | 0 => rfl
  | k + 1 => congrArg (fun y => SnocList.snoc y blank) (cat_blanks x k)

/-- **B&dM p.252**: `entab=triple assocl π₁ (𝟙×blanks) cat`, from (10.1). -/
public theorem entab_triple [Detab] :
    entab = triple ≫ assocl ≫ (relProd (⟨Str × Nat⟩ : RelSet.{0}) ⟨Nat⟩).π₁ ≫ rprodMap (𝟙 (dSL Unit Char)) blanks ≫ cat := by
  rw [triple_graph, assocl, show (relProd (⟨Str × Nat⟩ : RelSet.{0}) ⟨Nat⟩).π₁ = graph Prod.fst from rfl, blanks, rprodMap_id_graph, cat, graph_comp,
    graph_comp, graph_comp, graph_comp, entab]
  exact congrArg graph (funext fun x => (entab_unfill x).trans (cat_blanks _ _).symm)

-- printing-only unexpanders: the two tupled algebras print as the book's `[base,step]`, `[base,op]`.
open Lean PrettyPrinter in
@[app_unexpander detabAlg] public meta def unexpandDetabAlg : Unexpander
  | `($_:ident) => `($(mkIdent (Name.mkSimple "[base,step]")))
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander tcAlg] public meta def unexpandTcAlg : Unexpander
  | `($_:ident) => `($(mkIdent (Name.mkSimple "[base,op]")))
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander tripleAlg] public meta def unexpandTripleAlg : Unexpander
  | `($_:ident) => `($(mkIdent (Name.mkSimple "[base,op]")))
  | _ => throw ()

-- The pointwise functions print under the book's names: the arrow of the same book name (`col`,
-- `detab`, …) holds the bare name, so the function beside it cannot.
open Lean PrettyPrinter in
@[app_unexpander entabFn] public meta def unexpandEntabFn : Unexpander
  | `($_ $xs*) => `($(mkIdent `entab) $xs*) | `($_:ident) => `($(mkIdent `entab)) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander tbcFn] public meta def unexpandTbcFn : Unexpander
  | `($_ $xs*) => `($(mkIdent `tbc) $xs*) | `($_:ident) => `($(mkIdent `tbc)) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander colFn] public meta def unexpandColFn : Unexpander
  | `($_ $xs*) => `($(mkIdent `col) $xs*) | `($_:ident) => `($(mkIdent `col)) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander fillFn] public meta def unexpandFillFn : Unexpander
  | `($_ $xs*) => `($(mkIdent `fill) $xs*) | `($_:ident) => `($(mkIdent `fill)) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander unfillFn] public meta def unexpandUnfillFn : Unexpander
  | `($_ $xs*) => `($(mkIdent `unfill) $xs*) | `($_:ident) => `($(mkIdent `unfill)) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander expandFn] public meta def unexpandExpandFn : Unexpander
  | `($_ $xs*) => `($(mkIdent `expand) $xs*) | `($_:ident) => `($(mkIdent `expand)) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander detabFn] public meta def unexpandDetabFn : Unexpander
  | `($_ $xs*) => `($(mkIdent `detab) $xs*) | `($_:ident) => `($(mkIdent `detab)) | _ => throw ()

-- Exercise 10.1's `step` is `loopStep f g`: `f`, `g` are the exercise's own data, and the bare name
-- `step` is §10.2's `detab` step.
open Lean PrettyPrinter in
@[app_unexpander loopStep] public meta def unexpandLoopStep : Unexpander
  | `($_ $_ $_ $x $xs*) => `($(mkIdent `step) $x $xs*) | `($_ $_ $_) => `($(mkIdent `step)) | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander SnocList.snoc] public meta def unexpandSnoc : Unexpander
  | `($_ $x $a) => `($(mkIdent `snoc) $x $a) | _ => throw ()

-- `pad y k` appends `k` blanks: the book's `y⧺blanks(k)`.
open Lean PrettyPrinter in
@[app_unexpander pad] public meta def unexpandPad : Unexpander
  -- the note's `⧺` node (`diag/StrDiagNames.lean`), by kind: this module cannot import its syntax
  | `($_ $y $k) => do pure (.node .none `Freyd.Alg.noteCat #[y, mkAtom "⧺", ← `($(mkIdent `blanks) $k)])
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander loop'] public meta def unexpandLoop' : Unexpander
  | `($_ $f $g $xs*) => `($(mkIdent `loop') ($f, $g) $xs*) | _ => throw ()

-- A first component is the note's `π₁` (B&dM's `outl`), applied pointwise as well.
open Lean PrettyPrinter in
@[app_unexpander Prod.fst] public meta def unexpandProdFst : Unexpander
  | `($_ $xs*) => `($(mkIdent `π₁) $xs*) | _ => throw ()

/-- `α°=[nil,snoc]°` is natural in the element type: `snocAlg_recip_strictNatural` with `α` spelled
    as the junction the §10 pictures carry. -/
public theorem alpha_recip_strictNatural :
    StrictNatural
      (Relator.sum (Relator.const (dL Unit))
        (Relator.prod (snocRelator Unit) (Relator.idRelator RelSet.{0})))
      (snocRelator Unit)
      (fun A => (junc (sumCop _ _) nil snoc
        : Fobj Unit A.carrier (dSL Unit A.carrier) ⟶ dSL Unit A.carrier)°) := by
  intro A B R
  have h := snocAlg_recip_strictNatural (L := Unit) R
  dsimp only at h ⊢
  rw [con_eq_junc, con_eq_junc] at h
  exact h

-- printing-only: `String` for the carrier (core's `String` holds the name).
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Detab.Str] public meta def unexpandDetabStr : Unexpander
  | _ => `($(mkIdent `String))

/-! ## `EntabRun`: the greedy step of `entab` on `RelRep`, and one run at tab width `4` -/

section EntabRun

deriving instance DecidableEq for SnocList

/-- Every prefix of a string, the string itself first. -/
@[expose] public def prefixes : Str → List Str
  | SnocList.wrap _ => [SnocList.wrap ()]
  | SnocList.snoc y c => SnocList.snoc y c :: prefixes y

public theorem mem_prefixes : ∀ {x y : Str}, x ∈ prefixes y ↔ prefixS x y
  | _, SnocList.wrap () => List.mem_singleton
  | _, SnocList.snoc _ _ => List.mem_cons.trans (or_congr Iff.rfl mem_prefixes)

/-- The decompositions `Λ(expand°)(y⧺[a])`: each prefix of `y` that fills to `y⧺[a]`, with `TB`,
    then `(y,a)` unless `a=TB`; `nil` has none. -/
@[expose] public def cands [Detab] : Str → List (Str × Char)
  | SnocList.wrap _ => []
  | SnocList.snoc ys a =>
      ((prefixes ys).filter fun zs => decide (fillFn zs = SnocList.snoc ys a)).map (·, tb)
        ++ if a = tb then [] else [(ys, a)]

/-- `cands` enumerates `expand°`. -/
public theorem rel_cands [Detab] (hn : 0 < n) :
    ((RelRep.enum cands).rel : dSL Unit Char ⟶ ⟨Str × Char⟩) = expand° :=
  hom_ext fun x ⟨y, b⟩ => by
    show (y, b) ∈ cands x ↔ x = expandFn y b
    cases x with
    | wrap u =>
      exact ⟨fun h => absurd h List.not_mem_nil, fun h => absurd h.symm (expand_ne_nil hn y b)⟩
    | snoc x a =>
      simp only [cands, List.mem_append, List.mem_map, List.mem_filter, mem_prefixes,
        decide_eq_true_eq, Prod.mk.injEq, expandFn]
      by_cases hb : b = tb
      · rw [if_pos hb]
        constructor
        · rintro (⟨z, ⟨_, hz⟩, rfl, _⟩ | h)
          · exact hz.symm
          · by_cases ha : a = tb
            · rw [if_pos ha] at h; exact absurd h List.not_mem_nil
            · rw [if_neg ha, List.mem_singleton, Prod.mk.injEq] at h
              exact absurd (h.2.symm.trans hb).symm (fun e => ha e.symm)
        · intro h
          exact Or.inl ⟨y, ⟨(fill_eq_snoc hn h.symm).2, h.symm⟩, rfl, hb.symm⟩
      · rw [if_neg hb]
        constructor
        · rintro (⟨_, _, _, e⟩ | h)
          · exact absurd e.symm hb
          · by_cases ha : a = tb
            · rw [if_pos ha] at h; exact absurd h List.not_mem_nil
            · rw [if_neg ha, List.mem_singleton, Prod.mk.injEq] at h
              rw [h.1, h.2]
        · intro h
          injection h with h1 h2
          subst h1; subst h2
          exact Or.inr (by rw [if_neg hb, List.mem_singleton])

/-- `V×U` decided on two decompositions. -/
@[expose] public def vu [Detab] (p q : Str × Char) : Bool :=
  decide (p.1 ∈ prefixes q.1 ∧ fillFn p.1 = fillFn q.1 ∧ (p.2 = tb ∨ p.2 = q.2))

/-- `V×U` as a `RelRep` test. -/
@[expose] public def VUt [Detab] : RelTest (Str × Char) (Str × Char) := .test vu

public theorem rel_VUt [Detab] :
    (VUt.rel : (⟨Str × Char⟩ : RelSet.{0}) ⟶ ⟨Str × Char⟩) = rprodMap V U :=
  hom_ext fun p q => by
    show decide _ = true ↔ (prefixS p.1 q.1 ∧ fillFn p.1 = fillFn q.1) ∧ (p.2 = tb ∨ p.2 = q.2)
    rw [decide_eq_true_iff, mem_prefixes]
    exact and_assoc.symm

/-- The greedy step: the `V×U`-least decompositions. -/
@[expose] public def estC [Detab] (xs : Str) : List (Str × Char) := RelRep.estList vu (cands xs)

/-- `estC` is `RelRep.est (V×U)` of `cands`. -/
public theorem estC_eq [Detab] : RelRep.est VUt (.enum cands) = .enum estC := rfl

/-- `estC` computes `Λ(expand°) est(V×U)`, the step of `entab_branch`. -/
public theorem rel_estC [Detab] (hn : 0 < n) :
    ((RelRep.enum estC).rel : dSL Unit Char ⟶ ⟨Str × Char⟩) = Λ (expand°) ≫ est (rprodMap V U) :=
  calc ((RelRep.enum estC).rel : dSL Unit Char ⟶ ⟨Str × Char⟩)
      = Λ ((RelRep.enum cands).rel : dSL Unit Char ⟶ ⟨Str × Char⟩) ≫ est VUt.rel :=
        by rw [← estC_eq]; exact RelRep.rel_est _ _
    _ = Λ (expand°) ≫ est (rprodMap V U) := by rw [rel_cands hn, rel_VUt]

/-- On `x⧺[a]` with `a≠TB` the greedy step returns `contract x a` and nothing else (`entab_step`). -/
public theorem estC_snoc [Detab] (hn : 0 < n) (x : Str) (a : Char) (ha : a ≠ tb)
    (p : Str × Char) : p ∈ estC (SnocList.snoc x a) ↔ p = contract x a := by
  have h : (RelRep.enum estC).rel (SnocList.snoc x a) p
      ↔ (Λ (expand°) ≫ est (rprodMap V U)) (SnocList.snoc x a) p := by rw [rel_estC hn]
  exact h.trans (entab_step hn x a ha p)

/-- The greedy step: the first `V×U`-least decomposition, then `X` on its string. -/
@[expose] public def entabStep [Detab] (X : Str → Str) : Str → Str
  | SnocList.wrap _ => SnocList.wrap ()
  | SnocList.snoc x a =>
      match estC (SnocList.snoc x a) with
      | p :: _ => SnocList.snoc (X p.1) p.2
      | [] => SnocList.snoc x a

/-- **The program**: every decomposition shortens the string, so `entabStep` recurses on the
    length. -/
@[expose] public def entabR [Detab] (xs : Str) : Str := RelRep.hylo length id entabStep xs

/-- B&dM's characters at tab width `4`. -/
@[expose] public def book4 : Detab := ⟨4, '\t', '\n', ' ', by decide, by decide⟩

/-- The note's line: `ab`, a tab, `c d`. -/
@[expose] public def entabXs : Str := convert ['a', 'b', '\t', 'c', ' ', 'd']

section
attribute [local instance] book4

/-- **entab-run**, the input. -/
public theorem run_input : entabXs = convert ['a', 'b', '\t', 'c', ' ', 'd'] := rfl

/-- **entab-run**: the tab after `ab` becomes the two blanks that reach column `4`. -/
public theorem run_detab :
    detabFn entabXs = SnocList.snoc (SnocList.snoc (SnocList.snoc (SnocList.snoc (SnocList.snoc
      (SnocList.snoc (SnocList.snoc (SnocList.wrap ()) 'a') 'b') ' ') ' ') 'c') ' ') 'd' := by
  decide

/-- **entab-run**: the decompositions of `ab` and two blanks, which ends on the tab stop. -/
public theorem run_cands :
    cands (SnocList.snoc (SnocList.snoc (SnocList.snoc (SnocList.snoc (SnocList.wrap ()) 'a') 'b')
      ' ') ' ')
      = [(SnocList.snoc (SnocList.snoc (SnocList.snoc (SnocList.wrap ()) 'a') 'b') ' ', '\t'),
         (SnocList.snoc (SnocList.snoc (SnocList.wrap ()) 'a') 'b', '\t'),
         (SnocList.snoc (SnocList.snoc (SnocList.snoc (SnocList.wrap ()) 'a') 'b') ' ', ' ')] := by
  decide

/-- **entab-run**: the `V×U`-least of them: `ab` and a tab. -/
public theorem run_estC :
    estC (SnocList.snoc (SnocList.snoc (SnocList.snoc (SnocList.snoc (SnocList.wrap ()) 'a') 'b')
      ' ') ' ')
      = [(SnocList.snoc (SnocList.snoc (SnocList.wrap ()) 'a') 'b', '\t')] := by
  decide

/-- **entab-run**: `entab` gives the input back, the tab restored and the lone blank kept. -/
public theorem run_entab :
    entabR (detabFn entabXs) = SnocList.snoc (SnocList.snoc (SnocList.snoc (SnocList.snoc
      (SnocList.snoc (SnocList.snoc (SnocList.wrap ()) 'a') 'b') '\t') 'c') ' ') 'd' := by
  decide

end

end EntabRun

end Freyd.Alg.RelSet.Detab

-- printing-only: `prefixS` is the book's pointwise `prefix`; the arrow `«prefix»` holds the name.
open Lean PrettyPrinter in
@[app_unexpander Freyd.Alg.RelSet.Detab.prefixS] public meta def Freyd.Alg.RelSet.Detab.unexpandDetabPrefix : Unexpander
  | `($_ $x $y) => `($(mkIdent `prefix) $x $y)
  | _ => `($(mkIdent `prefix))
