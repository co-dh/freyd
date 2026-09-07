/-
  Bird & de Moor, *Algebra of Programming* §9.4  Data compression (book pp. 238-243).

  Compress a string by textual substitution: the output is a sequence of `Code`s, each either a
  character or a pointer back into the part of the string already decoded.  The specification is
  `Λ(decode°) est(R)` with `R ≜ size≤size°`, and `decode ≜ ⦇[nil,extend]⦈ : [Code]⟶String` over
  `AOP.A6_SnocList`'s `F X = 1+(X×Code)` — SNOC-lists, as §9.4 requires, because a pointer refers
  backwards.  `extend` is PARTIAL, so `[nil,extend]` is a relation and so is `decode`.

  What is certified here is the note's `code-defn` and the first step of `code-laws`, Theorem 9.2
  (`AOP.A9_1.dynamic_programming_thin`) at `Q ≜ F(⊤+⊤,prefix°) = 𝟙+(prefix°×(⊤+⊤))`:

  * `code_mono` — `F(⊤+⊤,R)α⊑αR`, the book's "routine" condition: `snoc` adds one code element
    to both sides and its cost is a constant, so it never reverses `≤` on sizes;
  * `decode_prefix`/`code_V` — Proposition 9.4's `hV`, the book's `init·decode ⊆ decode·R`
    (p.240) proved directly at `prefix` rather than at `init` and closed up: a prefix of the
    decoded string is decoded by a code sequence no more expensive.  The last character is
    dropped by dropping the last `sym`, by shortening the last pointer's target (same cost), or
    by dropping that pointer (cheaper);
  * `code_thin_condition` — Theorem 9.2's `hQ`, Proposition 9.4 at `U ≜ ⊤+⊤` and `V ≜ prefix°`;
  * `code_laws` — the note's `code-laws` headline, Theorem 9.2 at those data.

  NOT DONE, and why: `code-laws` rows 3-4 (`lrt`, `reduce`, and `encode = (null→nil, reduce
  list((encode×𝟙)snoc) minlist R)`) need the sorted-list interface `list`/`minlist` that §8.3
  keeps abstract and a longest-repeated-tail algorithm the book itself only sketches — the same
  boundary `AOP.A8_4_Knapsack`'s last row stops at.

  Two modelling notes.  `String⁺` is not a separate type: `extend` guards its pointer with
  `zs≠nil`, which is exactly what `String⁺` asks of it.  `Str`/`slen`/`prefix` are declared here
  rather than imported from §10.2 (`AOP.A10_2_Detab`), which has the same snoc-string helpers,
  because a chapter-9 module must not import chapter 10.  `Real` is `Int`, as everywhere in this
  repo's chapter 8-10 case studies, and the book's "amount of space" is made explicit as `0≤c`,
  `0≤p`.
-/
module

public import AOP.A9_1
public import AOP.A6_SnocList
public import AOP.A5_6_ListCombinators

namespace Freyd.Alg.RelSet.Code

open Freyd Freyd.Alg Freyd.Alg.RelSet.SL

/-! ## `code-defn` -/

/-- **code-defn**: `String=[Char]`, a snoc-list of characters. -/
@[expose] public abbrev Str : Type := SnocList Unit Char

/-- The object carrying `String`. -/
@[expose] public abbrev dStr : RelSet.{0} := dSL Unit Char

/-- **code-defn**: `Code::=sym Char∣ptr (String,String⁺)`.  `String⁺` is the guard `zs≠nil`
    inside `extend`, not a second datatype. -/
public inductive Code where
  | sym : Char → Code
  | ptr : Str → Str → Code

/-- The object carrying `Code`. -/
@[expose] public abbrev dCode : RelSet.{0} := (⟨Code⟩ : RelSet.{0})

/-- The object carrying `[Code]`, the code sequences. -/
@[expose] public abbrev dCodes : RelSet.{0} := dSL Unit Code

/-- **code-defn**: `⧺` on snoc-strings. -/
@[expose] public def sappend (x : Str) : Str → Str
  | SnocList.wrap _ => x
  | SnocList.snoc y a => SnocList.snoc (sappend x y) a

/-- The length of a snoc-string. -/
@[expose] public def slen : Str → Nat
  | SnocList.wrap _ => 0
  | SnocList.snoc x _ => slen x + 1

/-- `x` is a prefix of `y`. -/
@[expose] public def prefixS : Str → Str → Prop
  | x, SnocList.wrap _ => x = SnocList.wrap ()
  | x, SnocList.snoc y a => x = SnocList.snoc y a ∨ prefixS x y

/-- **code-defn**: `prefix`, mirrored to diagram order — `prefixR x ys` reads "`ys` is a prefix
    of `x`", so `prefix°` is "is a prefix of". -/
@[expose] public def prefixR : dStr ⟶ dStr := fun x ys => prefixS ys x

/-- `x` is a PROPER prefix of `y` — the book's `init⁺`.  Properness is spelled as strictly
    shorter, which on prefixes is the same thing and needs no injectivity lemma. -/
@[expose] public def properPrefixS (x y : Str) : Prop := prefixS x y ∧ slen x < slen y

/-! ## Elementary facts about `sappend` and `prefixS` -/

public theorem slen_sappend : ∀ (x y : Str), slen (sappend x y) = slen x + slen y
  | _, SnocList.wrap _ => rfl
  | x, SnocList.snoc y a => by
    show slen (sappend x y) + 1 = slen x + (slen y + 1)
    rw [slen_sappend x y]
    omega

public theorem sappend_assoc : ∀ (x y z : Str), sappend (sappend x y) z = sappend x (sappend y z)
  | _, _, SnocList.wrap _ => rfl
  | x, y, SnocList.snoc z a => by
    show SnocList.snoc (sappend (sappend x y) z) a = SnocList.snoc (sappend x (sappend y z)) a
    rw [sappend_assoc x y z]

/-- A non-empty snoc-string is not `nil` — `String⁺`'s whole content, as `extend` uses it. -/
public theorem snoc_ne_wrap (x : Str) (a : Char) : SnocList.snoc x a ≠ SnocList.wrap () := by
  intro h
  have hs : slen x + 1 = 0 := by
    show slen (SnocList.snoc x a) = slen (SnocList.wrap ())
    rw [h]
  omega

public theorem prefixS_refl : ∀ x : Str, prefixS x x
  | SnocList.wrap _ => rfl
  | SnocList.snoc _ _ => Or.inl rfl

public theorem prefixS_slen_le : ∀ {x y : Str}, prefixS x y → slen x ≤ slen y
  | x, SnocList.wrap _, h => by rw [(h : x = SnocList.wrap ())]; exact Nat.zero_le _
  | x, SnocList.snoc y _, h => by
    rcases h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_succ_of_le (prefixS_slen_le h)

public theorem prefixS_trans : ∀ {x y z : Str}, prefixS x y → prefixS y z → prefixS x z
  | _, y, SnocList.wrap _, hxy, hyz => by rw [(hyz : y = SnocList.wrap ())] at hxy; exact hxy
  | _, _, SnocList.snoc _ _, hxy, hyz => by
    rcases hyz with rfl | hyz
    · exact hxy
    · exact Or.inr (prefixS_trans hxy hyz)

/-- A prefix is the string with a remainder appended. -/
public theorem prefixS_append : ∀ {u v : Str}, prefixS u v → ∃ t, sappend u t = v
  | u, SnocList.wrap _, h => ⟨SnocList.wrap (), h⟩
  | _, SnocList.snoc v a, h => by
    rcases h with rfl | h
    · exact ⟨SnocList.wrap (), rfl⟩
    · obtain ⟨t, ht⟩ := prefixS_append h
      exact ⟨SnocList.snoc t a, by rw [show sappend _ (SnocList.snoc t a)
        = SnocList.snoc (sappend _ t) a from rfl, ht]⟩

/-- Two prefixes of one string: the shorter is a prefix of the longer. -/
public theorem prefixS_of_slen_le : ∀ {u v t : Str}, prefixS u (sappend v t) → slen u ≤ slen v →
    prefixS u v
  | _, _, SnocList.wrap _, h, _ => h
  | _, v, SnocList.snoc t _, h, hlen => by
    rcases h with rfl | h
    · exfalso
      have hu : slen (sappend v t) + 1 ≤ slen v := hlen
      rw [slen_sappend] at hu
      omega
    · exact prefixS_of_slen_le h hlen

/-- Appending on the left is monotonic for `prefixS`. -/
public theorem prefixS_sappend_mono (u : Str) : ∀ {v w : Str}, prefixS v w →
    prefixS (sappend u v) (sappend u w)
  | v, SnocList.wrap _, h => by rw [(h : v = SnocList.wrap ())]; exact prefixS_refl _
  | _, SnocList.snoc w _, h => by
    rcases h with rfl | h
    · exact prefixS_refl _
    · exact Or.inr (prefixS_sappend_mono u h)

/-- A prefix of `xs⧺zs` is a prefix of `xs`, or `xs` extended by a prefix of `zs`. -/
public theorem prefixS_sappend_split (x u : Str) : ∀ (v : Str), prefixS x (sappend u v) →
    prefixS x u ∨ ∃ v', prefixS v' v ∧ x = sappend u v'
  | SnocList.wrap _, h => Or.inl h
  | SnocList.snoc v a, h => by
    rcases h with rfl | h
    · exact Or.inr ⟨SnocList.snoc v a, prefixS_refl _, rfl⟩
    · rcases prefixS_sappend_split x u v h with h | ⟨v', hv', hx⟩
      · exact Or.inl h
      · exact Or.inr ⟨v', Or.inr hv', hx⟩

/-- Shortening a pointer's target keeps it a pointer: `ys⧺zs'` and `xs⧺zs'` are both prefixes of
    the one string `xs⧺zs`, and the first is the shorter. -/
public theorem properPrefixS_shorten {xs ys zs zs' : Str}
    (h : properPrefixS (sappend ys zs) (sappend xs zs)) (hz : prefixS zs' zs) :
    properPrefixS (sappend ys zs') (sappend xs zs') := by
  obtain ⟨hp, hl⟩ := h
  rw [slen_sappend, slen_sappend] at hl
  obtain ⟨t, ht⟩ := prefixS_append hz
  have hsplit : sappend xs zs = sappend (sappend xs zs') t := by rw [sappend_assoc, ht]
  have h2 : prefixS (sappend ys zs') (sappend xs zs) :=
    prefixS_trans (prefixS_sappend_mono ys hz) hp
  rw [hsplit] at h2
  have hlen : slen (sappend ys zs') ≤ slen (sappend xs zs') := by
    rw [slen_sappend, slen_sappend]; omega
  refine ⟨prefixS_of_slen_le h2 hlen, ?_⟩
  rw [slen_sappend, slen_sappend]
  omega

/-! ## `decode`, `size` and the order `R` -/

/-- **code-defn**: `extend (xs,sym a)=xs⧺[a]`, and `extend (xs,ptr (ys,zs))=xs⧺zs` when `zs` is
    non-empty and `ys⧺zs` is a proper prefix of `xs⧺zs` — a PARTIAL function. -/
@[expose] public def extendP : Str × Code → Str → Prop
  | (xs, Code.sym a), w => w = SnocList.snoc xs a
  | (xs, Code.ptr ys zs), w =>
      w = sappend xs zs ∧ zs ≠ SnocList.wrap ()
        ∧ properPrefixS (sappend ys zs) (sappend xs zs)

/-- **code-defn**: `[nil,extend]`, the algebra `decode` folds. -/
@[expose] public def extendAlg : (F Unit Code).obj dStr ⟶ dStr := fun u w =>
  match u with
  | Sum.inl _ => w = SnocList.wrap ()
  | Sum.inr q => extendP q w

/-- **code-defn**: `decode≜⦇[nil,extend]⦈ : [Code]⟶String`, a partial function because `extend`
    is one. -/
@[expose] public def decode : dCodes ⟶ dStr := cataR extendAlg

/-- **code-defn**: `c`, `p` the constant costs of a symbol and a pointer. -/
@[expose] public def bytes (c p : Int) : Code → Int
  | Code.sym _ => c
  | Code.ptr _ _ => p

/-- **code-defn**: the algebra `[zero,distr [𝟙×c,𝟙×p] plus]` whose fold is `size`. -/
@[expose] public def sizeAlgFn (c p : Int) :
    (Fobj Unit Code (⟨Int⟩ : RelSet.{0})).carrier → Int
  | Sum.inl _ => 0
  | Sum.inr q => q.1 + bytes c p q.2

/-- **code-defn**: `size`, read as the function it is. -/
@[expose] public def sizeFn (c p : Int) : SnocList Unit Code → Int
  | SnocList.wrap _ => 0
  | SnocList.snoc cs e => sizeFn c p cs + bytes c p e

variable (c p : Int)

/-- **code-defn**: `size≜⦇[zero,distr [𝟙×c,𝟙×p] plus]⦈` — the fold of `sizeAlgFn` IS `sizeFn`. -/
public theorem size_cata :
    cataR (graph (sizeAlgFn c p) :
        Fobj Unit Code (⟨Int⟩ : RelSet.{0}) ⟶ (⟨Int⟩ : RelSet.{0}))
      = (graph (sizeFn c p) : dCodes ⟶ (⟨Int⟩ : RelSet.{0})) := by
  apply hom_ext; intro cs
  induction cs with
  | wrap _ => exact fun _ => Iff.rfl
  | snoc cs' e ih =>
    intro n
    constructor
    · rintro ⟨m, hm, hn⟩
      have hm' : m = sizeFn c p cs' := (ih m).mp hm
      subst hm'
      exact hn
    · intro h
      exact ⟨sizeFn c p cs', (ih _).mpr rfl, h⟩

/-- **code-defn**: `R≜size≤size°`. -/
@[expose] public def R (c p : Int) : dCodes ⟶ dCodes := fun u v => sizeFn c p u ≤ sizeFn c p v

/-- `R = size≤size°`, point-free. -/
public theorem R_eq :
    R c p = (graph (sizeFn c p) : dCodes ⟶ (⟨Int⟩ : RelSet.{0})) ≫ ListRel.leq
      ≫ (graph (sizeFn c p) : dCodes ⟶ (⟨Int⟩ : RelSet.{0}))° := by
  apply hom_ext; intro u v
  constructor
  · intro h; exact ⟨sizeFn c p u, rfl, sizeFn c p v, h, rfl⟩
  · rintro ⟨m, hm, n, hmn, hn⟩
    obtain rfl : m = sizeFn c p u := hm
    obtain rfl : n = sizeFn c p v := hn
    exact hmn

/-- `R°` is transitive — Theorem 9.2's `htrans`. -/
public theorem R_recip_trans : (R c p)° ≫ (R c p)° ⊑ (R c p)° :=
  le_iff.mpr fun u w h => by
    obtain ⟨v, h1, h2⟩ := h
    exact Int.le_trans (h2 : sizeFn c p w ≤ sizeFn c p v) (h1 : sizeFn c p v ≤ sizeFn c p u)

/-! ## `code-defn`: `U`, `V`, `Q` -/

/-- **code-defn**: `U≜⊤+⊤`, the universal relation on symbols beside the universal relation on
    pointers — between a symbol and a pointer nothing can be decided in advance. -/
@[expose] public def U : dCode ⟶ dCode := fun e f =>
  match e, f with
  | Code.sym _, Code.sym _ => True
  | Code.ptr _ _, Code.ptr _ _ => True
  | _, _ => False

/-- The book's "the sizes of symbols and pointers are constants", `[c,p](⊤+⊤)=[c,p]`. -/
public theorem bytes_U : ∀ {e f : Code}, U e f → bytes c p e = bytes c p f
  | Code.sym _, Code.sym _, _ => rfl
  | Code.ptr _ _, Code.ptr _ _, _ => rfl
  | Code.sym _, Code.ptr _ _, h => h.elim
  | Code.ptr _ _, Code.sym _, h => h.elim

/-- **code-defn**: `Q≜F(⊤+⊤,prefix°)=𝟙+(prefix°×(⊤+⊤))`. -/
@[expose] public def Q : (F Unit Code).obj dStr ⟶ (F Unit Code).obj dStr := fun u v =>
  match u, v with
  | Sum.inl _, Sum.inl _ => True
  | Sum.inr q, Sum.inr r => prefixS q.1 r.1 ∧ U q.2 r.2
  | _, _ => False

/-! ## `code-laws` -/

/-- **code-laws**, second row: `F(⊤+⊤,R)α⊑αR`, the book's "routine" monotonicity condition —
    `snoc` adds one code element to both sides and its cost is a constant, so it never reverses
    `≤` on sizes. -/
public theorem code_mono : MonotonicAlg (F := F Unit Code) (graph con) ((R c p)°) :=
  le_iff.mpr fun u out h => by
    obtain ⟨v, hFv, hout⟩ := h
    obtain rfl : out = con v := hout
    cases u with
    | inl _ =>
      cases v with
      | inl _ => exact ⟨SnocList.wrap (), rfl, Int.le_refl _⟩
      | inr _ => exact hFv.elim
    | inr q =>
      cases v with
      | inl _ => exact hFv.elim
      | inr r =>
        refine ⟨SnocList.snoc q.1 q.2, rfl, ?_⟩
        show sizeFn c p r.1 + bytes c p r.2 ≤ sizeFn c p q.1 + bytes c p q.2
        rw [← (hFv.2 : q.2 = r.2)]
        exact Int.add_le_add_right (hFv.1 : sizeFn c p r.1 ≤ sizeFn c p q.1) _

/-- **code-laws**, third row (Proposition 9.1, B&dM p.241): the decompositions of a non-empty
    string — take the last character as a symbol, or end with a pointer. -/
public theorem code_decomp (ws : Str) (a : Char) (xs : Str) (e : Code) :
    extendP (xs, e) (SnocList.snoc ws a)
      ↔ (e = Code.sym a ∧ xs = ws)
        ∨ ∃ ys zs, e = Code.ptr ys zs ∧ zs ≠ SnocList.wrap ()
            ∧ sappend xs zs = SnocList.snoc ws a
            ∧ properPrefixS (sappend ys zs) (SnocList.snoc ws a) := by
  cases e with
  | sym b =>
    constructor
    · intro h
      have h' : SnocList.snoc ws a = SnocList.snoc xs b := h
      injection h' with h1 h2
      refine Or.inl ⟨?_, h1.symm⟩
      rw [h2]
    · rintro (⟨h1, h2⟩ | ⟨ys, zs, h1, -⟩)
      · injection h1 with h1
        show SnocList.snoc ws a = SnocList.snoc xs b
        rw [h2, h1]
      · exact Code.noConfusion h1
  | ptr ys zs =>
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine Or.inr ⟨ys, zs, rfl, h2, h1.symm, ?_⟩
      rw [h1]; exact h3
    · rintro (⟨h1, -⟩ | ⟨ys', zs', h1, h2, h3, h4⟩)
      · exact Code.noConfusion h1
      · injection h1 with h1 h1'
        subst h1; subst h1'
        refine ⟨h3.symm, h2, ?_⟩
        rw [h3]; exact h4

/-- **code-laws**, third row: the book's `init·decode ⊆ decode·R` (p.240), proved at `prefix`
    directly.  Dropping the last character drops the last `sym` (cheaper), shortens the last
    pointer's target (same cost), or drops that pointer (cheaper); everything earlier is the
    induction hypothesis. -/
public theorem decode_prefix (hc : 0 ≤ c) (hp : 0 ≤ p) :
    ∀ (cs : SnocList Unit Code) (w : Str), decode cs w → ∀ x : Str, prefixS x w →
      ∃ cs₀, decode cs₀ x ∧ sizeFn c p cs₀ ≤ sizeFn c p cs := by
  intro cs
  induction cs with
  | wrap _ =>
    intro w hw x hx
    obtain rfl : w = SnocList.wrap () := hw
    obtain rfl : x = SnocList.wrap () := hx
    exact ⟨SnocList.wrap (), rfl, Int.le_refl _⟩
  | snoc cs e ih =>
    intro w hw x hx
    obtain ⟨w', hw', hstep⟩ := hw
    cases e with
    | sym a =>
      obtain rfl : w = SnocList.snoc w' a := hstep
      rcases hx with rfl | hx
      · exact ⟨SnocList.snoc cs (Code.sym a), ⟨w', hw', rfl⟩, Int.le_refl _⟩
      · obtain ⟨cs₀, hcs₀, hle⟩ := ih w' hw' x hx
        refine ⟨cs₀, hcs₀, ?_⟩
        show sizeFn c p cs₀ ≤ sizeFn c p cs + c
        omega
    | ptr ys zs =>
      obtain ⟨rfl, hzs, hpp⟩ := hstep
      rcases prefixS_sappend_split x w' zs hx with hxu | ⟨zs', hzs', rfl⟩
      · obtain ⟨cs₀, hcs₀, hle⟩ := ih w' hw' x hxu
        refine ⟨cs₀, hcs₀, ?_⟩
        show sizeFn c p cs₀ ≤ sizeFn c p cs + p
        omega
      · cases zs' with
        | wrap _ =>
          refine ⟨cs, hw', ?_⟩
          show sizeFn c p cs ≤ sizeFn c p cs + p
          omega
        | snoc zs₀ b =>
          refine ⟨SnocList.snoc cs (Code.ptr ys (SnocList.snoc zs₀ b)), ⟨w', hw', ?_⟩, ?_⟩
          · exact ⟨rfl, snoc_ne_wrap zs₀ b, properPrefixS_shorten hpp hzs'⟩
          · show sizeFn c p cs + p ≤ sizeFn c p cs + p
            exact Int.le_refl _

/-- **code-laws**, third row: Proposition 9.4's `hV`, `prefix° decode°⊑decode° R`. -/
public theorem code_V (hc : 0 ≤ c) (hp : 0 ≤ p) :
    (prefixR)° ≫ decode° ⊑ decode° ≫ R c p :=
  le_iff.mpr fun x cs h => by
    obtain ⟨w, hV, hw⟩ := h
    exact decode_prefix c p hc hp cs w hw x hV

/-- **code-laws**, second row: Theorem 9.2's thinning condition, Proposition 9.4 at `U≜⊤+⊤` and
    `V≜prefix°`.  `U` leaves the code element free but pins its cost, `code_V` supplies the
    cheaper code sequence for the shorter output, and `snoc` adds the same constant to both. -/
public theorem code_thin_condition (hc : 0 ≤ c) (hp : 0 ≤ p) :
    Q ≫ (F Unit Code).map (decode°) ≫ graph con
      ⊑ (F Unit Code).map (decode°) ≫ graph con ≫ R c p :=
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
          exact ⟨Sum.inl (), rfl, SnocList.wrap (), rfl, Int.le_refl _⟩
    | inr q =>
      cases v with
      | inl _ => exact hQ.elim
      | inr r =>
        cases w with
        | inl _ => exact hFw.elim
        | inr s =>
          obtain rfl : out = SnocList.snoc s.1 s.2 := hout
          obtain ⟨cs₀, hcs₀, hle⟩ := decode_prefix c p hc hp s.1 r.1 hFw.1 q.1 hQ.1
          refine ⟨Sum.inr (cs₀, q.2), ⟨hcs₀, rfl⟩, SnocList.snoc cs₀ q.2, rfl, ?_⟩
          show sizeFn c p cs₀ + bytes c p q.2 ≤ sizeFn c p s.1 + bytes c p s.2
          rw [← (hFw.2 : r.2 = s.2), bytes_U c p hQ.2]
          exact Int.add_le_add_right hle _

/-- **code-laws** (B&dM §9.4, p.240): a smallest code sequence decoding to the given string is
    the least fixed point of `(μX : Λ([nil,extend]°) thin(Q) P([nil,(X×𝟙)snoc]) est(R))` —
    decompose the string in every way, encode the front recursively, thin, and keep an
    `R`-smallest.  Theorem 9.2 at `Q≜𝟙+(prefix°×(⊤+⊤))`, with `code_mono` the monotonicity
    condition and `code_thin_condition` the thinning one.  `H = ⦇α⦈·⦇[nil,extend]⦈°` collapses to
    `decode°` by reflection (`AOP.A6_SnocList.cataR_con`). -/
public theorem code_laws (hc : 0 ≤ c) (hp : 0 ≤ p) :
    mu (fun X : dStr ⟶ dCodes =>
        Λ (Allegory.recip extendAlg) ≫ thinRel Q
          ≫ powerRel ((F Unit Code).map X ≫ graph (con (L := Unit) (E := Code))) ≫ est (R c p))
      ⊑ Λ (Allegory.recip decode) ≫ est (R c p) := by
  have hH : (relCata (F := F Unit Code) extendAlg)°
        ≫ relCata (F := F Unit Code) (I := initial Unit Code)
            (graph (con (L := Unit) (E := Code)))
      = Allegory.recip decode := by
    rw [← cataR_eq_relCata, ← cataR_eq_relCata, cataR_con]
    exact Cat.comp_id _
  have key := dynamic_programming_thin (F := F Unit Code) (F_preservesRecip Unit Code)
    (initial Unit Code) (h := graph (con (L := Unit) (E := Code))) (T := extendAlg)
    (R := R c p) (Q := Q) (graph_map con) (code_mono c p) (R_recip_trans c p)
    (by rw [hH]; exact code_thin_condition c p hc hp)
  rwa [hH] at key

-- printing-only unexpander: the note's `prefix` (a Lean keyword; the label emitter unescapes it).
open Lean PrettyPrinter in
@[app_unexpander prefixR] public meta def unexpandPrefixR : Unexpander
  | `($_:ident) => `($(mkIdent `prefix))
  | _ => throw ()

end Freyd.Alg.RelSet.Code
