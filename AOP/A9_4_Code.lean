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

  * `code_prog` — the note's fourth row, `reduce list((encode×𝟙)snoc)minlist(R)` refining that
    branch, with `reduce` listing `extend°`.

  NOT DONE, and why: the book's `lrt` (longest repeated tail) is an efficient `reduce`; `reduce`
  here enumerates the candidate splits and decides the pointer guard, which is the same relation
  and not the same cost — the boundary `AOP.A8_4_Knapsack`'s last row stops at.

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
public import AOP.A5_7_ListBeads
public import AOP.A9_3_Bracket

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

/-- **code-defn**: `extend`, the partial map above read as the arrow the note draws. -/
@[expose] public def extend : (⟨Str × Code⟩ : RelSet.{0}) ⟶ dStr := extendP

/-- **code-defn**: `[nil,extend]`, the algebra `decode` folds. -/
@[expose] public def extendAlg : (F Unit Code).obj dStr ⟶ dStr := fun u w =>
  match u with
  | Sum.inl _ => w = SnocList.wrap ()
  | Sum.inr q => extendP q w

/-- The algebra's `Str×Code` arm IS `extend`: `[nil,extend]` is the two written as one. -/
public theorem arm₂_extendAlg : arm₂ extendAlg = extend := rfl

/-- **code-defn**: the algebra IS the junction `[nil,extend]` the note writes.  A `match` on the
    coproduct draws as one box labelled with its own body; the junction draws as the note's two
    arms, which is why every §9.4 statement is written with this side. -/
public theorem extendAlg_eq_junc : extendAlg = junc (sumCop _ _) nilR extend := by
  apply hom_ext; intro u r
  constructor
  · intro h
    cases u with
    | inl d => exact Or.inl ⟨d, rfl, h⟩
    | inr q => exact Or.inr ⟨q, rfl, h⟩
  · intro h
    cases h with
    | inl h => obtain ⟨d, h1, h2⟩ := h; subst h1; exact h2
    | inr h => obtain ⟨q, h1, h2⟩ := h; subst h1; exact h2

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
        Λ ((junc (sumCop _ _) nilR extend
              : (F Unit Code).obj dStr ⟶ dStr)°) ≫ thinRel Q
          ≫ powerRel ((F Unit Code).map X ≫ junc (sumCop _ _) nilR snocR) ≫ est (R c p))
      ⊑ Λ (Allegory.recip decode) ≫ est (R c p) := by
  rw [← extendAlg_eq_junc, ← con_eq_junc]
  have hH : (relCata (F := F Unit Code) extendAlg)°
        ≫ relCata (F := F Unit Code) (I := initial Unit Code)
            (graph (con (L := Unit) (E := Code)))
      = Allegory.recip decode := by
    rw [← cataR_eq_relCata, ← cataR_eq_relCata, cataR_con]
    exact Cat.comp_id _
  have key := dynamic_programming_thin (F := F Unit Code) (F_preservesRecip Unit Code)
    (initial Unit Code) (h := graph (con (L := Unit) (E := Code))) (T := extendAlg)
    (R := R c p) (Q := Q) (graph_map con) (code_mono c p) (R_recip_trans c p)
    (by simp only [H]; rw [hH]; exact code_thin_condition c p hc hp)
  simp only [H] at key; rwa [hH] at key

/-- `extend` never returns the empty string: the symbol case snocs, and the pointer case appends
    a `zs` its own side condition keeps non-empty.  This is B&dM's Proposition 9.1 hypothesis
    `nil` and `extend` have disjoint ranges. -/
public theorem extend_ne_nil : ∀ (q : Str × Code) (w : Str), extendP q w → w ≠ SnocList.wrap ()
  | (xs, Code.sym a), w, h => by
      rw [(h : w = SnocList.snoc xs a)]; exact snoc_ne_wrap xs a
  | (xs, Code.ptr _ zs), w, h => by
      obtain ⟨hw, hz, _⟩ := h
      cases zs with
      | wrap _ => exact absurd rfl hz
      | snoc z b =>
        rw [hw]
        show SnocList.snoc (sappend xs z) b ≠ SnocList.wrap ()
        exact snoc_ne_wrap _ b

/-- **code-laws**, third row (Proposition 9.1): with `nil` and `extend` of disjoint ranges the
    branch `(extend°)%∋ thin(prefix°×(⊤+⊤))P((X×𝟙)snoc)est(R)` refines `code_laws`' body
    `([nil,extend]°)%∋ thin(Q)P([nil,(X×𝟙)snoc])est(R)` — `AOP.A9_1.thin_arm₂_le` at
    `[nil,extend]`, whose `Q₂` at `Q≜𝟙+(prefix°×(⊤+⊤))` is `prefix°×(⊤+⊤)`. -/
public theorem code_branch (X : dStr ⟶ dCodes) :
    Λ (extend°) ≫ thinRel (rprodMap (prefixR°) U)
        ≫ powerRel (rprodMap X (𝟙 (⟨Code⟩ : RelSet.{0})) ≫ snocR) ≫ est (R c p)
      ⊑ Λ ((junc (sumCop _ _) nilR extend
              : (F Unit Code).obj dStr ⟶ dStr)°) ≫ thinRel Q
          ≫ powerRel ((F Unit Code).map X ≫ junc (sumCop _ _) nilR snocR)
          ≫ est (R c p) := by
  rw [← extendAlg_eq_junc, ← con_eq_junc]
  -- `T` and `U` are named because `arm₂ ?T = extend` is a higher-order unification the elaborator
  -- will not solve; `arm₂_extendAlg` and `arm₂_con` say the two arms are these, definitionally.
  exact thin_arm₂_le (T := extendAlg) (X := X) (Q := Q) (R := R c p)
    (U := graph (con (L := Unit) (E := Code)))
    fun _d q w h1 h2 => extend_ne_nil q w h2 (h1 : w = SnocList.wrap ())

/-! ## `code-laws`, fourth row: the recursive program -/

/-- Every prefix of a snoc-string, longest first. -/
@[expose] public def prefixesFn : Str → CL.ConsList Unit Str
  | SnocList.wrap _ => CL.ConsList.cons (SnocList.wrap ()) (CL.ConsList.wrap ())
  | SnocList.snoc x a => CL.ConsList.cons (SnocList.snoc x a) (prefixesFn x)

public theorem mem_prefixes : ∀ (w u : Str), ListRel.inlistP (prefixesFn w) u ↔ prefixS u w
  | SnocList.wrap _, u => by
      show (u = SnocList.wrap () ∨ ListRel.inlistP (CL.ConsList.wrap ()) u)
        ↔ (u = SnocList.wrap ())
      exact ⟨fun h => h.elim id (fun hf => (hf : False).elim), fun h => Or.inl h⟩
  | SnocList.snoc x a, u => by
      show (u = SnocList.snoc x a ∨ ListRel.inlistP (prefixesFn x) u)
        ↔ (u = SnocList.snoc x a ∨ prefixS u x)
      exact or_congr Iff.rfl (mem_prefixes x u)

/-- `snoc a` on the RIGHT half of every split — what one more character at the end does to the
    splits of the string before it. -/
@[expose] public def snocSplits (a : Char) :
    CL.ConsList Unit (Str × Str) → CL.ConsList Unit (Str × Str)
  | CL.ConsList.wrap u => CL.ConsList.wrap u
  | CL.ConsList.cons s ss => CL.ConsList.cons (s.1, SnocList.snoc s.2 a) (snocSplits a ss)

/-- Every way of cutting a snoc-string into a prefix and a suffix. -/
@[expose] public def splitsFn : Str → CL.ConsList Unit (Str × Str)
  | SnocList.wrap _ =>
      CL.ConsList.cons (SnocList.wrap (), SnocList.wrap ()) (CL.ConsList.wrap ())
  | SnocList.snoc x a =>
      CL.ConsList.cons (SnocList.snoc x a, SnocList.wrap ()) (snocSplits a (splitsFn x))

public theorem mem_snocSplits (a : Char) (s : Str × Str) :
    ∀ ss : CL.ConsList Unit (Str × Str),
      ListRel.inlistP (snocSplits a ss) s
        ↔ ∃ t, s = (t.1, SnocList.snoc t.2 a) ∧ ListRel.inlistP ss t
  | CL.ConsList.wrap _ => ⟨fun (h : False) => h.elim, fun ⟨_, _, ht⟩ => (ht : False).elim⟩
  | CL.ConsList.cons t ts => by
      show (s = (t.1, SnocList.snoc t.2 a) ∨ ListRel.inlistP (snocSplits a ts) s) ↔ _
      rw [mem_snocSplits a s ts]
      constructor
      · rintro (h | ⟨r, hr, hm⟩)
        · exact ⟨t, h, Or.inl rfl⟩
        · exact ⟨r, hr, Or.inr hm⟩
      · rintro ⟨r, hr, (rfl | hm)⟩
        · exact Or.inl hr
        · exact Or.inr ⟨r, hr, hm⟩

/-- `splits` LISTS the cuts: `(xs,zs)` occurs in `splitsFn w` exactly when `xs⧺zs = w`. -/
public theorem mem_splits : ∀ (w : Str) (s : Str × Str),
    ListRel.inlistP (splitsFn w) s ↔ sappend s.1 s.2 = w
  | SnocList.wrap _, s => by
      show (s = (SnocList.wrap (), SnocList.wrap ()) ∨ ListRel.inlistP (CL.ConsList.wrap ()) s)
        ↔ sappend s.1 s.2 = SnocList.wrap ()
      constructor
      · rintro (rfl | (hf : False))
        · rfl
        · exact hf.elim
      · intro h
        left
        obtain ⟨x, z⟩ := s
        cases z with
        | wrap _ =>
            have hx : x = SnocList.wrap () := h
            rw [hx]
        | snoc z b => exact absurd h (snoc_ne_wrap (sappend x z) b)
  | SnocList.snoc x a, s => by
      show (s = (SnocList.snoc x a, SnocList.wrap ())
          ∨ ListRel.inlistP (snocSplits a (splitsFn x)) s)
        ↔ sappend s.1 s.2 = SnocList.snoc x a
      rw [mem_snocSplits a s (splitsFn x)]
      constructor
      · rintro (rfl | ⟨r, rfl, hm⟩)
        · rfl
        · show SnocList.snoc (sappend r.1 r.2) a = SnocList.snoc x a
          exact congrArg (fun t => SnocList.snoc t a) ((mem_splits x r).mp hm)
      · intro h
        obtain ⟨u, z⟩ := s
        cases z with
        | wrap _ =>
            left
            have hu : u = SnocList.snoc x a := h
            rw [hu]
        | snoc z b =>
            right
            have hb : SnocList.snoc (sappend u z) b = SnocList.snoc x a := h
            injection hb with h1 h2
            exact ⟨(u, z), by rw [h2], (mem_splits x (u, z)).mpr h1⟩

/-- A string is a prefix of itself extended on the right. -/
public theorem prefixS_sappend_self : ∀ (u t : Str), prefixS u (sappend u t)
  | u, SnocList.wrap _ => prefixS_refl u
  | u, SnocList.snoc t _ => Or.inr (prefixS_sappend_self u t)

/-- The `sym` candidate: the last character stands for itself. -/
@[expose] public def symCands : Str → CL.ConsList Unit (Str × Code)
  | SnocList.wrap u => CL.ConsList.wrap u
  | SnocList.snoc x a => CL.ConsList.cons (x, Code.sym a) (CL.ConsList.wrap ())

/-- The `ptr` candidates at ONE cut `(xs,zs)`: one for each earlier position `ys` the tail could
    point back to. -/
@[expose] public def ptrsAt (s : Str × Str) :
    CL.ConsList Unit Str → CL.ConsList Unit (Str × Code)
  | CL.ConsList.wrap u => CL.ConsList.wrap u
  | CL.ConsList.cons u us => CL.ConsList.cons (s.1, Code.ptr u s.2) (ptrsAt s us)

/-- The `ptr` candidates over every cut. -/
@[expose] public def ptrCands (us : CL.ConsList Unit Str) :
    CL.ConsList Unit (Str × Str) → CL.ConsList Unit (Str × Code)
  | CL.ConsList.wrap u => CL.ConsList.wrap u
  | CL.ConsList.cons s ss => ListRel.cappend (ptrsAt s us) (ptrCands us ss)

public theorem inlistP_cappend {B : Type} (z : B) :
    ∀ x y : CL.ConsList Unit B,
      ListRel.inlistP (ListRel.cappend x y) z
        ↔ ListRel.inlistP x z ∨ ListRel.inlistP y z
  | CL.ConsList.wrap _, _ =>
      ⟨fun h => Or.inr h, fun h => h.elim (fun (hf : False) => hf.elim) id⟩
  | CL.ConsList.cons b x, y => by
      show (z = b ∨ ListRel.inlistP (ListRel.cappend x y) z) ↔ _
      rw [inlistP_cappend z x y]
      constructor
      · rintro (h | (h | h))
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

public theorem mem_ptrsAt (s : Str × Str) (q : Str × Code) :
    ∀ us : CL.ConsList Unit Str,
      ListRel.inlistP (ptrsAt s us) q
        ↔ ∃ u, ListRel.inlistP us u ∧ q = (s.1, Code.ptr u s.2)
  | CL.ConsList.wrap _ => ⟨fun (h : False) => h.elim, fun ⟨_, hu, _⟩ => (hu : False).elim⟩
  | CL.ConsList.cons u us => by
      show (q = (s.1, Code.ptr u s.2) ∨ ListRel.inlistP (ptrsAt s us) q) ↔ _
      rw [mem_ptrsAt s q us]
      constructor
      · rintro (h | ⟨v, hv, hq⟩)
        · exact ⟨u, Or.inl rfl, h⟩
        · exact ⟨v, Or.inr hv, hq⟩
      · rintro ⟨v, (rfl | hv), hq⟩
        · exact Or.inl hq
        · exact Or.inr ⟨v, hv, hq⟩

public theorem mem_ptrCands (us : CL.ConsList Unit Str) (q : Str × Code) :
    ∀ ss : CL.ConsList Unit (Str × Str),
      ListRel.inlistP (ptrCands us ss) q
        ↔ ∃ s, ListRel.inlistP ss s ∧ ∃ u, ListRel.inlistP us u ∧ q = (s.1, Code.ptr u s.2)
  | CL.ConsList.wrap _ => ⟨fun (h : False) => h.elim, fun ⟨_, hs, _⟩ => (hs : False).elim⟩
  | CL.ConsList.cons s ss => by
      show ListRel.inlistP (ListRel.cappend (ptrsAt s us) (ptrCands us ss)) q ↔ _
      rw [inlistP_cappend q (ptrsAt s us) (ptrCands us ss), mem_ptrsAt s q us,
        mem_ptrCands us q ss]
      constructor
      · rintro (⟨u, hu, hq⟩ | ⟨t, ht, hrest⟩)
        · exact ⟨s, Or.inl rfl, u, hu, hq⟩
        · exact ⟨t, Or.inr ht, hrest⟩
      · rintro ⟨t, (rfl | ht), hrest⟩
        · exact Or.inl hrest
        · exact Or.inr ⟨t, ht, hrest⟩

/-- Snoc-strings have decidable equality: deciding a pointer's guard is comparing the two
    occurrences of its tail, so `reduce` needs it to be a program at all. -/
public def decEqStr : (x y : Str) → Decidable (x = y)
  | SnocList.wrap _, SnocList.wrap _ => isTrue rfl
  | SnocList.wrap _, SnocList.snoc _ _ => isFalse (by simp)
  | SnocList.snoc _ _, SnocList.wrap _ => isFalse (by simp)
  | SnocList.snoc x a, SnocList.snoc y b =>
      match decEqStr x y with
      | isFalse hx => isFalse fun h => by injection h with h1 _; exact hx h1
      | isTrue hx =>
          match (inferInstance : Decidable (a = b)) with
          | isFalse ha => isFalse fun h => by injection h with _ h2; exact ha h2
          | isTrue ha => isTrue (by rw [hx, ha])

public instance : DecidableEq Str := decEqStr

public def decPrefixS (x : Str) : (y : Str) → Decidable (prefixS x y)
  | SnocList.wrap _ => decEqStr x (SnocList.wrap ())
  | SnocList.snoc y a =>
      match decEqStr x (SnocList.snoc y a) with
      | isTrue h => isTrue (Or.inl h)
      | isFalse h1 =>
          match decPrefixS x y with
          | isTrue h => isTrue (Or.inr h)
          | isFalse h2 => isFalse fun h => h.elim h1 h2

public instance (x y : Str) : Decidable (prefixS x y) := decPrefixS x y

public instance (x y : Str) : Decidable (properPrefixS x y) :=
  inferInstanceAs (Decidable (prefixS x y ∧ slen x < slen y))

public instance : (q : Str × Code) → (w : Str) → Decidable (extendP q w)
  | (xs, Code.sym a), w => decEqStr w (SnocList.snoc xs a)
  | (xs, Code.ptr ys zs), w =>
      inferInstanceAs (Decidable (w = sappend xs zs ∧ zs ≠ SnocList.wrap ()
        ∧ properPrefixS (sappend ys zs) (sappend xs zs)))

/-- Keep the candidates `extend` really does decode to `w`. -/
@[expose] public def keepExtends (w : Str) :
    CL.ConsList Unit (Str × Code) → CL.ConsList Unit (Str × Code)
  | CL.ConsList.wrap u => CL.ConsList.wrap u
  | CL.ConsList.cons q qs =>
      if extendP q w then CL.ConsList.cons q (keepExtends w qs) else keepExtends w qs

public theorem mem_keepExtends (w : Str) (q : Str × Code) :
    ∀ qs : CL.ConsList Unit (Str × Code),
      ListRel.inlistP (keepExtends w qs) q ↔ ListRel.inlistP qs q ∧ extendP q w
  | CL.ConsList.wrap _ => ⟨fun (h : False) => h.elim, fun ⟨hf, _⟩ => (hf : False).elim⟩
  | CL.ConsList.cons r rs => by
      by_cases hr : extendP r w
      · have hE : keepExtends w (CL.ConsList.cons r rs)
            = CL.ConsList.cons r (keepExtends w rs) := if_pos hr
        rw [hE]
        show (q = r ∨ ListRel.inlistP (keepExtends w rs) q) ↔ _
        rw [mem_keepExtends w q rs]
        constructor
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨Or.inl rfl, hr⟩
          · exact ⟨Or.inr h1, h2⟩
        · rintro ⟨(rfl | h1), h2⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨h1, h2⟩
      · have hE : keepExtends w (CL.ConsList.cons r rs) = keepExtends w rs := if_neg hr
        rw [hE, mem_keepExtends w q rs]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨Or.inr h1, h2⟩
        · rintro ⟨(rfl | h1), h2⟩
          · exact absurd h2 hr
          · exact ⟨h1, h2⟩

/-- **code-laws**, fourth row: `reduce`, every way of splitting a legal last code off a string —
    the `sym` cut, and one `ptr` cut for each way of cutting the string and each earlier position
    its tail could point back to.  Both halves of a legal cut are prefixes of the string, so the
    candidates can be enumerated and the pointer's guard then decided. -/
@[expose] public def reduceFn (w : Str) : CL.ConsList Unit (Str × Code) :=
  keepExtends w (ListRel.cappend (symCands w) (ptrCands (prefixesFn w) (splitsFn w)))

/-- `reduce : String⟶[(String,Code)]`, the map the note's panel draws. -/
@[expose] public def reduce : dStr ⟶ ListRel.dList (Str × Code) := graph reduceFn

/-- `reduce` LISTS `extend°`: `(xs,e)` occurs in `reduceFn w` exactly when `extend (xs,e) = w`. -/
public theorem mem_reduce (w : Str) (q : Str × Code) :
    ListRel.inlistP (reduceFn w) q ↔ extendP q w := by
  show ListRel.inlistP
      (keepExtends w (ListRel.cappend (symCands w) (ptrCands (prefixesFn w) (splitsFn w)))) q
    ↔ extendP q w
  rw [mem_keepExtends, inlistP_cappend]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨xs, e⟩ := q
  cases e with
  | sym a =>
      have hw : w = SnocList.snoc xs a := h
      subst hw
      exact Or.inl (Or.inl rfl)
  | ptr ys zs =>
      obtain ⟨hw, _, hpp⟩ := h
      subst hw
      right
      rw [mem_ptrCands]
      exact ⟨(xs, zs), (mem_splits _ (xs, zs)).mpr rfl, ys,
        (mem_prefixes _ ys).mpr (prefixS_trans (prefixS_sappend_self ys zs) hpp.1), rfl⟩

/-- **code-laws**, fourth row (B&dM p.242): `reduce list((encode×𝟙)snoc)minlist(R)` refines the
    branch `(extend°)%∋ thin(prefix°×(⊤+⊤))P((encode×𝟙)snoc)est(R)` — `reduce` implements
    `extend°` (`mem_reduce`) and `minlist R` implements `est(R)`, the list standing in for the set
    it `setify`s to.  The one inequality is `CL.list_comp_minlist_le`, `setify`'s lax naturality: a
    list of `f`-images of the splits has, as a SET, a `P(f)`-image of the set of splits.  Thinning
    is free on the way in — `prefix°×(⊤+⊤)` is
    reflexive, so keeping every split is a legal thinning — and it is what an efficient `reduce`
    would exploit. -/
public theorem code_prog (encode : dStr ⟶ dCodes) :
    reduce ≫ ListRel.list (rprodMap encode (𝟙 dCode) ≫ snocR) ≫ minlist(R c p)
      ⊑ Λ (extend°) ≫ thinRel (rprodMap (prefixR°) U)
          ≫ powerRel (rprodMap encode (𝟙 dCode) ≫ snocR) ≫ est (R c p) := by
  have hmem : ∀ w : Str, (fun q => ListRel.inlistP (reduceFn w) q) = fun q => extendP q w :=
    fun w => funext fun q => propext (mem_reduce w q)
  have hred : reduce ≫ ListRel.setify = Λ (extend°) := by
    rw [Λ_eq_classifier]
    funext w S
    refine propext ⟨?_, ?_⟩
    · rintro ⟨_, rfl, hS⟩
      exact (hS : S = fun q => ListRel.inlistP (reduceFn w) q).trans (hmem w)
    · intro hS
      exact ⟨reduceFn w, rfl, (hS : S = fun q => extendP q w).trans (hmem w).symm⟩
  have hrefl : 𝟙 (⟨Str × Code⟩ : RelSet.{0}) ⊑ rprodMap (prefixR°) U :=
    le_iff.mpr fun s t hst => by
      obtain rfl := (hst : s = t)
      obtain ⟨x, e⟩ := s
      refine ⟨prefixS_refl x, ?_⟩
      cases e with
      | sym _ => exact trivial
      | ptr _ _ => exact trivial
  calc reduce ≫ ListRel.list (rprodMap encode (𝟙 dCode) ≫ snocR) ≫ minlist(R c p)
      ⊑ reduce ≫ ListRel.setify
          ≫ powerRel (rprodMap encode (𝟙 dCode) ≫ snocR) ≫ est (R c p) :=
        comp_mono_left reduce (CL.list_comp_minlist_le _ _)
    _ = Λ (extend°) ≫ powerRel (rprodMap encode (𝟙 dCode) ≫ snocR) ≫ est (R c p) := by
        rw [← Cat.assoc, hred]
    _ ⊑ Λ (extend°) ≫ thinRel (rprodMap (prefixR°) U)
          ≫ powerRel (rprodMap encode (𝟙 dCode) ≫ snocR) ≫ est (R c p) := by
        refine comp_mono_left _ ?_
        have h := comp_mono_right (id_le_thinRel hrefl)
          (powerRel (rprodMap encode (𝟙 dCode) ≫ snocR) ≫ est (R c p))
        rwa [Cat.id_comp] at h

-- `extend` keeps its namespace where `decode` does not, `Freyd.UF.Filter.extend` sharing the name;
-- a picture of §9.4's algebra has no second `extend` to tell this one from.
open Lean PrettyPrinter in
@[app_unexpander extend] public meta def unexpandExtend : Unexpander
  | _ => `($(mkIdent `extend))

-- `U≜⊤+⊤` is written by what it IS, the way `RinterH` is written `R∩H`: the note's box says the
-- relation, not the letter the definition bound it to.  Its own brackets, because it appears as a
-- factor of `prefix°×(⊤+⊤)` and `+` binds looser than `×`.
open Lean PrettyPrinter in
@[app_unexpander U] public meta def unexpandCodeU : Unexpander
  | _ => `($(mkIdent (Name.mkSimple "(⊤+⊤)")))

-- printing-only unexpander: the note's `prefix` (a Lean keyword; the label emitter unescapes it).
open Lean PrettyPrinter in
@[app_unexpander prefixR] public meta def unexpandPrefixR : Unexpander
  | `($_:ident) => `($(mkIdent `prefix))
  | _ => throw ()

end Freyd.Alg.RelSet.Code
