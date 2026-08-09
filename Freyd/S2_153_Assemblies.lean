/-
  Freyd & Scedrov, *Categories, Allegories* §2.153  Assemblies.

  "2.153. Let K be a collection of partial endofunctions on the set of natural numbers N.
   We make the following assumptions on K:
     (i)   K contains the identity,
     (ii)  K is closed under composition,
     (iii) K contains two total functions ℓ and ϰ such that for any φ, ψ in K there exists θ
           in K defined on the common domain of φ and ψ, such that φ contains θℓ and ψ
           contains θϰ.
   [If (−,−) : N×N → N is a coding of pairs and (n,k)ℓ = n, (n,k)ϰ = k for all numbers n, k,
    then in the condition (iii) one may let θ = (φ,ψ).  For example, K may be the collection
    of all partial recursive functions.]

   We consider the category A of ASSEMBLIES A = (X, {Yₙ}), where X is a set and {Yₙ} a
   sequence of subsets Yₙ ⊆ X called CAUCUSES and written A|ₙ.  Caucuses are not necessarily
   pairwise disjoint.  The CARRIER of an assembly A is the set |A| = ⋃ₙ A|ₙ.  A morphism
   f : A → B is an ordinary function f : |A| → |B| for which there exists φ in K (a MODULUS
   of f) so that for every n ∈ N, x ∈ |A|: if x ∈ A|ₙ, then φ(n) is defined and f(x) ∈ B|φ(n).

   THE CATEGORY OF ASSEMBLIES IS A POSITIVE PRE-LOGOS.

   BECAUSE: the empty set is a coterminator.  The equalizer of f, g : A → B is the ordinary
   Set equalizer |E| = {x : f(x) = g(x)} with E|ₙ = |E| ∩ A|ₙ.  A terminator is a one-element
   set 1 with 1|ₙ = 1.  For binary products, (A×B)|ₙ = A|ₙℓ × B|ₙϰ.  Given f : A → B the
   image B′ has |B′| = the ordinary image of f and B′|ₙ = f(A|ₙ); B′ is a subobject of B
   named by inclusion using the same modulus as f (hence any subobject may be named by an
   inclusion-monic with some modulus); the factor A → B′ is f with identity modulus.
   Minimality and stability under pullbacks are left to the reader, as is the construction
   of disjoint unions.  [...]  Note the functor ∇ : S → A given by |∇X| = (∇X)|ₙ = X; ∇
   preserves coterminator, equalizers, and finite products, but not unions."

  ## Design decisions

  * CARRIER.  The book's morphisms are functions on |A| = ⋃ₙ A|ₙ, not on X.  We therefore
    require every element of `X` to lie in some caucus (`carrier_mem`), i.e. we take X to BE
    the carrier.  No generality is lost (replace X by |A|), and it spares us a subtype
    carrier in every construction.

  * PARTIAL FUNCTIONS.  `ModFun` encodes a partial endofunction of N relationally: a graph
    `Nat → Nat → Prop` plus functionality.  Composition (`ModFun.comp`) is in DIAGRAM ORDER,
    matching the book's `θℓ` = "first θ, then ℓ".  "φ contains θ" is graph inclusion.

  * THE PAIRING IS EXPLICIT DATA.  Conditions (i)(ii)(iii) alone are provably NOT enough for
    the BECAUSE-paragraph.  Counterexample: K₀ := all restrictions of the identity satisfies
    (i)(ii)(iii) with ℓ = ϰ = id — but over K₀ the book's image formula fails minimality:
    take S = ({s₁,s₂}, S|₁={s₁}, S|₂={s₂}), B = ({y}, B|₁=B|₂={y}) and m : S → B constant.
    m is monic (any two parallel maps into S agree: a K₀-modulus forces u(w) ∈ S|ₙ for every
    caucus of w, and each S|ₙ is a singleton), yet m is not injective, and the book's image
    of m (= all of B) is NOT ≤ the subobject (S,m): a factoring B → S would need a modulus φ
    with h(y) ∈ S|₁ ∩ S|₂ = ∅.  Freyd's bracketed remark shows the INTENDED ℓ, ϰ arise from
    a coding of pairs — which makes (n,k) ↦ code n k jointly surjective onto pairs and
    restores monic ⟺ injective (see `monic_iff_injective`), unblocking image minimality.
    We therefore take the coding `code` with projections `proj₁` (= ℓ), `proj₂` (= ϰ) as
    explicit fields, with θ := the coded pair (φ,ψ); book (iii) is then a theorem
    (`ModulusSystem.book_iii`).

  * TAGS FOR UNIONS/COPRODUCTS.  The book leaves "the construction of disjoint unions to the
    reader".  Any construction of subobject unions and coproducts needs K to dispatch on a
    tag (which side of the union an index comes from); (i)(ii)(iii) provide no such closure
    (they are product-shaped, not coproduct-shaped — K₀ again witnesses the failure).  We
    add explicit total injections `inL`, `inR` with disjoint ranges and a closure axiom
    `cases_mem` for definition-by-cases WITH PARAMETER: from φ, ψ ∈ K the function
    `code x (inL y) ↦ φ(code x y)`, `code x (inR y) ↦ ψ(code x y)` is in K.  The parameter
    slot `x` is what lets tagged caucus indices flow through pullbacks (inverse images).
    All caucus families built by tagging use the shape `code parameter (inL k)` so that this
    single closure axiom suffices.  The collection of ALL partial functions — and all
    partial recursive functions — satisfies every field (`ModulusSystem.allPartial`).

  ## Fields to provide (repo classes, all in namespace `Freyd`)

  * `Cat (Assembly K)` (S1_1): Hom, id, comp, id_comp, comp_id, assoc.                  [M1]
  * `HasTerminal` (S1_42): one, trm, uniq.  `HasCoterminator` (S1_58): zero, init,
    init_uniq.                                                                          [M2]
  * `HasBinaryProducts` (S1_42): prod, fst, snd, pair, fst_pair, snd_pair, pair_uniq.
    `HasEqualizers` (S1_43): cone/lift/fac/uniq per pair.  (⇒ `CartesianCategory`.)     [M3]
  * `HasPullbacks` (S1_45): via `products_equalizers_implies_pullbacks` (S1_43).        [M4]
  * `HasImages` (S1_51): image + isImage (Allows + minimality).
    `PullbacksTransferCovers` (S1_52): arbitrary pullback cone, cover opposite ⇒ cover.
    (⇒ `RegularCategory`.)                                                              [M5]
  * `HasSubobjectUnions` (S1_60): union, union_left, union_right, union_min.
    `PreLogos` (S1_60): bottom, bottom_min, bottom_dom_iso, invImage_preserves_union,
    invImage_preserves_bottom.                                                          [M6]
  * `HasBinaryCoproducts` (S1_58): coprod, inl, inr, case, case_inl, case_inr, case_uniq.
    (⇒ `PositivePreLogos`.)  `DisjointBinaryCoproduct` (S1_62): inl_monic, inr_monic,
    inl_inter_inr, inl_union_inr.                                                       [M7]
  * `∇ : Type u → Assembly K` functor + preservation lemmas.                            [M8]
-/

module

public import Freyd.S1_62

universe u u₁ v₁

namespace Freyd

/-! ## Partial endofunctions of N -/

/-- A PARTIAL ENDOFUNCTION of N, encoded relationally: a functional graph.
    `graph n m` means "defined at `n` with value `m`".  The relational encoding keeps
    composition and definition-by-cases proof-term-free (no `Classical.choice` to build
    values from domain proofs). -/
public structure ModFun where
  graph : Nat → Nat → Prop
  functional : ∀ {n m₁ m₂}, graph n m₁ → graph n m₂ → m₁ = m₂

namespace ModFun

/-- The identity endofunction (book (i)). -/
@[expose] public def ident : ModFun := ⟨fun n m => m = n, fun h₁ h₂ => h₁.trans h₂.symm⟩

/-- A total function as a `ModFun` (e.g. the book's total ℓ and ϰ). -/
@[expose] public def ofFun (f : Nat → Nat) : ModFun := ⟨fun n m => m = f n, fun h₁ h₂ => h₁.trans h₂.symm⟩

/-- Composition in DIAGRAM ORDER: `(φ.comp ψ)(n) = ψ(φ(n))` — first φ, then ψ.
    Matches the book's juxtaposition `θℓ` = "θ then ℓ". -/
@[expose] public def comp (φ ψ : ModFun) : ModFun where
  graph n m := ∃ j, φ.graph n j ∧ ψ.graph j m
  functional := fun ⟨j₁, hφ₁, hψ₁⟩ ⟨j₂, hφ₂, hψ₂⟩ => by
    cases φ.functional hφ₁ hφ₂; exact ψ.functional hψ₁ hψ₂

/-- The coded pair `θ = (φ,ψ)` from the book's bracketed remark: `n ↦ code (φ n) (ψ n)`,
    defined exactly on the common domain of φ and ψ. -/
@[expose] public def pairC (code : Nat → Nat → Nat) (φ ψ : ModFun) : ModFun where
  graph n m := ∃ a b, φ.graph n a ∧ ψ.graph n b ∧ m = code a b
  functional := fun ⟨a₁, b₁, ha₁, hb₁, he₁⟩ ⟨a₂, b₂, ha₂, hb₂, he₂⟩ => by
    cases φ.functional ha₁ ha₂; cases ψ.functional hb₁ hb₂; exact he₁.trans he₂.symm

/-- Definition by cases WITH PARAMETER on a tagged code:
    `code x (inL y) ↦ φ(code x y)` and `code x (inR y) ↦ ψ(code x y)`.
    Stated via the projections so that functionality needs only injectivity/disjointness of
    the tags (not of `code`).  This is the K-closure that the book's "disjoint unions left
    to the reader" implicitly requires; the parameter slot `x` is what lets tagged indices
    survive inside pair-coded pullback indices. -/
@[expose] public def casesC (proj₁ proj₂ : Nat → Nat) (code : Nat → Nat → Nat) (inL inR : Nat → Nat)
    (hL : ∀ {a b : Nat}, inL a = inL b → a = b) (hR : ∀ {a b : Nat}, inR a = inR b → a = b)
    (hLR : ∀ a b, inL a ≠ inR b) (φ ψ : ModFun) : ModFun where
  graph n m :=
    (∃ y, proj₂ n = inL y ∧ φ.graph (code (proj₁ n) y) m) ∨
    (∃ y, proj₂ n = inR y ∧ ψ.graph (code (proj₁ n) y) m)
  functional := by
    rintro n m₁ m₂ (⟨y₁, hy₁, h₁⟩ | ⟨y₁, hy₁, h₁⟩) (⟨y₂, hy₂, h₂⟩ | ⟨y₂, hy₂, h₂⟩)
    · cases hL (hy₁.symm.trans hy₂); exact φ.functional h₁ h₂
    · exact absurd (hy₁.symm.trans hy₂) (hLR y₁ y₂)
    · exact absurd (hy₂.symm.trans hy₁) (hLR y₂ y₁)
    · cases hR (hy₁.symm.trans hy₂); exact ψ.functional h₁ h₂

/-! Graph-introduction helpers: every modulus built later is a `comp`/`pairC`/`casesC`
    combinator term over `ident`/`ofFun`, and its graph values are computed by chaining
    these four intro rules, then normalizing indices with `code_proj₁/₂`. -/

public theorem ident_graph (n : Nat) : ident.graph n n := rfl

public theorem ofFun_graph (f : Nat → Nat) (n : Nat) : (ofFun f).graph n (f n) := rfl

@[simp] public theorem ofFun_graph_iff {f : Nat → Nat} {n m : Nat} :
    (ofFun f).graph n m ↔ m = f n := Iff.rfl

public theorem comp_graph {φ ψ : ModFun} {n j m : Nat} (h₁ : φ.graph n j) (h₂ : ψ.graph j m) :
    (φ.comp ψ).graph n m := ⟨j, h₁, h₂⟩

public theorem pairC_graph {code : Nat → Nat → Nat} {φ ψ : ModFun} {n a b : Nat}
    (h₁ : φ.graph n a) (h₂ : ψ.graph n b) : (pairC code φ ψ).graph n (code a b) :=
  ⟨a, b, h₁, h₂, rfl⟩

end ModFun

/-! ## Modulus systems -/

/-- A MODULUS SYSTEM: the book's collection K of partial endofunctions on N with
    (i) the identity, (ii) composition closure, and the pairing structure of (iii) —
    following the bracketed remark, the coding of pairs `code` with total projections
    `proj₁` (ℓ) and `proj₂` (ϰ) is explicit data and θ := the coded pair (φ,ψ)
    (book (iii) becomes the theorem `book_iii` below).  The tag fields `inL`, `inR`,
    `cases_mem` are the closure that the book's "construction of disjoint unions"
    (left to the reader) needs; see the module docstring for why (i)(ii)(iii) alone
    provably do not suffice. -/
public structure ModulusSystem where
  /-- Membership: which partial endofunctions belong to K. -/
  mem : ModFun → Prop
  /-- (i) K contains the identity. -/
  id_mem : mem ModFun.ident
  /-- (ii) K is closed under composition (diagram order). -/
  comp_mem : ∀ {φ ψ}, mem φ → mem ψ → mem (φ.comp ψ)
  /-- The coding of pairs (−,−) : N×N → N from the book's bracketed remark. -/
  code : Nat → Nat → Nat
  /-- ℓ: the first projection, total, in K. -/
  proj₁ : Nat → Nat
  /-- ϰ: the second projection, total, in K. -/
  proj₂ : Nat → Nat
  proj₁_mem : mem (ModFun.ofFun proj₁)
  proj₂_mem : mem (ModFun.ofFun proj₂)
  /-- (n,k)ℓ = n. -/
  code_proj₁ : ∀ a b, proj₁ (code a b) = a
  /-- (n,k)ϰ = k. -/
  code_proj₂ : ∀ a b, proj₂ (code a b) = b
  /-- θ = (φ,ψ) ∈ K — the book's construction discharging (iii). -/
  pair_mem : ∀ {φ ψ}, mem φ → mem ψ → mem (ModFun.pairC code φ ψ)
  /-- Left tag: a total injection in K (e.g. `2·`). -/
  inL : Nat → Nat
  /-- Right tag: a total injection in K, range disjoint from `inL` (e.g. `2·+1`). -/
  inR : Nat → Nat
  inL_mem : mem (ModFun.ofFun inL)
  inR_mem : mem (ModFun.ofFun inR)
  inL_inj : ∀ {a b : Nat}, inL a = inL b → a = b
  inR_inj : ∀ {a b : Nat}, inR a = inR b → a = b
  inLR_ne : ∀ a b, inL a ≠ inR b
  /-- Definition-by-cases with parameter on the tag, in K (see `ModFun.casesC`). -/
  cases_mem : ∀ {φ ψ}, mem φ → mem ψ →
    mem (ModFun.casesC proj₁ proj₂ code inL inR inL_inj inR_inj inLR_ne φ ψ)

namespace ModulusSystem

variable (K : ModulusSystem)

/-- The coded pair θ = (φ,ψ) over K's coding. -/
@[expose] public abbrev pairF (φ ψ : ModFun) : ModFun := ModFun.pairC K.code φ ψ

/-- Definition-by-cases with parameter over K's tags. -/
@[expose] public abbrev casesF (φ ψ : ModFun) : ModFun :=
  ModFun.casesC K.proj₁ K.proj₂ K.code K.inL K.inR K.inL_inj K.inR_inj K.inLR_ne φ ψ

/-- ℓ as a `ModFun`. -/
@[expose] public abbrev projF₁ : ModFun := ModFun.ofFun K.proj₁
/-- ϰ as a `ModFun`. -/
@[expose] public abbrev projF₂ : ModFun := ModFun.ofFun K.proj₂

/-- The coding is jointly surjective onto pairs — Freyd's "(n,k)ℓ = n, (n,k)ϰ = k for ALL
    n, k".  This is the pairing strength that bare (iii) lacks (module docstring). -/
theorem proj_surj_pair (a b : Nat) : ∃ n, K.proj₁ n = a ∧ K.proj₂ n = b :=
  ⟨K.code a b, K.code_proj₁ a b, K.code_proj₂ a b⟩

/-- Intro rule for `casesF` on a left-tagged code. -/
theorem casesF_graph_inl {φ ψ : ModFun} {x y m : Nat} (h : φ.graph (K.code x y) m) :
    (K.casesF φ ψ).graph (K.code x (K.inL y)) m :=
  Or.inl ⟨y, K.code_proj₂ x (K.inL y), by rw [K.code_proj₁]; exact h⟩

/-- Intro rule for `casesF` on a right-tagged code. -/
theorem casesF_graph_inr {φ ψ : ModFun} {x y m : Nat} (h : ψ.graph (K.code x y) m) :
    (K.casesF φ ψ).graph (K.code x (K.inR y)) m :=
  Or.inr ⟨y, K.code_proj₂ x (K.inR y), by rw [K.code_proj₁]; exact h⟩

/-- **Book (iii)** is a theorem of a modulus system: for φ, ψ ∈ K there is θ ∈ K defined
    exactly on the common domain of φ and ψ with φ ⊇ θℓ and ψ ⊇ θϰ (graph containment;
    composition in diagram order). -/
theorem book_iii {φ ψ : ModFun} (hφ : K.mem φ) (hψ : K.mem ψ) :
    ∃ θ, K.mem θ ∧
      (∀ n, (∃ m, θ.graph n m) ↔ (∃ m, φ.graph n m) ∧ (∃ m, ψ.graph n m)) ∧
      (∀ n m, (θ.comp K.projF₁).graph n m → φ.graph n m) ∧
      (∀ n m, (θ.comp K.projF₂).graph n m → ψ.graph n m) := by
  refine ⟨K.pairF φ ψ, K.pair_mem hφ hψ, fun n => ?_, fun n m h => ?_, fun n m h => ?_⟩
  · constructor
    · rintro ⟨m, a, b, ha, hb, rfl⟩; exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; exact ⟨K.code a b, a, b, ha, hb, rfl⟩
  · obtain ⟨j, ⟨a, b, ha, hb, rfl⟩, hm⟩ := h
    rw [show m = a from hm.trans (K.code_proj₁ a b)]; exact ha
  · obtain ⟨j, ⟨a, b, ha, hb, rfl⟩, hm⟩ := h
    rw [show m = b from hm.trans (K.code_proj₂ a b)]; exact hb

end ModulusSystem

/-! ## Assemblies and their category -/

/-- An ASSEMBLY over the modulus system K: a set `X` with a sequence of CAUCUSES
    `caucus n ⊆ X`.  Following the book, morphisms are functions on the carrier
    ⋃ₙ caucus n; we require `X` to BE the carrier (`carrier_mem`) — no generality is
    lost and every construction is spared a subtype carrier (module docstring). -/
public structure Assembly (K : ModulusSystem) : Type (u + 1) where
  X : Type u
  caucus : Nat → X → Prop
  carrier_mem : ∀ x, ∃ n, caucus n x

variable {K : ModulusSystem}

/-- `φ` is a MODULUS (tracker) for the function `f` between the underlying sets of two
    assemblies: if `x ∈ A|ₙ` then `φ(n)` is defined and `f(x) ∈ B|φ(n)`. -/
@[expose] public def Tracks (φ : ModFun) (A B : Assembly.{u} K) (f : A.X → B.X) : Prop :=
  ∀ n x, A.caucus n x → ∃ m, φ.graph n m ∧ B.caucus m (f x)

/-- A morphism of assemblies: an ordinary function admitting a modulus in K.
    The modulus is PROPERTY, not structure — two morphisms are equal iff their
    underlying functions are (`AsmHom.ext`). -/
public structure AsmHom (A B : Assembly.{u} K) : Type u where
  toFun : A.X → B.X
  tracked : ∃ φ, K.mem φ ∧ Tracks φ A B toFun

@[ext] public theorem AsmHom.ext {A B : Assembly.{u} K} {f g : AsmHom A B}
    (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

/-- The category **A** of assemblies (§2.153): identity has the identity modulus (i),
    composition composes moduli (ii). -/
@[expose] public instance asmCat : Cat.{u, u + 1} (Assembly.{u} K) where
  Hom := AsmHom
  id A := ⟨fun x => x, ModFun.ident, K.id_mem, fun n _ hx => ⟨n, rfl, hx⟩⟩
  comp {A B C} f g :=
    ⟨fun x => g.toFun (f.toFun x), by
      obtain ⟨φ, hφ, hf⟩ := f.tracked
      obtain ⟨ψ, hψ, hg⟩ := g.tracked
      refine ⟨φ.comp ψ, K.comp_mem hφ hψ, fun n x hx => ?_⟩
      obtain ⟨m, hm, hBx⟩ := hf n x hx
      obtain ⟨p, hp, hCx⟩ := hg m _ hBx
      exact ⟨p, ⟨m, hm, hp⟩, hCx⟩⟩
  id_comp _ := AsmHom.ext rfl
  comp_id _ := AsmHom.ext rfl
  assoc _ _ _ := AsmHom.ext rfl

@[simp] theorem asmComp_toFun {A B C : Assembly.{u} K} (f : A ⟶ B) (g : B ⟶ C) (x : A.X) :
    (f ≫ g).toFun x = g.toFun (f.toFun x) := rfl

@[simp] theorem asmId_toFun (A : Assembly.{u} K) (x : A.X) :
    (Cat.id A).toFun x = x := rfl

/-! ## Non-vacuity: the collection of ALL partial endofunctions is a modulus system

  Concrete coding: `code a b = 2^a·(2b+1)` with 2-adic valuation `val2` as ℓ and
  odd-part decoding as ϰ; tags `inL = 2·`, `inR = 2·+1`. -/

/-- 2-adic valuation: the exponent of 2 in `n` (0 at 0). -/
@[expose] public def val2 (n : Nat) : Nat :=
  if h : n % 2 = 0 ∧ n ≠ 0 then val2 (n / 2) + 1 else 0
  termination_by n
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h.2) (by omega)

public theorem val2_odd {n : Nat} (h : n % 2 = 1) : val2 n = 0 := by
  rw [val2]; simp [show ¬(n % 2 = 0 ∧ n ≠ 0) by omega]

public theorem val2_two_mul {n : Nat} (h : n ≠ 0) : val2 (2 * n) = val2 n + 1 := by
  rw [val2]
  simp [show 2 * n % 2 = 0 by omega, show ¬(2 * n = 0) by omega, show 2 * n / 2 = n by omega]

public theorem two_pow_pos (a : Nat) : 0 < 2 ^ a := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.pow_succ]; omega

public theorem val2_code (a b : Nat) : val2 (2 ^ a * (2 * b + 1)) = a := by
  induction a with
  | zero => rw [Nat.pow_zero, Nat.one_mul]; exact val2_odd (by omega)
  | succ a ih =>
      have h2 : 2 ^ (a + 1) * (2 * b + 1) = 2 * (2 ^ a * (2 * b + 1)) := by
        rw [Nat.pow_succ]; rw [Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]
      have hpos : 0 < 2 ^ a * (2 * b + 1) := Nat.mul_pos (two_pow_pos a) (by omega)
      rw [h2, val2_two_mul (Nat.pos_iff_ne_zero.mp hpos), ih]

/-- The collection of ALL partial endofunctions of N is a modulus system — the
    non-vacuity witness required by the book's "for example, K may be the collection of
    all partial recursive functions" (any closure conditions hold a fortiori). -/
@[expose] public def ModulusSystem.allPartial : ModulusSystem where
  mem _ := True
  id_mem := trivial
  comp_mem _ _ := trivial
  code a b := 2 ^ a * (2 * b + 1)
  proj₁ := val2
  proj₂ n := (n / 2 ^ val2 n - 1) / 2
  proj₁_mem := trivial
  proj₂_mem := trivial
  code_proj₁ := val2_code
  code_proj₂ a b := by
    rw [val2_code, show 2 ^ a * (2 * b + 1) / 2 ^ a = 2 * b + 1 from
      Nat.mul_div_cancel_left _ (two_pow_pos a)]
    omega
  pair_mem _ _ := trivial
  inL k := 2 * k
  inR k := 2 * k + 1
  inL_mem := trivial
  inR_mem := trivial
  inL_inj h := by omega
  inR_inj h := by omega
  inLR_ne a b := by omega
  cases_mem _ _ := trivial

/-! ## M2: terminator and coterminator

  Book: "A terminator is given by a one-element set 1 so that 1|ₙ = 1." and
  "The empty set is a coterminator." -/

/-- The one-element assembly `1` with `1|ₙ = 1` for all n. -/
@[expose] public def oneAsm : Assembly.{u} K := ⟨PUnit, fun _ _ => True, fun _ => ⟨0, trivial⟩⟩

/-- §2.153: `1|ₙ = 1` is a terminator; the unique map has the identity modulus. -/
@[expose] public instance asmHasTerminal : HasTerminal (Assembly.{u} K) where
  one := oneAsm
  trm _ := ⟨fun _ => PUnit.unit, ModFun.ident, K.id_mem, fun n _ _ => ⟨n, rfl, trivial⟩⟩
  uniq _ _ := AsmHom.ext (funext fun _ => rfl)

/-- The empty assembly (no elements, all caucuses empty). -/
@[expose] public def zeroAsm : Assembly.{u} K := ⟨PEmpty, fun _ _ => False, fun x => x.elim⟩

/-- §2.153: "The empty set is a coterminator."  All modulus obligations are vacuous. -/
@[expose] public instance asmHasCoterminator : HasCoterminator (Assembly.{u} K) where
  zero := zeroAsm
  init _ := ⟨fun x => x.elim, ModFun.ident, K.id_mem, fun _ _ h => h.elim⟩
  init_uniq _ _ := AsmHom.ext (funext fun x => x.elim)

/-! ## M3: binary products and equalizers

  Book: "For binary products, let (A×B)|ₙ = A|ₙℓ × B|ₙϰ."  The projections are tracked by
  ℓ and ϰ; the pairing ⟨f,g⟩ is tracked by the book's θ = (φ,ψ) — this construction is
  exactly what condition (iii) exists for.

  "Given a pair of morphisms f, g : A → B, their equalizer is obtained as
  |E| = {x : f(x) = g(x)} (the ordinary equalizer in the category of sets), and E|ₙ is the
  ordinary intersection of |E| and A|ₙ." -/

/-- Binary product of assemblies: `(A×B)|ₙ = A|ₙℓ × B|ₙϰ`. -/
@[expose] public def prodAsm (A B : Assembly.{u} K) : Assembly.{u} K where
  X := A.X × B.X
  caucus n p := A.caucus (K.proj₁ n) p.1 ∧ B.caucus (K.proj₂ n) p.2
  carrier_mem p := by
    obtain ⟨j, hj⟩ := A.carrier_mem p.1
    obtain ⟨k, hk⟩ := B.carrier_mem p.2
    exact ⟨K.code j k, by rw [K.code_proj₁]; exact hj, by rw [K.code_proj₂]; exact hk⟩

/-- §2.153 binary products: `fst`/`snd` tracked by ℓ/ϰ, `pair` tracked by θ = (φ,ψ). -/
@[expose] public instance asmHasBinaryProducts : HasBinaryProducts (Assembly.{u} K) where
  prod := prodAsm
  fst := ⟨Prod.fst, K.projF₁, K.proj₁_mem, fun n _ hp => ⟨K.proj₁ n, rfl, hp.1⟩⟩
  snd := ⟨Prod.snd, K.projF₂, K.proj₂_mem, fun n _ hp => ⟨K.proj₂ n, rfl, hp.2⟩⟩
  pair f g :=
    ⟨fun x => (f.toFun x, g.toFun x), by
      obtain ⟨φ, hφ, hf⟩ := f.tracked
      obtain ⟨ψ, hψ, hg⟩ := g.tracked
      refine ⟨K.pairF φ ψ, K.pair_mem hφ hψ, fun n x hx => ?_⟩
      obtain ⟨a, ha, hAx⟩ := hf n x hx
      obtain ⟨b, hb, hBx⟩ := hg n x hx
      exact ⟨K.code a b, ⟨a, b, ha, hb, rfl⟩,
        by rw [K.code_proj₁]; exact hAx, by rw [K.code_proj₂]; exact hBx⟩⟩
  fst_pair _ _ := AsmHom.ext rfl
  snd_pair _ _ := AsmHom.ext rfl
  pair_uniq _ _ h h₁ h₂ := AsmHom.ext (funext fun x =>
    Prod.ext (congrArg (fun k => AsmHom.toFun k x) h₁) (congrArg (fun k => AsmHom.toFun k x) h₂))

/-- Equalizer assembly: the Set equalizer with the induced caucuses `E|ₙ = |E| ∩ A|ₙ`. -/
@[expose] public def eqAsm {A B : Assembly.{u} K} (f g : A ⟶ B) : Assembly.{u} K where
  X := {x : A.X // f.toFun x = g.toFun x}
  caucus n x := A.caucus n x.val
  carrier_mem x := A.carrier_mem x.val

/-- §2.153 equalizers: the inclusion and the induced factorization both have the identity
    modulus (a map into the equalizer is tracked by any modulus of its composite with the
    inclusion, since the caucuses are induced). -/
@[expose] public instance asmHasEqualizers : HasEqualizers (Assembly.{u} K) where
  eq _ _ f g :=
    { cone :=
        { dom := eqAsm f g
          map := ⟨Subtype.val, ModFun.ident, K.id_mem, fun n x hx => ⟨n, rfl, hx⟩⟩
          eq := AsmHom.ext (funext fun x => x.property) }
      lift c :=
        ⟨fun y => ⟨c.map.toFun y, congrArg (fun k => AsmHom.toFun k y) c.eq⟩, by
          obtain ⟨φ, hφ, hc⟩ := c.map.tracked
          exact ⟨φ, hφ, fun n y hy => hc n y hy⟩⟩
      fac _ := AsmHom.ext rfl
      uniq c m hm := AsmHom.ext (funext fun y =>
        Subtype.ext (congrArg (fun k => AsmHom.toFun k y) hm)) }

/-- The category of assemblies is Cartesian (terminator + products + equalizers). -/
@[expose] public instance asmCartesian : CartesianCategory (Assembly.{u} K) where
  toHasTerminal := inferInstance
  toHasBinaryProducts := inferInstance
  toHasEqualizers := inferInstance

/-! ## M4: pullbacks

  Derived from products and equalizers by the repo's §1.432 construction (DRY): the
  pullback of `f : A → C ← B : g` is the sub-assembly of `A × B` where the two composites
  agree, with the product's ℓ/ϰ-coded caucuses restricted. -/

/-- §2.153 pullbacks, via §1.432 (products + equalizers ⇒ pullbacks). -/
@[expose] public instance asmHasPullbacks : HasPullbacks (Assembly.{u} K) where
  has f g := products_equalizers_implies_pullbacks f g

/-! ## M5: monics, images, covers — the regular structure

  Book: "Given a morphism f : A → B, we wish to obtain the minimal subobject B′ of B such
  that f factors through B′.  Let |B′| be the ordinary image of the map f and let
  B′|ₙ = f(A|ₙ).  B′ is a subobject of B named by inclusion using the same modulus as f.
  (Note that we will have therefore shown that any subobject may be named by a monic given
  by inclusion with some modulus.)  The required factor A → B′ is obtained as f with the
  identity as its modulus.  The minimality and the stability under pullbacks is left to
  the reader."

  The "left to the reader" minimality rests on monic ⟺ injective, which is where the
  pairing surjectivity earns its keep: a one-point probe assembly caucused exactly at
  `code a b` maps to either of two f-identified points via ℓ and ϰ. -/

/-- A morphism whose underlying function is injective is monic (the underlying-set functor
    is faithful). -/
public theorem asmMonic_of_injective {A B : Assembly.{u} K} (m : A ⟶ B)
    (hinj : Function.Injective m.toFun) : Monic m := fun _ _ huv =>
  AsmHom.ext (funext fun x => hinj (congrArg (fun k => AsmHom.toFun k x) huv))

/-- A monic of assemblies is injective on the underlying sets.  Probe: for `m s₁ = m s₂`
    with `s₁ ∈ A|ₐ`, `s₂ ∈ A|ᵦ`, the one-point assembly caucused exactly at `code a b`
    maps to `s₁` with modulus ℓ and to `s₂` with modulus ϰ; monicness forces the two maps
    (hence `s₁`, `s₂`) to coincide.  This is FALSE for a modulus system with bare
    (i)(ii)(iii) — see the module docstring — and is exactly what the book's coding of
    pairs provides. -/
public theorem asmInjective_of_monic {A B : Assembly.{u} K} (m : A ⟶ B) (hm : Monic m) :
    Function.Injective m.toFun := by
  intro s₁ s₂ hs
  obtain ⟨a, ha⟩ := A.carrier_mem s₁
  obtain ⟨b, hb⟩ := A.carrier_mem s₂
  let W : Assembly.{u} K := ⟨PUnit, fun n _ => n = K.code a b, fun _ => ⟨K.code a b, rfl⟩⟩
  let u : W ⟶ A := ⟨fun _ => s₁, K.projF₁, K.proj₁_mem,
    fun n _ hn => ⟨K.proj₁ n, rfl, by rw [hn, K.code_proj₁]; exact ha⟩⟩
  let v : W ⟶ A := ⟨fun _ => s₂, K.projF₂, K.proj₂_mem,
    fun n _ hn => ⟨K.proj₂ n, rfl, by rw [hn, K.code_proj₂]; exact hb⟩⟩
  have huv : u = v := hm u v (AsmHom.ext (funext fun _ => hs))
  exact congrArg (fun k => AsmHom.toFun k PUnit.unit) huv

/-- The image assembly: `|B′|` = the ordinary image of `f`, `B′|ₙ = f(A|ₙ)`. -/
@[expose] public def imgAsm {A B : Assembly.{u} K} (f : A ⟶ B) : Assembly.{u} K where
  X := {y : B.X // ∃ x, f.toFun x = y}
  caucus n y := ∃ x, A.caucus n x ∧ f.toFun x = y.val
  carrier_mem y := by
    obtain ⟨x, hx⟩ := y.property
    obtain ⟨n, hn⟩ := A.carrier_mem x
    exact ⟨n, x, hn, hx⟩

/-- The image as a subobject: "named by inclusion using the same modulus as f". -/
@[expose] public def imgSub {A B : Assembly.{u} K} (f : A ⟶ B) : Subobject (Assembly.{u} K) B where
  dom := imgAsm f
  arr := ⟨Subtype.val, by
    obtain ⟨φ, hφ, hf⟩ := f.tracked
    refine ⟨φ, hφ, fun n y hy => ?_⟩
    obtain ⟨x, hx, hfx⟩ := hy
    obtain ⟨m, hm, hBx⟩ := hf n x hx
    exact ⟨m, hm, hfx ▸ hBx⟩⟩
  monic := asmMonic_of_injective _ fun _ _ h => Subtype.ext h

/-- §2.153: the book's image formula is the image.  Allows: "the required factor A → B′ is
    f with the identity as its modulus".  Minimality: for a subobject S allowing f via g,
    send `y = f(x)` to `g(x)` — well-defined since `S.arr` is monic hence injective; a
    modulus of g is a modulus of the factorization because the image caucus at n consists
    exactly of `f`-values of points of `A|ₙ`. -/
public theorem asm_isImage {A B : Assembly.{u} K} (f : A ⟶ B) : IsImage f (imgSub f) := by
  constructor
  · exact ⟨⟨fun x => ⟨f.toFun x, x, rfl⟩, ModFun.ident, K.id_mem,
      fun n x hx => ⟨n, rfl, x, hx, rfl⟩⟩, AsmHom.ext rfl⟩
  · intro S hS
    obtain ⟨g, hg⟩ := hS
    have hg' : ∀ x, S.arr.toFun (g.toFun x) = f.toFun x :=
      fun x => congrArg (fun k => AsmHom.toFun k x) hg
    have hSinj : Function.Injective S.arr.toFun := asmInjective_of_monic S.arr S.monic
    -- the factorization y ↦ g(x) for any x with f(x) = y (all such g(x) agree)
    have hval : ∀ (y : (imgAsm f).X) (x : A.X), f.toFun x = y.val →
        g.toFun (y.property.choose) = g.toFun x := fun y x hx =>
      hSinj (by rw [hg', hg', y.property.choose_spec, hx])
    refine ⟨⟨fun y => g.toFun (y.property.choose), ?_⟩, ?_⟩
    · obtain ⟨σ, hσ, hgtr⟩ := g.tracked
      refine ⟨σ, hσ, fun n y hy => ?_⟩
      obtain ⟨x, hx, hfx⟩ := hy
      obtain ⟨m, hm, hSx⟩ := hgtr n x hx
      refine ⟨m, hm, ?_⟩
      show S.dom.caucus m (g.toFun (y.property.choose))
      rw [hval y x hfx]; exact hSx
    · exact AsmHom.ext (funext fun y => (hg' _).trans y.property.choose_spec)

/-- §1.51: assemblies have images. -/
@[expose] public instance asmHasImages : HasImages (Assembly.{u} K) where
  image := imgSub
  isImage := asm_isImage

/-! ### Covers

  A morphism is a cover iff its image is the whole codomain ASSEMBLY: surjective on
  carriers and, uniformly in n, `B|ₙ ⊆ f(A|ψ(n))` for a single ψ ∈ K.  (Surjectivity
  follows from the caucus condition since every point lies in some caucus.) -/

/-- The concrete cover condition: some ψ ∈ K maps each caucus of B into the f-image of a
    caucus of A. -/
@[expose] public def AsmCover {A B : Assembly.{u} K} (f : A ⟶ B) : Prop :=
  ∃ ψ, K.mem ψ ∧ ∀ n y, B.caucus n y →
    ∃ m, ψ.graph n m ∧ ∃ x, A.caucus m x ∧ f.toFun x = y

theorem AsmCover.surjective {A B : Assembly.{u} K} {f : A ⟶ B} (hc : AsmCover f) :
    Function.Surjective f.toFun := by
  intro y
  obtain ⟨n, hn⟩ := B.carrier_mem y
  obtain ⟨ψ, _, hdom⟩ := hc
  obtain ⟨m, _, x, _, hfx⟩ := hdom n y hn
  exact ⟨x, hfx⟩

/-- `Cover = AsmCover` in assemblies. -/
public theorem asmCover_iff {A B : Assembly.{u} K} (f : A ⟶ B) : Cover f ↔ AsmCover f := by
  constructor
  · -- f factors through its image inclusion; a cover makes the inclusion iso, and the
    -- iso-inverse's modulus is the required ψ.
    intro hc
    obtain ⟨e, he⟩ := (asm_isImage f).1
    obtain ⟨j, _, hji⟩ := hc (imgSub f).arr e (imgSub f).monic he
    obtain ⟨ψ, hψ, hj⟩ := j.tracked
    refine ⟨ψ, hψ, fun n y hy => ?_⟩
    obtain ⟨m, hm, himg⟩ := hj n y hy
    obtain ⟨x, hx, hfx⟩ := himg
    refine ⟨m, hm, x, hx, hfx.trans ?_⟩
    exact congrArg (fun k => AsmHom.toFun k y) hji
  · -- Conversely: any monic the map factors through is bijective with tracked inverse.
    intro hc M m e hm hem
    have hminj : Function.Injective m.toFun := asmInjective_of_monic m hm
    have hme : ∀ x, m.toFun (e.toFun x) = f.toFun x :=
      fun x => congrArg (fun k => AsmHom.toFun k x) hem
    obtain ⟨ψ, hψ, hdom⟩ := hc
    obtain ⟨η, hη, hetr⟩ := e.tracked
    -- the inverse: y ↦ e(x) for the point x with f(x) = y supplied by the cover condition
    have hsur : ∀ y : B.X, ∃ w, m.toFun w = y := by
      intro y
      obtain ⟨n, hn⟩ := B.carrier_mem y
      obtain ⟨_, _, x, _, hfx⟩ := hdom n y hn
      exact ⟨e.toFun x, (hme x).trans hfx⟩
    refine ⟨⟨fun y => (hsur y).choose, ?_⟩, ?_, ?_⟩
    · -- modulus: ψ then a modulus of e
      refine ⟨ψ.comp η, K.comp_mem hψ hη, fun n y hy => ?_⟩
      obtain ⟨m₁, hm₁, x, hx, hfx⟩ := hdom n y hy
      obtain ⟨p, hp, hMx⟩ := hetr m₁ x hx
      refine ⟨p, ⟨m₁, hm₁, hp⟩, ?_⟩
      have hce : (hsur y).choose = e.toFun x :=
        hminj ((hsur y).choose_spec.trans (hfx.symm.trans (hme x).symm))
      show M.caucus p ((hsur y).choose)
      rw [hce]; exact hMx
    · exact AsmHom.ext (funext fun w => hminj (hsur (m.toFun w)).choose_spec)
    · exact AsmHom.ext (funext fun y => (hsur y).choose_spec)

/-- The canonical pullback of a cover is a cover: for `c₀ ∈ C|ₙ`, track `g(c₀)` into a
    caucus of B (modulus γ), pull back along the cover condition of f (modulus ψ), and
    pair the resulting A-index with n — modulus `(γψ, id)`. -/
public theorem asmCover_pullback_canonical {A B C : Assembly.{u} K} (f : A ⟶ B) (g : C ⟶ B)
    (hf : AsmCover f) : AsmCover (asmHasPullbacks.has f g).cone.π₂ := by
  obtain ⟨ψ, hψ, hdom⟩ := hf
  obtain ⟨γ, hγ, hgtr⟩ := g.tracked
  refine ⟨K.pairF (γ.comp ψ) ModFun.ident, K.pair_mem (K.comp_mem hγ hψ) K.id_mem,
    fun n c₀ hc₀ => ?_⟩
  obtain ⟨k, hk, hBgc⟩ := hgtr n c₀ hc₀
  obtain ⟨m₁, hm₁, x, hx, hfx⟩ := hdom k (g.toFun c₀) hBgc
  refine ⟨K.code m₁ n, ⟨m₁, n, ⟨k, hk, hm₁⟩, rfl, rfl⟩,
    ⟨⟨(x, c₀), hfx⟩, ⟨?_, ?_⟩, rfl⟩⟩
  · rw [K.code_proj₁]; exact hx
  · rw [K.code_proj₂]; exact hc₀

/-- Covers transfer between any two pullbacks of the same cospan: if the chosen pullback's
    second projection is a cover then so is that of any pullback cone (the comparison map
    is an iso; `cover_precomp_iso` transports).  Generic in the category — a candidate for
    S1_45, kept local to avoid touching shared files. -/
public theorem cover_pi2_of_isPullback {𝒟 : Type u₁} [Cat.{v₁} 𝒟] {A B C : 𝒟} {f : A ⟶ B}
    {g : C ⟶ B} (pb : HasPullback f g) (c : Cone f g) (hpb : c.IsPullback)
    (hcov : Cover pb.cone.π₂) : Cover c.π₂ := by
  obtain ⟨v, ⟨hv₁, hv₂⟩, _⟩ := hpb pb.cone
  obtain ⟨u₀, _, hu₀⟩ := hpb c
  have hiv : pb.lift c ≫ v = Cat.id c.pt := by
    rw [hu₀ (pb.lift c ≫ v) (by rw [Cat.assoc, hv₁, pb.lift_fst])
          (by rw [Cat.assoc, hv₂, pb.lift_snd]),
        hu₀ (Cat.id c.pt) (Cat.id_comp _) (Cat.id_comp _)]
  have hvi : v ≫ pb.lift c = Cat.id pb.cone.pt := by
    rw [pb.lift_uniq pb.cone (v ≫ pb.lift c)
          (by rw [Cat.assoc, pb.lift_fst, hv₁]) (by rw [Cat.assoc, pb.lift_snd, hv₂]),
        pb.lift_uniq pb.cone (Cat.id pb.cone.pt) (Cat.id_comp _) (Cat.id_comp _)]
  rw [← pb.lift_snd c]
  -- introduce `Cover`'s binders explicitly (Cover-as-def metavar gotcha)
  intro C' m g' hm hgm
  exact cover_precomp_iso (i := pb.lift c) ⟨v, hiv, hvi⟩ hcov m g' hm hgm

/-- §1.52: pullbacks transfer covers.  An arbitrary pullback cone is compared (iso) with
    the canonical one, where the transfer is `asmCover_pullback_canonical`. -/
@[expose] public instance asmPullbacksTransferCovers : PullbacksTransferCovers (Assembly.{u} K) where
  pullbacks_transfer_covers {_A _B _C f g} c hpb hf :=
    cover_pi2_of_isPullback (asmHasPullbacks.has f g) c hpb
      ((asmCover_iff _).2 (asmCover_pullback_canonical f g ((asmCover_iff f).1 hf)))

/-- **§2.153, regular part**: the category of assemblies is a regular category. -/
@[expose] public instance asmRegular : RegularCategory (Assembly.{u} K) where
  toHasTerminal := inferInstance
  toHasBinaryProducts := inferInstance
  toHasPullbacks := inferInstance
  toHasImages := inferInstance
  toPullbacksTransferCovers := inferInstance

/-! ## M6: subobject unions, bottom, inverse images — the pre-logos structure

  The union of two subobjects S, T ⊆ B: carrier = the union of their image sets; the
  caucus at a LEFT-tagged index `code p (inL k)` (any parameter p) is the S-image of
  `S.dom|ₖ`, at a RIGHT-tagged index `code p (inR k)` the T-image of `T.dom|ₖ`.  The
  inclusion is tracked by definition-by-cases over the two subobjects' moduli
  (`cases_mem`); `S ≤ S∪T` is tracked by `k ↦ code k (inL k)`; minimality dispatches the
  two factorizations' moduli by cases.  The parameter slot is what lets these tagged
  indices survive inside the ℓ/ϰ-coded caucuses of a pullback (inverse image) — see
  `invImage_union_le`. -/

section Unions

variable {B : Assembly.{u} K}

/-- The union assembly of two subobjects of B (carrier and tagged caucuses). -/
@[expose] public def unionAsm (S T : Subobject (Assembly.{u} K) B) : Assembly.{u} K where
  X := {y : B.X // (∃ s, S.arr.toFun s = y) ∨ (∃ t, T.arr.toFun t = y)}
  caucus n y :=
    (∃ p k, n = K.code p (K.inL k) ∧ ∃ s, S.dom.caucus k s ∧ S.arr.toFun s = y.val) ∨
    (∃ p k, n = K.code p (K.inR k) ∧ ∃ t, T.dom.caucus k t ∧ T.arr.toFun t = y.val)
  carrier_mem y := by
    rcases y.property with ⟨s, hs⟩ | ⟨t, ht⟩
    · obtain ⟨k, hk⟩ := S.dom.carrier_mem s
      exact ⟨K.code k (K.inL k), Or.inl ⟨k, k, rfl, s, hk, hs⟩⟩
    · obtain ⟨k, hk⟩ := T.dom.carrier_mem t
      exact ⟨K.code k (K.inR k), Or.inr ⟨k, k, rfl, t, hk, ht⟩⟩

/-- The union subobject: the inclusion of `unionAsm`, tracked by cases on the tag. -/
@[expose] public def unionSub (S T : Subobject (Assembly.{u} K) B) : Subobject (Assembly.{u} K) B where
  dom := unionAsm S T
  arr := ⟨Subtype.val, by
    obtain ⟨ρS, hρS, htrS⟩ := S.arr.tracked
    obtain ⟨ρT, hρT, htrT⟩ := T.arr.tracked
    refine ⟨K.casesF (K.projF₂.comp ρS) (K.projF₂.comp ρT),
      K.cases_mem (K.comp_mem K.proj₂_mem hρS) (K.comp_mem K.proj₂_mem hρT),
      fun n y hy => ?_⟩
    rcases hy with ⟨p, k, hn, s, hks, hsy⟩ | ⟨p, k, hn, t, hkt, hty⟩
    · obtain ⟨m, hm, hBm⟩ := htrS k s hks
      refine ⟨m, Or.inl ⟨k, by rw [hn, K.code_proj₂],
        ⟨K.proj₂ (K.code (K.proj₁ n) k), rfl, by rw [K.code_proj₂]; exact hm⟩⟩, ?_⟩
      rw [← hsy]; exact hBm
    · obtain ⟨m, hm, hBm⟩ := htrT k t hkt
      refine ⟨m, Or.inr ⟨k, by rw [hn, K.code_proj₂],
        ⟨K.proj₂ (K.code (K.proj₁ n) k), rfl, by rw [K.code_proj₂]; exact hm⟩⟩, ?_⟩
      rw [← hty]; exact hBm⟩
  monic := asmMonic_of_injective _ fun _ _ h => Subtype.ext h

/-- `S ≤ S ∪ T`, tracked by `k ↦ code k (inL k)`. -/
public theorem unionSub_left (S T : Subobject (Assembly.{u} K) B) : S.le (unionSub S T) := by
  refine ⟨⟨fun s => ⟨S.arr.toFun s, Or.inl ⟨s, rfl⟩⟩,
    K.pairF ModFun.ident (ModFun.ofFun K.inL), K.pair_mem K.id_mem K.inL_mem,
    fun k s hks => ?_⟩, AsmHom.ext rfl⟩
  exact ⟨K.code k (K.inL k),
    ModFun.pairC_graph (ModFun.ident_graph k) (ModFun.ofFun_graph _ k),
    Or.inl ⟨k, k, rfl, s, hks, rfl⟩⟩

/-- `T ≤ S ∪ T`, tracked by `k ↦ code k (inR k)`. -/
public theorem unionSub_right (S T : Subobject (Assembly.{u} K) B) : T.le (unionSub S T) := by
  refine ⟨⟨fun t => ⟨T.arr.toFun t, Or.inr ⟨t, rfl⟩⟩,
    K.pairF ModFun.ident (ModFun.ofFun K.inR), K.pair_mem K.id_mem K.inR_mem,
    fun k t hkt => ?_⟩, AsmHom.ext rfl⟩
  exact ⟨K.code k (K.inR k),
    ModFun.pairC_graph (ModFun.ident_graph k) (ModFun.ofFun_graph _ k),
    Or.inr ⟨k, k, rfl, t, hkt, rfl⟩⟩

/-- Minimality of the union: factorizations of S and T through U are dispatched by cases
    on the tag (well-defined because `U.arr` is monic hence injective). -/
public theorem unionSub_min (S T U : Subobject (Assembly.{u} K) B)
    (hS : S.le U) (hT : T.le U) : (unionSub S T).le U := by
  obtain ⟨hs, hhs⟩ := hS
  obtain ⟨ht, hht⟩ := hT
  have hhs' : ∀ x, U.arr.toFun (hs.toFun x) = S.arr.toFun x :=
    fun x => congrArg (fun j => AsmHom.toFun j x) hhs
  have hht' : ∀ x, U.arr.toFun (ht.toFun x) = T.arr.toFun x :=
    fun x => congrArg (fun j => AsmHom.toFun j x) hht
  have hUinj := asmInjective_of_monic U.arr U.monic
  have hex : ∀ y : (unionAsm S T).X, ∃ w, U.arr.toFun w = y.val := by
    intro y
    rcases y.property with ⟨s, hsy⟩ | ⟨t, hty⟩
    · exact ⟨hs.toFun s, (hhs' s).trans hsy⟩
    · exact ⟨ht.toFun t, (hht' t).trans hty⟩
  refine ⟨⟨fun y => (hex y).choose, ?_⟩,
    AsmHom.ext (funext fun y => (hex y).choose_spec)⟩
  obtain ⟨σS, hσS, htrS⟩ := hs.tracked
  obtain ⟨σT, hσT, htrT⟩ := ht.tracked
  refine ⟨K.casesF (K.projF₂.comp σS) (K.projF₂.comp σT),
    K.cases_mem (K.comp_mem K.proj₂_mem hσS) (K.comp_mem K.proj₂_mem hσT),
    fun n y hy => ?_⟩
  rcases hy with ⟨p, k, hn, s, hks, hsy⟩ | ⟨p, k, hn, t, hkt, hty⟩
  · obtain ⟨m, hm, hUm⟩ := htrS k s hks
    refine ⟨m, Or.inl ⟨k, by rw [hn, K.code_proj₂],
      ⟨K.proj₂ (K.code (K.proj₁ n) k), rfl, by rw [K.code_proj₂]; exact hm⟩⟩, ?_⟩
    have hcs : (hex y).choose = hs.toFun s :=
      hUinj ((hex y).choose_spec.trans (hsy.symm.trans (hhs' s).symm))
    show U.dom.caucus m ((hex y).choose)
    rw [hcs]; exact hUm
  · obtain ⟨m, hm, hUm⟩ := htrT k t hkt
    refine ⟨m, Or.inr ⟨k, by rw [hn, K.code_proj₂],
      ⟨K.proj₂ (K.code (K.proj₁ n) k), rfl, by rw [K.code_proj₂]; exact hm⟩⟩, ?_⟩
    have hct : (hex y).choose = ht.toFun t :=
      hUinj ((hex y).choose_spec.trans (hty.symm.trans (hht' t).symm))
    show U.dom.caucus m ((hex y).choose)
    rw [hct]; exact hUm

end Unions

/-- §1.6: assemblies have subobject unions. -/
@[expose] public instance asmHasSubobjectUnions : HasSubobjectUnions (Assembly.{u} K) where
  union := unionSub
  union_left := unionSub_left
  union_right := unionSub_right
  union_min := unionSub_min

/-- The bottom subobject: the empty assembly, included vacuously. -/
@[expose] public def botSub (A : Assembly.{u} K) : Subobject (Assembly.{u} K) A where
  dom := zeroAsm
  arr := ⟨fun x => x.elim, ModFun.ident, K.id_mem, fun _ x => x.elim⟩
  monic := fun g _ _ => AsmHom.ext (funext fun w => (g.toFun w).elim)

public theorem botSub_min {A : Assembly.{u} K} (S : Subobject (Assembly.{u} K) A) :
    (botSub A).le S :=
  ⟨⟨fun (x : PEmpty) => x.elim, ModFun.ident, K.id_mem, fun _ x => x.elim⟩,
    AsmHom.ext (funext fun (x : PEmpty) => x.elim)⟩

/-! ### Inverse image preserves unions and bottom

  The chosen pullback of `f : A → B` against the inclusion of a subobject V has carrier
  `{(a, v) : f a = v}` with caucuses ℓ/ϰ-coded from A's and V.dom's.  For V = S∪T the
  ϰ-side index is a TAGGED index `code p (inL k)`; the parameter-cases closure is exactly
  what re-tags it into an index of `f#S ∪ f#T` (and back) — see the module docstring. -/

section InvImageUnion

variable {A B : Assembly.{u} K}

/-- `f#(S∪T) ≤ f#S ∪ f#T`.  Underlying function: `(a, u) ↦ a`.  Modulus: reassociate
    `n ↦ code (code n (ℓn)) (ϰϰn)`, then dispatch on the tag of `ϰϰn` with the pair
    `(n, ℓn)` as parameter, producing `code n (inL (code (ℓn) k))`. -/
public theorem invImage_union_le (f : A ⟶ B) (S T : Subobject (Assembly.{u} K) B) :
    (InverseImage f (unionSub S T)).le
      (unionSub (InverseImage f S) (InverseImage f T)) := by
  have hmem : ∀ w : (InverseImage f (unionSub S T)).dom.X,
      (∃ q, (InverseImage f S).arr.toFun q = w.val.1) ∨
      (∃ q, (InverseImage f T).arr.toFun q = w.val.1) := by
    intro w
    have hw : f.toFun w.val.1 = (w.val.2 : (unionAsm S T).X).val := w.property
    rcases (w.val.2 : (unionAsm S T).X).property with ⟨s, hs⟩ | ⟨t, ht⟩
    · exact Or.inl ⟨⟨(w.val.1, s), hw.trans hs.symm⟩, rfl⟩
    · exact Or.inr ⟨⟨(w.val.1, t), hw.trans ht.symm⟩, rfl⟩
  refine ⟨⟨fun w => ⟨w.val.1, hmem w⟩, ?_⟩, AsmHom.ext rfl⟩
  refine ⟨(K.pairF (K.pairF ModFun.ident K.projF₁) (K.projF₂.comp K.projF₂)).comp
      (K.casesF
        (K.pairF (K.projF₁.comp K.projF₁)
          ((K.pairF (K.projF₁.comp K.projF₂) K.projF₂).comp (ModFun.ofFun K.inL)))
        (K.pairF (K.projF₁.comp K.projF₁)
          ((K.pairF (K.projF₁.comp K.projF₂) K.projF₂).comp (ModFun.ofFun K.inR)))),
    K.comp_mem
      (K.pair_mem (K.pair_mem K.id_mem K.proj₁_mem) (K.comp_mem K.proj₂_mem K.proj₂_mem))
      (K.cases_mem
        (K.pair_mem (K.comp_mem K.proj₁_mem K.proj₁_mem)
          (K.comp_mem (K.pair_mem (K.comp_mem K.proj₁_mem K.proj₂_mem) K.proj₂_mem)
            K.inL_mem))
        (K.pair_mem (K.comp_mem K.proj₁_mem K.proj₁_mem)
          (K.comp_mem (K.pair_mem (K.comp_mem K.proj₁_mem K.proj₂_mem) K.proj₂_mem)
            K.inR_mem))),
    fun n w hw => ?_⟩
  have hw' : f.toFun w.val.1 = (w.val.2 : (unionAsm S T).X).val := w.property
  obtain ⟨hA, hu⟩ := hw
  rcases hu with ⟨p, k, hn2, s, hks, hsy⟩ | ⟨p, k, hn2, t, hkt, hty⟩
  · refine ⟨K.code n (K.inL (K.code (K.proj₁ n) k)),
      ModFun.comp_graph
        (ModFun.pairC_graph
          (ModFun.pairC_graph (ModFun.ident_graph n) (ModFun.ofFun_graph _ n))
          (ModFun.comp_graph (ModFun.ofFun_graph _ n) (ModFun.ofFun_graph _ _)))
        (Or.inl ⟨k, ?_, ?_⟩), ?_⟩
    · rw [K.code_proj₂, hn2, K.code_proj₂]
    · rw [K.code_proj₁]
      exact ModFun.pairC_graph
        (ModFun.comp_graph (ModFun.ofFun_graph _ _) (by simp only [ModFun.ofFun_graph_iff,
          K.code_proj₁]))
        (ModFun.comp_graph
          (ModFun.pairC_graph
            (ModFun.comp_graph (ModFun.ofFun_graph _ _) (by simp only [ModFun.ofFun_graph_iff,
              K.code_proj₁, K.code_proj₂]))
            (by simp only [ModFun.ofFun_graph_iff, K.code_proj₂]))
          (ModFun.ofFun_graph _ _))
    · refine Or.inl ⟨n, K.code (K.proj₁ n) k, rfl, ⟨(w.val.1, s), hw'.trans hsy.symm⟩,
        ⟨?_, ?_⟩, rfl⟩
      · show A.caucus (K.proj₁ (K.code (K.proj₁ n) k)) w.val.1
        rw [K.code_proj₁]; exact hA
      · show S.dom.caucus (K.proj₂ (K.code (K.proj₁ n) k)) s
        rw [K.code_proj₂]; exact hks
  · refine ⟨K.code n (K.inR (K.code (K.proj₁ n) k)),
      ModFun.comp_graph
        (ModFun.pairC_graph
          (ModFun.pairC_graph (ModFun.ident_graph n) (ModFun.ofFun_graph _ n))
          (ModFun.comp_graph (ModFun.ofFun_graph _ n) (ModFun.ofFun_graph _ _)))
        (Or.inr ⟨k, ?_, ?_⟩), ?_⟩
    · rw [K.code_proj₂, hn2, K.code_proj₂]
    · rw [K.code_proj₁]
      exact ModFun.pairC_graph
        (ModFun.comp_graph (ModFun.ofFun_graph _ _) (by simp only [ModFun.ofFun_graph_iff,
          K.code_proj₁]))
        (ModFun.comp_graph
          (ModFun.pairC_graph
            (ModFun.comp_graph (ModFun.ofFun_graph _ _) (by simp only [ModFun.ofFun_graph_iff,
              K.code_proj₁, K.code_proj₂]))
            (by simp only [ModFun.ofFun_graph_iff, K.code_proj₂]))
          (ModFun.ofFun_graph _ _))
    · refine Or.inr ⟨n, K.code (K.proj₁ n) k, rfl, ⟨(w.val.1, t), hw'.trans hty.symm⟩,
        ⟨?_, ?_⟩, rfl⟩
      · show A.caucus (K.proj₁ (K.code (K.proj₁ n) k)) w.val.1
        rw [K.code_proj₁]; exact hA
      · show T.dom.caucus (K.proj₂ (K.code (K.proj₁ n) k)) t
        rw [K.code_proj₂]; exact hkt

/-- `f#S ∪ f#T ≤ f#(S∪T)`.  Underlying function: `a ↦ (a, f a)`.  Modulus: on a tagged
    index `code p (inL k)` produce `code (ℓk) (code k (inL (ϰk)))` — the pullback pairing
    of the A-part of k with the retagged S-part. -/
public theorem le_invImage_union (f : A ⟶ B) (S T : Subobject (Assembly.{u} K) B) :
    (unionSub (InverseImage f S) (InverseImage f T)).le
      (InverseImage f (unionSub S T)) := by
  have hmem : ∀ y : (unionAsm (InverseImage f S) (InverseImage f T)).X,
      (∃ s, S.arr.toFun s = f.toFun y.val) ∨ (∃ t, T.arr.toFun t = f.toFun y.val) := by
    intro y
    rcases y.property with ⟨q, hq⟩ | ⟨q, hq⟩
    · have hq' : f.toFun (q.val.1) = S.arr.toFun (q.val.2) := q.property
      exact Or.inl ⟨q.val.2, hq'.symm.trans (congrArg f.toFun hq)⟩
    · have hq' : f.toFun (q.val.1) = T.arr.toFun (q.val.2) := q.property
      exact Or.inr ⟨q.val.2, hq'.symm.trans (congrArg f.toFun hq)⟩
  refine ⟨⟨fun y => ⟨(y.val, ⟨f.toFun y.val, hmem y⟩), rfl⟩, ?_⟩, AsmHom.ext rfl⟩
  refine ⟨K.casesF
      (K.pairF (K.projF₂.comp K.projF₁)
        (K.pairF K.projF₂ ((K.projF₂.comp K.projF₂).comp (ModFun.ofFun K.inL))))
      (K.pairF (K.projF₂.comp K.projF₁)
        (K.pairF K.projF₂ ((K.projF₂.comp K.projF₂).comp (ModFun.ofFun K.inR)))),
    K.cases_mem
      (K.pair_mem (K.comp_mem K.proj₂_mem K.proj₁_mem)
        (K.pair_mem K.proj₂_mem (K.comp_mem (K.comp_mem K.proj₂_mem K.proj₂_mem) K.inL_mem)))
      (K.pair_mem (K.comp_mem K.proj₂_mem K.proj₁_mem)
        (K.pair_mem K.proj₂_mem (K.comp_mem (K.comp_mem K.proj₂_mem K.proj₂_mem) K.inR_mem))),
    fun n y hy => ?_⟩
  rcases hy with ⟨p, k, hn, q, hkq, hqa⟩ | ⟨p, k, hn, q, hkq, hqa⟩
  · obtain ⟨hkA, hkS⟩ := hkq
    refine ⟨K.code (K.proj₁ k) (K.code k (K.inL (K.proj₂ k))),
      Or.inl ⟨k, by rw [hn, K.code_proj₂], ?_⟩, ⟨?_, ?_⟩⟩
    · exact ModFun.pairC_graph
        (ModFun.comp_graph (ModFun.ofFun_graph _ _) (by simp only [ModFun.ofFun_graph_iff,
          K.code_proj₂]))
        (ModFun.pairC_graph
          (by simp only [ModFun.ofFun_graph_iff, K.code_proj₂])
          (ModFun.comp_graph
            (ModFun.comp_graph (ModFun.ofFun_graph _ _) (ModFun.ofFun_graph _ _))
            (by simp only [ModFun.ofFun_graph_iff, K.code_proj₂])))
    · show A.caucus (K.proj₁ (K.code (K.proj₁ k) (K.code k (K.inL (K.proj₂ k))))) y.val
      rw [K.code_proj₁, ← hqa]
      exact hkA
    · show (unionAsm S T).caucus
        (K.proj₂ (K.code (K.proj₁ k) (K.code k (K.inL (K.proj₂ k)))))
        ⟨f.toFun y.val, hmem y⟩
      rw [K.code_proj₂]
      have hq' : f.toFun (q.val.1) = S.arr.toFun (q.val.2) := q.property
      exact Or.inl ⟨k, K.proj₂ k, rfl, q.val.2, hkS,
        hq'.symm.trans (congrArg f.toFun hqa)⟩
  · obtain ⟨hkA, hkT⟩ := hkq
    refine ⟨K.code (K.proj₁ k) (K.code k (K.inR (K.proj₂ k))),
      Or.inr ⟨k, by rw [hn, K.code_proj₂], ?_⟩, ⟨?_, ?_⟩⟩
    · exact ModFun.pairC_graph
        (ModFun.comp_graph (ModFun.ofFun_graph _ _) (by simp only [ModFun.ofFun_graph_iff,
          K.code_proj₂]))
        (ModFun.pairC_graph
          (by simp only [ModFun.ofFun_graph_iff, K.code_proj₂])
          (ModFun.comp_graph
            (ModFun.comp_graph (ModFun.ofFun_graph _ _) (ModFun.ofFun_graph _ _))
            (by simp only [ModFun.ofFun_graph_iff, K.code_proj₂])))
    · show A.caucus (K.proj₁ (K.code (K.proj₁ k) (K.code k (K.inR (K.proj₂ k))))) y.val
      rw [K.code_proj₁, ← hqa]
      exact hkA
    · show (unionAsm S T).caucus
        (K.proj₂ (K.code (K.proj₁ k) (K.code k (K.inR (K.proj₂ k)))))
        ⟨f.toFun y.val, hmem y⟩
      rw [K.code_proj₂]
      have hq' : f.toFun (q.val.1) = T.arr.toFun (q.val.2) := q.property
      exact Or.inr ⟨k, K.proj₂ k, rfl, q.val.2, hkT,
        hq'.symm.trans (congrArg f.toFun hqa)⟩

/-- `f#(⊥) ≅ ⊥`: the pullback against the empty subobject is empty. -/
public theorem invImage_bot_iso (f : A ⟶ B) :
    Isomorphic (InverseImage f (botSub B)).dom (botSub A).dom := by
  refine ⟨⟨fun w => (w.val.2 : PEmpty).elim, ModFun.ident, K.id_mem,
      fun _ _ hw => (hw.2 : False).elim⟩,
    ⟨fun (e : PEmpty) => e.elim, ModFun.ident, K.id_mem, fun _ _ h => (h : False).elim⟩,
    AsmHom.ext (funext fun w => (w.val.2 : PEmpty).elim),
    AsmHom.ext (funext fun (e : PEmpty) => e.elim)⟩

end InvImageUnion

/-- **§2.153, pre-logos part**: the category of assemblies is a pre-logos. -/
@[expose] public instance asmPreLogos : PreLogos (Assembly.{u} K) where
  toRegularCategory := inferInstance
  toHasSubobjectUnions := inferInstance
  bottom := botSub
  bottom_min := botSub_min
  bottom_dom_iso _ _ := ⟨Cat.id zeroAsm, Cat.id zeroAsm, Cat.id_comp _, Cat.id_comp _⟩
  invImage_preserves_union f S T := ⟨invImage_union_le f S T, le_invImage_union f S T⟩
  invImage_preserves_bottom f := invImage_bot_iso f

/-! ## M7: binary coproducts — positivity

  The book leaves "the construction of disjoint unions to the reader".  ON PAPER: the
  carrier must be the disjoint sum |A| ⊕ |B|; the question is the caucuses.  Untagged
  same-index caucuses `(A⊕B)|ₙ = A|ₙ ⊕ B|ₙ` give the injections identity moduli, but the
  case map `[f,g]` would need a single K-index containing both `φ(n)`-caucus values of C
  (from left elements) and `ψ(n)`-caucus values (right) — false in general.  So the
  caucuses must be TAGGED, `(A⊕B)|_{code p (inL k)} = inl(A|ₖ)` and
  `(A⊕B)|_{code p (inR k)} = inr(B|ₖ)`, whence the injections are tracked by
  `k ↦ code k (inL k)` (needs `pair_mem` + tag membership) and `[f,g]` by
  definition-by-cases on the tag (needs `cases_mem`) — conditions (i)(ii)(iii) alone
  provably do NOT provide either (the K₀ counterexample in the module docstring kills
  even the weaker image property), which is why `ModulusSystem` carries the tag closure
  explicitly; all partial functions satisfy it (`ModulusSystem.allPartial`).

  These caucuses are BY CONSTRUCTION those of `unionSub (inlSub) (inrSub)`, so the §1.621
  disjointness conditions (inl ∩ inr ≤ 0, inl ∪ inr = A+B) fall out definitionally: the
  pullback of the two injections has empty carrier, and the identity is a modulus for
  `A+B ≤ inl ∪ inr`. -/

/-- The coproduct assembly: disjoint sum with tag-shaped caucuses. -/
@[expose] public def coprodAsm (A B : Assembly.{u} K) : Assembly.{u} K where
  X := A.X ⊕ B.X
  caucus n z :=
    (∃ p k, n = K.code p (K.inL k) ∧ ∃ a, A.caucus k a ∧ Sum.inl a = z) ∨
    (∃ p k, n = K.code p (K.inR k) ∧ ∃ b, B.caucus k b ∧ Sum.inr b = z)
  carrier_mem z := by
    rcases z with a | b
    · obtain ⟨k, hk⟩ := A.carrier_mem a
      exact ⟨K.code k (K.inL k), Or.inl ⟨k, k, rfl, a, hk, rfl⟩⟩
    · obtain ⟨k, hk⟩ := B.carrier_mem b
      exact ⟨K.code k (K.inR k), Or.inr ⟨k, k, rfl, b, hk, rfl⟩⟩

/-- §2.153 coproducts: injections tracked by `k ↦ code k (in• k)`, case map by
    definition-by-cases on the tag. -/
@[expose] public instance asmHasBinaryCoproducts : HasBinaryCoproducts (Assembly.{u} K) where
  coprod := coprodAsm
  inl := ⟨Sum.inl, K.pairF ModFun.ident (ModFun.ofFun K.inL),
    K.pair_mem K.id_mem K.inL_mem, fun k a hk =>
      ⟨K.code k (K.inL k),
        ModFun.pairC_graph (ModFun.ident_graph k) (ModFun.ofFun_graph _ k),
        Or.inl ⟨k, k, rfl, a, hk, rfl⟩⟩⟩
  inr := ⟨Sum.inr, K.pairF ModFun.ident (ModFun.ofFun K.inR),
    K.pair_mem K.id_mem K.inR_mem, fun k b hk =>
      ⟨K.code k (K.inR k),
        ModFun.pairC_graph (ModFun.ident_graph k) (ModFun.ofFun_graph _ k),
        Or.inr ⟨k, k, rfl, b, hk, rfl⟩⟩⟩
  case f g :=
    ⟨Sum.elim f.toFun g.toFun, by
      obtain ⟨φ, hφ, hf⟩ := f.tracked
      obtain ⟨ψ, hψ, hg⟩ := g.tracked
      refine ⟨K.casesF (K.projF₂.comp φ) (K.projF₂.comp ψ),
        K.cases_mem (K.comp_mem K.proj₂_mem hφ) (K.comp_mem K.proj₂_mem hψ),
        fun n z hz => ?_⟩
      rcases hz with ⟨p, k, hn, a, hka, hza⟩ | ⟨p, k, hn, b, hkb, hzb⟩
      · obtain ⟨m, hm, hXa⟩ := hf k a hka
        refine ⟨m, Or.inl ⟨k, by rw [hn, K.code_proj₂],
          ⟨K.proj₂ (K.code (K.proj₁ n) k), rfl, by rw [K.code_proj₂]; exact hm⟩⟩, ?_⟩
        rw [← hza]; exact hXa
      · obtain ⟨m, hm, hXb⟩ := hg k b hkb
        refine ⟨m, Or.inr ⟨k, by rw [hn, K.code_proj₂],
          ⟨K.proj₂ (K.code (K.proj₁ n) k), rfl, by rw [K.code_proj₂]; exact hm⟩⟩, ?_⟩
        rw [← hzb]; exact hXb⟩
  case_inl _ _ := AsmHom.ext rfl
  case_inr _ _ := AsmHom.ext rfl
  case_uniq f g h h₁ h₂ := AsmHom.ext (funext fun z => by
    rcases z with a | b
    · exact congrArg (fun j => AsmHom.toFun j a) h₁
    · exact congrArg (fun j => AsmHom.toFun j b) h₂)

/-- **§2.153 HEADLINE: the category of assemblies is a POSITIVE PRE-LOGOS.** -/
@[expose] public instance asmPositivePreLogos : PositivePreLogos (Assembly.{u} K) where
  toPreLogos := inferInstance
  toHasBinaryCoproducts := inferInstance

/-- §1.621/§1.623: the coproduct is a disjoint complemented union — the injections are
    monic, their intersection is bottom (the fibre product of `inl`, `inr` is empty), and
    their union is everything (identity modulus, since the coproduct caucuses ARE the
    union's caucuses). -/
@[expose] public instance asmDisjointBinaryCoproduct : DisjointBinaryCoproduct (Assembly.{u} K) where
  toPositivePreLogos := inferInstance
  inl_monic {A B} := asmMonic_of_injective (HasBinaryCoproducts.inl (A := A) (B := B))
    fun _ _ h => Sum.inl.inj h
  inr_monic {A B} := asmMonic_of_injective (HasBinaryCoproducts.inr (A := A) (B := B))
    fun _ _ h => Sum.inr.inj h
  inl_inter_inr {A B} := by
    have habs : ∀ w : (Subobject.inter
        (inlSub (𝒞 := Assembly.{u} K) (A := A) (B := B)
          (asmMonic_of_injective _ fun _ _ h => Sum.inl.inj h))
        (inrSub (asmMonic_of_injective _ fun _ _ h => Sum.inr.inj h))).dom.X, False :=
      fun w => nomatch (show Sum.inl w.val.1 = Sum.inr w.val.2 from w.property)
    exact ⟨⟨fun w => (habs w).elim, ModFun.ident, K.id_mem, fun _ w _ => (habs w).elim⟩,
      AsmHom.ext (funext fun w => (habs w).elim)⟩
  inl_union_inr {A B} := by
    refine ⟨⟨fun z => ⟨z, ?_⟩, ModFun.ident, K.id_mem, fun n z hz => ⟨n, rfl, ?_⟩⟩,
      AsmHom.ext rfl⟩
    · rcases z with a | b
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inr ⟨b, rfl⟩
    · rcases hz with ⟨p, k, hn, a, hka, hza⟩ | ⟨p, k, hn, b, hkb, hzb⟩
      · exact Or.inl ⟨p, k, hn, a, hka, hza⟩
      · exact Or.inr ⟨p, k, hn, b, hkb, hzb⟩

/-! ## M8: the functor ∇ : S → A

  Book: "Note the functor ∇ : S → A given by |∇X| = (∇X)|ₙ = X, for all n; for
  f : X → Y let ∇f be f with the identity as modulus.  ∇ preserves coterminator,
  equalizers, and finite products, but not unions."

  Preservations are stated as isomorphisms with the chosen constructions.  That ∇ does
  NOT preserve unions is a remark about a suitable K (e.g. partial recursives): a union
  of subobjects of ∇X carries tagged caucuses remembering WHICH side an element came
  from, while ∇ of the set-union forgets it; no K-modulus can recompute the side from
  the full caucuses of ∇(S∪T) when membership in S is not "decidable" relative to K.
  Over `allPartial` every function has a modulus and the failure disappears, so there is
  no uniform counterexample to formalize here; left as this remark (as in the book). -/

/-- The assembly ∇X: all caucuses equal to the whole of X. -/
@[expose] public def nablaAsm (X : Type u) : Assembly.{u} K := ⟨X, fun _ _ => True, fun _ => ⟨0, trivial⟩⟩

/-- ∇ on morphisms: `f` with the identity modulus. -/
def nablaMap {X Y : Type u} (f : X → Y) : nablaAsm (K := K) X ⟶ nablaAsm Y :=
  ⟨f, ModFun.ident, K.id_mem, fun n _ _ => ⟨n, rfl, trivial⟩⟩

/-- ∇ is a functor from S = `Type u` (with `setCat`) to the category of assemblies. -/
def nablaFunctor : Functor (Type u) (Assembly.{u} K) where
  obj := nablaAsm (K := K)
  map := nablaMap
  map_id _ := AsmHom.ext rfl
  map_comp _ _ := AsmHom.ext rfl

/-- ∇ preserves the coterminator: `∇∅ ≅ 0`. -/
theorem nabla_coterminator : Isomorphic (nablaAsm (K := K) PEmpty) zeroAsm :=
  ⟨⟨fun (x : PEmpty) => x.elim, ModFun.ident, K.id_mem, fun _ x _ => x.elim⟩,
    ⟨fun (x : PEmpty) => x.elim, ModFun.ident, K.id_mem, fun _ x _ => x.elim⟩,
    AsmHom.ext (funext fun (x : PEmpty) => x.elim),
    AsmHom.ext (funext fun (x : PEmpty) => x.elim)⟩

/-- ∇ preserves the terminator: `∇1 ≅ 1`. -/
theorem nabla_terminator : Isomorphic (nablaAsm (K := K) PUnit) oneAsm :=
  ⟨⟨fun _ => PUnit.unit, ModFun.ident, K.id_mem, fun n _ _ => ⟨n, rfl, trivial⟩⟩,
    ⟨fun _ => PUnit.unit, ModFun.ident, K.id_mem, fun n _ _ => ⟨n, rfl, trivial⟩⟩,
    AsmHom.ext (funext fun _ => rfl), AsmHom.ext (funext fun _ => rfl)⟩

/-- ∇ preserves equalizers: the assembly equalizer of ∇f, ∇g is ∇ of the set equalizer. -/
theorem nabla_equalizer {X Y : Type u} (f g : X → Y) :
    Isomorphic (eqObj (nablaMap (K := K) f) (nablaMap g))
      (nablaAsm {x : X // f x = g x}) :=
  ⟨⟨fun e => ⟨e.val, e.property⟩, ModFun.ident, K.id_mem, fun n _ _ => ⟨n, rfl, trivial⟩⟩,
    ⟨fun e => ⟨e.val, e.property⟩, ModFun.ident, K.id_mem, fun n _ hx => ⟨n, rfl, hx⟩⟩,
    AsmHom.ext (funext fun _ => rfl), AsmHom.ext (funext fun _ => rfl)⟩

/-- ∇ preserves binary products: `∇X × ∇Y ≅ ∇(X × Y)`. -/
theorem nabla_product (X Y : Type u) :
    Isomorphic (prodAsm (nablaAsm (K := K) X) (nablaAsm Y)) (nablaAsm (X × Y)) :=
  ⟨⟨fun p => p, ModFun.ident, K.id_mem, fun n _ _ => ⟨n, rfl, trivial⟩⟩,
    ⟨fun p => p, ModFun.ident, K.id_mem, fun n _ _ =>
      ⟨n, rfl, trivial, trivial⟩⟩,
    AsmHom.ext (funext fun _ => rfl), AsmHom.ext (funext fun _ => rfl)⟩

/-! ## Remaining work (book claims not formalized here)

  * "The category of assemblies is NOT effective."  PROVED in
    `Freyd/S2_153f_ParityWitness.lean` (via the reduction of `S2_153_NonEffective`).
    An earlier version of this note guessed the claim needs a recursion-theoretically
    nontrivial K and that effectiveness "plausibly HOLDS" over `allPartial` — wrong:
    the obstruction is uniformity of naming (a splitting forces a single caucus index
    of the relation to contain the whole kernel), so the parity witness on `∇ℕ` works
    UNIFORMLY, over the partial-recursive `Krec` (`S2_153b`) and over `allPartial`.

  * "∇ does not preserve unions" — a claim about a suitable K; see the M8 section
    comment. -/

end Freyd
