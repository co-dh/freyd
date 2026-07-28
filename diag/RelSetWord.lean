/-
  `diag.RelSetWord` — the strict tower's interpretation in `Rel(Set)`.

  WHY THIS FILE EXISTS.  The tower is strict, so its objects are WORDS, not sets: `(a ⊗ b) ⊗ c` and
  `a ⊗ (b ⊗ c)` are the same word and the associator is gone.  `Rel(Set)` (`AOP/A6_1_RelSet.lean`)
  cannot be the object type — `(A × B) × C` is not `A × (B × C)` as a Lean type — so a word is
  INTERPRETED as a set instead: `⟦[a, b, c]⟧ = a × (b × c)`, and an arrow of the tower is
  an honest relation between interpretations.  This is where the coherence isomorphisms of the
  non-strict presentation went: `⟦u ++ v⟧ ≅ ⟦u⟧ × ⟦v⟧` is `split`/`merge` below, proved once here
  rather than carried through every theorem of the tower.

  WHAT IT BUYS.  A theorem proved in the tower, instantiated at this model, is a statement about
  relations between Lean types — which is what the AOP layer manipulates.  Without it the strict
  tower says nothing about `AOP/`.
-/
import diag.Monoidal
import AOP.A6_1_RelSet

universe u

namespace Freyd.Diag

open Freyd Freyd.Alg
open scoped Word

/-- A word of sets interpreted as a set: the letters' product, right-nested, with NO unit tail —
    a one-letter word denotes its letter, `⟦[a]⟧ = a`, not `a × PUnit`.

    That choice is the whole point of the file.  An AOP relation `List α ⇸ Nat` is then literally an
    arrow of this model between one-letter words; with a tail it would only be one up to
    `a × PUnit ≅ a`, and that isomorphism would have to be spent at every statement AOP ever borrows
    from the tower.  The price is paid here instead: `split` and `merge` below case on whether
    either side is empty, and their proofs carry those cases. -/
def Interp : List RelSet.{u} → Type u
  | [] => PUnit
  | [a] => a.carrier
  | a :: rest => a.carrier × Interp rest

/-- The set a word denotes. -/
def carrier (a : Word RelSet.{u}) : Type u := Interp (Word.letters a)

/-- `⟦u ++ v⟧ → ⟦u⟧ × ⟦v⟧`, by recursion on the left word.  The two singleton cases are where the
    missing unit tail is paid for: a one-letter left word carries no pair to take apart. -/
def split : (u v : List RelSet.{u}) → Interp (u ++ v) → Interp u × Interp v
  | [], _, p => (PUnit.unit, p)
  | [_], [], p => (p, PUnit.unit)
  | [_], _ :: _, p => (p.1, p.2)
  | _ :: (b :: u), v, p => ((p.1, (split (b :: u) v p.2).1), (split (b :: u) v p.2).2)

/-- `⟦u⟧ × ⟦v⟧ → ⟦u ++ v⟧`, the inverse. -/
def merge : (u v : List RelSet.{u}) → Interp u × Interp v → Interp (u ++ v)
  | [], _, p => p.2
  | [_], [], p => p.1
  | [_], _ :: _, p => (p.1, p.2)
  | _ :: (b :: u), v, p => (p.1.1, merge (b :: u) v (p.1.2, p.2))

@[simp] theorem split_merge (u v : List RelSet.{u}) (p : Interp u × Interp v) :
    split u v (merge u v p) = p := by
  induction u, v, p using merge.induct <;> simp_all only [split, merge] <;> rfl

@[simp] theorem merge_split (u v : List RelSet.{u}) (p : Interp (u ++ v)) :
    merge u v (split u v p) = p := by
  induction u, v, p using split.induct <;> simp_all only [split, merge] <;> rfl

/-! ### The isomorphism at the level of words

  `letters` turns a product of words into a concatenation, but only up to a propositional equality
  of lists, so the transport is written out once here and never again. -/

/-- `⟦a ⊗ b⟧ → ⟦a⟧ × ⟦b⟧`. -/
def splitTens (a b : Word RelSet.{u}) (p : carrier (Word.tens a b)) : carrier a × carrier b :=
  split _ _ (cast (congrArg Interp (Word.letters_tens a b)) p)

/-- `⟦a⟧ × ⟦b⟧ → ⟦a ⊗ b⟧`, the inverse. -/
def mergeTens (a b : Word RelSet.{u}) (p : carrier a × carrier b) : carrier (Word.tens a b) :=
  cast (congrArg Interp (Word.letters_tens a b)).symm (merge _ _ p)

@[simp] theorem splitTens_mergeTens (a b : Word RelSet.{u}) (p : carrier a × carrier b) :
    splitTens a b (mergeTens a b p) = p := by
  show split _ _ (cast _ (cast _ (merge _ _ p))) = p
  rw [cast_cast, cast_eq, split_merge]

@[simp] theorem mergeTens_splitTens (a b : Word RelSet.{u}) (p : carrier (Word.tens a b)) :
    mergeTens a b (splitTens a b p) = p := by
  show cast _ (merge _ _ (split _ _ (cast _ p))) = p
  rw [merge_split, cast_cast, cast_eq]

/-! ### The category

  An arrow of the tower at `Rel(Set)` is a relation between the interpretations — the same
  definition `AOP/A6_1_RelSet.lean` gives for `RelSet` itself, read through `carrier`. -/

instance : Cat (Word RelSet.{u}) where
  Hom a b := carrier a → carrier b → Prop
  id _ := fun x y => x = y
  comp R S := fun x z => ∃ y, R x y ∧ S y z
  id_comp _ := funext fun x => funext fun _ => propext ⟨fun ⟨_, h, hR⟩ => h ▸ hR,
    fun hR => ⟨x, rfl, hR⟩⟩
  comp_id _ := funext fun _ => funext fun y => propext ⟨fun ⟨_, hR, h⟩ => h ▸ hR,
    fun hR => ⟨y, hR, rfl⟩⟩
  assoc _ _ _ := funext fun _ => funext fun _ => propext
    ⟨fun ⟨_, ⟨y, hR, hS⟩, hT⟩ => ⟨y, hR, _, hS, hT⟩,
     fun ⟨y, hR, _, hS, hT⟩ => ⟨_, ⟨y, hR, hS⟩, hT⟩⟩

instance : HomLE (Word RelSet.{u}) where
  «≤» R S := ∀ x y, R x y → S x y

instance : OrderedCat (Word RelSet.{u}) where
  «≤_refl» _ _ _ h := h
  «≤_trans» hRS hST x y h := hST x y (hRS x y h)
  «≤_antisymm» hRS hSR :=
    funext fun x => funext fun y => propext ⟨fun h => hRS x y h, fun h => hSR x y h⟩
  comp_mono hR hS x z := fun ⟨y, hxy, hyz⟩ => ⟨y, hR x y hxy, hS y z hyz⟩

/-! ### The tensor of two relations

  `R ⊗ S` relates a pair to a pair componentwise, the pairs read off by `splitTens`.  Everything
  below is proved by turning an element of `⟦a ⊗ b⟧` into the pair it splits into and back, so the
  only facts used are that `splitTens` and `mergeTens` are inverse. -/

/-- The tensor of two relations. -/
def tensRel {a a' b b' : Word RelSet.{u}} (R : a ⟶ a') (S : b ⟶ b') :
    Word.tens a b ⟶ Word.tens a' b' :=
  fun p q => R (splitTens a b p).1 (splitTens a' b' q).1 ∧ S (splitTens a b p).2 (splitTens a' b' q).2

/-- `splitTens` is injective, because `mergeTens` undoes it. -/
theorem splitTens_inj {a b : Word RelSet.{u}} {p q : carrier (Word.tens a b)}
    (h : splitTens a b p = splitTens a b q) : p = q := by
  rw [← mergeTens_splitTens a b p, ← mergeTens_splitTens a b q, h]

theorem tensRel_id (a b : Word RelSet.{u}) :
    tensRel (𝟙 a) (𝟙 b) = 𝟙 (Word.tens a b) := by
  funext p q
  refine propext ⟨fun ⟨h1, h2⟩ => splitTens_inj ?_, fun h => ?_⟩
  · exact Prod.ext h1 h2
  · exact ⟨congrArg (·.1) (congrArg (splitTens a b) h), congrArg (·.2) (congrArg (splitTens a b) h)⟩

theorem tensRel_comp {a a' a'' b b' b'' : Word RelSet.{u}}
    (R : a ⟶ a') (R' : a' ⟶ a'') (S : b ⟶ b') (S' : b' ⟶ b'') :
    tensRel (R ≫ R') (S ≫ S') = tensRel R S ≫ tensRel R' S' := by
  funext p q
  refine propext ⟨fun ⟨⟨y, hR, hR'⟩, ⟨z, hS, hS'⟩⟩ => ⟨mergeTens a' b' (y, z), ?_, ?_⟩,
    fun ⟨m, ⟨hR, hS⟩, ⟨hR', hS'⟩⟩ => ⟨⟨_, hR, hR'⟩, ⟨_, hS, hS'⟩⟩⟩
  · simp only [tensRel, splitTens_mergeTens]; exact ⟨hR, hS⟩
  · simp only [tensRel, splitTens_mergeTens]; exact ⟨hR', hS'⟩

theorem tensRel_mono {a a' b b' : Word RelSet.{u}} {R R' : a ⟶ a'} {S S' : b ⟶ b'}
    (hR : R ≤ R') (hS : S ≤ S') : tensRel R S ≤ tensRel R' S' :=
  fun _ _ ⟨h1, h2⟩ => ⟨hR _ _ h1, hS _ _ h2⟩

/-! ### Re-bracketing

  `(a ⊗ b) ⊗ c` and `a ⊗ (b ⊗ c)` are the same word, so the two ways of building an element of it
  out of three pieces must agree — that agreement is what `tensHom_assoc` needs, and it is the one
  place an induction over the letters is unavoidable. -/

/-- A transport along a list equality passes through a `cons` whose tail is itself a `cons` — the
    only shape in which `Interp` is a pair, now that a one-letter word denotes its letter. -/
theorem cast_cons {x b b' : RelSet.{u}} {l l' : List RelSet.{u}} (h : b :: l = b' :: l')
    (v : x.carrier) (p : Interp (b :: l)) :
    cast (congrArg Interp (congrArg (x :: ·) h)) ((v, p) : Interp (x :: b :: l))
      = ((v, cast (congrArg Interp h) p) : Interp (x :: b' :: l')) := by
  injection h with hb hl
  subst hb; subst hl; rfl

/-- Building an element of `u ++ v ++ w` from three pieces does not depend on the bracketing.  This
    is what `tensHom_assoc` consumes, and the one place the letters have to be inducted over. -/
theorem merge_assoc (u v w : List RelSet.{u}) (x : Interp u) (y : Interp v) (z : Interp w) :
    merge (u ++ v) w (merge u v (x, y), z)
      = cast (congrArg Interp (List.append_assoc u v w).symm)
          (merge u (v ++ w) (x, merge v w (y, z))) := by
  induction u with
  | nil => rfl
  | cons head u ih =>
    cases u with
    | nil => cases v with
      | nil => rfl
      | cons _ _ => rfl
    | cons b u' =>
      show (x.1, merge ((b :: u') ++ v) w (merge (b :: u') v (x.2, y), z)) = _
      rw [ih x.2, ← cast_cons (List.append_assoc (b :: u') v w).symm x.1]
      rfl

/-- A transport on the left factor comes out of the merge. -/
theorem merge_cast_left {u u' v : List RelSet.{u}} (h : u = u') (m : Interp u) (z : Interp v) :
    merge u' v (cast (congrArg Interp h) m, z)
      = cast (congrArg Interp (congrArg (· ++ v) h)) (merge u v (m, z)) := by
  subst h; rfl

/-- A transport on the right factor comes out of the merge. -/
theorem merge_cast_right {u v v' : List RelSet.{u}} (h : v = v') (m : Interp u) (z : Interp v) :
    merge u v' (m, cast (congrArg Interp h) z)
      = cast (congrArg Interp (congrArg (u ++ ·) h)) (merge u v (m, z)) := by
  subst h; rfl

/-- The word-level re-bracketing: `(x ⊗ y) ⊗ z` and `x ⊗ (y ⊗ z)` are the same element of the same
    object.  Every transport in sight is an equality of TYPES, so proof irrelevance identifies them
    and the two sides differ by nothing. -/
theorem mergeTens_assoc (a b c : Word RelSet.{u})
    (x : carrier a) (y : carrier b) (z : carrier c) :
    mergeTens (Word.tens a b) c (mergeTens a b (x, y), z)
      = mergeTens a (Word.tens b c) (x, mergeTens b c (y, z)) := by
  show cast _ (merge _ _ (cast _ (merge _ _ (x, y)), z))
      = cast _ (merge _ _ (x, cast _ (merge _ _ (y, z))))
  rw [merge_cast_left, merge_cast_right, merge_assoc, cast_cast, cast_cast, cast_cast]
  · exact (Word.letters_tens b c).symm
  · exact (Word.letters_tens a b).symm

/-- Reading three pieces off `a ⊗ (b ⊗ c)` gives back the three that built it as `(a ⊗ b) ⊗ c`. -/
theorem splitTens_assoc (a b c : Word RelSet.{u})
    (x : carrier a) (y : carrier b) (z : carrier c) :
    splitTens a (Word.tens b c) (mergeTens (Word.tens a b) c (mergeTens a b (x, y), z))
      = (x, mergeTens b c (y, z)) := by
  rw [mergeTens_assoc, splitTens_mergeTens]

theorem tensRel_assoc {a a' b b' c c' : Word RelSet.{u}}
    (R : a ⟶ a') (S : b ⟶ b') (T : c ⟶ c') :
    tensRel (tensRel R S) T = tensRel R (tensRel S T) := by
  funext p q
  -- Every element of `(a ⊗ b) ⊗ c` is three pieces put together; say so, and both sides read the
  -- same three back.
  rw [← mergeTens_splitTens (Word.tens a b) c p, ← mergeTens_splitTens (Word.tens a' b') c' q]
  generalize splitTens (Word.tens a b) c p = P
  generalize splitTens (Word.tens a' b') c' q = Q
  obtain ⟨pab, pc⟩ := P
  obtain ⟨qab, qc⟩ := Q
  rw [← mergeTens_splitTens a b pab, ← mergeTens_splitTens a' b' qab]
  generalize splitTens a b pab = X
  generalize splitTens a' b' qab = Y
  obtain ⟨pa, pb⟩ := X
  obtain ⟨qa, qb⟩ := Y
  simp only [tensRel, splitTens_mergeTens, splitTens_assoc]
  exact propext ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

/-! ### The units and the symmetry -/

theorem tensRel_lunit {a b : Word RelSet.{u}} (R : a ⟶ b) :
    tensRel (𝟙 (Word.unit : Word RelSet.{u})) R = R := by
  funext p q
  exact propext ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

/-- Splitting off the empty word on the RIGHT gives back what you started with.  The left unit needs
    no such lemma — `split` recurses on its left argument, so `𝕀 ⊗ b` reduces on its own. -/
theorem split_nil (u : List RelSet.{u}) (p : Interp (u ++ [])) :
    (split u [] p).1 = cast (congrArg Interp (List.append_nil u)) p := by
  induction u with
  | nil => rfl
  | cons head u ih =>
    cases u with
    | nil => rfl
    | cons b u' =>
      show (p.1, (split (b :: u') [] p.2).1) = _
      rw [ih p.2, ← cast_cons (List.append_nil (b :: u')) p.1]
      rfl

theorem splitTens_unit_right (a : Word RelSet.{u}) (p : carrier (Word.tens a Word.unit)) :
    (splitTens a Word.unit p).1 = p := by
  show (split a.letters [] (cast (congrArg Interp (Word.letters_tens a Word.unit)) p)).1 = p
  rw [split_nil, cast_cast]
  rfl

theorem tensRel_runit {a b : Word RelSet.{u}} (R : a ⟶ b) :
    tensRel R (𝟙 (Word.unit : Word RelSet.{u})) = R := by
  funext p q
  rw [tensRel, splitTens_unit_right, splitTens_unit_right]
  exact propext ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

/-- Two elements built from pieces agree exactly when the pieces do. -/
@[simp] theorem mergeTens_inj {a b : Word RelSet.{u}} {p q : carrier a × carrier b} :
    mergeTens a b p = mergeTens a b q ↔ p = q := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have := congrArg (splitTens a b) h
  rwa [splitTens_mergeTens, splitTens_mergeTens] at this

/-- The symmetry: the two halves change places. -/
def swapRel (a b : Word RelSet.{u}) : Word.tens a b ⟶ Word.tens b a :=
  fun p q => (splitTens a b p).1 = (splitTens b a q).2 ∧ (splitTens a b p).2 = (splitTens b a q).1

theorem swapRel_swapRel (a b : Word RelSet.{u}) :
    swapRel a b ≫ swapRel b a = 𝟙 (Word.tens a b) := by
  funext p r
  refine propext ⟨fun ⟨q, ⟨h1, h2⟩, ⟨h3, h4⟩⟩ => splitTens_inj (Prod.ext ?_ ?_), fun h => ?_⟩
  · rw [h1, h4]
  · rw [h2, h3]
  · subst h
    exact ⟨mergeTens b a ((splitTens a b p).2, (splitTens a b p).1), by
      simp [swapRel, splitTens_mergeTens], by simp [swapRel, splitTens_mergeTens]⟩

theorem swapRel_nat {a a' b b' : Word RelSet.{u}} (R : a ⟶ a') (S : b ⟶ b') :
    tensRel R S ≫ swapRel a' b' = swapRel a b ≫ tensRel S R := by
  funext p q
  refine propext ⟨fun ⟨m, ⟨hR, hS⟩, ⟨h1, h2⟩⟩ => ?_, fun ⟨n, ⟨h1, h2⟩, ⟨hS, hR⟩⟩ => ?_⟩
  · refine ⟨mergeTens b a ((splitTens a b p).2, (splitTens a b p).1), ?_, ?_⟩
    · simp [swapRel, splitTens_mergeTens]
    · simp only [tensRel, splitTens_mergeTens]
      exact ⟨h2 ▸ hS, h1 ▸ hR⟩
  · refine ⟨mergeTens a' b' ((splitTens b' a' q).2, (splitTens b' a' q).1), ?_, ?_⟩
    · simp only [tensRel, splitTens_mergeTens]
      exact ⟨h1 ▸ hR, h2 ▸ hS⟩
    · simp [swapRel, splitTens_mergeTens]

/-- The hexagon, with every associator an identity: taking `a` past `b ⊗ c` is taking it past `b`
    and then past `c`.  Both sides are read off the same three pieces. -/
theorem swapRel_hexagon (a b c : Word RelSet.{u}) :
    swapRel a (Word.tens b c)
      = ((tensRel (swapRel a b) (𝟙 c) :
            Word.tens (Word.tens a b) c ⟶ Word.tens (Word.tens b a) c)
          ≫ (tensRel (𝟙 b) (swapRel a c) :
            Word.tens b (Word.tens a c) ⟶ Word.tens b (Word.tens c a))) := by
  funext p q
  rw [← mergeTens_splitTens (Word.tens a b) c p,
    ← mergeTens_splitTens (Word.tens b c) a q]
  generalize splitTens (Word.tens a b) c p = P
  generalize splitTens (Word.tens b c) a q = Q
  obtain ⟨pab, pc⟩ := P
  obtain ⟨qbc, qa⟩ := Q
  rw [← mergeTens_splitTens a b pab, ← mergeTens_splitTens b c qbc]
  generalize splitTens a b pab = X
  generalize splitTens b c qbc = Y
  obtain ⟨pa, pb⟩ := X
  obtain ⟨qb, qc⟩ := Y
  refine propext ⟨fun ⟨h1, h2⟩ => ⟨mergeTens (Word.tens b a) c (mergeTens b a (pb, pa), pc), ?_, ?_⟩,
    fun ⟨m, hm1, hm2⟩ => ?_⟩
  · simp_all only [tensRel, swapRel, splitTens_mergeTens, splitTens_assoc, mergeTens_inj,
      Prod.mk.injEq]
    exact ⟨⟨trivial, trivial⟩, rfl⟩
  · simp_all only [tensRel, swapRel, splitTens_mergeTens, splitTens_assoc, mergeTens_inj,
      Prod.mk.injEq]
    exact ⟨rfl, trivial, trivial⟩
  · rw [← mergeTens_splitTens (Word.tens b a) c m] at hm1 hm2
    generalize splitTens (Word.tens b a) c m = M at hm1 hm2
    obtain ⟨mba, mc⟩ := M
    rw [← mergeTens_splitTens b a mba] at hm1 hm2
    generalize splitTens b a mba = N at hm1 hm2
    obtain ⟨mb, ma⟩ := N
    simp only [tensRel, swapRel, splitTens_mergeTens, splitTens_assoc, mergeTens_inj,
      Prod.mk.injEq] at hm1 hm2 ⊢
    exact ⟨hm1.1.1.trans hm2.2.1, hm1.1.2.trans hm2.1, hm1.2.trans hm2.2.2⟩

/-! ### The model

  Everything above assembles into the interpretation the strict tower was missing. -/

instance : SymMonCat RelSet.{u} :=
  { (inferInstance : OrderedCat (Word RelSet.{u})) with
    tensHom := tensRel
    tensHom_id := tensRel_id
    tensHom_comp := tensRel_comp
    tensHom_mono := tensRel_mono
    tensHom_assoc := tensRel_assoc
    tensHom_lunit := tensRel_lunit
    tensHom_runit := tensRel_runit
    swap := swapRel
    swap_swap := swapRel_swapRel
    swap_nat := swapRel_nat
    hexagon := swapRel_hexagon }

/-- THE PAYOFF, stated so it cannot rot: an arrow between one-letter words IS a relation between the
    letters — the same thing `AOP/A6_1_RelSet.lean` calls an arrow of `RelSet`.  This is what the
    unit-tail-free `Interp` bought, and what makes a theorem of the tower a statement about the
    types the AOP layer manipulates. -/
theorem hom_gen (X Y : RelSet.{u}) :
    (Word.gen X ⟶ Word.gen Y) = (X.carrier → Y.carrier → Prop) := rfl

end Freyd.Diag
