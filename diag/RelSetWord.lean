/-
  `diag.RelSetWord` — the strict tower's interpretation in `Rel(Set)`.

  WHY THIS FILE EXISTS.  The tower is strict, so its objects are WORDS, not sets: `(a ⊗ b) ⊗ c` and
  `a ⊗ (b ⊗ c)` are the same word and the associator is gone.  `Rel(Set)` (`AOP/A6_1_RelSet.lean`)
  cannot be the object type — `(A × B) × C` is not `A × (B × C)` as a Lean type — so a word is
  INTERPRETED as a set instead: `⟦[a, b, c]⟧ = a × (b × (c × PUnit))`, and an arrow of the tower is
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

/-- A word of sets interpreted as a set: the letters' product, right-nested, empty word to `PUnit`.
    The tail `PUnit` is what makes `⟦u ++ v⟧ ≅ ⟦u⟧ × ⟦v⟧` hold for EVERY split, including the two
    where one side is empty — with `⟦[a]⟧ = a` the empty split would need `a ≅ a × PUnit` instead,
    which is the same isomorphism moved somewhere less convenient. -/
def Interp : List RelSet.{u} → Type u
  | [] => PUnit
  | a :: rest => a.carrier × Interp rest

/-- The set a word denotes. -/
def carrier (a : Word RelSet.{u}) : Type u := Interp (Word.letters a)

/-- `⟦u ++ v⟧ → ⟦u⟧ × ⟦v⟧`, by recursion on the left word. -/
def split : (u v : List RelSet.{u}) → Interp (u ++ v) → Interp u × Interp v
  | [], _, p => (PUnit.unit, p)
  | _ :: u, v, p => ((p.1, (split u v p.2).1), (split u v p.2).2)

/-- `⟦u⟧ × ⟦v⟧ → ⟦u ++ v⟧`, the inverse. -/
def merge : (u v : List RelSet.{u}) → Interp u × Interp v → Interp (u ++ v)
  | [], _, p => p.2
  | _ :: u, v, p => (p.1.1, merge u v (p.1.2, p.2))

@[simp] theorem split_merge (u v : List RelSet.{u}) (p : Interp u × Interp v) :
    split u v (merge u v p) = p := by
  induction u with
  | nil => exact match p with | (PUnit.unit, _) => rfl
  | cons _ u ih =>
    show ((p.1.1, (split u v (merge u v (p.1.2, p.2))).1), (split u v (merge u v (p.1.2, p.2))).2) = p
    rw [ih (p.1.2, p.2)]
    rfl

@[simp] theorem merge_split (u v : List RelSet.{u}) (p : Interp (u ++ v)) :
    merge u v (split u v p) = p := by
  induction u with
  | nil => rfl
  | cons _ u ih =>
    show (p.1, merge u v ((split u v p.2).1, (split u v p.2).2)) = p
    rw [show ((split u v p.2).1, (split u v p.2).2) = split u v p.2 from rfl, ih p.2]
    rfl

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

/-- A transport along a list equality passes through a `cons`. -/
theorem cast_cons {x : RelSet.{u}} {l l' : List RelSet.{u}} (h : l = l')
    (v : x.carrier) (p : Interp l) :
    cast (congrArg Interp (congrArg (x :: ·) h)) ((v, p) : Interp (x :: l))
      = ((v, cast (congrArg Interp h) p) : Interp (x :: l')) := by
  subst h; rfl

theorem merge_assoc (u v w : List RelSet.{u}) (x : Interp u) (y : Interp v) (z : Interp w) :
    merge (u ++ v) w (merge u v (x, y), z)
      = cast (congrArg Interp (List.append_assoc u v w).symm)
          (merge u (v ++ w) (x, merge v w (y, z))) := by
  induction u with
  | nil => rfl
  | cons head u ih =>
    show (x.1, merge (u ++ v) w (merge u v (x.2, y), z)) = _
    rw [ih x.2, ← cast_cons (List.append_assoc u v w).symm x.1]
    rfl

end Freyd.Diag
