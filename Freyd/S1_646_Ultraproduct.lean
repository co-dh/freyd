/-
  Mathlib-free ultraproduct of a family of types modulo an ultrafilter (§1.646, Phase B).

  ## Why this file exists

  §1.646's representation of a small special pre-logos into `𝒮` (sets) is built in two halves:

  * **Phase A** (`Freyd/Ultrafilter.lean`): the index `I` of finite sets of proper subobjects, the
    pre-filter `F₀` of principal coideals, and an ULTRAFILTER `U ⊇ F₀` extending it.
  * **Phase B** (THIS FILE): the ultra-product functor `𝒮^I →[U] 𝒮`, `X ↦ Ultraproduct X U`, which
    collapses the `I`-indexed power down to a single set while PRESERVING finite limits (so the
    composite `Tᶠ : 𝒞 → 𝒮` is still left-exact / faithful) and PRESERVING PROPERNESS (a proper
    subobject survives because its support coideal lies in `U` — the §1.645 "`%e(U) = ∅`" argument,
    `S1_64.lean:113-124`).

  Freyd treats the ultra-product as ambient set theory.  We build it from `Classical.choice` (via the
  `Quotient`/`Quot.sound` already used by the ultrafilter file) and NOTHING ELSE — no mathlib, no
  category theory.  The category-theoretic hand-off (`Tᶠ : 𝒞 → 𝒮`) is Phase D and lives elsewhere; this
  file is the pure-set ultra-product and the Łoś-style preservation lemmas it needs.

  ## What is here

  * `Ultraproduct X U`           — the quotient of `∀ i, X i` by `x ≈ y ⟺ {i | x i = y i} ∈ U`.
  * `Ultraproduct.map`           — functoriality: a family `f : ∀ i, X i → Y i` acts on classes.
  * `Ultraproduct.prodEquiv`     — `Ultraproduct (X × Y) U ≃ Ultraproduct X U × Ultraproduct Y U`.
  * `Ultraproduct.unitEquiv`     — `Ultraproduct (fun _ => Unit) U ≃ Unit` (terminal).
  * `Ultraproduct.equalizerEquiv`— ultra-product of equalisers IS the equaliser (Łoś for `=`).
  * `Ultraproduct.map_injective` — `f i` injective on a `U`-large set ⟹ `map f U` injective.
  * `Ultraproduct.map_not_surjective` — `f i` proper (non-surjective) on a `U`-large set ⟹ `map f U`
    not surjective.  This is the properness-survival the §1.646 representation turns on.
-/
import Freyd.S1_646_Ultrafilter

namespace Freyd.UF

universe u v w

open Filter

variable {I : Type u}

/-! ## The ultra-product setoid

`x ≈ y` iff `x` and `y` agree on a `U`-large set of coordinates.  Reflexivity uses `univ ∈ U`;
symmetry uses symmetry of `=`; transitivity intersects the two agreement sets (`inter_mem'`) and
up-closes along `{i | x i = z i} ⊇ {x = y} ∩ {y = z}`. -/

/-- The agreement set `{i | x i = y i}` of two sections. -/
def agree {X : I → Type w} (x y : ∀ i, X i) : Sub I := fun i => x i = y i

theorem agree_refl {X : I → Type w} (x : ∀ i, X i) : agree x x = univ :=
  Sub.ext fun _ => ⟨fun _ => trivial, fun _ => rfl⟩

/-- The ultra-product relation on sections: agreement on a `U`-large set. -/
def UEq {X : I → Type w} (U : Ultrafilter I) (x y : ∀ i, X i) : Prop :=
  U.toFilter.sets (agree x y)

theorem UEq.refl {X : I → Type w} (U : Ultrafilter I) (x : ∀ i, X i) : UEq U x x := by
  have := U.toFilter.univ_mem
  rwa [← agree_refl x] at this

theorem UEq.symm {X : I → Type w} {U : Ultrafilter I} {x y : ∀ i, X i}
    (h : UEq U x y) : UEq U y x := by
  have he : agree x y = agree y x := Sub.ext fun _ => ⟨Eq.symm, Eq.symm⟩
  unfold UEq at h ⊢; rwa [he] at h

theorem UEq.trans {X : I → Type w} {U : Ultrafilter I} {x y z : ∀ i, X i}
    (hxy : UEq U x y) (hyz : UEq U y z) : UEq U x z := by
  -- {x = y} ∩ {y = z} ⊆ {x = z}, and the intersection is in U.
  have hcap : U.toFilter.sets (agree x y ∩ᵤ agree y z) := U.toFilter.inter_mem hxy hyz
  exact U.toFilter.up_closed hcap (fun i ⟨h1, h2⟩ => h1.trans h2)

/-- The ultra-product setoid on `∀ i, X i`. -/
def ultraSetoid {X : I → Type w} (U : Ultrafilter I) : Setoid (∀ i, X i) where
  r := UEq U
  iseqv := ⟨UEq.refl U, UEq.symm, UEq.trans⟩

/-- **The ultra-product** of a family `X : I → Type w` modulo an ultrafilter `U`. -/
def Ultraproduct (X : I → Type w) (U : Ultrafilter I) : Type (max u w) :=
  Quotient (ultraSetoid (X := X) U)

namespace Ultraproduct

variable {X : I → Type w} {Y : I → Type w} {Z : I → Type w} {U : Ultrafilter I}

/-- The class of a section `x : ∀ i, X i`. -/
def mk (U : Ultrafilter I) (x : ∀ i, X i) : Ultraproduct X U := Quotient.mk (ultraSetoid U) x

@[simp] theorem mk_eq (x : ∀ i, X i) : Quotient.mk (ultraSetoid (X := X) U) x = mk U x := rfl

/-- Agreement on a `U`-large set implies equal classes (`Quot.sound`). -/
theorem sound {x y : ∀ i, X i} (h : U.toFilter.sets (agree x y)) : mk U x = mk U y :=
  Quotient.sound h

/-- Equal classes give agreement on a `U`-large set (`Quotient.exact`). -/
theorem exact {x y : ∀ i, X i} (h : mk U x = mk U y) : U.toFilter.sets (agree x y) :=
  Quotient.exact h

/-- Eliminator: every element of the ultra-product is the class of some section. -/
@[elab_as_elim]
theorem ind {motive : Ultraproduct X U → Prop} (h : ∀ x, motive (mk U x)) :
    ∀ q, motive q := Quotient.ind h

/-! ## Functoriality

A family of maps `f : ∀ i, X i → Y i` acts coordinatewise and descends to classes: if `x ≈ y` then
`(fun i => f i (x i)) ≈ (fun i => f i (y i))`, because agreement of `x, y` is up-closed into agreement
of their `f`-images. -/

/-- The coordinatewise action of a family of maps on sections. -/
def liftSection (f : ∀ i, X i → Y i) (x : ∀ i, X i) : ∀ i, Y i := fun i => f i (x i)

/-- **Functoriality.**  A family `f : ∀ i, X i → Y i` induces a map on ultra-products. -/
def map (f : ∀ i, X i → Y i) (U : Ultrafilter I) : Ultraproduct X U → Ultraproduct Y U :=
  Quotient.lift (fun x => mk U (liftSection f x)) <| by
    intro x y h
    -- {x = y} ⊆ {f∘x = f∘y}, so the image classes agree.
    refine sound (U.toFilter.up_closed h (fun i hi => ?_))
    simp only [agree, liftSection] at hi ⊢; rw [hi]

@[simp] theorem map_mk (f : ∀ i, X i → Y i) (x : ∀ i, X i) :
    map f U (mk U x) = mk U (liftSection f x) := rfl

/-- `map` of the identity family is the identity. -/
@[simp] theorem map_id : map (fun _ => id) U = (id : Ultraproduct X U → _) := by
  funext q; induction q using ind with | _ x => rfl

/-- `map` is functorial in the family (composition). -/
theorem map_comp (f : ∀ i, X i → Y i) (g : ∀ i, Y i → Z i) :
    map g U ∘ map f U = map (fun i => g i ∘ f i) U := by
  funext q; induction q using ind with | _ x => rfl

/-- A binary family `f : ∀ i, X i → Y i → Z i` lifts to a map on the product of ultra-products. -/
def map₂ (f : ∀ i, X i → Y i → Z i) (U : Ultrafilter I) :
    Ultraproduct X U → Ultraproduct Y U → Ultraproduct Z U := by
  refine Quotient.lift₂ (fun x y => mk U (fun i => f i (x i) (y i))) ?_
  intro x₁ y₁ x₂ y₂ hx hy
  -- {x₁=x₂} ∩ {y₁=y₂} ⊆ {f x₁ y₁ = f x₂ y₂}.
  refine sound (U.toFilter.up_closed (U.toFilter.inter_mem hx hy) (fun i hi => ?_))
  obtain ⟨h1, h2⟩ := hi
  simp only [agree] at h1 h2 ⊢; rw [h1, h2]

@[simp] theorem map₂_mk (f : ∀ i, X i → Y i → Z i) (x : ∀ i, X i) (y : ∀ i, Y i) :
    map₂ f U (mk U x) (mk U y) = mk U (fun i => f i (x i) (y i)) := rfl

/-! ## Łoś-style finite-limit preservation

A plain bijection of types (`Bij`) packages "the ultra-product of this limit IS the limit of the
ultra-products".  We do not reach for `Cat`'s `≃` (it drags in the whole category library); a bare
type bijection is all §1.646 needs, since the limit-preservation is checked on underlying sets. -/

/-- A bare bijection of types (mathlib-free `Equiv`). -/
structure Bij (A : Type v) (B : Type v) where
  /-- forward map. -/
  toFun : A → B
  /-- backward map. -/
  invFun : B → A
  /-- left inverse. -/
  left_inv : ∀ a, invFun (toFun a) = a
  /-- right inverse. -/
  right_inv : ∀ b, toFun (invFun b) = b

namespace Bij
variable {A B : Type v}

/-- The forward map of a bijection is injective. -/
theorem toFun_injective (e : Bij A B) : ∀ {a a'}, e.toFun a = e.toFun a' → a = a' := by
  intro a a' h; rw [← e.left_inv a, ← e.left_inv a', h]

/-- The forward map of a bijection is surjective. -/
theorem toFun_surjective (e : Bij A B) (b : B) : ∃ a, e.toFun a = b :=
  ⟨e.invFun b, e.right_inv b⟩

end Bij

/-! ### Products: `Ⓤ(X × Y) ≃ ⓊX × ⓊY` -/

/-- **Products preserved.**  The ultra-product of the pointwise product is the product of the
    ultra-products: forward splits a class into its two coordinate classes (`map fst`, `map snd`),
    backward re-pairs (`map₂ Prod.mk`).  The round-trips hold because pairing/unpairing is the
    identity coordinatewise, so the agreement set is `univ`. -/
def prodEquiv (X Y : I → Type w) (U : Ultrafilter I) :
    Bij (Ultraproduct (fun i => X i × Y i) U) (Ultraproduct X U × Ultraproduct Y U) where
  toFun q := (map (fun _ => Prod.fst) U q, map (fun _ => Prod.snd) U q)
  invFun p := map₂ (fun _ => Prod.mk) U p.1 p.2
  left_inv := by
    intro q; induction q using ind with
    | _ x =>
      -- forward gives (mk fst∘x, mk snd∘x), back re-pairs to mk (fst∘x, snd∘x) = mk x (defeq).
      refine sound (U.toFilter.up_closed U.toFilter.univ_mem (fun i _ => ?_)); rfl
  right_inv := by
    intro p; obtain ⟨a, b⟩ := p
    induction a using ind with
    | _ x => induction b using ind with
      | _ y =>
        refine Prod.ext ?_ ?_ <;>
          exact sound (U.toFilter.up_closed U.toFilter.univ_mem (fun i _ => rfl))

/-! ### Terminal object: `Ⓤ(fun _ => Unit) ≃ Unit` -/

/-- **Terminal preserved.**  The ultra-product of the constant family `PUnit` is `PUnit`: every
    section is `fun _ => ()`, so the whole product is a single class.  (`PUnit` at the ambient universe
    `max u w` so the types live in one universe, as `Bij` requires.) -/
def unitEquiv (U : Ultrafilter I) :
    Bij (Ultraproduct (fun _ : I => PUnit.{max u w + 1}) U) PUnit.{max u w + 1} where
  toFun _ := PUnit.unit
  invFun _ := mk U (fun _ => PUnit.unit)
  left_inv := by
    intro q; induction q using ind with
    | _ x =>
      refine sound (U.toFilter.up_closed U.toFilter.univ_mem (fun i _ => ?_))
      exact Subsingleton.elim _ _
  right_inv := fun _ => rfl

/-! ### Equalisers (Łoś for `=`): the fibre/diagonal piece

Given `f g : ∀ i, X i → Y i`, the equaliser of `map f, map g` in `Set` is `{q | map f q = map g q}`.
We show its members are exactly the classes of sections `x` with `f x = g x` on a `U`-large set — i.e.
the ultra-product of the pointwise equalisers `Eq i := {a : X i // f i a = g i a}` injects onto it.
This is the diagonal/equaliser preservation `PreservesPullbacks` needs (a pullback is the equaliser of
the two projections composed with the maps). -/

/-- The pointwise equaliser subtype `{a : X i // f i a = g i a}`. -/
def Equ (f g : ∀ i, X i → Y i) (i : I) : Type w := { a : X i // f i a = g i a }

/-- **The Łoś equality lemma.**  Two ultra-product classes are equal iff `map f` and `map g` send them
    to the same class — phrased as: `map f q = map g q` iff `q` is the class of a section `x` with
    `{i | f i (x i) = g i (x i)} ∈ U`.  This is the engine of equaliser/pullback preservation. -/
theorem map_eq_map_iff (f g : ∀ i, X i → Y i) (x : ∀ i, X i) :
    map f U (mk U x) = map g U (mk U x) ↔ U.toFilter.sets (fun i => f i (x i) = g i (x i)) := by
  have hmk : (mk U (liftSection f x) = mk U (liftSection g x)) ↔
      U.toFilter.sets (agree (liftSection f x) (liftSection g x)) :=
    ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
  rw [map_mk, map_mk, hmk]
  constructor <;> intro h <;> (refine U.toFilter.up_closed h (fun i hi => ?_)) <;>
    simpa only [agree, liftSection] using hi

/-- A **diagonal section** of the equaliser family: a global choice of equalising element at every
    coordinate.  Such a section is exactly what is needed to fill the `U`-small bad coordinates when
    pulling a class of the equaliser back into the ultra-product of the pointwise equalisers.  (In the
    §1.646 application the relevant equalisers/pullbacks always have a global section — a point of the
    fibre — so this hypothesis is met; without ANY equalising element the fibre family can be locally
    empty and no total section exists, so the hypothesis is genuinely required, not a shortcut.) -/
abbrev Diag (f g : ∀ i, X i → Y i) := ∀ i, Equ f g i

open Classical in
/-- Correct a section `x : ∀ i, X i` to a section of the equaliser family, using a diagonal section `d`
    on the coordinates where `x` fails to equalise. -/
noncomputable def correct (f g : ∀ i, X i → Y i) (d : Diag f g) (x : ∀ i, X i) : ∀ i, Equ f g i :=
  fun i => if hi : f i (x i) = g i (x i) then ⟨x i, hi⟩ else d i

/-- On coordinates where `x` already equalises, the correction returns `x i`. -/
theorem correct_val_of_eq (f g : ∀ i, X i → Y i) (d : Diag f g) {x : ∀ i, X i} {i : I}
    (hi : f i (x i) = g i (x i)) : (correct f g d x i).1 = x i := by
  rw [correct, dif_pos hi]

/-- **Equalisers preserved** (given a diagonal section `d`).  The ultra-product of the pointwise
    equalisers `Equ f g` bijects with the equaliser `{q // map f q = map g q}` of the two
    ultra-product maps.  Forward: include each coordinate (`Subtype.val`); the result equalises
    everywhere, hence `U`-largely (`map_eq_map_iff`).  Backward: a class in the equaliser is the class
    of an `x` equalising `U`-largely; `correct f g d x` is a genuine equaliser section agreeing with
    `x` on that large set, so the two classes match. -/
noncomputable def equalizerEquiv (f g : ∀ i, X i → Y i) (d : Diag f g) (U : Ultrafilter I) :
    Bij (Ultraproduct (Equ f g) U)
      { q : Ultraproduct X U // map f U q = map g U q } where
  toFun := by
    refine Quotient.lift (fun e => ⟨mk U (fun i => (e i).1), ?_⟩) ?_
    · refine (map_eq_map_iff f g _).2 (U.toFilter.up_closed U.toFilter.univ_mem (fun i _ => ?_))
      exact (e i).2
    · intro a b h
      refine Subtype.ext (sound (U.toFilter.up_closed h (fun i hi => ?_)))
      simp only [agree] at hi ⊢; rw [hi]
  invFun q := by
    refine Quotient.liftOn q.1 (fun x => mk U (correct f g d x)) ?_
    intro a b h
    -- on {a = b} ∈ U, correct a and correct b coincide coordinatewise (same value, same branch).
    refine sound (U.toFilter.up_closed h (fun i hi => ?_))
    simp only [agree] at hi ⊢
    simp only [correct]; rw [hi]
  left_inv := by
    intro e; induction e using ind with
    | _ x =>
      -- correct (val ∘ x) = x on the (everywhere-true) set where val∘x equalises.
      show mk U (correct f g d (fun i => (x i).1)) = mk U x
      refine sound (U.toFilter.up_closed U.toFilter.univ_mem (fun i _ => ?_))
      have hi : f i (x i).1 = g i (x i).1 := (x i).2
      simp only [agree, correct, dif_pos hi]
      rfl
  right_inv := by
    intro q; obtain ⟨q, hq⟩ := q
    induction q using ind with
    | _ x =>
      -- the equality witness `hq` says x equalises U-largely; there correct x = x, so the val-classes
      -- agree U-largely.
      have hlarge : U.toFilter.sets (fun i => f i (x i) = g i (x i)) := (map_eq_map_iff f g x).1 hq
      refine Subtype.ext ?_
      show mk U (fun i => (correct f g d x i).1) = mk U x
      refine sound (U.toFilter.up_closed hlarge (fun i hi => ?_))
      simp only [agree]; exact correct_val_of_eq f g d hi

/-! ## Injectivity / properness transfer (the §1.645/§1.646 key)

The ultra-product map inherits injectivity and non-surjectivity from a `U`-large set of coordinates.
These are exactly the two facts the representation `Tᶠ : 𝒞 → 𝒮` needs: a mono `m` (injective on each
`Hom(i,-)`) stays mono, and a PROPER subobject (`m i` non-surjective on a `U`-large coideal of `i`)
stays proper — its complement element survives in the ultra-product, so `%e(U) = ∅`. -/

/-- **Injectivity transfer.**  If `f i` is injective for a `U`-large set of `i`, then `map f U` is
    injective.  (`{f x = f y} ∩ {f i injective} ⊆ {x = y}`, and both are in `U`.) -/
theorem map_injective (f : ∀ i, X i → Y i) (U : Ultrafilter I)
    (hinj : U.toFilter.sets (fun i => Function.Injective (f i))) :
    Function.Injective (map f U) := by
  refine fun q r h => ?_
  induction q using ind with
  | _ x => induction r using ind with
    | _ y =>
      -- map f (mk x) = map f (mk y) gives {f x = f y} ∈ U.
      have hmk : mk U (liftSection f x) = mk U (liftSection f y) ↔
          U.toFilter.sets (agree (liftSection f x) (liftSection f y)) :=
        ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
      have hfeq : U.toFilter.sets (agree (liftSection f x) (liftSection f y)) := hmk.1 h
      -- intersect with the injectivity set, then x = y on the intersection.
      refine sound (U.toFilter.up_closed (U.toFilter.inter_mem hfeq hinj) (fun i hi => ?_))
      obtain ⟨hfi, hinji⟩ := hi
      exact hinji hfi

/-- **Properness / non-surjectivity transfer.**  If there is a family `b : ∀ i, Y i` that lies outside
    the image of `f i` for a `U`-large set of `i` (`{i | ∀ a, f i a ≠ b i} ∈ U`), then the class of `b`
    is NOT hit by `map f U`: the ultra-product map is not surjective.  This is the survival of a proper
    subobject — `b` is the "missing point" the ultra-product keeps because its support coideal is in
    `U`. -/
theorem map_not_surjective (f : ∀ i, X i → Y i) (U : Ultrafilter I) (b : ∀ i, Y i)
    (hmiss : U.toFilter.sets (fun i => ∀ a, f i a ≠ b i)) :
    ¬ ∃ q, map f U q = mk U b := by
  rintro ⟨q, hq⟩
  induction q using ind with
  | _ x =>
    -- map f (mk x) = mk b gives {f x = b} ∈ U; intersect with the miss-set to get ∅ ∈ U.
    have hmk : mk U (liftSection f x) = mk U b ↔ U.toFilter.sets (agree (liftSection f x) b) :=
      ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
    have hhit : U.toFilter.sets (agree (liftSection f x) b) := hmk.1 hq
    have hcap : U.toFilter.sets (agree (liftSection f x) b ∩ᵤ (fun i => ∀ a, f i a ≠ b i)) :=
      U.toFilter.inter_mem hhit hmiss
    -- the intersection is empty: at any i in it, f(x i) = b i AND f(x i) ≠ b i.
    obtain ⟨i, hi, hmissi⟩ := U.toFilter.mem_nonempty hcap
    exact hmissi (x i) hi

/-- `map f U` is surjective if `f i` is surjective for a `U`-large set of `i`.  (Choose a preimage at
    each large coordinate; default elsewhere — needs a section `d : ∀ i, X i`.) -/
theorem map_surjective (f : ∀ i, X i → Y i) (U : Ultrafilter I) (d : ∀ i, X i)
    (hsurj : U.toFilter.sets (fun i => Function.Surjective (f i))) :
    Function.Surjective (map f U) := by
  classical
  refine fun q => ?_
  induction q using ind with
  | _ y =>
    -- pick a preimage of y i where f i is surjective, default to d i otherwise.
    refine ⟨mk U (fun i => if h : Function.Surjective (f i) then (h (y i)).choose else d i), ?_⟩
    have hmk : (mk U (liftSection f (fun i => if h : Function.Surjective (f i) then
            (h (y i)).choose else d i)) = mk U y) ↔
        U.toFilter.sets (agree (liftSection f (fun i => if h : Function.Surjective (f i) then
            (h (y i)).choose else d i)) y) :=
      ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
    rw [map_mk, hmk]
    refine U.toFilter.up_closed hsurj (fun i hi => ?_)
    simp only [agree, liftSection, dif_pos hi]
    exact (hi (y i)).choose_spec

/-! ## Hand-off to Phase D (assembling `Tᶠ : 𝒞 → 𝒮`)

Phase D builds the faithful, properness-preserving §1.646 representation `Tᶠ : 𝒞 → 𝒮` from the finite
base case (`Freyd/FiniteSeparation.lean`) and this file:

* **Object part.**  Over the index `I := List (ProperSub 𝒞)` of finite sets of proper subobjects, the
  finite base gives `T_S : 𝒞 → 𝒮^|𝒞|` per `S ∈ I`; collapsing a coordinate gives `T_S : 𝒞 → 𝒮`, and
  `Tᶠ A := Ultraproduct (fun S => T_S A) U` for the ultrafilter `U ⊇ F₀` from
  `exists_ultrafilter_of_base` (Phase A).

* **Morphism part = `map`.**  A map `φ : A ⟶ B` gives the family `S ↦ T_S φ : T_S A → T_S B`, and
  `Tᶠ φ := Ultraproduct.map (fun S => T_S φ) U`.  Functoriality is `map_id` / `map_comp`.

* **Left-exactness.**  `prodEquiv` (products), `unitEquiv` (terminal) and `equalizerEquiv` (equalisers,
  hence pullbacks via the projection-equaliser presentation) supply the finite-limit preservation that
  `pullback_faithful_iff_preserves_properness` (§1.453) consumes.  `equalizerEquiv` needs a diagonal
  section `Diag`, available in the application because each relevant fibre has a global point.

* **Faithful + properness-preserving.**  For a proper mono `m : A' ↪ A`, every `S` containing `m`
  separates it (`finite_separation`): `T_S m` is injective and non-surjective.  The set of such `S` is
  the principal coideal of `{m}`, which lies in `F₀ ⊆ U`.  Then:
  - `map_injective` makes `Tᶠ m` injective (mono preserved) since `T_S m` is injective `U`-largely;
  - `map_not_surjective` (fed the missing-point family from the `U`-large non-surjectivity) makes
    `Tᶠ m` non-surjective, so `Tᶠ m` stays PROPER — the §1.645 "`%e(U) = ∅`" faithfulness.

  The only residual for Phase D is the categorical bookkeeping wiring `T_S`/`Diag`/coideal-membership
  into these signatures; the set-level ultra-product mathematics is complete and Sorry-free here. -/

end Ultraproduct

end Freyd.UF
