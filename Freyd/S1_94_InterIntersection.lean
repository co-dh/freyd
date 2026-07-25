/-
  Freyd & Scedrov, *Categories and Allegories* §1.94 — NAME OF A SUBOBJECT and the
  INTERNALLY DEFINED INTERSECTION ∩F (the power-object / classifier core of §1.94).

  ## Why this file exists (import-architecture)

  These definitions (`powObj`, `nameOf`, `NamedBy`, `membershipMap`, `interIntersection`
  and the β/η-law lemma cluster around them) depend ONLY on the power-object /
  subobject-classifier machinery of `S1_9`/`S1_92`, which sit UPSTREAM of `S1_94`.

  They used to live in `S1_94.lean`, but `S1_94` is also where the §1.94 chapter
  theorems (`topos_is_regular`, `topos_is_logos`, …) are *stated*, and those theorems
  need the (Sorry-free) topos-regularity instances built downstream in
  `InternalForallTopos` (`toposHasImages`, `topos_is_regular_real`).  Since
  `InternalForallTopos` itself *consumes* `nameOf`/`membershipMap`/`interIntersection`
  (it builds the internal-∀ `forallC`/`bigInter` from them), keeping the cluster in
  `S1_94` created the cycle

      S1_94 → InternalForall → InternalForallTopos → S1_94.

  Relocating the cluster to this upstream file breaks the cycle: both `S1_94` (which
  re-exports it) and `InternalForallTopos` import `InterIntersection` instead, and
  neither imports the other through it.  The definitions are byte-identical to the
  originals — this is a pure mechanical move, no statement or proof changed.
-/

import Freyd.S1_90
import Freyd.S1_92
import Freyd.S1_60

universe v u

namespace Freyd

open HasSubobjectClassifier

variable {𝒞 : Type u} [Cat.{v} 𝒞] [Topos 𝒞]

/-! ## §1.94  Power object [A] and families named by F

  In a topos the POWER OBJECT [A] is the exponential Ω^A (§1.92).
  A subobject A' ↣ A is NAMED BY F ⊆ [A] if its name 'A'' ≤ F (§1.942). -/

/-- The POWER OBJECT [A] = Ω^A (§1.92). -/
noncomputable abbrev powObj (A : 𝒞) : 𝒞 := omega (𝒞 := 𝒞) ^^ A

/-! ## §1.942  Name of a subobject

  For A' ↣ A with characteristic map χ_{A'} : A → Ω, the NAME OF A',
  written 'A'', is curry(χ_{A'}) : 1 → Ω^A = [A].  The adjunction
  prod A 1 ≅ A → Ω^A gives 'A'' = curry(fst ≫ χ_{A'}) : 1 → [A]. -/

/-- The NAME 'A'' : 1 → [A] of the monic m : A' → A (§1.942).
    curry(fst ≫ χ_m) : one → Ω^A, where fst : prod A one → A. -/
noncomputable def nameOf {A A' : 𝒞} (m : A' ⟶ A) (hm : Monic m) : one ⟶ powObj A :=
  curry (fst ≫ classify m hm)

/-- A' is NAMED BY F ⊆ [A] if 'A'' ∈ F, i.e. 'A'' factors through F (§1.942). -/
def NamedBy {A : 𝒞} (A' : Subobject 𝒞 A) (F : Subobject 𝒞 (powObj A)) : Prop :=
  ∃ h : one ⟶ F.dom, h ≫ F.arr = nameOf A'.arr A'.monic

/-! ## §1.94  Internally defined intersection ∩F

  The construction from the book: pull back `true : 1 → Ω` along the
  membership evaluation map A → Ω induced by F.  When F ⊆ [A] is presented
  as a subobject F ↣ [A], its "adjoint" 1 → [[A]] is its name.  For the
  case where F is given by a global element `F_name : 1 → [A]` (i.e. F
  is the singleton subobject of [A] containing F_name), the membership map is

      A ──pair(id,term≫F_name)──→ A × [A] ──eval──→ Ω.

  and ∩F is the pullback of true along this map. -/

/-- The membership test A → Ω for a global element F_name : 1 → [A].
    Evaluates F_name at each a : A via `eval ∘ ⟨id_A, term_A ≫ F_name⟩`. -/
noncomputable def membershipMap {A : 𝒞} (F_name : one ⟶ powObj A) : A ⟶ omega (𝒞 := 𝒞) :=
  pair (Cat.id A) (term A ≫ F_name) ≫ eval_exp A (omega (𝒞 := 𝒞))

/-- **§1.94**: INTERNALLY DEFINED INTERSECTION ∩F for a global element F_name : 1 → [A].
    Constructed as the pullback of true : 1 → Ω along membershipMap F_name. -/
noncomputable def interIntersection {A : 𝒞} (F_name : one ⟶ powObj A) : Subobject 𝒞 A :=
  InverseImage (membershipMap F_name) ⟨one, true (𝒞 := 𝒞), HasSubobjectClassifier.true_monic⟩

/-! ## §1.943  ∩F is a lower bound; glb when F is well-pointed -/

/-- **§1.942/§1.94 β-law**: evaluating the NAME 'A'' at a point reconstructs the
    characteristic map.  Concretely the membership test of `nameOf m hm` equals
    the classifier `χ_m`: `membershipMap (nameOf m hm) = classify m hm`.

    Proof: `nameOf m hm = curry(fst ≫ χ_m)`; the membership map factors as
    `pair id (term) ≫ prodMap (curry …) ≫ eval`, and `curry_eval` collapses the
    `prodMap … ≫ eval` to `fst ≫ χ_m`, then `fst (pair id term) = id`. -/
theorem membershipMap_nameOf {A A' : 𝒞} (m : A' ⟶ A) (hm : Monic m) :
    membershipMap (nameOf m hm) = HasSubobjectClassifier.classify m hm := by
  show pair (Cat.id A) (term A ≫ nameOf m hm) ≫ eval_exp A (omega (𝒞 := 𝒞))
      = HasSubobjectClassifier.classify m hm
  -- pair id (term ≫ N) = pair id term ≫ prodMap A one (Ω^A) N
  have hfactor : pair (Cat.id A) (term A ≫ nameOf m hm)
      = pair (Cat.id A) (term A) ≫ prodMap A one (omega (𝒞 := 𝒞) ^^ A) (nameOf m hm) :=
    (pair_uniq _ _ _
      (by rw [Cat.assoc, prodMap_fst, fst_pair])
      (by rw [Cat.assoc, prodMap_snd, ← Cat.assoc, snd_pair])).symm
  rw [hfactor, Cat.assoc]
  -- prodMap A one _ (curry (fst ≫ χ_m)) ≫ eval = fst ≫ χ_m
  show pair (Cat.id A) (term A) ≫
      (prodMap A one (omega (𝒞 := 𝒞) ^^ A) (curry (fst ≫ HasSubobjectClassifier.classify m hm))
        ≫ eval_exp A (omega (𝒞 := 𝒞))) = _
  rw [curry_eval_eq, ← Cat.assoc, fst_pair, Cat.id_comp]

/-- **§1.943** (part 1): ∩F is below every subobject A' named by F.
    For A' ↣ A with 'A'' ∈ F_name (i.e. nameOf A'.arr A'.monic = F_name),
    we have ∩F ≤ A'.

    Proof (§1.943): 'A'' ∈ F means the membership map for A' factors through
    true : 1 → Ω, so ∩F = pullback(true along membershipMap) ≤ A'. -/
theorem inter_le_named {A : 𝒞} (F_name : one ⟶ powObj A)
    (A' : Subobject 𝒞 A)
    (hA' : nameOf A'.arr A'.monic = F_name) :
    Subobject.le (interIntersection F_name) A' := by
  -- membershipMap F_name = χ_{A'} = classify A'.arr A'.monic
  have hχ : membershipMap F_name = HasSubobjectClassifier.classify A'.arr A'.monic := by
    rw [← hA', membershipMap_nameOf]
  -- ∩F = inverse image of {true} along membershipMap F_name; its arr is π₁ of the
  -- canonical pullback `pb` over the cospan (membershipMap F_name, true).
  let pb := HasPullbacks.has (membershipMap F_name) (HasSubobjectClassifier.true (𝒞 := 𝒞))
  -- A' is the pullback of `true` along χ_{A'} (classify_pullback); use its universal
  -- property to lift pb.cone, getting u : pb.cone.pt → A' with u ≫ A'.arr = pb.cone.π₁.
  have hpbA' := HasSubobjectClassifier.classify_pullback A'.arr A'.monic
  -- pb.cone is a cone over (χ_{A'}, true) after rewriting membershipMap F_name = χ_{A'}.
  have hsq : pb.cone.π₁ ≫ HasSubobjectClassifier.classify A'.arr A'.monic
      = pb.cone.π₂ ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
    rw [← hχ]; exact pb.cone.w
  obtain ⟨u, ⟨hu₁, _⟩, _⟩ :=
    hpbA' ⟨pb.cone.pt, pb.cone.π₁, pb.cone.π₂, hsq⟩
  exact ⟨u, hu₁⟩

/-- **§1.94 η-law** (name reconstruction): the curry of `fst ≫ membershipMap G`
    is `G` itself.  This is the inverse to the β-law `membershipMap_nameOf`: a
    global element `G : 1 → [A]` is recovered from its membership test.

    Proof: `fst ≫ membershipMap G = pair fst (snd ≫ G) ≫ eval = prodMap A one [A] G ≫ eval`
    (using `fst ≫ term A = snd` by terminal-uniqueness), so `curry_unique_eq` gives `= G`. -/
theorem curry_fst_membershipMap {A : 𝒞} (G : one ⟶ powObj A) :
    curry (fst (A := A) (B := one) ≫ membershipMap G) = G := by
  symm
  apply curry_unique_eq
  -- prodMap A one [A] G ≫ eval = fst ≫ membershipMap G
  show prodMap A one (omega (𝒞 := 𝒞) ^^ A) G ≫ eval_exp A (omega (𝒞 := 𝒞))
      = fst ≫ (pair (Cat.id A) (term A ≫ G) ≫ eval_exp A (omega (𝒞 := 𝒞)))
  -- fst ≫ pair id (term≫G) = pair fst (fst ≫ term ≫ G) = pair fst (snd ≫ G) = prodMap A one [A] G
  have hpair : fst (A := A) (B := one) ≫ pair (Cat.id A) (term A ≫ G)
      = prodMap A one (omega (𝒞 := 𝒞) ^^ A) G := by
    dsimp only [prodMap]
    apply pair_uniq _ _ _ ?_ ?_
    · rw [Cat.assoc, fst_pair, Cat.comp_id]
    · rw [Cat.assoc, snd_pair, ← Cat.assoc,
        term_uniq (fst (A := A) (B := one) ≫ term A) (snd (A := A) (B := one))]
  rw [← Cat.assoc, hpair]

/-- **§1.94**: the membership map `membershipMap G` classifies `interIntersection G`.
    Since `interIntersection G = InverseImage (membershipMap G) {true}` is the pullback
    of `true` along `membershipMap G`, the classifier-uniqueness gives
    `classify (∩G).arr = membershipMap G`. -/
theorem classify_interIntersection {A : 𝒞} (G : one ⟶ powObj A) :
    HasSubobjectClassifier.classify (interIntersection G).arr (interIntersection G).monic
      = membershipMap G := by
  symm
  -- pb = pullback of (membershipMap G, true); (∩G).arr = pb.cone.π₁, (∩G).dom = pb.cone.pt.
  let pb := HasPullbacks.has (membershipMap G) (HasSubobjectClassifier.true (𝒞 := 𝒞))
  -- the cone square gives  (∩G).arr ≫ membershipMap G = π₂ ≫ true = term ≫ true.
  have hsq : (interIntersection G).arr ≫ membershipMap G
      = term (interIntersection G).dom ≫ HasSubobjectClassifier.true (𝒞 := 𝒞) := by
    show pb.cone.π₁ ≫ membershipMap G = _
    rw [pb.cone.w]; congr 1; exact term_uniq _ _
  apply HasSubobjectClassifier.classify_unique (interIntersection G).arr (interIntersection G).monic
    (membershipMap G) hsq
  -- the inverse-image pullback cone IS a pullback (over (membershipMap G, true)).
  intro d
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := pb.cone_isPullback d
  refine ⟨u, ⟨hu₁, term_uniq _ _⟩, fun v hv₁ _ => huniq v hv₁ (term_uniq _ _)⟩

/-- **§1.94**: the NAME of `interIntersection G` is `G` itself.
    `nameOf (∩G).arr = curry(fst ≫ χ_{∩G}) = curry(fst ≫ membershipMap G) = G`
    (by `classify_interIntersection` then `curry_fst_membershipMap`). -/
theorem nameOf_interIntersection {A : 𝒞} (G : one ⟶ powObj A) :
    nameOf (interIntersection G).arr (interIntersection G).monic = G := by
  show curry (fst ≫ HasSubobjectClassifier.classify (interIntersection G).arr
      (interIntersection G).monic) = G
  rw [classify_interIntersection, curry_fst_membershipMap]

/-- **§1.943** (part 2, singleton lower-bound — NOT the full glb): for every point
    `x : 1 → F.dom`, the singleton intersection `∩{x ≫ F.arr}` is itself a subobject
    NAMED by F (its name is `x ≫ F.arr`, witnessed by `x`).  Hence any `L` that sits
    below every F-named subobject (`hL`) sits below `∩{x ≫ F.arr}` in particular.

    INTEGRITY NOTE: this is deliberately *not* called `inter_is_glb`.  The genuine glb
    claim "`L ≤ ⋂F`" of §1.943 ranges over the whole family `F ↣ [A]`, whereas
    `interIntersection` takes a *single* global name `1 → [A]` (a singleton family).
    There is no `⋂F`-over-a-subobject-family construction in this file, so the real glb
    cannot even be *stated* here; it needs the §1.543 capitalization lemma plus the
    contravariant power functor `Ω^(−)` carrying the jointly-epic point family of F to a
    jointly-monic family.  What is proved here is exactly the per-singleton bound, and
    the name now says so.  `hL` IS used; the old unused `WellPointed F.dom` hypothesis is
    dropped since the per-singleton statement does not need it.

    Proof: for each point `x : 1 → F.dom`, `interIntersection (x ≫ F.arr)` is named by F
    via `nameOf_interIntersection`, witnessed by the point `x`; apply `hL`. -/
theorem inter_le_singleton_named {A : 𝒞} (F : Subobject 𝒞 (powObj A))
    (L : Subobject 𝒞 A)
    (hL : ∀ A' : Subobject 𝒞 A, NamedBy A' F → Subobject.le L A') :
    ∀ x : one ⟶ F.dom,
        Subobject.le L (interIntersection (x ≫ F.arr)) := by
  intro x
  -- ∩(x ≫ F.arr) is named by F: its name is x ≫ F.arr, witnessed by the point x.
  apply hL
  exact ⟨x, by rw [nameOf_interIntersection]⟩

/-! ## §1.94(10)  The singleton map A1 : A → [A] -/

/-- **§1.94(10)**: The SINGLETON MAP A1 : A → [A] = Ω^A sends a : A to its name
    'a'' = {a}.  It is `curry(χ_{Δ_A})`, the curried classifier of the diagonal —
    exactly the §1.92 `singletonMapCat`, reused here (DRY). -/
noncomputable def singletonMap (A : 𝒞) : A ⟶ powObj A :=
  singletonMapCat (𝒞 := 𝒞) A

/-- **§1.94(10)**: the singleton map is monic (§1.92, reuse of `singletonMapCat_monic`). -/
theorem singletonMap_monic (A : 𝒞) : Monic (singletonMap A) :=
  singletonMapCat_monic (𝒞 := 𝒞) A

end Freyd
