/-
  Freyd & Scedrov, *Categories and Allegories* — §2.16(14), SECOND PRESENTATION of the
  effective reflection `E` of `Rel(A)` (A = the category of assemblies, §2.153).

  Book text (the closing remark of §2.16(14)): "The category E may also be presented as
  the result of splitting all SYMMETRIC IDEMPOTENTS of the full subcategory of Rel(A) of
  those assemblies that have all caucuses equal (in other words, those assemblies that are
  simply SETS).  In fact, Rel(A) is itself the result of splitting all COREFLEXIVE
  morphisms of this full subcategory."

  The first presentation `E = Spl(Eq (Rel A)) = AsmEffReflection K` is built in
  `S2_16d`.  Here we supply the OBJECT-LEVEL bridge underlying the two presentations —
  the substantive mathematical content — reusing the repo's splitting-completion machinery
  (`SplObj`/`SplCorObj`/`SymIdem`, S2_16/S2_165) and the `Rel(C)` graph calculus (S2_111).

  ## Set-like assemblies
  An assembly is SET-LIKE ("simply a set", the image of `∇ : Set → A`) when all its
  caucuses are equal (`IsSetLike`).  Since every carrier point lies in some caucus
  (`carrier_mem`), that forces every caucus to be the whole carrier; `setLikeOf X` is the
  canonical such assembly on a set `X` (`(∇X)|ₙ = X`).

  ## The set-like cover of an arbitrary assembly (the DRY core)
  For any assembly `A`, the identity function `A → setLikeOf A.X` (=`∇|A|`) is a monic
  assembly morphism `idInto A` (tracked by the identity modulus, injective).  Its graph
  `ι = setGraph A : ⟨A⟩ ⟶ ⟨setLikeOf A.X⟩` in `Rel(A)` satisfies
      `ι ≫ ι° = 1_⟨A⟩`   (idInto A monic — §2.214 `relGraph_comp_recip_of_monic`),
  and `e_A := ι° ≫ ι` is a COREFLEXIVE symmetric idempotent on the SET-LIKE object
  `⟨setLikeOf A.X⟩` (simplicity of the graph map).  This single datum drives both
  presentations.

  ## Presentation B  (`Rel(A)` = coreflexive splitting of the set-like subcategory)
  `asm_iso_coreflexiveSplit_setLike`: every object `⟨A⟩` of `Rel(A)`, sat as `(⟨A⟩, 1)`,
  is ISOMORPHIC in the coreflexive splitting completion `SplCorObj (Rel A)` to the
  coreflexive split `(⟨setLikeOf A.X⟩, e_A)` of a SET-LIKE object.  (Iso legs `ι`, `ι°`.)

  ## Presentation A  (`E` = symmetric-idempotent splitting of the set-like subcategory)
  `effRefl_iso_symIdemSplit_setLike`: every object `⟨A, I⟩` of `E` (an equivalence
  relation `I` on an assembly `A`), sat as the `SplObj (Rel A)` object `(⟨A⟩, I)`, is
  ISOMORPHIC in `SplObj (Rel A)` to `(⟨setLikeOf A.X⟩, g)`, where `g := ι° ≫ I ≫ ι` is a
  SYMMETRIC IDEMPOTENT (a partial equivalence relation, not necessarily reflexive) on the
  SET-LIKE object.  (Iso legs `I ≫ ι`, `ι° ≫ I`.)

  ## Scope
  Both presentations are given as the OBJECT/iso-level correspondence (every object of the
  target is an idempotent-split of a set-like object, hole-free).  The full categorical
  equivalence `E ≃ Spl(SymIdem 𝒮)` / `Rel(A) ≃ Spl(Coreflexive 𝒮)` — with the sub-allegory
  `𝒮` of set-like objects as a standalone type and the comparison functors + natural isos —
  is NOT built (it needs a full-sub-allegory construction not present in the repo); see the
  final note.  Working inside `SplObj/SplCorObj (Rel A)` — where objects of `E`, of
  `Rel(A)`, and of the two set-like splittings all coexist — the iso is exactly the content
  of the book's remark and avoids duplicating the completion machinery (DRY).

  Conventions: diagram-order `R ≫ S`, reciprocation `R°`, order `R ⊑ S`.  Mathlib-free.
-/
module

public import Freyd.S2_16d
public import Freyd.S2_111_RelCat

universe u

namespace Freyd.Alg.AsmTwo

open Cat DisjointGluing

variable (K : ModulusSystem)

/-! ## Set-like assemblies (`∇`-image: all caucuses equal) -/

/-- An assembly is SET-LIKE ("simply a set") when all its caucuses are equal.  Together
    with `carrier_mem` this forces each caucus to be the whole carrier — the image of the
    book's `∇ : Set → A`. -/
def IsSetLike (A : Assembly.{u} K) : Prop := ∀ m n x, A.caucus m x ↔ A.caucus n x

/-- The canonical set-like assembly on a set `X`: `(∇X)|ₙ = X` for every `n`. -/
def setLikeOf (X : Type u) : Assembly.{u} K := ⟨X, fun _ _ => True, fun _ => ⟨0, trivial⟩⟩

/-- `setLikeOf X` is set-like (every caucus is all of `X`). -/
theorem isSetLike_setLikeOf (X : Type u) : IsSetLike K (setLikeOf K X) :=
  fun _ _ _ => Iff.rfl

/-! ## The set-like cover `ι : ⟨A⟩ ⟶ ⟨setLikeOf A.X⟩` -/

/-- The identity function `A → setLikeOf A.X = ∇|A|` as an assembly morphism: tracked by the
    identity modulus (the target caucuses are trivially total). -/
def idInto (A : Assembly.{u} K) : A ⟶ setLikeOf K A.X :=
  ⟨fun x => x, ModFun.ident, K.id_mem, fun n _ _ => ⟨n, rfl, trivial⟩⟩

/-- The set-like cover `ι` of `A`: the graph of `idInto A` as a `Rel(A)`-relation
    `⟨A⟩ ⟶ ⟨setLikeOf A.X⟩`. -/
def setGraph (A : Assembly.{u} K) :
    (⟨A⟩ : RelObj (Assembly.{u} K)) ⟶ ⟨setLikeOf K A.X⟩ :=
  relGraph (idInto K A)

/-- **`ι ≫ ι° = 1_⟨A⟩`** (idInto A monic; §2.214 `relGraph_comp_recip_of_monic`).  `A` is a
    coreflexive-split of the set-like `setLikeOf A.X` — this is the crux of both
    presentations. -/
theorem setGraph_comp_recip (A : Assembly.{u} K) :
    setGraph K A ≫ (setGraph K A)° = Cat.id (⟨A⟩ : RelObj (Assembly.{u} K)) :=
  relGraph_comp_recip_of_monic (idInto K A) (asmMonic_of_injective _ (fun _ _ h => h))

/-- **`ι° ≫ ι ⊑ 1`** — `e_A := ι° ≫ ι` is coreflexive (the graph map `ι` is simple). -/
theorem setGraph_recip_comp_coreflexive (A : Assembly.{u} K) :
    Coreflexive ((setGraph K A)° ≫ setGraph K A) :=
  (relClass_graph_map (idInto K A)).2

/-- **`e_A ≫ e_A = e_A`** — `e_A := ι° ≫ ι` is idempotent (uses `ι ≫ ι° = 1`). -/
theorem setGraph_recip_comp_idem (A : Assembly.{u} K) :
    ((setGraph K A)° ≫ setGraph K A) ≫ ((setGraph K A)° ≫ setGraph K A)
      = (setGraph K A)° ≫ setGraph K A := by
  rw [Cat.assoc, ← Cat.assoc (setGraph K A) (setGraph K A)° (setGraph K A),
      setGraph_comp_recip, Cat.id_comp]

/-- The coreflexive symmetric idempotent `e_A := ι° ≫ ι` on the SET-LIKE object
    `⟨setLikeOf A.X⟩` whose split (in `SplCorObj`) is `⟨A⟩`. -/
def setIdem (A : Assembly.{u} K) : SymIdem (⟨setLikeOf K A.X⟩ : RelObj (Assembly.{u} K)) where
  e := (setGraph K A)° ≫ setGraph K A
  sym := by rw [Allegory.recip_comp, Allegory.recip_recip]
  idem := setGraph_recip_comp_idem K A

/-! ## Presentation B — `Rel(A)` = coreflexive splitting of the set-like subcategory

  Every object `⟨A⟩` of `Rel(A)`, placed in the coreflexive splitting completion
  `SplCorObj (Rel A)` as `(⟨A⟩, 1)`, is ISOMORPHIC to the coreflexive split
  `(⟨setLikeOf A.X⟩, e_A)` of a SET-LIKE object.  The iso legs are `ι` and `ι°`. -/

/-- `⟨A⟩` as the identity object `(⟨A⟩, 1)` of the coreflexive splitting `SplCorObj (Rel A)`. -/
def bObjA (A : Assembly.{u} K) : SplCorObj (RelObj (Assembly.{u} K)) :=
  ⟨⟨⟨A⟩, ⟨Cat.id (⟨A⟩ : RelObj (Assembly.{u} K)), recip_id, Cat.id_comp _⟩⟩, le_refl _⟩

/-- The coreflexive split `(⟨setLikeOf A.X⟩, e_A)` of the SET-LIKE object `⟨setLikeOf A.X⟩`. -/
def bObjS (A : Assembly.{u} K) : SplCorObj (RelObj (Assembly.{u} K)) :=
  ⟨⟨⟨setLikeOf K A.X⟩, setIdem K A⟩, setGraph_recip_comp_coreflexive K A⟩

/-- **§2.16(14), presentation B (object level)**: in the coreflexive splitting completion
    `SplCorObj (Rel A)`, every `⟨A⟩` (as `(⟨A⟩, 1)`) is ISOMORPHIC to the coreflexive split
    `(⟨setLikeOf A.X⟩, e_A)` of a set-like object — the content of "Rel(A) is itself the
    result of splitting all coreflexive morphisms of the set-like subcategory".  Iso legs
    `ι = setGraph A` and `ι°`. -/
theorem asm_iso_coreflexiveSplit_setLike (A : Assembly.{u} K) :
    ∃ (i : bObjA K A ⟶ bObjS K A) (j : bObjS K A ⟶ bObjA K A),
      i ≫ j = Cat.id (bObjA K A) ∧ j ≫ i = Cat.id (bObjS K A) := by
  refine ⟨⟨setGraph K A, ?_⟩, ⟨(setGraph K A)°, ?_⟩, ?_, ?_⟩
  · show Cat.id (⟨A⟩ : RelObj (Assembly.{u} K)) ≫ setGraph K A ≫
        ((setGraph K A)° ≫ setGraph K A) = setGraph K A
    rw [Cat.id_comp, ← Cat.assoc, setGraph_comp_recip, Cat.id_comp]
  · show ((setGraph K A)° ≫ setGraph K A) ≫ (setGraph K A)° ≫
        Cat.id (⟨A⟩ : RelObj (Assembly.{u} K)) = (setGraph K A)°
    rw [Cat.comp_id, Cat.assoc, setGraph_comp_recip, Cat.comp_id]
  · apply SplHom.ext
    show setGraph K A ≫ (setGraph K A)° = Cat.id (⟨A⟩ : RelObj (Assembly.{u} K))
    exact setGraph_comp_recip K A
  · exact SplHom.ext rfl

/-! ## Conjugation by a partial iso in the splitting completion (the DRY core of both)

  Generic to any allegory: if `ι : a ⟶ s` is a partial iso onto `a`
  (`ι ≫ ι° = 1_a`) and `I` is a symmetric idempotent on `a`, then `g := ι° ≫ I ≫ ι`
  is a symmetric idempotent on `s`, and the two split objects `(a, I)` and `(s, g)` are
  ISOMORPHIC in `SplObj 𝒜`, with legs `I ≫ ι` and `ι° ≫ I`.  (`ι = setGraph A`,
  `s = setLikeOf A.X` set-like gives presentation A; `I = 1_a` recovers `e_A`.) -/

section Conjugation
variable {𝒜 : Type u} [Allegory 𝒜]

/-- `g := ι° ≫ I ≫ ι` is a symmetric idempotent on `s` when `ι ≫ ι° = 1_a` and `I` is a
    symmetric idempotent on `a` (the transport of `I` along the partial iso `ι`). -/
def symIdemConj {a s : 𝒜} (ι : a ⟶ s) (hι : ι ≫ ι° = Cat.id a)
    (I : a ⟶ a) (hIsym : I° = I) (hIidem : I ≫ I = I) : SymIdem s where
  e := ι° ≫ I ≫ ι
  sym := by
    rw [Allegory.recip_comp, Allegory.recip_comp, Allegory.recip_recip, hIsym, Cat.assoc]
  idem := by
    calc (ι° ≫ I ≫ ι) ≫ (ι° ≫ I ≫ ι)
        = ι° ≫ I ≫ (ι ≫ ι°) ≫ I ≫ ι := by simp only [Cat.assoc]
      _ = ι° ≫ I ≫ Cat.id a ≫ I ≫ ι := by rw [hι]
      _ = ι° ≫ I ≫ I ≫ ι := by rw [Cat.id_comp]
      _ = ι° ≫ (I ≫ I) ≫ ι := by rw [Cat.assoc]
      _ = ι° ≫ I ≫ ι := by rw [hIidem]

/-- **The conjugation isomorphism** `(a, I) ≅ (s, ι° ≫ I ≫ ι)` in `SplObj 𝒜`.  Legs
    `i = I ≫ ι` and `j = ι° ≫ I`; `i ≫ j = I = id_{(a,I)}`, `j ≫ i = ι° ≫ I ≫ ι = id`. -/
theorem splObj_conj_iso {a s : 𝒜} (ι : a ⟶ s) (hι : ι ≫ ι° = Cat.id a)
    (I : a ⟶ a) (hIsym : I° = I) (hIidem : I ≫ I = I) :
    ∃ (i : (⟨a, ⟨I, hIsym, hIidem⟩⟩ : SplObj 𝒜) ⟶ ⟨s, symIdemConj ι hι I hIsym hIidem⟩)
      (j : (⟨s, symIdemConj ι hι I hIsym hIidem⟩ : SplObj 𝒜) ⟶ ⟨a, ⟨I, hIsym, hIidem⟩⟩),
      i ≫ j = Cat.id (⟨a, ⟨I, hIsym, hIidem⟩⟩ : SplObj 𝒜) ∧
      j ≫ i = Cat.id (⟨s, symIdemConj ι hι I hIsym hIidem⟩ : SplObj 𝒜) := by
  refine ⟨⟨I ≫ ι, ?_⟩, ⟨ι° ≫ I, ?_⟩, ?_, ?_⟩
  · -- fixed i: I ≫ (I ≫ ι) ≫ (ι° ≫ I ≫ ι) = I ≫ ι
    show I ≫ (I ≫ ι) ≫ (ι° ≫ I ≫ ι) = I ≫ ι
    calc I ≫ (I ≫ ι) ≫ (ι° ≫ I ≫ ι)
        = (I ≫ I) ≫ (ι ≫ ι°) ≫ I ≫ ι := by simp only [Cat.assoc]
      _ = (I ≫ I) ≫ Cat.id a ≫ I ≫ ι := by rw [hι]
      _ = (I ≫ I) ≫ (I ≫ ι) := by rw [Cat.id_comp]
      _ = I ≫ ι := by rw [hIidem, ← Cat.assoc, hIidem]
  · -- fixed j: (ι° ≫ I ≫ ι) ≫ (ι° ≫ I) ≫ I = ι° ≫ I
    show (ι° ≫ I ≫ ι) ≫ (ι° ≫ I) ≫ I = ι° ≫ I
    calc (ι° ≫ I ≫ ι) ≫ (ι° ≫ I) ≫ I
        = ι° ≫ I ≫ (ι ≫ ι°) ≫ I ≫ I := by simp only [Cat.assoc]
      _ = ι° ≫ I ≫ Cat.id a ≫ I ≫ I := by rw [hι]
      _ = ι° ≫ I ≫ I ≫ I := by rw [Cat.id_comp]
      _ = ι° ≫ I := by rw [hIidem, hIidem]
  · -- i ≫ j = id_{(a,I)}: (I ≫ ι) ≫ (ι° ≫ I) = I
    apply SplHom.ext
    show (I ≫ ι) ≫ (ι° ≫ I) = I
    calc (I ≫ ι) ≫ (ι° ≫ I)
        = I ≫ (ι ≫ ι°) ≫ I := by simp only [Cat.assoc]
      _ = I ≫ Cat.id a ≫ I := by rw [hι]
      _ = I ≫ I := by rw [Cat.id_comp]
      _ = I := hIidem
  · -- j ≫ i = id_{(s,g)}: (ι° ≫ I) ≫ (I ≫ ι) = ι° ≫ I ≫ ι
    apply SplHom.ext
    show (ι° ≫ I) ≫ (I ≫ ι) = ι° ≫ I ≫ ι
    calc (ι° ≫ I) ≫ (I ≫ ι)
        = ι° ≫ (I ≫ I) ≫ ι := by simp only [Cat.assoc]
      _ = ι° ≫ I ≫ ι := by rw [hIidem]

end Conjugation

/-! ## Presentation A — `E` = symmetric-idempotent splitting of the set-like subcategory

  Every object `⟨A, I⟩` of the effective reflection `E` (an equivalence relation `I` on an
  assembly `A`), placed in `SplObj (Rel A)` as `(⟨A⟩, I)`, is ISOMORPHIC to
  `(⟨setLikeOf A.X⟩, ι° ≫ I ≫ ι)`, a symmetric-idempotent split of a SET-LIKE object.
  This is the content of "E may be presented as the result of splitting all symmetric
  idempotents of the set-like subcategory". -/

/-- The symmetric idempotent `g := ι° ≫ I ≫ ι` on the SET-LIKE object, transporting the
    equivalence relation `I` of an `E`-object along the set-like cover `ι = setGraph A`. -/
def effIdem (A : Assembly.{u} K) (I : (⟨A⟩ : RelObj (Assembly.{u} K)) ⟶ ⟨A⟩)
    (hsym : I° = I) (hidem : I ≫ I = I) :
    SymIdem (⟨setLikeOf K A.X⟩ : RelObj (Assembly.{u} K)) :=
  symIdemConj (setGraph K A) (setGraph_comp_recip K A) I hsym hidem

/-- **§2.16(14), presentation A (object level)**: the object `⟨A, I⟩` of `E` (as the
    `SplObj (Rel A)` object `(⟨A⟩, I)`) is ISOMORPHIC in `SplObj (Rel A)` to
    `(⟨setLikeOf A.X⟩, g)`, a SYMMETRIC-IDEMPOTENT split of a set-like object.  Iso legs
    `I ≫ ι` and `ι° ≫ I`.  Instance of `splObj_conj_iso` at the set-like cover `ι`. -/
theorem effRefl_iso_symIdemSplit_setLike (A : Assembly.{u} K)
    (I : (⟨A⟩ : RelObj (Assembly.{u} K)) ⟶ ⟨A⟩) (hsym : I° = I) (hidem : I ≫ I = I) :
    ∃ (i : (⟨⟨A⟩, ⟨I, hsym, hidem⟩⟩ : SplObj (RelObj (Assembly.{u} K)))
            ⟶ ⟨⟨setLikeOf K A.X⟩, effIdem K A I hsym hidem⟩)
      (j : (⟨⟨setLikeOf K A.X⟩, effIdem K A I hsym hidem⟩ : SplObj (RelObj (Assembly.{u} K)))
            ⟶ ⟨⟨A⟩, ⟨I, hsym, hidem⟩⟩),
      i ≫ j = Cat.id (⟨⟨A⟩, ⟨I, hsym, hidem⟩⟩ : SplObj (RelObj (Assembly.{u} K))) ∧
      j ≫ i = Cat.id (⟨⟨setLikeOf K A.X⟩, effIdem K A I hsym hidem⟩
                        : SplObj (RelObj (Assembly.{u} K))) :=
  splObj_conj_iso (setGraph K A) (setGraph_comp_recip K A) I hsym hidem

/-- **§2.16(14), presentation A packaged for the book's `E`**: the same iso stated for a
    genuine object `EO` of the effective reflection `E = AsmEffReflection K` (extracting its
    underlying assembly and equivalence relation via `asmEffReflection_obj_form`). -/
theorem effReflObj_iso_symIdemSplit_setLike (EO : AsmEffReflection.{u} K) :
    ∃ (A : Assembly.{u} K) (I : (⟨A⟩ : RelObj (Assembly.{u} K)) ⟶ ⟨A⟩)
      (hsym : I° = I) (hidem : I ≫ I = I)
      (i : (⟨⟨A⟩, ⟨I, hsym, hidem⟩⟩ : SplObj (RelObj (Assembly.{u} K)))
            ⟶ ⟨⟨setLikeOf K A.X⟩, effIdem K A I hsym hidem⟩)
      (j : (⟨⟨setLikeOf K A.X⟩, effIdem K A I hsym hidem⟩ : SplObj (RelObj (Assembly.{u} K)))
            ⟶ ⟨⟨A⟩, ⟨I, hsym, hidem⟩⟩),
      i ≫ j = Cat.id (⟨⟨A⟩, ⟨I, hsym, hidem⟩⟩ : SplObj (RelObj (Assembly.{u} K))) ∧
      j ≫ i = Cat.id (⟨⟨setLikeOf K A.X⟩, effIdem K A I hsym hidem⟩
                        : SplObj (RelObj (Assembly.{u} K))) := by
  obtain ⟨A, I, hrefl, hsym, htrans, _⟩ := asmEffReflection_obj_form K EO
  obtain ⟨i, j, hij, hji⟩ := splObj_conj_iso (setGraph K A) (setGraph_comp_recip K A) I
    (symmetric_eq hsym) (reflexive_transitive_idempotent hrefl htrans)
  exact ⟨A, I, symmetric_eq hsym, reflexive_transitive_idempotent hrefl htrans, i, j, hij, hji⟩

end Freyd.Alg.AsmTwo
