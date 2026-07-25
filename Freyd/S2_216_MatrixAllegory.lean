/-
  Freyd & Scedrov, *Categories and Allegories* §2.216 / §2.342
  MATRIX ALLEGORY  Mat 𝒜  over a distributive allegory 𝒜.

  Objects  = Fin-n-indexed families of 𝒜-objects  (MatObj 𝒜).
  Morphisms = n×m matrices of base morphisms       (MatHom X Y).

  No Finset/Fintype/LinearOrder from Std — uses only List, Fin n, List.ofFn.
-/

import Freyd.S1_1
import Freyd.S2_10
import Freyd.S2_20
import Freyd.S2_30

universe v u

open Freyd Freyd.Alg

namespace Freyd.Alg.Mat

/-! ## §A  List-based finite join  in a distributive allegory

  `listJoin' l` = fold of `∪` right-to-left with unit `𝟘`. -/

section ListJoin

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

def listJoin' {a b : 𝒜} : List (a ⟶ b) → a ⟶ b
  | []      => 𝟘
  | x :: xs => x ∪ listJoin' xs

@[simp] theorem listJoin'_nil  {a b : 𝒜} : listJoin' ([] : List (a ⟶ b)) = 𝟘 := rfl
@[simp] theorem listJoin'_cons {a b : 𝒜} (x : a ⟶ b) (xs : List (a ⟶ b)) :
    listJoin' (x :: xs) = x ∪ listJoin' xs := rfl

theorem le_listJoin' {a b : 𝒜} {x : a ⟶ b} {l : List (a ⟶ b)} (hx : x ∈ l) :
    x ⊑ listJoin' l := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    simp only [listJoin'_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact le_union_left x _
    · exact le_trans (ih hmem) (le_union_right _ _)

theorem listJoin'_le {a b : 𝒜} {l : List (a ⟶ b)} {T : a ⟶ b}
    (h : ∀ x ∈ l, x ⊑ T) : listJoin' l ⊑ T := by
  induction l with
  | nil => exact zero_le T
  | cons y ys ih =>
    simp only [listJoin'_cons]
    exact union_lub (h y List.mem_cons_self)
      (ih (fun x hx => h x (List.mem_cons_of_mem y hx)))

/-- `finJoin f = ⨆_{i : Fin n} f i`. -/
def finJoin {a b : 𝒜} {n : Nat} (f : Fin n → (a ⟶ b)) : a ⟶ b :=
  listJoin' (List.ofFn f)

theorem finJoin_mono {a b : 𝒜} {n : Nat} {f g : Fin n → (a ⟶ b)}
    (h : ∀ i, f i ⊑ g i) : finJoin f ⊑ finJoin g :=
  listJoin'_le (fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact le_trans (h i) (show g i ⊑ finJoin g from le_listJoin' (List.mem_ofFn.mpr ⟨i, rfl⟩)))

theorem comp_finJoin {a b c : 𝒜} {n : Nat} (R : a ⟶ b) (f : Fin n → (b ⟶ c)) :
    R ≫ finJoin f = finJoin (fun j => R ≫ f j) := by
  simp only [finJoin]
  induction n with
  | zero => simp [List.ofFn_zero, DistributiveAllegory.comp_zero]
  | succ n ih =>
    simp only [List.ofFn_succ, listJoin'_cons, DistributiveAllegory.comp_union_distrib]
    congr 1; exact ih (fun i => f i.succ)

theorem finJoin_comp {a b c : 𝒜} {n : Nat} (f : Fin n → (a ⟶ b)) (R : b ⟶ c) :
    finJoin f ≫ R = finJoin (fun j => f j ≫ R) := by
  simp only [finJoin]
  induction n with
  | zero => simp [List.ofFn_zero, DistributiveAllegory.zero_comp]
  | succ n ih =>
    simp only [List.ofFn_succ, listJoin'_cons, union_comp_distrib]
    congr 1; exact ih (fun i => f i.succ)

theorem recip_finJoin {a b : 𝒜} {n : Nat} (f : Fin n → (a ⟶ b)) :
    (finJoin f)° = finJoin (fun j => (f j)°) := by
  apply le_antisymm
  · rw [recip_le_iff]
    refine listJoin'_le (fun x hx => ?_); obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    rw [← recip_le_iff]
    exact show (fun j => (f j)°) j ⊑ finJoin (fun j => (f j)°) from le_listJoin' (List.mem_ofFn.mpr ⟨j, rfl⟩)
  · refine listJoin'_le (fun x hx => ?_); obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx; exact recip_mono (show f j ⊑ finJoin f from le_listJoin' (List.mem_ofFn.mpr ⟨j, rfl⟩))

theorem inter_finJoin {a b : 𝒜} {n : Nat} (T : a ⟶ b) (f : Fin n → (a ⟶ b)) :
    T ∩ finJoin f = finJoin (fun j => T ∩ f j) := by
  simp only [finJoin]
  induction n with
  | zero =>
    simp [List.ofFn_zero]
    exact le_antisymm (inter_lb_right T 𝟘) (le_inter (zero_le T) (le_refl 𝟘))
  | succ n ih =>
    simp only [List.ofFn_succ, listJoin'_cons]
    rw [DistributiveAllegory.inter_union_distrib]
    congr 1; exact ih (fun i => f i.succ)

end ListJoin

/-! ## §B  List-based finite meet  in an allegory

  `listMeet' (x :: xs)` = fold of `∩` over a nonempty list.
  We instantiate at `l = List.ofFn f` when n ≥ 1. -/

section ListMeet

variable {𝒜 : Type u} [Allegory 𝒜]

def listMeet' {a b : 𝒜} : (l : List (a ⟶ b)) → l ≠ [] → a ⟶ b
  | [x],            _  => x
  | x :: y :: rest, _  => x ∩ listMeet' (y :: rest) (List.cons_ne_nil y rest)

theorem listMeet'_singleton {a b : 𝒜} {x : a ⟶ b} (h : [x] ≠ []) :
    listMeet' [x] h = x := rfl

theorem listMeet'_cons_cons {a b : 𝒜} {x y : a ⟶ b} {rest : List (a ⟶ b)}
    (h : x :: y :: rest ≠ []) :
    listMeet' (x :: y :: rest) h = x ∩ listMeet' (y :: rest) (List.cons_ne_nil y rest) := rfl

theorem listMeet'_le {a b : 𝒜} (l : List (a ⟶ b)) (hne : l ≠ []) {x : a ⟶ b}
    (hx : x ∈ l) : listMeet' l hne ⊑ x := by
  induction l with
  | nil => exact absurd rfl hne
  | cons y ys ih =>
    rcases ys with _ | ⟨z, zs⟩
    · rcases List.mem_cons.mp hx with rfl | h
      · exact le_refl _
      · exact absurd h List.not_mem_nil
    · rw [listMeet'_cons_cons]
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact inter_lb_left _ _
      · exact le_trans (inter_lb_right _ _) (ih (List.cons_ne_nil z zs) hmem)

theorem le_listMeet' {a b : 𝒜} (l : List (a ⟶ b)) (hne : l ≠ []) {T : a ⟶ b}
    (h : ∀ x ∈ l, T ⊑ x) : T ⊑ listMeet' l hne := by
  induction l with
  | nil => exact absurd rfl hne
  | cons y ys ih =>
    rcases ys with _ | ⟨z, zs⟩
    · exact h y List.mem_cons_self
    · rw [listMeet'_cons_cons]
      exact le_inter (h y List.mem_cons_self)
        (ih (List.cons_ne_nil z zs) (fun x hx => h x (List.mem_cons_of_mem y hx)))

/-- `finMeet f = ⋀_{i : Fin (n+1)} f i`. -/
def finMeet {a b : 𝒜} {n : Nat} (f : Fin (n + 1) → (a ⟶ b)) : a ⟶ b :=
  listMeet' (List.ofFn f) (by rw [List.ofFn_succ]; exact List.cons_ne_nil _ _)

theorem le_finMeet {a b : 𝒜} {n : Nat} {f : Fin (n + 1) → (a ⟶ b)} {T : a ⟶ b}
    (h : ∀ i, T ⊑ f i) : T ⊑ finMeet f :=
  le_listMeet' _ _ (fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact h i)

end ListMeet

/-! ## §C  MatObj and MatHom -/

/-- An object of `Mat 𝒜`: a `Fin n`-indexed family of 𝒜-objects. -/
structure MatObj (𝒜 : Type u) where
  n    : Nat
  objs : Fin n → 𝒜

/-- Morphisms in `Mat 𝒜`: n×m matrices of 𝒜 morphisms. -/
abbrev MatHom [Cat.{v} 𝒜] (X Y : MatObj 𝒜) : Type v :=
  (i : Fin X.n) → (j : Fin Y.n) → X.objs i ⟶ Y.objs j

/-! ## §D  Category structure on MatObj 𝒜 -/

section MatCat

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

def matId (X : MatObj 𝒜) : MatHom X X :=
  fun i j => if h : i = j then (by subst h; exact Cat.id (X.objs i)) else 𝟘

/-- Diagonal entry of the matrix identity. -/
theorem matId_diag {X : MatObj 𝒜} (i : Fin X.n) : matId X i i = Cat.id (X.objs i) := by
  simp only [matId, ↓reduceDIte]

/-- Off-diagonal entry of the matrix identity. -/
theorem matId_off {X : MatObj 𝒜} {i i' : Fin X.n} (h : i ≠ i') : matId X i i' = 𝟘 := by
  simp only [matId, dif_neg h]

def matComp {X Y Z : MatObj 𝒜} (M : MatHom X Y) (N : MatHom Y Z) : MatHom X Z :=
  fun i k => finJoin (fun j => M i j ≫ N j k)

theorem matId_comp {X Y : MatObj 𝒜} (M : MatHom X Y) : matComp (matId X) M = M := by
  funext i k; simp only [matComp, matId]
  apply le_antisymm
  · refine listJoin'_le (fun x hx => ?_); obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    by_cases h : i = j
    · subst h; simp only [↓reduceDIte, Cat.id_comp, le_refl]
    · simp only [h, ↓reduceDIte, DistributiveAllegory.zero_comp]; exact zero_le _
  · have key := show (fun j => (if h : i = j then (by subst h; exact Cat.id (X.objs i) : X.objs i ⟶ X.objs j) else 𝟘) ≫ M j k) i ⊑ finJoin (fun j => (if h : i = j then (by subst h; exact Cat.id (X.objs i) : X.objs i ⟶ X.objs j) else 𝟘) ≫ M j k) from le_listJoin' (List.mem_ofFn.mpr ⟨i, rfl⟩)
    simp only [↓reduceDIte, Cat.id_comp] at key; exact key

theorem matComp_id {X Y : MatObj 𝒜} (M : MatHom X Y) : matComp M (matId Y) = M := by
  funext i k; simp only [matComp, matId]
  apply le_antisymm
  · refine listJoin'_le (fun x hx => ?_); obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    by_cases h : j = k
    · subst h; simp only [↓reduceDIte, Cat.comp_id, le_refl]
    · simp only [h, ↓reduceDIte, DistributiveAllegory.comp_zero]; exact zero_le _
  · have key := show (fun j => M i j ≫ (if h : j = k then (by subst h; exact Cat.id (Y.objs j) : Y.objs j ⟶ Y.objs k) else 𝟘)) k ⊑ finJoin (fun j => M i j ≫ (if h : j = k then (by subst h; exact Cat.id (Y.objs j) : Y.objs j ⟶ Y.objs k) else 𝟘)) from le_listJoin' (List.mem_ofFn.mpr ⟨k, rfl⟩)
    simp only [↓reduceDIte, Cat.comp_id] at key; exact key

theorem matComp_assoc {W X Y Z : MatObj 𝒜}
    (M : MatHom W X) (N : MatHom X Y) (P : MatHom Y Z) :
    matComp (matComp M N) P = matComp M (matComp N P) := by
  funext i l; simp only [matComp]
  apply le_antisymm
  · refine listJoin'_le (fun x hx => ?_); obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    rw [finJoin_comp]; refine listJoin'_le (fun x hx => ?_); obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    rw [Cat.assoc]
    exact le_trans (comp_mono_left (M i j) (show (fun k => N j k ≫ P k l) k ⊑ finJoin (fun k => N j k ≫ P k l) from le_listJoin' (List.mem_ofFn.mpr ⟨k, rfl⟩)))
                   (show (fun j => M i j ≫ finJoin (fun k => N j k ≫ P k l)) j ⊑ finJoin (fun j => M i j ≫ finJoin (fun k => N j k ≫ P k l)) from le_listJoin' (List.mem_ofFn.mpr ⟨j, rfl⟩))
  · refine listJoin'_le (fun x hx => ?_); obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    rw [comp_finJoin]; refine listJoin'_le (fun x hx => ?_); obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    rw [← Cat.assoc]
    exact le_trans (comp_mono_right (show (fun j => M i j ≫ N j k) j ⊑ finJoin (fun j => M i j ≫ N j k) from le_listJoin' (List.mem_ofFn.mpr ⟨j, rfl⟩)) (P k l))
                   (show (fun k => finJoin (fun j => M i j ≫ N j k) ≫ P k l) k ⊑ finJoin (fun k => finJoin (fun j => M i j ≫ N j k) ≫ P k l) from le_listJoin' (List.mem_ofFn.mpr ⟨k, rfl⟩))

instance instCatMatObj : Cat.{v} (MatObj 𝒜) where
  Hom     := MatHom
  id      := matId
  comp    := matComp
  id_comp := matId_comp
  comp_id := matComp_id
  assoc   := matComp_assoc

end MatCat

/-! ## §E  Allegory instance -/

section MatAllegory

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

def matRecip {X Y : MatObj 𝒜} (M : MatHom X Y) : MatHom Y X :=
  fun j i => (M i j)°

def matInter {X Y : MatObj 𝒜} (M N : MatHom X Y) : MatHom X Y :=
  fun i j => M i j ∩ N i j

theorem matRecip_comp {X Y Z : MatObj 𝒜} (M : MatHom X Y) (N : MatHom Y Z) :
    matRecip (matComp M N) = matComp (matRecip N) (matRecip M) := by
  funext k i; simp only [matRecip, matComp, recip_finJoin]
  congr 1; funext j; rw [Allegory.recip_comp]

theorem matSemidistrib {X Y Z : MatObj 𝒜} (R : MatHom X Y) (S T : MatHom Y Z) :
    matComp R (matInter S T) =
      matInter (matInter (matComp R S) (matComp R (matInter S T))) (matComp R T) := by
  funext i k; simp only [matComp, matInter]
  apply le_antisymm
  · apply le_inter
    · apply le_inter _ (le_refl _)
      exact finJoin_mono (fun j => comp_mono_left _ (inter_lb_left _ _))
    · exact finJoin_mono (fun j => comp_mono_left _ (inter_lb_right _ _))
  · exact le_trans (inter_lb_left _ _) (inter_lb_right _ _)

/-- Modular law: push `∩` inside the finite join via `inter_finJoin`, apply base `modular_le`. -/
theorem matModular {X Y Z : MatObj 𝒜} (R : MatHom X Y) (S : MatHom Y Z) (T : MatHom X Z) :
    matInter (matComp R S) T =
      matInter (matInter (matComp R S) T)
               (matComp (matInter R (matComp T (matRecip S))) S) := by
  funext i k; simp only [matInter, matComp, matRecip]
  apply le_antisymm
  · apply le_inter (le_refl _)
    rw [Allegory.inter_comm, inter_finJoin]
    apply finJoin_mono; intro j
    rw [Allegory.inter_comm]
    exact le_trans (modular_le (R i j) (S j k) (T i k))
      (comp_mono_right (le_inter (inter_lb_left _ _)
        (le_trans (inter_lb_right _ _) (show (fun l => T i l ≫ (S j l)°) k ⊑ finJoin (fun l => T i l ≫ (S j l)°) from le_listJoin' (List.mem_ofFn.mpr ⟨k, rfl⟩)))) _)
  · exact le_trans (inter_lb_left _ _) (le_refl _)

/-- §2.216: `Mat 𝒜` is an allegory. -/
instance instAllegoryMat : Allegory (MatObj 𝒜) where
  recip       := @matRecip 𝒜 _
  inter       := @matInter 𝒜 _
  recip_recip := fun M => by funext i j; simp [matRecip, Allegory.recip_recip]
  recip_comp  := matRecip_comp
  recip_inter := fun M N => by funext j i; simp [matRecip, matInter, Allegory.recip_inter]
  inter_idem  := fun M => by funext i j; simp [matInter, Allegory.inter_idem]
  inter_comm  := fun M N => by funext i j; simp [matInter, Allegory.inter_comm]
  inter_assoc := fun M N P => by funext i j; simp [matInter, Allegory.inter_assoc]
  semidistrib := matSemidistrib
  modular     := matModular

end MatAllegory

/-! ## §F  Distributive allegory instance -/

section MatDistributive

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

def matZero {X Y : MatObj 𝒜} : MatHom X Y := fun _i _j => 𝟘
def matUnion {X Y : MatObj 𝒜} (M N : MatHom X Y) : MatHom X Y := fun i j => M i j ∪ N i j

theorem matZero_comp {X Y Z : MatObj 𝒜} (N : MatHom Y Z) :
    matComp (matZero (X := X)) N = matZero := by
  funext i k; simp only [matComp, matZero, finJoin]
  apply le_antisymm
  · apply listJoin'_le; intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    rw [DistributiveAllegory.zero_comp]; exact le_refl _
  · exact zero_le _

theorem matComp_zero {X Y Z : MatObj 𝒜} (M : MatHom X Y) :
    matComp M (matZero (Y := Z)) = matZero := by
  funext i k; simp only [matComp, matZero, finJoin]
  apply le_antisymm
  · apply listJoin'_le; intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    rw [DistributiveAllegory.comp_zero]; exact le_refl _
  · exact zero_le _

theorem matComp_union_distrib {X Y Z : MatObj 𝒜} (M : MatHom X Y) (N P : MatHom Y Z) :
    matComp M (matUnion N P) = matUnion (matComp M N) (matComp M P) := by
  funext i k; simp only [matComp, matUnion]
  apply le_antisymm
  · refine listJoin'_le (fun x hx => ?_); obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    rw [DistributiveAllegory.comp_union_distrib]
    exact union_lub
      (le_trans (show (fun j => M i j ≫ N j k) j ⊑ finJoin (fun j => M i j ≫ N j k) from le_listJoin' (List.mem_ofFn.mpr ⟨j, rfl⟩)) (le_union_left _ _))
      (le_trans (show (fun j => M i j ≫ P j k) j ⊑ finJoin (fun j => M i j ≫ P j k) from le_listJoin' (List.mem_ofFn.mpr ⟨j, rfl⟩)) (le_union_right _ _))
  · exact union_lub (finJoin_mono (fun j => comp_mono_left (M i j) (le_union_left _ _)))
                    (finJoin_mono (fun j => comp_mono_left (M i j) (le_union_right _ _)))

/-- §2.216: `Mat 𝒜` is a distributive allegory. -/
instance instDistributiveAllegoryMat : DistributiveAllegory (MatObj 𝒜) :=
  { instAllegoryMat with
    zero  := matZero
    union := matUnion
    zero_comp  := matZero_comp
    comp_zero  := matComp_zero
    union_idem := fun M   => by funext i j; simp [matUnion, DistributiveAllegory.union_idem]
    union_comm := fun M N => by funext i j; simp [matUnion, DistributiveAllegory.union_comm]
    union_assoc := fun M N P => by
      funext i j; simp [matUnion, DistributiveAllegory.union_assoc]
    union_inter_absorb := fun M N => by
      funext i j; simp only [matUnion]; exact DistributiveAllegory.union_inter_absorb _ _
    inter_union_absorb := fun M N => by
      funext i j; show matInter (matUnion M N) M i j = M i j
      simp only [matUnion, matInter]; exact DistributiveAllegory.inter_union_absorb _ _
    comp_union_distrib := matComp_union_distrib
    inter_union_distrib := fun M N P => by
      funext i j; simp only [matUnion]; exact DistributiveAllegory.inter_union_distrib _ _ _
    zero_union := fun M => by
      funext i j; simp only [matUnion, matZero]; exact DistributiveAllegory.zero_union _ }

/-- `finJoin` of a family supported at a single index `k₀` is its value there. -/
theorem finJoin_single {a b : 𝒜} {n : Nat} (f : Fin n → (a ⟶ b)) (k₀ : Fin n)
    (h : ∀ k, k ≠ k₀ → f k = 𝟘) : finJoin f = f k₀ := by
  apply le_antisymm
  · refine listJoin'_le (fun x hx => ?_); obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    by_cases hk : k = k₀
    · subst hk; exact le_refl _
    · rw [h k hk]; exact zero_le _
  · exact show f k₀ ⊑ finJoin f from le_listJoin' (List.mem_ofFn.mpr ⟨k₀, rfl⟩)

theorem zero_inter {a b : 𝒜} (R : a ⟶ b) : (𝟘 : a ⟶ b) ∩ R = 𝟘 :=
  le_antisymm (inter_lb_left _ _) (zero_le _)

/-- Pointwise characterization of the matrix order: `M ⊑ N` iff entrywise. -/
theorem matLe_iff {X Y : MatObj 𝒜} {M N : X ⟶ Y} :
    (M ⊑ N) ↔ ∀ i j, M i j ⊑ N i j := by
  simp only [le]; constructor
  · intro h i j; exact congrFun (congrFun (show M ∩ N = M from h) i) j
  · intro h; show M ∩ N = M; funext i j; exact h i j

end MatDistributive

/-! ## §G  Division allegory instance (§2.342)

  (R/S)_{ij} = ⋀_{k : Fin Z.n} (R_{ik}/S_{jk}).

  When Z.n = 0 the composition T ≫ S : MatHom X Z has no entries (Fin 0 columns),
  so T ≫ S ⊑ R is vacuously true for any T, and we use
    matDiv R S i j = Cat.id (X.objs i) / (𝟘 : Y.objs j ⟶ X.objs i)
  as a "top" for the hom-set X.objs i ⟶ Y.objs j:
    T ⊑ id / 𝟘  iff  T ≫ 𝟘 ⊑ id  iff  𝟘 ⊑ id  (always true by zero_le). -/

section MatDivision

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-- Matrix division: `(R/S)_{ij} = ⋀_{k:Fin Z.n} (R_{ik}/S_{jk})`.
    When Z.n = 0, use the top morphism `id / 𝟘` (satisfied vacuously). -/
noncomputable def matDiv {X Y Z : MatObj 𝒜} (R : MatHom X Z) (S : MatHom Y Z) : MatHom X Y :=
  fun i j =>
    match h : Z.n with
    | 0     => Cat.id (X.objs i) / (𝟘 : Y.objs j ⟶ X.objs i)
    | _ + 1 => finMeet (fun k => R i (h ▸ k) / S j (h ▸ k))

theorem matDiv_le_div {X Y Z : MatObj 𝒜} (T : X ⟶ Y) (R : X ⟶ Z) (S : Y ⟶ Z)
    (h : T ≫ S ⊑ R) : T ⊑ matDiv R S := by
  cases Z with | mk zn zobjs =>
  rw [matLe_iff] at h ⊢; intro i j
  simp only [Cat.comp, matComp] at h
  simp only [matDiv]
  cases zn with
  | zero => rw [le_div_iff, DistributiveAllegory.comp_zero]; exact zero_le _
  | succ m =>
    apply le_finMeet; intro k
    rw [le_div_iff]
    -- The cast in S j (· ▸ k) is rfl after cases Z, so it's identity
    simp only
    exact le_trans (show (fun j => T i j ≫ S j k) j ⊑ finJoin (fun j => T i j ≫ S j k) from le_listJoin' (List.mem_ofFn.mpr ⟨j, rfl⟩)) (h i k)

theorem le_matDiv_comp {X Y Z : MatObj 𝒜} (R : X ⟶ Z) (S : Y ⟶ Z) :
    (matDiv R S : X ⟶ Y) ≫ S ⊑ R := by
  cases Z with | mk zn zobjs =>
  rw [matLe_iff]; intro i k
  simp only [Cat.comp, matComp, matDiv]
  cases zn with
  | zero => exact Fin.elim0 k
  | succ m =>
    simp only
    refine listJoin'_le (fun x hx => ?_); obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact le_trans (comp_mono_right (listMeet'_le _ _ (List.mem_ofFn.mpr ⟨k, rfl⟩)) _)
      (DivisionAllegory.div_comp_le _ _)

/-- §2.342  POSITIVE REFLECTION THEOREM: the positive reflection A⁺ of a division allegory is
    a division allegory (Freyd §2.342).

    The positive reflection A⁺ = `MatObj 𝒜` (finite-index-family objects, matrix morphisms).
    Division is entrywise: `(R/S)_{ij} = ⋀_{k} (R_{ik}/S_{jk})` (finite meet over codomain index k).
    The adjointness `T ⊑ R/S ↔ T≫S ⊑ R` lifts from the base via `le_div_iff` + `listJoin'_le`/`le_finMeet`.
    The faithful embedding `embed1 : 𝒜 → MatObj 𝒜` (§2.216) preserves ≫, °, ∩, ∪, 𝟘, /. -/
noncomputable instance instDivisionAllegoryMat : DivisionAllegory (MatObj 𝒜) :=
  { instDistributiveAllegoryMat with
    div         := fun R S => matDiv R S
    div_comp_le := fun R S => le_matDiv_comp R S
    le_div      := fun T R S h => matDiv_le_div T R S h }

end MatDivision

/-! ## §H  The 1×1 faithful embedding  A → Mat A  (§2.216 / §2.342) -/

section Embed1

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- The single-object 1×1 matrix object. -/
def unitObj (a : 𝒜) : MatObj 𝒜 := { n := 1, objs := fun _ => a }

/-- The 1×1 embedding: wraps a morphism as a 1×1 matrix. -/
def embed1 {a b : 𝒜} (R : a ⟶ b) : MatHom (unitObj a) (unitObj b) :=
  fun _i _j => R

/-- `embed1` is injective (faithful). -/
theorem embed1_injective {a b : 𝒜} {R S : a ⟶ b} (h : embed1 R = embed1 S) : R = S :=
  congrFun (congrFun h ⟨0, Nat.zero_lt_one⟩) ⟨0, Nat.zero_lt_one⟩

/-- `embed1` preserves composition. -/
theorem embed1_comp {a b c : 𝒜} (R : a ⟶ b) (S : b ⟶ c) :
    embed1 (R ≫ S) = matComp (embed1 R) (embed1 S) := by
  funext i k; simp only [embed1, matComp, finJoin, List.ofFn_succ, List.ofFn_zero, listJoin'_cons,
    listJoin'_nil, union_zero]

/-- `embed1` preserves reciprocation. -/
theorem embed1_recip {a b : 𝒜} (R : a ⟶ b) :
    embed1 (R°) = matRecip (embed1 R) := rfl

/-- `embed1` preserves intersection. -/
theorem embed1_inter {a b : 𝒜} (R S : a ⟶ b) :
    embed1 (R ∩ S) = matInter (embed1 R) (embed1 S) := rfl

/-- `embed1` preserves union. -/
theorem embed1_union {a b : 𝒜} (R S : a ⟶ b) :
    embed1 (R ∪ S) = matUnion (embed1 R) (embed1 S) := rfl

theorem embed1_zero {a b : 𝒜} :
    embed1 (𝟘 : a ⟶ b) = matZero := rfl

end Embed1

section Embed1Div

variable {𝒜 : Type u} [DivisionAllegory 𝒜]

/-- `embed1` preserves division. -/
theorem embed1_div {a b c : 𝒜} (R : a ⟶ c) (S : b ⟶ c) :
    embed1 (R / S) = matDiv (embed1 R) (embed1 S) := by
  funext i j
  simp only [embed1, matDiv, unitObj]
  -- Z.n = 1 = 0.succ, so the match hits | succ m with m = 0
  -- finMeet (fun k : Fin 1 => R (rfl ▸ k) / S (rfl ▸ k)) = R ⟨0,..⟩ / S ⟨0,..⟩ = R / S
  simp only [finMeet, List.ofFn_succ, List.ofFn_zero, listMeet']

end Embed1Div

/-! ## §J  Positive allegory instance (§2.215)

  `Mat 𝒜` has finite coproducts: `X ⊕ Y` is the concatenation of the two index
  families (`Fin (X.n + Y.n)`), and its injections are the reciprocals of the two
  block matrices `mInlR`, `mInrR` selecting the left / right summand.  Verifying the
  five `Coproduct` equations (§2.214) makes `(MatObj 𝒜)` a `PositiveAllegory`. -/

section MatPositive

variable {𝒜 : Type u} [DistributiveAllegory 𝒜]

/-- The coproduct object `X ⊕ Y`: concatenated index families. -/
def mCP (X Y : MatObj 𝒜) : MatObj 𝒜 :=
  { n := X.n + Y.n, objs := Fin.addCases X.objs Y.objs }

theorem mCP_L (X Y : MatObj 𝒜) (i : Fin X.n) :
    (mCP X Y).objs (Fin.castAdd Y.n i) = X.objs i := by simp [mCP, Fin.addCases_left]

theorem mCP_R (X Y : MatObj 𝒜) (j : Fin Y.n) :
    (mCP X Y).objs (Fin.natAdd X.n j) = Y.objs j := by simp [mCP, Fin.addCases_right]

/-- The transposed left injection `(X ⊕ Y) → X`: identity on the left block, 0 on the right. -/
def mInlR (X Y : MatObj 𝒜) : MatHom (mCP X Y) X :=
  fun k i => Fin.addCases (fun k_l => mCP_L X Y k_l ▸ matId X k_l i) (fun _k_r => 𝟘) k

/-- The transposed right injection `(X ⊕ Y) → Y`: 0 on the left block, identity on the right. -/
def mInrR (X Y : MatObj 𝒜) : MatHom (mCP X Y) Y :=
  fun k j => Fin.addCases (fun _k_l => 𝟘) (fun k_r => mCP_R X Y k_r ▸ matId Y k_r j) k

/-- The left injection `X → (X ⊕ Y)` (reciprocal of `mInlR`). -/
def mInl (X Y : MatObj 𝒜) : MatHom X (mCP X Y) := matRecip (mInlR X Y)
/-- The right injection `Y → (X ⊕ Y)` (reciprocal of `mInrR`). -/
def mInr (X Y : MatObj 𝒜) : MatHom Y (mCP X Y) := matRecip (mInrR X Y)

theorem mInl_recip (X Y : MatObj 𝒜) : matRecip (mInl X Y) = mInlR X Y := by
  funext k i; simp only [mInl, matRecip, Allegory.recip_recip]
theorem mInr_recip (X Y : MatObj 𝒜) : matRecip (mInr X Y) = mInrR X Y := by
  funext k i; simp only [mInr, matRecip, Allegory.recip_recip]

/-! ### Transport helpers across the `objs`-equalities `mCP_L`, `mCP_R`. -/

theorem cast_comp_recip {A B C : 𝒜} (h : A = B) (f g : B ⟶ C) :
    (h ▸ f : A ⟶ C) ≫ (h ▸ g : A ⟶ C)° = h ▸ (f ≫ g°) := by
  have recip_cast : (h ▸ g : A ⟶ C)° = h ▸ g° := by cases h; rfl
  rw [recip_cast]; cases h; rfl

theorem cast_recip_comp {A B C D : 𝒜} (h : A = B) (f : B ⟶ C) (g : B ⟶ D) :
    (h ▸ f : A ⟶ C)° ≫ (h ▸ g : A ⟶ D) = f° ≫ g := by cases h; rfl

theorem finJoin_cast_endo {A B : 𝒜} (h : A = B) {n} (t : Fin n → B ⟶ B) :
    finJoin (fun i => (h ▸ t i : A ⟶ A)) = h ▸ finJoin t := by cases h; rfl

theorem cast_id_is_id {A B : 𝒜} (h : A = B) : (h ▸ Cat.id B : A ⟶ A) = Cat.id A := by cases h; rfl

theorem cast_zero_src {A B C : 𝒜} (h : A = B) : (h ▸ (𝟘 : B ⟶ C) : A ⟶ C) = 𝟘 := by cases h; rfl

theorem cast_zero_recip {A B C : 𝒜} (h : A = B) : (h ▸ (𝟘 : B ⟶ C) : A ⟶ C)° = 𝟘 := by
  cases h; simp [recip_zero]

/-! ### `finJoin` helpers: zero family, append split, dependent-codomain vanishing. -/

theorem finJoin_zero_all {a b : 𝒜} {n : Nat} {f : Fin n → (a ⟶ b)}
    (h : ∀ k, f k = 𝟘) : finJoin f = 𝟘 :=
  le_antisymm (listJoin'_le (fun x hx => by
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx; rw [h k]; exact le_refl _)) (zero_le _)

theorem listJoin'_append {a b : 𝒜} (l₁ l₂ : List (a ⟶ b)) :
    listJoin' (l₁ ++ l₂) = listJoin' l₁ ∪ listJoin' l₂ := by
  induction l₁ with
  | nil => simp only [List.nil_append, listJoin'_nil, DistributiveAllegory.zero_union]
  | cons x xs ih =>
    simp only [List.cons_append, listJoin'_cons, ih, DistributiveAllegory.union_assoc]

/-- Split a `finJoin` over `Fin (m + n)` into its left (`castAdd`) and right (`natAdd`) blocks. -/
theorem finJoin_addCases {a b : 𝒜} {m n : Nat} (f : Fin (m + n) → (a ⟶ b)) :
    finJoin f = finJoin (fun i => f (Fin.castAdd n i)) ∪ finJoin (fun j => f (Fin.natAdd m j)) := by
  simp only [finJoin]; rw [List.ofFn_add, listJoin'_append]; rfl

theorem finJoin_first_zero {A C : 𝒜} {n} {B : Fin n → 𝒜}
    (f : (i : Fin n) → A ⟶ B i) (g : (i : Fin n) → C ⟶ B i) (hf : ∀ i, f i = 𝟘) :
    finJoin (fun i => f i ≫ (g i)°) = (𝟘 : A ⟶ C) := by
  apply finJoin_zero_all; intro i; rw [hf i, DistributiveAllegory.zero_comp]

theorem finJoin_second_zero {A C : 𝒜} {n} {B : Fin n → 𝒜}
    (f : (i : Fin n) → A ⟶ B i) (g : (i : Fin n) → C ⟶ B i) (hg : ∀ i, g i = 𝟘) :
    finJoin (fun i => f i ≫ (g i)°) = (𝟘 : A ⟶ C) := by
  apply finJoin_zero_all; intro i; rw [hg i, recip_zero, DistributiveAllegory.comp_zero]

/-! ### `Fin.castAdd` / `Fin.natAdd` injectivity and disjointness. -/

theorem castAdd_inj {m n : Nat} {i j : Fin m} (h : Fin.castAdd n i = Fin.castAdd n j) : i = j := by
  have : (Fin.castAdd n i).val = (Fin.castAdd n j).val := by rw [h]
  simp only [Fin.val_castAdd] at this; exact Fin.ext this

theorem natAdd_inj {m n : Nat} {i j : Fin n} (h : Fin.natAdd m i = Fin.natAdd m j) : i = j := by
  have : (Fin.natAdd m i).val = (Fin.natAdd m j).val := by rw [h]
  simp only [Fin.val_natAdd] at this; exact Fin.ext (Nat.add_left_cancel this)

theorem castAdd_ne_natAdd {m n : Nat} (i : Fin m) (j : Fin n) :
    Fin.castAdd n i ≠ Fin.natAdd m j := by
  intro h; have : (Fin.castAdd n i).val = (Fin.natAdd m j).val := by rw [h]
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega

/-! ### Orthonormality of the identity "basis" matrix. -/

/-- `∑ⱼ (matId k j)(matId k j)° = id` : the rows of `matId` are orthonormal. -/
theorem basis_self {X : MatObj 𝒜} (k : Fin X.n) :
    finJoin (fun i => matId X k i ≫ (matId X k i)°) = Cat.id (X.objs k) := by
  apply le_antisymm
  · refine listJoin'_le (fun x hx => ?_); obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    by_cases h : k = i
    · subst h; simp only [matId, ↓reduceDIte, Cat.id_comp, recip_id, le_refl]
    · simp only [matId, h, ↓reduceDIte, DistributiveAllegory.zero_comp]; exact zero_le _
  · have key := show (fun i => matId X k i ≫ (matId X k i)°) k ⊑ finJoin (fun i => matId X k i ≫ (matId X k i)°) from le_listJoin' (List.mem_ofFn.mpr ⟨k, rfl⟩)
    simp only [matId, ↓reduceDIte, Cat.id_comp, recip_id] at key
    exact key

/-- `∑ⱼ (matId j i)° (matId j k) = matId i k` : the columns of `matId` are orthonormal. -/
theorem basis_recip_self {X : MatObj 𝒜} (i k : Fin X.n) :
    finJoin (fun j => (matId X j i)° ≫ matId X j k) = matId X i k := by
  apply le_antisymm
  · refine listJoin'_le (fun x hx => ?_); obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    by_cases hji : j = i
    · subst hji
      by_cases hjk : j = k
      · subst hjk; simp only [matId, ↓reduceDIte, recip_id, Cat.id_comp, le_refl]
      · simp only [matId, hjk, ↓reduceDIte, recip_id, DistributiveAllegory.comp_zero, le_refl]
    · simp only [matId, hji, ↓reduceDIte, recip_zero, DistributiveAllegory.zero_comp]
      exact zero_le _
  · by_cases hik : i = k
    · subst hik
      have key := show (fun j => (matId X j i)° ≫ matId X j i) i ⊑ finJoin (fun j => (matId X j i)° ≫ matId X j i) from le_listJoin' (List.mem_ofFn.mpr ⟨i, rfl⟩)
      simp only [matId, ↓reduceDIte, recip_id, Cat.id_comp] at key
      simpa [matId] using key
    · simp only [matId, hik, ↓reduceDIte]; exact zero_le _

/-! ### Diagonal / off-diagonal block computations for the injections. -/

theorem finJoin_diag_L (X Y : MatObj 𝒜) (k_l : Fin X.n) :
    finJoin (fun i => mInlR X Y (Fin.castAdd Y.n k_l) i ≫ (mInlR X Y (Fin.castAdd Y.n k_l) i)°)
      = Cat.id ((mCP X Y).objs (Fin.castAdd Y.n k_l)) := by
  have step : (fun i => mInlR X Y (Fin.castAdd Y.n k_l) i ≫ (mInlR X Y (Fin.castAdd Y.n k_l) i)°)
      = (fun i => (mCP_L X Y k_l ▸ (matId X k_l i ≫ (matId X k_l i)°)
          : (mCP X Y).objs (Fin.castAdd Y.n k_l) ⟶ (mCP X Y).objs (Fin.castAdd Y.n k_l))) := by
    funext i; simp only [mInlR, Fin.addCases_left]; exact cast_comp_recip (mCP_L X Y k_l) _ _
  rw [step, finJoin_cast_endo (mCP_L X Y k_l), basis_self, cast_id_is_id (mCP_L X Y k_l)]

theorem finJoin_cross_LL (X Y : MatObj 𝒜) (k_l k_l' : Fin X.n) (hkk : k_l ≠ k_l') :
    finJoin (fun i => mInlR X Y (Fin.castAdd Y.n k_l) i ≫ (mInlR X Y (Fin.castAdd Y.n k_l') i)°)
      = (𝟘 : (mCP X Y).objs (Fin.castAdd Y.n k_l) ⟶ (mCP X Y).objs (Fin.castAdd Y.n k_l')) := by
  apply finJoin_zero_all; intro i; simp only [mInlR, Fin.addCases_left]
  by_cases hki : k_l = i
  · subst hki
    have hz : matId X k_l' k_l = 𝟘 := by
      simp only [matId, dite_eq_right_iff]; intro h; exact absurd h hkk.symm
    rw [hz, cast_zero_recip (mCP_L X Y k_l'), DistributiveAllegory.comp_zero]
  · have hz : matId X k_l i = 𝟘 := by
      simp only [matId, dite_eq_right_iff]; intro h; exact absurd h hki
    rw [hz, cast_zero_src (mCP_L X Y k_l), DistributiveAllegory.zero_comp]

theorem finJoin_diag_R (X Y : MatObj 𝒜) (k_r : Fin Y.n) :
    finJoin (fun i => mInrR X Y (Fin.natAdd X.n k_r) i ≫ (mInrR X Y (Fin.natAdd X.n k_r) i)°)
      = Cat.id ((mCP X Y).objs (Fin.natAdd X.n k_r)) := by
  have step : (fun i => mInrR X Y (Fin.natAdd X.n k_r) i ≫ (mInrR X Y (Fin.natAdd X.n k_r) i)°)
      = (fun i => (mCP_R X Y k_r ▸ (matId Y k_r i ≫ (matId Y k_r i)°)
          : (mCP X Y).objs (Fin.natAdd X.n k_r) ⟶ (mCP X Y).objs (Fin.natAdd X.n k_r))) := by
    funext i; simp only [mInrR, Fin.addCases_right]; exact cast_comp_recip (mCP_R X Y k_r) _ _
  rw [step, finJoin_cast_endo (mCP_R X Y k_r), basis_self, cast_id_is_id (mCP_R X Y k_r)]

theorem finJoin_cross_RR (X Y : MatObj 𝒜) (k_r k_r' : Fin Y.n) (hkk : k_r ≠ k_r') :
    finJoin (fun i => mInrR X Y (Fin.natAdd X.n k_r) i ≫ (mInrR X Y (Fin.natAdd X.n k_r') i)°)
      = (𝟘 : (mCP X Y).objs (Fin.natAdd X.n k_r) ⟶ (mCP X Y).objs (Fin.natAdd X.n k_r')) := by
  apply finJoin_zero_all; intro i; simp only [mInrR, Fin.addCases_right]
  by_cases hki : k_r = i
  · subst hki
    have hz : matId Y k_r' k_r = 𝟘 := by
      simp only [matId, dite_eq_right_iff]; intro h; exact absurd h hkk.symm
    rw [hz, cast_zero_recip (mCP_R X Y k_r'), DistributiveAllegory.comp_zero]
  · have hz : matId Y k_r i = 𝟘 := by
      simp only [matId, dite_eq_right_iff]; intro h; exact absurd h hki
    rw [hz, cast_zero_src (mCP_R X Y k_r), DistributiveAllegory.zero_comp]

theorem mInlR_natAdd (X Y : MatObj 𝒜) (j : Fin Y.n) (i : Fin X.n) :
    mInlR X Y (Fin.natAdd X.n j) i = 𝟘 := by simp only [mInlR, Fin.addCases_right]
theorem mInrR_castAdd (X Y : MatObj 𝒜) (j : Fin X.n) (i : Fin Y.n) :
    mInrR X Y (Fin.castAdd Y.n j) i = 𝟘 := by simp only [mInrR, Fin.addCases_left]

/-! ### `matId` on the coproduct object. -/

theorem matId_mCP_LL_off (X Y : MatObj 𝒜) (k_l k_l' : Fin X.n) (h : k_l ≠ k_l') :
    matId (mCP X Y) (Fin.castAdd Y.n k_l) (Fin.castAdd Y.n k_l') = 𝟘 := by
  simp only [matId, dite_eq_right_iff]; intro he; exact absurd (castAdd_inj he) h
theorem matId_mCP_LR (X Y : MatObj 𝒜) (k_l : Fin X.n) (k_r : Fin Y.n) :
    matId (mCP X Y) (Fin.castAdd Y.n k_l) (Fin.natAdd X.n k_r) = 𝟘 := by
  simp only [matId, dite_eq_right_iff]; intro he; exact absurd he (castAdd_ne_natAdd k_l k_r)
theorem matId_mCP_RL (X Y : MatObj 𝒜) (k_r : Fin Y.n) (k_l : Fin X.n) :
    matId (mCP X Y) (Fin.natAdd X.n k_r) (Fin.castAdd Y.n k_l) = 𝟘 := by
  simp only [matId, dite_eq_right_iff]; intro he; exact absurd he.symm (castAdd_ne_natAdd k_l k_r)
theorem matId_mCP_RR_off (X Y : MatObj 𝒜) (k_r k_r' : Fin Y.n) (h : k_r ≠ k_r') :
    matId (mCP X Y) (Fin.natAdd X.n k_r) (Fin.natAdd X.n k_r') = 𝟘 := by
  simp only [matId, dite_eq_right_iff]; intro he; exact absurd (natAdd_inj he) h

/-! ### The five `Coproduct` equations (§2.214). -/

/-- §2.214 eq.1: `u₁ ≫ u₁° = id_X`, i.e. `mInl ≫ mInlR = id`. -/
theorem mCoprod_eq1 (X Y : MatObj 𝒜) : matComp (mInl X Y) (mInlR X Y) = matId X := by
  funext i k
  simp only [matComp, mInl, matRecip]
  rw [finJoin_addCases]
  have hleft : (fun j => (mInlR X Y (Fin.castAdd Y.n j) i)° ≫ mInlR X Y (Fin.castAdd Y.n j) k)
      = (fun j => (matId X j i)° ≫ matId X j k) := by
    funext j; simp only [mInlR, Fin.addCases_left]
    exact cast_recip_comp (mCP_L X Y j) (matId X j i) (matId X j k)
  have hright : finJoin
      (fun j => (mInlR X Y (Fin.natAdd X.n j) i)° ≫ mInlR X Y (Fin.natAdd X.n j) k) = 𝟘 := by
    apply finJoin_zero_all; intro j
    simp only [mInlR, Fin.addCases_right, recip_zero, DistributiveAllegory.zero_comp]
  rw [hleft, basis_recip_self, hright, union_zero]

/-- §2.214 eq.2: `u₁ ≫ u₂° = 0`, i.e. `mInl ≫ mInrR = 0`. -/
theorem mCoprod_eq2 (X Y : MatObj 𝒜) : matComp (mInl X Y) (mInrR X Y) = matZero := by
  funext i k
  simp only [matComp, mInl, matRecip, matZero]
  rw [finJoin_addCases]
  have hleft : finJoin
      (fun j => (mInlR X Y (Fin.castAdd Y.n j) i)° ≫ mInrR X Y (Fin.castAdd Y.n j) k) = 𝟘 := by
    apply finJoin_zero_all; intro j
    simp only [mInlR, mInrR, Fin.addCases_left, DistributiveAllegory.comp_zero]
  have hright : finJoin
      (fun j => (mInlR X Y (Fin.natAdd X.n j) i)° ≫ mInrR X Y (Fin.natAdd X.n j) k) = 𝟘 := by
    apply finJoin_zero_all; intro j
    simp only [mInlR, Fin.addCases_right, recip_zero, DistributiveAllegory.zero_comp]
  rw [hleft, hright, union_zero]

/-- §2.214 eq.3: `u₂ ≫ u₁° = 0`, i.e. `mInr ≫ mInlR = 0`. -/
theorem mCoprod_eq3 (X Y : MatObj 𝒜) : matComp (mInr X Y) (mInlR X Y) = matZero := by
  funext i k
  simp only [matComp, mInr, matRecip, matZero]
  rw [finJoin_addCases]
  have hleft : finJoin
      (fun j => (mInrR X Y (Fin.castAdd Y.n j) i)° ≫ mInlR X Y (Fin.castAdd Y.n j) k) = 𝟘 := by
    apply finJoin_zero_all; intro j
    simp only [mInrR, Fin.addCases_left, recip_zero, DistributiveAllegory.zero_comp]
  have hright : finJoin
      (fun j => (mInrR X Y (Fin.natAdd X.n j) i)° ≫ mInlR X Y (Fin.natAdd X.n j) k) = 𝟘 := by
    apply finJoin_zero_all; intro j
    simp only [mInrR, mInlR, Fin.addCases_right, DistributiveAllegory.comp_zero]
  rw [hleft, hright, union_zero]

/-- §2.214 eq.4: `u₂ ≫ u₂° = id_Y`, i.e. `mInr ≫ mInrR = id`. -/
theorem mCoprod_eq4 (X Y : MatObj 𝒜) : matComp (mInr X Y) (mInrR X Y) = matId Y := by
  funext i k
  simp only [matComp, mInr, matRecip]
  rw [finJoin_addCases]
  have hleft : finJoin
      (fun j => (mInrR X Y (Fin.castAdd Y.n j) i)° ≫ mInrR X Y (Fin.castAdd Y.n j) k) = 𝟘 := by
    apply finJoin_zero_all; intro j
    simp only [mInrR, Fin.addCases_left, recip_zero, DistributiveAllegory.zero_comp]
  have hright : (fun j => (mInrR X Y (Fin.natAdd X.n j) i)° ≫ mInrR X Y (Fin.natAdd X.n j) k)
      = (fun j => (matId Y j i)° ≫ matId Y j k) := by
    funext j; simp only [mInrR, Fin.addCases_right]
    exact cast_recip_comp (mCP_R X Y j) (matId Y j i) (matId Y j k)
  rw [hleft, hright, basis_recip_self, DistributiveAllegory.zero_union]

/-- §2.214 eq.5: `(u₁° ≫ u₁) ∪ (u₂° ≫ u₂) = id_{X⊕Y}`.  Checked over the four index blocks. -/
theorem mCoprod_eq5 (X Y : MatObj 𝒜) :
    matUnion (matComp (mInlR X Y) (mInl X Y)) (matComp (mInrR X Y) (mInr X Y))
      = matId (mCP X Y) := by
  funext k k'
  simp only [matUnion, matComp, mInl, mInr, matRecip]
  refine Fin.addCases (fun k_l => ?_) (fun k_r => ?_) k <;>
    refine Fin.addCases (fun k_l' => ?_) (fun k_r' => ?_) k'
  · by_cases hkk : k_l = k_l'
    · subst hkk
      rw [finJoin_diag_L, finJoin_first_zero _ _ (fun i => mInrR_castAdd X Y k_l i), union_zero,
        matId_diag]
    · rw [finJoin_cross_LL X Y k_l k_l' hkk,
        finJoin_first_zero _ _ (fun i => mInrR_castAdd X Y k_l i), union_zero,
        matId_mCP_LL_off X Y k_l k_l' hkk]
  · rw [finJoin_second_zero _ _ (fun i => mInlR_natAdd X Y k_r' i),
      finJoin_first_zero _ _ (fun i => mInrR_castAdd X Y k_l i), union_zero, matId_mCP_LR]
  · rw [finJoin_first_zero _ _ (fun i => mInlR_natAdd X Y k_r i),
      finJoin_second_zero _ _ (fun i => mInrR_castAdd X Y k_l' i), union_zero, matId_mCP_RL]
  · by_cases hkk : k_r = k_r'
    · subst hkk
      rw [finJoin_diag_R, finJoin_first_zero _ _ (fun i => mInlR_natAdd X Y k_r i),
        DistributiveAllegory.zero_union, matId_diag]
    · rw [finJoin_cross_RR X Y k_r k_r' hkk,
        finJoin_first_zero _ _ (fun i => mInlR_natAdd X Y k_r i),
        DistributiveAllegory.zero_union, matId_mCP_RR_off X Y k_r k_r' hkk]

/-- §2.214: the `Coproduct` diagram `X → (X ⊕ Y) ← Y` built from the five equations. -/
def mCoproduct (X Y : MatObj 𝒜) : Coproduct (mCP X Y) X Y where
  u₁ := mInl X Y
  u₂ := mInr X Y
  u₁_self_comp_recip :=
    (by show matComp (mInl X Y) (matRecip (mInl X Y)) = matId X
        rw [mInl_recip]; exact mCoprod_eq1 X Y)
  u₁_u₂_recip :=
    (by show matComp (mInl X Y) (matRecip (mInr X Y)) = matZero
        rw [mInr_recip]; exact mCoprod_eq2 X Y)
  u₂_u₁_recip :=
    (by show matComp (mInr X Y) (matRecip (mInl X Y)) = matZero
        rw [mInl_recip]; exact mCoprod_eq3 X Y)
  u₂_self_comp_recip :=
    (by show matComp (mInr X Y) (matRecip (mInr X Y)) = matId Y
        rw [mInr_recip]; exact mCoprod_eq4 X Y)
  recip_union_eq_id :=
    (by show matUnion (matComp (matRecip (mInl X Y)) (mInl X Y))
              (matComp (matRecip (mInr X Y)) (mInr X Y)) = matId (mCP X Y)
        rw [mInl_recip, mInr_recip]; exact mCoprod_eq5 X Y)

/-- §2.215: `Mat 𝒜` is a positive allegory (has finite coproducts). -/
instance instPositiveAllegoryMat : PositiveAllegory (MatObj 𝒜) :=
  { instDistributiveAllegoryMat with
    coterm := { n := 0, objs := Fin.elim0 }
    coprod := mCP
    has_coproduct := mCoproduct }

end MatPositive

/-! ## §K  Tabularity of `Mat 𝒜`  (§2.342)

  If 𝒜 is tabular, so is `Mat 𝒜`.  Given a matrix `M : X ⟶ Y` (entries
  `M i j : X.objs i ⟶ Y.objs j`), tabulate each entry in 𝒜 — apex `c i j`, map legs
  `p i j : c i j ⟶ X.objs i`, `q i j : c i j ⟶ Y.objs j` with `M i j = p° ≫ q` and
  `p p° ∩ q q° = 1`.  The tabulation of `M` in `Mat 𝒜` has apex the coproduct
  `⊕_{i,j} c i j` (a `MatObj` indexed by `Fin (X.n * Y.n)`), with left leg `f` carrying
  block `p i j` into row `i` (zero off that row) and right leg `g` carrying `q i j` into
  column `j`.  The disjointness of the index blocks (off-diagonal terms vanish) reduces all
  four `Tabulates` conjuncts to the per-entry tabulation data. -/

section MatTabular

variable {𝒜 : Type u}

/-! ### Pairing of two `Fin` indices into one flat index for the apex. -/

def pairIdx {m n : Nat} (i : Fin m) (j : Fin n) : Fin (m * n) :=
  ⟨i.val * n + j.val, by
    have hi := i.isLt
    have h2 : i.val * n + n = (i.val + 1) * n := by rw [Nat.succ_mul]
    have h3 : (i.val + 1) * n ≤ m * n := Nat.mul_le_mul_right n hi
    omega⟩

def unpairFst {m n : Nat} (k : Fin (m * n)) : Fin m :=
  ⟨k.val / n, by
    have hk := k.isLt
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp [Nat.mul_zero] at hk
      · exact h
    exact Nat.div_lt_of_lt_mul (Nat.mul_comm m n ▸ hk)⟩

def unpairSnd {m n : Nat} (k : Fin (m * n)) : Fin n :=
  ⟨k.val % n, by
    have hk := k.isLt
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp [Nat.mul_zero] at hk
      · exact h
    exact Nat.mod_lt _ hn⟩

theorem unpairFst_pairIdx {m n : Nat} (i : Fin m) (j : Fin n) : unpairFst (pairIdx i j) = i := by
  apply Fin.ext; simp only [unpairFst, pairIdx]
  rw [Nat.mul_comm, Nat.mul_add_div (Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt),
    Nat.div_eq_of_lt j.isLt, Nat.add_zero]

theorem unpairSnd_pairIdx {m n : Nat} (i : Fin m) (j : Fin n) : unpairSnd (pairIdx i j) = j := by
  apply Fin.ext; simp only [unpairSnd, pairIdx]
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]

theorem pairIdx_unpair {m n : Nat} (k : Fin (m * n)) :
    pairIdx (unpairFst k) (unpairSnd k) = k := by
  apply Fin.ext; simp only [pairIdx, unpairFst, unpairSnd]
  rw [Nat.mul_comm]; exact Nat.div_add_mod k.val n

/-- The flat index `k` is recovered from its two coordinates, hence `(uFst, uSnd)` is injective. -/
theorem index_unique {m n : Nat} {k k' : Fin (m * n)}
    (hf : unpairFst k = unpairFst k') (hs : unpairSnd k = unpairSnd k') : k = k' := by
  rw [← pairIdx_unpair k, ← pairIdx_unpair k', hf, hs]

/-- A combined `Tabular`+`Distributive` allegory: one merged `Allegory` parent (so the matrix
    construction — which needs `DistributiveAllegory` — and the entry tabulations — which need
    `TabularAllegory` — share a single `Allegory 𝒜`, avoiding the diamond).  (Mat's own class
    `MatObj` is built over `DistributiveAllegory`; this is the §2.342 hypothesis for tabularity.
    Cannot reuse `MapCat.TabularUnitaryDistributiveAllegory`: importing `MapCat` here would cycle
    `MatrixAllegory → S2_21 → … → MapCat → S2_21`.) -/
class TabularDistributiveAllegory (𝒜 : Type u) extends TabularAllegory 𝒜, DistributiveAllegory 𝒜

variable [TabularDistributiveAllegory 𝒜]

/-! ### Per-entry tabulation data, chosen by `Classical.choice`. -/

noncomputable def entryTab {X Y : MatObj 𝒜} (M : MatHom X Y) (i : Fin X.n) (j : Fin Y.n) :
    {c : 𝒜 // ∃ (f : c ⟶ X.objs i) (g : c ⟶ Y.objs j), Tabulates f g (M i j)} :=
  ⟨(TabularAllegory.tabular (M i j)).choose, (TabularAllegory.tabular (M i j)).choose_spec⟩

/-- Apex object: the family `c (uFst k) (uSnd k)` over `Fin (X.n * Y.n)`. -/
noncomputable def tabApex {X Y : MatObj 𝒜} (M : MatHom X Y) : MatObj 𝒜 :=
  { n := X.n * Y.n, objs := fun k => (entryTab M (unpairFst k) (unpairSnd k)).1 }

noncomputable def tabP {X Y : MatObj 𝒜} (M : MatHom X Y) (i : Fin X.n) (j : Fin Y.n) :
    (entryTab M i j).1 ⟶ X.objs i := (entryTab M i j).2.choose
noncomputable def tabQ {X Y : MatObj 𝒜} (M : MatHom X Y) (i : Fin X.n) (j : Fin Y.n) :
    (entryTab M i j).1 ⟶ Y.objs j := (entryTab M i j).2.choose_spec.choose

/-- Left leg `f : tabApex ⟶ X`: block `tabP` on the diagonal row, `0` off-diagonal. -/
noncomputable def tabF {X Y : MatObj 𝒜} (M : MatHom X Y) : MatHom (tabApex M) X :=
  fun k i' => if h : unpairFst k = i' then (h ▸ tabP M (unpairFst k) (unpairSnd k)) else 𝟘
/-- Right leg `g : tabApex ⟶ Y`: block `tabQ` on the diagonal column, `0` off-diagonal. -/
noncomputable def tabG {X Y : MatObj 𝒜} (M : MatHom X Y) : MatHom (tabApex M) Y :=
  fun k j' => if h : unpairSnd k = j' then (h ▸ tabQ M (unpairFst k) (unpairSnd k)) else 𝟘

/-! ### Cast pushers for the index-casts in the legs (`hf : i₀ = i` recasts `X.objs i₀`). -/

/-- `(hf ▸ f)° ≫ (hs ▸ g)` where `hf : iF = i`, `hs : iS = j` recast the TARGETS of
    `f : A ⟶ F iF`, `g : A ⟶ G iS` along families `F`, `G`. -/
theorem idxCast_recip_comp {ιF ιG : Type} {F : ιF → 𝒜} {G : ιG → 𝒜}
    {iF i : ιF} {iS j : ιG} (hf : iF = i) (hs : iS = j) {A : 𝒜}
    (f : A ⟶ F iF) (g : A ⟶ G iS) :
    (hf ▸ f : A ⟶ F i)° ≫ (hs ▸ g : A ⟶ G j)
      = (hf ▸ (hs ▸ (f° ≫ g : F iF ⟶ G iS) : F iF ⟶ G j) : F i ⟶ G j) := by
  cases hf; cases hs; rfl

/-- Collapse the index-casts on a matrix entry: `hf ▸ hs ▸ M iF iS = M i j`. -/
theorem entry_idxCast {X Y : MatObj 𝒜} (M : MatHom X Y) {iF i : Fin X.n} {iS j : Fin Y.n}
    (hf : iF = i) (hs : iS = j) :
    (hf ▸ (hs ▸ (M iF iS : X.objs iF ⟶ Y.objs iS) : X.objs iF ⟶ Y.objs j) : X.objs i ⟶ Y.objs j)
      = M i j := by cases hf; cases hs; rfl

/-! ### Conjunct 3: `M = f° ≫ g`.  (Only `k = pairIdx i j` survives in the join.) -/

theorem tab_recipF_comp_G {X Y : MatObj 𝒜} (M : MatHom X Y) :
    matComp (matRecip (tabF M)) (tabG M) = M := by
  funext i j
  simp only [matComp, matRecip]
  rw [finJoin_single _ (pairIdx i j)]
  · have hf : unpairFst (pairIdx i j) = i := unpairFst_pairIdx i j
    have hs : unpairSnd (pairIdx i j) = j := unpairSnd_pairIdx i j
    show (tabF M (pairIdx i j) i)° ≫ tabG M (pairIdx i j) j = M i j
    simp only [tabF, tabG, dif_pos hf, dif_pos hs]
    rw [idxCast_recip_comp hf hs,
      (show Tabulates (tabP M (unpairFst (pairIdx i j)) (unpairSnd (pairIdx i j)))
          (tabQ M (unpairFst (pairIdx i j)) (unpairSnd (pairIdx i j)))
          (M (unpairFst (pairIdx i j)) (unpairSnd (pairIdx i j)))
        from (entryTab M (unpairFst (pairIdx i j)) (unpairSnd (pairIdx i j))).2.choose_spec.choose_spec
      ).2.2.1.symm,
      entry_idxCast M hf hs]
  · intro k hk
    by_cases hfi : unpairFst k = i
    · by_cases hsj : unpairSnd k = j
      · exact absurd (index_unique (by rw [hfi, unpairFst_pairIdx])
          (by rw [hsj, unpairSnd_pairIdx])) hk
      · simp only [tabG, hsj, ↓reduceDIte, DistributiveAllegory.comp_zero]
    · simp only [tabF, hfi, ↓reduceDIte, recip_zero, DistributiveAllegory.zero_comp]

/-! ### `f ≫ f°` and `g ≫ g°` blocks (off-diagonal vanishing + diagonal value). -/

theorem tabFFr_off {X Y : MatObj 𝒜} (M : MatHom X Y) {k k' : Fin (tabApex M).n}
    (h : unpairFst k ≠ unpairFst k') :
    matComp (tabF M) (matRecip (tabF M)) k k' = 𝟘 := by
  simp only [matComp, matRecip]
  apply finJoin_zero_all; intro i
  by_cases hi : unpairFst k = i
  · have hk' : unpairFst k' ≠ i := fun e => h (hi.trans e.symm)
    simp only [tabF, dif_neg hk', recip_zero, DistributiveAllegory.comp_zero]
  · simp only [tabF, dif_neg hi, DistributiveAllegory.zero_comp]

theorem tabGGr_off {X Y : MatObj 𝒜} (M : MatHom X Y) {k k' : Fin (tabApex M).n}
    (h : unpairSnd k ≠ unpairSnd k') :
    matComp (tabG M) (matRecip (tabG M)) k k' = 𝟘 := by
  simp only [matComp, matRecip]
  apply finJoin_zero_all; intro j
  by_cases hj : unpairSnd k = j
  · have hk' : unpairSnd k' ≠ j := fun e => h (hj.trans e.symm)
    simp only [tabG, dif_neg hk', recip_zero, DistributiveAllegory.comp_zero]
  · simp only [tabG, dif_neg hj, DistributiveAllegory.zero_comp]

theorem tabFFr_diag {X Y : MatObj 𝒜} (M : MatHom X Y) (k : Fin (tabApex M).n) :
    matComp (tabF M) (matRecip (tabF M)) k k
      = (tabP M (unpairFst k) (unpairSnd k)) ≫ (tabP M (unpairFst k) (unpairSnd k))° := by
  simp only [matComp, matRecip]
  rw [finJoin_single _ (unpairFst k)]
  · simp only [tabF, ↓reduceDIte]
  · intro i hi
    simp only [tabF, dif_neg (Ne.symm hi), DistributiveAllegory.zero_comp]

theorem tabGGr_diag {X Y : MatObj 𝒜} (M : MatHom X Y) (k : Fin (tabApex M).n) :
    matComp (tabG M) (matRecip (tabG M)) k k
      = (tabQ M (unpairFst k) (unpairSnd k)) ≫ (tabQ M (unpairFst k) (unpairSnd k))° := by
  simp only [matComp, matRecip]
  rw [finJoin_single _ (unpairSnd k)]
  · simp only [tabG, ↓reduceDIte]
  · intro j hj
    simp only [tabG, dif_neg (Ne.symm hj), DistributiveAllegory.zero_comp]

/-! ### Conjunct 4: `f ≫ f° ∩ g ≫ g° = id`. -/

theorem tab_orthonormal {X Y : MatObj 𝒜} (M : MatHom X Y) :
    matInter (matComp (tabF M) (matRecip (tabF M)))
             (matComp (tabG M) (matRecip (tabG M))) = matId (tabApex M) := by
  funext k k'
  by_cases hk : k = k'
  · subst hk
    simp only [matInter, tabFFr_diag, tabGGr_diag, matId, ↓reduceDIte]
    exact (entryTab M (unpairFst k) (unpairSnd k)).2.choose_spec.choose_spec.2.2.2
  · simp only [matInter, matId, dif_neg hk]
    by_cases hf : unpairFst k = unpairFst k'
    · have hs : unpairSnd k ≠ unpairSnd k' := fun e => hk (index_unique hf e)
      rw [tabGGr_off M hs]; exact le_antisymm (inter_lb_right _ _) (zero_le _)
    · rw [tabFFr_off M hf, zero_inter]

/-! ### Conjuncts 1,2: `Map f`, `Map g`. -/

theorem matDom_eq {X Y : MatObj 𝒜} (R : X ⟶ Y) :
    dom R = matInter (matId X) (matComp R (matRecip R)) := rfl

theorem tabF_entire {X Y : MatObj 𝒜} (M : MatHom X Y) :
    Entire (𝒜 := MatObj 𝒜) (tabF M) := by
  rw [Entire, matDom_eq]; show _ = matId (tabApex M); funext k k'
  by_cases hk : k = k'
  · subst hk
    simp only [matInter, tabFFr_diag, matId, ↓reduceDIte]
    exact (entryTab M (unpairFst k) (unpairSnd k)).2.choose_spec.choose_spec.1.1
  · simp only [matInter, matId, dif_neg hk, zero_inter]

theorem tabG_entire {X Y : MatObj 𝒜} (M : MatHom X Y) :
    Entire (𝒜 := MatObj 𝒜) (tabG M) := by
  rw [Entire, matDom_eq]; show _ = matId (tabApex M); funext k k'
  by_cases hk : k = k'
  · subst hk
    simp only [matInter, tabGGr_diag, matId, ↓reduceDIte]
    exact (entryTab M (unpairFst k) (unpairSnd k)).2.choose_spec.choose_spec.2.1.1
  · simp only [matInter, matId, dif_neg hk, zero_inter]

/-- `(f° ≫ f) i i' = ⨆_k (tabF k i)° ≫ (tabF k i')`: supported where `uFst k = i = i'`;
    on the diagonal each term is `(tabP)° ≫ (tabP) ⊑ id` (`tabP` simple), so the join is `⊑ id`. -/
theorem tabFrF_entry_le {X Y : MatObj 𝒜} (M : MatHom X Y) (i i' : Fin X.n) :
    matComp (matRecip (tabF M)) (tabF M) i i' ⊑ matId X i i' := by
  simp only [matComp, matRecip]
  by_cases hii : i = i'
  · subst hii
    simp only [matId, ↓reduceDIte]
    refine listJoin'_le (fun x hx => ?_); obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    by_cases hi : unpairFst k = i
    · simp only [tabF, dif_pos hi]
      rw [idxCast_recip_comp hi hi]
      have hsim : Simple (tabP M (unpairFst k) (unpairSnd k)) :=
        (entryTab M (unpairFst k) (unpairSnd k)).2.choose_spec.choose_spec.1.2
      generalize tabP M (unpairFst k) (unpairSnd k) = P at *
      cases hi; simpa using hsim
    · simp only [tabF, dif_neg hi, recip_zero, DistributiveAllegory.zero_comp]; exact zero_le _
  · simp only [matId, dif_neg hii]
    rw [finJoin_zero_all]; · exact zero_le _
    intro k
    by_cases hi : unpairFst k = i
    · have hi' : unpairFst k ≠ i' := fun e => hii (hi.symm.trans e)
      simp only [tabF, dif_neg hi', DistributiveAllegory.comp_zero]
    · simp only [tabF, dif_neg hi, recip_zero, DistributiveAllegory.zero_comp]

theorem tabGrG_entry_le {X Y : MatObj 𝒜} (M : MatHom X Y) (i i' : Fin Y.n) :
    matComp (matRecip (tabG M)) (tabG M) i i' ⊑ matId Y i i' := by
  simp only [matComp, matRecip]
  by_cases hii : i = i'
  · subst hii
    simp only [matId, ↓reduceDIte]
    refine listJoin'_le (fun x hx => ?_); obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    by_cases hi : unpairSnd k = i
    · simp only [tabG, dif_pos hi]
      rw [idxCast_recip_comp hi hi]
      have hsim : Simple (tabQ M (unpairFst k) (unpairSnd k)) :=
        (entryTab M (unpairFst k) (unpairSnd k)).2.choose_spec.choose_spec.2.1.2
      generalize tabQ M (unpairFst k) (unpairSnd k) = Q at *
      cases hi; simpa using hsim
    · simp only [tabG, dif_neg hi, recip_zero, DistributiveAllegory.zero_comp]; exact zero_le _
  · simp only [matId, dif_neg hii]
    rw [finJoin_zero_all]; · exact zero_le _
    intro k
    by_cases hi : unpairSnd k = i
    · have hi' : unpairSnd k ≠ i' := fun e => hii (hi.symm.trans e)
      simp only [tabG, dif_neg hi', DistributiveAllegory.comp_zero]
    · simp only [tabG, dif_neg hi, recip_zero, DistributiveAllegory.zero_comp]

theorem tabF_simple {X Y : MatObj 𝒜} (M : MatHom X Y) :
    Simple (𝒜 := MatObj 𝒜) (tabF M) := by funext i i'; exact tabFrF_entry_le M i i'
theorem tabG_simple {X Y : MatObj 𝒜} (M : MatHom X Y) :
    Simple (𝒜 := MatObj 𝒜) (tabG M) := by funext i i'; exact tabGrG_entry_le M i i'

theorem tabF_map {X Y : MatObj 𝒜} (M : MatHom X Y) : Map (𝒜 := MatObj 𝒜) (tabF M) :=
  ⟨tabF_entire M, tabF_simple M⟩
theorem tabG_map {X Y : MatObj 𝒜} (M : MatHom X Y) : Map (𝒜 := MatObj 𝒜) (tabG M) :=
  ⟨tabG_entire M, tabG_simple M⟩

/-- §2.342: every matrix morphism is tabular; apex = `⊕_{i,j} c i j`, legs `tabF`, `tabG`. -/
theorem mat_tabular {X Y : MatObj 𝒜} (M : MatHom X Y) : Tabular (𝒜 := MatObj 𝒜) M :=
  ⟨tabApex M, tabF M, tabG M,
    tabF_map M, tabG_map M, (tab_recipF_comp_G M).symm, tab_orthonormal M⟩

/-- §2.342: `Mat 𝒜` is a tabular allegory when 𝒜 is. -/
noncomputable instance instTabularAllegoryMat : TabularAllegory (MatObj 𝒜) :=
  { instAllegoryMat with tabular := fun R => mat_tabular R }

end MatTabular

/-! ## §L  Unitarity of `Mat 𝒜`  (§2.342)

  If 𝒜 is unitary (unit `λ`), so is `Mat 𝒜`: the unit object is the 1×1 matrix `[λ]`.
  `PartialUnit [λ]` reduces to `PartialUnit λ` (a `[λ]⟶[λ]` matrix is a single `λ⟶λ`).
  Entire-to-unit: for any `m = (αᵢ)`, the single-column matrix of the entire base morphisms
  `αᵢ ⟶ λ` is entire. -/

section MatUnitary

/-- A combined `Unitary`+`Distributive` allegory: one merged `Allegory` parent (so the matrix
    construction over `DistributiveAllegory` and the base unit live on the same `Allegory 𝒜`).
    This is the §2.342 hypothesis for unitarity of `Mat 𝒜`. -/
class UnitaryDistributiveAllegory (𝒜 : Type u) extends UnitaryAllegory 𝒜, DistributiveAllegory 𝒜

variable {𝒜 : Type u} [UnitaryDistributiveAllegory 𝒜]

/-- The unit object of `Mat 𝒜`: the 1×1 matrix on the base unit `λ`. -/
def matUnitObj : MatObj 𝒜 := unitObj (UnitaryAllegory.unit_obj (𝒜 := 𝒜))

theorem matPartialUnit : PartialUnit (𝒜 := MatObj 𝒜) matUnitObj := by
  intro R
  obtain ⟨hPU, _⟩ := UnitaryAllegory.unit_prop (𝒜 := 𝒜)
  funext i j
  show (matInter R (matId matUnitObj)) i j = R i j
  have hi : i = ⟨0, Nat.zero_lt_one⟩ := Fin.fin_one_eq_zero i
  have hj : j = ⟨0, Nat.zero_lt_one⟩ := Fin.fin_one_eq_zero j
  subst hi; subst hj
  simp only [matInter, matId, matUnitObj, unitObj, ↓reduceDIte]
  exact hPU _

/-- For any `Mat 𝒜` object `m`, the single-column matrix of entire base morphisms
    `m.objs i ⟶ λ` is entire. -/
theorem matEntireToUnit (m : MatObj 𝒜) :
    ∃ (R : m ⟶ matUnitObj), Entire (𝒜 := MatObj 𝒜) R := by
  obtain ⟨_, hEnt⟩ := UnitaryAllegory.unit_prop (𝒜 := 𝒜)
  let r : (i : Fin m.n) → (m.objs i ⟶ UnitaryAllegory.unit_obj (𝒜 := 𝒜)) :=
    fun i => (hEnt (m.objs i)).choose
  have hr : ∀ i, Entire (r i) := fun i => (hEnt (m.objs i)).choose_spec
  let R : MatHom m matUnitObj := fun i _j => r i
  refine ⟨R, ?_⟩
  rw [Entire]; show _ = matId m; funext i i'
  show (matInter (matId m) (matComp R (matRecip R))) i i' = _
  by_cases hii : i = i'
  · subst hii
    simp only [matInter, matComp, matRecip, matId, ↓reduceDIte, R,
      finJoin, List.ofFn_succ, List.ofFn_zero, listJoin'_cons, listJoin'_nil, union_zero]
    exact hr i
  · simp only [matInter, matId, dif_neg hii, zero_inter]

theorem matIsUnit : IsUnit (𝒜 := MatObj 𝒜) matUnitObj :=
  ⟨matPartialUnit, fun m => matEntireToUnit m⟩

/-- §2.342: `Mat 𝒜` is a unitary allegory when 𝒜 is. -/
noncomputable instance instUnitaryAllegoryMat : UnitaryAllegory (MatObj 𝒜) :=
  { instAllegoryMat with
    unit_obj := matUnitObj
    unit_prop := matIsUnit }

end MatUnitary

/-! ## §I  Summary
  §2.216  Allegory (MatObj 𝒜)               : instAllegoryMat             [PROVED]
  §2.216  DistributiveAllegory (MatObj 𝒜)   : instDistributiveAllegoryMat [PROVED]
  §2.342  DivisionAllegory (MatObj 𝒜)       : instDivisionAllegoryMat     [PROVED]
  §2.215  PositiveAllegory (MatObj 𝒜)       : instPositiveAllegoryMat     [PROVED]
  §2.342  TabularAllegory (MatObj 𝒜)        : instTabularAllegoryMat      [PROVED]
                                              ([TabularDistributiveAllegory 𝒜])
  §2.342  UnitaryAllegory (MatObj 𝒜)        : instUnitaryAllegoryMat      [PROVED]
                                              ([UnitaryDistributiveAllegory 𝒜])
  embed1 : 𝒜 → MatObj 𝒜 : faithful, preserves ≫, °, ∩, ∪, 𝟘, /  [PROVED]
-/

end Freyd.Alg.Mat
