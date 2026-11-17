/-
  freyd's reading of rel's syntactic category (`doc/rel-denotation-design.md` §4.1, decision D4 = G): the category laws
  `Rel.Lang.Syn` proves over `Core.Rel` as the `Cat Syn` instance, `⟦−⟧ρ` as a `Functor Syn RelSet`, and the §4.2
  rows whose right side is a field of a `RelSet` instance.
-/
import Rel.Lang.Syn
import RelAop.Core

namespace RelAop.Syn

open Freyd Freyd.Alg Freyd.Alg.RelSet
open Rel.Lang (Syn Tm Val)

instance : Cat Syn where
  Hom := Syn.Hom
  id := Syn.id
  comp := Syn.comp
  id_comp := Syn.id_comp
  comp_id := Syn.comp_id
  assoc := Syn.assoc

/-- `⟦−⟧ρ` as a functor into `Rel(Set)`: an object to the set of its elements, a hom to its meaning. -/
def den (ρ : Val) : Functor Syn RelSet.{0} where
  obj A := ⟨Rel.Obj.El A⟩
  map f := Syn.Hom.den ρ f
  map_id _ := rfl
  map_comp f g := Syn.Hom.den_comp ρ f g

variable {A B : Rel.Obj}

/-- `⟦π₁⟧` is the first projection of `RelSet`'s relational product. -/
theorem den_outl (ρ : Val) :
    (Tm.outl : Tm (.prod A B) A true).den ρ = (HasRelProd.relProd (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).π₁ := rfl

/-- `⟦π₂⟧` is the second projection of `RelSet`'s relational product. -/
theorem den_outr (ρ : Val) :
    (Tm.outr : Tm (.prod A B) B true).den ρ = (HasRelProd.relProd (⟨A.El⟩ : RelSet.{0}) ⟨B.El⟩).π₂ := rfl

end RelAop.Syn
