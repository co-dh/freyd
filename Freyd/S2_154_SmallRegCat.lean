/-
  Freyd & Scedrov, *Categories, Allegories* §2.154.

  The small bundled regular categories used by the §2.154 equivalence.  This leaf module keeps the
  book-defined object importable by the earlier capitalization machinery without importing the
  later allegory construction back into Chapter 1.
-/
import Freyd.S1_52

namespace Freyd.S2_154

universe u



/-- **§2.154**: a SMALL REGULAR CATEGORY (bundled). -/
structure SmallRegCat : Type (u + 1) where
  carrier : Type u
  [cat : Cat.{u} carrier]
  [reg : RegularCategory carrier]

attribute [instance] SmallRegCat.cat SmallRegCat.reg

end Freyd.S2_154
