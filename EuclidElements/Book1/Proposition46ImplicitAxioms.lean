import EuclidElements.Book1.Proposition34

namespace Euclid.Book1

open Euclid

/--
Construction data for I.46: erect a perpendicular at A, copy AB onto it, and
draw the two parallels.  The result is a right-angled parallelogram with
AB congruent to DA; I.34 supplies the remaining side equalities.
-/
class Proposition46ImplicitAxioms (G : Geometry) : Prop where
  squareFrame : ∀ {A B : G.Point},
    A ≠ B →
    ∃ C D : G.Point,
      IsQuadrilateral G A B C D ∧
      Parallelogram G A B C D ∧
      G.segmentCongruent A B D A ∧
      RightAngledQuadrilateral G A B C D

end Euclid.Book1
