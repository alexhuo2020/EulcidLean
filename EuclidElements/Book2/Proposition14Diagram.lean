import EuclidElements.Book2.Proposition13
import EuclidElements.Book1.Proposition45

namespace Euclid.Book2

open Euclid
open Euclid.Book1

/-- Geometry-only data for Euclid II.14 after I.45 has reduced the given figure
to a right-angled parallelogram.  In the unequal-side case this is Euclid's
midpoint/semicircle construction.  No area equality is a field. -/
class Proposition14DiagramAxioms (G : Geometry) : Prop where
  rightAngleWitness : ∃ α : Angle G.Point, ValidAngle G α ∧ RightAngle G α

  rectangleCase : ∀ {A B C D : G.Point},
    Parallelogram G A B C D → RightAngle G ⟨D, A, B⟩ →
    G.segmentCongruent A B A D ∨
    ∃ X H Y Z Q : G.Point,
      IsMidpoint G H X Z ∧
      G.between X H Y ∧
      G.between H Y Z ∧
      ((G.segmentCongruent X Y A B ∧ G.segmentCongruent Y Z A D) ∨
       (G.segmentCongruent X Y A D ∧ G.segmentCongruent Y Z A B)) ∧
      IsTriangle G Y H Q ∧
      RightAngle G ⟨H, Y, Q⟩ ∧
      G.segmentCongruent H Q H Z

end Euclid.Book2
