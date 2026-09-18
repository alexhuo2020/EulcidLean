import EuclidElements.Book2.Proposition10

namespace Euclid.Book2

open Euclid
open Euclid.Book1

/-- Geometry-only perpendicular-foot constructions for the oblique-triangle
propositions II.12 and II.13. -/
class Proposition12_13DiagramAxioms (G : Geometry) : Prop where
  obtuseFoot : ∀ {A B C : G.Point},
    IsTriangle G A B C → ObtuseAngle G ⟨B, A, C⟩ →
    ∃ D : G.Point,
      G.between D A C ∧
      IsTriangle G D C B ∧ RightAngle G ⟨C, D, B⟩ ∧
      IsTriangle G D A B ∧ RightAngle G ⟨A, D, B⟩

  acuteFoot : ∀ {A B C : G.Point},
    IsTriangle G A B C → AcuteAngle G ⟨A, B, C⟩ →
    ∃ D : G.Point,
      G.between C D B ∧
      IsTriangle G D B A ∧ RightAngle G ⟨B, D, A⟩ ∧
      IsTriangle G D C A ∧ RightAngle G ⟨C, D, A⟩

end Euclid.Book2
