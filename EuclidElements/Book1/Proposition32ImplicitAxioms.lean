import EuclidElements.Book1.Proposition31
import EuclidElements.Book1.Proposition29
import EuclidElements.Book1.AngleAdditionGeometry

namespace Euclid.Book1

open Euclid

/--
Local diagram extracted from Euclid I.32 after drawing through C a line parallel
to AB (I.31) and applying I.29.  The point E lies inside the exterior angle
ACD and the two subangles copy the two remote interior angles.
-/
class Proposition32ImplicitAxioms
    (G : Geometry)
    [AngleInteriorGeometry G] : Prop where
  parallelAtVertexDiagram : ∀ {A B C D : G.Point},
    IsTriangle G A B C → G.between B C D →
    ∃ E : G.Point,
      InsideAngle G A C D E ∧
      G.angleCongruent ⟨B, A, C⟩ ⟨A, C, E⟩ ∧
      G.angleCongruent ⟨A, B, C⟩ ⟨E, C, D⟩

end Euclid.Book1
