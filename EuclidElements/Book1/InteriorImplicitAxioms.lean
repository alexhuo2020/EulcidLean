import EuclidElements.Book1.SegmentArithmeticImplicitAxioms

namespace Euclid.Book1

open Euclid

class InteriorImplicitAxioms
    (G : Geometry)
    [TriangleInteriorGeometry G] : Prop where
  cevianIntersection : ∀ {A B C D : G.Point},
    IsTriangle G A B C → InsideTriangle G A B C D →
    ∃ E : G.Point,
      G.between A E C ∧ G.between B D E ∧
      IsTriangle G A B E ∧ IsTriangle G E D C

end Euclid.Book1
