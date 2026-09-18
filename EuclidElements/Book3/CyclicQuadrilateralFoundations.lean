import EuclidElements.Book3.Proposition21

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Diagram/arc data for four points in cyclic order.  This class only records
    which selected arcs the relevant inscribed angles stand on and that the
    diagonal through D splits its interior angle; the supplementary conclusion
    of III.22 is not assumed. -/
class CyclicQuadrilateralFoundations
    (G : Geometry)
    [AngleInteriorGeometry G]
    [AngleArcGeometry G] : Prop where
  data : forall
    {c : G.Circle} {A B C D : G.Point},
    G.onCircle A c -> G.onCircle B c ->
    G.onCircle C c -> G.onCircle D c ->
    IsQuadrilateral G A B C D ->
    exists sBC sAB : ArcRef G,
      ArcOn G sBC c B C ∧
      StandsOnArc G ⟨B, A, C⟩ sBC ∧
      StandsOnArc G ⟨B, D, C⟩ sBC ∧
      ArcOn G sAB c A B ∧
      StandsOnArc G ⟨A, C, B⟩ sAB ∧
      StandsOnArc G ⟨A, D, B⟩ sAB ∧
      InsideAngle G A D C B ∧
      IsTriangle G A B C ∧
      IsTriangle G B D C ∧
      IsTriangle G A D B

end Euclid.Book3
