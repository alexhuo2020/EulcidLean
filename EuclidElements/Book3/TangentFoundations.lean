import EuclidElements.Book3.Proposition15
import EuclidElements.Book1.Proposition17
import EuclidElements.Book1.PythagoreanFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Incidence/angle facts for a line perpendicular to a radius at its endpoint. -/
class TangentLineFoundations (G : Geometry) : Prop where
  triangleFromPerpendicularEndpoint : forall
    {c : G.Circle} {O A X : G.Point} {radius tangent : G.Line},
    G.isCenter c O -> G.onCircle A c ->
    G.onLine O radius -> G.onLine A radius ->
    G.onLine A tangent -> G.onLine X tangent ->
    Perpendicular G radius tangent -> X ≠ A ->
    IsTriangle G O A X ∧ RightAngle G ⟨O, A, X⟩

/-- Two right angles cannot have sum strictly less than two right angles. -/
class RightAngleSumFoundations (G : Geometry) : Prop where
  notSumLessTwoRight : forall {α β : Angle G.Point},
    RightAngle G α -> RightAngle G β ->
    ¬ G.sumLessThanTwoRight α β

end Euclid.Book3
