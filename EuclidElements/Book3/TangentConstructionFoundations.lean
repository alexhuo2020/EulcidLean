import EuclidElements.Book3.Proposition16
import EuclidElements.Book1.Proposition12

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Geometry-only construction frame for Euclid III.17.  It supplies the
    auxiliary right-angle construction; tangency is still proved by III.16. -/
class ExternalTangentConstructionAxioms
    (G : Geometry) [CircleOrderGeometry G] : Prop where
  construct : forall {c : G.Circle} {O A : G.Point},
    G.isCenter c O -> OutsideCircle G A c ->
    exists T : G.Point, exists radius tangent : G.Line,
      G.onCircle T c ∧
      G.onLine O radius ∧ G.onLine T radius ∧
      G.onLine A tangent ∧ G.onLine T tangent ∧
      Perpendicular G radius tangent

/-- Generic circle-order facts used in the converse tangent theorem III.18. -/
class TangentConverseFoundations
    (G : Geometry) [CircleOrderGeometry G] : Prop where
  centerOffTangent : forall {c : G.Circle} {O A : G.Point} {l : G.Line},
    G.isCenter c O -> TangentAt G c l A -> ¬ G.onLine O l

  perpendicularFootInsideUnlessContact : forall
    {c : G.Circle} {O A F : G.Point} {l m : G.Line},
    G.isCenter c O -> TangentAt G c l A ->
    G.onLine F l -> G.onLine O m -> G.onLine F m ->
    Perpendicular G l m -> F ≠ A ->
    InsideCircle G F c

  lineThroughInteriorHasOtherBoundaryPoint : forall
    {c : G.Circle} {A F : G.Point} {l : G.Line},
    TangentAt G c l A -> InsideCircle G F c -> G.onLine F l ->
    exists X : G.Point, X ≠ A ∧ G.onCircle X c ∧ G.onLine X l

end Euclid.Book3
