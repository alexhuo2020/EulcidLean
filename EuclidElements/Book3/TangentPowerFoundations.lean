import EuclidElements.Book3.Proposition35
import EuclidElements.Book3.Proposition18

namespace Euclid.Book3

open Euclid
open Euclid.Book1
open Euclid.Book2

class TangentPowerDiagramAxioms (G : Geometry) : Prop where
  rightTriangle : forall
    {c : G.Circle} {O B D : G.Point} {t radius : G.Line},
    G.isCenter c O -> TangentAt G c t B ->
    G.onLine D t -> D ≠ B ->
    G.onLine O radius -> G.onLine B radius ->
    Perpendicular G t radius ->
    IsTriangle G B O D ∧ RightAngle G ⟨O, B, D⟩

class SquareMagnitudeFaithful
    (G : Geometry) [AreaGeometry G] : Prop where
  segmentCongruentOfSquareEq : forall {A B C D : G.Point},
    Sq G A B = Sq G C D -> G.segmentCongruent A B C D

end Euclid.Book3
