import EuclidElements.Book3.Proposition31

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Pure angle algebra used in III.32. -/
class TangentChordAngleAlgebraFoundations
    (G : Geometry)
    [AngleAdditionGeometry G] : Prop where
  complementOfRight : forall
    {α ρ β R γ : Angle G.Point},
    ThreeAnglesTwoRight G α ρ β ->
    RightAngle G ρ -> RightAngle G R ->
    AngleSumEq G β γ R ->
    G.angleCongruent γ α

/-- Euclid's III.32 diagram after erecting the perpendicular at the contact.
    It supplies the diameter and cyclic-order incidence; the two tangent-chord
    angle equalities are not fields. -/
class TangentChordDiagramAxioms
    (G : Geometry)
    [AngleInteriorGeometry G]
    [AngleArcGeometry G] : Prop where
  diagram : forall
    {c : G.Circle} {O B D : G.Point} {tangent : G.Line},
    G.isCenter c O -> TangentAt G c tangent B ->
    G.onCircle D c -> B ≠ D ->
    exists A C E F : G.Point, exists semi : ArcRef G,
      G.onCircle A c ∧ G.onCircle C c ∧
      IsDiameter G c A B ∧
      ArcOn G semi c A B ∧
      StandsOnArc G ⟨A, D, B⟩ semi ∧
      IsTriangle G A D B ∧
      G.onLine E tangent ∧ G.onLine F tangent ∧
      G.between E B F ∧
      RightAngle G ⟨A, B, F⟩ ∧
      InsideAngle G A B F D ∧
      (¬ G.Collinear E B D) ∧
      IsQuadrilateral G B A D C

end Euclid.Book3
