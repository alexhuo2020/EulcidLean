import EuclidElements.Book3.Proposition30

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Generic angle arithmetic needed in III.31. -/
class SemicircleAngleArithmeticFoundations
    (G : Geometry)
    [AngleSumGeometry G]
    [AngleAdditionGeometry G] : Prop where
  halfDiameterAngleRight : forall
    {c : G.Circle} {O A B : G.Point} {α : Angle G.Point},
    IsDiameter G c A B -> G.isCenter c O ->
    AngleSumEq G α α ⟨A, O, B⟩ ->
    RightAngle G α

  rightComplementLess : forall {α ρ : Angle G.Point},
    G.sumLessThanTwoRight α ρ -> RightAngle G ρ ->
    G.angleLess α ρ

  supplementOfAcuteObtuse : forall {α β : Angle G.Point},
    AcuteAngle G α -> Supplementary G α β ->
    ObtuseAngle G β

/-- Euclid's final two boundary-angle comparisons in III.31 are immediate from
    the segment topology but are not ordinary rectilinear angle statements. -/
class BoundarySegmentComparisonFoundations
    (G : Geometry)
    [BoundaryAngleOrderGeometry G] : Prop where
  greaterSegmentBoundary : forall
    {s : SegmentRef G} {ρ : Angle G.Point},
    ValidSegment G s -> RightAngle G ρ ->
    BoundaryAngleGreater G ⟨s⟩ ρ

  lesserSegmentBoundary : forall
    {s : SegmentRef G} {ρ : Angle G.Point},
    ValidSegment G s -> RightAngle G ρ ->
    BoundaryAngleLess G ⟨s⟩ ρ

end Euclid.Book3
