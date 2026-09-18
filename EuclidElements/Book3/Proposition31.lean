import EuclidElements.Book3.SemicircleAngleFoundations
import EuclidElements.Book1.Proposition17

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Thales' theorem, extracted as the first part of III.31 for later use. -/
theorem proposition31_semicircle
    (G : Geometry)
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleInteriorGeometry G]
    [AngleSumGeometry G]
    [AngleAdditionGeometry G]
    [AngleArcGeometry G]
    [AI : AngleImplicitAxioms G]
    [AA : AngleAdditionImplicitAxioms G]
    [P32 : Proposition32ImplicitAxioms G]
    [C0 : CircleBasicAxioms G]
    [CA : InscribedAngleCaseAxioms G]
    [ALG : AngleSumAlgebraFoundations G]
    [SA : SemicircleAngleArithmeticFoundations G]
    {s : ArcRef G} {c : G.Circle} {O A B C : G.Point}
    (hdiam : IsDiameter G c B C)
    (hO : G.isCenter c O)
    (hArc : ArcOn G s c B C)
    (hStand : StandsOnArc G ⟨B, A, C⟩ s)
    (hA : G.onCircle A c)
    (hB : G.onCircle B c)
    (hC : G.onCircle C c)
    (htri : IsTriangle G B A C) :
    RightAngle G ⟨B, A, C⟩ := by
  have hdouble := proposition20 G hArc hStand hO hA hB hC htri
  exact SA.halfDiameterAngleRight hdiam hO hdouble

/-- Euclid III.31, rectilinear-angle part.  The selected arc `s` is the
    semicircle from B to C containing A. -/
theorem proposition31
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [AngleSumGeometry G]
    [AngleAdditionGeometry G]
    [AngleArcGeometry G]
    [AI : AngleImplicitAxioms G]
    [AA : AngleAdditionImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [P16 : Proposition16ImplicitAxioms G]
    [P32 : Proposition32ImplicitAxioms G]
    [C0 : CircleBasicAxioms G]
    [CA : InscribedAngleCaseAxioms G]
    [ALG : AngleSumAlgebraFoundations G]
    [SA : SemicircleAngleArithmeticFoundations G]
    [TR : TwoRightAngleAlgebraFoundations G]
    [CQ : CyclicQuadrilateralFoundations G]
    {s : ArcRef G} {c : G.Circle} {O A B C D : G.Point}
    (hdiam : IsDiameter G c B C)
    (hO : G.isCenter c O)
    (hArc : ArcOn G s c B C)
    (hStand : StandsOnArc G ⟨B, A, C⟩ s)
    (hA : G.onCircle A c)
    (hB : G.onCircle B c)
    (hC : G.onCircle C c)
    (hD : G.onCircle D c)
    (htri : IsTriangle G B A C)
    (hquad : IsQuadrilateral G A B C D) :
    RightAngle G ⟨B, A, C⟩ ∧
    AcuteAngle G ⟨A, B, C⟩ ∧
    ObtuseAngle G ⟨A, D, C⟩ := by
  have hright : RightAngle G ⟨B, A, C⟩ :=
    proposition31_semicircle G hdiam hO hArc hStand hA hB hC htri

  have hCBAtri : IsTriangle G C B A :=
    L.triangleCycle (L.triangleCycle htri)
  have hsum : G.sumLessThanTwoRight ⟨C, B, A⟩ ⟨B, A, C⟩ :=
    proposition17 G hCBAtri
  have hless0 : G.angleLess ⟨C, B, A⟩ ⟨B, A, C⟩ :=
    SA.rightComplementLess hsum hright
  have hrev : G.angleCongruent ⟨C, B, A⟩ ⟨A, B, C⟩ :=
    L.angleReverse C B A
  have hless : G.angleLess ⟨A, B, C⟩ ⟨B, A, C⟩ :=
    AO.lt_congr_left hrev hless0
  have hacute : AcuteAngle G ⟨A, B, C⟩ := ⟨⟨B, A, C⟩, hright, hless⟩

  have hsupp : Supplementary G ⟨A, B, C⟩ ⟨A, D, C⟩ :=
    proposition22 G hA hB hC hD hquad
  have hobtuse : ObtuseAngle G ⟨A, D, C⟩ :=
    SA.supplementOfAcuteObtuse hacute hsupp
  exact ⟨hright, hacute, hobtuse⟩

end Euclid.Book3
