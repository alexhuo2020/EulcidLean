import EuclidElements.Book3.SegmentConstructionFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Euclid III.33: on a given straight line describe a circular segment
    admitting a given rectilinear angle. -/
theorem proposition33
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
    [TC : TangentChordAngleAlgebraFoundations G]
    [TD : TangentChordDiagramAxioms G]
    [SC : SegmentConstructionAxioms G]
    {A B : G.Point} {α : Angle G.Point}
    (hAB : A ≠ B) (hα : ValidAngle G α) :
    exists c : G.Circle, exists X : G.Point,
      G.onCircle A c ∧ G.onCircle B c ∧ G.onCircle X c ∧
      G.angleCongruent ⟨A, X, B⟩ α := by
  obtain ⟨c, O, t, hO, hA, hB, htan, hcopy⟩ :=
    SC.onGivenBase hAB hα
  obtain ⟨X, Y, E, F, hX, hY, hEt, hFt, hF_AB_AXB, _⟩ :=
    proposition32 G hO htan hB hAB
  have hFα : G.angleCongruent ⟨F, A, B⟩ α := hcopy F hFt
  have hAXBα : G.angleCongruent ⟨A, X, B⟩ α :=
    I.angleTrans (I.angleSymm hF_AB_AXB) hFα
  exact ⟨c, X, hA, hB, hX, hAXBα⟩

end Euclid.Book3
