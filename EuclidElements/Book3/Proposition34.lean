import EuclidElements.Book3.SegmentConstructionFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Euclid III.34: cut from a given circle a segment admitting a given
    rectilinear angle. -/
theorem proposition34
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
    {c : G.Circle} {O : G.Point} {α : Angle G.Point}
    (hO : G.isCenter c O) (hα : ValidAngle G α) :
    exists A B C : G.Point,
      G.onCircle A c ∧ G.onCircle B c ∧ G.onCircle C c ∧
      B ≠ C ∧ G.angleCongruent ⟨B, A, C⟩ α := by
  obtain ⟨B, C, t, hB, hC, hBC, htan, hcopy⟩ :=
    SC.cutFromGivenCircle hO hα
  obtain ⟨A, X, E, F, hA, hX, hEt, hFt, hFBC_BAC, _⟩ :=
    proposition32 G hO htan hC hBC
  have hFα : G.angleCongruent ⟨F, B, C⟩ α := hcopy F hFt
  have hBACα : G.angleCongruent ⟨B, A, C⟩ α :=
    I.angleTrans (I.angleSymm hFBC_BAC) hFα
  exact ⟨A, B, C, hA, hB, hC, hBC, hBACα⟩

end Euclid.Book3
