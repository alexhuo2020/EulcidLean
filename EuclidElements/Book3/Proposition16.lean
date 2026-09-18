import EuclidElements.Book3.TangentFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Euclid III.16 corollary: a line perpendicular to a radius at its endpoint
    touches the circle.  The uniqueness of the intersection is derived from
    equal radii, I.5 and I.17. -/
theorem proposition16_tangent
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AI : AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [P16 : Proposition16ImplicitAxioms G]
    [C : CircleBasicAxioms G]
    [TL : TangentLineFoundations G]
    [RA : RightAngleCongruenceAxioms G]
    [RS : RightAngleSumFoundations G]
    {c : G.Circle} {O A : G.Point} {radius tangent : G.Line}
    (hcenter : G.isCenter c O)
    (hA : G.onCircle A c)
    (hOr : G.onLine O radius)
    (hAr : G.onLine A radius)
    (hAt : G.onLine A tangent)
    (hperp : Perpendicular G radius tangent) :
    TangentAt G c tangent A := by
  refine ⟨hA, hAt, ?_⟩
  intro X hX hXt
  by_cases hXA : X = A
  · exact hXA
  · obtain ⟨htri, hrightA⟩ :=
      TL.triangleFromPerpendicularEndpoint hcenter hA hOr hAr hAt hXt hperp hXA
    have hrad : G.segmentCongruent O A O X := C.radiiCongruent hcenter hA hX
    have hbase : G.angleCongruent ⟨O, A, X⟩ ⟨A, X, O⟩ :=
      proposition5_baseAngles G htri hrad
    have hrightX : RightAngle G ⟨A, X, O⟩ :=
      RA.rightAngleOfCongruent (I.angleSymm hbase) hrightA
    have hlt : G.sumLessThanTwoRight ⟨O, A, X⟩ ⟨A, X, O⟩ :=
      proposition17 G htri
    exact False.elim ((RS.notSumLessTwoRight hrightA hrightX) hlt)

end Euclid.Book3
