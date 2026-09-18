import EuclidElements.Book3.TangentConstructionFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Euclid III.17: from an exterior point draw a tangent to the circle. -/
theorem proposition17
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
    [CircleOrderGeometry G]
    [EC : ExternalTangentConstructionAxioms G]
    {c : G.Circle} {O A : G.Point}
    (hcenter : G.isCenter c O)
    (hout : OutsideCircle G A c) :
    exists T : G.Point, exists l : G.Line,
      G.onLine A l ∧ TangentAt G c l T := by
  obtain ⟨T, radius, tangent, hT, hOr, hTr, hAt, hTt, hperp⟩ :=
    EC.construct hcenter hout
  have htangent : TangentAt G c tangent T :=
    proposition16_tangent G hcenter hT hOr hTr hTt hperp
  exact ⟨T, tangent, hAt, htangent⟩

end Euclid.Book3
