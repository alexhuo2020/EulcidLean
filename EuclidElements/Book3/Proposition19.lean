import EuclidElements.Book3.Proposition18

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Generic uniqueness of the perpendicular through a fixed point to a fixed line. -/
class PerpendicularThroughPointUniqueness (G : Geometry) : Prop where
  unique : forall {base l m : G.Line} {A : G.Point},
    G.onLine A l -> G.onLine A m ->
    Perpendicular G base l -> Perpendicular G base m ->
    l = m

/-- Euclid III.19: if a line is drawn from the point of contact perpendicular
    to the tangent, the center lies on that line. -/
theorem proposition19
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    [CircleOrderGeometry G]
    [TC : TangentConverseFoundations G]
    [U : PerpendicularThroughPointUniqueness G]
    {c : G.Circle} {O A : G.Point} {tangent l : G.Line}
    (hcenter : G.isCenter c O)
    (htan : TangentAt G c tangent A)
    (hAl : G.onLine A l)
    (hperp : Perpendicular G tangent l) :
    G.onLine O l := by
  obtain ⟨radius, hOr, hAr, hpr⟩ := proposition18 G hcenter htan
  have hEq : l = radius := U.unique hAl hAr hperp hpr
  simpa [hEq] using hOr

end Euclid.Book3
