import EuclidElements.Book3.TangentConstructionFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Euclid III.18: the radius drawn to the point of contact is perpendicular
    to the tangent. -/
theorem proposition18
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    [CircleOrderGeometry G]
    [TC : TangentConverseFoundations G]
    {c : G.Circle} {O A : G.Point} {tangent : G.Line}
    (hcenter : G.isCenter c O)
    (htan : TangentAt G c tangent A) :
    exists radius : G.Line,
      G.onLine O radius ∧ G.onLine A radius ∧
      Perpendicular G tangent radius := by
  have hOoff : ¬ G.onLine O tangent := TC.centerOffTangent hcenter htan
  obtain ⟨F, radius, hFt, hOr, hFr, hperp⟩ :=
    proposition12 G tangent O hOoff
  have hFA : F = A := by
    by_cases h : F = A
    · exact h
    · have hinside : InsideCircle G F c :=
        TC.perpendicularFootInsideUnlessContact hcenter htan hFt hOr hFr hperp h
      obtain ⟨X, hXA, hXc, hXt⟩ :=
        TC.lineThroughInteriorHasOtherBoundaryPoint htan hinside hFt
      have hEq : X = A := htan.2.2 X hXc hXt
      exact False.elim (hXA hEq)
  subst F
  exact ⟨radius, hOr, hFr, hperp⟩

end Euclid.Book3
