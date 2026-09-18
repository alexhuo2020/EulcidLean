import EuclidElements.Book3.CircleDistanceFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Euclid III.7 with “nearer to the line through the center” made precise by
    the central-angle order `NearerFarSide`. -/
theorem proposition7
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G] [SegmentSumGeometry G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G] [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [Proposition16ImplicitAxioms G]
    [SegmentArithmeticImplicitAxioms G]
    [TriangleConstructionImplicitAxioms G]
    [AngleRayConstructionAxioms G]
    [CB : CircleBasicAxioms G]
    [DF : CircleDistanceEndpointFoundations G]
    {c : G.Circle} {O A D F B C H : G.Point}
    (hO : G.isCenter c O)
    (hdiam : IsDiameter G c A D)
    (hAFO : G.between A F O)
    (hFneO : F ≠ O)
    (hB : G.onCircle B c) (hC : G.onCircle C c) (hH : G.onCircle H c)
    (hBneA : B ≠ A) (hBneD : B ≠ D)
    (hCneA : C ≠ A) (hCneD : C ≠ D)
    (hHneA : H ≠ A) (hHneD : H ≠ D)
    (hnearBC : NearerFarSide G O F B C)
    (hnearCH : NearerFarSide G O F C H) :
    (forall X : G.Point,
      G.onCircle X c -> X ≠ A -> X ≠ D ->
      SegmentLess G F X F A ∧ SegmentLess G F D F X) ∧
    SegmentLess G F C F B ∧
    SegmentLess G F H F C ∧
    (exists Y : G.Point,
      G.onCircle Y c ∧ Y ≠ H ∧
      G.segmentCongruent F H F Y ∧
      (forall K : G.Point, G.onCircle K c ->
        G.segmentCongruent F H F K -> K = H ∨ K = Y)) := by
  have htriB : IsTriangle G O B F :=
    DF.insideTriangle hO hdiam hAFO hB hBneA hBneD
  have htriC : IsTriangle G O C F :=
    DF.insideTriangle hO hdiam hAFO hC hCneA hCneD
  have htriH : IsTriangle G O H F :=
    DF.insideTriangle hO hdiam hAFO hH hHneA hHneD
  have hBC : SegmentLess G F C F B :=
    farSideDistanceMonotone G hO hB hC htriB htriC hnearBC
  have hCH : SegmentLess G F H F C :=
    farSideDistanceMonotone G hO hC hH htriC htriH hnearCH
  refine ⟨?_, hBC, hCH, ?_⟩
  · intro X hX hXneA hXneD
    exact DF.insideExtremes hO hdiam hAFO hFneO hX hXneA hXneD
  · exact DF.insideMirror hO hFneO hH

end Euclid.Book3
