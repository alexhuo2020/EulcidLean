import EuclidElements.Book3.CircleDistanceFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Euclid III.8 with the ambiguous “nearer” relation replaced by explicit
    central-angle order on the far and near sides of the diameter. -/
theorem proposition8
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
    {c : G.Circle} {O A Gp D E F C K L H : G.Point}
    (hO : G.isCenter c O)
    (hdiam : IsDiameter G c A Gp)
    (hOGD : G.between O Gp D)
    (hE : G.onCircle E c) (hF : G.onCircle F c) (hC : G.onCircle C c)
    (hK : G.onCircle K c) (hL : G.onCircle L c) (hH : G.onCircle H c)
    (hEneA : E ≠ A) (hEneG : E ≠ Gp)
    (hFneA : F ≠ A) (hFneG : F ≠ Gp)
    (hCneA : C ≠ A) (hCneG : C ≠ Gp)
    (hKneA : K ≠ A) (hKneG : K ≠ Gp)
    (hLneA : L ≠ A) (hLneG : L ≠ Gp)
    (hHneA : H ≠ A) (hHneG : H ≠ Gp)
    (hnearEF : NearerFarSide G O D E F)
    (hnearFC : NearerFarSide G O D F C)
    (hnearKL : NearerNearSide G O D K L)
    (hnearLH : NearerNearSide G O D L H) :
    (forall X : G.Point,
      G.onCircle X c -> X ≠ A -> X ≠ Gp ->
      SegmentLess G D X D A ∧ SegmentLess G D Gp D X) ∧
    SegmentLess G D F D E ∧
    SegmentLess G D C D F ∧
    SegmentLess G D K D L ∧
    SegmentLess G D L D H ∧
    (exists Y : G.Point,
      G.onCircle Y c ∧ Y ≠ K ∧
      G.segmentCongruent D K D Y ∧
      (forall N : G.Point, G.onCircle N c ->
        G.segmentCongruent D K D N -> N = K ∨ N = Y)) := by
  have htriE : IsTriangle G O E D :=
    DF.outsideTriangle hO hdiam hOGD hE hEneA hEneG
  have htriF : IsTriangle G O F D :=
    DF.outsideTriangle hO hdiam hOGD hF hFneA hFneG
  have htriC : IsTriangle G O C D :=
    DF.outsideTriangle hO hdiam hOGD hC hCneA hCneG
  have htriK : IsTriangle G O K D :=
    DF.outsideTriangle hO hdiam hOGD hK hKneA hKneG
  have htriL : IsTriangle G O L D :=
    DF.outsideTriangle hO hdiam hOGD hL hLneA hLneG
  have htriH : IsTriangle G O H D :=
    DF.outsideTriangle hO hdiam hOGD hH hHneA hHneG
  have hEF : SegmentLess G D F D E :=
    farSideDistanceMonotone G hO hE hF htriE htriF hnearEF
  have hFC : SegmentLess G D C D F :=
    farSideDistanceMonotone G hO hF hC htriF htriC hnearFC
  have hKL : SegmentLess G D K D L :=
    nearSideDistanceMonotone G hO hK hL htriK htriL hnearKL
  have hLH : SegmentLess G D L D H :=
    nearSideDistanceMonotone G hO hL hH htriL htriH hnearLH
  refine ⟨?_, hEF, hFC, hKL, hLH, ?_⟩
  · intro X hX hXneA hXneG
    exact DF.outsideExtremes hO hdiam hOGD hX hXneA hXneG
  · exact DF.outsideMirror hO hK

end Euclid.Book3
