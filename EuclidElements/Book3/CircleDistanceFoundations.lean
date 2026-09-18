import EuclidElements.Book3.Proposition06
import EuclidElements.Book1.Proposition24

namespace Euclid.Book3

open Euclid
open Euclid.Book1

def NearerFarSide (G : Geometry) (O P X Y : G.Point) : Prop :=
  G.angleLess ⟨Y, O, P⟩ ⟨X, O, P⟩

def NearerNearSide (G : Geometry) (O P X Y : G.Point) : Prop :=
  G.angleLess ⟨X, O, P⟩ ⟨Y, O, P⟩

class CircleDistanceEndpointFoundations
    (G : Geometry) [SegmentOrder G] : Prop where
  insideTriangle : forall
    {c : G.Circle} {O A D F X : G.Point},
    G.isCenter c O -> IsDiameter G c A D ->
    G.between A F O -> G.onCircle X c -> X ≠ A -> X ≠ D ->
    IsTriangle G O X F

  outsideTriangle : forall
    {c : G.Circle} {O A Gp D X : G.Point},
    G.isCenter c O -> IsDiameter G c A Gp ->
    G.between O Gp D -> G.onCircle X c -> X ≠ A -> X ≠ Gp ->
    IsTriangle G O X D

  insideExtremes : forall
    {c : G.Circle} {O A D F X : G.Point},
    G.isCenter c O -> IsDiameter G c A D ->
    G.between A F O -> F ≠ O ->
    G.onCircle X c -> X ≠ A -> X ≠ D ->
    SegmentLess G F X F A ∧ SegmentLess G F D F X

  outsideExtremes : forall
    {c : G.Circle} {O A Gp D X : G.Point},
    G.isCenter c O -> IsDiameter G c A Gp ->
    G.between O Gp D ->
    G.onCircle X c -> X ≠ A -> X ≠ Gp ->
    SegmentLess G D X D A ∧ SegmentLess G D Gp D X

  insideMirror : forall
    {c : G.Circle} {O F X : G.Point},
    G.isCenter c O -> F ≠ O -> G.onCircle X c ->
    exists Y : G.Point,
      G.onCircle Y c ∧ Y ≠ X ∧
      G.segmentCongruent F X F Y ∧
      (forall K : G.Point, G.onCircle K c ->
        G.segmentCongruent F X F K -> K = X ∨ K = Y)

  outsideMirror : forall
    {c : G.Circle} {O D X : G.Point},
    G.isCenter c O -> G.onCircle X c ->
    exists Y : G.Point,
      G.onCircle Y c ∧ Y ≠ X ∧
      G.segmentCongruent D X D Y ∧
      (forall K : G.Point, G.onCircle K c ->
        G.segmentCongruent D X D K -> K = X ∨ K = Y)

theorem farSideDistanceMonotone
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
    {c : G.Circle} {O Pnt X Y : G.Point}
    (hO : G.isCenter c O)
    (hX : G.onCircle X c) (hY : G.onCircle Y c)
    (htriX : IsTriangle G O X Pnt)
    (htriY : IsTriangle G O Y Pnt)
    (hnear : NearerFarSide G O Pnt X Y) :
    SegmentLess G Pnt Y Pnt X := by
  have hrad : G.segmentCongruent O X O Y := CB.radiiCongruent hO hX hY
  have hOP : G.segmentCongruent O Pnt O Pnt := I.segmentRefl O Pnt
  have h0 : SegmentLess G Y Pnt X Pnt :=
    proposition24 G htriX htriY hrad hOP hnear
  have h1 : SegmentLess G Pnt Y X Pnt :=
    L.segmentLess_congr_left (I.segmentReverse Y Pnt) h0
  exact L.segmentLess_congr_right (I.segmentReverse X Pnt) h1

theorem nearSideDistanceMonotone
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
    {c : G.Circle} {O Pnt X Y : G.Point}
    (hO : G.isCenter c O)
    (hX : G.onCircle X c) (hY : G.onCircle Y c)
    (htriX : IsTriangle G O X Pnt)
    (htriY : IsTriangle G O Y Pnt)
    (hnear : NearerNearSide G O Pnt X Y) :
    SegmentLess G Pnt X Pnt Y := by
  have hrad : G.segmentCongruent O Y O X :=
    I.segmentSymm (CB.radiiCongruent hO hX hY)
  have hOP : G.segmentCongruent O Pnt O Pnt := I.segmentRefl O Pnt
  have h0 : SegmentLess G X Pnt Y Pnt :=
    proposition24 G htriY htriX hrad hOP hnear
  have h1 : SegmentLess G Pnt X Y Pnt :=
    L.segmentLess_congr_left (I.segmentReverse X Pnt) h0
  exact L.segmentLess_congr_right (I.segmentReverse Y Pnt) h1

end Euclid.Book3
