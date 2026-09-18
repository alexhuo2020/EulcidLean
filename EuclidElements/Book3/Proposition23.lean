import EuclidElements.Book3.CircleSegmentFoundations
import EuclidElements.Book1.Proposition16

namespace Euclid.Book3

open Euclid
open Euclid.Book1

private theorem proposition23_firstNesting
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [P16 : Proposition16ImplicitAxioms G]
    {A B C D : G.Point}
    (hACD : G.between A C D)
    (htri : IsTriangle G B D C)
    (hsim : G.angleCongruent ⟨A, C, B⟩ ⟨A, D, B⟩) : False := by
  have hDCA : G.between D C A := L.betweenSymm hACD
  have hless : G.angleLess ⟨B, D, C⟩ ⟨B, C, A⟩ :=
    (proposition16 G htri hDCA).2

  have hDneA : D ≠ A := (I.betweenDistinct hDCA).2.2
  have hDneC : D ≠ C := (I.betweenDistinct hDCA).1
  have hray : SameRay G D A C :=
    ⟨hDneA, hDneC, Or.inr (Or.inr hDCA)⟩
  have hADB_CDB : G.angleCongruent ⟨A, D, B⟩ ⟨C, D, B⟩ :=
    L.angleSameRayLeft hray
  have hCDB_BDC : G.angleCongruent ⟨C, D, B⟩ ⟨B, D, C⟩ :=
    L.angleReverse C D B
  have hACB_BDC : G.angleCongruent ⟨A, C, B⟩ ⟨B, D, C⟩ :=
    I.angleTrans (I.angleTrans hsim hADB_CDB) hCDB_BDC
  have hBDC_ACB : G.angleCongruent ⟨B, D, C⟩ ⟨A, C, B⟩ :=
    I.angleSymm hACB_BDC
  have hACB_BCA : G.angleCongruent ⟨A, C, B⟩ ⟨B, C, A⟩ :=
    L.angleReverse A C B
  have hEq : G.angleCongruent ⟨B, D, C⟩ ⟨B, C, A⟩ :=
    I.angleTrans hBDC_ACB hACB_BCA
  exact (AO.lt_not_congr hless) hEq

private theorem proposition23_secondNesting
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [P16 : Proposition16ImplicitAxioms G]
    {A B C D : G.Point}
    (hADC : G.between A D C)
    (htri : IsTriangle G B C D)
    (hsim : G.angleCongruent ⟨A, C, B⟩ ⟨A, D, B⟩) : False := by
  have hCDA : G.between C D A := L.betweenSymm hADC
  have hless : G.angleLess ⟨B, C, D⟩ ⟨B, D, A⟩ :=
    (proposition16 G htri hCDA).2

  have hCneA : C ≠ A := (I.betweenDistinct hCDA).2.2
  have hCneD : C ≠ D := (I.betweenDistinct hCDA).1
  have hray : SameRay G C A D :=
    ⟨hCneA, hCneD, Or.inr (Or.inr hCDA)⟩
  have hACB_DCB : G.angleCongruent ⟨A, C, B⟩ ⟨D, C, B⟩ :=
    L.angleSameRayLeft hray
  have hDCB_BCD : G.angleCongruent ⟨D, C, B⟩ ⟨B, C, D⟩ :=
    L.angleReverse D C B
  have hACB_BCD : G.angleCongruent ⟨A, C, B⟩ ⟨B, C, D⟩ :=
    I.angleTrans hACB_DCB hDCB_BCD
  have hBCD_ADB : G.angleCongruent ⟨B, C, D⟩ ⟨A, D, B⟩ :=
    I.angleTrans (I.angleSymm hACB_BCD) hsim
  have hADB_BDA : G.angleCongruent ⟨A, D, B⟩ ⟨B, D, A⟩ :=
    L.angleReverse A D B
  have hEq : G.angleCongruent ⟨B, C, D⟩ ⟨B, D, A⟩ :=
    I.angleTrans hBCD_ADB hADB_BDA
  exact (AO.lt_not_congr hless) hEq

/-- Euclid III.23: on the same chord and same side, similar circular segments
    cannot be unequal. -/
theorem proposition23
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [P16 : Proposition16ImplicitAxioms G]
    [CircleSegmentGeometry G]
    [N : SameBaseSegmentNestingAxioms G]
    {s t : SegmentRef G} {l : G.Line}
    (hs : ValidSegment G s)
    (ht : ValidSegment G t)
    (ha : t.a = s.a)
    (hb : t.b = s.b)
    (hal : G.onLine s.a l)
    (hbl : G.onLine s.b l)
    (hside : G.sameSide s.arcPoint t.arcPoint l)
    (hsim : SimilarSegments G s t) :
    SegmentRegionEq G s t := by
  by_cases heq : SegmentRegionEq G s t
  · exact heq
  · have hsim' : G.angleCongruent
        ⟨s.a, s.arcPoint, s.b⟩ ⟨s.a, t.arcPoint, s.b⟩ := by
      simpa [SimilarSegments, SegmentAngle, ha, hb] using hsim
    rcases N.nested hs ht ha hb hal hbl hside heq with hfirst | hsecond
    · exact False.elim
        (proposition23_firstNesting G hfirst.1 hfirst.2 hsim')
    · exact False.elim
        (proposition23_secondNesting G hsecond.1 hsecond.2 hsim')

end Euclid.Book3
