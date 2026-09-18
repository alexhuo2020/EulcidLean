import EuclidElements.Book1.Proposition03
import EuclidElements.Book1.Proposition05
import EuclidElements.Book1.Proposition16

/-!
# Euclid I.18 -- the greater side subtends the greater angle
-/

namespace Euclid.Book1

open Euclid

theorem proposition18
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [Proposition16ImplicitAxioms G]
    {A B C : G.Point}
    (htri : IsTriangle G A B C)
    (hABltAC : SegmentLess G A B A C) :
    G.angleLess ⟨B, C, A⟩ ⟨A, B, C⟩ := by
  have hAB : A ≠ B := htri.1
  obtain ⟨D, hADC, hAD_AB⟩ := proposition3 G A C A B hAB hABltAC

  obtain ⟨hBADtri, hBCDtri⟩ := L.trianglesFromSidePoint (L.triangleSwap23 htri) hADC
  have hADBtri : IsTriangle G A D B := L.triangleCycle hBADtri
  have hisoAngles := proposition5_baseAngles G hADBtri hAD_AB
  have hADB_BDA : G.angleCongruent ⟨A, D, B⟩ ⟨B, D, A⟩ := L.angleReverse A D B
  have hBDA_DBA : G.angleCongruent ⟨B, D, A⟩ ⟨D, B, A⟩ :=
    I.angleTrans (I.angleSymm hADB_BDA) hisoAngles

  have hCDA : G.between C D A := L.betweenSymm hADC
  have hext := proposition16 G hBCDtri hCDA
  have hBCD_BDA : G.angleLess ⟨B, C, D⟩ ⟨B, D, A⟩ := hext.2
  have hBCD_DBA : G.angleLess ⟨B, C, D⟩ ⟨D, B, A⟩ :=
    AO.lt_congr_right hBDA_DBA hBCD_BDA

  have hCneA : C ≠ A := htri.2.2.1
  have hCneD : C ≠ D := Ne.symm (I.betweenDistinct hADC).2.1
  have hrayCAD : SameRay G C A D :=
    ⟨hCneA, hCneD, Or.inr (Or.inr hCDA)⟩
  have hBCA_BCD : G.angleCongruent ⟨B, C, A⟩ ⟨B, C, D⟩ :=
    L.angleSameRayRight hrayCAD
  have hBCA_DBA : G.angleLess ⟨B, C, A⟩ ⟨D, B, A⟩ :=
    AO.lt_congr_left (I.angleSymm hBCA_BCD) hBCD_DBA

  have hins : InsideAngle G A B C D := AO.sidePointInsideOppositeAngle htri hADC
  have hABD_ABC : G.angleLess ⟨A, B, D⟩ ⟨A, B, C⟩ := AO.properSubangleLeft hins
  have hDBA_ABC : G.angleLess ⟨D, B, A⟩ ⟨A, B, C⟩ :=
    AO.lt_congr_left (L.angleReverse A B D) hABD_ABC
  exact AO.lt_trans hBCA_DBA hDBA_ABC

end Euclid.Book1
