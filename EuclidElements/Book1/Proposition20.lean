import EuclidElements.Book1.Proposition05
import EuclidElements.Book1.Proposition19
import EuclidElements.Book1.SegmentArithmeticImplicitAxioms

/-!
# Euclid I.20 -- the sum of any two sides of a triangle is greater than the third
-/

namespace Euclid.Book1

open Euclid

theorem proposition20
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G]
    [SegmentSumGeometry G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [Proposition16ImplicitAxioms G]
    [SA : SegmentArithmeticImplicitAxioms G]
    {A B C : G.Point}
    (htri : IsTriangle G A B C) :
    SegmentSumGreater G B A A C B C := by
  have hBA : B ≠ A := Ne.symm htri.1
  have hAC : A ≠ C := Ne.symm htri.2.2.1
  obtain ⟨D, hBAD, hAD_AC⟩ := SA.extendByCongruent hBA hAC
  obtain ⟨hACDtri, hBCDtri⟩ := SA.extensionTriangles htri hBAD

  have hAC_AD : G.segmentCongruent A C A D := I.segmentSymm hAD_AC
  have hiso := proposition5_baseAngles G hACDtri hAC_AD
  have hACD_CDA : G.angleCongruent ⟨A, C, D⟩ ⟨C, D, A⟩ := hiso

  have hDAB : G.between D A B := L.betweenSymm hBAD
  have hDneA : D ≠ A := (I.betweenDistinct hDAB).1
  have hDneB : D ≠ B := (I.betweenDistinct hDAB).2.2
  have hrayDAB : SameRay G D A B :=
    ⟨hDneA, hDneB, Or.inr (Or.inl hDAB)⟩
  have hCDA_CDB : G.angleCongruent ⟨C, D, A⟩ ⟨C, D, B⟩ :=
    L.angleSameRayRight hrayDAB
  have hACD_CDB : G.angleCongruent ⟨A, C, D⟩ ⟨C, D, B⟩ :=
    I.angleTrans hACD_CDA hCDA_CDB

  have hins : InsideAngle G B C D A := AO.sidePointInsideOppositeAngle hBCDtri hBAD
  have hACD_BCD : G.angleLess ⟨A, C, D⟩ ⟨B, C, D⟩ :=
    AO.properSubangleRight hins
  have hCDB_BCD : G.angleLess ⟨C, D, B⟩ ⟨B, C, D⟩ :=
    AO.lt_congr_left hACD_CDB hACD_BCD

  have hBC_lt_BD : SegmentLess G B C B D :=
    proposition19 G hBCDtri hCDB_BCD
  exact SA.sumGreater_from_extension hBAD hAD_AC hBC_lt_BD

end Euclid.Book1
