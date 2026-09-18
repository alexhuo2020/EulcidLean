import EuclidElements.Book4.PentagonConstructionFoundations

namespace Euclid.Book4

open Euclid
open Euclid.Book1
open Euclid.Book3

/-- Euclid IV.10: construct an isosceles triangle whose base angles are each
    double the remaining angle. -/
theorem proposition10
    (G : Geometry)
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleInteriorGeometry G]
    [AngleSumGeometry G]
    [AngleAdditionGeometry G]
    [AA : AngleAdditionImplicitAxioms G]
    [ALG : AngleSumAlgebraFoundations G]
    [C : GoldenTriangleConstructionAxioms G] :
    ∃ A B D : G.Point,
      IsTriangle G A B D ∧
      G.segmentCongruent A B A D ∧
      AngleDouble G ⟨D, A, B⟩ ⟨B, D, A⟩ ∧
      AngleDouble G ⟨D, A, B⟩ ⟨D, B, A⟩ := by
  obtain ⟨A, B, C0, D, hABD, hCAD, hAB_AD, hCA_CD,
      hBDC_DAC, hDAC_DAB, hBDA_BCD, hDBA_BCD, hsplit⟩ := C.frame
  have hCAD_ADC : G.angleCongruent ⟨C0, A, D⟩ ⟨A, D, C0⟩ :=
    proposition5_baseAngles G hCAD hCA_CD
  have hCDA_ADC : G.angleCongruent ⟨C0, D, A⟩ ⟨A, D, C0⟩ :=
    L.angleReverse C0 D A
  have hCAD_DAC : G.angleCongruent ⟨C0, A, D⟩ ⟨D, A, C0⟩ :=
    L.angleReverse C0 A D
  have hCDA_DAC : G.angleCongruent ⟨C0, D, A⟩ ⟨D, A, C0⟩ :=
    I.angleTrans hCDA_ADC (I.angleTrans (I.angleSymm hCAD_ADC) hCAD_DAC)
  have hBDC_DAB : G.angleCongruent ⟨B, D, C0⟩ ⟨D, A, B⟩ :=
    I.angleTrans hBDC_DAC hDAC_DAB
  have hCDA_DAB : G.angleCongruent ⟨C0, D, A⟩ ⟨D, A, B⟩ :=
    I.angleTrans hCDA_DAC hDAC_DAB
  have hdoubleD : AngleDouble G ⟨D, A, B⟩ ⟨B, D, A⟩ :=
    AA.sumCongr (I.angleSymm hBDC_DAB) (I.angleSymm hCDA_DAB) hsplit
  have hBDA_DBA : G.angleCongruent ⟨B, D, A⟩ ⟨D, B, A⟩ :=
    I.angleTrans hBDA_BCD (I.angleSymm hDBA_BCD)
  have hdoubleB : AngleDouble G ⟨D, A, B⟩ ⟨D, B, A⟩ :=
    ALG.resultCongr hdoubleD hBDA_DBA
  exact ⟨A, B, D, hABD, hAB_AD, hdoubleD, hdoubleB⟩

end Euclid.Book4
