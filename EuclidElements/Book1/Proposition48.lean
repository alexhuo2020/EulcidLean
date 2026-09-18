import EuclidElements.Book1.Proposition46
import EuclidElements.Book1.Proposition47

/-!
# Euclid I.48 -- converse of the Pythagorean theorem
-/

namespace Euclid.Book1

open Euclid

theorem proposition48
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [D34 : Proposition34ImplicitAxioms G]
    [C46 : Proposition46ImplicitAxioms G]
    [LaterAreaGeometry G]
    [AF : AreaFoundations G]
    [QuadPartitionGeometry G]
    [AS : AreaSumFoundations G]
    [SF : SquareAreaFoundations G]
    [PD : PythagoreanDiagramAxioms G]
    [PC : PythagoreanConverseConstructionAxioms G]
    [RA : RightAngleCongruenceAxioms G]
    {A B C Pp Q R S T U : G.Point}
    (htri : IsTriangle G A B C)
    (hABsq : Square G A B Pp Q)
    (hACsq : Square G A C R S)
    (hBCsq : Square G B C T U)
    (hpyth : QuadAreaSumEq G A B Pp Q A C R S B C T U) :
    RightAngle G ⟨B, A, C⟩ := by
  obtain ⟨D, hADC, hrightDAC, hAD_AB⟩ :=
    PC.comparisonRightTriangle htri

  have hAneD : A ≠ D := hADC.1
  have hDneC : D ≠ C := hADC.2.1
  obtain ⟨J, K, hADsq⟩ := proposition46 G hAneD
  obtain ⟨V, W, hDCsq⟩ := proposition46 G hDneC

  have hrightSum : QuadAreaSumEq G A D J K A C R S D C V W :=
    proposition47 G hrightDAC hADsq hACsq hDCsq

  have hAB_AD : G.segmentCongruent A B A D := I.segmentSymm hAD_AB
  have hABsq_ADsq : QuadAreaEq G A B Pp Q A D J K :=
    SF.congruentSidesGiveEqualSquares hABsq hADsq hAB_AD
  have hACrefl : QuadAreaEq G A C R S A C R S := AS.quadEqRefl A C R S
  have hrightSum' : QuadAreaSumEq G A B Pp Q A C R S D C V W :=
    AS.sumCongr hABsq_ADsq hACrefl hrightSum

  have hBCsq_DCsq : QuadAreaEq G B C T U D C V W :=
    AS.sumCancelLeft hpyth hrightSum'
  have hBC_DC : G.segmentCongruent B C D C :=
    SF.equalSquaresGiveCongruentSides hBCsq hDCsq hBCsq_DCsq

  have hAC_AC : G.segmentCongruent A C A C := I.segmentRefl A C
  have hsss := L.sss htri hADC hAB_AD hAC_AC hBC_DC
  have hBAC_DAC : G.angleCongruent ⟨B, A, C⟩ ⟨D, A, C⟩ := hsss.1
  exact RA.rightAngleOfCongruent hBAC_DAC hrightDAC

end Euclid.Book1
