import EuclidElements.Book1.Proposition41
import EuclidElements.Book1.PythagoreanFoundations

/-!
# Euclid I.47 -- Pythagorean theorem

The proof is the synthetic dissection proof: the two squares on the legs are
shown equal to two parallelogram pieces, and those pieces partition the square
on the hypotenuse.
-/

namespace Euclid.Book1

open Euclid

theorem proposition47
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
    [LaterAreaGeometry G]
    [AF : AreaFoundations G]
    [QuadPartitionGeometry G]
    [AS : AreaSumFoundations G]
    [SF : SquareAreaFoundations G]
    [PD : PythagoreanDiagramAxioms G]
    {A B C Pp Q R S T U : G.Point}
    (hright : RightAngle G ⟨B, A, C⟩)
    (hABsq : Square G A B Pp Q)
    (hACsq : Square G A C R S)
    (hBCsq : Square G B C T U) :
    QuadAreaSumEq G A B Pp Q A C R S B C T U := by
  obtain ⟨X1, X2, X3, X4, Y1, Y2, Y3, Y4,
    hXpara, hYpara, hXtri, hYtri,
    hAB_X12, hAP_X13, hBP_X23,
    hAC_Y12, hAR_Y13, hCR_Y23, hpartition⟩ :=
    PD.dissection hright hABsq hACsq hBCsq

  have hABtri : IsTriangle G A B Pp := SF.squareFirstTriangle hABsq
  have hACtri : IsTriangle G A C R := SF.squareFirstTriangle hACsq
  have hABpara : Parallelogram G A B Pp Q := SF.squareParallelogram hABsq
  have hACpara : Parallelogram G A C R S := SF.squareParallelogram hACsq

  have hABhalf_Xhalf : TriangleAreaEq G A B Pp X1 X2 X3 :=
    L.congruentTrianglesEqualArea hABtri hXtri hAB_X12 hAP_X13 hBP_X23
  have hAChalf_Yhalf : TriangleAreaEq G A C R Y1 Y2 Y3 :=
    L.congruentTrianglesEqualArea hACtri hYtri hAC_Y12 hAR_Y13 hCR_Y23

  have hABdouble : QuadDoubleTriangle G A B Pp Q A B Pp :=
    proposition41 G hABpara hABtri
  have hXdouble : QuadDoubleTriangle G X1 X2 X3 X4 X1 X2 X3 :=
    proposition41 G hXpara hXtri
  have hACdouble : QuadDoubleTriangle G A C R S A C R :=
    proposition41 G hACpara hACtri
  have hYdouble : QuadDoubleTriangle G Y1 Y2 Y3 Y4 Y1 Y2 Y3 :=
    proposition41 G hYpara hYtri

  have hABeqX : QuadAreaEq G A B Pp Q X1 X2 X3 X4 :=
    AS.equalDoubleFigures hABdouble hXdouble hABhalf_Xhalf
  have hACeqY : QuadAreaEq G A C R S Y1 Y2 Y3 Y4 :=
    AS.equalDoubleFigures hACdouble hYdouble hAChalf_Yhalf

  have hXYhyp : QuadAreaSumEq G X1 X2 X3 X4 Y1 Y2 Y3 Y4 B C T U :=
    AS.partitionSum hpartition
  exact AS.sumCongr hABeqX hACeqY hXYhyp

end Euclid.Book1
