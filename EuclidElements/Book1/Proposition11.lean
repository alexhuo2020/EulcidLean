import EuclidElements.Book1.Proposition01
import EuclidElements.Book1.Proposition08

/-!
# Euclid I.11 -- erect a perpendicular at a point on a line
-/

namespace Euclid.Book1

open Euclid

theorem proposition11
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    (l : G.Line) (A C : G.Point)
    (hAon : G.onLine A l) (hCon : G.onLine C l)
    (hAC : A ≠ C) :
    ∃ m : G.Line, G.onLine C m ∧ Perpendicular G l m := by
  obtain ⟨D, hACD⟩ := P.postulate2 A C hAC
  have hCneD : C ≠ D := (I.betweenDistinct hACD).2.1
  have hDneC : D ≠ C := Ne.symm hCneD
  obtain ⟨E, hDCE, hCD_CE⟩ := L.symmetricPoint (D := D) (C := C) hDneC
  have hDneE : D ≠ E := (I.betweenDistinct hDCE).2.2
  obtain ⟨F, _lDF, _lEF, _hD, _hF1, _hE, _hF2, _htriDEF, heqDEF⟩ :=
    proposition1_construction G D E hDneE
  obtain ⟨hCDF, hCEF⟩ := L.equilateralBaseSubtriangles hDCE heqDEF
  have hCF_CF : G.segmentCongruent C F C F := I.segmentRefl C F
  have hDF_EF : G.segmentCongruent D F E F := heqDEF.2.2
  have hsss := proposition8 G hCDF hCEF hCD_CE hCF_CF hDF_EF
  have hDCF_ECF : G.angleCongruent ⟨D, C, F⟩ ⟨E, C, F⟩ := hsss.1
  have hECF_FCE : G.angleCongruent ⟨E, C, F⟩ ⟨F, C, E⟩ :=
    L.angleReverse E C F
  have hright : RightAngle G ⟨D, C, F⟩ :=
    ⟨E, hDCE, I.angleTrans hDCF_ECF hECF_FCE⟩
  have hcol := I.betweenCollinear hACD
  obtain ⟨l2, hAl2, hCl2, hDl2⟩ := hcol
  have hl2 : l2 = l := I.lineUnique hAC hAl2 hCl2 hAon hCon
  have hDon : G.onLine D l := by simpa [hl2] using hDl2
  have hCneF : C ≠ F := Ne.symm hCDF.2.2.1
  obtain ⟨m, hCom, hFom⟩ := P.postulate1 C F hCneF
  have hperp : Perpendicular G l m := by
    exact ⟨C, D, F, hCneD, hCneF, hCon, hDon, hCom, hFom, hright⟩
  exact ⟨m, hCom, hperp⟩

end Euclid.Book1
