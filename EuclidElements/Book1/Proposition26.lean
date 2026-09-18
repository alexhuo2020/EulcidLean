import EuclidElements.Book1.Proposition03
import EuclidElements.Book1.AngleOrderImplicitAxioms
import EuclidElements.Book1.Proposition04

/-!
# Euclid I.26 -- ASA (joined-side case)

The second AAS case is recorded below after the joined-side theorem.
-/

namespace Euclid.Book1

open Euclid

private theorem proposition26_noGreaterFirstSide
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    {A B C D E F : G.Point}
    (hABC : IsTriangle G A B C)
    (hDEF : IsTriangle G D E F)
    (hB_E : G.angleCongruent ⟨A, B, C⟩ ⟨D, E, F⟩)
    (hC_F : G.angleCongruent ⟨B, C, A⟩ ⟨E, F, D⟩)
    (hBC_EF : G.segmentCongruent B C E F)
    (hDE_AB : SegmentLess G D E A B) : False := by
  have hDE_BA : SegmentLess G D E B A :=
    L.segmentLess_congr_right (I.segmentReverse A B) hDE_AB
  obtain ⟨Gp, hBGA, hBG_DE⟩ := proposition3 G B A D E hDEF.1 hDE_BA
  have hAGB : G.between A Gp B := L.betweenSymm hBGA
  have hBGC : IsTriangle G B Gp C := L.triangleOnSide hABC hAGB
  have hEDF : IsTriangle G E D F := L.triangleSwap23 (L.triangleCycle hDEF)

  have hBG_ED : G.segmentCongruent B Gp E D :=
    I.segmentTrans hBG_DE (I.segmentReverse D E)
  have hBneA : B ≠ A := Ne.symm hABC.1
  have hBneG : B ≠ Gp := (I.betweenDistinct hBGA).1
  have hRay : SameRay G B A Gp :=
    ⟨hBneA, hBneG, Or.inr (Or.inr hBGA)⟩
  have hABC_GBC : G.angleCongruent ⟨A, B, C⟩ ⟨Gp, B, C⟩ :=
    L.angleSameRayLeft hRay
  have hGBC_DEF : G.angleCongruent ⟨Gp, B, C⟩ ⟨D, E, F⟩ :=
    I.angleTrans (I.angleSymm hABC_GBC) hB_E

  have hsas := proposition4 G hBGC hEDF hBG_ED hBC_EF hGBC_DEF
  have hBCG_EFD : G.angleCongruent ⟨B, C, Gp⟩ ⟨E, F, D⟩ := hsas.2.2.1
  have hBCG_BCA : G.angleCongruent ⟨B, C, Gp⟩ ⟨B, C, A⟩ :=
    I.angleTrans hBCG_EFD (I.angleSymm hC_F)

  have hBCA : IsTriangle G B C A := L.triangleCycle hABC
  have hins : InsideAngle G B C A Gp := AO.sidePointInsideOppositeAngle hBCA hBGA
  have hproper : G.angleLess ⟨B, C, Gp⟩ ⟨B, C, A⟩ :=
    AO.properSubangleLeft hins
  exact (AO.lt_not_congr hproper) hBCG_BCA

/-- I.26, case where the given equal side joins the two equal angles (ASA). -/
theorem proposition26_asa
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    {A B C D E F : G.Point}
    (hABC : IsTriangle G A B C)
    (hDEF : IsTriangle G D E F)
    (hB_E : G.angleCongruent ⟨A, B, C⟩ ⟨D, E, F⟩)
    (hC_F : G.angleCongruent ⟨B, C, A⟩ ⟨E, F, D⟩)
    (hBC_EF : G.segmentCongruent B C E F) :
    G.segmentCongruent A B D E ∧
    G.segmentCongruent A C D F ∧
    G.angleCongruent ⟨B, A, C⟩ ⟨E, D, F⟩ := by
  rcases L.segmentTrichotomy A B D E with hAB_DE | hAB_DE | hDE_AB
  · have hBAC : IsTriangle G B A C := L.triangleSwap23 (L.triangleCycle hABC)
    have hEDF : IsTriangle G E D F := L.triangleSwap23 (L.triangleCycle hDEF)
    have hBA_ED : G.segmentCongruent B A E D := by
      have hBA_AB : G.segmentCongruent B A A B := I.segmentReverse B A
      have hDE_ED : G.segmentCongruent D E E D := I.segmentReverse D E
      exact I.segmentTrans (I.segmentTrans hBA_AB hAB_DE) hDE_ED
    have hsas := proposition4 G hBAC hEDF hBA_ED hBC_EF hB_E
    exact ⟨hAB_DE, hsas.1, hsas.2.1⟩
  · exact False.elim (proposition26_noGreaterFirstSide G hDEF hABC
      (I.angleSymm hB_E) (I.angleSymm hC_F) (I.segmentSymm hBC_EF) hAB_DE)
  · exact False.elim (proposition26_noGreaterFirstSide G hABC hDEF
      hB_E hC_F hBC_EF hDE_AB)

end Euclid.Book1
