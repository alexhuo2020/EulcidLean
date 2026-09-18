import EuclidElements.Book1.Proposition03
import EuclidElements.Book1.Proposition04
import EuclidElements.Book1.Proposition16

/-!
# Euclid I.26 -- AAS (non-joined-side case)
-/

namespace Euclid.Book1

open Euclid

private theorem proposition26_aas_noGreaterSecondSide
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
    [AI : AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [P16 : Proposition16ImplicitAxioms G]
    {A B C D E F : G.Point}
    (hABC : IsTriangle G A B C)
    (hDEF : IsTriangle G D E F)
    (hB_E : G.angleCongruent ⟨A, B, C⟩ ⟨D, E, F⟩)
    (hC_F : G.angleCongruent ⟨B, C, A⟩ ⟨E, F, D⟩)
    (hAB_DE : G.segmentCongruent A B D E)
    (hEF_BC : SegmentLess G E F B C) : False := by
  obtain ⟨Gp, hBGC, hBG_EF⟩ := proposition3 G B C E F hDEF.2.1 hEF_BC

  have hBCAtri : IsTriangle G B C A := L.triangleCycle hABC
  obtain ⟨hABG, hACG⟩ := L.trianglesFromSidePoint hBCAtri hBGC
  have hBAG : IsTriangle G B A Gp := L.triangleSwap23 (L.triangleCycle hABG)
  have hEDF : IsTriangle G E D F := L.triangleSwap23 (L.triangleCycle hDEF)

  have hBA_ED : G.segmentCongruent B A E D := by
    have hBA_AB : G.segmentCongruent B A A B := I.segmentReverse B A
    have hDE_ED : G.segmentCongruent D E E D := I.segmentReverse D E
    exact I.segmentTrans (I.segmentTrans hBA_AB hAB_DE) hDE_ED

  have hBneC : B ≠ C := hABC.2.1
  have hBneG : B ≠ Gp := (I.betweenDistinct hBGC).1
  have hRayBCG : SameRay G B C Gp :=
    ⟨hBneC, hBneG, Or.inr (Or.inr hBGC)⟩
  have hABC_ABG : G.angleCongruent ⟨A, B, C⟩ ⟨A, B, Gp⟩ :=
    L.angleSameRayRight hRayBCG
  have hABG_DEF : G.angleCongruent ⟨A, B, Gp⟩ ⟨D, E, F⟩ :=
    I.angleTrans (I.angleSymm hABC_ABG) hB_E

  have hsas := proposition4 G hBAG hEDF hBA_ED hBG_EF hABG_DEF
  have hBGA_EFD : G.angleCongruent ⟨B, Gp, A⟩ ⟨E, F, D⟩ := hsas.2.2.1
  have hAGB_EFD : G.angleCongruent ⟨A, Gp, B⟩ ⟨E, F, D⟩ :=
    I.angleTrans (L.angleReverse A Gp B) hBGA_EFD

  have hCGB : G.between C Gp B := L.betweenSymm hBGC
  have hCGtri : IsTriangle G A C Gp := hACG
  have hext := proposition16 G hCGtri hCGB
  have hACG_AGB : G.angleLess ⟨A, C, Gp⟩ ⟨A, Gp, B⟩ := hext.2

  have hCneB : C ≠ B := Ne.symm hABC.2.1
  have hCneG : C ≠ Gp := (I.betweenDistinct hCGB).1
  have hRayCBG : SameRay G C B Gp :=
    ⟨hCneB, hCneG, Or.inr (Or.inr hCGB)⟩
  have hACB_ACG : G.angleCongruent ⟨A, C, B⟩ ⟨A, C, Gp⟩ :=
    L.angleSameRayRight hRayCBG
  have hACG_ACB : G.angleCongruent ⟨A, C, Gp⟩ ⟨A, C, B⟩ := I.angleSymm hACB_ACG
  have hACB_BCA : G.angleCongruent ⟨A, C, B⟩ ⟨B, C, A⟩ := L.angleReverse A C B
  have hACG_EFD : G.angleCongruent ⟨A, C, Gp⟩ ⟨E, F, D⟩ :=
    I.angleTrans (I.angleTrans hACG_ACB hACB_BCA) hC_F
  have hACG_AGB_eq : G.angleCongruent ⟨A, C, Gp⟩ ⟨A, Gp, B⟩ :=
    I.angleTrans hACG_EFD (I.angleSymm hAGB_EFD)
  exact (AO.lt_not_congr hACG_AGB) hACG_AGB_eq

/-- I.26, case where the equal side subtends one of the equal angles (AAS). -/
theorem proposition26_aas
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
    [AI : AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [P16 : Proposition16ImplicitAxioms G]
    {A B C D E F : G.Point}
    (hABC : IsTriangle G A B C)
    (hDEF : IsTriangle G D E F)
    (hB_E : G.angleCongruent ⟨A, B, C⟩ ⟨D, E, F⟩)
    (hC_F : G.angleCongruent ⟨B, C, A⟩ ⟨E, F, D⟩)
    (hAB_DE : G.segmentCongruent A B D E) :
    G.segmentCongruent B C E F ∧
    G.segmentCongruent A C D F ∧
    G.angleCongruent ⟨B, A, C⟩ ⟨E, D, F⟩ := by
  rcases L.segmentTrichotomy B C E F with hBC_EF | hBC_EF | hEF_BC
  · have hBAC : IsTriangle G B A C := L.triangleSwap23 (L.triangleCycle hABC)
    have hEDF : IsTriangle G E D F := L.triangleSwap23 (L.triangleCycle hDEF)
    have hBA_ED : G.segmentCongruent B A E D := by
      have hBA_AB : G.segmentCongruent B A A B := I.segmentReverse B A
      have hDE_ED : G.segmentCongruent D E E D := I.segmentReverse D E
      exact I.segmentTrans (I.segmentTrans hBA_AB hAB_DE) hDE_ED
    have hsas := proposition4 G hBAC hEDF hBA_ED hBC_EF hB_E
    exact ⟨hBC_EF, hsas.1, hsas.2.1⟩
  · exact False.elim (proposition26_aas_noGreaterSecondSide G hDEF hABC
      (I.angleSymm hB_E) (I.angleSymm hC_F) (I.segmentSymm hAB_DE) hBC_EF)
  · exact False.elim (proposition26_aas_noGreaterSecondSide G hABC hDEF
      hB_E hC_F hAB_DE hEF_BC)

end Euclid.Book1
