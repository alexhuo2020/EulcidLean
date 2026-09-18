import EuclidElements.Book1.Proposition19
import EuclidElements.Book1.AngleRayConstructionAxioms

/-!
# Euclid I.24 -- hinge theorem

If two triangles have two corresponding sides congruent, but the included
angle of the first is greater, then its remaining side is greater.

The auxiliary construction no longer assumes the decisive angle inequality in
the final triangle.  That comparison is derived below from I.5 and proper-
subangle order.
-/

namespace Euclid.Book1

open Euclid

theorem proposition24
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
    [SegmentArithmeticImplicitAxioms G]
    [TriangleConstructionImplicitAxioms G]
    [H : AngleRayConstructionAxioms G]
    {A B C D E F : G.Point}
    (hABC : IsTriangle G A B C)
    (hDEF : IsTriangle G D E F)
    (hAB_DE : G.segmentCongruent A B D E)
    (hAC_DF : G.segmentCongruent A C D F)
    (hangle : G.angleLess ⟨E, D, F⟩ ⟨B, A, C⟩) :
    SegmentLess G E F B C := by
  obtain ⟨Gp, hDEG, hDFG, hEFG, hDG_DF, hEDG_BAC,
    hDinsideF, hEinsideG⟩ :=
    H.copiedGreaterAngleWithMarkedRay hABC hDEF hangle

  have hAC_DG : G.segmentCongruent A C D Gp :=
    I.segmentTrans hAC_DF (I.segmentSymm hDG_DF)
  have hBAC_EDG : G.angleCongruent ⟨B, A, C⟩ ⟨E, D, Gp⟩ :=
    I.angleSymm hEDG_BAC
  have hsas := proposition4 G hABC hDEG hAB_DE hAC_DG hBAC_EDG
  have hBC_EG : G.segmentCongruent B C E Gp := hsas.1

  -- The marked triangle DFG is isosceles, so its base angles are equal.
  have hDF_DG : G.segmentCongruent D F D Gp := I.segmentSymm hDG_DF
  have hDFG_FGD : G.angleCongruent ⟨D, F, Gp⟩ ⟨F, Gp, D⟩ :=
    proposition5_baseAngles G hDFG hDF_DG
  have hDGF_FGD : G.angleCongruent ⟨D, Gp, F⟩ ⟨F, Gp, D⟩ :=
    L.angleReverse D Gp F
  have hDGF_DFG : G.angleCongruent ⟨D, Gp, F⟩ ⟨D, F, Gp⟩ :=
    I.angleTrans hDGF_FGD (I.angleSymm hDFG_FGD)

  -- D is inside ∠EFG and E is inside ∠DGF.
  have hEGF_DGF : G.angleLess ⟨E, Gp, F⟩ ⟨D, Gp, F⟩ :=
    AO.properSubangleRight hEinsideG
  have hDFG_EFG : G.angleLess ⟨D, F, Gp⟩ ⟨E, F, Gp⟩ :=
    AO.properSubangleRight hDinsideF
  have hEGF_DFG : G.angleLess ⟨E, Gp, F⟩ ⟨D, F, Gp⟩ :=
    AO.lt_congr_right hDGF_DFG hEGF_DGF
  have hEGF_EFG : G.angleLess ⟨E, Gp, F⟩ ⟨E, F, Gp⟩ :=
    AO.lt_trans hEGF_DFG hDFG_EFG

  have hEGF_FGE : G.angleCongruent ⟨E, Gp, F⟩ ⟨F, Gp, E⟩ :=
    L.angleReverse E Gp F
  have hFGE_EFG : G.angleLess ⟨F, Gp, E⟩ ⟨E, F, Gp⟩ :=
    AO.lt_congr_left hEGF_FGE hEGF_EFG
  have hEF_EG : SegmentLess G E F E Gp :=
    proposition19 G hEFG hFGE_EFG
  exact L.segmentLess_congr_right (I.segmentSymm hBC_EG) hEF_EG

end Euclid.Book1
