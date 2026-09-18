import EuclidElements.Book1.Proposition24

/-!
# Euclid I.25 -- converse hinge theorem
-/

namespace Euclid.Book1

open Euclid

theorem proposition25
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
    [AngleRayConstructionAxioms G]
    {A B C D E F : G.Point}
    (hABC : IsTriangle G A B C)
    (hDEF : IsTriangle G D E F)
    (hAB_DE : G.segmentCongruent A B D E)
    (hAC_DF : G.segmentCongruent A C D F)
    (hEF_BC : SegmentLess G E F B C) :
    G.angleLess ⟨E, D, F⟩ ⟨B, A, C⟩ := by
  rcases AO.angleTrichotomy ⟨E, D, F⟩ ⟨B, A, C⟩ with hEq | hLt | hGt
  · have hsas := proposition4 G hABC hDEF hAB_DE hAC_DF (I.angleSymm hEq)
    have hBC_EF : G.segmentCongruent B C E F := hsas.1
    have hbad : SegmentLess G E F E F :=
      L.segmentLess_congr_right hBC_EF hEF_BC
    exact False.elim (L.segmentLess_irrefl E F hbad)
  · exact hLt
  · have hBC_EF : SegmentLess G B C E F :=
      proposition24 G hDEF hABC (I.segmentSymm hAB_DE) (I.segmentSymm hAC_DF) hGt
    have hbad : SegmentLess G E F E F := L.segmentLess_trans hEF_BC hBC_EF
    exact False.elim (L.segmentLess_irrefl E F hbad)

end Euclid.Book1
