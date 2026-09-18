import EuclidElements.Book1.Proposition08

/-!
# Euclid I.9 -- bisect a given rectilinear angle
-/

namespace Euclid.Book1

open Euclid

theorem proposition9
    (G : Geometry)
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    {B A C : G.Point}
    (hangle : ValidAngle G ⟨B, A, C⟩) :
    ∃ F : G.Point,
      F ≠ A ∧ G.angleCongruent ⟨B, A, F⟩ ⟨F, A, C⟩ := by
  obtain ⟨D, E, hRayB, hRayC, hAD_AE, hADE⟩ :=
    L.equalPointsOnAngleArms hangle
  obtain ⟨F, heqDEF, hADF, hAEF⟩ := L.equilateralAwayFromPoint hADE

  have hAF_AF : G.segmentCongruent A F A F := I.segmentRefl A F
  have hDF_EF : G.segmentCongruent D F E F := heqDEF.2.2
  have hsss := proposition8 G hADF hAEF hAD_AE hAF_AF hDF_EF
  have hDAF_EAF : G.angleCongruent ⟨D, A, F⟩ ⟨E, A, F⟩ := hsss.1

  have hBAF_DAF : G.angleCongruent ⟨B, A, F⟩ ⟨D, A, F⟩ :=
    L.angleSameRayLeft hRayB
  have hEAF_FAE : G.angleCongruent ⟨E, A, F⟩ ⟨F, A, E⟩ :=
    L.angleReverse E A F
  have hFAC_FAE : G.angleCongruent ⟨F, A, C⟩ ⟨F, A, E⟩ :=
    L.angleSameRayRight hRayC
  have hFAE_FAC : G.angleCongruent ⟨F, A, E⟩ ⟨F, A, C⟩ :=
    I.angleSymm hFAC_FAE

  have hBAF_FAC := I.angleTrans hBAF_DAF
    (I.angleTrans hDAF_EAF (I.angleTrans hEAF_FAE hFAE_FAC))
  have hFneA : F ≠ A := hADF.2.2.1
  exact ⟨F, hFneA, hBAF_FAC⟩

end Euclid.Book1
