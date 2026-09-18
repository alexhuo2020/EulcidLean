import EuclidElements.Book4.FinalPolygonConstructionFoundations

namespace Euclid.Book4

open Euclid

/-- Euclid IV.15: inscribe a regular hexagon in a given circle; the final
    component records Euclid's corollary that a side equals the radius. -/
theorem proposition15
    (G : Geometry)
    [H : HexagonBook4ConstructionAxioms G]
    {c : G.Circle} :
    ∃ O A B C D E F : G.Point,
      G.isCenter c O ∧
      HexagonInscribedInCircle G c A B C D E F ∧
      G.segmentCongruent A B O A := by
  obtain ⟨O, A, B, C, D, E, F, hO,
      hA, hB, hC, hD, hE, hF,
      hAB_BC, hBC_CD, hCD_DE, hDE_EF, hEF_FA,
      hAang, hBang, hCang, hDang, hEang, hsideRadius⟩ := H.frame c
  refine ⟨O, A, B, C, D, E, F, hO, ?_, hsideRadius⟩
  exact ⟨⟨hAB_BC, hBC_CD, hCD_DE, hDE_EF, hEF_FA,
    hAang, hBang, hCang, hDang, hEang⟩,
    hA, hB, hC, hD, hE, hF⟩

end Euclid.Book4
