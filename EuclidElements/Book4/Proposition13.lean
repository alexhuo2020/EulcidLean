import EuclidElements.Book4.Proposition12

namespace Euclid.Book4

open Euclid
open Euclid.Book1
open Euclid.Book3

/-- Euclid IV.13: inscribe a circle in a regular pentagon. -/
theorem proposition13
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AI : AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [P16 : Proposition16ImplicitAxioms G]
    [CB : CircleBasicAxioms G]
    [TL : TangentLineFoundations G]
    [RA : RightAngleCongruenceAxioms G]
    [RS : RightAngleSumFoundations G]
    [PC : PentagonBook4ConstructionAxioms G]
    {A B C D E : G.Point}
    (hreg : RegularPentagon G A B C D E) :
    ∃ c : G.Circle, CircleInscribedInPentagon G c A B C D E := by
  obtain ⟨O, T, U, V, W, X,
      lAB, lBC, lCD, lDE, lEA, rT, rU, rV, rW, rX,
      hAB, hBC, hCD, hDE, hEA,
      hTlAB, hUlBC, hVlCD, hWlDE, hXlEA,
      hOrT, hTrT, hpT, hOrU, hUrU, hpU,
      hOrV, hVrV, hpV, hOrW, hWrW, hpW,
      hOrX, hXrX, hpX, hOT,
      hOT_OU, hOT_OV, hOT_OW, hOT_OX⟩ := PC.incircleFrame hreg
  obtain ⟨c, hcenter, hTc, hcircle⟩ := P.postulate3 O T hOT
  have hUc : G.onCircle U c := (hcircle U).2 (I.segmentSymm hOT_OU)
  have hVc : G.onCircle V c := (hcircle V).2 (I.segmentSymm hOT_OV)
  have hWc : G.onCircle W c := (hcircle W).2 (I.segmentSymm hOT_OW)
  have hXc : G.onCircle X c := (hcircle X).2 (I.segmentSymm hOT_OX)
  have htT := proposition16_tangent G hcenter hTc hOrT hTrT hTlAB hpT
  have htU := proposition16_tangent G hcenter hUc hOrU hUrU hUlBC hpU
  have htV := proposition16_tangent G hcenter hVc hOrV hVrV hVlCD hpV
  have htW := proposition16_tangent G hcenter hWc hOrW hWrW hWlDE hpW
  have htX := proposition16_tangent G hcenter hXc hOrX hXrX hXlEA hpX
  refine ⟨c, hreg, ?_⟩
  exact ⟨lAB, lBC, lCD, lDE, lEA, T, U, V, W, X,
    hAB, hBC, hCD, hDE, hEA, htT, htU, htV, htW, htX⟩

end Euclid.Book4
