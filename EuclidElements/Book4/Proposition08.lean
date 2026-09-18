import EuclidElements.Book4.SquareConstructionFoundations

namespace Euclid.Book4

open Euclid
open Euclid.Book1
open Euclid.Book3

/-- Euclid IV.8: inscribe a circle in a given square. -/
theorem proposition8
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
    [S : SquareBook4ConstructionAxioms G]
    {A B C D : G.Point}
    (hsq : Square G A B C D) :
    ∃ c : G.Circle, CircleInscribedInSquare G c A B C D := by
  obtain ⟨O, T, U, V, W,
      lAB, lBC, lCD, lDA, rT, rU, rV, rW,
      hAB, hBC, hCD, hDA,
      hTlAB, hUlBC, hVlCD, hWlDA,
      hOrT, hTrT, hperpT, hOrU, hUrU, hperpU,
      hOrV, hVrV, hperpV, hOrW, hWrW, hperpW,
      hOT, hOT_OU, hOT_OV, hOT_OW⟩ := S.incircleFrame hsq
  obtain ⟨c, hcenter, hTc, hcircle⟩ := P.postulate3 O T hOT
  have hUc : G.onCircle U c := (hcircle U).2 (I.segmentSymm hOT_OU)
  have hVc : G.onCircle V c := (hcircle V).2 (I.segmentSymm hOT_OV)
  have hWc : G.onCircle W c := (hcircle W).2 (I.segmentSymm hOT_OW)
  have htT : TangentAt G c lAB T :=
    proposition16_tangent G hcenter hTc hOrT hTrT hTlAB hperpT
  have htU : TangentAt G c lBC U :=
    proposition16_tangent G hcenter hUc hOrU hUrU hUlBC hperpU
  have htV : TangentAt G c lCD V :=
    proposition16_tangent G hcenter hVc hOrV hVrV hVlCD hperpV
  have htW : TangentAt G c lDA W :=
    proposition16_tangent G hcenter hWc hOrW hWrW hWlDA hperpW
  refine ⟨c, hsq, ?_⟩
  exact ⟨lAB, lBC, lCD, lDA, T, U, V, W,
    hAB, hBC, hCD, hDA, htT, htU, htV, htW⟩

end Euclid.Book4
