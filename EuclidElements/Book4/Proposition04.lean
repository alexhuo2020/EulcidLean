import EuclidElements.Book4.TriangleConstructionFoundations

namespace Euclid.Book4

open Euclid
open Euclid.Book1
open Euclid.Book3

/-- Euclid IV.4: inscribe a circle in a given triangle.  The construction
    frame supplies the angle-bisector/perpendicular-foot geometry; tangency is
    derived with III.16. -/
theorem proposition4
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
    [T : TriangleBook4ConstructionAxioms G]
    {A B C : G.Point}
    (hABC : IsTriangle G A B C) :
    ∃ c : G.Circle, CircleInscribedInTriangle G c A B C := by
  obtain ⟨D, E, F, H, lAB, lBC, lCA, rE, rF, rH,
      hAB, hBC, hCA, hElAB, hFlBC, hHlCA,
      hDrE, hErE, hperpE, hDrF, hFrF, hperpF,
      hDrH, hHrH, hperpH, hDE, hDF, hDH, hDE_DF, hDE_DH⟩ :=
    T.incircleFrame hABC
  obtain ⟨c, hcenter, hEc, hcircle⟩ := P.postulate3 D E hDE
  have hFc : G.onCircle F c :=
    (hcircle F).2 (I.segmentSymm hDE_DF)
  have hHc : G.onCircle H c :=
    (hcircle H).2 (I.segmentSymm hDE_DH)
  have htE : TangentAt G c lAB E :=
    proposition16_tangent G hcenter hEc hDrE hErE hElAB hperpE
  have htF : TangentAt G c lBC F :=
    proposition16_tangent G hcenter hFc hDrF hFrF hFlBC hperpF
  have htH : TangentAt G c lCA H :=
    proposition16_tangent G hcenter hHc hDrH hHrH hHlCA hperpH
  refine ⟨c, hABC, ?_⟩
  exact ⟨lAB, lBC, lCA, E, F, H, hAB, hBC, hCA, htE, htF, htH⟩

end Euclid.Book4
