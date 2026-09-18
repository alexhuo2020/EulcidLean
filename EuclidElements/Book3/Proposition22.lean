import EuclidElements.Book3.CyclicQuadrilateralFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Euclid III.22: opposite angles of a quadrilateral inscribed in a circle
    are together equal to two right angles.  `Supplementary` is the synthetic
    two-right-angles relation. -/
theorem proposition22
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleInteriorGeometry G]
    [AngleSumGeometry G]
    [AngleAdditionGeometry G]
    [AngleArcGeometry G]
    [AI : AngleImplicitAxioms G]
    [AA : AngleAdditionImplicitAxioms G]
    [P32 : Proposition32ImplicitAxioms G]
    [C0 : CircleBasicAxioms G]
    [CA : InscribedAngleCaseAxioms G]
    [ALG : AngleSumAlgebraFoundations G]
    [TR : TwoRightAngleAlgebraFoundations G]
    [CQ : CyclicQuadrilateralFoundations G]
    {c : G.Circle} {A B C D : G.Point}
    (hA : G.onCircle A c)
    (hB : G.onCircle B c)
    (hC : G.onCircle C c)
    (hD : G.onCircle D c)
    (hquad : IsQuadrilateral G A B C D) :
    Supplementary G ⟨A, B, C⟩ ⟨A, D, C⟩ := by
  obtain ⟨sBC, sAB,
    hArcBC, hBAC, hBDC,
    hArcAB, hACB, hADB,
    hInsideD, hABC, hBDCtri, hADBtri⟩ :=
      CQ.data hA hB hC hD hquad

  have hBACtri : IsTriangle G B A C :=
    L.triangleSwap23 (L.triangleCycle hABC)
  have hSameBC : G.angleCongruent ⟨B, A, C⟩ ⟨B, D, C⟩ :=
    proposition21 G hArcBC hBAC hBDC hA hD hB hC hBACtri hBDCtri
  have hSameAB0 : G.angleCongruent ⟨A, C, B⟩ ⟨A, D, B⟩ :=
    proposition21 G hArcAB hACB hADB hC hD hA hB
      (L.triangleSwap23 hABC) hADBtri
  have hBCA_ADB : G.angleCongruent ⟨B, C, A⟩ ⟨A, D, B⟩ := by
    have hBCA_ACB : G.angleCongruent ⟨B, C, A⟩ ⟨A, C, B⟩ :=
      L.angleReverse B C A
    exact I.angleTrans hBCA_ACB hSameAB0

  have hsplitD0 : AngleSumEq G ⟨A, D, B⟩ ⟨B, D, C⟩ ⟨A, D, C⟩ :=
    AA.splitInside hInsideD
  have hsplitD : AngleSumEq G ⟨B, C, A⟩ ⟨B, A, C⟩ ⟨A, D, C⟩ :=
    AA.sumCongr hBCA_ADB hSameBC hsplitD0

  obtain ⟨E, hBCE⟩ := by
    have hBC : B ≠ C := hABC.2.1
    exact P.postulate2 B C hBC
  have htriSum : ThreeAnglesTwoRight G
      ⟨B, A, C⟩ ⟨A, B, C⟩ ⟨B, C, A⟩ :=
    (proposition32 G hABC hBCE).2

  exact TR.replacePair htriSum hsplitD

end Euclid.Book3
