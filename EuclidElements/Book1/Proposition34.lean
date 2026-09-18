import EuclidElements.Book1.Proposition26
import EuclidElements.Book1.Proposition34ImplicitAxioms

/-!
# Euclid I.34 -- opposite sides/angles of a parallelogram; diagonal bisection
-/

namespace Euclid.Book1

open Euclid

theorem proposition34
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [D34 : Proposition34ImplicitAxioms G]
    {A B C D : G.Point}
    (hpara : Parallelogram G A B C D) :
    G.segmentCongruent A B C D ∧
    G.segmentCongruent B C D A ∧
    G.angleCongruent ⟨A, B, C⟩ ⟨C, D, A⟩ ∧
    TriangleAreaEq G A B C C D A := by
  obtain ⟨hABC, hDCA, hBAC_DCA, hACB_CAD⟩ := D34.diagonalData hpara
  have hBAC : IsTriangle G B A C := L.triangleSwap23 (L.triangleCycle hABC)
  have hAC_CA : G.segmentCongruent A C C A := I.segmentReverse A C
  have hasa := proposition26_asa G hBAC hDCA hBAC_DCA hACB_CAD hAC_CA
  have hBA_DC : G.segmentCongruent B A D C := hasa.1
  have hBC_DA : G.segmentCongruent B C D A := hasa.2.1
  have hABC_CDA : G.angleCongruent ⟨A, B, C⟩ ⟨C, D, A⟩ := hasa.2.2

  have hAB_CD : G.segmentCongruent A B C D := by
    have hAB_BA : G.segmentCongruent A B B A := I.segmentReverse A B
    have hDC_CD : G.segmentCongruent D C C D := I.segmentReverse D C
    exact I.segmentTrans (I.segmentTrans hAB_BA hBA_DC) hDC_CD

  have hCDA : IsTriangle G C D A := L.triangleSwap23 (L.triangleCycle hDCA)
  have harea : TriangleAreaEq G A B C C D A :=
    L.congruentTrianglesEqualArea hABC hCDA hAB_CD hAC_CA hBC_DA
  exact ⟨hAB_CD, hBC_DA, hABC_CDA, harea⟩

end Euclid.Book1
