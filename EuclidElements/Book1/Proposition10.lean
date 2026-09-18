import EuclidElements.Book1.Proposition01
import EuclidElements.Book1.Proposition04
import EuclidElements.Book1.Proposition09

/-!
# Euclid I.10 -- bisect a finite straight line
-/

namespace Euclid.Book1

open Euclid

theorem proposition10
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    (A B : G.Point)
    (hAB : A ≠ B) :
    ∃ M : G.Point, IsMidpoint G M A B := by
  obtain ⟨C, _lAC, _lBC, _hA, _hC1, _hB, _hC2, htri, heq⟩ :=
    proposition1_construction G A B hAB
  have htriACB : IsTriangle G A C B := L.triangleSwap23 htri
  have hValid : ValidAngle G ⟨A, C, B⟩ := by
    exact ⟨htriACB.1, Ne.symm htriACB.2.1, htriACB.2.2.2⟩
  obtain ⟨F, hFneC, hbis⟩ := proposition9 G hValid
  obtain ⟨M, hAMB, hACM_MCB⟩ := L.bisectorMeetsOppositeSide htri hFneC hbis
  obtain ⟨hCAM, hCBM⟩ := L.trianglesFromSidePoint htri hAMB
  have hAC_BC : G.segmentCongruent A C B C := heq.2.2
  have hCA_AC : G.segmentCongruent C A A C := I.segmentReverse C A
  have hBC_CB : G.segmentCongruent B C C B := I.segmentReverse B C
  have hCA_CB : G.segmentCongruent C A C B :=
    I.segmentTrans (I.segmentTrans hCA_AC hAC_BC) hBC_CB
  have hCM_CM : G.segmentCongruent C M C M := I.segmentRefl C M
  have hMCB_BCM : G.angleCongruent ⟨M, C, B⟩ ⟨B, C, M⟩ :=
    L.angleReverse M C B
  have hACM_BCM : G.angleCongruent ⟨A, C, M⟩ ⟨B, C, M⟩ :=
    I.angleTrans hACM_MCB hMCB_BCM
  have hsas := proposition4 G hCAM hCBM hCA_CB hCM_CM hACM_BCM
  have hBM_MB : G.segmentCongruent B M M B := I.segmentReverse B M
  have hAM_MB : G.segmentCongruent A M M B := I.segmentTrans hsas.1 hBM_MB
  exact ⟨M, hAMB, hAM_MB⟩

end Euclid.Book1
