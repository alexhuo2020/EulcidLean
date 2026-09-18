import EuclidElements.Book1.Proposition08
import EuclidElements.Book1.Proposition10

/-!
# Euclid I.12 -- drop a perpendicular to a line from an external point
-/

namespace Euclid.Book1

open Euclid

theorem proposition12
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    (l : G.Line) (A : G.Point)
    (hAoff : ¬ G.onLine A l) :
    ∃ M : G.Point, ∃ m : G.Line,
      G.onLine M l ∧ G.onLine A m ∧ G.onLine M m ∧
      Perpendicular G l m := by
  obtain ⟨c, E, F, hEF, _hc, _hEon, _hFon, hEl, hFl, hAE_AF⟩ :=
    L.secantCircleThroughLine hAoff
  obtain ⟨M, hmid⟩ := proposition10 G E F hEF
  have hEMF := hmid.1
  have hEM_MF := hmid.2
  have hME_EM : G.segmentCongruent M E E M := I.segmentReverse M E
  have hME_MF : G.segmentCongruent M E M F := I.segmentTrans hME_EM hEM_MF
  have hMon : G.onLine M l := L.betweenOnLine hEMF hEl hFl
  have hAneM : A ≠ M := by
    intro h
    subst M
    exact hAoff hMon
  obtain ⟨hMEA, hMFA⟩ := L.offLineSecantTriangles hAoff hEl hFl hEMF
  have hMA_MA : G.segmentCongruent M A M A := I.segmentRefl M A
  have hEA_AE : G.segmentCongruent E A A E := I.segmentReverse E A
  have hAF_FA : G.segmentCongruent A F F A := I.segmentReverse A F
  have hEA_FA : G.segmentCongruent E A F A :=
    I.segmentTrans (I.segmentTrans hEA_AE hAE_AF) hAF_FA
  have hsss := proposition8 G hMEA hMFA hME_MF hMA_MA hEA_FA
  have hEMA_FMA : G.angleCongruent ⟨E, M, A⟩ ⟨F, M, A⟩ := hsss.1
  have hFMA_AMF : G.angleCongruent ⟨F, M, A⟩ ⟨A, M, F⟩ :=
    L.angleReverse F M A
  have hright : RightAngle G ⟨E, M, A⟩ :=
    ⟨F, hEMF, I.angleTrans hEMA_FMA hFMA_AMF⟩
  obtain ⟨m, hMom, hAom⟩ := P.postulate1 M A (Ne.symm hAneM)
  have hMneE : M ≠ E := Ne.symm (I.betweenDistinct hEMF).1
  have hperp : Perpendicular G l m := by
    exact ⟨M, E, A, hMneE, Ne.symm hAneM, hMon, hEl, hMom, hAom, hright⟩
  exact ⟨M, m, hMon, hAom, hMom, hperp⟩

end Euclid.Book1
