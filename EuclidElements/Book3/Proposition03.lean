import EuclidElements.Book3.CircleFoundations
import EuclidElements.Book1.Proposition26AAS

namespace Euclid.Book3

open Euclid
open Euclid.Book1

theorem proposition3_bisector_perpendicular
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [C : CircleBasicAxioms G]
    {c : G.Circle} {O A B M : G.Point} {l m : G.Line}
    (hcenter : G.isCenter c O)
    (hchord : Chord G c A B)
    (hAl : G.onLine A l) (hBl : G.onLine B l) (hMl : G.onLine M l)
    (hOm : G.onLine O m) (hMm : G.onLine M m)
    (hOnot : ¬ G.onLine O l)
    (hmid : IsMidpoint G M A B) :
    Perpendicular G l m := by
  have hAneB : A ≠ B := hchord.1
  have hMneA : M ≠ A := Ne.symm (I.betweenDistinct hmid.1).1
  have hMneO : M ≠ O := by
    intro h
    subst O
    exact hOnot hMl
  have hOAB : IsTriangle G O A B := by
    refine ⟨?_, hAneB, ?_, ?_⟩
    · intro h
      subst O
      exact C.centerNotOnCircle hcenter hchord.2.1
    · intro h
      subst O
      exact C.centerNotOnCircle hcenter hchord.2.2
    · intro hcol
      rcases hcol with ⟨u, hOu, hAu, hBu⟩
      have hul : u = l := I.lineUnique hAneB hAu hBu hAl hBl
      exact hOnot (by simpa [hul] using hOu)
  have hABO : IsTriangle G A B O := L.triangleCycle hOAB
  obtain ⟨hOAM, hOBM⟩ := L.trianglesFromSidePoint hABO hmid.1
  have hMAO : IsTriangle G M A O :=
    L.triangleSwap23 (L.triangleCycle (L.triangleCycle hOAM))
  have hMBO : IsTriangle G M B O :=
    L.triangleSwap23 (L.triangleCycle (L.triangleCycle hOBM))
  have hMA_MB : G.segmentCongruent M A M B := by
    exact I.segmentTrans (I.segmentReverse M A) hmid.2
  have hMO_MO : G.segmentCongruent M O M O := I.segmentRefl M O
  have hAO_BO : G.segmentCongruent A O B O := by
    have hOA_OB := C.radiiCongruent hcenter hchord.2.1 hchord.2.2
    exact I.segmentTrans (I.segmentTrans (I.segmentReverse A O) hOA_OB)
      (I.segmentReverse O B)
  have hMAO_BMO : G.angleCongruent ⟨A, M, O⟩ ⟨B, M, O⟩ :=
    (L.sss hMAO hMBO hMA_MB hMO_MO hAO_BO).1
  have hright : RightAngle G ⟨A, M, O⟩ :=
    ⟨B, hmid.1, I.angleTrans hMAO_BMO (L.angleReverse B M O)⟩
  exact ⟨M, A, O, hMneA, hMneO, hMl, hAl, hMm, hOm, hright⟩

theorem proposition3_perpendicular_bisects
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [Proposition16ImplicitAxioms G]
    [C : CircleBasicAxioms G]
    [PI : PerpendicularIntersectionAxioms G]
    {c : G.Circle} {O A B M : G.Point} {l m : G.Line}
    (hcenter : G.isCenter c O)
    (hchord : Chord G c A B)
    (hAl : G.onLine A l) (hBl : G.onLine B l) (hMl : G.onLine M l)
    (hOm : G.onLine O m) (hMm : G.onLine M m)
    (hOnot : ¬ G.onLine O l)
    (hbetween : G.between A M B)
    (hperp : Perpendicular G l m) :
    IsMidpoint G M A B := by
  have hAneB : A ≠ B := hchord.1
  have hMneO : M ≠ O := by
    intro h
    subst O
    exact hOnot hMl
  have hOAB : IsTriangle G O A B := by
    refine ⟨?_, hAneB, ?_, ?_⟩
    · intro h
      subst O
      exact C.centerNotOnCircle hcenter hchord.2.1
    · intro h
      subst O
      exact C.centerNotOnCircle hcenter hchord.2.2
    · intro hcol
      rcases hcol with ⟨u, hOu, hAu, hBu⟩
      have hul : u = l := I.lineUnique hAneB hAu hBu hAl hBl
      exact hOnot (by simpa [hul] using hOu)
  have hABO : IsTriangle G A B O := L.triangleCycle hOAB
  obtain ⟨hOAM, hOBM⟩ := L.trianglesFromSidePoint hABO hbetween
  have hOA_OB : G.segmentCongruent O A O B :=
    C.radiiCongruent hcenter hchord.2.1 hchord.2.2
  have hbase : G.angleCongruent ⟨O, A, B⟩ ⟨A, B, O⟩ :=
    proposition5_baseAngles G hOAB hOA_OB
  have hAneM : A ≠ M := (I.betweenDistinct hbetween).1
  have hBneM : B ≠ M := Ne.symm (I.betweenDistinct hbetween).2.1
  have hRayA : SameRay G A B M :=
    ⟨hAneB, hAneM, Or.inr (Or.inr hbetween)⟩
  have hMBA : G.between B M A := L.betweenSymm hbetween
  have hRayB : SameRay G B A M :=
    ⟨Ne.symm hAneB, hBneM, Or.inr (Or.inr hMBA)⟩
  have hOAB_OAM : G.angleCongruent ⟨O, A, B⟩ ⟨O, A, M⟩ :=
    L.angleSameRayRight hRayA
  have hABO_MBO : G.angleCongruent ⟨A, B, O⟩ ⟨M, B, O⟩ :=
    L.angleSameRayLeft hRayB
  have hOAM_MBO : G.angleCongruent ⟨O, A, M⟩ ⟨M, B, O⟩ :=
    I.angleTrans (I.angleSymm hOAB_OAM) (I.angleTrans hbase hABO_MBO)
  have hOAM_OBM : G.angleCongruent ⟨O, A, M⟩ ⟨O, B, M⟩ :=
    I.angleTrans hOAM_MBO (L.angleReverse M B O)
  have hrs := PI.adjacentRightAngles hperp hbetween
    hAl hMl hBl hMm hOm hMneO
  have hrightCongr : G.angleCongruent ⟨A, M, O⟩ ⟨B, M, O⟩ :=
    P.postulate4 _ _ hrs.1 hrs.2
  have hasa := proposition26_aas G hOAM hOBM
    hOAM_OBM hrightCongr hOA_OB
  have hAM_BM : G.segmentCongruent A M B M := hasa.1
  exact ⟨hbetween, I.segmentTrans hAM_BM (I.segmentReverse B M)⟩

end Euclid.Book3
