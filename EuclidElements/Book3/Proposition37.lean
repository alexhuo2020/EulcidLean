import EuclidElements.Book3.Proposition17
import EuclidElements.Book3.ConversePowerFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1
open Euclid.Book2

/-- Euclid III.37: converse of III.36. -/
theorem proposition37
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
    [AI : AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [P16 : Proposition16ImplicitAxioms G]
    [CBA : CircleBasicAxioms G]
    [CircleOrderGeometry G]
    [CPA : CirclePositionAxioms G]
    [TL : TangentLineFoundations G]
    [RA : RightAngleCongruenceAxioms G]
    [RS : RightAngleSumFoundations G]
    [EC : ExternalTangentConstructionAxioms G]
    [TC : TangentConverseFoundations G]
    [AreaGeometry G] [AA : AreaAxioms G]
    [D34 : Proposition34ImplicitAxioms G]
    [C46 : Proposition46ImplicitAxioms G]
    [LaterAreaGeometry G]
    [AF : AreaFoundations G]
    [QuadPartitionGeometry G]
    [AS : AreaSumFoundations G]
    [SF : SquareAreaFoundations G]
    [PD : PythagoreanDiagramAxioms G]
    [B1 : Book1AreaMagnitudeBridge G]
    [CP : CirclePowerDiagramAxioms G]
    [TP : TangentPowerDiagramAxioms G]
    [SM : SquareMagnitudeFaithful G]
    [CV : ConversePowerFoundations G]
    {c : G.Circle} {O D C A B : G.Point} {candidate : G.Line}
    (hcenter : G.isCenter c O)
    (hout : OutsideCircle G D c)
    (hC : G.onCircle C c) (hA : G.onCircle A c) (hB : G.onCircle B c)
    (hDCA : G.between D C A)
    (hDcand : G.onLine D candidate)
    (hBcand : G.onLine B candidate)
    (hpower : Rect G A D C D = Sq G D B) :
    TangentAt G c candidate B := by
  obtain ⟨E, t, hDt, htanE⟩ := Euclid.Book3.proposition17 G hcenter hout
  have hDneE : D ≠ E := by
    intro h
    subst E
    exact (CPA.outsideNotBoundary hout) htanE.1
  have h36 := proposition36 G hcenter hC hA htanE.1 hDCA htanE hDt hDneE
  have hsq : Sq G D E = Sq G D B := by
    calc
      Sq G D E = Rect G A D C D := h36.symm
      _ = Sq G D B := hpower
  have hDE_DB : G.segmentCongruent D E D B :=
    SM.segmentCongruentOfSquareEq hsq
  have hEO_BO : G.segmentCongruent E O B O := by
    have hOE_OB : G.segmentCongruent O E O B :=
      CBA.radiiCongruent hcenter htanE.1 hB
    exact I.segmentTrans (I.segmentReverse E O)
      (I.segmentTrans hOE_OB (I.segmentReverse O B))
  have hDO_DO : G.segmentCongruent D O D O := I.segmentRefl D O

  obtain ⟨radiusE, hOrE, hErE, hperpE⟩ := proposition18 G hcenter htanE
  obtain ⟨htriEOD, hrightOED⟩ :=
    TP.rightTriangle hcenter htanE hDt hDneE hOrE hErE hperpE
  have htriODE : IsTriangle G O D E := L.triangleCycle htriEOD
  have htriDEO : IsTriangle G D E O := L.triangleCycle htriODE
  have htriDBO : IsTriangle G D B O :=
    CV.candidateTriangle hcenter hout hC hA hB hDCA hpower
  have hsss := L.sss htriDEO htriDBO hDE_DB hDO_DO hEO_BO
  have hDEO_DBO : G.angleCongruent ⟨D, E, O⟩ ⟨D, B, O⟩ := hsss.2.1
  have hrightDEO : RightAngle G ⟨D, E, O⟩ :=
    RA.rightAngleOfCongruent (L.angleReverse D E O) hrightOED
  have hrightDBO : RightAngle G ⟨D, B, O⟩ :=
    RA.rightAngleOfCongruent (I.angleSymm hDEO_DBO) hrightDEO
  have hrightOBD : RightAngle G ⟨O, B, D⟩ :=
    RA.rightAngleOfCongruent (L.angleReverse O B D) hrightDBO

  have hOneB : O ≠ B := by
    intro h
    subst B
    exact CBA.centerNotOnCircle hcenter hB
  obtain ⟨radiusB, hOrB, hBrB⟩ := P.postulate1 O B hOneB
  have hDneB : D ≠ B := by
    intro h
    subst B
    exact (CPA.outsideNotBoundary hout) hB
  have hBneO : B ≠ O := Ne.symm hOneB
  have hBneD : B ≠ D := Ne.symm hDneB
  have hperpCandidate : Perpendicular G radiusB candidate := by
    exact ⟨B, O, D, hBneO, hBneD, hBrB, hOrB, hBcand, hDcand, hrightOBD⟩
  exact proposition16_tangent G hcenter hB hOrB hBrB hBcand hperpCandidate

end Euclid.Book3
