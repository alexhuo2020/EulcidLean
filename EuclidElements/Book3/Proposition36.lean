import EuclidElements.Book3.TangentPowerFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1
open Euclid.Book2

/-- Euclid III.36: from an exterior point, the rectangle on a secant equals
    the square on a tangent from the same point. -/
theorem proposition36
    (G : Geometry)
    [I : ImplicitAxioms G]
    [AreaGeometry G] [AA : AreaAxioms G]
    [P : Postulates G]
    [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [D34 : Proposition34ImplicitAxioms G]
    [C46 : Proposition46ImplicitAxioms G]
    [LaterAreaGeometry G]
    [AF : AreaFoundations G]
    [QuadPartitionGeometry G]
    [AS : AreaSumFoundations G]
    [SF : SquareAreaFoundations G]
    [PD : PythagoreanDiagramAxioms G]
    [B1 : Book1AreaMagnitudeBridge G]
    [CB : CircleBasicAxioms G]
    [CircleOrderGeometry G]
    [TC : TangentConverseFoundations G]
    [CP : CirclePowerDiagramAxioms G]
    [TP : TangentPowerDiagramAxioms G]
    {c : G.Circle} {O D C A B : G.Point} {t : G.Line}
    (hcenter : G.isCenter c O)
    (hC : G.onCircle C c) (hA : G.onCircle A c)
    (hB : G.onCircle B c)
    (hDCA : G.between D C A)
    (htan : TangentAt G c t B)
    (hDt : G.onLine D t)
    (hDB : D ≠ B) :
    Rect G A D C D = Sq G D B := by
  obtain ⟨A', C', F, hDA, hDC, hA', hC'⟩ :=
    CP.externalFrame hcenter hC hA hDCA
  have hpow := externalSecantPower G F
  have hAD_A'D : G.segmentCongruent A D A' D := by
    exact I.segmentTrans (I.segmentReverse A D)
      (I.segmentTrans hDA (I.segmentReverse D A'))
  have hCD_C'D : G.segmentCongruent C D C' D := by
    exact I.segmentTrans (I.segmentReverse C D)
      (I.segmentTrans hDC (I.segmentReverse D C'))
  have hrect : Rect G A D C D = Rect G A' D C' D := by
    calc
      Rect G A D C D = Rect G A' D C D := AA.rectCongrLeft hAD_A'D
      _ = Rect G A' D C' D := AA.rectCongrRight hCD_C'D
  obtain ⟨radius, hOr, hBr, hperp⟩ := proposition18 G hcenter htan
  obtain ⟨htri, hright⟩ :=
    TP.rightTriangle hcenter htan hDt hDB hOr hBr hperp
  have hpy := pythagoreanMagnitude G htri hright
  have hrad : G.segmentCongruent O C' O B :=
    CB.radiiCongruent hcenter hC' hB
  have hsqrad : Sq G O C' = Sq G O B := AA.squareCongr hrad
  have hBO_OB : Sq G B O = Sq G O B :=
    AA.squareCongr (I.segmentReverse B O)
  have hDB_BD : Sq G D B = Sq G B D :=
    AA.squareCongr (I.segmentReverse D B)
  have hsec : Add G (Rect G A D C D) (Sq G O B) = Sq G O D := by
    calc
      Add G (Rect G A D C D) (Sq G O B)
          = Add G (Rect G A' D C' D) (Sq G O C') := by rw [hrect, hsqrad]
      _ = Sq G O D := hpow
  have htanpy : Add G (Sq G O B) (Sq G D B) = Sq G O D := by
    calc
      Add G (Sq G O B) (Sq G D B)
          = Add G (Sq G B O) (Sq G B D) := by rw [hBO_OB, hDB_BD]
      _ = Sq G O D := hpy
  apply AA.addCancelLeft (Sq G O B)
  calc
    Add G (Sq G O B) (Rect G A D C D)
        = Add G (Rect G A D C D) (Sq G O B) := AA.addComm _ _
    _ = Sq G O D := hsec
    _ = Add G (Sq G O B) (Sq G D B) := htanpy.symm

end Euclid.Book3
