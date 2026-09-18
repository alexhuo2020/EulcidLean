import EuclidElements.Book2.Proposition09_10Diagrams

/-! # Euclid II.9 -/
namespace Euclid.Book2

open Euclid
open Euclid.Book1

/-- The common Pythagorean calculation underlying Euclid II.9 and II.10. -/
theorem doubleSquareFromRightDiagram
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
    [C46 : Proposition46ImplicitAxioms G]
    [LaterAreaGeometry G]
    [AF : AreaFoundations G]
    [QuadPartitionGeometry G]
    [AS : AreaSumFoundations G]
    [SF : SquareAreaFoundations G]
    [PD : PythagoreanDiagramAxioms G]
    [AreaGeometry G]
    [AA : AreaAxioms G]
    [B : Book1AreaMagnitudeBridge G]
    {A C D Bp E F H : G.Point}
    (hDAF : IsTriangle G D A F) (hrD : RightAngle G ⟨A, D, F⟩)
    (hDF_DB : G.segmentCongruent D F D Bp)
    (hEAF : IsTriangle G E A F) (hrE : RightAngle G ⟨A, E, F⟩)
    (hCAE : IsTriangle G C A E) (hrC : RightAngle G ⟨A, C, E⟩)
    (hCE_AC : G.segmentCongruent C E A C)
    (hHEF : IsTriangle G H E F) (hrH : RightAngle G ⟨E, H, F⟩)
    (hHE_CD : G.segmentCongruent H E C D)
    (hHF_CD : G.segmentCongruent H F C D) :
    Add G (Sq G A D) (Sq G D Bp) =
      Add G (Add G (Sq G A C) (Sq G C D))
        (Add G (Sq G A C) (Sq G C D)) := by
  have hDAFpy := pythagoreanMagnitude G hDAF hrD
  have hEAFpy := pythagoreanMagnitude G hEAF hrE
  have hCAEpy := pythagoreanMagnitude G hCAE hrC
  have hHEFpy := pythagoreanMagnitude G hHEF hrH

  have hDA_AD : Sq G D A = Sq G A D :=
    AA.squareCongr (I.segmentReverse D A)
  have hDF_DBsq : Sq G D F = Sq G D Bp := AA.squareCongr hDF_DB
  have hADDB_AF : Add G (Sq G A D) (Sq G D Bp) = Sq G A F := by
    calc
      Add G (Sq G A D) (Sq G D Bp)
          = Add G (Sq G D A) (Sq G D F) := by rw [hDA_AD, hDF_DBsq]
      _ = Sq G A F := hDAFpy

  have hEA_AE : Sq G E A = Sq G A E :=
    AA.squareCongr (I.segmentReverse E A)
  have hAE_EF_AF : Add G (Sq G A E) (Sq G E F) = Sq G A F := by
    calc
      Add G (Sq G A E) (Sq G E F)
          = Add G (Sq G E A) (Sq G E F) := by rw [hEA_AE]
      _ = Sq G A F := hEAFpy

  have hCA_AC : Sq G C A = Sq G A C :=
    AA.squareCongr (I.segmentReverse C A)
  have hCE_ACsq : Sq G C E = Sq G A C := AA.squareCongr hCE_AC
  have htwiceAC : Add G (Sq G A C) (Sq G A C) = Sq G A E := by
    calc
      Add G (Sq G A C) (Sq G A C)
          = Add G (Sq G C A) (Sq G C E) := by rw [hCA_AC, hCE_ACsq]
      _ = Sq G A E := hCAEpy

  have hHE_CDsq : Sq G H E = Sq G C D := AA.squareCongr hHE_CD
  have hHF_CDsq : Sq G H F = Sq G C D := AA.squareCongr hHF_CD
  have htwiceCD : Add G (Sq G C D) (Sq G C D) = Sq G E F := by
    calc
      Add G (Sq G C D) (Sq G C D)
          = Add G (Sq G H E) (Sq G H F) := by rw [hHE_CDsq, hHF_CDsq]
      _ = Sq G E F := hHEFpy

  calc
    Add G (Sq G A D) (Sq G D Bp) = Sq G A F := hADDB_AF
    _ = Add G (Sq G A E) (Sq G E F) := hAE_EF_AF.symm
    _ = Add G
          (Add G (Sq G A C) (Sq G A C))
          (Add G (Sq G C D) (Sq G C D)) := by rw [htwiceAC, htwiceCD]
    _ = Add G
          (Add G (Sq G A C) (Sq G C D))
          (Add G (Sq G A C) (Sq G C D)) :=
            addFourPerm G _ _ _ _

/-- Euclid II.9. -/
theorem proposition9
    (G : Geometry)
    [P : Postulates G] [I : ImplicitAxioms G] [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G] [TriangleAreaGeometry G] [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G] [AO : AngleOrderImplicitAxioms G]
    [D34 : Proposition34ImplicitAxioms G] [C46 : Proposition46ImplicitAxioms G]
    [LaterAreaGeometry G] [AF : AreaFoundations G] [QuadPartitionGeometry G]
    [AS : AreaSumFoundations G] [SF : SquareAreaFoundations G]
    [PD : PythagoreanDiagramAxioms G]
    [AreaGeometry G] [AA : AreaAxioms G] [B : Book1AreaMagnitudeBridge G]
    [D9 : Proposition9_10DiagramAxioms G]
    {A C D Bp : G.Point}
    (hmid : IsMidpoint G C A Bp)
    (hACD : G.between A C D)
    (hCDB : G.between C D Bp) :
    Add G (Sq G A D) (Sq G D Bp) =
      Add G (Add G (Sq G A C) (Sq G C D))
        (Add G (Sq G A C) (Sq G C D)) := by
  obtain ⟨E, F, H, hDAF, hrD, hDF, hEAF, hrE,
    hCAE, hrC, hCE, hHEF, hrH, hHE, hHF⟩ := D9.unequalCut hmid hACD hCDB
  exact doubleSquareFromRightDiagram G hDAF hrD hDF hEAF hrE
    hCAE hrC hCE hHEF hrH hHE hHF

end Euclid.Book2
