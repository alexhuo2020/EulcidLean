import EuclidElements.Book2.Proposition14Diagram

/-! # Euclid II.14 -/
namespace Euclid.Book2

open Euclid
open Euclid.Book1

/-- Construct a square equal in area to a given rectilinear figure. -/
theorem proposition14
    (G : Geometry)
    [P : Postulates G] [I : ImplicitAxioms G] [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G] [TriangleAreaGeometry G] [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G] [AO : AngleOrderImplicitAxioms G]
    [D34 : Proposition34ImplicitAxioms G] [C46 : Proposition46ImplicitAxioms G]
    [LaterAreaGeometry G] [AF : AreaFoundations G]
    [AT : AreaTriangleConstructionAxioms G]
    [PolygonTriangulationGeometry G] [PT : PolygonTriangulationFoundations G]
    [PC : ParallelogramCompositionAxioms G]
    [QuadPartitionGeometry G] [AS : AreaSumFoundations G]
    [SF : SquareAreaFoundations G] [PD : PythagoreanDiagramAxioms G]
    [RA : RightAngleCongruenceAxioms G]
    [AreaGeometry G] [AA : AreaAxioms G] [BM : Book1AreaMagnitudeBridge G]
    [D14 : Proposition14DiagramAxioms G]
    (p : Polygon G.Point)
    (hfig : RectilinearFigure G p) :
    ∃ U V : G.Point, PolygonArea G p = Sq G U V := by
  obtain ⟨α, hvalid, hrightα⟩ := D14.rightAngleWitness
  obtain ⟨A, B, C, D, hpara, hpolyEq, hangle⟩ :=
    proposition45 G p hfig hvalid
  have hright : RightAngle G ⟨D, A, B⟩ :=
    RA.rightAngleOfCongruent hangle hrightα
  have hpolyQuad : PolygonArea G p = QuadArea G A B C D :=
    BM.polygonArea hpolyEq
  have hquadRect : QuadArea G A B C D = Rect G A B A D :=
    BM.rectangleArea hpara hright
  have hpolyRect : PolygonArea G p = Rect G A B A D :=
    hpolyQuad.trans hquadRect

  rcases D14.rectangleCase hpara hright with hEq | hUnequal
  · have hrectCong : Rect G A B A B = Rect G A B A D :=
      AA.rectCongrRight hEq
    have hrectSq : Rect G A B A D = Sq G A B := by
      calc
        Rect G A B A D = Rect G A B A B := hrectCong.symm
        _ = Sq G A B := (AA.squareAsRectangle A B).symm
    exact ⟨A, B, hpolyRect.trans hrectSq⟩

  · obtain ⟨X, H, Y, Z, Q, hmid, hXHY, hHYZ, hsides,
      hYHQ, hrightY, hHQ_HZ⟩ := hUnequal
    have h5 := proposition5 G hmid hXHY hHYZ
    have hpy := pythagoreanMagnitude G hYHQ hrightY
    have hHY_YH : Sq G H Y = Sq G Y H :=
      AA.squareCongr (I.segmentReverse H Y)
    have hHQ_HZsq : Sq G H Q = Sq G H Z := AA.squareCongr hHQ_HZ
    have hpy' : Add G (Sq G H Y) (Sq G Y Q) = Sq G H Z := by
      calc
        Add G (Sq G H Y) (Sq G Y Q)
            = Add G (Sq G Y H) (Sq G Y Q) :=
                addCongrLeft G hHY_YH (Sq G Y Q)
        _ = Sq G H Q := hpy
        _ = Sq G H Z := hHQ_HZsq
    have hcommon :
        Add G (Sq G H Y) (Rect G X Y Y Z) =
          Add G (Sq G H Y) (Sq G Y Q) := by
      calc
        Add G (Sq G H Y) (Rect G X Y Y Z)
            = Add G (Rect G X Y Y Z) (Sq G H Y) := AA.addComm _ _
        _ = Sq G H Z := h5
        _ = Add G (Sq G H Y) (Sq G Y Q) := hpy'.symm
    have hXYsq : Rect G X Y Y Z = Sq G Y Q :=
      AA.addCancelLeft (Sq G H Y) _ _ hcommon

    have hrectTarget : Rect G X Y Y Z = Rect G A B A D := by
      rcases hsides with hdirect | hswap
      · have h1 : Rect G X Y Y Z = Rect G A B Y Z :=
          AA.rectCongrLeft hdirect.1
        have h2 : Rect G A B Y Z = Rect G A B A D :=
          AA.rectCongrRight hdirect.2
        exact h1.trans h2
      · have h1 : Rect G X Y Y Z = Rect G A D Y Z :=
          AA.rectCongrLeft hswap.1
        have h2 : Rect G A D Y Z = Rect G A D A B :=
          AA.rectCongrRight hswap.2
        exact h1.trans (h2.trans (AA.rectSymm A D A B))

    have htargetSq : Rect G A B A D = Sq G Y Q :=
      hrectTarget.symm.trans hXYsq
    exact ⟨Y, Q, hpolyRect.trans htargetSq⟩

end Euclid.Book2
