import EuclidElements.Book2.Proposition09

/-! # Euclid II.10 -/
namespace Euclid.Book2

open Euclid
open Euclid.Book1

/-- Euclid II.10: if a straight line is bisected and produced, the squares on
the whole produced line and the produced part equal twice the squares on the
half and on the line made up of the half and produced part. -/
theorem proposition10
    (G : Geometry)
    [P : Postulates G] [I : ImplicitAxioms G] [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G] [TriangleAreaGeometry G] [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G] [AO : AngleOrderImplicitAxioms G]
    [D34 : Proposition34ImplicitAxioms G] [C46 : Proposition46ImplicitAxioms G]
    [LaterAreaGeometry G] [AF : AreaFoundations G] [QuadPartitionGeometry G]
    [AS : AreaSumFoundations G] [SF : SquareAreaFoundations G]
    [PD : PythagoreanDiagramAxioms G]
    [AreaGeometry G] [AA : AreaAxioms G] [B : Book1AreaMagnitudeBridge G]
    [D10 : Proposition9_10DiagramAxioms G]
    {A C Bp D : G.Point}
    (hmid : IsMidpoint G C A Bp)
    (hABD : G.between A Bp D)
    (hCBD : G.between C Bp D) :
    Add G (Sq G A D) (Sq G D Bp) =
      Add G (Add G (Sq G A C) (Sq G C D))
        (Add G (Sq G A C) (Sq G C D)) := by
  obtain ⟨E, F, H, hDAF, hrD, hDF, hEAF, hrE,
    hCAE, hrC, hCE, hHEF, hrH, hHE, hHF⟩ := D10.produced hmid hABD hCBD
  exact doubleSquareFromRightDiagram G hDAF hrD hDF hEAF hrE
    hCAE hrC hCE hHEF hrH hHE hHF

end Euclid.Book2
