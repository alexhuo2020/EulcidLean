import EuclidElements.Book2.Proposition11Diagram
import EuclidElements.Book2.Book1AreaBridge

/-! # Euclid II.11 -/
namespace Euclid.Book2

open Euclid
open Euclid.Book1

/-- Cut a given straight line so that the rectangle contained by the whole and
one segment equals the square on the remaining segment. -/
theorem proposition11
    (G : Geometry)
    [P : Postulates G] [I : ImplicitAxioms G] [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G] [TriangleAreaGeometry G] [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G] [AO : AngleOrderImplicitAxioms G]
    [D34 : Proposition34ImplicitAxioms G] [C46 : Proposition46ImplicitAxioms G]
    [LaterAreaGeometry G] [AF : AreaFoundations G] [QuadPartitionGeometry G]
    [AS : AreaSumFoundations G] [SF : SquareAreaFoundations G]
    [PD : PythagoreanDiagramAxioms G]
    [AreaGeometry G] [AA : AreaAxioms G] [B : Book1AreaMagnitudeBridge G]
    [D11 : Proposition11DiagramAxioms G]
    {A Bp : G.Point}
    (hAB : A ≠ Bp) :
    ∃ H : G.Point,
      G.between A H Bp ∧ Rect G A Bp Bp H = Sq G A H := by
  obtain ⟨C, E, F, H, hmid, hCAF, hEAF, hEF_EB,
    hAEB, hright, hAHB, common, hbig, habSquare⟩ := D11.construct hAB

  have h6 := proposition6 G hmid hCAF hEAF
  have hpy := pythagoreanMagnitude G hAEB hright
  have hEF_EBsq : Sq G E F = Sq G E Bp := AA.squareCongr hEF_EB
  have hEA_AE : Sq G E A = Sq G A E :=
    AA.squareCongr (I.segmentReverse E A)

  have hcancelEq :
      Add G (Sq G E A) (Rect G C F A F) =
        Add G (Sq G E A) (Sq G A Bp) := by
    calc
      Add G (Sq G E A) (Rect G C F A F)
          = Add G (Rect G C F A F) (Sq G E A) := AA.addComm _ _
      _ = Sq G E F := h6
      _ = Sq G E Bp := hEF_EBsq
      _ = Add G (Sq G A E) (Sq G A Bp) := hpy.symm
      _ = Add G (Sq G E A) (Sq G A Bp) := by rw [hEA_AE]

  have hrect_sq : Rect G C F A F = Sq G A Bp :=
    AA.addCancelLeft (Sq G E A) _ _ hcancelEq

  have hcommon :
      Add G common (Sq G A H) = Add G common (Rect G A Bp Bp H) := by
    calc
      Add G common (Sq G A H) = Rect G C F A F := hbig.symm
      _ = Sq G A Bp := hrect_sq
      _ = Add G common (Rect G A Bp Bp H) := habSquare

  have hremain : Sq G A H = Rect G A Bp Bp H :=
    AA.addCancelLeft common _ _ hcommon
  exact ⟨H, hAHB, hremain.symm⟩

end Euclid.Book2
