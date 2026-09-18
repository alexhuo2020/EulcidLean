import EuclidElements.Book2.Proposition05

/-! # Euclid II.6 -/
namespace Euclid.Book2
open Euclid
open Euclid.Book1

/-- If a straight line is bisected and produced, the rectangle contained by
the whole with the produced part and the produced part, together with the square
on the half, equals the square on the line made up of the half and the produced
part.  Configuration: `A-C-B-D`, with `C` the midpoint of `AB`. -/
theorem proposition6
    (G : Geometry) [I : ImplicitAxioms G]
    [AreaGeometry G] [A : AreaAxioms G]
    {A0 C B D : G.Point}
    (hmid : IsMidpoint G C A0 B)
    (hABD : G.between A0 B D)
    (hCBD : G.between C B D) :
    Add G (Rect G A0 D B D) (Sq G C B) = Sq G C D := by
  have hcut1 : Rect G A0 D B D =
      Add G (Rect G A0 B B D) (Rect G B D B D) :=
    A.rectCutLeft hABD
  have hcut2 : Rect G A0 B B D =
      Add G (Rect G A0 C B D) (Rect G C B B D) :=
    A.rectCutLeft hmid.1
  have hAC_CB : G.segmentCongruent A0 C C B := hmid.2
  have hrect : Rect G A0 C B D = Rect G C B B D :=
    A.rectCongrLeft hAC_CB
  have h4 := proposition4 G hCBD
  calc
    Add G (Rect G A0 D B D) (Sq G C B)
        = Add G
            (Add G (Rect G A0 B B D) (Rect G B D B D))
            (Sq G C B) := by rw [hcut1]
    _ = Add G
          (Add G
            (Add G (Rect G A0 C B D) (Rect G C B B D))
            (Rect G B D B D))
          (Sq G C B) := by rw [hcut2]
    _ = Add G
          (Add G
            (Add G (Rect G C B B D) (Rect G C B B D))
            (Sq G B D))
          (Sq G C B) := by
            rw [hrect, ← A.squareAsRectangle B D]
    _ = Add G
          (Add G (Sq G C B) (Rect G C B B D))
          (Add G (Rect G C B B D) (Sq G B D)) :=
            addFourNestedRotate G _ _ _ _
    _ = Sq G C D := h4.symm

end Euclid.Book2
