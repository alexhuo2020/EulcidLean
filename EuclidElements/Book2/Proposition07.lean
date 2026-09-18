import EuclidElements.Book2.Proposition06

/-! # Euclid II.7 -/
namespace Euclid.Book2
open Euclid

/-- If a straight line is cut at random, the square on the whole together with
the square on one part equals twice the rectangle contained by the whole and
that part together with the square on the other part. -/
theorem proposition7
    (G : Geometry) [AreaGeometry G] [A : AreaAxioms G]
    {P Q R : G.Point}
    (h : G.between P Q R) :
    Add G (Sq G P R) (Sq G Q R) =
      Add G
        (Add G (Rect G P R Q R) (Rect G P R Q R))
        (Sq G P Q) := by
  have h4 := proposition4 G h
  have hrect0 := A.rectCutLeft (D := Q) (E := R) h
  have hrect : Rect G P R Q R =
      Add G (Rect G P Q Q R) (Sq G Q R) := by
    calc
      Rect G P R Q R
          = Add G (Rect G P Q Q R) (Rect G Q R Q R) := hrect0
      _ = Add G (Rect G P Q Q R) (Sq G Q R) := by
          rw [← A.squareAsRectangle Q R]
  calc
    Add G (Sq G P R) (Sq G Q R)
        = Add G
            (Add G
              (Add G (Sq G P Q) (Rect G P Q Q R))
              (Add G (Rect G P Q Q R) (Sq G Q R)))
            (Sq G Q R) := by rw [h4]
    _ = Add G
          (Add G
            (Add G (Rect G P Q Q R) (Sq G Q R))
            (Add G (Rect G P Q Q R) (Sq G Q R)))
          (Sq G P Q) := addPattern7 G _ _ _
    _ = Add G
          (Add G (Rect G P R Q R) (Rect G P R Q R))
          (Sq G P Q) := by rw [← hrect]

end Euclid.Book2
