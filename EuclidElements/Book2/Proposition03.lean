import EuclidElements.Book2.Proposition02

/-! # Euclid II.3 -/
namespace Euclid.Book2
open Euclid

/-- If a straight line is cut at random, the rectangle contained by the whole
and one part equals the square on that part together with the rectangle
contained by the two parts. -/
theorem proposition3
    (G : Geometry) [AreaGeometry G] [A : AreaAxioms G]
    {P Q R : G.Point}
    (h : G.between P Q R) :
    Rect G P R P Q = Add G (Sq G P Q) (Rect G P Q Q R) := by
  have hcut := A.rectCutLeft (D := P) (E := Q) h
  calc
    Rect G P R P Q
        = Add G (Rect G P Q P Q) (Rect G Q R P Q) := hcut
    _ = Add G (Sq G P Q) (Rect G P Q Q R) := by
      rw [← A.squareAsRectangle P Q, A.rectSymm Q R P Q]

end Euclid.Book2
