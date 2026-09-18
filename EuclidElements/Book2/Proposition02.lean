import EuclidElements.Book2.Proposition01

/-! # Euclid II.2 -/
namespace Euclid.Book2
open Euclid

/-- If a straight line is cut at random, the rectangle contained by the whole
and either part together with the rectangle contained by the whole and the
other part equals the square on the whole. -/
theorem proposition2
    (G : Geometry) [AreaGeometry G] [A : AreaAxioms G]
    {P Q R : G.Point}
    (h : G.between P Q R) :
    Sq G P R = Add G (Rect G P R P Q) (Rect G P R Q R) := by
  rw [A.squareAsRectangle]
  exact A.rectCutRight h

end Euclid.Book2
