import EuclidElements.Book2.Proposition03

/-! # Euclid II.4 -/
namespace Euclid.Book2
open Euclid

/-- If a straight line is cut at random, the square on the whole equals the
squares on the two parts together with twice the rectangle contained by the
parts.  The right side is left in Euclid's geometric decomposition order. -/
theorem proposition4
    (G : Geometry) [AreaGeometry G] [A : AreaAxioms G]
    {P Q R : G.Point}
    (h : G.between P Q R) :
    Sq G P R =
      Add G
        (Add G (Sq G P Q) (Rect G P Q Q R))
        (Add G (Rect G P Q Q R) (Sq G Q R)) := by
  have hwhole := A.rectCutLeft (D := P) (E := R) h
  have hleft := A.rectCutRight (A := P) (B := Q) h
  have hright := A.rectCutRight (A := Q) (B := R) h
  rw [A.squareAsRectangle]
  calc
    Rect G P R P R
        = Add G (Rect G P Q P R) (Rect G Q R P R) := hwhole
    _ = Add G
          (Add G (Rect G P Q P Q) (Rect G P Q Q R))
          (Add G (Rect G Q R P Q) (Rect G Q R Q R)) := by
            rw [hleft, hright]
    _ = Add G
          (Add G (Sq G P Q) (Rect G P Q Q R))
          (Add G (Rect G P Q Q R) (Sq G Q R)) := by
            rw [← A.squareAsRectangle P Q, ← A.squareAsRectangle Q R,
              A.rectSymm Q R P Q]

end Euclid.Book2
