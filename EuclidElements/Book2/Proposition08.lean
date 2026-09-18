import EuclidElements.Book2.Proposition07

/-! # Euclid II.8 -/
namespace Euclid.Book2
open Euclid

/-- If a straight line is cut at random, four times the rectangle contained by
the whole and one part, together with the square on the other part, equals the
square on the line composed of the whole and the first-mentioned part.
Configuration: `P-Q-R-S`, with `RS ≅ QR`. -/
theorem proposition8
    (G : Geometry) [AreaGeometry G] [A : AreaAxioms G]
    {P Q R S : G.Point}
    (hPQR : G.between P Q R)
    (hPRS : G.between P R S)
    (hRS_QR : G.segmentCongruent R S Q R) :
    Add G
      (Add G
        (Add G (Rect G P R Q R) (Rect G P R Q R))
        (Add G (Rect G P R Q R) (Rect G P R Q R)))
      (Sq G P Q) = Sq G P S := by
  let r : Area G := Rect G P R Q R
  let q : Area G := Sq G Q R
  let p : Area G := Sq G P Q
  have h7 : Add G (Sq G P R) q = Add G (Add G r r) p := by
    simpa [r, q, p] using proposition7 G hPQR
  have hrect : Rect G P R R S = r := by
    simpa [r] using A.rectCongrRight hRS_QR
  have hsq : Sq G R S = q := by
    simpa [q] using A.squareCongr hRS_QR
  have h4 := proposition4 G hPRS
  change Add G (Add G (Add G r r) (Add G r r)) p = Sq G P S
  calc
    Add G (Add G (Add G r r) (Add G r r)) p
        = Add G (Add G (Add G r r) p) (Add G r r) :=
            addSwapMiddle G (Add G r r) (Add G r r) p
    _ = Add G (Add G (Sq G P R) q) (Add G r r) := by rw [h7]
    _ = Add G (Add G (Sq G P R) r) (Add G q r) :=
          addFourPerm G (Sq G P R) q r r
    _ = Add G (Add G (Sq G P R) r) (Add G r q) := by rw [A.addComm q r]
    _ = Add G
          (Add G (Sq G P R) (Rect G P R R S))
          (Add G (Rect G P R R S) (Sq G R S)) := by rw [hrect, hsq]
    _ = Sq G P S := h4.symm

end Euclid.Book2
