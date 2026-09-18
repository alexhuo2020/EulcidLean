import EuclidElements.Book2.AreaAxioms

/-! # Euclid II.1 -/
namespace Euclid.Book2
open Euclid
open Euclid.Book1

/-- If one of two straight lines is cut into any number of segments, the
rectangle contained by the two whole lines equals the sum of the rectangles
contained by the uncut line and each segment. -/
theorem proposition1
    (G : Geometry) [AreaGeometry G] [AA : AreaAxioms G]
    {P Q X Y : G.Point} {parts : List (G.Point × G.Point)}
    (h : SegmentChain G X Y parts) :
    Rect G P Q X Y = AreaSum G (RectanglesOnChain G P Q parts) := by
  induction h with
  | single U V =>
      change Rect G P Q U V = Add G (Rect G P Q U V) (Zero G)
      exact (AA.addZeroRight _).symm
  | split hUWX hrest ih =>
      rw [AA.rectCutRight hUWX]
      change Add G (Rect G P Q _ _) (Rect G P Q _ _) =
        Add G (Rect G P Q _ _) (AreaSum G (RectanglesOnChain G P Q _))
      rw [ih]

end Euclid.Book2
