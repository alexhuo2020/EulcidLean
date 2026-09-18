import EuclidElements.Book2.AreaLemmas

/-! # Euclid II.5 -/
namespace Euclid.Book2
open Euclid
open Euclid.Book1

/-- If a straight line is bisected and also cut unequally, the rectangle
contained by the unequal parts together with the square on the segment between
the two points of section equals the square on the half.  We state the
configuration with `A-C-D-B`. -/
theorem proposition5
    (G : Geometry) [I : ImplicitAxioms G]
    [AreaGeometry G] [A : AreaAxioms G]
    {A0 C D B : G.Point}
    (hmid : IsMidpoint G C A0 B)
    (hACD : G.between A0 C D)
    (hCDB : G.between C D B) :
    Add G (Rect G A0 D D B) (Sq G C D) = Sq G C B := by
  have hcut : Rect G A0 D D B =
      Add G (Rect G A0 C D B) (Rect G C D D B) :=
    A.rectCutLeft hACD
  have hAC_CB : G.segmentCongruent A0 C C B := hmid.2
  have hrect : Rect G A0 C D B = Rect G C B D B :=
    A.rectCongrLeft hAC_CB
  have h3 := proposition3 G hCDB
  have h2 := proposition2 G hCDB
  calc
    Add G (Rect G A0 D D B) (Sq G C D)
        = Add G
            (Add G (Rect G A0 C D B) (Rect G C D D B))
            (Sq G C D) := by rw [hcut]
    _ = Add G
          (Add G (Rect G C B D B) (Rect G C D D B))
          (Sq G C D) := by rw [hrect]
    _ = Add G
          (Add G (Sq G C D) (Rect G C D D B))
          (Rect G C B D B) := addThreePerm G _ _ _
    _ = Add G (Rect G C B C D) (Rect G C B D B) := by rw [h3]
    _ = Sq G C B := h2.symm

end Euclid.Book2
