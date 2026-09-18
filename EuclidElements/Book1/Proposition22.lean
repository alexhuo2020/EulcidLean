import EuclidElements.Book1.TriangleConstructionImplicitAxioms

/-!
# Euclid I.22 -- construct a triangle from three given straight lines
-/

namespace Euclid.Book1

open Euclid

theorem proposition22_onRay
    (G : Geometry)
    [SegmentSumGeometry G]
    [TC : TriangleConstructionImplicitAxioms G]
    {O R A A' B B' C C' : G.Point}
    (hOR : O ≠ R) (hAA : A ≠ A') (hBB : B ≠ B') (hCC : C ≠ C')
    (h1 : SegmentSumGreater G A A' B B' C C')
    (h2 : SegmentSumGreater G A A' C C' B B')
    (h3 : SegmentSumGreater G B B' C C' A A') :
    ∃ K S : G.Point,
      SameRay G O R S ∧
      G.segmentCongruent O K A A' ∧
      G.segmentCongruent O S B B' ∧
      G.segmentCongruent K S C C' ∧
      IsTriangle G O S K := by
  exact TC.constructOnRay hOR hAA hBB hCC h1 h2 h3

end Euclid.Book1
