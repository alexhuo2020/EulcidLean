import EuclidElements.Book1.SegmentArithmeticImplicitAxioms

namespace Euclid.Book1

open Euclid

/--
A circle-continuity construction schema: three positive segment magnitudes
satisfying the three triangle inequalities can be realized as a triangle on a
chosen ray. This isolates the continuity content silently used in Euclid I.22.
-/
class TriangleConstructionImplicitAxioms
    (G : Geometry)
    [SegmentSumGeometry G] : Prop where
  constructOnRay : ∀
    {O R A A' B B' C C' : G.Point},
    O ≠ R → A ≠ A' → B ≠ B' → C ≠ C' →
    SegmentSumGreater G A A' B B' C C' →
    SegmentSumGreater G A A' C C' B B' →
    SegmentSumGreater G B B' C C' A A' →
    ∃ K S : G.Point,
      SameRay G O R S ∧
      G.segmentCongruent O K A A' ∧
      G.segmentCongruent O S B B' ∧
      G.segmentCongruent K S C C' ∧
      IsTriangle G O S K

end Euclid.Book1
