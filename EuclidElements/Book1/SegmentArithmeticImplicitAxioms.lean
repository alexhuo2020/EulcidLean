import EuclidElements.Book1.AngleOrderImplicitAxioms

namespace Euclid.Book1

open Euclid

/-- Synthetic segment-addition facts used by the triangle inequality block. -/
class SegmentArithmeticImplicitAxioms
    (G : Geometry)
    [SegmentOrder G]
    [SegmentSumGeometry G] : Prop where
  extendByCongruent : ∀ {B A C : G.Point},
    B ≠ A → A ≠ C →
    ∃ D : G.Point, G.between B A D ∧ G.segmentCongruent A D A C

  extensionTriangles : ∀ {A B C D : G.Point},
    IsTriangle G A B C → G.between B A D →
    IsTriangle G A C D ∧ IsTriangle G B C D

  sumGreater_from_extension : ∀ {B A C D : G.Point},
    G.between B A D → G.segmentCongruent A D A C →
    SegmentLess G B C B D →
    SegmentSumGreater G B A A C B C

  sumGreater_reverse_first : ∀ {A B C D E F : G.Point},
    SegmentSumGreater G A B C D E F → SegmentSumGreater G B A C D E F

  sumGreater_reverse_second : ∀ {A B C D E F : G.Point},
    SegmentSumGreater G A B C D E F → SegmentSumGreater G A B D C E F

  sumGreater_reverse_result : ∀ {A B C D E F : G.Point},
    SegmentSumGreater G A B C D E F → SegmentSumGreater G A B C D F E

  combineInteriorBrokenLines : ∀ {A B C D E : G.Point},
    G.between A E C → G.between B D E →
    SegmentSumGreater G B A A E B E →
    SegmentSumGreater G E D D C E C →
    SegmentSumLess G B D D C B A A C

end Euclid.Book1
