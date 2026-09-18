import EuclidElements.Book1.LaterImplicitAxioms

/-!
# Euclid I.4 -- SAS
-/

namespace Euclid.Book1

open Euclid

theorem proposition4
    (G : Geometry)
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [LaterImplicitAxioms G]
    {A B C D E F : G.Point}
    (hABC : IsTriangle G A B C)
    (hDEF : IsTriangle G D E F)
    (hAB : G.segmentCongruent A B D E)
    (hAC : G.segmentCongruent A C D F)
    (hA : G.angleCongruent ⟨B, A, C⟩ ⟨E, D, F⟩) :
    G.segmentCongruent B C E F ∧
    G.angleCongruent ⟨A, B, C⟩ ⟨D, E, F⟩ ∧
    G.angleCongruent ⟨A, C, B⟩ ⟨D, F, E⟩ ∧
    TriangleAreaEq G A B C D E F := by
  exact LaterImplicitAxioms.sas hABC hDEF hAB hAC hA

end Euclid.Book1
