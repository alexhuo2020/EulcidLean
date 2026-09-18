import EuclidElements.Book1.AngleImplicitAxioms

/-!
# Euclid I.14 -- converse straight-angle criterion
-/

namespace Euclid.Book1

open Euclid

theorem proposition14
    (G : Geometry)
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [LaterImplicitAxioms G]
    [AS : AngleImplicitAxioms G]
    {A B C D : G.Point}
    (hAB : A ≠ B) (hCB : C ≠ B) (hDB : D ≠ B)
    (hsupp : Supplementary G ⟨A, B, C⟩ ⟨C, B, D⟩) :
    G.between A B D := by
  exact AS.supplementaryAdjacentConverse hAB hCB hDB hsupp

end Euclid.Book1
