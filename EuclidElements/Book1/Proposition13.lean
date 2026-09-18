import EuclidElements.Book1.AngleImplicitAxioms

/-!
# Euclid I.13 -- a straight line standing on another makes two right angles
-/

namespace Euclid.Book1

open Euclid

theorem proposition13
    (G : Geometry)
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [LaterImplicitAxioms G]
    [AS : AngleImplicitAxioms G]
    {A B C D : G.Point}
    (hABC : G.between A B C)
    (hnoncol : ¬ G.Collinear A B D) :
    Supplementary G ⟨A, B, D⟩ ⟨D, B, C⟩ := by
  exact AS.linearPairSupplementary hABC hnoncol

end Euclid.Book1
