import EuclidElements.Book1.Proposition13
import EuclidElements.Book1.Proposition16

/-!
# Euclid I.17 -- any two angles of a triangle are less than two right angles
-/

namespace Euclid.Book1

open Euclid

theorem proposition17
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [LaterImplicitAxioms G]
    [AS : AngleImplicitAxioms G]
    [AngleOrderImplicitAxioms G]
    [Proposition16ImplicitAxioms G]
    {A B C : G.Point}
    (htri : IsTriangle G A B C) :
    G.sumLessThanTwoRight ⟨A, B, C⟩ ⟨B, C, A⟩ := by
  have hBC : B ≠ C := htri.2.1
  obtain ⟨D, hBCD⟩ := P.postulate2 B C hBC
  have hext := proposition16 G htri hBCD
  have hABC_ACD : G.angleLess ⟨A, B, C⟩ ⟨A, C, D⟩ := hext.2
  have hnoncolBCA : ¬ G.Collinear B C A := by
    intro h
    rcases h with ⟨l, hBl, hCl, hAl⟩
    exact htri.2.2.2 ⟨l, hAl, hBl, hCl⟩
  have hsupp0 : Supplementary G ⟨B, C, A⟩ ⟨A, C, D⟩ :=
    proposition13 G hBCD hnoncolBCA
  exact AS.twoAnglesLtTwoRight hsupp0 hABC_ACD

end Euclid.Book1
