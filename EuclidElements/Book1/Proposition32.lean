import EuclidElements.Book1.Proposition32ImplicitAxioms

/-!
# Euclid I.32 -- exterior angle and triangle angle sum
-/

namespace Euclid.Book1

open Euclid

theorem proposition32
    (G : Geometry)
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleInteriorGeometry G]
    [AngleSumGeometry G]
    [AngleAdditionGeometry G]
    [AI : AngleImplicitAxioms G]
    [AA : AngleAdditionImplicitAxioms G]
    [P32 : Proposition32ImplicitAxioms G]
    {A B C D : G.Point}
    (hABC : IsTriangle G A B C)
    (hBCD : G.between B C D) :
    AngleSumEq G ⟨B, A, C⟩ ⟨A, B, C⟩ ⟨A, C, D⟩ ∧
    ThreeAnglesTwoRight G ⟨B, A, C⟩ ⟨A, B, C⟩ ⟨B, C, A⟩ := by
  obtain ⟨E, hins, hBAC_ACE, hABC_ECD⟩ :=
    P32.parallelAtVertexDiagram hABC hBCD
  have hsplit : AngleSumEq G ⟨A, C, E⟩ ⟨E, C, D⟩ ⟨A, C, D⟩ :=
    AA.splitInside hins
  have hext : AngleSumEq G ⟨B, A, C⟩ ⟨A, B, C⟩ ⟨A, C, D⟩ :=
    AA.sumCongr hBAC_ACE hABC_ECD hsplit

  have hBCAtri : IsTriangle G B C A := L.triangleCycle hABC
  have hsupp : Supplementary G ⟨B, C, A⟩ ⟨A, C, D⟩ :=
    AI.linearPairSupplementary hBCD hBCAtri.2.2.2
  have hsum : ThreeAnglesTwoRight G ⟨B, A, C⟩ ⟨A, B, C⟩ ⟨B, C, A⟩ :=
    AA.supplementaryReplaceSum hext hsupp
  exact ⟨hext, hsum⟩

end Euclid.Book1
