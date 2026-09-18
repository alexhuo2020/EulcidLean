import EuclidElements.Book1.Proposition13
import EuclidElements.Book1.AngleImplicitAxioms

/-!
# Euclid I.15 -- vertical angles are congruent
-/

namespace Euclid.Book1

open Euclid

theorem proposition15
    (G : Geometry)
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [LaterImplicitAxioms G]
    [AS : AngleImplicitAxioms G]
    {A B C D E : G.Point}
    (hABC : G.between A B C)
    (hDBE : G.between D B E)
    (hnoncol : ¬ G.Collinear A B D) :
    G.angleCongruent ⟨A, B, D⟩ ⟨C, B, E⟩ ∧
    G.angleCongruent ⟨D, B, C⟩ ⟨E, B, A⟩ := by
  have hs1 : Supplementary G ⟨A, B, D⟩ ⟨D, B, C⟩ :=
    proposition13 G hABC hnoncol
  have hnoncolDBC : ¬ G.Collinear D B C := by
    intro hDBC
    obtain ⟨l0, hAl0, hBl0, hCl0⟩ := I.betweenCollinear hABC
    rcases hDBC with ⟨l1, hDl1, hBl1, hCl1⟩
    have hBC : B ≠ C := (I.betweenDistinct hABC).2.1
    have hl : l1 = l0 := I.lineUnique hBC hBl1 hCl1 hBl0 hCl0
    apply hnoncol
    exact ⟨l0, hAl0, hBl0, by simpa [hl] using hDl1⟩
  have hs2 : Supplementary G ⟨D, B, C⟩ ⟨C, B, E⟩ :=
    proposition13 G hDBE hnoncolDBC
  have hs1sym : Supplementary G ⟨D, B, C⟩ ⟨A, B, D⟩ :=
    AS.supplementarySymm hs1
  have hvert1 : G.angleCongruent ⟨A, B, D⟩ ⟨C, B, E⟩ :=
    AS.equalSupplements hs1sym hs2

  have hnoncolDBA : ¬ G.Collinear D B A := by
    intro h
    rcases h with ⟨l, hDl, hBl, hAl⟩
    exact hnoncol ⟨l, hAl, hBl, hDl⟩
  have hs3raw : Supplementary G ⟨D, B, A⟩ ⟨A, B, E⟩ :=
    proposition13 G hDBE hnoncolDBA
  have hDBA_ABD : G.angleCongruent ⟨D, B, A⟩ ⟨A, B, D⟩ :=
    LaterImplicitAxioms.angleReverse D B A
  have hs3 : Supplementary G ⟨A, B, D⟩ ⟨A, B, E⟩ :=
    AS.supplementaryCongrLeft hDBA_ABD hs3raw
  have hDBC_ABE : G.angleCongruent ⟨D, B, C⟩ ⟨A, B, E⟩ :=
    AS.equalSupplements hs1 hs3
  have hABE_EBA : G.angleCongruent ⟨A, B, E⟩ ⟨E, B, A⟩ :=
    LaterImplicitAxioms.angleReverse A B E
  have hvert2 : G.angleCongruent ⟨D, B, C⟩ ⟨E, B, A⟩ :=
    I.angleTrans hDBC_ABE hABE_EBA
  exact ⟨hvert1, hvert2⟩

end Euclid.Book1
