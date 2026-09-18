import EuclidElements.Book1.LaterImplicitAxioms

namespace Euclid.Book1

open Euclid

class AngleImplicitAxioms
    (G : Geometry)
    [AngleSumGeometry G] : Prop where

  linearPairSupplementary : ∀ {A B C D : G.Point},
    G.between A B C → ¬ G.Collinear A B D →
    Supplementary G ⟨A, B, D⟩ ⟨D, B, C⟩

  supplementarySymm : ∀ {α β : Angle G.Point},
    Supplementary G α β → Supplementary G β α

  equalSupplements : ∀ {α β γ : Angle G.Point},
    Supplementary G α β → Supplementary G α γ →
    G.angleCongruent β γ

  supplementaryCongrLeft : ∀ {α α' β : Angle G.Point},
    G.angleCongruent α α' → Supplementary G α β →
    Supplementary G α' β

  supplementaryAdjacentConverse : ∀ {A B C D : G.Point},
    A ≠ B → C ≠ B → D ≠ B →
    Supplementary G ⟨A, B, C⟩ ⟨C, B, D⟩ →
    G.between A B D

  twoAnglesLtTwoRight : ∀ {α β γ : Angle G.Point},
    Supplementary G β γ → G.angleLess α γ →
    G.sumLessThanTwoRight α β

end Euclid.Book1
