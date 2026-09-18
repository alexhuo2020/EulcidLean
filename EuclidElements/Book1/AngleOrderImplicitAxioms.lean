import EuclidElements.Book1.AngleImplicitAxioms

namespace Euclid.Book1

open Euclid

/-- Generic order facts for synthetic angles. -/
class AngleOrderImplicitAxioms (G : Geometry) [AngleInteriorGeometry G] : Prop where
  lt_trans : ∀ {α β γ : Angle G.Point},
    G.angleLess α β → G.angleLess β γ → G.angleLess α γ
  lt_congr_left : ∀ {α α' β : Angle G.Point},
    G.angleCongruent α α' → G.angleLess α β → G.angleLess α' β
  lt_congr_right : ∀ {α β β' : Angle G.Point},
    G.angleCongruent β β' → G.angleLess α β → G.angleLess α β'
  lt_not_congr : ∀ {α β : Angle G.Point},
    G.angleLess α β → ¬ G.angleCongruent α β
  angleTrichotomy : ∀ α β : Angle G.Point,
    G.angleCongruent α β ∨ G.angleLess α β ∨ G.angleLess β α
  properSubangleLeft : ∀ {A B C D : G.Point},
    InsideAngle G A B C D → G.angleLess ⟨A, B, D⟩ ⟨A, B, C⟩
  properSubangleRight : ∀ {A B C D : G.Point},
    InsideAngle G A B C D → G.angleLess ⟨D, B, C⟩ ⟨A, B, C⟩
  sidePointInsideOppositeAngle : ∀ {A B C D : G.Point},
    IsTriangle G A B C → G.between A D C →
    InsideAngle G A B C D

class Proposition16ImplicitAxioms
    (G : Geometry)
    [TriangleInteriorGeometry G]
    [AngleInteriorGeometry G] : Prop where
  constructionTriangles : ∀ {A B C E F : G.Point},
    IsTriangle G A B C →
    G.between A E C → G.between B E F →
    IsTriangle G E A B ∧ IsTriangle G E C F

  constructedRayInsideExterior : ∀ {A B C D E F : G.Point},
    IsTriangle G A B C →
    G.between B C D →
    IsMidpoint G E A C →
    G.between B E F →
    G.segmentCongruent E B E F →
    InsideAngle G A C D F

  mirroredExteriorReduction : ∀ {A B C D : G.Point},
    IsTriangle G A B C → G.between B C D →
    G.angleLess ⟨B, A, C⟩ ⟨A, C, D⟩ →
    G.angleLess ⟨A, B, C⟩ ⟨A, C, D⟩

end Euclid.Book1
