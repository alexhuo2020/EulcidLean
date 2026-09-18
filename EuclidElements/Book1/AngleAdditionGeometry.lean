import EuclidElements.Book1.AngleImplicitAxioms

namespace Euclid.Book1

open Euclid

/-- Synthetic angle-addition language; no numerical angle measure is used. -/
class AngleAdditionGeometry (G : Geometry) where
  sumEq : Angle G.Point → Angle G.Point → Angle G.Point → Prop
  threeTwoRight : Angle G.Point → Angle G.Point → Angle G.Point → Prop

def AngleSumEq (G : Geometry) [A : AngleAdditionGeometry G]
    (α β γ : Angle G.Point) : Prop := A.sumEq α β γ

def ThreeAnglesTwoRight (G : Geometry) [A : AngleAdditionGeometry G]
    (α β γ : Angle G.Point) : Prop := A.threeTwoRight α β γ

class AngleAdditionImplicitAxioms
    (G : Geometry)
    [AngleInteriorGeometry G]
    [AngleSumGeometry G]
    [AngleAdditionGeometry G] : Prop where
  splitInside : ∀ {A B C D : G.Point},
    InsideAngle G A B C D →
    AngleSumEq G ⟨A, B, D⟩ ⟨D, B, C⟩ ⟨A, B, C⟩

  sumCongr : ∀ {α α' β β' γ : Angle G.Point},
    G.angleCongruent α α' → G.angleCongruent β β' →
    AngleSumEq G α' β' γ → AngleSumEq G α β γ

  supplementaryReplaceSum : ∀ {α β γ δ : Angle G.Point},
    AngleSumEq G α β γ → Supplementary G δ γ →
    ThreeAnglesTwoRight G α β δ

end Euclid.Book1
