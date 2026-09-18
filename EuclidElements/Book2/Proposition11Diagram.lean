import EuclidElements.Book2.Proposition10

namespace Euclid.Book2

open Euclid
open Euclid.Book1

/-- Geometry/region-decomposition data of Euclid II.11.  The fields describe
Euclid's two squares and the common subregion `AK`; they do not assert the final
rectangle=square conclusion. -/
class Proposition11DiagramAxioms
    (G : Geometry) [AreaGeometry G] : Prop where
  construct : ∀ {A B : G.Point}, A ≠ B →
    ∃ C E F H : G.Point,
      IsMidpoint G E C A ∧
      G.between C A F ∧
      G.between E A F ∧
      G.segmentCongruent E F E B ∧
      IsTriangle G A E B ∧
      RightAngle G ⟨E, A, B⟩ ∧
      G.between A H B ∧
      ∃ common : Area G,
        Rect G C F A F = Add G common (Sq G A H) ∧
        Sq G A B = Add G common (Rect G A B B H)

end Euclid.Book2
