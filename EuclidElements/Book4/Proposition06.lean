import EuclidElements.Book4.SquareConstructionFoundations

namespace Euclid.Book4

open Euclid
open Euclid.Book1

/-- Euclid IV.6: inscribe a square in a given circle. -/
theorem proposition6
    (G : Geometry)
    [S : SquareBook4ConstructionAxioms G]
    {c : G.Circle} :
    ∃ A B C D : G.Point, SquareInscribedInCircle G c A B C D := by
  obtain ⟨A, B, C, D, hquad, hA, hB, hC, hD, heq, hright⟩ :=
    S.inscribedFrame c
  exact ⟨A, B, C, D, ⟨hquad, heq, hright⟩, hA, hB, hC, hD⟩

end Euclid.Book4
