import EuclidElements.Book4.SquareConstructionFoundations

namespace Euclid.Book4

open Euclid
open Euclid.Book1
open Euclid.Book3

/-- Euclid IV.7: circumscribe a square about a given circle. -/
theorem proposition7
    (G : Geometry)
    [S : SquareBook4ConstructionAxioms G]
    {c : G.Circle} :
    ∃ A B C D : G.Point, CircleInscribedInSquare G c A B C D := by
  obtain ⟨A, B, C, D, lAB, lBC, lCD, lDA, T, U, V, W,
      hquad, heq, hright, hAB, hBC, hCD, hDA,
      htAB, htBC, htCD, htDA⟩ := S.circumscribedFrame c
  refine ⟨A, B, C, D, ⟨hquad, heq, hright⟩, ?_⟩
  exact ⟨lAB, lBC, lCD, lDA, T, U, V, W,
    hAB, hBC, hCD, hDA, htAB, htBC, htCD, htDA⟩

end Euclid.Book4
