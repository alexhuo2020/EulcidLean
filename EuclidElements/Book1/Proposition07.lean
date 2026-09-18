import EuclidElements.Book1.LaterImplicitAxioms

/-!
# Euclid I.7

On the same base and on the same side, two distinct vertices cannot have both
corresponding sides equal.
-/

namespace Euclid.Book1

open Euclid

theorem proposition7
    (G : Geometry)
    [ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    {A B C D : G.Point}
    (hAB : A ≠ B)
    (hsame : ∃ l : G.Line,
      G.onLine A l ∧ G.onLine B l ∧ G.sameSide C D l)
    (hAC_AD : G.segmentCongruent A C A D)
    (hBC_BD : G.segmentCongruent B C B D) :
    C = D := by
  obtain ⟨l, hAl, hBl, hCDside⟩ := hsame
  exact L.equalDistancesSameSide_unique hAB hAl hBl hCDside hAC_AD hBC_BD

end Euclid.Book1
