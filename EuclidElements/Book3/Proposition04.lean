import EuclidElements.Book3.Proposition03

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Generic uniqueness of the perpendicular through a given point to a fixed
    line. -/
class PerpendicularUniquenessAxioms (G : Geometry) : Prop where
  throughPoint : ∀ {l n m : G.Line} {P : G.Point},
    Perpendicular G l m → Perpendicular G n m →
    G.onLine P l → G.onLine P n → G.onLine P m → l = n

/-- Euclid III.4: two distinct noncentral chords that intersect cannot bisect
    one another. -/
theorem proposition4
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [C : CircleBasicAxioms G]
    [U : PerpendicularUniquenessAxioms G]
    {c : G.Circle} {O A B C D M : G.Point} {lAB lCD : G.Line}
    (hcenter : G.isCenter c O)
    (hAB : Chord G c A B) (hCD : Chord G c C D)
    (hA : G.onLine A lAB) (hB : G.onLine B lAB) (hMAB : G.onLine M lAB)
    (hC : G.onLine C lCD) (hD : G.onLine D lCD) (hMCD : G.onLine M lCD)
    (hABnoncentral : ¬ G.onLine O lAB)
    (hCDnoncentral : ¬ G.onLine O lCD)
    (hneq : lAB ≠ lCD)
    (hmidAB : IsMidpoint G M A B)
    (hmidCD : IsMidpoint G M C D) : False := by
  have hOM : O ≠ M := by
    intro h
    subst O
    exact hABnoncentral hMAB
  obtain ⟨m, hOm, hMm⟩ := P.postulate1 O M hOM
  have hpAB : Perpendicular G lAB m :=
    proposition3_bisector_perpendicular G hcenter hAB
      hA hB hMAB hOm hMm hABnoncentral hmidAB
  have hpCD : Perpendicular G lCD m :=
    proposition3_bisector_perpendicular G hcenter hCD
      hC hD hMCD hOm hMm hCDnoncentral hmidCD
  have heq : lAB = lCD := U.throughPoint hpAB hpCD hMAB hMCD hMm
  exact hneq heq

end Euclid.Book3
