import EuclidElements.Book3.Proposition04

namespace Euclid.Book3

open Euclid

/-- Euclid III.5: two circles which cut one another cannot have the same
    center. -/
theorem proposition5
    (G : Geometry)
    [E : CircleExtensionalityAxioms G]
    {c d : G.Circle} {A B O : G.Point}
    (hcut : CirclesCutAt G c d A B)
    (hneq : c ≠ d)
    (hc : G.isCenter c O) (hd : G.isCenter d O) : False := by
  have heq : c = d := E.sameCenterCommonPoint hc hd hcut.2.1 hcut.2.2.1
  exact hneq heq

end Euclid.Book3
