import EuclidElements.Book3.Proposition05

namespace Euclid.Book3

open Euclid

/-- Euclid III.6: two circles which touch one another cannot have the same
    center. -/
theorem proposition6
    (G : Geometry)
    [E : CircleExtensionalityAxioms G]
    {c d : G.Circle} {T O : G.Point}
    (htouch : CirclesTouchAt G c d T)
    (hneq : c ≠ d)
    (hc : G.isCenter c O) (hd : G.isCenter d O) : False := by
  have heq : c = d := E.sameCenterCommonPoint hc hd htouch.1 htouch.2.1
  exact hneq heq

end Euclid.Book3
