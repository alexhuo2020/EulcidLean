import EuclidElements.Book3.TangencyFoundations

namespace Euclid.Book3

open Euclid

/-- Euclid III.11: for internal tangency, the inner center lies between the
    outer center and the contact point. -/
theorem proposition11
    (G : Geometry)
    [T : TangencyOrderGeometry G]
    {c d : G.Circle} {O P A : G.Point}
    (htouch : T.internallyTangentAt c d A)
    (hOc : G.isCenter c O)
    (hPd : G.isCenter d P) :
    G.between O P A := by
  have hcommon := T.internalCommonPoint htouch
  have hcol : G.Collinear O P A := by
    by_cases hc : G.Collinear O P A
    · exact hc
    · obtain ⟨X, hXA, hXc, hXd⟩ :=
        T.noncollinearCommonPointGivesSecond hOc hPd hcommon.1 hcommon.2 hc
      have hXT : X = A := T.internalNoSecondIntersection htouch hXc hXd
      exact False.elim (hXA hXT)
  exact T.internalOrderOfCollinearCenters htouch hOc hPd hcol

end Euclid.Book3
