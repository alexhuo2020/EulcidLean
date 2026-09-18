import EuclidElements.Book3.TangencyFoundations

namespace Euclid.Book3

open Euclid

/-- Euclid III.12: for external tangency, the contact point lies between the
    two centers. -/
theorem proposition12
    (G : Geometry)
    [T : TangencyOrderGeometry G]
    {c d : G.Circle} {O P A : G.Point}
    (htouch : T.externallyTangentAt c d A)
    (hOc : G.isCenter c O)
    (hPd : G.isCenter d P) :
    G.between O A P := by
  have hcommon := T.externalCommonPoint htouch
  have hcol : G.Collinear O P A := by
    by_cases hc : G.Collinear O P A
    · exact hc
    · obtain ⟨X, hXA, hXc, hXd⟩ :=
        T.noncollinearCommonPointGivesSecond hOc hPd hcommon.1 hcommon.2 hc
      have hXT : X = A := T.externalNoSecondIntersection htouch hXc hXd
      exact False.elim (hXA hXT)
  exact T.externalOrderOfCollinearCenters htouch hOc hPd hcol

end Euclid.Book3
