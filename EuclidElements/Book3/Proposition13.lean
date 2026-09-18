import EuclidElements.Book3.TangencyFoundations

namespace Euclid.Book3

open Euclid

/-- Euclid III.13, internal case: an internally tangent pair has only one
    contact point.  The external case is analogous. -/
theorem proposition13_internal
    (G : Geometry)
    [T : TangencyOrderGeometry G]
    {c d : G.Circle} {A B : G.Point}
    (hA : T.internallyTangentAt c d A)
    (hB : G.onCircle B c)
    (hBd : G.onCircle B d) :
    B = A :=
  T.internalNoSecondIntersection hA hB hBd

theorem proposition13_external
    (G : Geometry)
    [T : TangencyOrderGeometry G]
    {c d : G.Circle} {A B : G.Point}
    (hA : T.externallyTangentAt c d A)
    (hB : G.onCircle B c)
    (hBd : G.onCircle B d) :
    B = A :=
  T.externalNoSecondIntersection hA hB hBd

end Euclid.Book3
