import EuclidElements.Book1.AreaFoundations

namespace Euclid.Book1

open Euclid

/-- I.39: equal triangles on the same base and same side lie between the same parallels. -/
theorem proposition39
    (G : Geometry)
    [I : ImplicitAxioms G]
    [TriangleAreaGeometry G]
    [LaterAreaGeometry G]
    [AF : AreaFoundations G]
    {A B C D : G.Point} {base : G.Line}
    (h1 : IsTriangle G A B C) (h2 : IsTriangle G D B C)
    (hEq : TriangleAreaEq G A B C D B C)
    (hBb : G.onLine B base) (hCb : G.onLine C base)
    (hsame : G.sameSide A D base) :
    ∃ top : G.Line, G.onLine A top ∧ G.onLine D top ∧ Parallel G base top := by
  exact AF.equalAreaEqualBaseDeterminesParallel h1 h2 (I.segmentRefl B C) hEq
    hBb hCb hBb hCb hsame

end Euclid.Book1
