import EuclidElements.Book1.AreaFoundations

namespace Euclid.Book1

open Euclid

/-- I.40: equal triangles on equal bases, on the same line and same side, lie between the same parallels. -/
theorem proposition40
    (G : Geometry)
    [TriangleAreaGeometry G]
    [LaterAreaGeometry G]
    [AF : AreaFoundations G]
    {A B C D E F : G.Point} {base : G.Line}
    (h1 : IsTriangle G A B C) (h2 : IsTriangle G D E F)
    (hBC_EF : G.segmentCongruent B C E F)
    (hEq : TriangleAreaEq G A B C D E F)
    (hBb : G.onLine B base) (hCb : G.onLine C base)
    (hEb : G.onLine E base) (hFb : G.onLine F base)
    (hsame : G.sameSide A D base) :
    ∃ top : G.Line, G.onLine A top ∧ G.onLine D top ∧ Parallel G base top := by
  exact AF.equalAreaEqualBaseDeterminesParallel h1 h2 hBC_EF hEq
    hBb hCb hEb hFb hsame

end Euclid.Book1
