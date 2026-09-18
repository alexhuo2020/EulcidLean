import EuclidElements.Book1.AreaFoundations

namespace Euclid.Book1

open Euclid

/-- I.38: triangles on equal bases and between the same parallels are equal. -/
theorem proposition38
    (G : Geometry)
    [TriangleAreaGeometry G]
    [LaterAreaGeometry G]
    [AF : AreaFoundations G]
    {A B C D E F : G.Point} {base top : G.Line}
    (h1 : IsTriangle G A B C) (h2 : IsTriangle G D E F)
    (hBC_EF : G.segmentCongruent B C E F)
    (hBb : G.onLine B base) (hCb : G.onLine C base)
    (hEb : G.onLine E base) (hFb : G.onLine F base)
    (hAt : G.onLine A top) (hDt : G.onLine D top)
    (hpar : Parallel G base top) :
    TriangleAreaEq G A B C D E F := by
  exact AF.equalBaseSameAltitude h1 h2 hBC_EF
    hBb hCb hEb hFb hAt hDt hpar

end Euclid.Book1
