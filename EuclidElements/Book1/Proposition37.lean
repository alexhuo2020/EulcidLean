import EuclidElements.Book1.AreaFoundations

namespace Euclid.Book1

open Euclid

/-- I.37: triangles on the same base and between the same parallels are equal. -/
theorem proposition37
    (G : Geometry)
    [I : ImplicitAxioms G]
    [TriangleAreaGeometry G]
    [LaterAreaGeometry G]
    [AF : AreaFoundations G]
    {A B C D : G.Point} {base top : G.Line}
    (h1 : IsTriangle G A B C) (h2 : IsTriangle G D B C)
    (hBb : G.onLine B base) (hCb : G.onLine C base)
    (hAt : G.onLine A top) (hDt : G.onLine D top)
    (hpar : Parallel G base top) :
    TriangleAreaEq G A B C D B C := by
  exact AF.equalBaseSameAltitude h1 h2 (I.segmentRefl B C)
    hBb hCb hBb hCb hAt hDt hpar

end Euclid.Book1
