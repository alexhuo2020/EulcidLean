import EuclidElements.Book1.AreaComplementFoundations

namespace Euclid.Book1

open Euclid

/-- I.43: complements of parallelograms about a diagonal are equal. -/
theorem proposition43
    (G : Geometry)
    [TriangleAreaGeometry G]
    [LaterAreaGeometry G]
    [AreaDiagramGeometry G]
    [AF : AreaComplementFoundations G]
    {A B C D E F H I : G.Point}
    (hdiag : ComplementsAboutDiagonal G A B C D E F H I) :
    QuadAreaEq G A B C D E F H I := by
  exact AF.equalComplements hdiag

end Euclid.Book1
