import EuclidElements.Book1.Proposition34
import EuclidElements.Book1.AreaFoundations

namespace Euclid.Book1

open Euclid

/-- I.41: a parallelogram is double the triangle cut off by one diagonal. -/
theorem proposition41
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [D34 : Proposition34ImplicitAxioms G]
    [LaterAreaGeometry G]
    [AF : AreaFoundations G]
    {A B C D : G.Point}
    (hpara : Parallelogram G A B C D)
    (_htri : IsTriangle G A B C) :
    QuadDoubleTriangle G A B C D A B C := by
  have h34 := proposition34 G hpara
  have hABC_ACD : TriangleAreaEq G A B C A C D := by
    have hCDA_ACD : TriangleAreaEq G C D A A C D :=
      L.areaEq_symm (L.areaEq_cycle A C D)
    exact L.areaEq_trans h34.2.2.2 hCDA_ACD
  exact AF.quadDouble_of_equalDiagonalHalves hABC_ACD

end Euclid.Book1
