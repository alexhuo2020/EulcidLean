import EuclidElements.Book1.Proposition34
import EuclidElements.Book1.AreaFoundations

namespace Euclid.Book1

open Euclid

/-- I.35: parallelograms on the same base and between the same parallels are equal. -/
theorem proposition35
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
    {A B C D E F : G.Point} {base top : G.Line}
    (h1 : Parallelogram G A B C D) (h2 : Parallelogram G E B C F)
    (hBb : G.onLine B base) (hCb : G.onLine C base)
    (hAt : G.onLine A top) (hDt : G.onLine D top)
    (hEt : G.onLine E top) (hFt : G.onLine F top)
    (hpar : Parallel G base top) :
    QuadAreaEq G A B C D E B C F := by
  obtain ⟨hABC, _hDCA, _ha1, _ha2⟩ := D34.diagonalData h1
  obtain ⟨hEBC, _hFCE, _he1, _he2⟩ := D34.diagonalData h2

  have hABC_EBC : TriangleAreaEq G A B C E B C :=
    AF.equalBaseSameAltitude hABC hEBC (I.segmentRefl B C)
      hBb hCb hBb hCb hAt hEt hpar

  have h34a := proposition34 G h1
  have h34e := proposition34 G h2

  have hABC_ACD : TriangleAreaEq G A B C A C D := by
    have hCDA_ACD : TriangleAreaEq G C D A A C D :=
      L.areaEq_symm (L.areaEq_cycle A C D)
    exact L.areaEq_trans h34a.2.2.2 hCDA_ACD

  have hEBC_ECF : TriangleAreaEq G E B C E C F := by
    have hCFE_ECF : TriangleAreaEq G C F E E C F :=
      L.areaEq_symm (L.areaEq_cycle E C F)
    exact L.areaEq_trans h34e.2.2.2 hCFE_ECF

  have hACD_ECF : TriangleAreaEq G A C D E C F :=
    L.areaEq_trans (L.areaEq_symm hABC_ACD)
      (L.areaEq_trans hABC_EBC hEBC_ECF)

  exact AF.quadEq_of_diagonalParts hABC_EBC hACD_ECF

end Euclid.Book1
