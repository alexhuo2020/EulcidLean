import EuclidElements.Book1.Proposition34
import EuclidElements.Book1.AreaFoundations

namespace Euclid.Book1

open Euclid

/-- I.36: parallelograms on equal bases and between the same parallels are equal. -/
theorem proposition36
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
    {A B C D E F H Ipt : G.Point} {base top : G.Line}
    (h1 : Parallelogram G A B C D) (h2 : Parallelogram G E F H Ipt)
    (hAB_EF : G.segmentCongruent A B E F)
    (hAb : G.onLine A base) (hBb : G.onLine B base)
    (hEb : G.onLine E base) (hFb : G.onLine F base)
    (hCt : G.onLine C top) (hDt : G.onLine D top)
    (hHt : G.onLine H top) (hIt : G.onLine Ipt top)
    (hpar : Parallel G base top) :
    QuadAreaEq G A B C D E F H Ipt := by
  obtain ⟨hABC, _hDCA, _ha1, _ha2⟩ := D34.diagonalData h1
  obtain ⟨hEFH, _hIHE, _he1, _he2⟩ := D34.diagonalData h2

  have hCAB : IsTriangle G C A B := L.triangleCycle (L.triangleCycle hABC)
  have hHEF : IsTriangle G H E F := L.triangleCycle (L.triangleCycle hEFH)
  have hCAB_HEF : TriangleAreaEq G C A B H E F :=
    AF.equalBaseSameAltitude hCAB hHEF hAB_EF
      hAb hBb hEb hFb hCt hHt hpar

  have hABC_CAB : TriangleAreaEq G A B C C A B :=
    L.areaEq_trans (L.areaEq_cycle A B C) (L.areaEq_cycle B C A)
  have hEFH_HEF : TriangleAreaEq G E F H H E F :=
    L.areaEq_trans (L.areaEq_cycle E F H) (L.areaEq_cycle F H E)
  have hABC_EFH : TriangleAreaEq G A B C E F H :=
    L.areaEq_trans hABC_CAB
      (L.areaEq_trans hCAB_HEF (L.areaEq_symm hEFH_HEF))

  have h34a := proposition34 G h1
  have h34e := proposition34 G h2

  have hABC_ACD : TriangleAreaEq G A B C A C D := by
    have hCDA_ACD : TriangleAreaEq G C D A A C D :=
      L.areaEq_symm (L.areaEq_cycle A C D)
    exact L.areaEq_trans h34a.2.2.2 hCDA_ACD

  have hEFH_EHI : TriangleAreaEq G E F H E H Ipt := by
    have hHIE_EHI : TriangleAreaEq G H Ipt E E H Ipt :=
      L.areaEq_symm (L.areaEq_cycle E H Ipt)
    exact L.areaEq_trans h34e.2.2.2 hHIE_EHI

  have hACD_EHI : TriangleAreaEq G A C D E H Ipt :=
    L.areaEq_trans (L.areaEq_symm hABC_ACD)
      (L.areaEq_trans hABC_EFH hEFH_EHI)

  exact AF.quadEq_of_diagonalParts hABC_EFH hACD_EHI

end Euclid.Book1
