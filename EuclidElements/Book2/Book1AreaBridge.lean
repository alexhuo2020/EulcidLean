import EuclidElements.Book2.Proposition08
import EuclidElements.Book1.Proposition47
import EuclidElements.Book1.Proposition46

namespace Euclid.Book2

open Euclid
open Euclid.Book1

class Book1AreaMagnitudeBridge
    (G : Geometry)
    [AreaGeometry G]
    [LaterAreaGeometry G] : Prop where
  squareArea : ∀ {A B C D : G.Point},
    Square G A B C D → QuadArea G A B C D = Sq G A B
  sumArea : ∀ {A B C D E F H I P Q R S : G.Point},
    QuadAreaSumEq G A B C D E F H I P Q R S →
    Add G (QuadArea G A B C D) (QuadArea G E F H I) =
      QuadArea G P Q R S
  polygonArea : ∀ {p : Polygon G.Point} {A B C D : G.Point},
    PolygonQuadAreaEq G p A B C D →
    PolygonArea G p = QuadArea G A B C D
  rectangleArea : ∀ {A B C D : G.Point},
    Parallelogram G A B C D → RightAngle G ⟨D, A, B⟩ →
    QuadArea G A B C D = Rect G A B A D

theorem pythagoreanMagnitude
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
    [C46 : Proposition46ImplicitAxioms G]
    [LaterAreaGeometry G]
    [AF : AreaFoundations G]
    [QuadPartitionGeometry G]
    [AS : AreaSumFoundations G]
    [SF : SquareAreaFoundations G]
    [PD : PythagoreanDiagramAxioms G]
    [AreaGeometry G]
    [B : Book1AreaMagnitudeBridge G]
    {A C D : G.Point}
    (htri : IsTriangle G A C D)
    (hright : RightAngle G ⟨C, A, D⟩) :
    Add G (Sq G A C) (Sq G A D) = Sq G C D := by
  obtain ⟨X1, X2, hACsq⟩ := proposition46 G htri.1
  have hAD : A ≠ D := Ne.symm htri.2.2.1
  obtain ⟨Y1, Y2, hADsq⟩ := proposition46 G hAD
  have hCD : C ≠ D := htri.2.1
  obtain ⟨Z1, Z2, hCDsq⟩ := proposition46 G hCD
  have h47 := proposition47 G hright hACsq hADsq hCDsq
  have hsum := B.sumArea h47
  calc
    Add G (Sq G A C) (Sq G A D)
        = Add G (QuadArea G A C X1 X2) (QuadArea G A D Y1 Y2) := by
            rw [B.squareArea hACsq, B.squareArea hADsq]
    _ = QuadArea G C D Z1 Z2 := hsum
    _ = Sq G C D := B.squareArea hCDsq

end Euclid.Book2
