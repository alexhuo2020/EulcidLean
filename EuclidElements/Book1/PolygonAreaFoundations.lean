import EuclidElements.Book1.PythagoreanFoundations

namespace Euclid.Book1

open Euclid

/-- One nondegenerate triangular piece in a triangulation of a rectilinear
    figure. -/
structure TrianglePiece (G : Geometry) where
  a : G.Point
  b : G.Point
  c : G.Point
  valid : IsTriangle G a b c

/-- Recursive statement that a parallelogram has the same area as a finite
    nonempty list of triangular pieces.  This is built from the primitive
    triangle--quadrilateral equality and quadrilateral area addition. -/
inductive TriangleListQuadAreaEq
    (G : Geometry) [LaterAreaGeometry G] :
    List (TrianglePiece G) → G.Point → G.Point → G.Point → G.Point → Prop
  | single {t : TrianglePiece G} {A B C D : G.Point} :
      TriangleQuadAreaEq G t.a t.b t.c A B C D →
      TriangleListQuadAreaEq G [t] A B C D
  | cons {t : TrianglePiece G} {ts : List (TrianglePiece G)}
      {A B C D E F H I P Q R S : G.Point} :
      TriangleQuadAreaEq G t.a t.b t.c A B C D →
      TriangleListQuadAreaEq G ts E F H I →
      QuadAreaSumEq G A B C D E F H I P Q R S →
      TriangleListQuadAreaEq G (t :: ts) P Q R S

/-- Primitive triangulation relation connecting a boundary polygon to its
    certified triangle pieces. -/
class PolygonTriangulationGeometry (G : Geometry) where
  triangulates : Polygon G.Point → List (TrianglePiece G) → Prop

def PolygonTriangulation (G : Geometry) [T : PolygonTriangulationGeometry G]
    (p : Polygon G.Point) (pieces : List (TrianglePiece G)) : Prop :=
  T.triangulates p pieces

/-- A rectilinear figure for I.45 is a polygon equipped with a finite,
    nonempty triangulation. -/
def RectilinearFigure (G : Geometry) [PolygonTriangulationGeometry G]
    (p : Polygon G.Point) : Prop :=
  ∃ pieces : List (TrianglePiece G),
    pieces ≠ [] ∧ PolygonTriangulation G p pieces

/-- Semantic compatibility of polygon area with a certified triangulation. -/
class PolygonTriangulationFoundations
    (G : Geometry)
    [LaterAreaGeometry G]
    [PolygonTriangulationGeometry G] : Prop where
  transfer : ∀ {p : Polygon G.Point} {pieces : List (TrianglePiece G)}
    {A B C D : G.Point},
    PolygonTriangulation G p pieces →
    TriangleListQuadAreaEq G pieces A B C D →
    PolygonQuadAreaEq G p A B C D

/-- Generic composition construction used in the induction for I.45: two
    parallelograms already equal to two pieces can be combined into one
    parallelogram in the same prescribed angle. -/
class ParallelogramCompositionAxioms
    (G : Geometry)
    [LaterAreaGeometry G] : Prop where
  combineSameAngle : ∀
    {A B C D E F H I : G.Point} {α : Angle G.Point},
    Parallelogram G A B C D →
    Parallelogram G E F H I →
    G.angleCongruent ⟨D, A, B⟩ α →
    G.angleCongruent ⟨I, E, F⟩ α →
    ∃ P Q R S : G.Point,
      Parallelogram G P Q R S ∧
      G.angleCongruent ⟨S, P, Q⟩ α ∧
      QuadAreaSumEq G A B C D E F H I P Q R S

end Euclid.Book1
