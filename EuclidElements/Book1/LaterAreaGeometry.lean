import EuclidElements.Book1.ExtendedLanguage

namespace Euclid.Book1

open Euclid

/--
Abstract area/equal-figure language for Euclid I.35-I.48.  These relations are
synthetic: no real-valued area function or coordinates are introduced.
-/
class LaterAreaGeometry (G : Geometry) where
  quadEq :
    G.Point → G.Point → G.Point → G.Point →
    G.Point → G.Point → G.Point → G.Point → Prop
  triQuadEq :
    G.Point → G.Point → G.Point →
    G.Point → G.Point → G.Point → G.Point → Prop
  quadDoubleTri :
    G.Point → G.Point → G.Point → G.Point →
    G.Point → G.Point → G.Point → Prop
  quadSumEq :
    G.Point → G.Point → G.Point → G.Point →
    G.Point → G.Point → G.Point → G.Point →
    G.Point → G.Point → G.Point → G.Point → Prop
  polygonQuadEq : Polygon G.Point →
    G.Point → G.Point → G.Point → G.Point → Prop

def QuadAreaEq (G : Geometry) [A : LaterAreaGeometry G]
    (P Q R S U V W X : G.Point) : Prop :=
  A.quadEq P Q R S U V W X

def TriangleQuadAreaEq (G : Geometry) [A : LaterAreaGeometry G]
    (P Q R U V W X : G.Point) : Prop :=
  A.triQuadEq P Q R U V W X

def QuadDoubleTriangle (G : Geometry) [A : LaterAreaGeometry G]
    (P Q R S U V W : G.Point) : Prop :=
  A.quadDoubleTri P Q R S U V W

def QuadAreaSumEq (G : Geometry) [A : LaterAreaGeometry G]
    (A1 A2 A3 A4 B1 B2 B3 B4 C1 C2 C3 C4 : G.Point) : Prop :=
  A.quadSumEq A1 A2 A3 A4 B1 B2 B3 B4 C1 C2 C3 C4

def PolygonQuadAreaEq (G : Geometry) [A : LaterAreaGeometry G]
    (p : Polygon G.Point) (Q R S T : G.Point) : Prop :=
  A.polygonQuadEq p Q R S T

end Euclid.Book1
