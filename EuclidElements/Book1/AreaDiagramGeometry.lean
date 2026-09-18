import EuclidElements.Book1.LaterAreaGeometry

namespace Euclid.Book1

open Euclid

/-- Extra diagram predicates needed only for Euclid's equal-figure block. -/
class AreaDiagramGeometry (G : Geometry) where
  complementsAboutDiagonal :
    G.Point → G.Point → G.Point → G.Point →
    G.Point → G.Point → G.Point → G.Point → Prop

def ComplementsAboutDiagonal (G : Geometry) [D : AreaDiagramGeometry G]
    (A B C Dp E F H I : G.Point) : Prop :=
  D.complementsAboutDiagonal A B C Dp E F H I

end Euclid.Book1
