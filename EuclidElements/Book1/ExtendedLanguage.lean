import EuclidElements.Book1.ImplicitAxioms

/-!
# Extended synthetic language for later Book I
-/

namespace Euclid.Book1

open Euclid

class SegmentOrder (G : Geometry) where
  less : G.Point → G.Point → G.Point → G.Point → Prop

def SegmentLess (G : Geometry) [S : SegmentOrder G]
    (A B C D : G.Point) : Prop := S.less A B C D

class SegmentSumGeometry (G : Geometry) where
  sumGreater : G.Point → G.Point → G.Point → G.Point → G.Point → G.Point → Prop
  sumLess : G.Point → G.Point → G.Point → G.Point → G.Point → G.Point → G.Point → G.Point → Prop

def SegmentSumGreater (G : Geometry) [S : SegmentSumGeometry G]
    (A B C D E F : G.Point) : Prop := S.sumGreater A B C D E F

def SegmentSumLess (G : Geometry) [S : SegmentSumGeometry G]
    (A B C D E F H I : G.Point) : Prop := S.sumLess A B C D E F H I

class TriangleAreaGeometry (G : Geometry) where
  equalArea : G.Point → G.Point → G.Point → G.Point → G.Point → G.Point → Prop
  lessArea : G.Point → G.Point → G.Point → G.Point → G.Point → G.Point → Prop

def TriangleAreaEq (G : Geometry) [A : TriangleAreaGeometry G]
    (P Q R X Y Z : G.Point) : Prop := A.equalArea P Q R X Y Z

def TriangleAreaLess (G : Geometry) [A : TriangleAreaGeometry G]
    (P Q R X Y Z : G.Point) : Prop := A.lessArea P Q R X Y Z

class AngleSumGeometry (G : Geometry) where
  supplementary : Angle G.Point → Angle G.Point → Prop

def Supplementary (G : Geometry) [S : AngleSumGeometry G]
    (α β : Angle G.Point) : Prop := S.supplementary α β

class AngleInteriorGeometry (G : Geometry) where
  insideAngle : G.Point → G.Point → G.Point → G.Point → Prop

def InsideAngle (G : Geometry) [I : AngleInteriorGeometry G]
    (A B C P : G.Point) : Prop := I.insideAngle A B C P

class TriangleInteriorGeometry (G : Geometry) where
  insideTriangle : G.Point → G.Point → G.Point → G.Point → Prop

def InsideTriangle (G : Geometry) [I : TriangleInteriorGeometry G]
    (A B C P : G.Point) : Prop := I.insideTriangle A B C P

def SameRay (G : Geometry) (O A B : G.Point) : Prop :=
  O ≠ A ∧ O ≠ B ∧
    (A = B ∨ G.between O A B ∨ G.between O B A)

def IsMidpoint (G : Geometry) (M A B : G.Point) : Prop :=
  G.between A M B ∧ G.segmentCongruent A M M B

def IsAngleBisector (G : Geometry) (A B C D : G.Point) : Prop :=
  G.angleCongruent ⟨A, B, D⟩ ⟨D, B, C⟩

def Parallelogram (G : Geometry) (A B C D : G.Point) : Prop :=
  ∃ lAB lBC lCD lDA : G.Line,
    G.onLine A lAB ∧ G.onLine B lAB ∧
    G.onLine B lBC ∧ G.onLine C lBC ∧
    G.onLine C lCD ∧ G.onLine D lCD ∧
    G.onLine D lDA ∧ G.onLine A lDA ∧
    Parallel G lAB lCD ∧ Parallel G lBC lDA

end Euclid.Book1
