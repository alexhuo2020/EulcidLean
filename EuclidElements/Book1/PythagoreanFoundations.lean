import EuclidElements.Book1.AreaFoundations

namespace Euclid.Book1

open Euclid

/-- Geometry of a quadrilateral partition: the first two quadrilaterals form
    the third without overlap.  This is incidence/region data, not an area
    equality. -/
class QuadPartitionGeometry (G : Geometry) where
  partition :
    G.Point → G.Point → G.Point → G.Point →
    G.Point → G.Point → G.Point → G.Point →
    G.Point → G.Point → G.Point → G.Point → Prop

def QuadPartition (G : Geometry) [Q : QuadPartitionGeometry G]
    (A B C D E F H I P Qp R S : G.Point) : Prop :=
  Q.partition A B C D E F H I P Qp R S

/-- Generic common-notion laws for doubling and addition of equal figures. -/
class AreaSumFoundations
    (G : Geometry)
    [TriangleAreaGeometry G]
    [LaterAreaGeometry G]
    [QuadPartitionGeometry G] : Prop where
  equalDoubleFigures : ∀
    {A B C D E F H I : G.Point},
    QuadDoubleTriangle G A B C D A B C →
    QuadDoubleTriangle G E F H I E F H →
    TriangleAreaEq G A B C E F H →
    QuadAreaEq G A B C D E F H I

  partitionSum : ∀
    {A B C D E F H I P Q R S : G.Point},
    QuadPartition G A B C D E F H I P Q R S →
    QuadAreaSumEq G A B C D E F H I P Q R S

  sumCongr : ∀
    {A B C D E F H I P Q R S
     A' B' C' D' E' F' H' I' : G.Point},
    QuadAreaEq G A B C D A' B' C' D' →
    QuadAreaEq G E F H I E' F' H' I' →
    QuadAreaSumEq G A' B' C' D' E' F' H' I' P Q R S →
    QuadAreaSumEq G A B C D E F H I P Q R S

  quadEqRefl : ∀ A B C D : G.Point, QuadAreaEq G A B C D A B C D

  sumCancelLeft : ∀
    {A B C D E F H I P Q R S U V W X : G.Point},
    QuadAreaSumEq G A B C D E F H I P Q R S →
    QuadAreaSumEq G A B C D E F H I U V W X →
    QuadAreaEq G P Q R S U V W X

/-- Generic facts about squares used by I.47-I.48. -/
class SquareAreaFoundations
    (G : Geometry)
    [TriangleAreaGeometry G]
    [LaterAreaGeometry G] : Prop where
  squareParallelogram : ∀ {A B C D : G.Point},
    Square G A B C D → Parallelogram G A B C D
  squareFirstTriangle : ∀ {A B C D : G.Point},
    Square G A B C D → IsTriangle G A B C
  congruentSidesGiveEqualSquares : ∀
    {A B C D E F H I : G.Point},
    Square G A B C D → Square G E F H I →
    G.segmentCongruent A B E F →
    QuadAreaEq G A B C D E F H I
  equalSquaresGiveCongruentSides : ∀
    {A B C D E F H I : G.Point},
    Square G A B C D → Square G E F H I →
    QuadAreaEq G A B C D E F H I →
    G.segmentCongruent A B E F

/-- Geometry-only dissection data used in Euclid I.47.  No area equality is a
    field: it supplies two parallelogram pieces, congruent triangle halves,
    and the fact that those pieces partition the hypotenuse square. -/
class PythagoreanDiagramAxioms
    (G : Geometry)
    [QuadPartitionGeometry G] : Prop where
  dissection : ∀
    {A B C P Q R S T U : G.Point},
    RightAngle G ⟨B, A, C⟩ →
    Square G A B P Q →
    Square G A C R S →
    Square G B C T U →
    ∃ X1 X2 X3 X4 Y1 Y2 Y3 Y4 : G.Point,
      Parallelogram G X1 X2 X3 X4 ∧
      Parallelogram G Y1 Y2 Y3 Y4 ∧
      IsTriangle G X1 X2 X3 ∧
      IsTriangle G Y1 Y2 Y3 ∧
      G.segmentCongruent A B X1 X2 ∧
      G.segmentCongruent A P X1 X3 ∧
      G.segmentCongruent B P X2 X3 ∧
      G.segmentCongruent A C Y1 Y2 ∧
      G.segmentCongruent A R Y1 Y3 ∧
      G.segmentCongruent C R Y2 Y3 ∧
      QuadPartition G X1 X2 X3 X4 Y1 Y2 Y3 Y4 B C T U

/-- Geometry-only comparison construction for Euclid I.48. -/
class PythagoreanConverseConstructionAxioms
    (G : Geometry) : Prop where
  comparisonRightTriangle : ∀
    {A B C : G.Point},
    IsTriangle G A B C →
    ∃ D : G.Point,
      IsTriangle G A D C ∧
      RightAngle G ⟨D, A, C⟩ ∧
      G.segmentCongruent A D A B

/-- Rightness is invariant under angle congruence. -/
class RightAngleCongruenceAxioms (G : Geometry) : Prop where
  rightAngleOfCongruent : ∀ {α β : Angle G.Point},
    G.angleCongruent α β → RightAngle G β → RightAngle G α

end Euclid.Book1
