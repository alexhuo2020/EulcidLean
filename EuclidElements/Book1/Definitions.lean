import EuclidElements.Basic

/-!
# Euclid Book I: Definitions 1--23

The first seven definitions in Euclid are explanatory descriptions of the
primitive notions rather than definitions from previously defined objects.
We preserve their role in the comments below and represent their mathematical
content using the primitive sorts `Point` and `Line` from `Geometry`.
-/


namespace Euclid.Book1

open Euclid

/-!
## Definitions 1--7: primitive notions

**Definition 1.** A point is that which has no part.

**Definition 2.** A line is breadthless length.

**Definition 3.** The extremities of a line are points.

**Definition 4.** A straight line is a line which lies evenly with the points
on itself.

**Definition 5.** A surface is that which has length and breadth only.

**Definition 6.** The extremities of a surface are lines.

**Definition 7.** A plane surface is a surface which lies evenly with the
straight lines on itself.

Formalization policy: Book I takes place in one plane; `Geometry.Point` is the
primitive point sort and `Geometry.Line` is the primitive *straight-line* sort.
We therefore do not introduce meaningless predicates such as `hasNoPart` or
`breadthless`.  This makes the formalization operational while keeping Euclid's
historical descriptions explicit.
-/

/-- Definition 8/9: data for a nondegenerate rectilinear plane angle. -/
def ValidAngle (G : Geometry) (α : Angle G.Point) : Prop :=
  α.a ≠ α.vertex ∧ α.b ≠ α.vertex ∧
    ¬ G.Collinear α.a α.vertex α.b

/--
Definition 10: `∠AOB` is right when a line through `B,O` standing on the
straight line `A,O,C` makes equal adjacent angles `AOB` and `BOC`.
-/
def RightAngle (G : Geometry) (α : Angle G.Point) : Prop :=
  ∃ C : G.Point,
    G.between α.a α.vertex C ∧
    G.angleCongruent α ⟨α.b, α.vertex, C⟩

/-- Definition 10: two lines are perpendicular when they meet in a right angle. -/
def Perpendicular (G : Geometry) (l m : G.Line) : Prop :=
  ∃ O A B : G.Point,
    O ≠ A ∧ O ≠ B ∧
    G.onLine O l ∧ G.onLine A l ∧
    G.onLine O m ∧ G.onLine B m ∧
    RightAngle G ⟨A, O, B⟩

/-- Definition 11: an obtuse angle is greater than a right angle. -/
def ObtuseAngle (G : Geometry) (α : Angle G.Point) : Prop :=
  ∃ ρ : Angle G.Point, RightAngle G ρ ∧ G.angleLess ρ α

/-- Definition 12: an acute angle is less than a right angle. -/
def AcuteAngle (G : Geometry) (α : Angle G.Point) : Prop :=
  ∃ ρ : Angle G.Point, RightAngle G ρ ∧ G.angleLess α ρ

/-!
**Definition 13.** A boundary is that which is an extremity of anything.

This is a general mereological notion.  Book I only needs concrete boundaries
of the figures below, so no global `Boundary` primitive is imposed.
-/

/-- Definition 14: a polygonal figure is represented by its boundary vertices. -/
structure Polygon (Point : Type) where
  vertices : List Point

/-- Definition 15: a circle has a center from which all radii are congruent. -/
def IsCircle (G : Geometry) (c : G.Circle) : Prop :=
  ∃ O : G.Point,
    G.isCenter c O ∧
    ∀ X Y : G.Point,
      G.onCircle X c → G.onCircle Y c →
      G.segmentCongruent O X O Y

/-- Definition 16: `O` is the center of circle `c`. -/
def Center (G : Geometry) (c : G.Circle) (O : G.Point) : Prop :=
  G.isCenter c O

/-- Definition 17: a diameter has endpoints on the circle and passes through its center. -/
def IsDiameter (G : Geometry) (c : G.Circle) (A B : G.Point) : Prop :=
  G.onCircle A c ∧ G.onCircle B c ∧
    ∃ O : G.Point, G.isCenter c O ∧ G.between A O B

/-- Definition 18: data of a semicircle determined by a diameter. -/
structure Semicircle (G : Geometry) where
  circle : G.Circle
  a : G.Point
  b : G.Point
  diameter : IsDiameter G circle a b

/-- Definition 19: a trilateral figure has three boundary vertices. -/
def IsTrilateral {P : Type} (p : Polygon P) : Prop :=
  p.vertices.length = 3

/-- Definition 19: a quadrilateral figure has four boundary vertices. -/
def IsQuadrilateralPolygon {P : Type} (p : Polygon P) : Prop :=
  p.vertices.length = 4

/-- Definition 19: a multilateral figure has more than four boundary vertices. -/
def IsMultilateral {P : Type} (p : Polygon P) : Prop :=
  4 < p.vertices.length

/-- A genuine triangle: three distinct, noncollinear points. -/
def IsTriangle (G : Geometry) (A B C : G.Point) : Prop :=
  A ≠ B ∧ B ≠ C ∧ C ≠ A ∧ ¬ G.Collinear A B C

/-- Definition 20: an equilateral triangle has all three sides congruent. -/
def Equilateral (G : Geometry) (A B C : G.Point) : Prop :=
  G.segmentCongruent A B A C ∧
  G.segmentCongruent A B B C ∧
  G.segmentCongruent A C B C

/-- Definition 20: an isosceles triangle has two congruent sides. -/
def Isosceles (G : Geometry) (A B C : G.Point) : Prop :=
  G.segmentCongruent A B A C ∨
  G.segmentCongruent A B B C ∨
  G.segmentCongruent A C B C

/-- Definition 20: a scalene triangle has no congruent pair of sides. -/
def Scalene (G : Geometry) (A B C : G.Point) : Prop :=
  ¬ G.segmentCongruent A B A C ∧
  ¬ G.segmentCongruent A B B C ∧
  ¬ G.segmentCongruent A C B C

/-- Definition 21: a right-angled triangle contains a right angle. -/
def RightTriangle (G : Geometry) (A B C : G.Point) : Prop :=
  IsTriangle G A B C ∧
    (RightAngle G ⟨B, A, C⟩ ∨
     RightAngle G ⟨A, B, C⟩ ∨
     RightAngle G ⟨A, C, B⟩)

/-- Definition 21: an obtuse-angled triangle contains an obtuse angle. -/
def ObtuseTriangle (G : Geometry) (A B C : G.Point) : Prop :=
  IsTriangle G A B C ∧
    (ObtuseAngle G ⟨B, A, C⟩ ∨
     ObtuseAngle G ⟨A, B, C⟩ ∨
     ObtuseAngle G ⟨A, C, B⟩)

/-- Definition 21: an acute-angled triangle has all three angles acute. -/
def AcuteTriangle (G : Geometry) (A B C : G.Point) : Prop :=
  IsTriangle G A B C ∧
    AcuteAngle G ⟨B, A, C⟩ ∧
    AcuteAngle G ⟨A, B, C⟩ ∧
    AcuteAngle G ⟨A, C, B⟩

/-- A nondegenerate quadrilateral with pairwise distinct vertices. -/
def IsQuadrilateral (G : Geometry) (A B C D : G.Point) : Prop :=
  A ≠ B ∧ A ≠ C ∧ A ≠ D ∧
  B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
  ¬ G.Collinear A B C ∧
  ¬ G.Collinear B C D ∧
  ¬ G.Collinear C D A ∧
  ¬ G.Collinear D A B

/-- All four sides of `ABCD` are congruent. -/
def EquilateralQuadrilateral (G : Geometry) (A B C D : G.Point) : Prop :=
  G.segmentCongruent A B B C ∧
  G.segmentCongruent B C C D ∧
  G.segmentCongruent C D D A

/-- All four interior angles of `ABCD` are right. -/
def RightAngledQuadrilateral (G : Geometry) (A B C D : G.Point) : Prop :=
  RightAngle G ⟨D, A, B⟩ ∧
  RightAngle G ⟨A, B, C⟩ ∧
  RightAngle G ⟨B, C, D⟩ ∧
  RightAngle G ⟨C, D, A⟩

/-- Definition 22: a square is equilateral and right-angled. -/
def Square (G : Geometry) (A B C D : G.Point) : Prop :=
  IsQuadrilateral G A B C D ∧
  EquilateralQuadrilateral G A B C D ∧
  RightAngledQuadrilateral G A B C D

/-- Definition 22: an oblong is right-angled but not equilateral. -/
def Oblong (G : Geometry) (A B C D : G.Point) : Prop :=
  IsQuadrilateral G A B C D ∧
  RightAngledQuadrilateral G A B C D ∧
  ¬ EquilateralQuadrilateral G A B C D

/-- Definition 22: a rhombus is equilateral but not right-angled. -/
def Rhombus (G : Geometry) (A B C D : G.Point) : Prop :=
  IsQuadrilateral G A B C D ∧
  EquilateralQuadrilateral G A B C D ∧
  ¬ RightAngledQuadrilateral G A B C D

/-- Opposite sides and opposite angles of a quadrilateral are congruent. -/
def HasEqualOpposites (G : Geometry) (A B C D : G.Point) : Prop :=
  G.segmentCongruent A B C D ∧
  G.segmentCongruent B C D A ∧
  G.angleCongruent ⟨D, A, B⟩ ⟨B, C, D⟩ ∧
  G.angleCongruent ⟨A, B, C⟩ ⟨C, D, A⟩

/-- Definition 22: Euclid's rhomboid. -/
def Rhomboid (G : Geometry) (A B C D : G.Point) : Prop :=
  IsQuadrilateral G A B C D ∧
  HasEqualOpposites G A B C D ∧
  ¬ EquilateralQuadrilateral G A B C D ∧
  ¬ RightAngledQuadrilateral G A B C D

/--
Definition 22: Euclid calls all remaining quadrilaterals `trapezia`.
This is deliberately broader than the modern American definition of trapezoid.
-/
def Trapezium (G : Geometry) (A B C D : G.Point) : Prop :=
  IsQuadrilateral G A B C D ∧
  ¬ Square G A B C D ∧
  ¬ Oblong G A B C D ∧
  ¬ Rhombus G A B C D ∧
  ¬ Rhomboid G A B C D

/--
Definition 23: parallel straight lines are distinct coplanar lines which,
when produced indefinitely, do not meet.  Coplanarity is automatic because
`G` describes a single plane.
-/
def Parallel (G : Geometry) (l m : G.Line) : Prop :=
  l ≠ m ∧ ¬ G.LinesMeet l m

end Euclid.Book1
