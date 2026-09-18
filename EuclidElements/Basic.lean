/-!
# EuclidElements.Basic

A deliberately synthetic primitive language for Book I of Euclid's *Elements*.
No coordinates, real numbers, distances, angle measures, affine spaces, or
Mathlib Euclidean geometry are assumed.
-/

namespace Euclid

/-- A finite straight-line segment, represented by its two endpoints. -/
structure Segment (Point : Type) where
  a : Point
  b : Point

/-- A rectilinear angle `∠ABC`, with `b` the vertex. -/
structure Angle (Point : Type) where
  a : Point
  vertex : Point
  b : Point

/--
The primitive language of a synthetic plane.

`Point`, `Line`, and `Circle` are primitive sorts.  The remaining fields are
primitive relations needed to state Euclid's definitions and postulates.
They are intentionally not interpreted using coordinates.
-/
structure Geometry where
  Point : Type
  Line : Type
  Circle : Type
  onLine : Point → Line → Prop
  onCircle : Point → Circle → Prop
  between : Point → Point → Point → Prop
  isCenter : Circle → Point → Prop
  segmentCongruent : Point → Point → Point → Point → Prop
  angleCongruent : Angle Point → Angle Point → Prop
  angleLess : Angle Point → Angle Point → Prop
  sameSide : Point → Point → Line → Prop
  sumLessThanTwoRight : Angle Point → Angle Point → Prop

namespace Geometry

/-- `A,B,C` are collinear when they lie on a common straight line. -/
def Collinear (G : Geometry) (A B C : G.Point) : Prop :=
  ∃ l : G.Line, G.onLine A l ∧ G.onLine B l ∧ G.onLine C l

/-- Two lines meet if they have a common point. -/
def LinesMeet (G : Geometry) (l m : G.Line) : Prop :=
  ∃ P : G.Point, G.onLine P l ∧ G.onLine P m

/-- Segment congruence written as a relation on `Segment` objects. -/
def SegmentEq (G : Geometry) (s t : Segment G.Point) : Prop :=
  G.segmentCongruent s.a s.b t.a t.b

end Geometry

end Euclid
