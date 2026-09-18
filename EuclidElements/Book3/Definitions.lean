import EuclidElements.Book2

/-!
# Euclid Book III: circle language

Book III is kept synthetic.  Circles, lines, points, betweenness and congruence
remain primitive; no coordinates, real-valued radius, or numerical angle
measure is introduced.
-/

namespace Euclid.Book3

open Euclid
open Euclid.Book1
open Euclid.Book2

/-- A nondegenerate chord of a circle. -/
def Chord (G : Geometry) (c : G.Circle) (A B : G.Point) : Prop :=
  A ≠ B ∧ G.onCircle A c ∧ G.onCircle B c

/-- Book III Definition 1: equal circles have equal radii. -/
def EqualCircles (G : Geometry) (c d : G.Circle) : Prop :=
  ∀ O P A B : G.Point,
    G.isCenter c O → G.isCenter d P →
    G.onCircle A c → G.onCircle B d →
    G.segmentCongruent O A P B

/-- A line touches a circle at exactly one point.  This is the operational
    content of Book III Definition 2. -/
def TangentAt (G : Geometry) (c : G.Circle) (l : G.Line) (T : G.Point) : Prop :=
  G.onCircle T c ∧ G.onLine T l ∧
  ∀ X : G.Point, G.onCircle X c → G.onLine X l → X = T

/-- Two circles cut one another when they have two distinct common points. -/
def CirclesCutAt (G : Geometry) (c d : G.Circle) (A B : G.Point) : Prop :=
  A ≠ B ∧
  G.onCircle A c ∧ G.onCircle A d ∧
  G.onCircle B c ∧ G.onCircle B d

/-- Book III Definition 3: circles touch when they meet at one point and have
    no second common point. -/
def CirclesTouchAt (G : Geometry) (c d : G.Circle) (T : G.Point) : Prop :=
  G.onCircle T c ∧ G.onCircle T d ∧
  ∀ X : G.Point, G.onCircle X c → G.onCircle X d → X = T

/-- Synthetic inside/outside language for a circle. -/
class CircleOrderGeometry (G : Geometry) where
  inside : G.Point → G.Circle → Prop
  outside : G.Point → G.Circle → Prop

def InsideCircle (G : Geometry) [C : CircleOrderGeometry G]
    (P : G.Point) (c : G.Circle) : Prop := C.inside P c

def OutsideCircle (G : Geometry) [C : CircleOrderGeometry G]
    (P : G.Point) (c : G.Circle) : Prop := C.outside P c

/-- `M` is the foot of the perpendicular from the center `O` to chord `AB`. -/
def ChordFoot (G : Geometry) (c : G.Circle)
    (O A B M : G.Point) : Prop :=
  G.isCenter c O ∧ Chord G c A B ∧
  ∃ l m : G.Line,
    G.onLine A l ∧ G.onLine B l ∧ G.onLine M l ∧
    G.onLine O m ∧ G.onLine M m ∧ Perpendicular G l m

/-- Book III Definitions 4--5, expressed using perpendicular feet. -/
def ChordsEquidistantFromCenter (G : Geometry) (c : G.Circle)
    (O A B C D M N : G.Point) : Prop :=
  ChordFoot G c O A B M ∧ ChordFoot G c O C D N ∧
  G.segmentCongruent O M O N

def ChordFurtherFromCenter (G : Geometry) [SegmentOrder G] (c : G.Circle)
    (O A B C D M N : G.Point) : Prop :=
  ChordFoot G c O A B M ∧ ChordFoot G c O C D N ∧
  SegmentLess G O N O M

/-- A named arc: endpoints plus one point specifying which of the two arcs is
    intended.  Validity is kept separate so diagrams can carry the data first. -/
structure ArcRef (G : Geometry) where
  circle : G.Circle
  a : G.Point
  b : G.Point
  through : G.Point

def ValidArc (G : Geometry) (s : ArcRef G) : Prop :=
  s.a ≠ s.b ∧ s.through ≠ s.a ∧ s.through ≠ s.b ∧
  G.onCircle s.a s.circle ∧ G.onCircle s.b s.circle ∧
  G.onCircle s.through s.circle

/-- Abstract equality of circumferences/arcs.  Its laws are supplied by the
    circle-region foundation, not by numerical arc length. -/
class ArcGeometry (G : Geometry) where
  equalArc : ArcRef G → ArcRef G → Prop

def ArcEq (G : Geometry) [A : ArcGeometry G] (s t : ArcRef G) : Prop :=
  A.equalArc s t

/-- A circle segment is determined by its circle, chord, and a point on the
    chosen arc. -/
structure SegmentRef (G : Geometry) where
  circle : G.Circle
  a : G.Point
  b : G.Point
  arcPoint : G.Point

def ValidSegment (G : Geometry) (s : SegmentRef G) : Prop :=
  ValidArc G ⟨s.circle, s.a, s.b, s.arcPoint⟩

/-- Definition 8: the rectilinear angle in a segment. -/
def SegmentAngle (s : SegmentRef G) : Angle G.Point :=
  ⟨s.a, s.arcPoint, s.b⟩

/-- Definition 11: similar segments admit equal angles. -/
def SimilarSegments (G : Geometry) (s t : SegmentRef G) : Prop :=
  G.angleCongruent (SegmentAngle s) (SegmentAngle t)

/-- Synthetic equality of circular segments, needed for III.23--III.26. -/
class CircleSegmentGeometry (G : Geometry) where
  equalSegment : SegmentRef G → SegmentRef G → Prop

def SegmentRegionEq (G : Geometry) [S : CircleSegmentGeometry G]
    (s t : SegmentRef G) : Prop := S.equalSegment s t

/-- Definition 9: an angle stands on a selected circumference. -/
class AngleArcGeometry (G : Geometry) where
  standsOn : Angle G.Point → ArcRef G → Prop

def StandsOnArc (G : Geometry) [S : AngleArcGeometry G]
    (α : Angle G.Point) (arc : ArcRef G) : Prop := S.standsOn α arc

/-- Definition 10: sector data. -/
structure SectorRef (G : Geometry) where
  circle : G.Circle
  center : G.Point
  a : G.Point
  b : G.Point

/-- Definitions 6--7 include a non-rectilinear boundary angle.  We keep that
    as a separate token rather than pretending it is an ordinary `Angle`. -/
structure BoundaryAngleRef (G : Geometry) where
  segment : SegmentRef G

class BoundaryAngleOrderGeometry (G : Geometry) where
  greaterThanRect : BoundaryAngleRef G → Angle G.Point → Prop
  lessThanRect : BoundaryAngleRef G → Angle G.Point → Prop

def BoundaryAngleGreater (G : Geometry) [B : BoundaryAngleOrderGeometry G]
    (s : BoundaryAngleRef G) (α : Angle G.Point) : Prop :=
  B.greaterThanRect s α

def BoundaryAngleLess (G : Geometry) [B : BoundaryAngleOrderGeometry G]
    (s : BoundaryAngleRef G) (α : Angle G.Point) : Prop :=
  B.lessThanRect s α

end Euclid.Book3
