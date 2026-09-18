import EuclidElements.Book3.Proposition24

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Operational semantics for equality of selected arcs in equal circles:
    corresponding selected arcs are equal exactly when their central angles
    are congruent.  This is a reusable meaning principle for `ArcEq`, not a
    numbered Book III proposition. -/
class ArcCentralAngleFoundations
    (G : Geometry)
    [ArcGeometry G] : Prop where
  eqIffCentral : forall
    {c d : G.Circle} {O P A B C D : G.Point}
    {s t : ArcRef G},
    EqualCircles G c d ->
    G.isCenter c O -> G.isCenter d P ->
    ArcOn G s c A B -> ArcOn G t d C D ->
    (ArcEq G s t ↔
      G.angleCongruent ⟨A, O, B⟩ ⟨C, P, D⟩)

/-- SSS/SAS consequences for chords in equal circles.  These are generic
    chord-metric lemmas and contain no arc equality conclusion. -/
class ChordCentralAngleFoundations (G : Geometry) : Prop where
  equalChordGivesCentralAngle : forall
    {c d : G.Circle} {O P A B C D : G.Point},
    EqualCircles G c d ->
    G.isCenter c O -> G.isCenter d P ->
    Chord G c A B -> Chord G d C D ->
    G.segmentCongruent A B C D ->
    G.angleCongruent ⟨A, O, B⟩ ⟨C, P, D⟩

  equalCentralAngleGivesChord : forall
    {c d : G.Circle} {O P A B C D : G.Point},
    EqualCircles G c d ->
    G.isCenter c O -> G.isCenter d P ->
    Chord G c A B -> Chord G d C D ->
    G.angleCongruent ⟨A, O, B⟩ ⟨C, P, D⟩ ->
    G.segmentCongruent A B C D

/-- Generic complement-of-equals rule for the two arcs cut off by a chord. -/
class ArcComplementGeometry (G : Geometry) where
  complementary : ArcRef G -> ArcRef G -> Prop

def ComplementaryArcs (G : Geometry) [C : ArcComplementGeometry G]
    (small large : ArcRef G) : Prop := C.complementary small large

class ArcComplementFoundations
    (G : Geometry)
    [ArcGeometry G]
    [ArcComplementGeometry G] : Prop where
  complementOfEquals : forall
    {s1 l1 s2 l2 : ArcRef G},
    ComplementaryArcs G s1 l1 ->
    ComplementaryArcs G s2 l2 ->
    ArcEq G s1 s2 -> ArcEq G l1 l2

/-- Geometry-only construction data for III.30. -/
class ArcBisectionConstructionAxioms
    (G : Geometry)
    [ArcGeometry G] : Prop where
  construct : forall {s : ArcRef G},
    ValidArc G s ->
    exists D : G.Point, exists left right : ArcRef G,
      D ≠ s.a ∧ D ≠ s.b ∧
      G.onCircle D s.circle ∧
      ArcOn G left s.circle s.a D ∧
      ArcOn G right s.circle D s.b ∧
      G.segmentCongruent s.a D D s.b

end Euclid.Book3
