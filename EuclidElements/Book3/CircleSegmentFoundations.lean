import EuclidElements.Book3.Proposition22

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Equality of circular segment regions is an equivalence relation. -/
class CircleSegmentEqualityFoundations
    (G : Geometry) [CircleSegmentGeometry G] : Prop where
  refl : forall s : SegmentRef G, SegmentRegionEq G s s
  symm : forall {s t : SegmentRef G},
    SegmentRegionEq G s t -> SegmentRegionEq G t s
  trans : forall {s t u : SegmentRef G},
    SegmentRegionEq G s t -> SegmentRegionEq G t u -> SegmentRegionEq G s u

/-- Nesting fact used in III.23.  If unequal circular segments share a chord
    and lie on the same side, one boundary arc point lies on the straight line
    from the common endpoint through the other; this is exactly the diagram
    Euclid invokes before applying I.16. -/
class SameBaseSegmentNestingAxioms
    (G : Geometry)
    [CircleSegmentGeometry G] : Prop where
  nested : forall {s t : SegmentRef G} {l : G.Line},
    ValidSegment G s -> ValidSegment G t ->
    t.a = s.a -> t.b = s.b ->
    G.onLine s.a l -> G.onLine s.b l ->
    G.sameSide s.arcPoint t.arcPoint l ->
    (¬ SegmentRegionEq G s t) ->
    (G.between s.a s.arcPoint t.arcPoint ∧
      IsTriangle G s.b t.arcPoint s.arcPoint) ∨
    (G.between s.a t.arcPoint s.arcPoint ∧
      IsTriangle G s.b s.arcPoint t.arcPoint)

/-- Common-Notion-4 style superposition for circular segments.  It moves the
    second segment onto the first congruent base while preserving its segment
    region and angle, and places the two copied arcs on the same side. -/
class CircleSegmentSuperpositionAxioms
    (G : Geometry)
    [CircleSegmentGeometry G] : Prop where
  superpose : forall {s t : SegmentRef G} {l : G.Line},
    ValidSegment G s -> ValidSegment G t ->
    G.segmentCongruent s.a s.b t.a t.b ->
    SimilarSegments G s t ->
    G.onLine s.a l -> G.onLine s.b l ->
    exists u : SegmentRef G,
      ValidSegment G u ∧
      u.a = s.a ∧ u.b = s.b ∧
      SimilarSegments G s u ∧
      SegmentRegionEq G t u ∧
      G.sameSide s.arcPoint u.arcPoint l

end Euclid.Book3
