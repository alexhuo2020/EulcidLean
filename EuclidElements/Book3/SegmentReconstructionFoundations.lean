import EuclidElements.Book3.Proposition24
import EuclidElements.Book3.Proposition09

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Geometry-only reconstruction trace for III.25.  The construction supplies
    a candidate point equidistant from the three points of the given circular
    segment.  It deliberately does *not* assert that this candidate is the
    circle center; III.25 derives that conclusion from III.9. -/
class SegmentReconstructionAxioms (G : Geometry) : Prop where
  reconstruct : forall {s : SegmentRef G},
    ValidSegment G s ->
    exists M O : G.Point,
      IsMidpoint G M s.a s.b ∧
      IsTriangle G s.a s.b s.arcPoint ∧
      G.segmentCongruent O s.a O s.b ∧
      G.segmentCongruent O s.a O s.arcPoint

end Euclid.Book3
