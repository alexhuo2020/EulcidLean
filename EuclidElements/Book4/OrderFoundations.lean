import EuclidElements.Book4.Definitions

namespace Euclid.Book4

open Euclid
open Euclid.Book1

/-- Synthetic non-strict comparison of segment magnitudes. -/
def SegmentLe (G : Geometry) [SegmentOrder G]
    (A B C D : G.Point) : Prop :=
  G.segmentCongruent A B C D ∨ SegmentLess G A B C D

/-- The continuity fact missing in Euclid IV.1: a circle admits a chord of
    every magnitude strictly below a diameter.  It is stated as an
    intersection fact, not as IV.1 itself. -/
class ShortChordContinuityAxioms
    (G : Geometry) [SegmentOrder G] : Prop where
  shortChord : forall {c : G.Circle} {A B D E : G.Point},
    IsDiameter G c A B -> SegmentLess G D E A B ->
    ∃ X : G.Point,
      X ≠ A ∧ G.onCircle X c ∧ G.segmentCongruent A X D E

end Euclid.Book4
