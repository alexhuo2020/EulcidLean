import EuclidElements.Book4.ConstructionFoundations

namespace Euclid.Book4

open Euclid
open Euclid.Book1
open Euclid.Book3

/-- Euclid IV.1: fit into a circle a chord congruent to a given segment not
    greater than a diameter.  The strict case uses the explicit continuity
    principle isolated in `ShortChordContinuityAxioms`. -/
theorem proposition1
    (G : Geometry)
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [D : DiameterExistenceAxioms G]
    [S : ShortChordContinuityAxioms G]
    {c : G.Circle} {P Q : G.Point}
    (hbound : forall A B : G.Point,
      IsDiameter G c A B -> SegmentLe G P Q A B) :
    ∃ A B : G.Point,
      Chord G c A B ∧ G.segmentCongruent A B P Q := by
  obtain ⟨A, B, hdiam⟩ := D.diameter c
  have hle := hbound A B hdiam
  rcases hle with heq | hlt
  · have hAB : A ≠ B := by
      rcases hdiam.2.2 with ⟨O, hO, hbet⟩
      exact (I.betweenDistinct hbet).2.2
    exact ⟨A, B, ⟨hAB, hdiam.1, hdiam.2.1⟩, I.segmentSymm heq⟩
  · obtain ⟨X, hXneA, hXc, hAX⟩ := S.shortChord hdiam hlt
    exact ⟨A, X, ⟨Ne.symm hXneA, hdiam.1, hXc⟩, hAX⟩

end Euclid.Book4
