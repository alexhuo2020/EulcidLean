import EuclidElements.Book1.Proposition02
import EuclidElements.Book1.LaterImplicitAxioms

/-!
# Euclid I.3

**Proposition.** Given two unequal straight lines, to cut off from the greater
a straight line equal to the less.
-/

namespace Euclid.Book1

open Euclid

theorem proposition3
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    [S : SegmentOrder G]
    [A : TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    (A B C D : G.Point)
    (hCD : C ≠ D)
    (hless : SegmentLess G C D A B) :
    ∃ E : G.Point,
      G.between A E B ∧
      G.segmentCongruent A E C D := by
  obtain ⟨X, hAX_CD⟩ := proposition2 G A C D hCD
  have hAX : A ≠ X := L.segmentCongruent_nonzero_left hAX_CD hCD
  obtain ⟨c, hcCenter, hXon, hcRadius⟩ := P.postulate3 A X hAX
  have hCD_AX : G.segmentCongruent C D A X := I.segmentSymm hAX_CD
  have hAXless : SegmentLess G A X A B :=
    L.segmentLess_congr_left hCD_AX hless
  obtain ⟨E, hAEB, hEon⟩ := L.circleCutsSegment hcCenter hXon hAXless
  have hAE_AX : G.segmentCongruent A E A X :=
    (hcRadius E).mp hEon
  have hAE_CD : G.segmentCongruent A E C D :=
    I.segmentTrans hAE_AX hAX_CD
  exact ⟨E, hAEB, hAE_CD⟩

end Euclid.Book1
