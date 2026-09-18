import EuclidElements.Book3.SegmentReconstructionFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Euclid III.25: reconstruct the complete circle belonging to a given
    circular segment.  The reconstruction interface supplies only an
    equidistant candidate; III.9 identifies it as the center. -/
theorem proposition25
    (G : Geometry)
    [I : ImplicitAxioms G]
    [CB : CircleBasicAxioms G]
    [CU : CircumcenterUniquenessAxioms G]
    [SR : SegmentReconstructionAxioms G]
    {s : SegmentRef G}
    (hs : ValidSegment G s) :
    exists O : G.Point,
      G.isCenter s.circle O ∧
      G.onCircle s.a s.circle ∧
      G.onCircle s.b s.circle ∧
      G.onCircle s.arcPoint s.circle := by
  obtain ⟨M, O, hmid, htri, hOab, hOap⟩ := SR.reconstruct hs
  have hA : G.onCircle s.a s.circle := hs.2.2.2.1
  have hB : G.onCircle s.b s.circle := hs.2.2.2.2.1
  have hP : G.onCircle s.arcPoint s.circle := hs.2.2.2.2.2
  have hcenter : G.isCenter s.circle O :=
    proposition9 G htri hA hB hP hOab hOap
  exact ⟨O, hcenter, hA, hB, hP⟩

end Euclid.Book3
