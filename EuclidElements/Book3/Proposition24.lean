import EuclidElements.Book3.Proposition23

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Euclid III.24: similar circular segments on equal straight lines are equal.
    The proof uses the same superposition method as Euclid. -/
theorem proposition24
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [P16 : Proposition16ImplicitAxioms G]
    [CS : CircleSegmentGeometry G]
    [E : CircleSegmentEqualityFoundations G]
    [N : SameBaseSegmentNestingAxioms G]
    [S : CircleSegmentSuperpositionAxioms G]
    {s t : SegmentRef G} {l : G.Line}
    (hs : ValidSegment G s)
    (ht : ValidSegment G t)
    (hbase : G.segmentCongruent s.a s.b t.a t.b)
    (hsim : SimilarSegments G s t)
    (hal : G.onLine s.a l)
    (hbl : G.onLine s.b l) :
    SegmentRegionEq G s t := by
  obtain ⟨u, hu, hua, hub, hsu, htu, hside⟩ :=
    S.superpose hs ht hbase hsim hal hbl
  have hsuEq : SegmentRegionEq G s u :=
    proposition23 G hs hu hua hub hal hbl hside hsu
  exact E.trans hsuEq (E.symm htu)

end Euclid.Book3
