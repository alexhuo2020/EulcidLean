import EuclidElements.Book3.ChordOrderFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1
open Euclid.Book2

/-- Euclid III.15, first part: a diameter is greater than every non-diameter
    chord. -/
theorem proposition15_diameter
    (G : Geometry)
    [SegmentOrder G]
    [CO : ChordOrderFoundations G]
    {c : G.Circle} {A B C D : G.Point}
    (hdiam : IsDiameter G c A B)
    (hchord : Chord G c C D)
    (hnondiam : forall O : G.Point, G.isCenter c O -> ¬ G.Collinear C O D) :
    SegmentLess G C D A B :=
  CO.diameterGreaterThanChord hdiam hchord hnondiam

/-- Euclid III.15, comparison part: of two non-diameter chords, the one nearer
    the center is greater. -/
theorem proposition15_nearerGreater
    (G : Geometry)
    [SegmentOrder G]
    [AreaGeometry G]
    [CM : ChordMetricFoundations G]
    [CO : ChordOrderFoundations G]
    {c : G.Circle} {O A B C D M N : G.Point}
    (hAB : ChordFoot G c O A B M)
    (hCD : ChordFoot G c O C D N)
    (hnear : SegmentLess G O M O N) :
    SegmentLess G C D A B := by
  obtain ⟨hMmid, hMOA, hMright⟩ := CM.footGeometry hAB
  obtain ⟨hNmid, hNOC, hNright⟩ := CM.footGeometry hCD
  have hAon : G.onCircle A c := hAB.2.1.2.1
  have hCon : G.onCircle C c := hCD.2.1.2.1
  have hrad : G.segmentCongruent O A O C :=
    CM.sameCircleRadii hAB.1 hAon hCon
  have hhalf : SegmentLess G N C M A :=
    CO.equalHypotenuseComplementOrder hMOA hMright hNOC hNright hrad hnear
  exact CO.halfOrderToWholeOrder hMmid hNmid hhalf

end Euclid.Book3
