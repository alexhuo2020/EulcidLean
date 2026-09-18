import EuclidElements.Book3.Proposition14

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Generic metric order facts used by III.15.  They are not circle-specific:
    the key comparison is the right-triangle fact that, for equal hypotenuses,
    the smaller one leg is, the larger the complementary leg is. -/
class ChordOrderFoundations
    (G : Geometry)
    [SegmentOrder G] : Prop where

  equalHypotenuseComplementOrder : forall
    {O M A N C : G.Point},
    IsTriangle G M O A -> RightAngle G ⟨O, M, A⟩ ->
    IsTriangle G N O C -> RightAngle G ⟨O, N, C⟩ ->
    G.segmentCongruent O A O C ->
    SegmentLess G O M O N ->
    SegmentLess G N C M A

  halfOrderToWholeOrder : forall {A B C D M N : G.Point},
    IsMidpoint G M A B -> IsMidpoint G N C D ->
    SegmentLess G N C M A ->
    SegmentLess G C D A B

  diameterGreaterThanChord : forall
    {c : G.Circle} {A B C D : G.Point},
    IsDiameter G c A B -> Chord G c C D ->
    (forall O : G.Point, G.isCenter c O -> ¬ G.Collinear C O D) ->
    SegmentLess G C D A B

end Euclid.Book3
