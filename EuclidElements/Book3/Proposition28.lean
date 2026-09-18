import EuclidElements.Book3.Proposition27

namespace Euclid.Book3

open Euclid

/-- Euclid III.28: equal chords in equal circles cut off equal selected arcs;
    if the complementary arcs are supplied, the complementary (greater) arcs
    are equal as well. -/
theorem proposition28
    (G : Geometry)
    [ArcGeometry G]
    [ArcComplementGeometry G]
    [AC : ArcCentralAngleFoundations G]
    [CC : ChordCentralAngleFoundations G]
    [COMP : ArcComplementFoundations G]
    {c d : G.Circle} {O P A B C D : G.Point}
    {small1 large1 small2 large2 : ArcRef G}
    (heqCircles : EqualCircles G c d)
    (hO : G.isCenter c O) (hP : G.isCenter d P)
    (hAB : Chord G c A B) (hCD : Chord G d C D)
    (hs1 : ArcOn G small1 c A B) (hs2 : ArcOn G small2 d C D)
    (hcomp1 : ComplementaryArcs G small1 large1)
    (hcomp2 : ComplementaryArcs G small2 large2)
    (hchord : G.segmentCongruent A B C D) :
    ArcEq G small1 small2 ∧ ArcEq G large1 large2 := by
  have hang : G.angleCongruent ⟨A, O, B⟩ ⟨C, P, D⟩ :=
    CC.equalChordGivesCentralAngle heqCircles hO hP hAB hCD hchord
  have hsmall : ArcEq G small1 small2 :=
    proposition26_center G heqCircles hO hP hs1 hs2 hang
  exact ⟨hsmall, COMP.complementOfEquals hcomp1 hcomp2 hsmall⟩

end Euclid.Book3
