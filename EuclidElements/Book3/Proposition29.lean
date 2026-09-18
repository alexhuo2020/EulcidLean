import EuclidElements.Book3.Proposition28

namespace Euclid.Book3

open Euclid

/-- Euclid III.29: in equal circles, chords cutting off equal selected arcs
    are equal. -/
theorem proposition29
    (G : Geometry)
    [ArcGeometry G]
    [AC : ArcCentralAngleFoundations G]
    [CC : ChordCentralAngleFoundations G]
    {c d : G.Circle} {O P A B C D : G.Point}
    {s t : ArcRef G}
    (heqCircles : EqualCircles G c d)
    (hO : G.isCenter c O) (hP : G.isCenter d P)
    (hAB : Chord G c A B) (hCD : Chord G d C D)
    (hs : ArcOn G s c A B) (ht : ArcOn G t d C D)
    (harc : ArcEq G s t) :
    G.segmentCongruent A B C D := by
  have hang : G.angleCongruent ⟨A, O, B⟩ ⟨C, P, D⟩ :=
    proposition27_center G heqCircles hO hP hs ht harc
  exact CC.equalCentralAngleGivesChord heqCircles hO hP hAB hCD hang

end Euclid.Book3
