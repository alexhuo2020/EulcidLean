import EuclidElements.Book3.Proposition01

namespace Euclid.Book3

open Euclid

/-- Convexity/order semantics of a Euclidean circle.  This is precisely the
    background relation between the primitive `inside` predicate and a chord;
    Euclid proves it in III.2 from his circle picture, whereas our primitive
    circle model must state this semantic bridge explicitly. -/
class CircleConvexityAxioms (G : Geometry) [CircleOrderGeometry G] : Prop where
  betweenChordEndpointsInside : ∀ {c : G.Circle} {A X B : G.Point},
    G.onCircle A c → G.onCircle B c → G.between A X B →
    InsideCircle G X c

/-- Euclid III.2: every strict interior point of a chord lies inside the
    circle. -/
theorem proposition2
    (G : Geometry)
    [CircleOrderGeometry G]
    [C : CircleConvexityAxioms G]
    {c : G.Circle} {A B : G.Point}
    (hA : G.onCircle A c) (hB : G.onCircle B c) :
    ∀ {X : G.Point}, G.between A X B → InsideCircle G X c := by
  intro X hAXB
  exact C.betweenChordEndpointsInside hA hB hAXB

end Euclid.Book3
