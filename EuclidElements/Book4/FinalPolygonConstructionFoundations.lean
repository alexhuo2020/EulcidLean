import EuclidElements.Book4.Proposition14
import EuclidElements.Book4.Proposition02

namespace Euclid.Book4

open Euclid
open Euclid.Book1
open Euclid.Book3

class HexagonBook4ConstructionAxioms (G : Geometry) : Prop where
  frame : forall c : G.Circle,
    ∃ O A B C D E F : G.Point,
      G.isCenter c O ∧
      G.onCircle A c ∧ G.onCircle B c ∧ G.onCircle C c ∧
      G.onCircle D c ∧ G.onCircle E c ∧ G.onCircle F c ∧
      G.segmentCongruent A B B C ∧ G.segmentCongruent B C C D ∧
      G.segmentCongruent C D D E ∧ G.segmentCongruent D E E F ∧
      G.segmentCongruent E F F A ∧
      G.angleCongruent ⟨F, A, B⟩ ⟨A, B, C⟩ ∧
      G.angleCongruent ⟨A, B, C⟩ ⟨B, C, D⟩ ∧
      G.angleCongruent ⟨B, C, D⟩ ⟨C, D, E⟩ ∧
      G.angleCongruent ⟨C, D, E⟩ ⟨D, E, F⟩ ∧
      G.angleCongruent ⟨D, E, F⟩ ⟨E, F, A⟩ ∧
      G.segmentCongruent A B O A

class FifteenGonRegularityFoundations
    (G : Geometry) [FifteenGonGeometry G] : Prop where
  regularOfEqualArcSteps : forall {c : G.Circle} {p : FifteenGon G},
    EqualFifteenArcSteps G c p -> RegularFifteenGon G p

class EquilateralTriangleExistenceAxioms (G : Geometry) : Prop where
  existsTriangle : ∃ A B C : G.Point, IsTriangle G A B C ∧ Equilateral G A B C

class FifteenGonConstructionAxioms
    (G : Geometry) [SegmentOrder G] [FifteenGonGeometry G] : Prop where
  seed : forall {c : G.Circle}
    {A B C D E F P Q R S T : G.Point},
    TriangleInscribedInCircle G c A B C ->
    IsTriangle G D E F -> Equilateral G D E F ->
    EquiangularTriangles G A B C D E F ->
    PentagonInscribedInCircle G c P Q R S T ->
    ∃ U V : G.Point,
      (forall X Y : G.Point,
        IsDiameter G c X Y -> SegmentLe G U V X Y)

  complete : forall {c : G.Circle}
    {A B C P Q R S T U V X Y : G.Point},
    TriangleInscribedInCircle G c A B C ->
    PentagonInscribedInCircle G c P Q R S T ->
    Chord G c X Y -> G.segmentCongruent X Y U V ->
    ∃ p : FifteenGon G,
      EqualFifteenArcSteps G c p ∧
      (forall Z : G.Point, Z ∈ p.vertices -> G.onCircle Z c)

end Euclid.Book4
