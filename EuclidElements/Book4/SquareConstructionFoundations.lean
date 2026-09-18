import EuclidElements.Book4.Proposition05

namespace Euclid.Book4

open Euclid
open Euclid.Book1
open Euclid.Book3

/-- Geometry-only construction frames for IV.6--IV.9. -/
class SquareBook4ConstructionAxioms (G : Geometry) : Prop where
  inscribedFrame : forall c : G.Circle,
    ∃ A B C D : G.Point,
      IsQuadrilateral G A B C D ∧
      G.onCircle A c ∧ G.onCircle B c ∧ G.onCircle C c ∧ G.onCircle D c ∧
      EquilateralQuadrilateral G A B C D ∧
      RightAngledQuadrilateral G A B C D

  circumscribedFrame : forall c : G.Circle,
    ∃ A B C D : G.Point,
    ∃ lAB lBC lCD lDA : G.Line, ∃ T U V W : G.Point,
      IsQuadrilateral G A B C D ∧
      EquilateralQuadrilateral G A B C D ∧
      RightAngledQuadrilateral G A B C D ∧
      SideLine G A B lAB ∧ SideLine G B C lBC ∧
      SideLine G C D lCD ∧ SideLine G D A lDA ∧
      TangentAt G c lAB T ∧ TangentAt G c lBC U ∧
      TangentAt G c lCD V ∧ TangentAt G c lDA W

  incircleFrame : forall {A B C D : G.Point},
    Square G A B C D ->
    ∃ O T U V W : G.Point,
    ∃ lAB lBC lCD lDA rT rU rV rW : G.Line,
      SideLine G A B lAB ∧ SideLine G B C lBC ∧
      SideLine G C D lCD ∧ SideLine G D A lDA ∧
      G.onLine T lAB ∧ G.onLine U lBC ∧ G.onLine V lCD ∧ G.onLine W lDA ∧
      G.onLine O rT ∧ G.onLine T rT ∧ Perpendicular G rT lAB ∧
      G.onLine O rU ∧ G.onLine U rU ∧ Perpendicular G rU lBC ∧
      G.onLine O rV ∧ G.onLine V rV ∧ Perpendicular G rV lCD ∧
      G.onLine O rW ∧ G.onLine W rW ∧ Perpendicular G rW lDA ∧
      O ≠ T ∧
      G.segmentCongruent O T O U ∧
      G.segmentCongruent O T O V ∧
      G.segmentCongruent O T O W

  circumcenterFrame : forall {A B C D : G.Point},
    Square G A B C D ->
    ∃ O : G.Point,
      O ≠ A ∧
      G.segmentCongruent O A O B ∧
      G.segmentCongruent O A O C ∧
      G.segmentCongruent O A O D

end Euclid.Book4
