import EuclidElements.Book3.Proposition03
import EuclidElements.Book2.Book1AreaBridge

namespace Euclid.Book3

open Euclid
open Euclid.Book1
open Euclid.Book2

/-- Pythagoras at the abstract Book-II area-magnitude level.  In the integrated
    project this is discharged by Book I.47 through `Book1AreaMagnitudeBridge`. -/
class PythagoreanMagnitudeGeometry
    (G : Geometry) [AreaGeometry G] : Prop where
  pythagorean : forall {A B C : G.Point},
    IsTriangle G A B C ->
    RightAngle G ⟨B, A, C⟩ ->
    Add G (Sq G A B) (Sq G A C) = Sq G B C

/-- Generic metric consequences used in III.14. -/
class ChordMetricFoundations
    (G : Geometry)
    [AreaGeometry G] : Prop where

  footGeometry : forall {c : G.Circle} {O A B M : G.Point},
    ChordFoot G c O A B M ->
    IsMidpoint G M A B ∧
    IsTriangle G M O A ∧
    RightAngle G ⟨O, M, A⟩

  sameCircleRadii : forall {c : G.Circle} {O A C : G.Point},
    G.isCenter c O -> G.onCircle A c -> G.onCircle C c ->
    G.segmentCongruent O A O C

  equalWholesGiveEqualHalves : forall {A B C D M N : G.Point},
    IsMidpoint G M A B -> IsMidpoint G N C D ->
    G.segmentCongruent A B C D ->
    G.segmentCongruent M A N C

  equalHalvesGiveEqualWholes : forall {A B C D M N : G.Point},
    IsMidpoint G M A B -> IsMidpoint G N C D ->
    G.segmentCongruent M A N C ->
    G.segmentCongruent A B C D

  squareEqOfCongruent : forall {A B C D : G.Point},
    G.segmentCongruent A B C D -> Sq G A B = Sq G C D

  congruentOfSquareEq : forall {A B C D : G.Point},
    Sq G A B = Sq G C D -> G.segmentCongruent A B C D

end Euclid.Book3
