import EuclidElements.Book3.Definitions

namespace Euclid.Book3

open Euclid
open Euclid.Book1

class CircleBasicAxioms (G : Geometry) : Prop where
  centerExists : ∀ c : G.Circle, ∃ O : G.Point, G.isCenter c O
  centerUnique : ∀ {c : G.Circle} {O P : G.Point},
    G.isCenter c O → G.isCenter c P → O = P
  centerNotOnCircle : ∀ {c : G.Circle} {O : G.Point},
    G.isCenter c O → ¬ G.onCircle O c
  radiiCongruent : ∀ {c : G.Circle} {O A B : G.Point},
    G.isCenter c O → G.onCircle A c → G.onCircle B c →
    G.segmentCongruent O A O B

class PerpendicularIntersectionAxioms (G : Geometry) : Prop where
  adjacentRightAngles : ∀ {l m : G.Line} {A M B O : G.Point},
    Perpendicular G l m →
    G.between A M B →
    G.onLine A l → G.onLine M l → G.onLine B l →
    G.onLine M m → G.onLine O m → M ≠ O →
    RightAngle G ⟨A, M, O⟩ ∧ RightAngle G ⟨B, M, O⟩

class CenterConstructionAxioms (G : Geometry) : Prop where
  construct : ∀ c : G.Circle,
    ∃ A B D C E F : G.Point,
      Chord G c A B ∧
      IsMidpoint G D A B ∧
      G.onCircle C c ∧ G.onCircle E c ∧
      G.between C F E ∧
      G.segmentCongruent C F F E ∧
      G.isCenter c F

class CircleExtensionalityAxioms (G : Geometry) : Prop where
  sameCenterCommonPoint : ∀ {c d : G.Circle} {O A : G.Point},
    G.isCenter c O → G.isCenter d O →
    G.onCircle A c → G.onCircle A d → c = d

class CircumcenterUniquenessAxioms (G : Geometry) : Prop where
  unique : ∀ {A B C O P : G.Point},
    IsTriangle G A B C →
    G.segmentCongruent O A O B → G.segmentCongruent O A O C →
    G.segmentCongruent P A P B → G.segmentCongruent P A P C →
    O = P

class CirclePositionAxioms (G : Geometry) [CircleOrderGeometry G] : Prop where
  insideNotBoundary : ∀ {c : G.Circle} {P : G.Point},
    InsideCircle G P c → ¬ G.onCircle P c
  outsideNotBoundary : ∀ {c : G.Circle} {P : G.Point},
    OutsideCircle G P c → ¬ G.onCircle P c

class CollinearOrderAxioms (G : Geometry) : Prop where
  oneBetween : ∀ {A B C : G.Point},
    G.Collinear A B C → A ≠ B → B ≠ C → C ≠ A →
    G.between A B C ∨ G.between B A C ∨ G.between A C B

end Euclid.Book3
