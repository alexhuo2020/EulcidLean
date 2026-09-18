import EuclidElements.Book2.Book1AreaBridge

namespace Euclid.Book2

open Euclid
open Euclid.Book1

/-- Geometry-only auxiliary diagrams for Euclid II.9 and II.10.  Each triangle
is oriented with its right-angle vertex first, matching `pythagoreanMagnitude`.
No area identity is a field. -/
class Proposition9_10DiagramAxioms (G : Geometry) : Prop where
  unequalCut : ∀ {A C D B : G.Point},
    IsMidpoint G C A B → G.between A C D → G.between C D B →
    ∃ E F H : G.Point,
      IsTriangle G D A F ∧ RightAngle G ⟨A, D, F⟩ ∧
      G.segmentCongruent D F D B ∧
      IsTriangle G E A F ∧ RightAngle G ⟨A, E, F⟩ ∧
      IsTriangle G C A E ∧ RightAngle G ⟨A, C, E⟩ ∧
      G.segmentCongruent C E A C ∧
      IsTriangle G H E F ∧ RightAngle G ⟨E, H, F⟩ ∧
      G.segmentCongruent H E C D ∧
      G.segmentCongruent H F C D

  produced : ∀ {A C B D : G.Point},
    IsMidpoint G C A B → G.between A B D → G.between C B D →
    ∃ E F H : G.Point,
      IsTriangle G D A F ∧ RightAngle G ⟨A, D, F⟩ ∧
      G.segmentCongruent D F D B ∧
      IsTriangle G E A F ∧ RightAngle G ⟨A, E, F⟩ ∧
      IsTriangle G C A E ∧ RightAngle G ⟨A, C, E⟩ ∧
      G.segmentCongruent C E A C ∧
      IsTriangle G H E F ∧ RightAngle G ⟨E, H, F⟩ ∧
      G.segmentCongruent H E C D ∧
      G.segmentCongruent H F C D

end Euclid.Book2
