import EuclidElements.Book1.ExtendedLanguage

/-!
# Generic background principles for later Book I

These are not numbered Euclid propositions. They isolate incidence, order,
continuity, superposition, and area principles that Euclid tacitly uses.
-/

namespace Euclid.Book1

open Euclid

class LaterImplicitAxioms
    (G : Geometry)
    [SegmentOrder G]
    [TriangleAreaGeometry G] : Prop where

  segmentCongruent_nonzero_left : ∀ {A B C D : G.Point},
    G.segmentCongruent A B C D → C ≠ D → A ≠ B

  segmentLess_congr_left : ∀ {A B C D E F : G.Point},
    G.segmentCongruent A B C D → SegmentLess G A B E F →
    SegmentLess G C D E F

  segmentLess_congr_right : ∀ {A B C D E F : G.Point},
    G.segmentCongruent C D E F → SegmentLess G A B C D →
    SegmentLess G A B E F

  segmentLess_irrefl : ∀ A B : G.Point, ¬ SegmentLess G A B A B

  segmentLess_trans : ∀ {A B C D E F : G.Point},
    SegmentLess G A B C D → SegmentLess G C D E F →
    SegmentLess G A B E F

  circleCutsSegment : ∀ {A B D : G.Point} {c : G.Circle},
    G.isCenter c A → G.onCircle D c → SegmentLess G A D A B →
    ∃ E : G.Point, G.between A E B ∧ G.onCircle E c

  betweenSymm : ∀ {A B C : G.Point},
    G.between A B C → G.between C B A

  triangleOnSide : ∀ {A B C D : G.Point},
    IsTriangle G A B C → G.between A D B → IsTriangle G B D C

  triangleSwap23 : ∀ {A B C : G.Point},
    IsTriangle G A B C → IsTriangle G A C B

  triangleCycle : ∀ {A B C : G.Point},
    IsTriangle G A B C → IsTriangle G B C A

  equalPointsOnAngleArms : ∀ {B A C : G.Point},
    ValidAngle G ⟨B, A, C⟩ →
    ∃ D E : G.Point,
      SameRay G A B D ∧ SameRay G A C E ∧
      G.segmentCongruent A D A E ∧ IsTriangle G A D E

  angleSameRayLeft : ∀ {O A A' X : G.Point},
    SameRay G O A A' →
    G.angleCongruent ⟨A, O, X⟩ ⟨A', O, X⟩

  angleSameRayRight : ∀ {O A A' X : G.Point},
    SameRay G O A A' →
    G.angleCongruent ⟨X, O, A⟩ ⟨X, O, A'⟩

  equilateralAwayFromPoint : ∀ {A D E : G.Point},
    IsTriangle G A D E →
    ∃ F : G.Point,
      Equilateral G D E F ∧ IsTriangle G A D F ∧ IsTriangle G A E F

  bisectorMeetsOppositeSide : ∀ {A B C F : G.Point},
    IsTriangle G A B C → F ≠ C →
    G.angleCongruent ⟨A, C, F⟩ ⟨F, C, B⟩ →
    ∃ D : G.Point, G.between A D B ∧
      G.angleCongruent ⟨A, C, D⟩ ⟨D, C, B⟩

  trianglesFromSidePoint : ∀ {A B C D : G.Point},
    IsTriangle G A B C → G.between A D B →
    IsTriangle G C A D ∧ IsTriangle G C B D

  symmetricPoint : ∀ {D C : G.Point},
    D ≠ C → ∃ E : G.Point,
      G.between D C E ∧ G.segmentCongruent C D C E

  betweenOnLine : ∀ {A B C : G.Point} {l : G.Line},
    G.between A B C → G.onLine A l → G.onLine C l → G.onLine B l

  equilateralBaseSubtriangles : ∀ {D C E F : G.Point},
    G.between D C E → Equilateral G D E F →
    IsTriangle G C D F ∧ IsTriangle G C E F

  secantCircleThroughLine : ∀ {A : G.Point} {l : G.Line},
    (¬ G.onLine A l) →
    ∃ c : G.Circle, ∃ E F : G.Point,
      E ≠ F ∧ G.isCenter c A ∧
      G.onCircle E c ∧ G.onCircle F c ∧
      G.onLine E l ∧ G.onLine F l ∧
      G.segmentCongruent A E A F

  offLineSecantTriangles : ∀ {A E M F : G.Point} {l : G.Line},
    ¬ G.onLine A l → G.onLine E l → G.onLine F l →
    G.between E M F → IsTriangle G M E A ∧ IsTriangle G M F A

  angleReverse : ∀ A B C : G.Point,
    G.angleCongruent ⟨A, B, C⟩ ⟨C, B, A⟩

  angleSameRay : ∀ {A D B C : G.Point},
    G.between A D B →
    G.angleCongruent ⟨D, B, C⟩ ⟨A, B, C⟩

  segmentTrichotomy : ∀ A B C D : G.Point,
    G.segmentCongruent A B C D ∨ SegmentLess G A B C D ∨
    SegmentLess G C D A B

  sas : ∀ {A B C D E F : G.Point},
    IsTriangle G A B C → IsTriangle G D E F →
    G.segmentCongruent A B D E → G.segmentCongruent A C D F →
    G.angleCongruent ⟨B, A, C⟩ ⟨E, D, F⟩ →
    G.segmentCongruent B C E F ∧
    G.angleCongruent ⟨A, B, C⟩ ⟨D, E, F⟩ ∧
    G.angleCongruent ⟨A, C, B⟩ ⟨D, F, E⟩ ∧
    TriangleAreaEq G A B C D E F

  sss : ∀ {A B C D E F : G.Point},
    IsTriangle G A B C → IsTriangle G D E F →
    G.segmentCongruent A B D E → G.segmentCongruent A C D F →
    G.segmentCongruent B C E F →
    G.angleCongruent ⟨B, A, C⟩ ⟨E, D, F⟩ ∧
    G.angleCongruent ⟨A, B, C⟩ ⟨D, E, F⟩ ∧
    G.angleCongruent ⟨A, C, B⟩ ⟨D, F, E⟩ ∧
    TriangleAreaEq G A B C D E F

  congruentTrianglesEqualArea : ∀ {A B C D E F : G.Point},
    IsTriangle G A B C → IsTriangle G D E F →
    G.segmentCongruent A B D E → G.segmentCongruent A C D F →
    G.segmentCongruent B C E F → TriangleAreaEq G A B C D E F

  areaEq_symm : ∀ {A B C D E F : G.Point},
    TriangleAreaEq G A B C D E F → TriangleAreaEq G D E F A B C

  areaEq_trans : ∀ {A B C D E F H I J : G.Point},
    TriangleAreaEq G A B C D E F → TriangleAreaEq G D E F H I J →
    TriangleAreaEq G A B C H I J

  areaEq_swap12 : ∀ A B C : G.Point, TriangleAreaEq G A B C B A C
  areaEq_cycle : ∀ A B C : G.Point, TriangleAreaEq G A B C B C A
  areaEq_swap : ∀ A B C : G.Point, TriangleAreaEq G A B C A C B

  properSubtriangle_on_side : ∀ {A B C D : G.Point},
    G.between A D B → ¬ G.Collinear A B C →
    TriangleAreaLess G D B C A B C

  properSubtriangleLess : ∀ {A B C D : G.Point},
    G.between B D C → ¬ G.Collinear A B C →
    TriangleAreaLess G A B D A B C

  equalArea_not_less : ∀ {A B C D E F : G.Point},
    TriangleAreaEq G A B C D E F → ¬ TriangleAreaLess G A B C D E F

  equalDistancesSameSide_unique : ∀
    {A B C D : G.Point} {l : G.Line},
    A ≠ B → G.onLine A l → G.onLine B l → G.sameSide C D l →
    G.segmentCongruent A C A D → G.segmentCongruent B C B D → C = D

end Euclid.Book1
