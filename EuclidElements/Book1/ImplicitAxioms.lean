import EuclidElements.Book1.Postulates

/-!
# Implicit background assumptions used by Euclid

Lean makes visible assumptions which Euclid uses without listing among his five
postulates.  We keep them in a separate class so the distinction is auditable.

Only a small subset is required for Proposition I.1.  More order, continuity,
and superposition principles should be added here only when later propositions
force them.
-/


namespace Euclid.Book1

open Euclid

/-- Background laws tacitly used in Euclid's geometric reasoning. -/
class ImplicitAxioms (G : Geometry) : Prop where
  /-- Two distinct points determine at most one straight line. -/
  lineUnique : ∀ {A B : G.Point},
    A ≠ B →
    ∀ {l m : G.Line},
      G.onLine A l → G.onLine B l →
      G.onLine A m → G.onLine B m → l = m

  /-- Strict betweenness entails collinearity. -/
  betweenCollinear : ∀ {A B C : G.Point},
    G.between A B C → G.Collinear A B C

  /-- Strict betweenness entails distinct endpoints/inner point. -/
  betweenDistinct : ∀ {A B C : G.Point},
    G.between A B C → A ≠ B ∧ B ≠ C ∧ A ≠ C

  /-- Segment congruence is reflexive. -/
  segmentRefl : ∀ A B : G.Point,
    G.segmentCongruent A B A B

  /-- Segment congruence is symmetric. -/
  segmentSymm : ∀ {A B C D : G.Point},
    G.segmentCongruent A B C D → G.segmentCongruent C D A B

  /--
  Segment specialization of Common Notion 1: things congruent to the same
  segment are congruent to one another (transitivity form).
  -/
  segmentTrans : ∀ {A B C D E F : G.Point},
    G.segmentCongruent A B C D →
    G.segmentCongruent C D E F →
    G.segmentCongruent A B E F

  /-- Reversing the endpoints does not change a segment. -/
  segmentReverse : ∀ A B : G.Point,
    G.segmentCongruent A B B A

  /-- Angle congruence is reflexive. -/
  angleRefl : ∀ α : Angle G.Point, G.angleCongruent α α

  /-- Angle congruence is symmetric. -/
  angleSymm : ∀ {α β : Angle G.Point},
    G.angleCongruent α β → G.angleCongruent β α

  /-- Angle congruence is transitive. -/
  angleTrans : ∀ {α β γ : Angle G.Point},
    G.angleCongruent α β → G.angleCongruent β γ → G.angleCongruent α γ

  /--
  Circle-circle intersection principle implicitly used in Proposition I.1.

  If two distinct points are the centers of circles passing through one
  another, the circles have an intersection point off the center line.
  This is intentionally *not* folded into Postulate 3.
  -/
  equilateralCircleIntersection : ∀
    (A B : G.Point),
    A ≠ B →
    ∀ cA cB : G.Circle,
      G.isCenter cA A → G.onCircle B cA →
      G.isCenter cB B → G.onCircle A cB →
      ∃ C : G.Point,
        C ≠ A ∧ C ≠ B ∧
        G.onCircle C cA ∧ G.onCircle C cB ∧
        ¬ G.Collinear A B C

end Euclid.Book1

namespace Euclid.Book1

open Euclid

/--
Additional continuity/order principles first forced by Euclid I.2.

These are kept separate from `ImplicitAxioms` so the dependency growth of the
Elements can be audited proposition by proposition.
-/
class Proposition2ImplicitAxioms (G : Geometry) : Prop where
  /--
  A circle centered at `O` meets the continuation of any line through `O` on
  the side beyond `O`.  This is the line-circle intersection step used to
  choose `G` in Euclid I.2.
  -/
  circleBeyondCenter : ∀
    (X O R : G.Point) (c : G.Circle),
    X ≠ O →
    G.isCenter c O →
    G.onCircle R c →
    ∃ Y : G.Point,
      G.between X O Y ∧ G.onCircle Y c

  /--
  If `O-B-R` and `OX ≅ OB`, then the circle centered at `O` through `R`
  meets the ray `OX` beyond `X`.  This packages the order/continuity fact
  needed for the second circle-line intersection in I.2, without asserting
  the conclusion of I.2 itself.
  -/
  circleBeyondCongruentInnerPoint : ∀
    (O B R X : G.Point) (c : G.Circle),
    G.between O B R →
    G.segmentCongruent O X O B →
    G.isCenter c O →
    G.onCircle R c →
    ∃ Y : G.Point,
      G.between O X Y ∧ G.onCircle Y c

  /--
  Geometric specialization of Common Notion 3 (subtract equals from equals):
  from equal wholes `OL ≅ OG` and equal initial parts `OA ≅ OB`, with the
  stated betweenness, the remainders `AL` and `BG` are congruent.
  -/
  segmentSubtraction : ∀
    {O A L B Y : G.Point},
    G.between O A L →
    G.between O B Y →
    G.segmentCongruent O A O B →
    G.segmentCongruent O L O Y →
    G.segmentCongruent A L B Y

end Euclid.Book1
