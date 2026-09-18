import EuclidElements.Book1.Definitions

/-!
# Euclid Book I: The Five Postulates

The statements are kept synthetic.  In particular Postulate 5 is Euclid's
interior-angle formulation, not Playfair's axiom.
-/


namespace Euclid.Book1

open Euclid

/-- The five explicitly stated postulates of Book I. -/
class Postulates (G : Geometry) : Prop where
  /-- P1: To draw a straight line from any point to any point. -/
  postulate1 : ∀ A B : G.Point,
    A ≠ B →
    ∃ l : G.Line, G.onLine A l ∧ G.onLine B l

  /-- P2: To produce a finite straight line continuously in a straight line. -/
  postulate2 : ∀ A B : G.Point,
    A ≠ B →
    ∃ C : G.Point, G.between A B C

  /--
  P3: To describe a circle with any center and distance.

  The biconditional records the intended radius semantics: the circle centered
  at `O` through `A` consists exactly of points `X` for which `OX ≅ OA`.
  -/
  postulate3 : ∀ O A : G.Point,
    O ≠ A →
    ∃ c : G.Circle,
      G.isCenter c O ∧
      G.onCircle A c ∧
      (∀ X : G.Point,
        G.onCircle X c ↔ G.segmentCongruent O X O A)

  /-- P4: All right angles are congruent to one another. -/
  postulate4 : ∀ α β : Angle G.Point,
    RightAngle G α → RightAngle G β → G.angleCongruent α β

  /--
  P5: If a transversal makes the two interior angles on one side less than two
  right angles, the two lines, when produced, meet on that side.
  -/
  postulate5 : ∀
    (l m t : G.Line)
    (P Q A B : G.Point),
    P ≠ Q →
    G.onLine P l → G.onLine P t →
    G.onLine Q m → G.onLine Q t →
    G.onLine A l → G.onLine B m →
    A ≠ P → B ≠ Q →
    G.sameSide A B t →
    G.sumLessThanTwoRight ⟨A, P, Q⟩ ⟨P, Q, B⟩ →
    ∃ X : G.Point,
      G.onLine X l ∧ G.onLine X m ∧ G.sameSide X A t

end Euclid.Book1
