import EuclidElements.Book1.CommonNotions
import EuclidElements.Book1.ImplicitAxioms

/-!
# Euclid I.1

**Proposition.** On a given finite straight line, construct an equilateral
triangle.

The proof follows Euclid's construction:

1. Draw the circle centered at `A` through `B` (P3).
2. Draw the circle centered at `B` through `A` (P3).
3. Take a common point `C` of the circles (an implicit circle-intersection
   assumption in Euclid's proof).
4. Join `C` to `A` and `B` (P1).
5. Radius semantics give `AC ≅ AB` and `BC ≅ BA`.
6. Endpoint reversal and Common Notion 1 give the remaining side equalities.

No coordinates, real-number distances, angle measures, or Postulate 5 occur.
-/


namespace Euclid.Book1

open Euclid

/--
The full construction form of Proposition I.1.  Besides the new vertex `C`,
we explicitly return the two straight lines Euclid asks us to draw from `C`
to the endpoints of the given segment.
-/
theorem proposition1_construction
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    (A B : G.Point)
    (hAB : A ≠ B) :
    ∃ C : G.Point, ∃ lAC lBC : G.Line,
      G.onLine A lAC ∧ G.onLine C lAC ∧
      G.onLine B lBC ∧ G.onLine C lBC ∧
      IsTriangle G A B C ∧
      Equilateral G A B C := by
  -- Euclid I.1, construction step 1: circle with center A and radius AB.
  obtain ⟨cA, hcAcenter, hBoncA, hcAradius⟩ :=
    P.postulate3 A B hAB

  -- Construction step 2: circle with center B and radius BA.
  have hBA : B ≠ A := Ne.symm hAB
  obtain ⟨cB, hcBcenter, hAoncB, hcBradius⟩ :=
    P.postulate3 B A hBA

  -- Euclid silently assumes that the two circles meet off the center line.
  obtain ⟨C, hCneA, hCneB, hConcA, hConcB, hnoncol⟩ :=
    I.equilateralCircleIntersection
      A B hAB cA cB hcAcenter hBoncA hcBcenter hAoncB

  -- Construction step 3: join A to C and B to C (Postulate 1).
  have hAC : A ≠ C := Ne.symm hCneA
  have hBC : B ≠ C := Ne.symm hCneB
  obtain ⟨lAC, hAonAC, hConAC⟩ := P.postulate1 A C hAC
  obtain ⟨lBC, hBonBC, hConBC⟩ := P.postulate1 B C hBC

  -- Since C lies on the first circle, AC is congruent to AB.
  have hAC_AB : G.segmentCongruent A C A B :=
    (hcAradius C).mp hConcA

  -- Since C lies on the second circle, BC is congruent to BA.
  have hBC_BA : G.segmentCongruent B C B A :=
    (hcBradius C).mp hConcB

  -- Reverse AB/BA; then use CN1/transitivity exactly where Euclid says
  -- "things equal to the same thing are equal to one another."
  have hAB_BA : G.segmentCongruent A B B A := I.segmentReverse A B
  have hBA_BC : G.segmentCongruent B A B C := I.segmentSymm hBC_BA
  have hAB_BC : G.segmentCongruent A B B C :=
    I.segmentTrans hAB_BA hBA_BC

  have hAB_AC : G.segmentCongruent A B A C := I.segmentSymm hAC_AB
  have hAC_BC : G.segmentCongruent A C B C :=
    I.segmentTrans hAC_AB hAB_BC

  have htriangle : IsTriangle G A B C := by
    exact ⟨hAB, hBC, hCneA, hnoncol⟩

  have hequilateral : Equilateral G A B C := by
    exact ⟨hAB_AC, hAB_BC, hAC_BC⟩

  exact ⟨C, lAC, lBC,
    hAonAC, hConAC, hBonBC, hConBC,
    htriangle, hequilateral⟩

/--
The usual mathematical statement of Euclid I.1, obtained by forgetting the
witness lines returned by the construction theorem.
-/
theorem proposition1
    (G : Geometry)
    [Postulates G]
    [ImplicitAxioms G]
    (A B : G.Point)
    (hAB : A ≠ B) :
    ∃ C : G.Point,
      IsTriangle G A B C ∧ Equilateral G A B C := by
  obtain ⟨C, _lAC, _lBC, _hA, _hC1, _hB, _hC2, htri, heq⟩ :=
    proposition1_construction G A B hAB
  exact ⟨C, htri, heq⟩

end Euclid.Book1
