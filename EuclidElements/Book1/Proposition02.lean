import EuclidElements.Book1.Proposition01

/-!
# Euclid I.2

**Proposition.** To place at a given point (as an extremity) a straight line
 equal to a given straight line.

Given a point `A` and a nondegenerate segment `BC`, construct a point `L` such
that `AL ≅ BC`.

For the nontrivial case `A ≠ B`, the proof follows Euclid exactly:

1. Join `AB` (P1).
2. Construct equilateral triangle `DAB` (I.1).
3. Produce `DA` and `DB` (P2).
4. Draw the circle centered at `B` through `C` (P3), meeting the continuation
   of `DB` at `G`.
5. Draw the circle centered at `D` through `G` (P3), meeting the continuation
   of `DA` at `L`.
6. Since `DG ≅ DL`, `DA ≅ DB`, Common Notion 3 gives `AL ≅ BG`.
7. Since `BG ≅ BC`, Common Notion 1 gives `AL ≅ BC`.

The degenerate placement case `A = B` is discharged directly by taking `L=C`.
-/

namespace Euclid.Book1

open Euclid

/-- Full construction form of Euclid I.2, returning also a line through `A,L`. -/
theorem proposition2_construction
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    (A B C : G.Point)
    (hBC : B ≠ C) :
    ∃ L : G.Point, ∃ lAL : G.Line,
      G.onLine A lAL ∧ G.onLine L lAL ∧
      G.segmentCongruent A L B C := by
  by_cases hAB : A = B
  · subst A
    obtain ⟨lBC, hBon, hCon⟩ := P.postulate1 B C hBC
    exact ⟨C, lBC, hBon, hCon, I.segmentRefl B C⟩

  · -- Join AB and construct the equilateral triangle DAB (I.1).
    obtain ⟨_lAB, hAonAB, hBonAB⟩ := P.postulate1 A B hAB
    obtain ⟨D, _lAD, _lBD, _hAonAD, _hDonAD, _hBonBD, _hDonBD,
      _htriDAB, heqDAB⟩ := proposition1_construction G A B hAB

    have hDA_AD : G.segmentCongruent D A A D := I.segmentReverse D A
    have hAD_AB : G.segmentCongruent A D A B := I.segmentSymm heqDAB.1
    have hDA_AB : G.segmentCongruent D A A B := I.segmentTrans hDA_AD hAD_AB
    have hDA_BD : G.segmentCongruent D A B D := I.segmentTrans hDA_AB heqDAB.2.1
    have hBD_DB : G.segmentCongruent B D D B := I.segmentReverse B D
    have hDA_DB : G.segmentCongruent D A D B := I.segmentTrans hDA_BD hBD_DB

    -- D is distinct from A and B because DAB is a triangle.
    have hDneA : D ≠ A := _htriDAB.2.2.1
    have hDneB : D ≠ B := Ne.symm _htriDAB.2.1

    -- Produce DB beyond B (P2); Euclid denotes a point on this extension F.
    obtain ⟨F, hDBF⟩ := P.postulate2 D B hDneB

    -- Circle centered at B through C (P3), and choose G on DB produced.
    obtain ⟨cB, hcBcenter, hConcB, hcBradius⟩ := P.postulate3 B C hBC
    obtain ⟨Gpt, hDBG, hGoncB⟩ :=
      I2.circleBeyondCenter D B C cB hDneB hcBcenter hConcB

    have hBG_BC : G.segmentCongruent B Gpt B C :=
      (hcBradius Gpt).mp hGoncB

    -- Circle centered at D through G.
    have hDneG : D ≠ Gpt :=
      (I.betweenDistinct hDBG).2.2
    obtain ⟨cD, hcDcenter, hGoncD, hcDradius⟩ :=
      P.postulate3 D Gpt hDneG

    -- Because D-B-G and DA ≅ DB, the second circle meets DA produced at L.
    obtain ⟨L, hDAL, hLoncD⟩ :=
      I2.circleBeyondCongruentInnerPoint
        D B Gpt A cD hDBG hDA_DB hcDcenter hGoncD

    have hDL_DG : G.segmentCongruent D L D Gpt :=
      (hcDradius L).mp hLoncD

    -- CN3: subtract DA from DL and DB from DG.
    have hAL_BG : G.segmentCongruent A L B Gpt :=
      I2.segmentSubtraction hDAL hDBG hDA_DB hDL_DG

    -- CN1: AL ≅ BG and BG ≅ BC imply AL ≅ BC.
    have hAL_BC : G.segmentCongruent A L B C :=
      I.segmentTrans hAL_BG hBG_BC

    have hAneL : A ≠ L := (I.betweenDistinct hDAL).2.1
    obtain ⟨lAL, hAonAL, hLonAL⟩ := P.postulate1 A L hAneL
    exact ⟨L, lAL, hAonAL, hLonAL, hAL_BC⟩

/-- The usual existence statement of Euclid I.2. -/
theorem proposition2
    (G : Geometry)
    [Postulates G]
    [ImplicitAxioms G]
    [Proposition2ImplicitAxioms G]
    (A B C : G.Point)
    (hBC : B ≠ C) :
    ∃ L : G.Point, G.segmentCongruent A L B C := by
  obtain ⟨L, _l, _hA, _hL, hcong⟩ :=
    proposition2_construction G A B C hBC
  exact ⟨L, hcong⟩

end Euclid.Book1
