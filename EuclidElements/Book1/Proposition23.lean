import EuclidElements.Book1.Proposition08
import EuclidElements.Book1.Proposition20
import EuclidElements.Book1.Proposition22

/-!
# Euclid I.23 -- construct on a given straight line an angle equal to a given angle
-/

namespace Euclid.Book1

open Euclid

/--
Construction-strength form of I.23.  In addition to the copied angle, this
retains the fact (already present in Euclid's construction) that the new arm is
not collinear with the given target ray.
-/
theorem proposition23_construction
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G]
    [SegmentSumGeometry G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [Proposition16ImplicitAxioms G]
    [SA : SegmentArithmeticImplicitAxioms G]
    [TriangleConstructionImplicitAxioms G]
    {A B D C E : G.Point}
    (hAB : A ≠ B)
    (hang : ValidAngle G ⟨D, C, E⟩) :
    ∃ F : G.Point,
      F ≠ A ∧
      ¬ G.Collinear F A B ∧
      G.angleCongruent ⟨F, A, B⟩ ⟨D, C, E⟩ := by
  have hDC : D ≠ C := hang.1
  have hEC : E ≠ C := hang.2.1
  have hCE : C ≠ E := Ne.symm hEC
  have hDE : D ≠ E := by
    intro h
    subst E
    obtain ⟨l, hDl, hCl⟩ := P.postulate1 D C hDC
    exact hang.2.2 ⟨l, hDl, hCl, hDl⟩
  have hED : E ≠ D := Ne.symm hDE
  have hDCE : IsTriangle G D C E := ⟨hDC, hCE, hED, hang.2.2⟩

  have hCDE : IsTriangle G C D E :=
    L.triangleCycle (L.triangleCycle (L.triangleSwap23 hDCE))
  have hs1raw : SegmentSumGreater G D C C E D E := proposition20 G hCDE
  have hs1 : SegmentSumGreater G C D C E D E :=
    SA.sumGreater_reverse_first hs1raw

  have hs2raw : SegmentSumGreater G C D D E C E := proposition20 G hDCE
  have hs2 : SegmentSumGreater G C D D E C E := hs2raw

  have hECD : IsTriangle G E C D := L.triangleCycle (L.triangleSwap23 hDCE)
  have hs3raw : SegmentSumGreater G C E E D C D := proposition20 G hECD
  have hs3 : SegmentSumGreater G C E D E C D :=
    SA.sumGreater_reverse_second hs3raw

  obtain ⟨F, S, hRay, hAF_CD, hAS_CE, hFS_DE, hASF⟩ :=
    proposition22_onRay G hAB (Ne.symm hDC) hCE hDE hs1 hs2 hs3

  have hFAS : IsTriangle G F A S := L.triangleCycle (L.triangleCycle hASF)

  have hDC_FA : G.segmentCongruent D C F A := by
    have hCD_AF : G.segmentCongruent C D A F := I.segmentSymm hAF_CD
    have hDC_CD : G.segmentCongruent D C C D := I.segmentReverse D C
    have hAF_FA : G.segmentCongruent A F F A := I.segmentReverse A F
    exact I.segmentTrans (I.segmentTrans hDC_CD hCD_AF) hAF_FA
  have hDE_FS : G.segmentCongruent D E F S := I.segmentSymm hFS_DE
  have hCE_AS : G.segmentCongruent C E A S := I.segmentSymm hAS_CE

  have hsss := proposition8 G hDCE hFAS hDC_FA hDE_FS hCE_AS
  have hDCE_FAS : G.angleCongruent ⟨D, C, E⟩ ⟨F, A, S⟩ := hsss.2.1
  have hFAS_DCE : G.angleCongruent ⟨F, A, S⟩ ⟨D, C, E⟩ :=
    I.angleSymm hDCE_FAS
  have hFAB_FAS : G.angleCongruent ⟨F, A, B⟩ ⟨F, A, S⟩ :=
    L.angleSameRayRight hRay
  have hFAB_DCE : G.angleCongruent ⟨F, A, B⟩ ⟨D, C, E⟩ :=
    I.angleTrans hFAB_FAS hFAS_DCE

  have hnotcolFAB : ¬ G.Collinear F A B := by
    intro hFAB
    rcases hRay.2.2 with hBS | hABS | hASB
    · subst S
      exact hFAS.2.2.2 hFAB
    · rcases hFAB with ⟨l1, hFl1, hAl1, hBl1⟩
      rcases I.betweenCollinear hABS with ⟨l2, hAl2, hBl2, hSl2⟩
      have hl : l1 = l2 := I.lineUnique hAB hAl1 hBl1 hAl2 hBl2
      exact hFAS.2.2.2 ⟨l1, hFl1, hAl1, by simpa [hl] using hSl2⟩
    · rcases hFAB with ⟨l1, hFl1, hAl1, hBl1⟩
      rcases I.betweenCollinear hASB with ⟨l2, hAl2, hSl2, hBl2⟩
      have hl : l1 = l2 := I.lineUnique hAB hAl1 hBl1 hAl2 hBl2
      exact hFAS.2.2.2 ⟨l1, hFl1, hAl1, by simpa [hl] using hSl2⟩

  exact ⟨F, hFAS.1, hnotcolFAB, hFAB_DCE⟩

/-- The usual existence statement of Euclid I.23. -/
theorem proposition23
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G]
    [SegmentSumGeometry G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [Proposition16ImplicitAxioms G]
    [SA : SegmentArithmeticImplicitAxioms G]
    [TriangleConstructionImplicitAxioms G]
    {A B D C E : G.Point}
    (hAB : A ≠ B)
    (hang : ValidAngle G ⟨D, C, E⟩) :
    ∃ F : G.Point,
      F ≠ A ∧ G.angleCongruent ⟨F, A, B⟩ ⟨D, C, E⟩ := by
  obtain ⟨F, hF, _hnoncol, hangle⟩ := proposition23_construction G hAB hang
  exact ⟨F, hF, hangle⟩

end Euclid.Book1
