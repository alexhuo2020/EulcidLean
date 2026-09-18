import EuclidElements.Book1.Proposition16
import EuclidElements.Book1.Proposition20
import EuclidElements.Book1.InteriorImplicitAxioms

/-!
# Euclid I.21 -- an interior broken line is shorter and subtends a greater angle
-/

namespace Euclid.Book1

open Euclid

theorem proposition21
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
    [P16 : Proposition16ImplicitAxioms G]
    [SA : SegmentArithmeticImplicitAxioms G]
    [IN : InteriorImplicitAxioms G]
    {A B C D : G.Point}
    (htri : IsTriangle G A B C)
    (hinside : InsideTriangle G A B C D) :
    SegmentSumLess G B D D C B A A C ∧
    G.angleLess ⟨B, A, C⟩ ⟨B, D, C⟩ := by
  obtain ⟨E, hAEC, hBDE, hABEtri, hEDCtri⟩ := IN.cevianIntersection htri hinside

  have hsum1 : SegmentSumGreater G B A A E B E := proposition20 G hABEtri
  have hDECtri : IsTriangle G D E C :=
    L.triangleCycle (L.triangleCycle (L.triangleSwap23 hEDCtri))
  have hsum2 : SegmentSumGreater G E D D C E C := proposition20 G hDECtri
  have hsum : SegmentSumLess G B D D C B A A C :=
    SA.combineInteriorBrokenLines hAEC hBDE hsum1 hsum2

  have hEDB : G.between E D B := L.betweenSymm hBDE
  have hCEDtri : IsTriangle G C E D := L.triangleCycle (L.triangleCycle hEDCtri)
  have hext1 := proposition16 G hCEDtri hEDB
  have hCED_CDB : G.angleLess ⟨C, E, D⟩ ⟨C, D, B⟩ := hext1.2

  have hEneB : E ≠ B := Ne.symm (I.betweenDistinct hBDE).2.2
  have hEneD : E ≠ D := Ne.symm (I.betweenDistinct hBDE).2.1
  have hrayEBD : SameRay G E B D :=
    ⟨hEneB, hEneD, Or.inr (Or.inr hEDB)⟩
  have hCEB_CED : G.angleCongruent ⟨C, E, B⟩ ⟨C, E, D⟩ :=
    L.angleSameRayRight hrayEBD
  have hBEC_CED : G.angleCongruent ⟨B, E, C⟩ ⟨C, E, D⟩ :=
    I.angleTrans (L.angleReverse B E C) hCEB_CED
  have hBEC_CDB : G.angleLess ⟨B, E, C⟩ ⟨C, D, B⟩ :=
    AO.lt_congr_left (I.angleSymm hBEC_CED) hCED_CDB

  have hBAEtri : IsTriangle G B A E :=
    L.triangleCycle (L.triangleCycle (L.triangleSwap23 hABEtri))
  have hext2 := proposition16 G hBAEtri hAEC
  have hBAE_BEC : G.angleLess ⟨B, A, E⟩ ⟨B, E, C⟩ := hext2.2
  have hAneC : A ≠ C := Ne.symm htri.2.2.1
  have hAneE : A ≠ E := (I.betweenDistinct hAEC).1
  have hrayACE : SameRay G A C E :=
    ⟨hAneC, hAneE, Or.inr (Or.inr hAEC)⟩
  have hBAC_BAE : G.angleCongruent ⟨B, A, C⟩ ⟨B, A, E⟩ :=
    L.angleSameRayRight hrayACE
  have hBAC_BEC : G.angleLess ⟨B, A, C⟩ ⟨B, E, C⟩ :=
    AO.lt_congr_left (I.angleSymm hBAC_BAE) hBAE_BEC
  have hBAC_CDB : G.angleLess ⟨B, A, C⟩ ⟨C, D, B⟩ :=
    AO.lt_trans hBAC_BEC hBEC_CDB
  have hCDB_BDC : G.angleCongruent ⟨C, D, B⟩ ⟨B, D, C⟩ :=
    L.angleReverse C D B
  have hangle : G.angleLess ⟨B, A, C⟩ ⟨B, D, C⟩ :=
    AO.lt_congr_right hCDB_BDC hBAC_CDB
  exact ⟨hsum, hangle⟩

end Euclid.Book1
