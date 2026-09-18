import EuclidElements.Book1.Proposition10
import EuclidElements.Book1.Proposition15
import EuclidElements.Book1.AngleOrderImplicitAxioms

/-!
# Euclid I.16 -- the exterior angle is greater than either remote interior angle
-/

namespace Euclid.Book1

open Euclid

theorem proposition16
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [P16 : Proposition16ImplicitAxioms G]
    {A B C D : G.Point}
    (htri : IsTriangle G A B C)
    (hBCD : G.between B C D) :
    G.angleLess ⟨B, A, C⟩ ⟨A, C, D⟩ ∧
    G.angleLess ⟨A, B, C⟩ ⟨A, C, D⟩ := by
  have hAC : A ≠ C := Ne.symm htri.2.2.1
  obtain ⟨E, hmid⟩ := proposition10 G A C hAC
  have hAEC := hmid.1
  have hAE_EC := hmid.2
  have hBE : B ≠ E := by
    intro h
    subst E
    exact htri.2.2.2 (I.betweenCollinear hAEC)
  obtain ⟨F, hBEF, hEB_EF⟩ := L.symmetricPoint (D := B) (C := E) hBE

  obtain ⟨hEABtri, hECFtri⟩ := P16.constructionTriangles htri hAEC hBEF
  have hnoncolAEB : ¬ G.Collinear A E B := by
    intro hAEB
    rcases I.betweenCollinear hAEC with ⟨l0, hAl0, hEl0, hCl0⟩
    rcases hAEB with ⟨l1, hAl1, hEl1, hBl1⟩
    have hAE : A ≠ E := (I.betweenDistinct hAEC).1
    have hl : l1 = l0 := I.lineUnique hAE hAl1 hEl1 hAl0 hEl0
    exact htri.2.2.2 ⟨l0, hAl0, by simpa [hl] using hBl1, hCl0⟩
  have hvert := proposition15 G hAEC hBEF hnoncolAEB
  have hAEB_CEF : G.angleCongruent ⟨A, E, B⟩ ⟨C, E, F⟩ := hvert.1
  have hEA_AE : G.segmentCongruent E A A E := I.segmentReverse E A
  have hEA_EC : G.segmentCongruent E A E C := I.segmentTrans hEA_AE hAE_EC
  have hsas := proposition4 G hEABtri hECFtri hEA_EC hEB_EF hAEB_CEF
  have hEAB_ECF : G.angleCongruent ⟨E, A, B⟩ ⟨E, C, F⟩ := hsas.2.1

  have hAneE : A ≠ E := (I.betweenDistinct hAEC).1
  have hrayAEC : SameRay G A C E :=
    ⟨hAC, hAneE, Or.inr (Or.inr hAEC)⟩
  have hCAB_EAB : G.angleCongruent ⟨C, A, B⟩ ⟨E, A, B⟩ :=
    L.angleSameRayLeft hrayAEC
  have hBAC_EAB : G.angleCongruent ⟨B, A, C⟩ ⟨E, A, B⟩ :=
    I.angleTrans (L.angleReverse B A C) hCAB_EAB
  have hBAC_ECF : G.angleCongruent ⟨B, A, C⟩ ⟨E, C, F⟩ :=
    I.angleTrans hBAC_EAB hEAB_ECF

  have hins : InsideAngle G A C D F :=
    P16.constructedRayInsideExterior htri hBCD hmid hBEF hEB_EF
  have hACF_ACD : G.angleLess ⟨A, C, F⟩ ⟨A, C, D⟩ :=
    AO.properSubangleLeft hins
  have hCEA : G.between C E A := L.betweenSymm hAEC
  have hCneA : C ≠ A := htri.2.2.1
  have hCneE : C ≠ E := Ne.symm (I.betweenDistinct hAEC).2.1
  have hrayCEA : SameRay G C A E :=
    ⟨hCneA, hCneE, Or.inr (Or.inr hCEA)⟩
  have hACF_ECF : G.angleCongruent ⟨A, C, F⟩ ⟨E, C, F⟩ :=
    L.angleSameRayLeft hrayCEA
  have hECF_ACF : G.angleCongruent ⟨E, C, F⟩ ⟨A, C, F⟩ :=
    I.angleSymm hACF_ECF
  have hECF_ACD : G.angleLess ⟨E, C, F⟩ ⟨A, C, D⟩ :=
    AO.lt_congr_left hACF_ECF hACF_ACD
  have hremoteA : G.angleLess ⟨B, A, C⟩ ⟨A, C, D⟩ :=
    AO.lt_congr_left (I.angleSymm hBAC_ECF) hECF_ACD
  have hremoteB : G.angleLess ⟨A, B, C⟩ ⟨A, C, D⟩ :=
    P16.mirroredExteriorReduction htri hBCD hremoteA
  exact ⟨hremoteA, hremoteB⟩

end Euclid.Book1
