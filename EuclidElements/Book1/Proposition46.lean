import EuclidElements.Book1.Proposition46ImplicitAxioms

/-!
# Euclid I.46 -- construct a square on a given straight line
-/

namespace Euclid.Book1

open Euclid

theorem proposition46
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [D34 : Proposition34ImplicitAxioms G]
    [C46 : Proposition46ImplicitAxioms G]
    {A B : G.Point}
    (hAB : A ≠ B) :
    ∃ C D : G.Point, Square G A B C D := by
  obtain ⟨C, D, hquad, hpara, hAB_DA, hright⟩ := C46.squareFrame hAB
  have h34 := proposition34 G hpara
  have hAB_CD : G.segmentCongruent A B C D := h34.1
  have hBC_DA : G.segmentCongruent B C D A := h34.2.1

  have hDA_BC : G.segmentCongruent D A B C := I.segmentSymm hBC_DA
  have hAB_BC : G.segmentCongruent A B B C := I.segmentTrans hAB_DA hDA_BC
  have hBC_CD : G.segmentCongruent B C C D := by
    have hBC_AB : G.segmentCongruent B C A B := I.segmentTrans hBC_DA (I.segmentSymm hAB_DA)
    exact I.segmentTrans hBC_AB hAB_CD
  have hCD_DA : G.segmentCongruent C D D A := by
    have hCD_AB : G.segmentCongruent C D A B := I.segmentSymm hAB_CD
    exact I.segmentTrans hCD_AB hAB_DA

  have heq : EquilateralQuadrilateral G A B C D :=
    ⟨hAB_BC, hBC_CD, hCD_DA⟩
  exact ⟨C, D, hquad, heq, hright⟩

end Euclid.Book1
