import EuclidElements.Book1.Proposition05
import EuclidElements.Book1.Proposition18

/-!
# Euclid I.19 -- the greater angle is subtended by the greater side
-/

namespace Euclid.Book1

open Euclid

theorem proposition19
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [Proposition16ImplicitAxioms G]
    {A B C : G.Point}
    (htri : IsTriangle G A B C)
    (hC_lt_B : G.angleLess ⟨B, C, A⟩ ⟨A, B, C⟩) :
    SegmentLess G A B A C := by
  rcases L.segmentTrichotomy A B A C with hEq | hABltAC | hACltAB
  · have hbase := proposition5_baseAngles G htri hEq
    exact False.elim ((AO.lt_not_congr hC_lt_B) (I.angleSymm hbase))
  · exact hABltAC
  · have htri' : IsTriangle G A C B := L.triangleSwap23 htri
    have hwrong := proposition18 G htri' hACltAB
    have hACB_BCA : G.angleCongruent ⟨A, C, B⟩ ⟨B, C, A⟩ := L.angleReverse A C B
    have hABC_CBA : G.angleCongruent ⟨A, B, C⟩ ⟨C, B, A⟩ := L.angleReverse A B C
    have h1 : G.angleLess ⟨C, B, A⟩ ⟨A, C, B⟩ := hwrong
    have h2 : G.angleLess ⟨A, B, C⟩ ⟨A, C, B⟩ :=
      AO.lt_congr_left (I.angleSymm hABC_CBA) h1
    have hB_lt_C : G.angleLess ⟨A, B, C⟩ ⟨B, C, A⟩ :=
      AO.lt_congr_right hACB_BCA h2
    have hcycle : G.angleLess ⟨B, C, A⟩ ⟨B, C, A⟩ :=
      AO.lt_trans hC_lt_B hB_lt_C
    exact False.elim ((AO.lt_not_congr hcycle) (I.angleRefl ⟨B, C, A⟩))

end Euclid.Book1
