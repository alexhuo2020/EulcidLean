import EuclidElements.Book1.Proposition03
import EuclidElements.Book1.Proposition04

/-!
# Euclid I.6 -- converse of the isosceles triangle theorem
-/

namespace Euclid.Book1

open Euclid

theorem proposition6
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    [S : SegmentOrder G]
    [A : TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    {A B C : G.Point}
    (htri : IsTriangle G A B C)
    (hangles : G.angleCongruent ⟨A, B, C⟩ ⟨B, C, A⟩) :
    G.segmentCongruent A B A C := by

  have greaterImpossible : ∀ {X Y Z : G.Point},
      IsTriangle G X Y Z →
      G.angleCongruent ⟨X, Y, Z⟩ ⟨Y, Z, X⟩ →
      SegmentLess G X Z X Y → False := by
    intro X Y Z hXYZ hbase hXZltXY

    have hXZ : X ≠ Z := Ne.symm hXYZ.2.2.1
    have hXY_YX : G.segmentCongruent X Y Y X := I.segmentReverse X Y
    have hXZltYX : SegmentLess G X Z Y X :=
      L.segmentLess_congr_right hXY_YX hXZltXY

    obtain ⟨D, hYDX, hYD_XZ⟩ := proposition3 G Y X X Z hXZ hXZltYX
    have hXDY : G.between X D Y := L.betweenSymm hYDX

    have hYDC : IsTriangle G Y D Z := L.triangleOnSide hXYZ hXDY
    have hZXY : IsTriangle G Z X Y := by
      exact L.triangleCycle (L.triangleCycle hXYZ)

    have hXZ_ZX : G.segmentCongruent X Z Z X := I.segmentReverse X Z
    have hYD_ZX : G.segmentCongruent Y D Z X := I.segmentTrans hYD_XZ hXZ_ZX
    have hYZ_ZY : G.segmentCongruent Y Z Z Y := I.segmentReverse Y Z

    have hDYZ_XYZ : G.angleCongruent ⟨D, Y, Z⟩ ⟨X, Y, Z⟩ :=
      L.angleSameRay hXDY
    have hYZX_XZY : G.angleCongruent ⟨Y, Z, X⟩ ⟨X, Z, Y⟩ :=
      L.angleReverse Y Z X
    have hXYZ_XZY : G.angleCongruent ⟨X, Y, Z⟩ ⟨X, Z, Y⟩ :=
      I.angleTrans hbase hYZX_XZY
    have hDYZ_XZY : G.angleCongruent ⟨D, Y, Z⟩ ⟨X, Z, Y⟩ :=
      I.angleTrans hDYZ_XYZ hXYZ_XZY

    have hsas := proposition4 G hYDC hZXY hYD_ZX hYZ_ZY hDYZ_XZY
    have hareaYDZ_ZXY : TriangleAreaEq G Y D Z Z X Y := hsas.2.2.2

    have hareaDYZ_YDZ : TriangleAreaEq G D Y Z Y D Z :=
      L.areaEq_swap12 D Y Z
    have hareaXYZ_YZX : TriangleAreaEq G X Y Z Y Z X :=
      L.areaEq_cycle X Y Z
    have hareaYZX_ZXY : TriangleAreaEq G Y Z X Z X Y :=
      L.areaEq_cycle Y Z X
    have hareaXYZ_ZXY : TriangleAreaEq G X Y Z Z X Y :=
      L.areaEq_trans hareaXYZ_YZX hareaYZX_ZXY
    have hareaZXY_XYZ : TriangleAreaEq G Z X Y X Y Z :=
      L.areaEq_symm hareaXYZ_ZXY

    have hareaDYZ_XYZ : TriangleAreaEq G D Y Z X Y Z :=
      L.areaEq_trans (L.areaEq_trans hareaDYZ_YDZ hareaYDZ_ZXY) hareaZXY_XYZ

    have hproper : TriangleAreaLess G D Y Z X Y Z :=
      L.properSubtriangle_on_side hXDY hXYZ.2.2.2

    exact (L.equalArea_not_less hareaDYZ_XYZ) hproper

  rcases L.segmentTrichotomy A B A C with hEq | hABltAC | hACltAB
  · exact hEq
  · have htri' : IsTriangle G A C B := L.triangleSwap23 htri
    have hACB_BCA : G.angleCongruent ⟨A, C, B⟩ ⟨B, C, A⟩ :=
      L.angleReverse A C B
    have hBCA_ABC : G.angleCongruent ⟨B, C, A⟩ ⟨A, B, C⟩ :=
      I.angleSymm hangles
    have hABC_CBA : G.angleCongruent ⟨A, B, C⟩ ⟨C, B, A⟩ :=
      L.angleReverse A B C
    have hswapAngles : G.angleCongruent ⟨A, C, B⟩ ⟨C, B, A⟩ :=
      I.angleTrans (I.angleTrans hACB_BCA hBCA_ABC) hABC_CBA
    exact False.elim (greaterImpossible htri' hswapAngles hABltAC)
  · exact False.elim (greaterImpossible htri hangles hACltAB)

end Euclid.Book1
