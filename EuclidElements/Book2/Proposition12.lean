import EuclidElements.Book2.Proposition12_13Diagrams

/-! # Euclid II.12 -/
namespace Euclid.Book2

open Euclid
open Euclid.Book1

/-- In an obtuse triangle, the square on the side opposite the obtuse angle
equals the squares on the containing sides together with twice the rectangle
cut off outside by the perpendicular. -/
theorem proposition12
    (G : Geometry)
    [P : Postulates G] [I : ImplicitAxioms G] [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G] [TriangleAreaGeometry G] [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G] [AO : AngleOrderImplicitAxioms G]
    [D34 : Proposition34ImplicitAxioms G] [C46 : Proposition46ImplicitAxioms G]
    [LaterAreaGeometry G] [AF : AreaFoundations G] [QuadPartitionGeometry G]
    [AS : AreaSumFoundations G] [SF : SquareAreaFoundations G]
    [PD : PythagoreanDiagramAxioms G]
    [AreaGeometry G] [AA : AreaAxioms G] [B : Book1AreaMagnitudeBridge G]
    [D12 : Proposition12_13DiagramAxioms G]
    {A0 Bp C : G.Point}
    (htri : IsTriangle G A0 Bp C)
    (hobt : ObtuseAngle G ⟨Bp, A0, C⟩) :
    ∃ D : G.Point,
      G.between D A0 C ∧
      Sq G C Bp =
        Add G (Add G (Sq G A0 Bp) (Sq G A0 C))
          (Add G (Rect G D A0 A0 C) (Rect G D A0 A0 C)) := by
  obtain ⟨D, hDAC, hDCB, hrDCB, hDAB, hrDAB⟩ := D12.obtuseFoot htri hobt
  refine ⟨D, hDAC, ?_⟩
  let r : Area G := Rect G D A0 A0 C
  have h4 := proposition4 G hDAC
  have hpyCB := pythagoreanMagnitude G hDCB hrDCB
  have hpyAB := pythagoreanMagnitude G hDAB hrDAB
  change Sq G C Bp = Add G (Add G (Sq G A0 Bp) (Sq G A0 C)) (Add G r r)
  have h4' : Sq G D C =
      Add G (Add G (Sq G D A0) r) (Add G r (Sq G A0 C)) := by
    simpa [r] using h4
  calc
    Sq G C Bp = Add G (Sq G D C) (Sq G D Bp) := hpyCB.symm
    _ = Add G
          (Add G (Add G (Sq G D A0) r) (Add G r (Sq G A0 C)))
          (Sq G D Bp) := by rw [h4']
    _ = Add G
          (Add G (Sq G D A0) (Sq G D Bp))
          (Add G (Sq G A0 C) (Add G r r)) :=
            addPattern12 G _ _ _ _
    _ = Add G (Sq G A0 Bp) (Add G (Sq G A0 C) (Add G r r)) := by rw [hpyAB]
    _ = Add G (Add G (Sq G A0 Bp) (Sq G A0 C)) (Add G r r) :=
          (AA.addAssoc _ _ _).symm

end Euclid.Book2
