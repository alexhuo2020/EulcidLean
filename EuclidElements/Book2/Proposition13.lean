import EuclidElements.Book2.Proposition12

/-! # Euclid II.13 -/
namespace Euclid.Book2

open Euclid
open Euclid.Book1

/-- In an acute triangle, the square on the side opposite the acute angle is
less than the squares on the containing sides by twice the rectangle cut off
inside by the perpendicular; equivalently the latter sum is the former square
plus twice that rectangle. -/
theorem proposition13
    (G : Geometry)
    [P : Postulates G] [I : ImplicitAxioms G] [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G] [TriangleAreaGeometry G] [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G] [AO : AngleOrderImplicitAxioms G]
    [D34 : Proposition34ImplicitAxioms G] [C46 : Proposition46ImplicitAxioms G]
    [LaterAreaGeometry G] [AF : AreaFoundations G] [QuadPartitionGeometry G]
    [AS : AreaSumFoundations G] [SF : SquareAreaFoundations G]
    [PD : PythagoreanDiagramAxioms G]
    [AreaGeometry G] [AA : AreaAxioms G] [B : Book1AreaMagnitudeBridge G]
    [D13 : Proposition12_13DiagramAxioms G]
    {A0 Bp C : G.Point}
    (htri : IsTriangle G A0 Bp C)
    (hacute : AcuteAngle G ⟨A0, Bp, C⟩) :
    ∃ D : G.Point,
      G.between C D Bp ∧
      Add G (Sq G C Bp) (Sq G Bp A0) =
        Add G (Sq G C A0)
          (Add G (Rect G C Bp D Bp) (Rect G C Bp D Bp)) := by
  obtain ⟨D, hCDB, hDBA, hrDBA, hDCA, hrDCA⟩ := D13.acuteFoot htri hacute
  have h7 := proposition7 G hCDB
  have hpyBA := pythagoreanMagnitude G hDBA hrDBA
  have hpyCA0 := pythagoreanMagnitude G hDCA hrDCA
  have hCD_DC : Sq G C D = Sq G D C :=
    AA.squareCongr (I.segmentReverse C D)
  have hpyCA : Add G (Sq G C D) (Sq G D A0) = Sq G C A0 := by
    calc
      Add G (Sq G C D) (Sq G D A0)
          = Add G (Sq G D C) (Sq G D A0) :=
              addCongrLeft G hCD_DC (Sq G D A0)
      _ = Sq G C A0 := hpyCA0
  let r : Area G := Rect G C Bp D Bp
  refine ⟨D, hCDB, ?_⟩
  have h7' : Add G (Sq G C Bp) (Sq G D Bp) =
      Add G (Add G r r) (Sq G C D) := by
    simpa [r] using h7
  calc
    Add G (Sq G C Bp) (Sq G Bp A0)
        = Add G (Sq G C Bp) (Add G (Sq G D Bp) (Sq G D A0)) := by
            rw [← hpyBA]
    _ = Add G (Add G (Sq G C Bp) (Sq G D Bp)) (Sq G D A0) :=
          (AA.addAssoc _ _ _).symm
    _ = Add G (Add G (Add G r r) (Sq G C D)) (Sq G D A0) := by rw [h7']
    _ = Add G (Add G r r) (Add G (Sq G C D) (Sq G D A0)) :=
          AA.addAssoc _ _ _
    _ = Add G (Add G r r) (Sq G C A0) :=
          addCongrRight G (Add G r r) hpyCA
    _ = Add G (Sq G C A0) (Add G r r) := AA.addComm _ _

end Euclid.Book2
