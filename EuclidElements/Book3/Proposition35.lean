import EuclidElements.Book3.CirclePowerFoundations

namespace Euclid.Book3

open Euclid
open Euclid.Book1
open Euclid.Book2

/-- Euclid III.35: intersecting chords have equal rectangle products. -/
theorem proposition35
    (G : Geometry)
    [I : ImplicitAxioms G]
    [AreaGeometry G] [AA : AreaAxioms G]
    [P : Postulates G]
    [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [D34 : Proposition34ImplicitAxioms G]
    [C46 : Proposition46ImplicitAxioms G]
    [LaterAreaGeometry G]
    [AF : AreaFoundations G]
    [QuadPartitionGeometry G]
    [AS : AreaSumFoundations G]
    [SF : SquareAreaFoundations G]
    [PD : PythagoreanDiagramAxioms G]
    [B : Book1AreaMagnitudeBridge G]
    [CB : CircleBasicAxioms G]
    [CP : CirclePowerDiagramAxioms G]
    {c : G.Circle} {O A E C D Bp : G.Point}
    (hcenter : G.isCenter c O)
    (hA : G.onCircle A c) (hC : G.onCircle C c)
    (hD : G.onCircle D c) (hB : G.onCircle Bp c)
    (hAEC : G.between A E C)
    (hDEB : G.between D E Bp) :
    Rect G A E E C = Rect G D E E Bp := by
  obtain ⟨A', C', F1, hAE, hEC, hA', hC'⟩ :=
    CP.interiorFrame hcenter hA hC hAEC
  obtain ⟨D', B', F2, hDE, hEB, hD', hB'⟩ :=
    CP.interiorFrame hcenter hD hB hDEB
  have hp1 := interiorChordPower G F1
  have hp2 := interiorChordPower G F2
  have hrect1 : Rect G A E E C = Rect G A' E E C' := by
    calc
      Rect G A E E C = Rect G A' E E C := AA.rectCongrLeft hAE
      _ = Rect G A' E E C' := AA.rectCongrRight hEC
  have hrect2 : Rect G D E E Bp = Rect G D' E E B' := by
    calc
      Rect G D E E Bp = Rect G D' E E Bp := AA.rectCongrLeft hDE
      _ = Rect G D' E E B' := AA.rectCongrRight hEB
  have hrad : G.segmentCongruent O C' O B' :=
    CB.radiiCongruent hcenter hC' hB'
  have hsq : Sq G O C' = Sq G O B' := AA.squareCongr hrad
  have heq : Add G (Rect G A E E C) (Sq G O E) =
      Add G (Rect G D E E Bp) (Sq G O E) := by
    calc
      Add G (Rect G A E E C) (Sq G O E)
          = Add G (Rect G A' E E C') (Sq G O E) := by rw [hrect1]
      _ = Sq G O C' := hp1
      _ = Sq G O B' := hsq
      _ = Add G (Rect G D' E E B') (Sq G O E) := hp2.symm
      _ = Add G (Rect G D E E Bp) (Sq G O E) := by rw [← hrect2]
  apply AA.addCancelLeft (Sq G O E)
  calc
    Add G (Sq G O E) (Rect G A E E C)
        = Add G (Rect G A E E C) (Sq G O E) := AA.addComm _ _
    _ = Add G (Rect G D E E Bp) (Sq G O E) := heq
    _ = Add G (Sq G O E) (Rect G D E E Bp) := AA.addComm _ _

end Euclid.Book3
