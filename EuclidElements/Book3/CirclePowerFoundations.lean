import EuclidElements.Book3.Proposition32
import EuclidElements.Book2.Proposition06
import EuclidElements.Book2.Book1AreaBridge

namespace Euclid.Book3

open Euclid
open Euclid.Book1
open Euclid.Book2

structure InteriorChordPowerFrame (G : Geometry)
    (O A E C : G.Point) where
  g : G.Point
  hmid : IsMidpoint G g A C
  hAGE : G.between A g E
  hGEC : G.between g E C
  htriE : IsTriangle G g E O
  hrightE : RightAngle G ⟨E, g, O⟩
  htriC : IsTriangle G g C O
  hrightC : RightAngle G ⟨C, g, O⟩

structure ExternalSecantPowerFrame (G : Geometry)
    (O A C D : G.Point) where
  f : G.Point
  hmid : IsMidpoint G f A C
  hACD : G.between A C D
  hFCD : G.between f C D
  htriC : IsTriangle G f C O
  hrightC : RightAngle G ⟨C, f, O⟩
  htriD : IsTriangle G f D O
  hrightD : RightAngle G ⟨D, f, O⟩

class CirclePowerDiagramAxioms (G : Geometry) : Prop where
  interiorFrame : forall {c : G.Circle} {O A E C : G.Point},
    G.isCenter c O -> G.onCircle A c -> G.onCircle C c ->
    G.between A E C ->
    ∃ A' C' : G.Point,
    ∃ F : InteriorChordPowerFrame G O A' E C',
      G.segmentCongruent A E A' E ∧
      G.segmentCongruent E C E C' ∧
      G.onCircle A' c ∧ G.onCircle C' c

  externalFrame : forall {c : G.Circle} {O D C A : G.Point},
    G.isCenter c O -> G.onCircle C c -> G.onCircle A c ->
    G.between D C A ->
    ∃ A' C' : G.Point,
    ∃ F : ExternalSecantPowerFrame G O A' C' D,
      G.segmentCongruent D A D A' ∧
      G.segmentCongruent D C D C' ∧
      G.onCircle A' c ∧ G.onCircle C' c

theorem interiorChordPower
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
    {O A E C : G.Point}
    (F : InteriorChordPowerFrame G O A E C) :
    Add G (Rect G A E E C) (Sq G O E) = Sq G O C := by
  have h5 := proposition5 G F.hmid F.hAGE F.hGEC
  have hpyE := pythagoreanMagnitude G F.htriE F.hrightE
  have hpyC := pythagoreanMagnitude G F.htriC F.hrightC
  have hEO_OE : Sq G E O = Sq G O E :=
    AA.squareCongr (I.segmentReverse E O)
  have hCO_OC : Sq G C O = Sq G O C :=
    AA.squareCongr (I.segmentReverse C O)
  calc
    Add G (Rect G A E E C) (Sq G O E)
        = Add G (Rect G A E E C) (Sq G E O) := by rw [hEO_OE]
    _ = Add G (Rect G A E E C) (Add G (Sq G F.g E) (Sq G F.g O)) := by rw [hpyE]
    _ = Add G (Add G (Rect G A E E C) (Sq G F.g E)) (Sq G F.g O) :=
      (AA.addAssoc _ _ _).symm
    _ = Add G (Sq G F.g C) (Sq G F.g O) := by rw [h5]
    _ = Sq G C O := hpyC
    _ = Sq G O C := hCO_OC

theorem externalSecantPower
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
    {O A C D : G.Point}
    (F : ExternalSecantPowerFrame G O A C D) :
    Add G (Rect G A D C D) (Sq G O C) = Sq G O D := by
  have h6 := proposition6 G F.hmid F.hACD F.hFCD
  have hpyC := pythagoreanMagnitude G F.htriC F.hrightC
  have hpyD := pythagoreanMagnitude G F.htriD F.hrightD
  have hCO_OC : Sq G C O = Sq G O C :=
    AA.squareCongr (I.segmentReverse C O)
  have hDO_OD : Sq G D O = Sq G O D :=
    AA.squareCongr (I.segmentReverse D O)
  calc
    Add G (Rect G A D C D) (Sq G O C)
        = Add G (Rect G A D C D) (Sq G C O) := by rw [← hCO_OC]
    _ = Add G (Rect G A D C D) (Add G (Sq G F.f C) (Sq G F.f O)) := by rw [hpyC]
    _ = Add G (Add G (Rect G A D C D) (Sq G F.f C)) (Sq G F.f O) :=
      (AA.addAssoc _ _ _).symm
    _ = Add G (Sq G F.f D) (Sq G F.f O) := by rw [h6]
    _ = Sq G D O := hpyD
    _ = Sq G O D := hDO_OD

end Euclid.Book3
