import EuclidElements.Book1.Proposition42
import EuclidElements.Book1.Proposition43

namespace Euclid.Book1

open Euclid

/-- I.44: apply to a given straight line a parallelogram equal to a given triangle in a given angle. -/
theorem proposition44
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
    [LaterAreaGeometry G]
    [AreaDiagramGeometry G]
    [AF : AreaFoundations G]
    [AT : AreaTriangleConstructionAxioms G]
    [AC : AreaApplicationConstructionAxioms G]
    [CF : AreaComplementFoundations G]
    {A B C D E : G.Point} {α : Angle G.Point}
    (hAB : A ≠ B) (htri : IsTriangle G C D E) (hang : ValidAngle G α) :
    ∃ F H : G.Point,
      Parallelogram G A B F H ∧
      TriangleQuadAreaEq G C D E A B F H ∧
      G.angleCongruent ⟨H, A, B⟩ α := by
  obtain ⟨Pp, Q, R, S, htemp, htri_temp, htempAngle⟩ :=
    proposition42 G htri hang

  obtain ⟨F, H, htarget, hcomp, htargetAngle⟩ :=
    AC.applyParallelogramFrame hAB htemp hang htempAngle

  have htemp_target : QuadAreaEq G Pp Q R S A B F H :=
    proposition43 G hcomp
  have htri_target : TriangleQuadAreaEq G C D E A B F H :=
    AF.triangleQuadEq_trans_quad htri_temp htemp_target

  exact ⟨F, H, htarget, htri_target, htargetAngle⟩

end Euclid.Book1
