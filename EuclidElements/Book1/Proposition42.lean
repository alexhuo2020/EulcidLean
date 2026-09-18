import EuclidElements.Book1.Proposition41
import EuclidElements.Book1.AreaConstructionAxioms

namespace Euclid.Book1

open Euclid

/-- I.42: construct a parallelogram equal to a given triangle in a given angle. -/
theorem proposition42
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
    [AF : AreaFoundations G]
    [AC : AreaTriangleConstructionAxioms G]
    {A B C : G.Point} {α : Angle G.Point}
    (htri : IsTriangle G A B C) (hang : ValidAngle G α) :
    ∃ D E F H : G.Point,
      Parallelogram G D E F H ∧
      TriangleQuadAreaEq G A B C D E F H ∧
      G.angleCongruent ⟨H, D, E⟩ α := by
  obtain ⟨M, D, E, F, H, base, top,
    hmid, hAMC, hpara, hDEF, hMC_EF,
    hMb, hCb, hEb, hFb, hAt, hDt, hpar, hangle⟩ :=
    AC.triangleParallelogramFrame htri hang

  have hAMC_DEF : TriangleAreaEq G A M C D E F :=
    AF.equalBaseSameAltitude hAMC hDEF hMC_EF
      hMb hCb hEb hFb hAt hDt hpar

  have hdouble : QuadDoubleTriangle G D E F H D E F :=
    proposition41 G hpara hDEF

  have heq : TriangleQuadAreaEq G A B C D E F H :=
    AF.triangleQuadEq_of_midpointHalf hmid hAMC_DEF hdouble

  exact ⟨D, E, F, H, hpara, heq, hangle⟩

end Euclid.Book1
