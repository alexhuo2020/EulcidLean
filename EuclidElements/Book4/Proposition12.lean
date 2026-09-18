import EuclidElements.Book4.Proposition11

namespace Euclid.Book4

open Euclid
open Euclid.Book1
open Euclid.Book3

/-- Euclid IV.12: circumscribe a regular pentagon about a given circle. -/
theorem proposition12
    (G : Geometry)
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleInteriorGeometry G]
    [AngleSumGeometry G]
    [AngleAdditionGeometry G]
    [AA : AngleAdditionImplicitAxioms G]
    [ALG : AngleSumAlgebraFoundations G]
    [GT : GoldenTriangleConstructionAxioms G]
    [PC : PentagonBook4ConstructionAxioms G]
    {c : G.Circle} :
    ∃ A B C D E : G.Point, CircleInscribedInPentagon G c A B C D E := by
  obtain ⟨A0, B0, C0, D0, E0, hins⟩ := proposition11 G (c := c)
  obtain ⟨A, B, C, D, E, lAB, lBC, lCD, lDE, lEA, T, U, V, W, X,
      hEAB, hABC, hBCD, hCDE, hDEA, heqSide, heqAngle,
      hAB, hBC, hCD, hDE, hEA, htAB, htBC, htCD, htDE, htEA⟩ :=
    PC.circumscribedFromInscribed hins
  refine ⟨A, B, C, D, E, ?_⟩
  refine ⟨⟨hEAB, hABC, hBCD, hCDE, hDEA, heqSide, heqAngle⟩, ?_⟩
  exact ⟨lAB, lBC, lCD, lDE, lEA, T, U, V, W, X,
    hAB, hBC, hCD, hDE, hEA, htAB, htBC, htCD, htDE, htEA⟩

end Euclid.Book4
