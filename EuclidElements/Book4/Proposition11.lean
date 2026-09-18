import EuclidElements.Book4.Proposition10

namespace Euclid.Book4

open Euclid
open Euclid.Book1
open Euclid.Book3

/-- Euclid IV.11: inscribe a regular pentagon in a given circle. -/
theorem proposition11
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
    ∃ A B C D E : G.Point, PentagonInscribedInCircle G c A B C D E := by
  obtain ⟨X, Y, Z, hXYZ, hXY_XZ, hdoubleY, hdoubleZ⟩ := proposition10 G
  obtain ⟨A, B, C, D, E,
      hEAB, hABC, hBCD, hCDE, hDEA,
      hA, hB, hC, hD, hE, heqSide, heqAngle⟩ :=
    PC.inscribedFromGolden hXYZ
  exact ⟨A, B, C, D, E,
    ⟨⟨hEAB, hABC, hBCD, hCDE, hDEA, heqSide, heqAngle⟩,
      hA, hB, hC, hD, hE⟩⟩

end Euclid.Book4
