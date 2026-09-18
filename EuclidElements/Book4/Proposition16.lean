import EuclidElements.Book4.Proposition15
import EuclidElements.Book4.Proposition11
import EuclidElements.Book4.Proposition02
import EuclidElements.Book4.Proposition01

namespace Euclid.Book4

open Euclid
open Euclid.Book1
open Euclid.Book3

/-- Euclid IV.16: inscribe a regular fifteen-gon in a given circle.  The
    construction explicitly uses IV.2, IV.11, and IV.1 in Euclid's order. -/
theorem proposition16
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
    [TC : TriangleBook4ConstructionAxioms G]
    [TA : ThirdAngleCongruenceAxioms G]
    [DE : DiameterExistenceAxioms G]
    [SC : ShortChordContinuityAxioms G]
    [ET : EquilateralTriangleExistenceAxioms G]
    [F15 : FifteenGonGeometry G]
    [FR : FifteenGonRegularityFoundations G]
    [FC : FifteenGonConstructionAxioms G]
    {c : G.Circle} :
    ∃ p : FifteenGon G, FifteenGonInscribedInCircle G c p := by
  obtain ⟨D, E, F, hDEF, hequil⟩ := ET.existsTriangle
  obtain ⟨A, B, C, htriIn, hequiang⟩ := proposition2 G hDEF
  obtain ⟨P, Q, R, S, T, hpent⟩ := proposition11 G (c := c)
  obtain ⟨U, V, hbound⟩ := FC.seed htriIn hDEF hequil hequiang hpent
  obtain ⟨X, Y, hchord, hXY_UV⟩ := proposition1 G hbound
  obtain ⟨p, hsteps, honcircle⟩ :=
    FC.complete htriIn hpent hchord hXY_UV
  have hreg : RegularFifteenGon G p := FR.regularOfEqualArcSteps hsteps
  exact ⟨p, hreg, honcircle⟩

end Euclid.Book4
