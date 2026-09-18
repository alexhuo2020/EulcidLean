import EuclidElements.Book4.TriangleConstructionFoundations

namespace Euclid.Book4

open Euclid
open Euclid.Book1
open Euclid.Book3

/-- Euclid IV.3: circumscribe about a circle a triangle equiangular with a
    given triangle. -/
theorem proposition3
    (G : Geometry)
    [T : TriangleBook4ConstructionAxioms G]
    [A : ThirdAngleCongruenceAxioms G]
    {c : G.Circle} {D E F : G.Point}
    (hDEF : IsTriangle G D E F) :
    ∃ A0 B C : G.Point,
      CircleInscribedInTriangle G c A0 B C ∧
      EquiangularTriangles G A0 B C D E F := by
  obtain ⟨A0, B, C, lAB, lBC, lCA, P, Q, R,
      hABC, hAB, hBC, hCA, htAB, htBC, htCA, hBangle, hCangle⟩ :=
    T.circumscribedFrame hDEF
  have hAangle : G.angleCongruent ⟨B, A0, C⟩ ⟨E, D, F⟩ :=
    A.third hABC hDEF hBangle hCangle
  refine ⟨A0, B, C, ?_, ⟨hAangle, hBangle, hCangle⟩⟩
  exact ⟨hABC, lAB, lBC, lCA, P, Q, R, hAB, hBC, hCA, htAB, htBC, htCA⟩

end Euclid.Book4
