import EuclidElements.Book4.TriangleConstructionFoundations

namespace Euclid.Book4

open Euclid
open Euclid.Book1

/-- Euclid IV.2: inscribe in a circle a triangle equiangular with a given
    triangle. -/
theorem proposition2
    (G : Geometry)
    [T : TriangleBook4ConstructionAxioms G]
    [A : ThirdAngleCongruenceAxioms G]
    {c : G.Circle} {D E F : G.Point}
    (hDEF : IsTriangle G D E F) :
    ∃ A0 B C : G.Point,
      TriangleInscribedInCircle G c A0 B C ∧
      EquiangularTriangles G A0 B C D E F := by
  obtain ⟨A0, B, C, hABC, hA, hB, hC, hBangle, hCangle⟩ :=
    T.inscribedFrame hDEF
  have hAangle : G.angleCongruent ⟨B, A0, C⟩ ⟨E, D, F⟩ :=
    A.third hABC hDEF hBangle hCangle
  exact ⟨A0, B, C,
    ⟨hABC, hA, hB, hC⟩,
    ⟨hAangle, hBangle, hCangle⟩⟩

end Euclid.Book4
