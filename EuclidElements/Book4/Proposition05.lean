import EuclidElements.Book4.TriangleConstructionFoundations

namespace Euclid.Book4

open Euclid
open Euclid.Book1

/-- Euclid IV.5: circumscribe a circle about a given triangle.  The construction
    frame supplies the perpendicular-bisector intersection and its equal
    distances; Postulate 3 then produces the circle. -/
theorem proposition5
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [T : TriangleBook4ConstructionAxioms G]
    {A B C : G.Point}
    (hABC : IsTriangle G A B C) :
    ∃ c : G.Circle, CircleCircumscribedAboutTriangle G c A B C := by
  obtain ⟨O, hOA, hOA_OB, hOA_OC⟩ := T.circumcenterFrame hABC
  obtain ⟨c, hcenter, hAc, hcircle⟩ := P.postulate3 O A hOA
  have hBc : G.onCircle B c := (hcircle B).2 (I.segmentSymm hOA_OB)
  have hCc : G.onCircle C c := (hcircle C).2 (I.segmentSymm hOA_OC)
  exact ⟨c, hABC, hAc, hBc, hCc⟩

end Euclid.Book4
