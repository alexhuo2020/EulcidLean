import EuclidElements.Book4.Proposition13

namespace Euclid.Book4

open Euclid
open Euclid.Book1

/-- Euclid IV.14: circumscribe a circle about a regular pentagon. -/
theorem proposition14
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [AngleAdditionGeometry G]
    [PC : PentagonBook4ConstructionAxioms G]
    {A B C D E : G.Point}
    (hreg : RegularPentagon G A B C D E) :
    ∃ c : G.Circle, CircleCircumscribedAboutPentagon G c A B C D E := by
  obtain ⟨O, hOA, hOA_OB, hOA_OC, hOA_OD, hOA_OE⟩ := PC.circumcenterFrame hreg
  obtain ⟨c, hcenter, hAc, hcircle⟩ := P.postulate3 O A hOA
  have hBc : G.onCircle B c := (hcircle B).2 (I.segmentSymm hOA_OB)
  have hCc : G.onCircle C c := (hcircle C).2 (I.segmentSymm hOA_OC)
  have hDc : G.onCircle D c := (hcircle D).2 (I.segmentSymm hOA_OD)
  have hEc : G.onCircle E c := (hcircle E).2 (I.segmentSymm hOA_OE)
  exact ⟨c, hreg, hAc, hBc, hCc, hDc, hEc⟩

end Euclid.Book4
