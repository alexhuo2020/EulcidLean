import EuclidElements.Book4.SquareConstructionFoundations

namespace Euclid.Book4

open Euclid
open Euclid.Book1

/-- Euclid IV.9: circumscribe a circle about a given square. -/
theorem proposition9
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [S : SquareBook4ConstructionAxioms G]
    {A B C D : G.Point}
    (hsq : Square G A B C D) :
    ∃ c : G.Circle, CircleCircumscribedAboutSquare G c A B C D := by
  obtain ⟨O, hOA, hOA_OB, hOA_OC, hOA_OD⟩ := S.circumcenterFrame hsq
  obtain ⟨c, hcenter, hAc, hcircle⟩ := P.postulate3 O A hOA
  have hBc : G.onCircle B c := (hcircle B).2 (I.segmentSymm hOA_OB)
  have hCc : G.onCircle C c := (hcircle C).2 (I.segmentSymm hOA_OC)
  have hDc : G.onCircle D c := (hcircle D).2 (I.segmentSymm hOA_OD)
  exact ⟨c, hsq, hAc, hBc, hCc, hDc⟩

end Euclid.Book4
