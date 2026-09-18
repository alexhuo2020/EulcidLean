import EuclidElements.Book3.Proposition06

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Euclid III.9 in a construction-neutral form: three noncollinear boundary
    points at one distance from a point force that point to be the center. -/
theorem proposition9
    (G : Geometry)
    [I : ImplicitAxioms G]
    [C : CircleBasicAxioms G]
    [U : CircumcenterUniquenessAxioms G]
    {c : G.Circle} {P A B D : G.Point}
    (htri : IsTriangle G A B D)
    (hA : G.onCircle A c) (hB : G.onCircle B c) (hD : G.onCircle D c)
    (hPA_PB : G.segmentCongruent P A P B)
    (hPA_PD : G.segmentCongruent P A P D) :
    G.isCenter c P := by
  obtain ⟨O, hO⟩ := C.centerExists c
  have hOA_OB : G.segmentCongruent O A O B := C.radiiCongruent hO hA hB
  have hOA_OD : G.segmentCongruent O A O D := C.radiiCongruent hO hA hD
  have hOP : O = P := U.unique htri hOA_OB hOA_OD hPA_PB hPA_PD
  simpa [hOP] using hO

end Euclid.Book3
