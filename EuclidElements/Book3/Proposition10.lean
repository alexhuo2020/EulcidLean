import EuclidElements.Book3.Proposition09
import EuclidElements.Book3.Proposition02

namespace Euclid.Book3

open Euclid
open Euclid.Book1

private theorem three_circle_points_triangle
    (G : Geometry)
    [CircleOrderGeometry G]
    [CV : CircleConvexityAxioms G]
    [POS : CirclePositionAxioms G]
    [CO : CollinearOrderAxioms G]
    {c : G.Circle} {A B C : G.Point}
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A)
    (hA : G.onCircle A c) (hB : G.onCircle B c) (hC : G.onCircle C c) :
    IsTriangle G A B C := by
  refine ⟨hAB, hBC, hCA, ?_⟩
  intro hcol
  rcases CO.oneBetween hcol hAB hBC hCA with hABC | hBAC | hACB
  · have hin := CV.betweenChordEndpointsInside hA hC hABC
    exact POS.insideNotBoundary hin hB
  · have hin := CV.betweenChordEndpointsInside hB hC hBAC
    exact POS.insideNotBoundary hin hA
  · have hin := CV.betweenChordEndpointsInside hA hB hACB
    exact POS.insideNotBoundary hin hC

/-- Euclid III.10: two distinct circles cannot have three distinct common
    points. -/
theorem proposition10
    (G : Geometry)
    [I : ImplicitAxioms G]
    [CircleOrderGeometry G]
    [CB : CircleBasicAxioms G]
    [E : CircleExtensionalityAxioms G]
    [U : CircumcenterUniquenessAxioms G]
    [CV : CircleConvexityAxioms G]
    [POS : CirclePositionAxioms G]
    [CO : CollinearOrderAxioms G]
    {c d : G.Circle} {A B C : G.Point}
    (hneq : c ≠ d)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A)
    (hAc : G.onCircle A c) (hBc : G.onCircle B c) (hCc : G.onCircle C c)
    (hAd : G.onCircle A d) (hBd : G.onCircle B d) (hCd : G.onCircle C d) : False := by
  have htri : IsTriangle G A B C :=
    three_circle_points_triangle G hAB hBC hCA hAc hBc hCc
  obtain ⟨O, hOc⟩ := CB.centerExists c
  obtain ⟨P, hPd⟩ := CB.centerExists d
  have hOA_OB := CB.radiiCongruent hOc hAc hBc
  have hOA_OC := CB.radiiCongruent hOc hAc hCc
  have hPA_PB := CB.radiiCongruent hPd hAd hBd
  have hPA_PC := CB.radiiCongruent hPd hAd hCd
  have hOP : O = P := U.unique htri hOA_OB hOA_OC hPA_PB hPA_PC
  subst P
  have hcut : CirclesCutAt G c d A B :=
    ⟨hAB, hAc, hAd, hBc, hBd⟩
  exact proposition5 G hcut hneq hOc hPd

end Euclid.Book3
