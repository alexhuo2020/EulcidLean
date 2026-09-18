import EuclidElements.Book3.Proposition29

namespace Euclid.Book3

open Euclid

/-- Euclid III.30: bisect a given selected circumference. -/
theorem proposition30
    (G : Geometry)
    [ArcGeometry G]
    [AC : ArcCentralAngleFoundations G]
    [CC : ChordCentralAngleFoundations G]
    [BIS : ArcBisectionConstructionAxioms G]
    [C0 : CircleBasicAxioms G]
    {s : ArcRef G}
    (hs : ValidArc G s) :
    exists D : G.Point, exists left right : ArcRef G,
      ArcOn G left s.circle s.a D ∧
      ArcOn G right s.circle D s.b ∧
      ArcEq G left right := by
  obtain ⟨D, left, right, hDA, hDB, hD, hleft, hright, hAD_DB⟩ := BIS.construct hs
  obtain ⟨O, hO⟩ := C0.centerExists s.circle
  have hEqCircle : EqualCircles G s.circle s.circle := by
    intro O1 O2 A B hO1 hO2 hA hB
    have hOO : O1 = O2 := C0.centerUnique hO1 hO2
    subst O2
    exact C0.radiiCongruent hO1 hA hB
  have hAon : G.onCircle s.a s.circle := hs.2.2.2.1
  have hBon : G.onCircle s.b s.circle := hs.2.2.2.2.1
  have hChordAD : Chord G s.circle s.a D :=
    ⟨Ne.symm hDA, hAon, hD⟩
  have hChordDB : Chord G s.circle D s.b :=
    ⟨hDB, hD, hBon⟩
  have hang := CC.equalChordGivesCentralAngle hEqCircle hO hO hChordAD hChordDB hAD_DB
  have harc := proposition26_center G hEqCircle hO hO hleft hright hang
  exact ⟨D, left, right, hleft, hright, harc⟩

end Euclid.Book3
