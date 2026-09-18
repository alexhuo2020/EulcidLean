import EuclidElements.Book3.Proposition20

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Euclid III.21: angles in the same segment are equal.  The selected arc
    makes "same segment" explicit rather than inferring it from the chord alone. -/
theorem proposition21
    (G : Geometry)
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleInteriorGeometry G]
    [AngleSumGeometry G]
    [AngleAdditionGeometry G]
    [AngleArcGeometry G]
    [AI : AngleImplicitAxioms G]
    [AA : AngleAdditionImplicitAxioms G]
    [P32 : Proposition32ImplicitAxioms G]
    [C : CircleBasicAxioms G]
    [CA : InscribedAngleCaseAxioms G]
    [ALG : AngleSumAlgebraFoundations G]
    {s : ArcRef G} {c : G.Circle} {B Cpt P Q : G.Point}
    (hArc : ArcOn G s c B Cpt)
    (hPstand : StandsOnArc G ⟨B, P, Cpt⟩ s)
    (hQstand : StandsOnArc G ⟨B, Q, Cpt⟩ s)
    (hP : G.onCircle P c)
    (hQ : G.onCircle Q c)
    (hB : G.onCircle B c)
    (hC : G.onCircle Cpt c)
    (htriP : IsTriangle G B P Cpt)
    (htriQ : IsTriangle G B Q Cpt) :
    G.angleCongruent ⟨B, P, Cpt⟩ ⟨B, Q, Cpt⟩ := by
  obtain ⟨O, hO⟩ := C.centerExists c
  have h20P := proposition20 G hArc hPstand hO hP hB hC htriP
  have h20Q := proposition20 G hArc hQstand hO hQ hB hC htriQ
  exact ALG.doubleCancel h20P h20Q

end Euclid.Book3
