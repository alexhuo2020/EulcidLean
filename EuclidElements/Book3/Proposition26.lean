import EuclidElements.Book3.ArcChordFoundations
import EuclidElements.Book3.Proposition20

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Euclid III.26, central-angle form: equal central angles in equal circles
    stand on equal selected arcs. -/
theorem proposition26_center
    (G : Geometry)
    [ArcGeometry G]
    [AC : ArcCentralAngleFoundations G]
    {c d : G.Circle} {O P A B C D : G.Point}
    {s t : ArcRef G}
    (heqCircles : EqualCircles G c d)
    (hO : G.isCenter c O) (hP : G.isCenter d P)
    (hs : ArcOn G s c A B) (ht : ArcOn G t d C D)
    (hang : G.angleCongruent ⟨A, O, B⟩ ⟨C, P, D⟩) :
    ArcEq G s t :=
  (AC.eqIffCentral heqCircles hO hP hs ht).2 hang

/-- Euclid III.26, circumference-angle form. -/
theorem proposition26_circumference
    (G : Geometry)
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    [AngleInteriorGeometry G]
    [AngleSumGeometry G]
    [AngleAdditionGeometry G]
    [AngleArcGeometry G]
    [ArcGeometry G]
    [AI : AngleImplicitAxioms G]
    [AA : AngleAdditionImplicitAxioms G]
    [P32 : Proposition32ImplicitAxioms G]
    [C0 : CircleBasicAxioms G]
    [CA : InscribedAngleCaseAxioms G]
    [ALG : AngleSumAlgebraFoundations G]
    [AC : ArcCentralAngleFoundations G]
    {s t : ArcRef G} {c d : G.Circle}
    {O P A B C D X Y : G.Point}
    (heqCircles : EqualCircles G c d)
    (hs : ArcOn G s c A B) (ht : ArcOn G t d C D)
    (hXs : StandsOnArc G ⟨A, X, B⟩ s)
    (hYt : StandsOnArc G ⟨C, Y, D⟩ t)
    (hO : G.isCenter c O) (hP : G.isCenter d P)
    (hX : G.onCircle X c) (hY : G.onCircle Y d)
    (hA : G.onCircle A c) (hB : G.onCircle B c)
    (hC : G.onCircle C d) (hD : G.onCircle D d)
    (htriX : IsTriangle G A X B)
    (htriY : IsTriangle G C Y D)
    (hang : G.angleCongruent ⟨A, X, B⟩ ⟨C, Y, D⟩) :
    ArcEq G s t := by
  have h20X := proposition20 G hs hXs hO hX hA hB htriX
  have h20Y := proposition20 G ht hYt hP hY hC hD htriY
  have hcentral : G.angleCongruent ⟨A, O, B⟩ ⟨C, P, D⟩ :=
    ALG.doubleCongrResults hang h20X h20Y
  exact proposition26_center G heqCircles hO hP hs ht hcentral

end Euclid.Book3
