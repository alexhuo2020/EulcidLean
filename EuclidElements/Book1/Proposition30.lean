import EuclidElements.Book1.Proposition27
import EuclidElements.Book1.Proposition30ImplicitAxioms

/-!
# Euclid I.30 -- lines parallel to the same line are parallel to one another
-/

namespace Euclid.Book1

open Euclid

theorem proposition30
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AI : AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [P16 : Proposition16ImplicitAxioms G]
    [S : PlaneSeparationAxioms G]
    [P30 : Proposition30ImplicitAxioms G]
    {l m n : G.Line}
    (hlm : Parallel G l m)
    (hnm : Parallel G n m)
    (hln : l ≠ n) :
    Parallel G l n := by
  obtain ⟨s, hsl, hsn, hopp, halt⟩ := P30.outerAlternateWitness hlm hnm hln
  subst hsl
  subst hsn
  exact proposition27 G s hln hopp halt

end Euclid.Book1
