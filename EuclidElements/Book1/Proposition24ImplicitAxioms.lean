import EuclidElements.Book1.Proposition23

namespace Euclid.Book1

open Euclid

/--
Diagrammatic construction facts used in Euclid I.24.  This does not assume the
hinge conclusion.  It only packages the auxiliary point G in Euclid's diagram:
DG is copied from DF, EDG is the larger included angle, and the resulting
triangle EFG has angle EGF smaller than EFG.
-/
class Proposition24ImplicitAxioms
    (G : Geometry)
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleInteriorGeometry G] : Prop where
  hingeAuxiliary : ∀ {A B C D E F : G.Point},
    IsTriangle G A B C → IsTriangle G D E F →
    G.segmentCongruent A B D E →
    G.segmentCongruent A C D F →
    G.angleLess ⟨E, D, F⟩ ⟨B, A, C⟩ →
    ∃ Gp : G.Point,
      IsTriangle G D E Gp ∧
      IsTriangle G E F Gp ∧
      G.segmentCongruent D Gp D F ∧
      G.angleCongruent ⟨E, D, Gp⟩ ⟨B, A, C⟩ ∧
      G.angleLess ⟨E, Gp, F⟩ ⟨E, F, Gp⟩

end Euclid.Book1
