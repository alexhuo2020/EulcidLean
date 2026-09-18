import EuclidElements.Book1.Proposition23

/-!
# Generic copied-angle / marked-ray construction

This is a reusable construction interface for placing a copied larger angle and
marking a prescribed length on its new ray.  It deliberately does *not* assume
the hinge-theorem comparison of the final sides.
-/

namespace Euclid.Book1

open Euclid

class AngleRayConstructionAxioms
    (G : Geometry)
    [AngleInteriorGeometry G] : Prop where
  copiedGreaterAngleWithMarkedRay : ∀ {A B C D E F : G.Point},
    IsTriangle G A B C → IsTriangle G D E F →
    G.angleLess ⟨E, D, F⟩ ⟨B, A, C⟩ →
    ∃ Gp : G.Point,
      IsTriangle G D E Gp ∧
      IsTriangle G D F Gp ∧
      IsTriangle G E F Gp ∧
      G.segmentCongruent D Gp D F ∧
      G.angleCongruent ⟨E, D, Gp⟩ ⟨B, A, C⟩ ∧
      InsideAngle G E F Gp D ∧
      InsideAngle G D Gp F E

end Euclid.Book1
