import EuclidElements.Book3.Proposition32

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- Geometry-only construction frames for III.33--III.34.  They encode the
    straightedge/compass construction of a tangent/chord carrying a copied
    rectilinear angle; the resulting angle in the circular segment is still
    derived from III.32. -/
class SegmentConstructionAxioms (G : Geometry) : Prop where
  onGivenBase : forall {A B : G.Point} {α : Angle G.Point},
    A ≠ B -> ValidAngle G α ->
    exists c : G.Circle, exists O : G.Point, exists t : G.Line,
      G.isCenter c O ∧ G.onCircle A c ∧ G.onCircle B c ∧
      TangentAt G c t A ∧
      (forall F : G.Point, G.onLine F t ->
        G.angleCongruent ⟨F, A, B⟩ α)

  cutFromGivenCircle : forall {c : G.Circle} {O : G.Point} {α : Angle G.Point},
    G.isCenter c O -> ValidAngle G α ->
    exists B C : G.Point, exists t : G.Line,
      G.onCircle B c ∧ G.onCircle C c ∧ B ≠ C ∧
      TangentAt G c t B ∧
      (forall F : G.Point, G.onLine F t ->
        G.angleCongruent ⟨F, B, C⟩ α)

end Euclid.Book3
