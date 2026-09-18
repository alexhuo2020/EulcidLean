import EuclidElements.Book1.AreaFoundations
import EuclidElements.Book1.AreaDiagramGeometry

/-!
# Geometry-only construction frames for Euclid's equal-figure constructions

These classes return incidence/congruence/parallel/complement data only; no
field asserts an equal-area conclusion.
-/

namespace Euclid.Book1

open Euclid

class AreaTriangleConstructionAxioms
    (G : Geometry) : Prop where
  /-- Geometry behind I.42. -/
  triangleParallelogramFrame : ∀
    {A B C : G.Point} {α : Angle G.Point},
    IsTriangle G A B C → ValidAngle G α →
    ∃ M D E F H : G.Point, ∃ base top : G.Line,
      IsMidpoint G M B C ∧
      IsTriangle G A M C ∧
      Parallelogram G D E F H ∧
      IsTriangle G D E F ∧
      G.segmentCongruent M C E F ∧
      G.onLine M base ∧ G.onLine C base ∧
      G.onLine E base ∧ G.onLine F base ∧
      G.onLine A top ∧ G.onLine D top ∧
      Parallel G base top ∧
      G.angleCongruent ⟨H, D, E⟩ α

class AreaApplicationConstructionAxioms
    (G : Geometry)
    [AreaDiagramGeometry G] : Prop where
  /-- Geometry behind I.44. -/
  applyParallelogramFrame : ∀
    {A B P Q R S : G.Point} {α : Angle G.Point},
    A ≠ B →
    Parallelogram G P Q R S →
    ValidAngle G α →
    G.angleCongruent ⟨S, P, Q⟩ α →
    ∃ F H : G.Point,
      Parallelogram G A B F H ∧
      ComplementsAboutDiagonal G P Q R S A B F H ∧
      G.angleCongruent ⟨H, A, B⟩ α

end Euclid.Book1
