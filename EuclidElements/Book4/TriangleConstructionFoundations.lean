import EuclidElements.Book4.Proposition01
import EuclidElements.Book3.Proposition16

namespace Euclid.Book4

open Euclid
open Euclid.Book1
open Euclid.Book3

/-- Synthetic form of the standard consequence of I.32: if two angles of two
    triangles are pairwise congruent, the remaining angles are congruent. -/
class ThirdAngleCongruenceAxioms (G : Geometry) : Prop where
  third : forall {A B C D E F : G.Point},
    IsTriangle G A B C -> IsTriangle G D E F ->
    G.angleCongruent ⟨A, B, C⟩ ⟨D, E, F⟩ ->
    G.angleCongruent ⟨A, C, B⟩ ⟨D, F, E⟩ ->
    G.angleCongruent ⟨B, A, C⟩ ⟨E, D, F⟩

/-- Diagram/construction data for IV.2--IV.5.  No numbered conclusion occurs
    as a field. -/
class TriangleBook4ConstructionAxioms (G : Geometry) : Prop where
  inscribedFrame : forall {c : G.Circle} {D E F : G.Point},
    IsTriangle G D E F ->
    ∃ A B C : G.Point,
      IsTriangle G A B C ∧
      G.onCircle A c ∧ G.onCircle B c ∧ G.onCircle C c ∧
      G.angleCongruent ⟨A, B, C⟩ ⟨D, E, F⟩ ∧
      G.angleCongruent ⟨A, C, B⟩ ⟨D, F, E⟩

  circumscribedFrame : forall {c : G.Circle} {D E F : G.Point},
    IsTriangle G D E F ->
    ∃ A B C : G.Point, ∃ lAB lBC lCA : G.Line, ∃ T U V : G.Point,
      IsTriangle G A B C ∧
      SideLine G A B lAB ∧ SideLine G B C lBC ∧ SideLine G C A lCA ∧
      TangentAt G c lAB T ∧ TangentAt G c lBC U ∧ TangentAt G c lCA V ∧
      G.angleCongruent ⟨A, B, C⟩ ⟨D, E, F⟩ ∧
      G.angleCongruent ⟨A, C, B⟩ ⟨D, F, E⟩

  incircleFrame : forall {A B C : G.Point},
    IsTriangle G A B C ->
    ∃ D E F H : G.Point,
    ∃ lAB lBC lCA rE rF rH : G.Line,
      SideLine G A B lAB ∧ SideLine G B C lBC ∧ SideLine G C A lCA ∧
      G.onLine E lAB ∧ G.onLine F lBC ∧ G.onLine H lCA ∧
      G.onLine D rE ∧ G.onLine E rE ∧ Perpendicular G rE lAB ∧
      G.onLine D rF ∧ G.onLine F rF ∧ Perpendicular G rF lBC ∧
      G.onLine D rH ∧ G.onLine H rH ∧ Perpendicular G rH lCA ∧
      D ≠ E ∧ D ≠ F ∧ D ≠ H ∧
      G.segmentCongruent D E D F ∧ G.segmentCongruent D E D H

  circumcenterFrame : forall {A B C : G.Point},
    IsTriangle G A B C ->
    ∃ O : G.Point,
      O ≠ A ∧
      G.segmentCongruent O A O B ∧ G.segmentCongruent O A O C

end Euclid.Book4
