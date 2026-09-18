import EuclidElements.Book3.Proposition19
import EuclidElements.Book1.Proposition32

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/-- A selected arc of circle `c` with ordered endpoints `B,C`. -/
def ArcOn (G : Geometry) (s : ArcRef G) (c : G.Circle)
    (B C : G.Point) : Prop :=
  s.circle = c ∧ s.a = B ∧ s.b = C ∧ ValidArc G s

/-- Basic semantic bridge between selected arcs and central angles. -/
class AngleArcFoundations
    (G : Geometry) [AngleArcGeometry G] : Prop where
  centralStands : forall {s : ArcRef G} {c : G.Circle} {O B C : G.Point},
    ArcOn G s c B C -> G.isCenter c O ->
    StandsOnArc G ⟨B, O, C⟩ s

/-- Pure algebra of synthetic angle addition used by III.20--III.27. -/
class AngleSumAlgebraFoundations
    (G : Geometry)
    [AngleAdditionGeometry G] : Prop where
  resultCongr : forall {α β γ γ' : Angle G.Point},
    AngleSumEq G α β γ -> G.angleCongruent γ γ' ->
    AngleSumEq G α β γ'

  doubleAdd : forall {a b c A B C : Angle G.Point},
    AngleSumEq G a a A -> AngleSumEq G b b B ->
    AngleSumEq G a b c -> AngleSumEq G A B C ->
    AngleSumEq G c c C

  doubleSubtract : forall {a b c A B C : Angle G.Point},
    AngleSumEq G a a A -> AngleSumEq G b b B ->
    AngleSumEq G b c a -> AngleSumEq G B C A ->
    AngleSumEq G c c C

  doubleCancel : forall {a b C : Angle G.Point},
    AngleSumEq G a a C -> AngleSumEq G b b C ->
    G.angleCongruent a b

  doubleCongrResults : forall {a b A B : Angle G.Point},
    G.angleCongruent a b ->
    AngleSumEq G a a A -> AngleSumEq G b b B ->
    G.angleCongruent A B

  doubleCancelCongrResults : forall {a b A B : Angle G.Point},
    AngleSumEq G a a A -> AngleSumEq G b b B ->
    G.angleCongruent A B ->
    G.angleCongruent a b

/-- The two topological cases in Euclid III.20 after the line from the
    circumference point through the center is produced.  The selected arc
    records Euclid's phrase “the same circumference as base.” -/
class InscribedAngleCaseAxioms
    (G : Geometry)
    [AngleInteriorGeometry G]
    [AngleArcGeometry G] : Prop where
  cases : forall
    {s : ArcRef G} {c : G.Circle} {O P B C : G.Point},
    ArcOn G s c B C ->
    StandsOnArc G ⟨B, P, C⟩ s ->
    G.isCenter c O ->
    G.onCircle P c -> G.onCircle B c -> G.onCircle C c ->
    IsTriangle G B P C ->
    (exists D : G.Point,
      G.between P O D ∧
      IsTriangle G B P O ∧ IsTriangle G C P O ∧
      InsideAngle G B P C O ∧
      InsideAngle G B O C D) ∨
    (exists D : G.Point,
      G.between P O D ∧
      IsTriangle G B P O ∧ IsTriangle G C P O ∧
      InsideAngle G O P C B ∧
      InsideAngle G D O C B)

/-- Synthetic “three angles = two right angles” replacement rule used in
    III.22. -/
class TwoRightAngleAlgebraFoundations
    (G : Geometry)
    [AngleSumGeometry G]
    [AngleAdditionGeometry G] : Prop where
  replacePair : forall {α β γ δ : Angle G.Point},
    ThreeAnglesTwoRight G α β γ ->
    AngleSumEq G γ α δ ->
    Supplementary G β δ

end Euclid.Book3
