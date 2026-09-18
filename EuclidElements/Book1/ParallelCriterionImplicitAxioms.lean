import EuclidElements.Book1.Proposition16

namespace Euclid.Book1

open Euclid

/-- Incidence data for two lines cut by a transversal at distinct points. -/
structure TransversalSetup (G : Geometry) where
  l : G.Line
  m : G.Line
  t : G.Line
  p : G.Point
  q : G.Point
  a : G.Point
  b : G.Point
  hpq : p ≠ q
  hpl : G.onLine p l
  hpt : G.onLine p t
  hqm : G.onLine q m
  hqt : G.onLine q t
  hal : G.onLine a l
  hbm : G.onLine b m
  hap : a ≠ p
  hbq : b ≠ q
  hat : ¬ G.onLine a t
  hbt : ¬ G.onLine b t

namespace TransversalSetup

def angleAtP (s : TransversalSetup G) : Angle G.Point := ⟨s.a, s.p, s.q⟩
def angleAtQ (s : TransversalSetup G) : Angle G.Point := ⟨s.p, s.q, s.b⟩

end TransversalSetup

/--
Diagrammatic reductions behind I.27-I.28. `meetingForcesAlternateOrder` is the
I.16 consequence obtained after choosing a hypothetical intersection point;
it does not assert parallelism. The other fields are local angle-conversion
facts used in I.28.
-/
class ParallelCriterionImplicitAxioms
    (G : Geometry)
    [AngleSumGeometry G] : Prop where
  meetingForcesAlternateOrder : ∀ (s : TransversalSetup G),
    (¬ G.sameSide s.a s.b s.t) →
    G.LinesMeet s.l s.m →
    G.angleLess s.angleAtP s.angleAtQ ∨
      G.angleLess s.angleAtQ s.angleAtP

  correspondingToAlternate : ∀ (s : TransversalSetup G) (γ : Angle G.Point),
    G.angleCongruent s.angleAtP γ →
    G.angleCongruent γ s.angleAtQ →
    G.angleCongruent s.angleAtP s.angleAtQ

  supplementaryToAlternate : ∀ (s : TransversalSetup G) (γ : Angle G.Point),
    Supplementary G s.angleAtP γ →
    Supplementary G s.angleAtQ γ →
    G.angleCongruent s.angleAtP s.angleAtQ

end Euclid.Book1
