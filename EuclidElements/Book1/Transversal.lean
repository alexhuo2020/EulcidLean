import EuclidElements.Book1.ExtendedLanguage

/-!
# Transversal configurations

Reusable incidence data for two lines cut by a transversal.  This file contains
no Euclidean parallel assumption and no proposition-specific conclusion.
-/

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

end Euclid.Book1
