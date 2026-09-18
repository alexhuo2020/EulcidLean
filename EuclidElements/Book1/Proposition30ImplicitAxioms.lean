import EuclidElements.Book1.Proposition29

namespace Euclid.Book1

open Euclid

/-- Diagram construction used in I.30: a common transversal transfers the two
I.29 angle equalities to an alternate-angle equality for the outer pair. -/
class Proposition30ImplicitAxioms
    (G : Geometry)
    [AngleSumGeometry G] : Prop where
  outerAlternateWitness : ∀ {l m n : G.Line},
    Parallel G l m → Parallel G n m → l ≠ n →
    ∃ s : TransversalSetup G,
      s.l = l ∧ s.m = n ∧
      (¬ G.sameSide s.a s.b s.t) ∧
      G.angleCongruent s.angleAtP s.angleAtQ

end Euclid.Book1
