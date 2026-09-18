import EuclidElements.Book1.Proposition29

namespace Euclid.Book1

open Euclid

/-- Local incidence/angle data for the standard I.33 quadrilateral diagram. -/
class Proposition33ImplicitAxioms
    (G : Geometry)
    [AngleSumGeometry G] : Prop where
  diagram : ∀ {A B C D : G.Point} {lAB lCD lAC lBD : G.Line},
    G.onLine A lAB → G.onLine B lAB →
    G.onLine C lCD → G.onLine D lCD →
    Parallel G lAB lCD →
    G.onLine A lAC → G.onLine C lAC →
    G.onLine B lBD → G.onLine D lBD →
    ∃ s : TransversalSetup G,
      IsTriangle G A B C ∧
      IsTriangle G D C B ∧
      G.angleCongruent ⟨A, B, C⟩ ⟨D, C, B⟩ ∧
      s.l = lAC ∧ s.m = lBD ∧
      lAC ≠ lBD ∧
      (¬ G.sameSide s.a s.b s.t) ∧
      (G.angleCongruent ⟨A, C, B⟩ ⟨C, B, D⟩ →
        G.angleCongruent s.angleAtP s.angleAtQ)

end Euclid.Book1
