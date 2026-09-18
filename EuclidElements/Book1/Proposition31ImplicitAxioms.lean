import EuclidElements.Book1.Proposition23
import EuclidElements.Book1.Proposition27

namespace Euclid.Book1

open Euclid

/--
Construction data behind I.31: after choosing a point on the given line and
joining it to the external point, I.23 copies the alternate angle and P1 draws
the candidate line.  This class returns only that construction/angle witness;
parallelism is still proved by I.27.
-/
class Proposition31ImplicitAxioms
    (G : Geometry)
    [AngleSumGeometry G] : Prop where
  copiedAlternateLine : ∀ {l : G.Line} {A : G.Point},
    (¬ G.onLine A l) →
    ∃ m : G.Line, ∃ s : TransversalSetup G,
      s.l = l ∧ s.m = m ∧
      G.onLine A m ∧
      l ≠ m ∧
      (¬ G.sameSide s.a s.b s.t) ∧
      G.angleCongruent s.angleAtP s.angleAtQ

end Euclid.Book1
