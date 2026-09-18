import EuclidElements.Book1.Postulate5Theorems

/-!
# Euclid I.29 -- a transversal of parallel lines

This is the first Book I proposition whose proof depends on the Euclidean
parallel axiom.  The alternate-angle statement explicitly requires the selected
arms to lie on opposite sides of the transversal.
-/

namespace Euclid.Book1

open Euclid
open Euclid.Foundations

theorem proposition29_alternate
    (G : Geometry)
    [E5 : EuclideanParallelAxiom G]
    [IA : IncidenceAxioms G]
    [O : OrderAxioms G]
    [C : CongruenceAxioms G]
    [AngleSumGeometry G]
    [AI : AngleImplicitAxioms G]
    [AngleInteriorGeometry G]
    [AO : AngleOrderImplicitAxioms G]
    (s : TransversalSetup G)
    (hopposite : ¬ G.sameSide s.a s.b s.t)
    (hpar : Parallel G s.l s.m) :
    G.angleCongruent s.angleAtP s.angleAtQ := by
  rcases AO.angleTrichotomy s.angleAtP s.angleAtQ with heq | hlt | hgt
  · exact heq
  · have hmeet : G.LinesMeet s.l s.m :=
      strictAtPForcesMeet G s hopposite hlt
    exact False.elim (hpar.2 hmeet)
  · have hmeet : G.LinesMeet s.l s.m :=
      strictAtQForcesMeet G s hopposite hgt
    exact False.elim (hpar.2 hmeet)

/-- I.29: corresponding/exterior angles obtained from the alternate-angle part. -/
theorem proposition29_corresponding
    (G : Geometry)
    [E5 : EuclideanParallelAxiom G]
    [IA : IncidenceAxioms G]
    [O : OrderAxioms G]
    [C : CongruenceAxioms G]
    [AngleSumGeometry G]
    [AI : AngleImplicitAxioms G]
    [AngleInteriorGeometry G]
    [AO : AngleOrderImplicitAxioms G]
    (s : TransversalSetup G)
    (hopposite : ¬ G.sameSide s.a s.b s.t)
    (hpar : Parallel G s.l s.m)
    (γ δ : Angle G.Point)
    (hγ : G.angleCongruent γ s.angleAtP)
    (hδ : G.angleCongruent s.angleAtQ δ) :
    G.angleCongruent γ δ := by
  have halt := proposition29_alternate G s hopposite hpar
  exact C.angleTrans (C.angleTrans hγ halt) hδ

/-- I.29: interior angles on the same side are supplementary. -/
theorem proposition29_sameSide
    (G : Geometry)
    [E5 : EuclideanParallelAxiom G]
    [IA : IncidenceAxioms G]
    [O : OrderAxioms G]
    [C : CongruenceAxioms G]
    [AngleSumGeometry G]
    [AI : AngleImplicitAxioms G]
    [AngleInteriorGeometry G]
    [AO : AngleOrderImplicitAxioms G]
    (s : TransversalSetup G)
    (hopposite : ¬ G.sameSide s.a s.b s.t)
    (hpar : Parallel G s.l s.m)
    (γ : Angle G.Point)
    (hsupp : Supplementary G s.angleAtP γ) :
    Supplementary G s.angleAtQ γ := by
  have halt := proposition29_alternate G s hopposite hpar
  exact AI.supplementaryCongrLeft halt hsupp

end Euclid.Book1
