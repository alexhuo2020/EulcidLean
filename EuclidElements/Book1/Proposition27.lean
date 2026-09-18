import EuclidElements.Book1.ParallelCriterionTheorems

/-!
# Euclid I.27 -- equal alternate interior angles imply parallel lines

The only background geometry beyond the earlier propositions is the reusable
plane-separation/order layer.  No proposition-specific I.27 schema is assumed.
-/

namespace Euclid.Book1

open Euclid

theorem proposition27
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleSumGeometry G]
    [AngleInteriorGeometry G]
    [TriangleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AI : AngleImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [P16 : Proposition16ImplicitAxioms G]
    [S : PlaneSeparationAxioms G]
    (s : TransversalSetup G)
    (hlm : s.l ≠ s.m)
    (hopposite : ¬ G.sameSide s.a s.b s.t)
    (halt : G.angleCongruent s.angleAtP s.angleAtQ) :
    Parallel G s.l s.m := by
  refine ⟨hlm, ?_⟩
  intro hmeet
  rcases meetingForcesAlternateOrder G s hopposite hmeet with hlt | hgt
  · exact (AO.lt_not_congr hlt) halt
  · exact (AO.lt_not_congr hgt) (I.angleSymm halt)

end Euclid.Book1
