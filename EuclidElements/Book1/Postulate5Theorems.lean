import EuclidElements.Book1.Proposition28
import EuclidElements.Foundations.Congruence
import EuclidElements.Foundations.Parallel

/-!
# Direct consequences of Euclid's fifth postulate

These lemmas convert a strict alternate-angle inequality into the same-side
interior-angle configuration required by the Euclidean parallel axiom.  Their
geometric dependencies are now exactly incidence, order/separation, congruence,
and the parallel axiom.
-/

namespace Euclid.Book1

open Euclid
open Euclid.Foundations

private theorem noncollinear_arm_transversal
    (G : Geometry)
    [IA : IncidenceAxioms G]
    (s : TransversalSetup G) :
    ¬ G.Collinear s.b s.q s.p := by
  intro hcol
  rcases hcol with ⟨u, hbu, hqu, hpu⟩
  have hqp : s.q ≠ s.p := Ne.symm s.hpq
  have hut : u = s.t := IA.lineUnique hqp hqu hpu s.hqt s.hpt
  exact s.hbt (by simpa [hut] using hbu)

private theorem noncollinear_other_arm_transversal
    (G : Geometry)
    [IA : IncidenceAxioms G]
    (s : TransversalSetup G) :
    ¬ G.Collinear s.a s.p s.q := by
  intro hcol
  rcases hcol with ⟨u, hau, hpu, hqu⟩
  have hup : s.p ≠ s.q := s.hpq
  have hut : u = s.t := IA.lineUnique hup hpu hqu s.hpt s.hqt
  exact s.hat (by simpa [hut] using hau)

/-- Strict inequality at the first crossing forces the two lines to meet. -/
theorem strictAtPForcesMeet
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
    (hlt : G.angleLess s.angleAtP s.angleAtQ) :
    G.LinesMeet s.l s.m := by
  obtain ⟨b', hbb', hb'm, hside⟩ := O.oppositeCompanionAtQ s hopposite
  have hnoncol : ¬ G.Collinear s.b s.q s.p :=
    noncollinear_arm_transversal G s
  have hsupp0 : Supplementary G ⟨s.b, s.q, s.p⟩ ⟨s.p, s.q, b'⟩ :=
    AI.linearPairSupplementary hbb' hnoncol
  have hsupp : Supplementary G ⟨s.p, s.q, b'⟩ ⟨s.b, s.q, s.p⟩ :=
    AI.supplementarySymm hsupp0
  have hrev : G.angleCongruent s.angleAtQ ⟨s.b, s.q, s.p⟩ :=
    C.angleReverse s.p s.q s.b
  have hlt' : G.angleLess s.angleAtP ⟨s.b, s.q, s.p⟩ :=
    AO.lt_congr_right hrev hlt
  have hsum : G.sumLessThanTwoRight s.angleAtP ⟨s.p, s.q, b'⟩ :=
    AI.twoAnglesLtTwoRight hsupp hlt'
  have hbq' : b' ≠ s.q := Ne.symm (O.betweenDistinct hbb').2.1
  obtain ⟨x, hxl, hxm, _⟩ :=
    E5.postulate5 s.l s.m s.t s.p s.q s.a b'
      s.hpq s.hpl s.hpt s.hqm s.hqt s.hal hb'm s.hap hbq' hside hsum
  exact ⟨x, hxl, hxm⟩

/-- Strict inequality at the second crossing forces the two lines to meet. -/
theorem strictAtQForcesMeet
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
    (hgt : G.angleLess s.angleAtQ s.angleAtP) :
    G.LinesMeet s.l s.m := by
  obtain ⟨a', haa', ha'l, hside⟩ := O.oppositeCompanionAtP s hopposite
  have hnoncol : ¬ G.Collinear s.a s.p s.q :=
    noncollinear_other_arm_transversal G s
  have hsupp0 : Supplementary G ⟨s.a, s.p, s.q⟩ ⟨s.q, s.p, a'⟩ :=
    AI.linearPairSupplementary haa' hnoncol
  have hsupp : Supplementary G ⟨s.q, s.p, a'⟩ s.angleAtP :=
    AI.supplementarySymm hsupp0
  have hrev : G.angleCongruent s.angleAtQ ⟨s.b, s.q, s.p⟩ :=
    C.angleReverse s.p s.q s.b
  have hgt' : G.angleLess ⟨s.b, s.q, s.p⟩ s.angleAtP :=
    AO.lt_congr_left hrev hgt
  have hsum : G.sumLessThanTwoRight ⟨s.b, s.q, s.p⟩ ⟨s.q, s.p, a'⟩ :=
    AI.twoAnglesLtTwoRight hsupp hgt'
  have hap' : a' ≠ s.p := Ne.symm (O.betweenDistinct haa').2.1
  obtain ⟨x, hxm, hxl, _⟩ :=
    E5.postulate5 s.m s.l s.t s.q s.p s.b a'
      (Ne.symm s.hpq) s.hqm s.hqt s.hpl s.hpt s.hbm ha'l s.hbq hap' hside hsum
  exact ⟨x, hxl, hxm⟩

end Euclid.Book1
