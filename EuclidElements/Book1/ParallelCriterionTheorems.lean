import EuclidElements.Book1.Proposition16
import EuclidElements.Book1.PlaneSeparationAxioms

/-!
# Neutral-geometry transversal lemmas

The key I.27 diagram reduction is proved here from I.16 plus the generic
plane-separation/order layer.  It is no longer an assumption named after a
Euclid proposition.
-/

namespace Euclid.Book1

open Euclid

/-- If the cut lines actually meet, opposite-side alternate angles cannot be equal. -/
theorem meetingForcesAlternateOrder
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
    (hopposite : ¬ G.sameSide s.a s.b s.t)
    (hmeet : G.LinesMeet s.l s.m) :
    G.angleLess s.angleAtP s.angleAtQ ∨
      G.angleLess s.angleAtQ s.angleAtP := by
  obtain ⟨x, hcase | hcase⟩ := S.meetingRayCases s hopposite hmeet
  · rcases hcase with ⟨htri, hray, hxb⟩
    have hext := proposition16 G htri hxb
    have hxpq_qb : G.angleLess ⟨x, s.p, s.q⟩ ⟨s.p, s.q, s.b⟩ := hext.1
    have hap_xpq : G.angleCongruent s.angleAtP ⟨x, s.p, s.q⟩ :=
      L.angleSameRayLeft hray
    have hxpq_ap : G.angleCongruent ⟨x, s.p, s.q⟩ s.angleAtP :=
      I.angleSymm hap_xpq
    exact Or.inl (AO.lt_congr_left hxpq_ap hxpq_qb)
  · rcases hcase with ⟨htri, hray, hxa⟩
    have hext := proposition16 G htri hxa
    have hxqp_qpa : G.angleLess ⟨x, s.q, s.p⟩ ⟨s.q, s.p, s.a⟩ := hext.1
    have hbqp_xqp : G.angleCongruent ⟨s.b, s.q, s.p⟩ ⟨x, s.q, s.p⟩ :=
      L.angleSameRayLeft hray
    have hqpb_bqp : G.angleCongruent s.angleAtQ ⟨s.b, s.q, s.p⟩ :=
      L.angleReverse s.p s.q s.b
    have hqpb_xqp : G.angleCongruent s.angleAtQ ⟨x, s.q, s.p⟩ :=
      I.angleTrans hqpb_bqp hbqp_xqp
    have hxqp_qpb : G.angleCongruent ⟨x, s.q, s.p⟩ s.angleAtQ :=
      I.angleSymm hqpb_xqp
    have hqpa_apq : G.angleCongruent ⟨s.q, s.p, s.a⟩ s.angleAtP :=
      L.angleReverse s.q s.p s.a
    have h1 : G.angleLess s.angleAtQ ⟨s.q, s.p, s.a⟩ :=
      AO.lt_congr_left hxqp_qpb hxqp_qpa
    exact Or.inr (AO.lt_congr_right hqpa_apq h1)

end Euclid.Book1
