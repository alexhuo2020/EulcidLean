import EuclidElements.Book1.Proposition27

/-!
# Euclid I.28 -- two further criteria for parallel lines
-/

namespace Euclid.Book1

open Euclid

theorem proposition28_corresponding
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
    (γ : Angle G.Point)
    (hPγ : G.angleCongruent s.angleAtP γ)
    (hγQ : G.angleCongruent γ s.angleAtQ) :
    Parallel G s.l s.m := by
  have halt : G.angleCongruent s.angleAtP s.angleAtQ :=
    I.angleTrans hPγ hγQ
  exact proposition27 G s hlm hopposite halt

/-- I.28, same-side interior angles equal to two right angles. -/
theorem proposition28_supplementary
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
    (γ : Angle G.Point)
    (hP : Supplementary G s.angleAtP γ)
    (hQ : Supplementary G s.angleAtQ γ) :
    Parallel G s.l s.m := by
  have hγP : Supplementary G γ s.angleAtP := AI.supplementarySymm hP
  have hγQ : Supplementary G γ s.angleAtQ := AI.supplementarySymm hQ
  have halt : G.angleCongruent s.angleAtP s.angleAtQ :=
    AI.equalSupplements hγP hγQ
  exact proposition27 G s hlm hopposite halt

end Euclid.Book1
