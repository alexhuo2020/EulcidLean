import EuclidElements.Book1.Proposition04

/-!
# Euclid I.5 -- base angles of an isosceles triangle
-/

namespace Euclid.Book1

open Euclid

theorem proposition5_baseAngles
    (G : Geometry)
    [I : ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [L : LaterImplicitAxioms G]
    {A B C : G.Point}
    (htri : IsTriangle G A B C)
    (hiso : G.segmentCongruent A B A C) :
    G.angleCongruent ⟨A, B, C⟩ ⟨B, C, A⟩ := by
  have htri' : IsTriangle G A C B := by
    refine ⟨Ne.symm htri.2.2.1, Ne.symm htri.2.1, Ne.symm htri.1, ?_⟩
    intro hcol
    rcases hcol with ⟨l, hAl, hCl, hBl⟩
    exact htri.2.2.2 ⟨l, hAl, hBl, hCl⟩
  have hAC_AB : G.segmentCongruent A C A B := I.segmentSymm hiso
  have hangle : G.angleCongruent ⟨B, A, C⟩ ⟨C, A, B⟩ :=
    L.angleReverse B A C
  have hsas := proposition4 G htri htri' hiso hAC_AB hangle
  have hACB_BCA : G.angleCongruent ⟨A, C, B⟩ ⟨B, C, A⟩ :=
    L.angleReverse A C B
  exact I.angleTrans hsas.2.1 hACB_BCA

end Euclid.Book1
