import EuclidElements.Book1.Proposition42
import EuclidElements.Book1.PolygonAreaFoundations

/-!
# Euclid I.45 -- construct a parallelogram equal to a rectilinear figure

The rectilinear figure carries explicit triangulation evidence.  The proof is
an induction over its nonempty list of triangular pieces, applying I.42 to each
piece and combining successive equal parallelograms in the prescribed angle.
-/

namespace Euclid.Book1

open Euclid

private theorem proposition45_pieces
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [D34 : Proposition34ImplicitAxioms G]
    [LaterAreaGeometry G]
    [AF : AreaFoundations G]
    [AT : AreaTriangleConstructionAxioms G]
    [PC : ParallelogramCompositionAxioms G]
    (pieces : List (TrianglePiece G))
    (hne : pieces ≠ [])
    {α : Angle G.Point}
    (hang : ValidAngle G α) :
    ∃ A B C D : G.Point,
      Parallelogram G A B C D ∧
      TriangleListQuadAreaEq G pieces A B C D ∧
      G.angleCongruent ⟨D, A, B⟩ α := by
  induction pieces with
  | nil => exact False.elim (hne rfl)
  | cons t ts ih =>
      by_cases hts : ts = []
      · subst ts
        obtain ⟨A, B, C, D, hpara, heq, hangle⟩ :=
          proposition42 G t.valid hang
        exact ⟨A, B, C, D, hpara,
          TriangleListQuadAreaEq.single heq, hangle⟩
      · obtain ⟨A1, B1, C1, D1, hpara1, heq1, hangle1⟩ :=
          proposition42 G t.valid hang
        obtain ⟨A2, B2, C2, D2, hpara2, heq2, hangle2⟩ := ih hts
        obtain ⟨A, B, C, D, hpara, hangle, hsum⟩ :=
          PC.combineSameAngle hpara1 hpara2 hangle1 hangle2
        exact ⟨A, B, C, D, hpara,
          TriangleListQuadAreaEq.cons heq1 heq2 hsum, hangle⟩

/-- I.45 with the rectilinear-figure hypothesis made explicit. -/
theorem proposition45
    (G : Geometry)
    [P : Postulates G]
    [I : ImplicitAxioms G]
    [I2 : Proposition2ImplicitAxioms G]
    [SegmentOrder G]
    [TriangleAreaGeometry G]
    [AngleInteriorGeometry G]
    [L : LaterImplicitAxioms G]
    [AO : AngleOrderImplicitAxioms G]
    [D34 : Proposition34ImplicitAxioms G]
    [LaterAreaGeometry G]
    [AF : AreaFoundations G]
    [AT : AreaTriangleConstructionAxioms G]
    [PolygonTriangulationGeometry G]
    [PT : PolygonTriangulationFoundations G]
    [PC : ParallelogramCompositionAxioms G]
    (p : Polygon G.Point) {α : Angle G.Point}
    (hfig : RectilinearFigure G p)
    (hang : ValidAngle G α) :
    ∃ A B C D : G.Point,
      Parallelogram G A B C D ∧
      PolygonQuadAreaEq G p A B C D ∧
      G.angleCongruent ⟨D, A, B⟩ α := by
  obtain ⟨pieces, hne, htriang⟩ := hfig
  obtain ⟨A, B, C, D, hpara, heqPieces, hangle⟩ :=
    proposition45_pieces G pieces hne hang
  have heqPoly : PolygonQuadAreaEq G p A B C D :=
    PT.transfer htriang heqPieces
  exact ⟨A, B, C, D, hpara, heqPoly, hangle⟩

end Euclid.Book1
