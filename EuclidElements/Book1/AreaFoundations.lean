import EuclidElements.Book1.LaterAreaGeometry

/-!
# Generic synthetic area foundations

These are semantic/common-notion principles for equal figures.  They are not
numbered Book I propositions.  In particular, no field states I.35--I.41.
-/

namespace Euclid.Book1

open Euclid

class AreaFoundations
    (G : Geometry)
    [TriangleAreaGeometry G]
    [LaterAreaGeometry G] : Prop where

  /-- Equal bases lying on one line and vertices lying on a parallel line
      determine equal triangle areas (same altitude). -/
  equalBaseSameAltitude : ∀
    {A B C D E F : G.Point} {base top : G.Line},
    IsTriangle G A B C → IsTriangle G D E F →
    G.segmentCongruent B C E F →
    G.onLine B base → G.onLine C base →
    G.onLine E base → G.onLine F base →
    G.onLine A top → G.onLine D top →
    Parallel G base top →
    TriangleAreaEq G A B C D E F

  /-- Converse altitude principle: on the same side of the base line, equal
      triangles on congruent bases have their vertices on one parallel. -/
  equalAreaEqualBaseDeterminesParallel : ∀
    {A B C D E F : G.Point} {base : G.Line},
    IsTriangle G A B C → IsTriangle G D E F →
    G.segmentCongruent B C E F →
    TriangleAreaEq G A B C D E F →
    G.onLine B base → G.onLine C base →
    G.onLine E base → G.onLine F base →
    G.sameSide A D base →
    ∃ top : G.Line,
      G.onLine A top ∧ G.onLine D top ∧ Parallel G base top

  /-- Common Notion 2 for a fixed diagonal decomposition: equal corresponding
      triangular parts give equal quadrilateral wholes. -/
  quadEq_of_diagonalParts : ∀
    {A B C D E F H I : G.Point},
    TriangleAreaEq G A B C E F H →
    TriangleAreaEq G A C D E H I →
    QuadAreaEq G A B C D E F H I

  /-- A quadrilateral whose chosen diagonal cuts it into equal triangles is
      double either triangular half. -/
  quadDouble_of_equalDiagonalHalves : ∀
    {A B C D : G.Point},
    TriangleAreaEq G A B C A C D →
    QuadDoubleTriangle G A B C D A B C

  /-- If a midpoint cuts a triangle into two equal-base halves, and another
      quadrilateral is double an equal triangular half, the wholes are equal. -/
  triangleQuadEq_of_midpointHalf : ∀
    {A B C M D E F H : G.Point},
    IsMidpoint G M B C →
    TriangleAreaEq G A M C D E F →
    QuadDoubleTriangle G D E F H D E F →
    TriangleQuadAreaEq G A B C D E F H

  /-- Equality is preserved when an equal quadrilateral replaces the
      quadrilateral side of a triangle--quadrilateral equality. -/
  triangleQuadEq_trans_quad : ∀
    {A B C D E F H P Q R S : G.Point},
    TriangleQuadAreaEq G A B C D E F H →
    QuadAreaEq G D E F H P Q R S →
    TriangleQuadAreaEq G A B C P Q R S

end Euclid.Book1
