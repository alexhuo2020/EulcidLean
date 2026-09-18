import EuclidElements.Book5
import EuclidElements.Book1.LaterAreaGeometry

/-!
# Euclid Book VI: proportional plane geometry

Book VI applies the Eudoxian ratio theory of Book V to straight lines and to
areas of rectilinear figures.  This file introduces only the bridge needed to
state those results synthetically: segment and triangle magnitudes, and the
standard similarity predicates.  No coordinates or real-valued lengths are
used.
-/

namespace Euclid.Book6

open Euclid
open Euclid.Book1
open Euclid.Book5

/-- A synthetic magnitude interpretation of straight-line segments. -/
class SegmentMagnitudeGeometry (G : Geometry) where
  Magnitude : Type
  magnitudeStructure : MagnitudeStructure Magnitude
  magnitudeAxioms : MagnitudeAxioms Magnitude
  length : G.Point → G.Point → Magnitude
  positive : ∀ {A B : G.Point}, A ≠ B → Positive (length A B)
  congruent_iff : ∀ {A B C D : G.Point},
    G.segmentCongruent A B C D ↔ length A B = length C D

attribute [instance] SegmentMagnitudeGeometry.magnitudeStructure
attribute [instance] SegmentMagnitudeGeometry.magnitudeAxioms

/-- Ratio of two straight lines in the Eudoxian sense of Book V. -/
def SegmentRatio (G : Geometry) [S : SegmentMagnitudeGeometry G]
    (A B C D : G.Point) : Prop :=
  SameRatio (S.length A B) (S.length C D) (S.length A B) (S.length C D)

/-- Equality of two ratios of straight lines. -/
def SegmentProportional (G : Geometry) [S : SegmentMagnitudeGeometry G]
    (A B C D E F H I : G.Point) : Prop :=
  SameRatio (S.length A B) (S.length C D) (S.length E F) (S.length H I)

/-- Equiangular triangles, with vertices corresponding in the displayed order. -/
def EquiangularTriangles (G : Geometry)
    (A B C D E F : G.Point) : Prop :=
  G.angleCongruent ⟨B,A,C⟩ ⟨E,D,F⟩ ∧
  G.angleCongruent ⟨A,B,C⟩ ⟨D,E,F⟩ ∧
  G.angleCongruent ⟨A,C,B⟩ ⟨D,F,E⟩

/-- Euclid VI.Def.1: similar rectilinear figures have corresponding equal
angles and proportional corresponding sides.  The triangle specialization is
used throughout VI.4--VI.8 and VI.19. -/
def SimilarTriangles (G : Geometry) [S : SegmentMagnitudeGeometry G]
    (A B C D E F : G.Point) : Prop :=
  EquiangularTriangles G A B C D E F ∧
  SegmentProportional G A B B C D E E F ∧
  SegmentProportional G B C C A E F F D

/-- Euclid VI.Def.3: a straight line is cut in extreme and mean ratio. -/
def ExtremeMeanRatio (G : Geometry) [S : SegmentMagnitudeGeometry G]
    (A B C : G.Point) : Prop :=
  G.between A C B ∧ SegmentProportional G A B A C A C C B

/-- The ratio of two triangles, represented abstractly by positive area
magnitudes.  This keeps Book VI synthetic and independent of real-valued area. -/
class TriangleMagnitudeGeometry (G : Geometry) where
  Magnitude : Type
  magnitudeStructure : MagnitudeStructure Magnitude
  magnitudeAxioms : MagnitudeAxioms Magnitude
  area : G.Point → G.Point → G.Point → Magnitude
  positive : ∀ {A B C : G.Point}, IsTriangle G A B C → Positive (area A B C)

attribute [instance] TriangleMagnitudeGeometry.magnitudeStructure
attribute [instance] TriangleMagnitudeGeometry.magnitudeAxioms

def TriangleProportional (G : Geometry) [T : TriangleMagnitudeGeometry G]
    (A B C D E F P Q R U V W : G.Point) : Prop :=
  SameRatio (T.area A B C) (T.area D E F) (T.area P Q R) (T.area U V W)

end Euclid.Book6
