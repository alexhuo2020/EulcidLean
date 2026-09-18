import EuclidElements.Book3

/-!
# Euclid Book IV: figures inscribed in and circumscribed about circles

The language remains synthetic.  Book IV is almost entirely constructive, so
we make side-lines and tangency data explicit instead of hiding them in a
picture.
-/

namespace Euclid.Book4

open Euclid
open Euclid.Book1
open Euclid.Book3

def SideLine (G : Geometry) (A B : G.Point) (l : G.Line) : Prop :=
  A ≠ B ∧ G.onLine A l ∧ G.onLine B l

def EquiangularTriangles (G : Geometry)
    (A B C D E F : G.Point) : Prop :=
  G.angleCongruent ⟨B, A, C⟩ ⟨E, D, F⟩ ∧
  G.angleCongruent ⟨A, B, C⟩ ⟨D, E, F⟩ ∧
  G.angleCongruent ⟨A, C, B⟩ ⟨D, F, E⟩

def TriangleInscribedInCircle (G : Geometry) (c : G.Circle)
    (A B C : G.Point) : Prop :=
  IsTriangle G A B C ∧ G.onCircle A c ∧ G.onCircle B c ∧ G.onCircle C c

def CircleInscribedInTriangle (G : Geometry) (c : G.Circle)
    (A B C : G.Point) : Prop :=
  IsTriangle G A B C ∧
  ∃ lAB lBC lCA : G.Line, ∃ T U V : G.Point,
    SideLine G A B lAB ∧ SideLine G B C lBC ∧ SideLine G C A lCA ∧
    TangentAt G c lAB T ∧ TangentAt G c lBC U ∧ TangentAt G c lCA V

def CircleCircumscribedAboutTriangle (G : Geometry) (c : G.Circle)
    (A B C : G.Point) : Prop :=
  IsTriangle G A B C ∧ G.onCircle A c ∧ G.onCircle B c ∧ G.onCircle C c

def SquareInscribedInCircle (G : Geometry) (c : G.Circle)
    (A B C D : G.Point) : Prop :=
  Square G A B C D ∧
  G.onCircle A c ∧ G.onCircle B c ∧ G.onCircle C c ∧ G.onCircle D c

def CircleInscribedInSquare (G : Geometry) (c : G.Circle)
    (A B C D : G.Point) : Prop :=
  Square G A B C D ∧
  ∃ lAB lBC lCD lDA : G.Line, ∃ T U V W : G.Point,
    SideLine G A B lAB ∧ SideLine G B C lBC ∧
    SideLine G C D lCD ∧ SideLine G D A lDA ∧
    TangentAt G c lAB T ∧ TangentAt G c lBC U ∧
    TangentAt G c lCD V ∧ TangentAt G c lDA W

def CircleCircumscribedAboutSquare (G : Geometry) (c : G.Circle)
    (A B C D : G.Point) : Prop :=
  Square G A B C D ∧
  G.onCircle A c ∧ G.onCircle B c ∧ G.onCircle C c ∧ G.onCircle D c

def EquilateralPentagon (G : Geometry) (A B C D E : G.Point) : Prop :=
  G.segmentCongruent A B B C ∧ G.segmentCongruent B C C D ∧
  G.segmentCongruent C D D E ∧ G.segmentCongruent D E E A

def EquiangularPentagon (G : Geometry) (A B C D E : G.Point) : Prop :=
  G.angleCongruent ⟨E, A, B⟩ ⟨A, B, C⟩ ∧
  G.angleCongruent ⟨A, B, C⟩ ⟨B, C, D⟩ ∧
  G.angleCongruent ⟨B, C, D⟩ ⟨C, D, E⟩ ∧
  G.angleCongruent ⟨C, D, E⟩ ⟨D, E, A⟩

def RegularPentagon (G : Geometry) (A B C D E : G.Point) : Prop :=
  IsTriangle G E A B ∧ IsTriangle G A B C ∧ IsTriangle G B C D ∧
  IsTriangle G C D E ∧ IsTriangle G D E A ∧
  EquilateralPentagon G A B C D E ∧ EquiangularPentagon G A B C D E

def PentagonInscribedInCircle (G : Geometry) (c : G.Circle)
    (A B C D E : G.Point) : Prop :=
  RegularPentagon G A B C D E ∧
  G.onCircle A c ∧ G.onCircle B c ∧ G.onCircle C c ∧
  G.onCircle D c ∧ G.onCircle E c

def CircleInscribedInPentagon (G : Geometry) (c : G.Circle)
    (A B C D E : G.Point) : Prop :=
  RegularPentagon G A B C D E ∧
  ∃ lAB lBC lCD lDE lEA : G.Line, ∃ T U V W X : G.Point,
    SideLine G A B lAB ∧ SideLine G B C lBC ∧ SideLine G C D lCD ∧
    SideLine G D E lDE ∧ SideLine G E A lEA ∧
    TangentAt G c lAB T ∧ TangentAt G c lBC U ∧ TangentAt G c lCD V ∧
    TangentAt G c lDE W ∧ TangentAt G c lEA X

def CircleCircumscribedAboutPentagon (G : Geometry) (c : G.Circle)
    (A B C D E : G.Point) : Prop :=
  RegularPentagon G A B C D E ∧
  G.onCircle A c ∧ G.onCircle B c ∧ G.onCircle C c ∧
  G.onCircle D c ∧ G.onCircle E c

def RegularHexagon (G : Geometry)
    (A B C D E F : G.Point) : Prop :=
  G.segmentCongruent A B B C ∧ G.segmentCongruent B C C D ∧
  G.segmentCongruent C D D E ∧ G.segmentCongruent D E E F ∧
  G.segmentCongruent E F F A ∧
  G.angleCongruent ⟨F, A, B⟩ ⟨A, B, C⟩ ∧
  G.angleCongruent ⟨A, B, C⟩ ⟨B, C, D⟩ ∧
  G.angleCongruent ⟨B, C, D⟩ ⟨C, D, E⟩ ∧
  G.angleCongruent ⟨C, D, E⟩ ⟨D, E, F⟩ ∧
  G.angleCongruent ⟨D, E, F⟩ ⟨E, F, A⟩

def HexagonInscribedInCircle (G : Geometry) (c : G.Circle)
    (A B C D E F : G.Point) : Prop :=
  RegularHexagon G A B C D E F ∧
  G.onCircle A c ∧ G.onCircle B c ∧ G.onCircle C c ∧
  G.onCircle D c ∧ G.onCircle E c ∧ G.onCircle F c

structure FifteenGon (G : Geometry) where
  vertices : List G.Point
  length_eq : vertices.length = 15

/-- Finite polygon semantics for IV.16.  `equalArcSteps` records Euclid's
    construction by fifteen equal circumferences; `regular` records the
    resulting equilateral/equiangular boundary. -/
class FifteenGonGeometry (G : Geometry) where
  equalArcSteps : G.Circle → FifteenGon G → Prop
  regular : FifteenGon G → Prop

def EqualFifteenArcSteps (G : Geometry) [F : FifteenGonGeometry G]
    (c : G.Circle) (p : FifteenGon G) : Prop := F.equalArcSteps c p

def RegularFifteenGon (G : Geometry) [F : FifteenGonGeometry G]
    (p : FifteenGon G) : Prop := F.regular p

def FifteenGonInscribedInCircle (G : Geometry) [F : FifteenGonGeometry G]
    (c : G.Circle) (p : FifteenGon G) : Prop :=
  RegularFifteenGon G p ∧ ∀ X : G.Point, X ∈ p.vertices → G.onCircle X c

def AngleDouble (G : Geometry) [AngleAdditionGeometry G]
    (α β : Angle G.Point) : Prop := AngleSumEq G α α β

end Euclid.Book4
