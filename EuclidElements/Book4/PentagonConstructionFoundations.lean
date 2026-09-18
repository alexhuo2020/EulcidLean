import EuclidElements.Book4.Proposition09
import EuclidElements.Book3.CircleAngleFoundations

namespace Euclid.Book4

open Euclid
open Euclid.Book1
open Euclid.Book3

/-- Euclid's IV.10 construction trace after the II.11 cut, IV.1 chord fitting,
    IV.5 circumcircle, III.37 tangent converse and III.32 tangent-chord step.
    The doubled-angle conclusion itself is deliberately not a field. -/
class GoldenTriangleConstructionAxioms
    (G : Geometry) [AngleAdditionGeometry G] : Prop where
  frame : ∃ A B C D : G.Point,
    IsTriangle G A B D ∧
    IsTriangle G C A D ∧
    G.segmentCongruent A B A D ∧
    G.segmentCongruent C A C D ∧
    G.angleCongruent ⟨B, D, C⟩ ⟨D, A, C⟩ ∧
    G.angleCongruent ⟨D, A, C⟩ ⟨D, A, B⟩ ∧
    G.angleCongruent ⟨B, D, A⟩ ⟨B, C, D⟩ ∧
    G.angleCongruent ⟨D, B, A⟩ ⟨B, C, D⟩ ∧
    AngleSumEq G ⟨B, D, C⟩ ⟨C, D, A⟩ ⟨B, D, A⟩

/-- Construction data for IV.11--IV.14.  These fields expose the finite
    straightedge/compass diagram and component equalities; proposition files
    package them into the Book-IV predicates. -/
class PentagonBook4ConstructionAxioms (G : Geometry) : Prop where
  inscribedFromGolden : forall {c : G.Circle} {X Y Z : G.Point},
    IsTriangle G X Y Z ->
    ∃ A B C D E : G.Point,
      IsTriangle G E A B ∧ IsTriangle G A B C ∧ IsTriangle G B C D ∧
      IsTriangle G C D E ∧ IsTriangle G D E A ∧
      G.onCircle A c ∧ G.onCircle B c ∧ G.onCircle C c ∧
      G.onCircle D c ∧ G.onCircle E c ∧
      EquilateralPentagon G A B C D E ∧
      EquiangularPentagon G A B C D E

  circumscribedFromInscribed : forall {c : G.Circle} {A B C D E : G.Point},
    PentagonInscribedInCircle G c A B C D E ->
    ∃ P Q R S T : G.Point,
    ∃ lPQ lQR lRS lST lTP : G.Line, ∃ U V W X Y : G.Point,
      IsTriangle G T P Q ∧ IsTriangle G P Q R ∧ IsTriangle G Q R S ∧
      IsTriangle G R S T ∧ IsTriangle G S T P ∧
      EquilateralPentagon G P Q R S T ∧ EquiangularPentagon G P Q R S T ∧
      SideLine G P Q lPQ ∧ SideLine G Q R lQR ∧ SideLine G R S lRS ∧
      SideLine G S T lST ∧ SideLine G T P lTP ∧
      TangentAt G c lPQ U ∧ TangentAt G c lQR V ∧ TangentAt G c lRS W ∧
      TangentAt G c lST X ∧ TangentAt G c lTP Y

  incircleFrame : forall {A B C D E : G.Point},
    RegularPentagon G A B C D E ->
    ∃ O T U V W X : G.Point,
    ∃ lAB lBC lCD lDE lEA rT rU rV rW rX : G.Line,
      SideLine G A B lAB ∧ SideLine G B C lBC ∧ SideLine G C D lCD ∧
      SideLine G D E lDE ∧ SideLine G E A lEA ∧
      G.onLine T lAB ∧ G.onLine U lBC ∧ G.onLine V lCD ∧
      G.onLine W lDE ∧ G.onLine X lEA ∧
      G.onLine O rT ∧ G.onLine T rT ∧ Perpendicular G rT lAB ∧
      G.onLine O rU ∧ G.onLine U rU ∧ Perpendicular G rU lBC ∧
      G.onLine O rV ∧ G.onLine V rV ∧ Perpendicular G rV lCD ∧
      G.onLine O rW ∧ G.onLine W rW ∧ Perpendicular G rW lDE ∧
      G.onLine O rX ∧ G.onLine X rX ∧ Perpendicular G rX lEA ∧
      O ≠ T ∧
      G.segmentCongruent O T O U ∧ G.segmentCongruent O T O V ∧
      G.segmentCongruent O T O W ∧ G.segmentCongruent O T O X

  circumcenterFrame : forall {A B C D E : G.Point},
    RegularPentagon G A B C D E ->
    ∃ O : G.Point,
      O ≠ A ∧
      G.segmentCongruent O A O B ∧ G.segmentCongruent O A O C ∧
      G.segmentCongruent O A O D ∧ G.segmentCongruent O A O E

end Euclid.Book4
