import EuclidElements.Book2.Definitions

namespace Euclid.Book2

open Euclid
open Euclid.Book1

/-- Reusable Common-Notion-style area laws for Book II. -/
class AreaAxioms (G : Geometry) [AreaGeometry G] : Prop where
  addAssoc : ∀ a b c : Area G,
    Add G (Add G a b) c = Add G a (Add G b c)
  addComm : ∀ a b : Area G,
    Add G a b = Add G b a
  addZeroRight : ∀ a : Area G, Add G a (Zero G) = a
  addCancelLeft : ∀ a b c : Area G,
    Add G a b = Add G a c → b = c

  rectSymm : ∀ A B C D : G.Point,
    Rect G A B C D = Rect G C D A B

  rectCongrLeft : ∀ {A B A' B' C D : G.Point},
    G.segmentCongruent A B A' B' →
    Rect G A B C D = Rect G A' B' C D

  rectCongrRight : ∀ {A B C D C' D' : G.Point},
    G.segmentCongruent C D C' D' →
    Rect G A B C D = Rect G A B C' D'

  squareCongr : ∀ {A B C D : G.Point},
    G.segmentCongruent A B C D → Sq G A B = Sq G C D

  squareAsRectangle : ∀ A B : G.Point,
    Sq G A B = Rect G A B A B

  rectCutRight : ∀ {A B C D E : G.Point},
    G.between C D E →
    Rect G A B C E = Add G (Rect G A B C D) (Rect G A B D E)

  rectCutLeft : ∀ {A B C D E : G.Point},
    G.between A B C →
    Rect G A C D E = Add G (Rect G A B D E) (Rect G B C D E)

end Euclid.Book2
