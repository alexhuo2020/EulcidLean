import EuclidElements.Book1.Proposition23

/-!
# Oriented angle copying

Euclid's constructions routinely choose on which side of a line the new angle
is drawn.  The original I.23 statement suppresses this orientation choice.
This generic interface isolates precisely that missing construction principle.
-/

namespace Euclid.Book1

open Euclid

class OrientedAngleCopyAxioms (G : Geometry) : Prop where
  copyOppositeSide : ∀
    {A B X D C E : G.Point} {t : G.Line},
    A ≠ B →
    G.onLine A t → G.onLine B t →
    ¬ G.onLine X t →
    ValidAngle G ⟨D, C, E⟩ →
    ∃ F : G.Point,
      F ≠ A ∧
      ¬ G.onLine F t ∧
      ¬ G.sameSide F X t ∧
      G.angleCongruent ⟨F, A, B⟩ ⟨D, C, E⟩

end Euclid.Book1
