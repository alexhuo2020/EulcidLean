import EuclidElements.Book1.Transversal

/-!
# Plane separation and order consequences

These are reusable order/separation facts, not Euclid proposition conclusions.
They isolate the part of Hilbert's order theory still missing from the primitive
`between`/`sameSide` language.
-/

namespace Euclid.Book1

open Euclid

/--
Generic line-separation facts used for transversal arguments.

`meetingRayCases` says that, when the two cut lines meet and the selected arm
points are on opposite sides of the transversal, the intersection lies on the
selected ray at one crossing and on the opposite ray at the other.  The two
`oppositeCompanion...` fields express the elementary half-plane fact needed to
turn an alternate-angle inequality into the same-side-interior configuration of
Euclid's Postulate 5.
-/
class PlaneSeparationAxioms (G : Geometry) : Prop where
  meetingRayCases : ∀ (s : TransversalSetup G),
    (¬ G.sameSide s.a s.b s.t) →
    G.LinesMeet s.l s.m →
    ∃ x : G.Point,
      (IsTriangle G s.p x s.q ∧
        SameRay G s.p s.a x ∧
        G.between x s.q s.b) ∨
      (IsTriangle G s.q x s.p ∧
        SameRay G s.q s.b x ∧
        G.between x s.p s.a)

  oppositeCompanionAtQ : ∀ (s : TransversalSetup G),
    (¬ G.sameSide s.a s.b s.t) →
    ∃ b' : G.Point,
      G.between s.b s.q b' ∧
      G.onLine b' s.m ∧
      G.sameSide s.a b' s.t

  oppositeCompanionAtP : ∀ (s : TransversalSetup G),
    (¬ G.sameSide s.a s.b s.t) →
    ∃ a' : G.Point,
      G.between s.a s.p a' ∧
      G.onLine a' s.l ∧
      G.sameSide s.b a' s.t

end Euclid.Book1
