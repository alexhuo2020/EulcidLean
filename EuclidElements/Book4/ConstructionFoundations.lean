import EuclidElements.Book4.OrderFoundations

namespace Euclid.Book4

open Euclid
open Euclid.Book1
open Euclid.Book3

/-- Generic existence of a diameter of a circle.  Euclid repeatedly draws a
    straight line through the center and extends it to the circumference. -/
class DiameterExistenceAxioms (G : Geometry) : Prop where
  diameter : forall c : G.Circle, ∃ A B : G.Point, IsDiameter G c A B

end Euclid.Book4
