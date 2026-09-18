import EuclidElements.Book3.Proposition36

namespace Euclid.Book3

open Euclid
open Euclid.Book1
open Euclid.Book2

class ConversePowerFoundations
    (G : Geometry) [AreaGeometry G] [CircleOrderGeometry G] : Prop where
  candidateTriangle : forall
    {c : G.Circle} {O D C A B : G.Point},
    G.isCenter c O -> OutsideCircle G D c ->
    G.onCircle C c -> G.onCircle A c -> G.onCircle B c ->
    G.between D C A ->
    Rect G A D C D = Sq G D B ->
    IsTriangle G D B O

end Euclid.Book3
