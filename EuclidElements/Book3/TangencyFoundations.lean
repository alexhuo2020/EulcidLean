import EuclidElements.Book3.Proposition10

namespace Euclid.Book3

open Euclid
open Euclid.Book1

/--
Generic circle-tangency geometry used by III.11--III.13.  The relation-valued
fields make this a data/type interface rather than a `Prop` class.  Its proof
fields isolate diagrammatic facts suppressed by Euclid: a non-collinear common
boundary point forces a second intersection, and the internal/external labels
determine the appropriate order once collinearity is known.
-/
class TangencyOrderGeometry (G : Geometry) where
  internallyTangentAt : G.Circle -> G.Circle -> G.Point -> Prop
  externallyTangentAt : G.Circle -> G.Circle -> G.Point -> Prop

  internalCommonPoint : forall {c d : G.Circle} {T : G.Point},
    internallyTangentAt c d T -> G.onCircle T c ∧ G.onCircle T d
  externalCommonPoint : forall {c d : G.Circle} {T : G.Point},
    externallyTangentAt c d T -> G.onCircle T c ∧ G.onCircle T d

  internalNoSecondIntersection : forall {c d : G.Circle} {T X : G.Point},
    internallyTangentAt c d T ->
    G.onCircle X c -> G.onCircle X d -> X = T
  externalNoSecondIntersection : forall {c d : G.Circle} {T X : G.Point},
    externallyTangentAt c d T ->
    G.onCircle X c -> G.onCircle X d -> X = T

  noncollinearCommonPointGivesSecond : forall
    {c d : G.Circle} {O P T : G.Point},
    G.isCenter c O -> G.isCenter d P ->
    G.onCircle T c -> G.onCircle T d ->
    (¬ G.Collinear O P T) ->
    exists X : G.Point,
      X ≠ T ∧ G.onCircle X c ∧ G.onCircle X d

  internalOrderOfCollinearCenters : forall
    {c d : G.Circle} {O P T : G.Point},
    internallyTangentAt c d T ->
    G.isCenter c O -> G.isCenter d P ->
    G.Collinear O P T ->
    G.between O P T

  externalOrderOfCollinearCenters : forall
    {c d : G.Circle} {O P T : G.Point},
    externallyTangentAt c d T ->
    G.isCenter c O -> G.isCenter d P ->
    G.Collinear O P T ->
    G.between O T P

end Euclid.Book3
