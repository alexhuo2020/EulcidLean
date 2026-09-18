import EuclidElements.Book5.Proposition15

namespace Euclid.Book5

/-- Cross-comparison principle used by alternendo.  Here all four magnitudes
must be of one kind, because the alternate ratios compare first with third and
second with fourth. -/
class CrossComparisonAxioms
    (M : Type) [MagnitudeStructure M] : Prop where
  crossCompare : forall {a b c d : M},
    Positive a -> Positive b -> Positive c -> Positive d ->
    SameRatio a b c d ->
    forall m n : Nat, 0 < m -> 0 < n ->
      (Less (Multiple n c) (Multiple m a) <->
        Less (Multiple n d) (Multiple m b)) /\
      (Multiple m a = Multiple n c <->
        Multiple m b = Multiple n d) /\
      (Less (Multiple m a) (Multiple n c) <->
        Less (Multiple m b) (Multiple n d))

/-- Advanced comparison principle for adjoining the consequent to the
antecedent.  The two ratio pairs may belong to different kinds. -/
class JointRatioComparisonAxioms
    (M N : Type) [MagnitudeStructure M] [MagnitudeStructure N] : Prop where
  joint : forall {a b : M} {c d : N},
    Positive a -> Positive b -> Positive c -> Positive d ->
    SameRatio a b c d -> SameRatio (Add a b) b (Add c d) d

/-- Binary ex-aequali composition.  It is isolated because Euclid's proof uses
the comparison content of V.Def.4 beyond the bare Archimedean condition. -/
class RatioCompositionAxioms
    (M N : Type) [MagnitudeStructure M] [MagnitudeStructure N] : Prop where
  compose : forall {a b c : M} {d e f : N},
    Positive a -> Positive b -> Positive c ->
    Positive d -> Positive e -> Positive f ->
    SameRatio a b d e -> SameRatio b c e f -> SameRatio a c d f

/-- Perturbed three-term composition used in V.21/V.23. -/
class PerturbedRatioCompositionAxioms
    (M N : Type) [MagnitudeStructure M] [MagnitudeStructure N] : Prop where
  compose : forall {a b c : M} {d e f : N},
    Positive a -> Positive b -> Positive c ->
    Positive d -> Positive e -> Positive f ->
    SameRatio a b e f -> SameRatio b c d e -> SameRatio a c d f

/-- Additive compatibility of two ratios sharing corresponding consequents,
used in V.24. -/
class AntecedentAdditionComparisonAxioms
    (M N : Type) [MagnitudeStructure M] [MagnitudeStructure N] : Prop where
  addAntecedents : forall {a b e : M} {c d f : N},
    Positive a -> Positive b -> Positive e ->
    Positive c -> Positive d -> Positive f ->
    SameRatio a b c d -> SameRatio e b f d ->
    SameRatio (Add a e) b (Add c f) d

/-- A finite chain of adjacent corresponding ratios, represented by its
endpoints.  Positivity is carried by the construction so V.22 can apply the
binary composition principle at every step. -/
inductive RatioChain
    (M N : Type) [MagnitudeStructure M] [MagnitudeStructure N] :
    M -> M -> N -> N -> Prop
  | single {a b : M} {c d : N} :
      Positive a -> Positive b -> Positive c -> Positive d ->
      SameRatio a b c d -> RatioChain M N a b c d
  | step {a b c : M} {d e f : N} :
      Positive a -> Positive b -> Positive c ->
      Positive d -> Positive e -> Positive f ->
      SameRatio a b d e -> RatioChain M N b c e f ->
      RatioChain M N a c d f

end Euclid.Book5
