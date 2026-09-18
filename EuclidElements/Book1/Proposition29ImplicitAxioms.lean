import EuclidElements.Book1.Proposition28

namespace Euclid.Book1

open Euclid

/--
Local diagram reductions used in I.29. The two `strict...ForcesMeet` fields are
consequences of **Postulate 5** after converting a strict alternate-angle
inequality into the corresponding same-side-interior configuration. Making the
`Postulates G` instance an explicit class parameter keeps the Euclidean
parallel dependency visible in the type of I.29.
-/
class Proposition29ImplicitAxioms
    (G : Geometry)
    [Postulates G]
    [AngleSumGeometry G] : Prop where
  strictAtPForcesMeet : ∀ (s : TransversalSetup G),
    G.angleLess s.angleAtP s.angleAtQ → G.LinesMeet s.l s.m

  strictAtQForcesMeet : ∀ (s : TransversalSetup G),
    G.angleLess s.angleAtQ s.angleAtP → G.LinesMeet s.l s.m

  alternateToCorresponding : ∀ (s : TransversalSetup G) (γ δ : Angle G.Point),
    G.angleCongruent s.angleAtP s.angleAtQ →
    G.angleCongruent γ s.angleAtP →
    G.angleCongruent s.angleAtQ δ →
    G.angleCongruent γ δ

  alternateToSameSideSupplementary : ∀ (s : TransversalSetup G) (γ : Angle G.Point),
    G.angleCongruent s.angleAtP s.angleAtQ →
    Supplementary G s.angleAtP γ →
    Supplementary G s.angleAtQ γ

end Euclid.Book1
