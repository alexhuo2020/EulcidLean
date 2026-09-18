import EuclidElements.Book1.ExtendedLanguage

namespace Euclid.Book1

open Euclid

/-- Local angle data obtained from the two pairs of parallel sides of a
parallelogram and its diagonal AC (by I.29). -/
class Proposition34ImplicitAxioms (G : Geometry) : Prop where
  diagonalData : ∀ {A B C D : G.Point},
    Parallelogram G A B C D →
    IsTriangle G A B C ∧
    IsTriangle G D C A ∧
    G.angleCongruent ⟨B, A, C⟩ ⟨D, C, A⟩ ∧
    G.angleCongruent ⟨A, C, B⟩ ⟨C, A, D⟩

end Euclid.Book1
