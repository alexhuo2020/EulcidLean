import EuclidElements.Book5.MagnitudeFoundations

namespace Euclid.Book5

variable {M : Type}

/-- Synthetic finite sum of magnitudes. -/
def MagnitudeListSum [MagnitudeStructure M] : List M → M
  | [] => Zero
  | a :: as => Add a (MagnitudeListSum as)

/-- Two lists are termwise the same natural multiple. -/
inductive EquimultipleLists [MagnitudeStructure M] (n : Nat) : List M → List M → Prop
  | nil : EquimultipleLists n [] []
  | cons {a b : M} {as bs : List M} :
      a = Multiple n b → EquimultipleLists n as bs →
      EquimultipleLists n (a :: as) (b :: bs)

end Euclid.Book5
