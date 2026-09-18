import EuclidElements.Book5.FiniteMagnitudeFoundations

namespace Euclid.Book5

/-- Euclid V.1: sums of termwise equimultiples are equimultiples. -/
theorem proposition1
    (M : Type) [MagnitudeStructure M] [A : MagnitudeAxioms M]
    {n : Nat} {xs ys : List M}
    (h : EquimultipleLists n xs ys) :
    MagnitudeListSum xs = Multiple n (MagnitudeListSum ys) := by
  induction h with
  | nil =>
      simp [MagnitudeListSum, multiple_zero]
  | cons ha hs ih =>
      simp only [MagnitudeListSum]
      calc
        Add _ _ = Add (Multiple n _) (Multiple n _) := by rw [ha, ih]
        _ = Multiple n (Add _ _) := (multiple_add n _ _).symm

end Euclid.Book5
