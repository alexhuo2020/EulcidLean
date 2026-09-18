import EuclidElements.Book5.Proposition01

namespace Euclid.Book5

/-- Euclid V.2: sums of two pairs of equimultiples are equimultiples. -/
theorem proposition2
    (M : Type) [MagnitudeStructure M] [A : MagnitudeAxioms M]
    {a b c d e f : M} {m n : Nat}
    (hab : a = Multiple m b) (hcd : c = Multiple m d)
    (heb : e = Multiple n b) (hfd : f = Multiple n d) :
    Add a e = Multiple (m+n) b ∧ Add c f = Multiple (m+n) d := by
  constructor
  · calc
      Add a e = Add (Multiple m b) (Multiple n b) := by rw [hab, heb]
      _ = Multiple (m+n) b := (multiple_add_index m n b).symm
  · calc
      Add c f = Add (Multiple m d) (Multiple n d) := by rw [hcd, hfd]
      _ = Multiple (m+n) d := (multiple_add_index m n d).symm

end Euclid.Book5
