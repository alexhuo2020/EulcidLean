import EuclidElements.Book9
import EuclidElements.Book5.MagnitudeFoundations

/-!
# Euclid Book X: commensurable and irrational magnitudes

The opening theory is kept synthetic.  It reuses Book V's additive magnitude
structure and natural multiples, and introduces only the Book-X notions of
measurement, commensurability, numerical ratios, and square-commensurability.
-/
namespace Euclid.Book10
open Euclid.Book5

variable {M : Type}

/-- A magnitude `d` measures `a` when a positive natural multiple of `d` is `a`. -/
def Measures [MagnitudeStructure M] (d a : M) : Prop :=
  ∃ n : Nat, 0 < n ∧ Multiple n d = a

/-- X.Def.I.1: two magnitudes have a common measure. -/
def Commensurable [MagnitudeStructure M] (a b : M) : Prop :=
  ∃ d : M, Positive d ∧ Measures d a ∧ Measures d b

def Incommensurable [MagnitudeStructure M] (a b : M) : Prop :=
  ¬ Commensurable a b

/-- A concrete realization of the ratio `m:n` by magnitudes `a:b`. -/
def HasNumberRatio [MagnitudeStructure M] (a b : M) (m n : Nat) : Prop :=
  0 < m ∧ 0 < n ∧ ∃ d : M, Positive d ∧ Multiple m d = a ∧ Multiple n d = b

/-- X.5--8 terminology: the ratio of two magnitudes is the ratio of numbers. -/
def HasSomeNumberRatio [MagnitudeStructure M] (a b : M) : Prop :=
  ∃ m n : Nat, HasNumberRatio a b m n

/-- Greatest common measure in Euclid's divisibility sense. -/
def GreatestCommonMeasure [MagnitudeStructure M] (d a b : M) : Prop :=
  Measures d a ∧ Measures d b ∧
  ∀ e : M, Measures e a → Measures e b → Measures e d

/-- A three-magnitude greatest common measure. -/
def GreatestCommonMeasure3 [MagnitudeStructure M] (d a b c : M) : Prop :=
  Measures d a ∧ Measures d b ∧ Measures d c ∧
  ∀ e : M, Measures e a → Measures e b → Measures e c → Measures e d

/-- A sequence in which each remainder is at most half its predecessor. -/
def ExhaustionChain [MagnitudeStructure M] (s : Nat → M) : Prop :=
  ∀ n, Le (Add (s (n+1)) (s (n+1))) (s n)

/-- Primitive Archimedean/exhaustion consequence isolated for X.1. -/
class ExhaustionAxioms (M : Type) [MagnitudeStructure M] : Prop where
  eventuallyBelow : ∀ {s : Nat → M} {b : M},
    ExhaustionChain s → Positive b → Positive (s 0) →
    ∃ n : Nat, Less (s n) b

/-- Anthyphairesis data: the Euclidean subtraction process does not terminate. -/
def InfiniteAnthyphairesis [MagnitudeStructure M] (a b : M) : Prop :=
  ∀ d : M, Positive d → ¬ (Measures d a ∧ Measures d b)

/-- Construction/existence principles for greatest common measures.  These are
not ratio theorems; they isolate the termination/well-ordering content of X.3--4. -/
class CommonMeasureConstructionAxioms (M : Type) [MagnitudeStructure M] : Prop where
  gcd2 : ∀ {a b : M}, Commensurable a b → ∃ d : M, GreatestCommonMeasure d a b
  gcd3 : ∀ {a b c : M},
    (∃ d : M, Measures d a ∧ Measures d b ∧ Measures d c) →
    ∃ g : M, GreatestCommonMeasure3 g a b c

/-- Transport laws for commensurability used in X.11--13. -/
class CommensurabilityAxioms (M : Type) [MagnitudeStructure M] : Prop where
  refl : ∀ {a : M}, Positive a → Commensurable a a
  symm : ∀ {a b : M}, Commensurable a b → Commensurable b a
  trans : ∀ {a b c : M}, Commensurable a b → Commensurable b c → Commensurable a c
  proportionalTransport : ∀ {a b c d : M},
    SameRatio a b c d → Commensurable a b → Commensurable c d

/-- Cross-kind form of X.11: corresponding terms of equal ratios are
commensurable together.  This is needed when a line ratio is identified with
an area ratio (as in VI.1 and X.19--21). -/
class RatioCommensurabilityTransport (M N : Type)
    [MagnitudeStructure M] [MagnitudeStructure N] : Prop where
  commensurable_iff : forall {a b : M} {c d : N},
    SameRatio a b c d -> (Commensurable a b <-> Commensurable c d)

/-- Square data for straight-line magnitudes.  `Area` may be a different kind
of magnitude, as in Euclid. -/
class SquareMagnitude (L A : Type)
    [MagnitudeStructure L] [MagnitudeStructure A] where
  square : L → A

/-- X.Def.I.2. -/
def CommensurableInSquare (L A : Type)
    [MagnitudeStructure L] [MagnitudeStructure A] [Q : SquareMagnitude L A]
    (a b : L) : Prop := Commensurable (Q.square a) (Q.square b)

/-- Numerical square-ratio form occurring in X.9. -/
def HasSquareNumberRatio (L A : Type)
    [MagnitudeStructure L] [MagnitudeStructure A] [Q : SquareMagnitude L A]
    (a b : L) : Prop :=
  ∃ m n : Nat, 0 < m ∧ 0 < n ∧
    HasSomeNumberRatio (Q.square a) (Q.square b) ∧
    (∃ r s : Nat, m = r*r ∧ n = s*s)

/-- The genuinely geometric scaling fact behind X.9. -/
class SquareRatioAxioms (L A : Type)
    [MagnitudeStructure L] [MagnitudeStructure A] [SquareMagnitude L A] : Prop where
  squareRatio_of_commensurable : ∀ {a b : L},
    Commensurable a b → HasSquareNumberRatio L A a b
  commensurable_of_squareRatio : ∀ {a b : L},
    HasSquareNumberRatio L A a b → Commensurable a b


/-- The square on `a` exceeds the square on `b` by the square on `e`. -/
def SquareExcessBy (L A : Type)
    [MagnitudeStructure L] [MagnitudeStructure A] [Q : SquareMagnitude L A]
    (a b e : L) : Prop := Add (Q.square b) (Q.square e) = Q.square a

/-- Generic Pythagorean/similarity algebra behind X.14: proportional pairs
with corresponding square deficits have proportional complementary sides.
This is a geometric law, not a commensurability conclusion. -/
class SquareDifferenceRatioAxioms (L A : Type)
    [MagnitudeStructure L] [MagnitudeStructure A] [Q : SquareMagnitude L A] : Prop where
  complementary_ratio : forall {a b c d e f : L},
    SameRatio a b c d ->
    SquareExcessBy L A a b e ->
    SquareExcessBy L A c d f ->
    SameRatio a e c f

/-- The subtraction-of-measures fact needed for the converse direction of
X.15: if a common unit measures a sum and one summand, it measures the other.
This is a discrete consequence of the magnitude subtraction structure. -/
class MeasureDifferenceAxioms (M : Type)
    [MagnitudeStructure M] : Prop where
  right : ∀ {d a b : M}, Measures d (Add a b) → Measures d a → Measures d b
  left : ∀ {d a b : M}, Measures d (Add a b) → Measures d b → Measures d a


/-- Abstract rectangle area contained by two line magnitudes. -/
class RectangleMagnitude (L A : Type)
    [MagnitudeStructure L] [MagnitudeStructure A] where
  rect : L -> L -> A

/-- VI.1-style ratio law for a square and a rectangle on the same first side. -/
class RectangleRatioAxioms (L A : Type)
    [MagnitudeStructure L] [MagnitudeStructure A]
    [Q : SquareMagnitude L A] [R : RectangleMagnitude L A] : Prop where
  square_rectangle_ratio : forall {a b : L},
    SameRatio a b (Q.square a) (R.rect a b)

/-- A line is rational relative to an assigned rational line when their squares
are commensurable (this includes commensurability in length as a special case). -/
def RationalLineRelative (L A : Type)
    [MagnitudeStructure L] [MagnitudeStructure A] [Q : SquareMagnitude L A]
    (u a : L) : Prop := Commensurable (Q.square u) (Q.square a)

/-- An area is rational relative to the square on the assigned line. -/
def RationalAreaRelative (L A : Type)
    [MagnitudeStructure L] [MagnitudeStructure A] [Q : SquareMagnitude L A]
    (u : L) (x : A) : Prop := Commensurable (Q.square u) x

def IrrationalAreaRelative (L A : Type)
    [MagnitudeStructure L] [MagnitudeStructure A] [Q : SquareMagnitude L A]
    (u : L) (x : A) : Prop := ¬ RationalAreaRelative L A u x

/-- X.21 terminology: two lines are commensurable in square only when their
squares are commensurable but the lines themselves are not. -/
def CommensurableInSquareOnly (L A : Type)
    [MagnitudeStructure L] [MagnitudeStructure A] [Q : SquareMagnitude L A]
    (a b : L) : Prop :=
  Commensurable (Q.square a) (Q.square b) /\ Incommensurable a b

/-- X.Def.I.3 relative to a fixed rational reference line. -/
def RationalRelative [MagnitudeStructure M] (u a : M) : Prop := Commensurable u a

def IrrationalRelative [MagnitudeStructure M] (u a : M) : Prop := Incommensurable u a

end Euclid.Book10
