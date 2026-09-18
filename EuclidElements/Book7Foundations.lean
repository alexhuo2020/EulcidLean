import EuclidElements.Book6

/-!
# Euclid Book VII: elementary number theory

Book VII changes subject from plane geometry to positive integers.  We model a
Euclidean number by `Nat`, with positivity hypotheses where Euclid excludes the
unit/zero edge cases.  Divisibility is Lean's standard natural-number
relation; the definitions below record Euclid's terminology explicitly.
-/
namespace Euclid.Book7

/-- VII.Def.1: a unit is that by virtue of which each thing that exists is
called one. -/
def Unit (n : Nat) : Prop := n = 1

/-- VII.Def.2: a number is a multitude composed of units. -/
def Number (n : Nat) : Prop := 0 < n

/-- VII.Def.3: a number is a part of a number when it measures it. -/
def PartOf (a b : Nat) : Prop := a ∣ b

/-- VII.Def.4: parts when the smaller does not measure the greater. -/
def PartsOf (a b : Nat) : Prop := 0 < a ∧ a < b ∧ ¬ a ∣ b

/-- VII.Def.5: a multiple is measured by the smaller number. -/
def MultipleOf (b a : Nat) : Prop := a ∣ b

/-- VII.Def.11: prime number. -/
def Prime (p : Nat) : Prop := 1 < p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- VII.Def.12: numbers prime to one another. -/
def PrimeTo (a b : Nat) : Prop := Nat.gcd a b = 1

/-- VII.Def.13/14: composite number. -/
def Composite (n : Nat) : Prop := 1 < n ∧ ¬ Prime n

/-- Common measure of two numbers. -/
def CommonMeasure (d a b : Nat) : Prop := d ∣ a ∧ d ∣ b

/-- `d` is a greatest common measure of `a,b`. -/
def GreatestCommonMeasure (d a b : Nat) : Prop :=
  CommonMeasure d a b ∧ ∀ e : Nat, CommonMeasure e a b → e ∣ d

end Euclid.Book7

namespace Euclid.Book7

/-- Two numbers are the same exact aliquot part of two wholes when the wholes
are obtained by multiplying the parts by one common positive integer. -/
def SamePart (a b c d : Nat) : Prop :=
  ∃ n : Nat, 0 < n ∧ b = n * a ∧ d = n * c

/-- Algebraic form of Euclid's "same part or same parts": the two numerical
ratios agree.  Cross multiplication avoids division and therefore handles all
Book-VII ratio arguments constructively over naturals. -/
def SameParts (a b c d : Nat) : Prop := a * d = c * b

end Euclid.Book7

namespace Euclid.Book7

/-- A pair is least in its ratio when it is reduced and consequently measures
corresponding terms of every integral realization of that ratio. -/
def LeastRatioPair (a b : Nat) : Prop :=
  PrimeTo a b ∧ ∀ {c d : Nat}, SameParts a b c d → a ∣ c ∧ b ∣ d

theorem primeTo_symm {a b : Nat} (h : PrimeTo a b) : PrimeTo b a := by
  unfold PrimeTo at h ⊢
  simpa [Nat.gcd_comm] using h

end Euclid.Book7

namespace Euclid.Book7

/-- A number has a named `q`-th part `p` when the whole is `q` copies of that
part.  This is the arithmetic content of VII.37--VII.39. -/
def HasNamedPart (n q p : Nat) : Prop := n = q * p

/-- Least common multiple property for a finite displayed family. -/
def LeastCommonMultiple2 (l a b : Nat) : Prop :=
  a ∣ l ∧ b ∣ l ∧ ∀ n : Nat, a ∣ n → b ∣ n → l ∣ n

/-- Three-number version used in VII.36. -/
def LeastCommonMultiple3 (l a b c : Nat) : Prop :=
  a ∣ l ∧ b ∣ l ∧ c ∣ l ∧
  ∀ n : Nat, a ∣ n → b ∣ n → c ∣ n → l ∣ n

end Euclid.Book7
