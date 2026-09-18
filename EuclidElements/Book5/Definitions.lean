import EuclidElements.Book4

/-!
# Euclid Book V: Eudoxian magnitudes and ratios

Book V is formalized without real numbers or numerical quotients.  A kind of
magnitude carries synthetic addition and order; natural multiples are repeated
addition.  Equality of ratios is Euclid V.Def.5 itself: every pair of positive
integer multiples has the same comparison in the two ratio pairs.
-/

namespace Euclid.Book5

/-- Primitive operations on one *kind* of magnitude.  `zero` is an auxiliary
formal object useful for repeated addition; Euclid's ratio-bearing magnitudes
are required to be positive. -/
class MagnitudeStructure (M : Type) where
  zero : M
  add : M → M → M
  lt : M → M → Prop

variable {M N P : Type}

def Zero [S : MagnitudeStructure M] : M := S.zero

def Add [S : MagnitudeStructure M] (a b : M) : M := S.add a b

def Less [S : MagnitudeStructure M] (a b : M) : Prop := S.lt a b

def Le [S : MagnitudeStructure M] (a b : M) : Prop := a = b ∨ Less a b

def Positive [S : MagnitudeStructure M] (a : M) : Prop := Less (Zero : M) a

/-- Natural multiple, defined by repeated addition rather than scalar
multiplication in a numerical model. -/
def Multiple [S : MagnitudeStructure M] : Nat → M → M
  | 0, _ => Zero
  | n + 1, a => Add (Multiple n a) a

/-- V.Def.1: the less is a part of the greater when it measures the greater. -/
def PartOf [MagnitudeStructure M] (a b : M) : Prop :=
  Less a b ∧ ∃ n : Nat, 1 < n ∧ Multiple n a = b

/-- V.Def.2: the greater is a multiple of the less when measured by it. -/
def ProperMultipleOf [MagnitudeStructure M] (b a : M) : Prop :=
  ∃ n : Nat, 1 < n ∧ Multiple n a = b

/-- V.Def.3: a ratio is a size relation between positive magnitudes of one
kind.  The operational content is supplied by V.Def.4--5. -/
def RatioAdmissible [MagnitudeStructure M] (a b : M) : Prop :=
  Positive a ∧ Positive b

/-- V.Def.4: each magnitude can be multiplied so as to exceed the other. -/
def HasRatio [MagnitudeStructure M] (a b : M) : Prop :=
  Positive a ∧ Positive b ∧
  (∃ m : Nat, 0 < m ∧ Less b (Multiple m a)) ∧
  (∃ n : Nat, 0 < n ∧ Less a (Multiple n b))

/-- V.Def.5, Eudoxus' definition of equality of ratios.  The two ratio pairs
may belong to different kinds of magnitude. -/
def SameRatio [MagnitudeStructure M] [MagnitudeStructure N]
    (a b : M) (c d : N) : Prop :=
  ∀ m n : Nat, 0 < m → 0 < n →
    (Less (Multiple n b) (Multiple m a) ↔
      Less (Multiple n d) (Multiple m c)) ∧
    (Multiple m a = Multiple n b ↔ Multiple m c = Multiple n d) ∧
    (Less (Multiple m a) (Multiple n b) ↔
      Less (Multiple m c) (Multiple n d))

/-- V.Def.6. -/
def Proportional [MagnitudeStructure M] [MagnitudeStructure N]
    (a b : M) (c d : N) : Prop := SameRatio a b c d

/-- V.Def.7: a ratio is greater when one common pair of multiplier indices
makes the first ratio exceed while the second does not exceed. -/
def GreaterRatio [MagnitudeStructure M] [MagnitudeStructure N]
    (a b : M) (c d : N) : Prop :=
  ∃ m n : Nat, 0 < m ∧ 0 < n ∧
    Less (Multiple n b) (Multiple m a) ∧
    Le (Multiple m c) (Multiple n d)

/-- V.Def.8: the least proportion has three terms. -/
def ThreeTermProportion [MagnitudeStructure M] (a b c : M) : Prop :=
  SameRatio a b b c

/-- V.Def.9: `a:c` is duplicate of `a:b` when `a:b = b:c`. -/
def DuplicateRatio [MagnitudeStructure M] (a b c : M) : Prop :=
  SameRatio a b b c

/-- V.Def.10: a four-term continued proportion determines a triplicate ratio. -/
def TriplicateRatio [MagnitudeStructure M] (a b c d : M) : Prop :=
  SameRatio a b b c ∧ SameRatio b c c d

/-- V.Def.12: alternate proportion. -/
def AlternateProportion [MagnitudeStructure M]
    (a b c d : M) : Prop := SameRatio a c b d

/-- V.Def.13: inverse proportion. -/
def InverseProportion [MagnitudeStructure M] [MagnitudeStructure N]
    (a b : M) (c d : N) : Prop := SameRatio b a d c

/-- V.Def.14: taking a ratio jointly (componendo). -/
def JointProportion [MagnitudeStructure M] [MagnitudeStructure N]
    (a b : M) (c d : N) : Prop := SameRatio (Add a b) b (Add c d) d

/-- V.Def.15: taking separately (dividendo), with the antecedents displayed
as sums so the excess is explicit and no subtraction primitive is required. -/
def SeparateProportion [MagnitudeStructure M] [MagnitudeStructure N]
    (a b : M) (c d : N) : Prop := SameRatio a b c d

/-- V.Def.16: conversion, again with the whole displayed as a sum. -/
def ConvertedProportion [MagnitudeStructure M] [MagnitudeStructure N]
    (a b : M) (c d : N) : Prop := SameRatio (Add a b) a (Add c d) c

/-- V.Def.17: ex aequali for three terms on each side. -/
def ExAequo3 [MagnitudeStructure M] [MagnitudeStructure N]
    (a b c : M) (d e f : N) : Prop := SameRatio a c d f

/-- V.Def.18: perturbed proportion data for two chains of three magnitudes. -/
def Perturbed3 [MagnitudeStructure M] [MagnitudeStructure N]
    (a b c : M) (d e f : N) : Prop :=
  SameRatio a b e f ∧ SameRatio b c d e

end Euclid.Book5
