import EuclidElements.Book7

namespace Euclid.Book8
open Euclid.Book7

def SameRatio (a b c d : Nat) : Prop := a * d = b * c
def Continued3 (a b c : Nat) : Prop := SameRatio a b b c
def Continued4 (a b c d : Nat) : Prop := SameRatio a b b c ∧ SameRatio b c c d
def SquareNumber (n : Nat) : Prop := ∃ r : Nat, n = r ^ 2
def CubeNumber (n : Nat) : Prop := ∃ r : Nat, n = r ^ 3
def HasOneMean (a c : Nat) : Prop := ∃ b : Nat, Continued3 a b c
def HasTwoMeans (a d : Nat) : Prop := ∃ b c : Nat, Continued4 a b c d
def SimilarPlaneNumbers (a b : Nat) : Prop := HasOneMean a b
def SimilarSolidNumbers (a b : Nat) : Prop := HasTwoMeans a b
def SquareRatio (a b : Nat) : Prop := ∃ r s : Nat, SameRatio a b (r^2) (s^2)
def CubeRatio (a b : Nat) : Prop := ∃ r s : Nat, SameRatio a b (r^3) (s^3)
end Euclid.Book8
