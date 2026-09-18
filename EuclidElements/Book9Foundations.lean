import EuclidElements.Book8

namespace Euclid.Book9
open Euclid.Book7 Euclid.Book8

/-- Product of all integers from 2 through `n+1`; used for IX.20. -/
def productFromTwo : Nat -> Nat
  | 0 => 1
  | n+1 => productFromTwo n * (n+2)

@[simp] theorem productFromTwo_zero : productFromTwo 0 = 1 := rfl
@[simp] theorem productFromTwo_succ (n : Nat) :
    productFromTwo (n+1) = productFromTwo n * (n+2) := rfl

theorem productFromTwo_pos (n : Nat) : 0 < productFromTwo n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih => exact Nat.mul_pos ih (Nat.succ_pos _)

/-- Every `k` with `2 <= k <= n+1` divides the Euclidean product. -/
theorem dvd_productFromTwo {k n : Nat} (hk2 : 2 <= k) (hkn : k <= n+1) :
    k ∣ productFromTwo n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases htop : k = n+2
      · subst k
        exact Nat.dvd_mul_left _ _
      · have hkle : k <= n+1 := by omega
        exact Nat.dvd_trans (ih hkle) (Nat.dvd_mul_right _ _)

/-- Every natural number greater than one has a prime divisor. -/
theorem primeDivisor_exists {n : Nat} (hn : 1 < n) :
    ∃ p : Nat, Prime p ∧ p ∣ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      classical
      by_cases hp : Prime n
      · exact ⟨n, hp, Nat.dvd_refl n⟩
      · have hall : ¬ (∀ d : Nat, d ∣ n → d = 1 ∨ d = n) := by
          intro h; exact hp ⟨hn, h⟩
        rcases Classical.not_forall.mp hall with ⟨d, hd⟩
        rcases Classical.not_imp.mp hd with ⟨hdn, hdends⟩
        have hdne1 : d ≠ 1 := fun e => hdends (Or.inl e)
        have hdnen : d ≠ n := fun e => hdends (Or.inr e)
        have hnpos : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
        have hdle : d ≤ n := Nat.le_of_dvd hnpos hdn
        have hdlt : d < n := Nat.lt_of_le_of_ne hdle hdnen
        have hdpos : 0 < d := by
          rcases Nat.eq_zero_or_pos d with hd0 | hdp
          · subst d; rcases hdn with ⟨q,hq⟩; simp at hq; subst n
            exact False.elim (Nat.not_lt_zero 1 hn)
          · exact hdp
        have hdgt1 : 1 < d := Nat.lt_of_le_of_ne hdpos (Ne.symm hdne1)
        obtain ⟨p,hp,hpd⟩ := ih d hdlt hdgt1
        exact ⟨p,hp,Nat.dvd_trans hpd hdn⟩

/-- Euclid's even and odd number language for IX.21--IX.34. -/
def EvenNumber (n : Nat) : Prop := ∃ k : Nat, n = 2*k
def OddNumber (n : Nat) : Prop := ∃ k : Nat, n = 2*k+1

/-- `1 + 2 + ... + 2^(n-1)`. -/
def powSum2 : Nat -> Nat
  | 0 => 0
  | n+1 => powSum2 n + 2^n

@[simp] theorem powSum2_zero : powSum2 0 = 0 := rfl
@[simp] theorem powSum2_succ (n : Nat) : powSum2 (n+1) = powSum2 n + 2^n := rfl

theorem powSum2_add_one (n : Nat) : powSum2 n + 1 = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [powSum2_succ, Nat.pow_succ]
      omega

/-- The explicit aliquot-part sum used in Euclid IX.36. -/
def euclidAliquotSum (p : Nat) : Nat :=
  powSum2 p + (2^p - 1) * powSum2 (p-1)


end Euclid.Book9
