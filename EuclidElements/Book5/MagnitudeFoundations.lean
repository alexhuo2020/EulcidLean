import EuclidElements.Book5.Definitions

namespace Euclid.Book5

/-- Background laws for one kind of Euclidean magnitude.  These are additive
order/continuity laws, not ratio theorems. -/
class MagnitudeAxioms (M : Type) [MagnitudeStructure M] : Prop where
  addAssoc : ∀ a b c : M, Add (Add a b) c = Add a (Add b c)
  addComm : ∀ a b : M, Add a b = Add b a
  addZeroRight : ∀ a : M, Add a Zero = a
  addCancelRight : ∀ {a b c : M}, Add a c = Add b c → a = b
  ltIrrefl : ∀ a : M, ¬ Less a a
  ltTrans : ∀ {a b c : M}, Less a b → Less b c → Less a c
  ltTrichotomy : ∀ a b : M, Less a b ∨ a = b ∨ Less b a
  addLtAddRight : ∀ {a b : M} (c : M), Less a b → Less (Add a c) (Add b c)
  addLtCancelRight : ∀ {a b c : M}, Less (Add a c) (Add b c) → Less a b
  positiveAdd : ∀ {a b : M}, Positive a → Positive b → Positive (Add a b)
  archimedean : ∀ {a b : M}, Positive a → Positive b →
    ∃ n : Nat, 0 < n ∧ Less b (Multiple n a)
  difference : ∀ {a b : M}, Less a b →
    ∃ c : M, Positive c ∧ Add a c = b

/-- Finite-multiple separation used in V.8.  It is the least-multiple
number-selection consequence of the Archimedean condition, isolated so that no
real-number completeness is used. -/
class EudoxusSeparationAxioms (M : Type) [MagnitudeStructure M] : Prop where
  numerator : ∀ {a b c : M},
    Positive a → Positive b → Positive c → Less b a →
    ∃ m n : Nat, 0 < m ∧ 0 < n ∧
      Less (Multiple n c) (Multiple m a) ∧
      Le (Multiple m b) (Multiple n c)
  denominator : ∀ {a b c : M},
    Positive a → Positive b → Positive c → Less b a →
    ∃ m n : Nat, 0 < m ∧ 0 < n ∧
      Less (Multiple n b) (Multiple m c) ∧
      Le (Multiple m c) (Multiple n a)

variable {M N P : Type}

section Basic
variable [MagnitudeStructure M] [A : MagnitudeAxioms M]

theorem addZeroLeft (a : M) : Add Zero a = a := by
  calc Add Zero a = Add a Zero := A.addComm _ _
       _ = a := A.addZeroRight _

theorem addCancelLeft {a b c : M} (h : Add c a = Add c b) : a = b := by
  apply A.addCancelRight (c := c)
  calc Add a c = Add c a := A.addComm _ _
       _ = Add c b := h
       _ = Add b c := A.addComm _ _

theorem addLtAddLeft {a b : M} (c : M) (h : Less a b) :
    Less (Add c a) (Add c b) := by
  have h0 := A.addLtAddRight c h
  simpa [A.addComm a c, A.addComm b c] using h0

theorem addLtCancelLeft {a b c : M} (h : Less (Add c a) (Add c b)) :
    Less a b := by
  apply A.addLtCancelRight (c := c)
  simpa [A.addComm a c, A.addComm b c] using h

theorem addLtAdd {a b c d : M} (hab : Less a b) (hcd : Less c d) :
    Less (Add a c) (Add b d) := by
  have h1 : Less (Add a c) (Add b c) := A.addLtAddRight c hab
  have h2 : Less (Add b c) (Add b d) := addLtAddLeft b hcd
  exact A.ltTrans h1 h2

theorem addFourRearrange (a b c d : M) :
    Add (Add a b) (Add c d) = Add (Add a c) (Add b d) := by
  calc
    Add (Add a b) (Add c d) = Add a (Add b (Add c d)) := A.addAssoc _ _ _
    _ = Add a (Add c (Add b d)) := by
      apply congrArg (fun x => Add a x)
      calc
        Add b (Add c d) = Add (Add b c) d := (A.addAssoc _ _ _).symm
        _ = Add (Add c b) d := by rw [A.addComm b c]
        _ = Add c (Add b d) := A.addAssoc _ _ _
    _ = Add (Add a c) (Add b d) := (A.addAssoc _ _ _).symm

theorem less_not_eq {a b : M} (h : Less a b) : a ≠ b := by
  intro e
  subst b
  exact A.ltIrrefl a h

theorem less_asymm {a b : M} (h : Less a b) : ¬ Less b a := by
  intro hba
  exact A.ltIrrefl a (A.ltTrans h hba)

theorem le_of_not_greater {a b : M} (h : ¬ Less b a) : Le a b := by
  rcases A.ltTrichotomy a b with hab | hab | hba
  · exact Or.inr hab
  · exact Or.inl hab
  · exact False.elim (h hba)

theorem multiple_zero (n : Nat) : Multiple n (Zero : M) = Zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Multiple]
      rw [ih]
      exact addZeroLeft Zero

theorem multiple_one (a : M) : Multiple 1 a = a := by
  simp [Multiple, addZeroLeft]

theorem multiple_add_index (m n : Nat) (a : M) :
    Multiple (m+n) a = Add (Multiple m a) (Multiple n a) := by
  induction n with
  | zero => simp [Multiple, A.addZeroRight]
  | succ n ih =>
      rw [Nat.add_succ]
      simp only [Multiple]
      calc
        Add (Multiple (m+n) a) a
            = Add (Add (Multiple m a) (Multiple n a)) a := by rw [ih]
        _ = Add (Multiple m a) (Add (Multiple n a) a) := A.addAssoc _ _ _

theorem multiple_add (n : Nat) (a b : M) :
    Multiple n (Add a b) = Add (Multiple n a) (Multiple n b) := by
  induction n with
  | zero => simp [Multiple, addZeroLeft]
  | succ n ih =>
      simp only [Multiple]
      calc
        Add (Multiple n (Add a b)) (Add a b)
            = Add (Add (Multiple n a) (Multiple n b)) (Add a b) := by rw [ih]
        _ = Add (Add (Multiple n a) a) (Add (Multiple n b) b) :=
          addFourRearrange _ _ _ _

theorem multiple_multiple (m n : Nat) (a : M) :
    Multiple m (Multiple n a) = Multiple (m*n) a := by
  induction m with
  | zero => simp [Multiple]
  | succ m ih =>
      simp only [Multiple]
      calc
        Add (Multiple m (Multiple n a)) (Multiple n a)
            = Add (Multiple (m*n) a) (Multiple n a) := by rw [ih]
        _ = Multiple (m*n+n) a := (multiple_add_index (m*n) n a).symm
        _ = Multiple ((m+1)*n) a := by simp [Nat.add_mul]

theorem multiple_positive_succ (n : Nat) {a : M} (ha : Positive a) :
    Positive (Multiple (n+1) a) := by
  induction n with
  | zero => simpa [multiple_one] using ha
  | succ n ih =>
      simpa [Multiple] using A.positiveAdd ih ha

theorem multiple_positive {n : Nat} {a : M} (hn : 0 < n) (ha : Positive a) :
    Positive (Multiple n a) := by
  rcases n with _ | n
  · exact False.elim (Nat.not_lt_zero 0 hn)
  · exact multiple_positive_succ n ha

theorem multiple_lt_multiple_succ (n : Nat) {a b : M} (hab : Less a b) :
    Less (Multiple (n+1) a) (Multiple (n+1) b) := by
  induction n with
  | zero => simpa [multiple_one] using hab
  | succ n ih =>
      simpa [Multiple] using addLtAdd ih hab

theorem multiple_lt_multiple {n : Nat} {a b : M}
    (hn : 0 < n) (hab : Less a b) : Less (Multiple n a) (Multiple n b) := by
  rcases n with _ | n
  · exact False.elim (Nat.not_lt_zero 0 hn)
  · exact multiple_lt_multiple_succ n hab

theorem multiple_eq_reflect {n : Nat} {a b : M}
    (hn : 0 < n) (h : Multiple n a = Multiple n b) : a = b := by
  rcases A.ltTrichotomy a b with hab | hab | hba
  · have hh := multiple_lt_multiple hn hab
    rw [h] at hh
    exact False.elim (A.ltIrrefl _ hh)
  · exact hab
  · have hh := multiple_lt_multiple hn hba
    rw [h] at hh
    exact False.elim (A.ltIrrefl _ hh)

theorem multiple_compare_reflect {n : Nat} {a b : M}
    (hn : 0 < n) : Less (Multiple n a) (Multiple n b) ↔ Less a b := by
  constructor
  · intro h
    rcases A.ltTrichotomy a b with hab | hab | hba
    · exact hab
    · subst b; exact False.elim (A.ltIrrefl _ h)
    · have hh := multiple_lt_multiple hn hba
      exact False.elim (less_asymm h hh)
  · exact multiple_lt_multiple hn

theorem hasRatio_of_positive {a b : M} (ha : Positive a) (hb : Positive b) :
    HasRatio a b := by
  obtain ⟨m, hm, hbm⟩ := A.archimedean ha hb
  obtain ⟨n, hn, han⟩ := A.archimedean hb ha
  exact ⟨ha, hb, ⟨m, hm, hbm⟩, ⟨n, hn, han⟩⟩

theorem split_multiple_of_lt {m n : Nat} (h : m < n) (a : M) :
    ∃ k : Nat, 0 < k ∧ Multiple n a = Add (Multiple m a) (Multiple k a) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt h)
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst k
      simp at hk
      exact False.elim ((Nat.ne_of_lt h) hk.symm)
    · exact hkpos
  refine ⟨k, hkpos, ?_⟩
  rw [hk]
  exact multiple_add_index m k a

end Basic

section RatioLogic
variable [MagnitudeStructure M] [MagnitudeStructure N] [MagnitudeStructure P]

theorem sameRatio_refl (a b : M) : SameRatio a b a b := by
  intro m n hm hn
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem sameRatio_symm {a b : M} {c d : N}
    (h : SameRatio a b c d) : SameRatio c d a b := by
  intro m n hm hn
  obtain ⟨hg, he, hl⟩ := h m n hm hn
  exact ⟨hg.symm, he.symm, hl.symm⟩

theorem sameRatio_congr_left {a b a' b' : M} {c d : N}
    (haa : a = a') (hbb : b = b') (h : SameRatio a b c d) :
    SameRatio a' b' c d := by
  subst a'; subst b'; exact h

theorem sameRatio_congr_right {a b : M} {c d c' d' : N}
    (hcc : c = c') (hdd : d = d') (h : SameRatio a b c d) :
    SameRatio a b c' d' := by
  subst c'; subst d'; exact h

theorem sameRatio_not_greater [AN : MagnitudeAxioms N]
    {a b : M} {c d : N} (h : SameRatio a b c d) :
    ¬ GreaterRatio a b c d := by
  intro hg
  obtain ⟨m,n,hm,hn,hab,hcd⟩ := hg
  have hcgt : Less (Multiple n d) (Multiple m c) := (h m n hm hn).1.mp hab
  rcases hcd with heq | hlt
  · rw [heq] at hcgt
    exact AN.ltIrrefl _ hcgt
  · exact AN.ltIrrefl _ (AN.ltTrans hlt hcgt)

end RatioLogic

end Euclid.Book5
