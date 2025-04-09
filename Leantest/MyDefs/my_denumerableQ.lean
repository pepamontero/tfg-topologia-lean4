import Mathlib.Tactic

def Q : Set ℚ := {q : ℚ | 0 ≤ q ∧ q ≤ 1} -- `ℚ ∩ [0, 1]`

lemma Q1 : 1 ∈ Q := by simp [Q]
lemma Q0 : 0 ∈ Q := by simp [Q]

lemma hf : ∃ f : ℕ → Q, (f.Bijective ∧ f 0 = ⟨1, Q1⟩  ∧ f 1 = ⟨0, Q0⟩) := by
  sorry

noncomputable def f : ℕ → Q := Classical.choose hf

lemma f_prop : (f.Bijective ∧ f 0 = ⟨1, Q1⟩  ∧ f 1 = ⟨0, Q0⟩) := by
  let hf := Classical.choose_spec hf
  exact hf

lemma f_in_icc01 : ∀ n : ℕ, ⟨0, Q0⟩ ≤ f n ∧ f n ≤ ⟨1, Q1⟩ := by
  intro n
  constructor
  · exact (f n).property.left -- x.property handles membership, here f n is recognized as an element of Q
  · exact (f n).property.right


lemma f_has_inverse :  ∃ g, Function.LeftInverse g f ∧ Function.RightInverse g f
  := by
  rw [← Function.bijective_iff_has_inverse]
  exact f_prop.left

noncomputable def f_inv : Q → ℕ := Classical.choose f_has_inverse

lemma f_inv_prop : (∀ n : ℕ, f_inv (f n) = n) ∧
    (∀ q : Q, f (f_inv q) = q) := by
  let h := Classical.choose_spec f_has_inverse
  exact h

lemma f_inv_0 : f_inv ⟨0, Q0⟩ = 1 := by
  apply f_prop.left.left
  rw [f_inv_prop.right ⟨0, Q0⟩]
  exact f_prop.right.right.symm

lemma f_inv_1 : f_inv ⟨1, Q1⟩ = 0 := by
  apply f_prop.left.left
  rw [f_inv_prop.right ⟨1, Q1⟩]
  exact f_prop.right.left.symm
