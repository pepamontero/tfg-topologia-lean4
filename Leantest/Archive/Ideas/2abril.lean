import Leantest.Separation.def_G

#check G
#check G_Prop1 -- G n is open for all n
#check G_Prop2 -- G r n ⊆ G n ⊆ G s n



example {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC : normal_pair (C2ᶜ, C1))

    (n : ℕ)
    (h : f n < f (n+1))
    :
    Closure (G hT C1 C2 n) ⊆ G hT C1 C2 (n+1)

    := by

  let Q : ℕ → Prop := fun m ↦ (f m < f (m+1))

  apply my_stronger_induction n Q
  · exact h
  simp [Q]
  intro n h hi

  have cases : n = 0 ∨ n > 0 := by exact Nat.eq_zero_or_pos n
  cases' cases with hn hn

  · -- n = 0
    simp [hn] at h
    simp [f_prop] at h
    by_contra
    exact (Bool.eq_not_self ((1).blt ↑0)).mp h

  · -- n > 0

    /-

    creo que esto no tiene sentido-/
    sorry
