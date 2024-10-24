

import Mathlib.Tactic
import Leantest.Basic

open TopologicalSpace

-- topología de los complementarios abiertos

-- neccessary notions: complementary of sets, finite sets

def TopFC : TopologicalSpace ℝ where
  IsOpen (U : Set ℝ) := Set.Finite (Uᶜ)

  isOpen_univ := by
    have h : Set.univᶜ = ∅


    -- esto se debería poder hacer con refine Set.compl_univ
    -- pero no me deja
    · ext x
      apply Iff.intro
      · intro h
        simp at h
      · intro h
        simp
        exact h

    rw [h]
    exact Set.finite_empty

  isOpen_inter := by
    intro U V hU hV
    rw [Set.compl_inter U V]
    exact Set.Finite.union hU hV

  isOpen_sUnion := by
    intro S hS
    rw [Set.compl_sUnion]
    have h : (∃ t, t ∈ S) ∨ (¬ ∃ t, t ∈ S)
    exact Classical.em (∃ t, t ∈ S)

    cases' h with h1 h2

    cases' h1 with t ht
    specialize hS t ht
    have ht2 : tᶜ ∈ compl '' S
    simp
    exact ht
    exact Set.Finite.sInter ht2 hS

    have hS2 : S = ∅
    exact Set.not_nonempty_iff_eq_empty.mp h2
    rw [Set.image_eq_empty.mpr hS2]
    have hS3 : ⋂₀ ∅ = ∅
    ext x
    apply Iff.intro
    intro h

    sorry

    intro h
    by_contra
    exact h






example (U V : Set ℝ) : (U ∩ V)ᶜ = Uᶜ ∪ Vᶜ := by
  exact Set.compl_inter U V

example (S : Set (Set ℝ)) : (⋃₀ S)ᶜ = ⋂₀ (S.image compl) := by
  exact Set.compl_sUnion S

example (U V : Set ℝ) : (U.Finite ∧ V.Finite) → (U ∩ V).Finite  := by
  intro h
  cases' h with hU hV
  exact Set.Finite.inter_of_right hV U

example (P: Prop) : P ∨ ¬ P := by
  exact Classical.em P

example (P Q: Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  exact not_or

example (X : Type) (S : Set (Set X)) (x : X) (hx : x ∈ ⋂₀ S) : ∀ t ∈ S, x ∈ t := by
  exact fun t a ↦ hx t a

example (S : Set (Set ℝ)) (hS : ∃ t ∈ S, t.Finite) : (⋂₀ S).Finite := by
  sorry

example (S : Set (Set ℝ)) (hS : S = ∅) : (⋂₀S).Finite := by
  sorry
