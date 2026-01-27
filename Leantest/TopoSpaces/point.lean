import Mathlib.Tactic


-- point topology

open TopologicalSpace

lemma Set.inter_of_empty_left {X : Type} {A B : Set X} (hA : A = ∅) : A ∩ B = ∅ := by
  ext x
  constructor <;> intro hx
  rw [Set.mem_inter_iff] at hx
  rw [hA] at hx
  exact hx.left
  by_contra
  exact hx

lemma Set.inter_of_empty_right {X : Type} {A B : Set X} (hB : B = ∅) : A ∩ B = ∅ := by
  rw [Set.inter_comm]
  apply Set.inter_of_empty_left hB


lemma neg_left_or_then_right (P Q : Prop) (hP : ¬ P) (hPQ : P ∨ Q) : Q := by
  by_contra hQ
  cases' hPQ with h1 h2
  exact hP h1
  exact hQ h2



def PointTopology (X : Type) (a : X) : TopologicalSpace X where
  IsOpen (s : Set X) : Prop := a ∈ s ∨ s = ∅

  isOpen_univ := by
    dsimp
    left
    trivial
    -- or just simp

  isOpen_inter := by
    dsimp
    intro s t hs ht
    cases' hs with hs hs
    · cases' ht with ht ht
      · left
        exact Set.mem_inter hs ht
      · right
        exact Set.inter_of_empty_right ht
    · right
      exact Set.inter_of_empty_left hs

  isOpen_sUnion := by
    dsimp
    intro S hS

    have c : (∃ t ∈ S, a ∈ t) ∨ ¬ (∃ t ∈ S, a ∈ t)
    exact Classical.em (∃ t ∈ S, a ∈ t)

    cases' c with c c
    · left
      exact c
    · right
      rw [not_exists] at c

      have h : ∀ t ∈ S, t = ∅
      · intro t ht
        specialize hS t ht
        specialize c t
        rw [Classical.not_and_iff_or_not_not] at c
        apply neg_left_or_then_right at c
        apply neg_left_or_then_right at hS
        exact hS
        exact c
        simp
        exact ht

      simp
      exact h
