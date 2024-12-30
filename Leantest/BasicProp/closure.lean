import Leantest.BasicProp.basic

def Closure {X : Type} [T : TopologicalSpace X] (A : Set X) : Set X :=
    {x : X | ∀ V : Set X, Neighbourhood V x → V ∩ A ≠ ∅}


lemma set_inside_closure {X : Type} [T : TopologicalSpace X] (A : Set X) :
    A ⊆ Closure A := by

  intro x hx
  intro V hV
  by_contra hc

  have hc' : x ∈ V ∩ A
  constructor
  · cases' hV with U hU
    apply hU.left
    exact hU.right.left
  · exact hx

  rw [hc] at hc'
  exact hc'

lemma {X : Type} [T : TopologicalSpace X] (A : Set X) :
    (Closure A)ᶜ =

lemma closure_is_closed {X : Type} [T : TopologicalSpace X] (A : Set X) :
    IsClosed (Closure A) := by
  sorry
