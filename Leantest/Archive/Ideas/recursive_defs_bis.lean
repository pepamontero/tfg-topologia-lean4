
import Leantest.Separation.normal
import Leantest.MyDefs.my_rs_functions

#check characterization_of_normal

lemma hT {X : Type} [T : TopologicalSpace X] (h : NormalTopoSpace T) :
    ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U := by
  rw [← characterization_of_normal]
  exact h


def get_V {X : Type} [T : TopologicalSpace X] (normalT : NormalTopoSpace T)
    {U C: Set X}
    (hU : IsOpen U) (hC : IsClosed C)
    (hCU : C ⊆ U)
    : Set X
    := Classical.choose (hT normalT U C hU hC hCU)

def get_V_spec {X : Type} [T : TopologicalSpace X] (normalT : NormalTopoSpace T)
    {U C: Set X}
    (hU : IsOpen U) (hC : IsClosed C)
    (hCU : C ⊆ U)
    := Classical.choose_spec (hT normalT U C hU hC hCU)

lemma V_prop {X : Type} [T : TopologicalSpace X] (normalT : NormalTopoSpace T)
    {U C: Set X}
    (hU : IsOpen U) (hC : IsClosed C)
    (hCU : C ⊆ U)
    := IsOpen (get_V normalT hU hC hCU)




def G
  {X : Type} [T : TopologicalSpace X] (normalT : NormalTopoSpace T)
  {C1 C2 : Set X}
  (hC1 : IsClosed C1)
  (hC2 : IsOpen C2ᶜ)
  (hC : C1 ⊆ C2ᶜ)

    : ℕ → Set X × Prop
    := fun n ↦

  if n = 0 then (C2ᶜ, IsOpen C2ᶜ)
  else if n = 1 then ((get_V normalT hC2 hC1 hC), true)
  else ((get_V normalT hC2 hC1 hC), get_V_spec normalT hC2 hC1 hC)
