import Leantest.Archive.Ideas.well_founded
import Leantest.Separation.normal

#check wf_R
#check wf_S

#check WellFounded.induction

example {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    (G : ℕ → Set X)
    (hG0 : G 0 = C2ᶜ)
    (hG1 : G 1 = Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2))
    (hGOpen : ∀ n, IsOpen (G n))
    (hG: ∀ n > 1,
        (Closure (G (r n)) ⊆ G n) ∧
        (Closure (G n) ⊆ G (s n))
    )

    :

    ∀ n, ∀ m, f n < f m → Closure (G n) ⊆ G m

     := by

  intro n m hnm

  have U :

  apply WellFounded.induction R_is_wf
