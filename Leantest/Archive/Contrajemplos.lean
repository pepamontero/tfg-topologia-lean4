import Mathlib.Tactic

open TopologicalSpace

variable (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]

-- S es un subconjunto de X
variable (S : Set X)

-- `f : X → Y` es una función
variable (f : X → Y)



example (hf : Continuous f) (hS : IsCompact S) : IsCompact (f '' S) := by
  rw [isCompact_iff_finite_subcover] at *
  intros τ U hU hUS


  have ig:(f ⁻¹' (⋃ (i:τ), (U i))) = (⋃ (i:τ), (f ⁻¹' (U i)))  := by
    rw [Set.preimage_iUnion]

  have S_cont: S ⊆  (⋃ (i:τ), (f ⁻¹' (U i))) := by
    rw [← ig]
    rw [← Set.image_subset_iff]
    exact hUS

  -- Lo mismo que antes pero S_cont se sigue llamando hUS
  -- rw [Set.image_subset_iff,Set.preimage_iUnion] at hUS

  have existe:=hS (fun i => f ⁻¹' (U i)) (fun i => hf.isOpen_preimage (U i) (hU i)) S_cont
  obtain ⟨t, ht⟩ := existe
  use t
  rw [Set.image_subset_iff]
  have ig: (⋃ i ∈ t, (fun i ↦ f ⁻¹' U i) i) = (⋃ i ∈ t, f ⁻¹' U i) := by
    rfl
  rw [ig] at ht
  rw [← Set.preimage_iUnion₂] at ht

  -- have ig2: (⋃ i ∈ t, f ⁻¹' U i) = f ⁻¹' (⋃ i ∈ t, U i) := by
  --  rw [← Set.preimage_iUnion₂]
  --  rw [ig2] at ht
  -- rw [← Set.preimage_iUnion₂]
  exact ht
  done

example (hf : Continuous f) (hS : IsCompact S) : IsCompact (f '' S) := by
  rw [isCompact_iff_finite_subcover] at *
  intros τ U hU hUS


  have ig:(f ⁻¹' (⋃ (i:τ), (U i))) = (⋃ (i:τ), (f ⁻¹' (U i)))  := by
    rw [Set.preimage_iUnion]

  have S_cont: S ⊆  (⋃ (i:τ), (f ⁻¹' (U i))) := by
    rw [← ig]
    rw [← Set.image_subset_iff]
    exact hUS

  -- Lo mismo que antes pero S_cont se sigue llamando hUS
  -- rw [Set.image_subset_iff,Set.preimage_iUnion] at hUS
  -- no funciona ¿??¿?

  have existe:=hS (fun i => f ⁻¹' (U i)) (fun i => hf.isOpen_preimage (U i) (hU i)) S_cont
  obtain ⟨t, ht⟩ := existe
  use t

  simp only [Set.image_subset_iff, Set.preimage_iUnion₂]
  exact ht
  done

-- mi versión

example (hf : Continuous f) (hS : IsCompact S) : IsCompact (f '' S) := by
  rw [isCompact_iff_finite_subcover] at *

  intros ι U hU hR

  let V : ι → Set X := λ i => f ⁻¹' (U i)

  have hV : ∀ (i : ι), IsOpen (V i)
  intro i
  specialize hU i
  exact hf.isOpen_preimage (U i) hU

  have hS2 : S ⊆ ⋃ i, V i
  sorry

  specialize hS V hV hS2-- no tengo que poner ι porque lo deduce
  cases' hS with t ht
  use t

  have h1 : f '' S ⊆ f '' (⋃ i ∈ t, V i)
  exact Set.image_mono ht

  rw [Set.image_iUnion₂ f fun i j ↦ V i] at h1

  have Vdef : ∀ (i : ι), V i = f ⁻¹' (U i)
  intro i
  trivial

  have h2 : ∀ (i : ι), f '' V i ⊆ U i
  intro i
  rw [Vdef]
  exact Set.image_preimage_subset f (U i)

  intros x hx
  apply h1 at hx
  sorry




  rw [Vdef] at h1


  rw [h2] at h1





  sorry


example (A : Set X) (B : Set Y) (h : f '' A ⊆ B) : A ⊆ f ⁻¹' B := by
  exact Set.image_subset_iff.mp h

example (hf : Continuous f) (A : Set X) : f ⁻¹' (f '' A) ⊆ A := by
  intros x hx


example (hf : Continuous f) (V : Set Y) (hV : IsOpen V) : IsOpen (f ⁻¹' V) := by
  exact hf.isOpen_preimage V hV

def Sorgenfrey : TopologicalSpace ℝ where
  IsOpen (s:Set ℝ) :=  ∀ x ∈ s, ∃ δ > 0, Set.Ico x (x + δ) ⊆ s
  isOpen_univ:= by
    intro x hx
    use 2
    constructor
    linarith
    have result:= Set.subset_univ (Set.Ico x (x + 2))
    exact result
  isOpen_inter := by
    intros s t hs ht x hx
    obtain ⟨δ, hδ, h⟩ := hs x hx.left
    obtain ⟨ε, hε, h'⟩ := ht x hx.right
    use min δ ε
    constructor
    exact lt_min hδ hε
    have subcongr: Set.Ico x (x + min δ ε) ⊆  Set.Ico x (x + ε):=by
      intro y
      intro hy
      have left :=hy.left
      have right :=hy.right
      have hmin: (min δ ε) <= ε
      exact min_le_right δ ε
      have rigth1: x + (min δ ε) <= (x + ε)
      exact add_le_add_left hmin x /-library_search-/
      constructor
      exact left
      exact lt_add_of_lt_add_left right hmin
    have subcongr': Set.Ico x (x + min δ ε) ⊆  Set.Ico x (x + δ):= by
      intro y
      intro hy
      have left :=hy.left
      have right :=hy.right
      have hmin: (min δ ε) <= δ
      exact min_le_left δ ε
      have rigth1: x + (min δ ε) <= (x + δ)
      exact add_le_add_left hmin x /-library_search-/
      constructor
      exact left
      exact lt_add_of_lt_add_left right hmin
    intro y
    intro hy
    constructor
    apply h
    apply subcongr'
    exact hy
    apply h'
    apply subcongr
    exact hy
  isOpen_sUnion := by
    intro F
    intro hF
    intro x hx
    obtain ⟨s, hs⟩ := hx
    have hs1:=hs.left
    have hx1:=hs.right
    have p:=hF s hs1 x hx1
    have s_sub:s ⊆ ⋃₀ F := by
      intro y
      intro hy
      use s
    obtain ⟨δ, hδ⟩ := p
    use δ
    constructor
    exact hδ.left
    intro y
    intro hy
    apply s_sub
    apply hδ.right
    exact hy


def SorgenfreyPepa : TopologicalSpace ℝ where
  IsOpen (s : Set ℝ) :=  ∀ x ∈ s, ∃ δ > 0, Set.Ico x (x + δ) ⊆ s
  isOpen_univ:= by
    intros x hx
    use 1
    apply And.intro
    norm_num
    exact fun ⦃a⦄ a ↦ hx -- no se por que esto funciona pero vale

  isOpen_inter := by
    intros U V hU hV x hx
    rw [Set.mem_inter_iff] at hx
    specialize hU x hx.left
    specialize hV x hx.right
    cases' hU with δ1 h1
    cases' hV with δ2 h2
    use min δ1 δ2
    apply And.intro
    exact lt_min h1.left h2.left

    intros y hy
    rw [Set.mem_inter_iff]
    apply And.intro

    cases' h1 with h1 h11

    apply h11
    rw [Set.mem_Ico] at *
    apply And.intro
    exact hy.left
    have aux : x + min δ1 δ2 ≤ x + δ1
    simp
    linarith

    cases' h2 with h2 h22

    apply h22
    rw [Set.mem_Ico] at *
    apply And.intro
    exact hy.left
    have aux : x + min δ1 δ2 ≤ x + δ2
    simp
    linarith

  isOpen_sUnion := by
    intros U hU x hx
    cases' hx with S hS
    specialize hU S hS.left x hS.right
    cases' hU with δ hδ
    use δ
    apply And.intro
    exact hδ.left

    have h : S ⊆ ⋃₀ U
    exact Set.subset_sUnion_of_subset U S (fun ⦃a⦄ a ↦ a) hS.left

    apply Set.Subset.trans hδ.right h

example (x y : ℝ) (hx : x > 0) (hy : y > 0) : min x y > 0 := by
  exact lt_min hx hy

example (x y : ℝ) : min x y <= x := by
  exact min_le_left x y

example (U : Set (Set ℝ)) (S : Set ℝ) (hS : S ∈ U) : S ⊆ ⋃₀ U := by
  exact Set.subset_sUnion_of_subset U S (fun ⦃a⦄ a ↦ a) hS
