import Leantest.Continuous.basic
import Leantest.TopoSpaces.discrete
import Leantest.TopoSpaces.trivial
import Leantest.TopoSpaces.usual
import Leantest.TopoSpaces.sorgenfrey

#check DiscreteTopo
#check ContinuousPepa
#check TrivialTopology
#check Sorgenfrey
#check UsualTopology


theorem continuous_from_discrete {X Y : Type}
    [T : TopologicalSpace X]
    [TopologicalSpace Y]
    (h : T = DiscreteTopo X)
    (f : X → Y) : ContinuousPepa f := by

  rw [ContinuousPepa]
  intro U hU

  -- aquí lo que hago es que le digo
  -- que estoy trabajando con la discreta
  rw [h]
  rw [DiscreteTopo]
  -- (Aunque parezca que no hago nada)

  trivial

lemma preimage_of_univ {X Y : Type}
    [TopologicalSpace X]
    [TopologicalSpace Y]
    (f : X → Y) : f ⁻¹' (Set.univ) = Set.univ := by
  ext x
  constructor
  <;> intro h
  trivial
  exact h

lemma preimage_of_empty {X Y : Type}
    [TopologicalSpace X]
    [TopologicalSpace Y]
    (f : X → Y) : f ⁻¹' (∅) = ∅ := by
  ext x
  constructor
  <;> intro h
  simp at h
  exact h

theorem continuous_to_trivial {X Y : Type}
    [TopologicalSpace X]
    [T: TopologicalSpace Y]
    (h : T = TrivialTopology Y)
    (f : X → Y) : ContinuousPepa f := by

  rw [ContinuousPepa]
  intro U hU

  rw [h] at hU
  rw [TrivialTopology] at hU

  cases' hU with hU hU

  · -- si U = Y
    rw [hU]
    rw [preimage_of_univ]
    exact isOpen_univ

  · -- si U = ∅
    rw [hU]
    rw [preimage_of_empty]
    exact isOpen_empty


example [T1 : TopologicalSpace ℝ]
    [T2 : TopologicalSpace ℝ]
    (h1 : T1 = Sorgenfrey)
    (h2 : T2 = UsualTopology)
    (f : ℝ → ℝ := fun x ↦ x*x) : ContinuousPepa f := by

  rw [ContinuousPepa]
  intro U hU

  rw [h2] at hU
  rw [UsualTopology] at hU

  sorry
  -- este ejemplo es bastante más difícil
