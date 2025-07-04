import Leantest.Continuous.basic
import Leantest.TopoSpaces.discrete
import Leantest.TopoSpaces.trivial
import Leantest.TopoSpaces.usual
import Leantest.TopoSpaces.sorgenfrey

#check DiscreteTopo
#check TrivialTopology
#check Sorgenfrey
#check UsualTopology


lemma continuous_from_discrete {X Y : Type}
    [T : TopologicalSpace X]
    [TopologicalSpace Y]
    (h : T = DiscreteTopo X)
    (f : X → Y) : Continuous f := by

  rw [continuous_def]
  intro U _

  -- aquí lo que hago es que le digo
  -- que estoy trabajando con la discreta
  rw [h, DiscreteTopo]
  -- (Aunque parezca que no hago nada)
  trivial


lemma continuous_to_trivial {X Y : Type}
    [TopologicalSpace X]
    [T : TopologicalSpace Y]
    (h : T = TrivialTopology Y)
    (f : X → Y) : Continuous f := by

  rw [continuous_def]
  intro U hU
  rw [h, TrivialTopology] at hU
  cases' hU with hUuniv hUempty

  · -- si U = Y
    rw [hUuniv]
    exact isOpen_univ

  · -- si U = ∅
    rw [hUempty]
    exact isOpen_empty


example [T1 : TopologicalSpace ℝ]
    [T2 : TopologicalSpace ℝ]
    (h1 : T1 = Sorgenfrey)
    (h2 : T2 = UsualTopology)
    (f : ℝ → ℝ := fun x ↦ x*x) : Continuous f := by

  rw [continuous_def]
  intro U hU

  rw [h2] at hU
  rw [UsualTopology] at hU

  sorry
  -- este ejemplo es bastante más difícil
