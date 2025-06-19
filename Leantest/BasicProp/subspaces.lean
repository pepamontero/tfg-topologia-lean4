import Leantest.BasicProp.basic
import Leantest.TopoSpaces.usual

/-
  DEF: Topological subspace
Note: needs proof that it is actually a topological space
-/

def TopoSubspace {X : Type} (T : TopologicalSpace X) (Y : Set X) :
  TopologicalSpace Y where

  IsOpen (V : Set Y) := ∃ U : Set X, T.IsOpen U ∧ V = U ∩ Y
  isOpen_univ := by
    use (Set.univ : Set X)
    constructor
    · exact T.isOpen_univ
    · simp
  isOpen_inter := by
    intro V1 V2 h1 h2
    obtain ⟨U1, h1open, h1inter⟩ := h1
    obtain ⟨U2, h2open, h2inter⟩ := h2
    use U1 ∩ U2
    constructor
    · exact T.isOpen_inter U1 U2 h1open h2open
    · simp
      rw [h1inter, h2inter]
      exact Eq.symm (Set.inter_inter_distrib_right U1 U2 Y)
  isOpen_sUnion := by
    intro S hS

    -- tomamos S' = ∪_i V_i, los V_i de la def. de ab. para cada t_i ∈ S
    use ⋃ t : S, Classical.choose (hS t t.property)
    constructor
    · -- 1. S' es abierto
      apply T.isOpen_sUnion
      simp
      intro _ V hU hV
      obtain ⟨hUopen, _⟩ := Classical.choose_spec (hS V hU)
      rw [hV] at hUopen
      exact hUopen
    · -- 2. ⋃₀ S = S' ∩ Y
      ext x ; constructor <;> intro hx
      · simp at hx
        cases' hx with t ht
        cases' ht with ht ht'
        let hV := Classical.choose_spec (hS t ht)
        rw [Set.iUnion_inter]
        use t
        constructor
        · rw [hV.right]
          simp
          use t
          use ht
        · simp
          exact ht'

      · simp at hx
        cases' hx with hx' hx
        cases' hx' with t ht
        cases' ht with ht hx'
        let hV := Classical.choose_spec (hS t ht)

        have aux : x ∈ (t : Set X)
        · rw [hV.right]
          constructor
          · exact hx'
          · exact hx

        simp
        use t
        constructor
        · exact ht
        · use hx
          exact Set.mem_of_mem_image_val aux


/-
Example: [0, b) is open for b < 1 in [0, 1]
seen as a topological subspace of ℝ with the usual topology
-/

lemma ico_open_in_Icc01 {Y : Set ℝ}
    {hY : Y = Set.Icc 0 1}
    {R : TopologicalSpace Y}
    {hR : R = TopoSubspace UsualTopology Y}
    (b : ℝ) (hb : 0 < b ∧ b < 1) :
    R.IsOpen ({y | (y : ℝ) ∈ Set.Ico 0 b} : Set Y) := by

  rw [hR] -- usar la topo. del subesp.
  rw [UsualTopology] -- usar la def. de T_u
  use ((Set.Ioo (-1) b) : Set ℝ)
  constructor
  · exact ioo_open_in_R (-1) b
  · ext x; constructor
    all_goals
      intro hx
      simp at * -- convertirlo todo a inecuaciones
      constructor
      · simp [hY] at hx
        constructor
        all_goals linarith
      · exact hx.right



lemma ioc_open_in_Icc01 {Y : Set ℝ}
    {hY : Y = Set.Icc 0 1}
    {R : TopologicalSpace Y}
    {hR : R = TopoSubspace UsualTopology Y}
    (b : ℝ) (hb2 : 0 < b ∧ b < 1) :
    R.IsOpen ({y | (y : ℝ) ∈ Set.Ioc b 1} : Set Y) := by

  rw [hR] -- usar la topo. del subesp.
  rw [UsualTopology] -- usar la def. de T_u
  use ((Set.Ioo b 2) : Set ℝ)


  constructor
  · exact ioo_open_in_R b 2
  · ext x; constructor
    all_goals
      intro hx
      simp at * -- convertirlo todo a inecuaciones
      constructor
      · simp [hY] at hx
        constructor
        all_goals linarith
      · exact hx.right
