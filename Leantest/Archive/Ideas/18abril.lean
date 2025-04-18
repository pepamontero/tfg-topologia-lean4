import Leantest.Separation.def_G



def lt_pair : (ℕ × ℕ) → (ℕ × ℕ) → Prop := Prod.Lex (Nat.lt) (Nat.lt)
def lt_pair_wfr : WellFoundedRelation (ℕ × ℕ) := Prod.lex (Nat.lt_wfRel) (Nat.lt_wfRel)
lemma lt_pair_wf : WellFounded lt_pair := lt_pair_wfr.wf



lemma lt_pair_def (n m i j : ℕ)
    : lt_pair (n, m) (i, j) ↔ n < i ∨ (n = i ∧ m < j):= by
  constructor

  · intro h

    have cases : n < i ∨ i ≤ n := by exact Nat.lt_or_ge n i
    cases' cases with hni hni

    · -- n < i
      left
      exact hni

    have cases : i < n ∨ i = n := by exact Or.symm (Nat.eq_or_lt_of_le hni)
    cases' cases with hni hni

    · -- i < n
      apply (@Prod.Lex.left ℕ ℕ Nat.lt Nat.lt i j n m) at hni
      apply @WellFoundedRelation.asymmetric (ℕ × ℕ) lt_pair_wfr at hni
      by_contra
      exact hni h

    · -- i = n
      simp [hni]

      have cases : m < j ∨ j ≤ m := by exact Nat.lt_or_ge m j
      cases' cases with hmj hmj

      · -- m < j
        exact hmj

      have cases : j < m ∨ j = m := by exact Or.symm (Nat.eq_or_lt_of_le hmj)
      cases' cases with hmj hmj

      · -- j < m
        rw [hni] at h

        apply (@Prod.Lex.right ℕ ℕ Nat.lt Nat.lt n) at hmj
        apply @WellFoundedRelation.asymmetric (ℕ × ℕ) lt_pair_wfr at hmj
        by_contra
        exact hmj h

      · -- j = m
        rw [hni, hmj] at h
        by_contra
        have h' := h
        apply @WellFoundedRelation.asymmetric (ℕ × ℕ) lt_pair_wfr at h'
        exact h' h

  · intro h
    cases' h with h h
    · apply Prod.Lex.left
      exact h
    · rw [h.left]
      apply Prod.Lex.right
      exact h.right




example {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n m, f n < f m → Closure (G hT C1 C2 n) ⊆ G hT C1 C2 m := by

  intro n m
  let P : ℕ × ℕ → Prop := fun (n, m) ↦ (f n < f m → Closure (G hT C1 C2 n) ⊆ G hT C1 C2 m)
  have P_def : P (n, m) = (f n < f m → Closure (G hT C1 C2 n) ⊆ G hT C1 C2 m) := by rfl
  rw [← P_def]
  apply WellFounded.induction lt_pair_wf
  simp [P]

  intro n m
  intro hi hnm
  simp [lt_pair] at hi

  have n_neq_m : n ≠ m
  · by_contra c
    simp [c] at hnm

  have lema1 : n ≠ 0
  · by_contra c
    apply congrArg f at c
    rw [f_prop.right.left] at c
    rw [c] at hnm
    have f_prop := (f_in_icc01 m).right
    exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false hnm f_prop

  have lema2 : m ≠ 1
  · by_contra c
    apply congrArg f at c
    rw [f_prop.right.right] at c
    rw [c] at hnm
    have f_prop := (f_in_icc01 n).left
    exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false hnm f_prop

  have C_normal_pair : normal_pair (C2ᶜ, C1)
  · exact ⟨hC2, hC1, hC1C2⟩

  have G_Prop2 := G_Prop2 hT C1 C2 hC1 hC2 hC1C2

  have cases : n = 0 ∨ n > 0 := by exact Nat.eq_zero_or_pos n
  cases' cases with hn0 hn0

  · -- caso n = 0 (imposible)
    simp [hn0] at lema1

  · -- caso n > 0
    have cases : m = 0 ∨ m > 0 := by exact Nat.eq_zero_or_pos m
    cases' cases with hm0 hm0

    · -- caso n > 0, m = 0
      have cases : n = 1 ∨ n > 1 := by exact LE.le.eq_or_gt hn0
      cases' cases with hn1 hn1

      · -- caso n = 1, m = 0
        simp [hn1, hm0, G, from_normality, C_normal_pair]
        exact (Classical.choose_spec (hT C2ᶜ C1 hC2 hC1 hC1C2)).right.right

      · -- caso n > 1, m = 0
        -- inducción completa sobre n

        revert hnm hn1
        rw [hm0]

        apply my_strong_induction n

        intro n hi _ hn1

        have s_options := s_options n hn1
        cases' s_options with hs0 hs1

        · -- caso s(n) = 0
          rw [← hs0]
          exact (G_Prop2 n hn1).right

        · -- caso s(n) > 1
          trans Closure (G hT C1 C2 (s n))
          · trans G hT C1 C2 (s n)
            · exact (G_Prop2 n hn1).right
            · exact set_inside_closure (G hT C1 C2 (s n))

          · have s_prop := (s_prop n hn1).left
            simp at s_prop
            have aux : f (s n) < f 0
            · simp [f_prop]
              apply lt_of_le_of_ne (f_in_icc01 (s n)).right
              rw [← f_prop.right.left]
              by_contra c
              apply f_prop.left.left at c
              simp [c] at hs1
            exact hi (s n) s_prop aux hs1


    · -- caso n > 0, m > 0
      have cases : m = 1 ∨ m > 1 := by exact LE.le.eq_or_gt hm0
      cases' cases with hm1 hm1

      · -- caso n > 0, m = 1 (imposible)
        simp [hm1] at lema2

      · -- caso n > 0, m > 1
        have cases : n = 1 ∨ n > 1 := by exact LE.le.eq_or_gt hn0
        cases' cases with hn1 hn1

        · -- caso n = 1, m > 1
          -- inducción sobre m

          revert hnm hm1
          rw [hn1]

          apply my_strong_induction m

          intro m hi _ hm1

          have r_options := r_options m hm1
          cases' r_options with hr1 hr1

          · -- caso r(m) = 1
            rw [← hr1]
            exact (G_Prop2 m hm1).left

          · -- caso r(m) > 1
            trans G hT C1 C2 (r m)
            · have r_prop := (r_prop m hm1).left
              simp at r_prop
              have aux : f 1 < f (r m)
              · simp [f_prop]
                apply lt_of_le_of_ne (f_in_icc01 (r m)).left
                rw [← f_prop.right.right]
                by_contra c
                apply f_prop.left.left at c
                simp [c] at hr1
              exact hi (r m) r_prop aux hr1

            · trans Closure (G hT C1 C2 (r m))
              · exact set_inside_closure (G hT C1 C2 (r m))
              · exact (G_Prop2 m hm1).left


        · -- caso n > 1, m > 1

          have s_prop := s_prop n hn1
          have r_prop := r_prop m hm1
          simp at s_prop r_prop

          have cases : f (s n) < f m ∨ f m ≤ f (s n) := by exact lt_or_le (f (s n)) (f m)
          cases' cases with h h

          · -- si f (s n) < f m
            trans Closure (G hT C1 C2 (s n))
            · trans G hT C1 C2 (s n)
              · exact (G_Prop2 n hn1).right
              · exact set_inside_closure (G hT C1 C2 (s n))
            · exact hi (s n) m (by left; exact s_prop.left) h

          have cases : f m = f (s n) ∨ f m < f (s n)  := by exact (lt_or_eq_of_le h).symm
          cases' cases with h h

          · -- si f (s n) = f m
            apply f_prop.left.left at h
            rw [h]
            exact (G_Prop2 n hn1).right

          · -- si f m < f (s n)

            have cases : f n < f (r m) ∨ f (r m) ≤ f n := by exact lt_or_le (f n) (f (r m))
            cases' cases with h' h'

            · -- si f n < f (r m)
              trans G hT C1 C2 (r m)
              · exact hi n (r m) (by right; simp; exact r_prop.left) h'
              · trans Closure (G hT C1 C2 (r m))
                · exact set_inside_closure (G hT C1 C2 (r m))
                · exact (G_Prop2 m hm1).left


            have cases : f (r m) = f n ∨ f (r m) < f n := by exact (lt_or_eq_of_le h').symm
            cases' cases with h' h'

            · -- si f n = f (r m)
              apply f_prop.left.left at h'
              rw [← h']
              exact (G_Prop2 m hm1).left

            · -- si f (r m) < f n (imposible!)
              have aux : n < m
              · by_contra c
                simp at c
                apply lt_of_le_of_ne at c
                specialize c n_neq_m.symm
                have aux := s_prop.right.right
                specialize aux m c hnm
                apply not_lt.mpr at aux
                exact aux h

              by_contra
              have aux' := r_prop.right.right
              specialize aux' n aux hnm
              apply not_lt.mpr at aux'
              exact aux' h'
