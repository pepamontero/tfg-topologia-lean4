import Leantest.Separation.normal
import Leantest.MyDefs.my_induction
import Leantest.MyDefs.my_rs_functions


---- LO QUE MOLARÍA TENER

lemma would_be_cool {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :
      ∃ G : ℕ → Set X, (
        (G 0 = C2ᶜ)
        ∧
        (G 1 = Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2))
        ∧
        (∀ n, IsOpen (G n))
        ∧
        (∀ n > 1, (Closure (G (r n)) ⊆ G n ∧ Closure (G n) ⊆ G (s n)))
        )
    := by
  sorry

noncomputable def G_cool {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ℕ → Set X := Classical.choose (would_be_cool hT C1 C2 hC1 hC2 hC1C2)

lemma cool_prop1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n : ℕ, IsOpen (G_cool hT C1 C2 hC1 hC2 hC1C2 n) := by

  intro n
  simp [G_cool]
  exact (Classical.choose_spec (would_be_cool hT C1 C2 hC1 hC2 hC1C2)).right.right.left n

lemma cool_prop2a {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    let G := G_cool hT C1 C2 hC1 hC2 hC1C2

    ∀ n > 1, Closure (G (r n)) ⊆ G n:= by

  intro G n hn
  simp [G, G_cool]
  exact ((Classical.choose_spec (would_be_cool hT C1 C2 hC1 hC2 hC1C2)).right.right.right n hn).left

lemma cool_prop2b {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    let G := G_cool hT C1 C2 hC1 hC2 hC1C2

    ∀ n > 1, Closure (G n) ⊆ G (s n):= by

  intro G n hn
  simp [G, G_cool]
  exact ((Classical.choose_spec (would_be_cool hT C1 C2 hC1 hC2 hC1C2)).right.right.right n hn).right

lemma cool_inference {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    let G := G_cool hT C1 C2 hC1 hC2 hC1C2

    ∀ n m : ℕ, f n < f m → Closure (G n) ⊆ G m := by

  intro G n m hmn

  cases' n with n

  · -- n = 0
    cases' m with m
    · -- m = 0
      by_contra
      exact (lt_self_iff_false (f 0)).mp hmn

    cases' m with m
    · -- m = 1
      by_contra
      simp [f_prop.right.left, f_prop.right.right] at hmn
      exact (Bool.eq_not_self ((1).blt ↑0)).mp hmn

    · -- m > 1
      simp [G, G_cool]
      sorry


  · sorry


lemma somethingnew {X : Type} [T : TopologicalSpace X]
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

  /- UN INTENTO : utilizar inducción sobre P → Q
  creo que en verdad no sirve de nada

  intro n m

  let P : ℕ → ℕ → Prop := fun n ↦ fun m ↦ (f n < f m → Closure (G n) ⊆ G m)
  have hP : P n m = (f n < f m → Closure (G n) ⊆ G m) := by rfl
  rw [← hP]

  apply my_strong_double_induction n m P
  intro n m

  constructor

  · simp [P]
    intro hi hnm

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

    have cases : m = 0 ∨ m > 0 := by exact Nat.eq_zero_or_pos m
    cases' cases with hm0 hm0

    · -- case m = 0
      have cases : n = 0 ∨ n > 0 := by exact Nat.eq_zero_or_pos n
      cases' cases with hn0 hn0

      · -- n ≠ 0
        simp [lema1] at hn0

      have cases : n = 1 ∨ n > 1 := by exact LE.le.eq_or_gt hn0
      cases' cases with hn1 hn1

      · -- n = 1
        simp [hn1, hm0, hG0, hG1]
        exact (Classical.choose_spec (hT C2ᶜ C1 hC2 hC1 hC1C2)).right.right

      · -- n > 1
        have hnm' : m < n := by exact lt_of_eq_of_lt hm0 hn0
        have aux := (s_prop n hn1).left
        simp at aux
        have aux' := (s_prop n hn1).right.right m
        simp at aux'
        specialize aux' hnm' hnm

        have cases : f (s n) < f m ∨ f (s n) = f m := by exact lt_or_eq_of_le aux'
        cases' cases with h h

        · specialize hi (s n) aux h
          trans Closure (G (s n))
          · trans G (s n)
            · exact (hG n hn1).right
            · exact set_inside_closure (G (s n))
          · exact hi

        · have f_prop := f_prop.left.left
          apply f_prop at h
          rw [← h]
          exact (hG n hn1).right

    have cases : m = 1 ∨ m > 1 := by exact LE.le.eq_or_gt hm0
    cases' cases with hm1 hm1

    · -- case m = 1
      simp [lema2] at hm1

    · -- case m > 1
      have cases : n = 0 ∨ n > 0 := by exact Nat.eq_zero_or_pos n
      cases' cases with hn0 hn0

      · -- n ≠ 0
        simp [lema1] at hn0

      have cases : n = 1 ∨ n > 1 := by exact LE.le.eq_or_gt hn0
      cases' cases with hn1 hn1

      · -- n = 1

        have hnm' : n < m := by exact lt_of_eq_of_lt hn1 hm1
        have aux := (r_prop m hm1).left
        simp at aux
        have aux' := (r_prop m hm1).right.right n
        simp at aux'
        specialize aux' hnm' hnm

        have cases : f n < f (r m) ∨ f n = f (r m) := by exact lt_or_eq_of_le aux'
        cases' cases with h h

        · specialize hi (r m) aux h
          trans Closure (G (s n))
          · trans G (s n)
            · exact (hG n hn1).right
            · exact set_inside_closure (G (s n))
          · exact hi

        · have f_prop := f_prop.left.left
          apply f_prop at h
          rw [← h]
          exact (hG n hn1).right
        sorry

      · -- n > 1
        sorry


-/


  intro n m hnm

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
        simp [hn1, hm0, hG0, hG1]
        exact (Classical.choose_spec (hT C2ᶜ C1 hC2 hC1 hC1C2)).right.right

      · -- caso n > 1, m = 0
        -- inducción sobre n

        let P : ℕ → Prop := fun k ↦ k > 1
        have hPn : P n
        · simp [P]
          exact hn1

        let Q : ℕ → Prop := fun k ↦ Closure (G k) ⊆ G m
        have hQn : Q n = (Closure (G n) ⊆ G m) := by rfl
        rw [← hQn]

        apply my_stronger_induction n P Q
        · exact hPn
        · intro n hn hi
          simp [P, Q] at hi hn
          simp [Q]

          have s_options := s_options n hn
          cases' s_options with hs0 hs1

          · -- caso s(n) = 0
            rw [hm0, ← hs0]
            specialize hG n hn
            exact hG.right

          · -- caso s(n) > 1
            have s_prop := (s_prop n hn).left
            simp at s_prop
            specialize hi (s n) s_prop hs1

            trans Closure (G (s n))
            · trans G (s n)
              · specialize hG n hn
                exact hG.right
              · exact set_inside_closure (G (s n))
            · exact hi


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

          let P : ℕ → Prop := fun k ↦ k > 1
          have hPm : P m
          · simp [P]
            exact hm1

          let Q : ℕ → Prop := fun k ↦ Closure (G n) ⊆ G k
          have hQm : Q m = (Closure (G n) ⊆ G m) := by rfl
          rw [← hQm]

          apply my_stronger_induction m P Q
          · exact hPm
          · intro m hm hi
            simp [P, Q] at hi
            simp [Q]

            have r_options := r_options m hm
            cases' r_options with hr1 hr1

            · -- caso r(m) = 1
              rw [hn1, ← hr1]
              specialize hG m hm
              exact hG.left

            · -- caso r(n) > 1
              have r_prop := (r_prop m hm).left
              simp at r_prop
              specialize hi (r m) r_prop hr1

              trans G (r m)
              · exact hi
              · trans Closure (G (r m))
                · exact set_inside_closure (G (r m))
                · specialize hG m hm
                  exact hG.left


        · -- caso n > 1, m > 1





/-
          let P : ℕ → ℕ → Prop := fun k ↦ fun l ↦ (k > 1) ∧ (l > 1) ∧ (f k < f l)
          have hPnm : P n m
          · simp [P]
            constructor
            exact hn1
            constructor
            exact hm1
            exact hnm

          let Q : ℕ → ℕ → Prop := fun k ↦ fun l ↦ Closure (G k) ⊆ G l
          have hQnm : Q n m = (Closure (G n) ⊆ G m) := by rfl
          rw [← hQnm]

          apply my_stronger_double_induction n m P Q hPnm

          simp [P, Q]
          intro n m hn1 hm1 hfnm

          constructor

          · intro hi

            have cases := s_options n hn1
            cases' cases with hs0 hs1

            · sorry

            · have hs := (s_prop n hn1).left
              simp at hs
              specialize hi (s n) hs hs1 hm1

-/







          let P : ℕ → Prop := fun k ↦ (k > 1) ∧ (f k < f m)
          have hPn : P n
          · simp [P]
            constructor
            exact hn1
            exact hnm

          let Q : ℕ → Prop := fun k ↦ Closure (G k) ⊆ G m
          have hQn : Q n = (Closure (G n) ⊆ G m) := by rfl
          rw [← hQn]

          apply my_stronger_induction n P Q
          · exact hPn

          · intro n hn hi
            simp [P, Q] at hn hi
            simp [Q]

            have aux : n ≠ m
            · by_contra c
              rw [c] at hn
              simp at hn



            have cases : m < n ∨ n < m := by exact Nat.lt_or_gt_of_ne (id (Ne.symm aux))
            cases' cases with hnm hnm

            · -- caso m < n

              have fsnm : f (s n) ≤ f m
              · apply (s_prop n hn.left).right.right
                simp
                exact hnm
                exact hn.right

              have s_options := s_options n hn.left
              cases' s_options with hs0 hs1

              · -- caso s(n) = 0
                have aux : f (s n) = f m
                · by_contra c
                  apply lt_of_le_of_ne at fsnm
                  specialize fsnm c
                  rw [hs0, f_prop.right.left] at fsnm
                  have hf := (f_in_icc01 m).right
                  rw [← not_lt] at hf
                  exact hf fsnm

                have aux : s n = m
                · apply f_prop.left.left
                  exact aux

                rw [← aux]
                exact (hG n hn.left).right

              · -- caso s(n) > 1

                have cases : f (s n) = f m ∨ f (s n) < f m
                exact Or.symm (Decidable.lt_or_eq_of_le fsnm)
                cases' cases with fsnm fsnm

                · -- caso f (s n) = f m
                  have aux : s n = m
                  · apply f_prop.left.left
                    exact fsnm
                  rw [← aux]
                  exact (hG n hn.left).right

                · -- caso f (s n) < f m

                  have hsn := (s_prop n hn.left).left
                  simp at hsn

                  trans Closure (G (s n))
                  · trans G (s n)
                    · exact (hG n hn.left).right
                    · exact set_inside_closure (G (s n))
                  · specialize hi (s n) hsn hs1 fsnm
                    exact hi

            · -- caso n < m

              let P : ℕ → Prop := fun l ↦ (l > 1) ∧ (n < l) ∧ (f n < f l)
              have hP : P m
              · constructor
                exact hm1
                constructor
                exact hnm
                exact hn.right

              let Q : ℕ → Prop := fun l ↦ (Closure (G n) ⊆ G l)
              have hQ : Q m = (Closure (G n) ⊆ G m) := by rfl
              rw [← hQ]

              apply my_stronger_induction m P Q hP
              simp [P, Q]
              intro m hm1 hnm hfnm hi

              have r_options := r_options m hm1
              cases' r_options with hr1 hr1

              · -- caso r(m) = 1
                sorry

              · -- caso r (m) > 1

                have cases : r m < n ∨ r m = n ∨ r m > n
                sorry

                cases' cases with h h
                cases' h with h h

                · -- caso r m < n
                  -- inducción sobre n ???????
                  -- si escribiera un resultado antes????
                  sorry

                · -- caso r m = n
                  -- trivial
                  sorry

                · -- caso r m > n

                  -- por hipótesis de induccion

                  have aux := (r_prop m hm1).left
                  simp at aux

                  specialize hi (r m) aux hr1

                  sorry




              let P : ℕ → ℕ → Prop := fun k ↦ fun l ↦ (k>1) ∧ (l>1) ∧ (k<l) ∧ (f k < f l)
              have hP : P n m
              · constructor
                exact hn.left
                constructor
                exact hm1
                constructor
                exact hnm
                exact hn.right

              let Q : ℕ → ℕ → Prop := fun k ↦ fun l ↦ Closure (G k) ⊆ G l
              have hQ : Q n m = (Closure (G n) ⊆ G m) := by rfl
              rw [← hQ]

              apply my_stronger_double_induction n m P Q hP
              simp [P, Q]
              intro n m hn1 hm1 hmn hfnm
              constructor

              · intro hin
                simp [hm1] at hin

                sorry

              · intro him
                sorry

              let P : ℕ → Prop := fun l ↦ (l > 1) ∧ (n < l) ∧ (f n < f l)
              have hPm : P m
              · simp [P]
                constructor
                exact hm1
                constructor
                exact hnm
                exact hn.right

              let Q : ℕ → Prop := fun l ↦ Closure (G n) ⊆ G l
              have hQm : Q m = (Closure (G n) ⊆ G m) := by rfl
              rw [← hQm]

              apply my_stronger_induction m P Q
              · exact hPm

              · intro m hm hi
                cases' hn with hn _
                simp [P, Q] at hm hi
                simp [Q]

                have fsnm : f n ≤ f (r m)
                · apply (r_prop m hm.left).right.right
                  simp
                  exact hm.right.left
                  exact hm.right.right

                have r_options := r_options m hm.left
                cases' r_options with hr1 hr1

                · -- caso r(m) = 1
                  have aux : f n = f (r m)
                  · by_contra c
                    apply lt_of_le_of_ne at fsnm
                    specialize fsnm c
                    rw [hr1, f_prop.right.right] at fsnm
                    have hf := (f_in_icc01 n).left
                    rw [← not_lt] at hf
                    exact hf fsnm

                  have aux : n = r m
                  · apply f_prop.left.left
                    exact aux

                  rw [aux]
                  exact (hG m hm.left).left

                · -- caso r(m) > 1

                  have cases : f n = f (r m) ∨ f n < f (r m)
                  exact Or.symm (Decidable.lt_or_eq_of_le fsnm)
                  cases' cases with fsnm fsnm

                  · -- caso f n = f (r m)
                    have aux : n = r m
                    · apply f_prop.left.left
                      exact fsnm
                    rw [aux]
                    exact (hG m hm.left).left

                  · -- f n < f (r m)



                    have hrm := (r_prop m hm.left).left
                    simp at hrm


                    trans Closure (G (s n))
                    · trans G (s n)
                      · exact (hG n hn.left).right
                      · exact set_inside_closure (G (s n))
                    · specialize hi (s n) hsn hs1 fsnm
                      exact hi




                  sorry














            let P : ℕ → Prop := fun l ↦ (l > 1) ∧ (f n < f l) ∧ (∀ m_1 < n, 1 < m_1 → f m_1 < f l → Closure (G m_1) ⊆ G l)
            have hPm : P m
            · simp [P]
              constructor
              exact hm1
              constructor
              exact hn.right
              exact hi

            let Q : ℕ → Prop := fun l ↦ Closure (G n) ⊆ G l
            have hQm : Q m = (Closure (G n) ⊆ G m) := by rfl
            rw [← hQm]

            apply my_stronger_induction m P Q
            · exact hPm

            · intro m hm him
              simp [P, Q] at hm him
              simp [Q]

              cases' hm with hm1 hm
              cases' hm with hfnm hin
              have hn1 := hn.left

              have aux : n ≠ m
              · by_contra c
                rw [c] at hfnm
                simp at hfnm

              have cases : n < m ∨ m < n := by exact Nat.lt_or_gt_of_ne aux
              cases' cases with hnm hnm

              · -- caso n < m

                have fnrm : f n ≤ f (r m)
                · apply (r_prop m hm1).right.right
                  simp
                  exact hnm
                  exact hfnm

                have r_options := r_options m hm1
                cases' r_options with hr1 hr1

                · -- caso r(m) = 1
                  have aux : f n = f (r m)
                  · by_contra c
                    apply lt_of_le_of_ne at fnrm
                    specialize fnrm c
                    rw [hr1, f_prop.right.right] at fnrm
                    have hf := (f_in_icc01 n).left
                    rw [← not_lt] at hf
                    exact hf fnrm

                  have aux : n = r m
                  · apply f_prop.left.left
                    exact aux

                  rw [aux]
                  exact (hG m hm1).left

                · -- caso r(m) > 1
                  have cases : f n = f (r m) ∨ f n < f (r m)
                  exact Or.symm (Decidable.lt_or_eq_of_le fnrm)
                  cases' cases with fnrm fnrm

                  · -- caso f n = f (r m)
                    have aux : n = r m
                    · apply f_prop.left.left
                      exact fnrm
                    rw [aux]
                    exact (hG m hm1).left

                  · -- caso f n < f (r m)

                    have hrm := (r_prop m hm1).left
                    simp at hrm

                    have aux : ∀ m_1 < n, 1 < m_1 → f m_1 < f (r m) → Closure (G m_1) ⊆ G (r m)
                    · intro k hkn hk1 hfkrm
                      have hfkm : f k < f m
                      · trans f (r m)
                        · exact hfkrm
                        · exact (r_prop m hm1).right.left
                      specialize hin k hkn hk1 hfkm
                      sorry

                    specialize him (r m) hrm hr1 fnrm aux
                    -- `CREO QUE AQUÍ ESTÁ LO QUE ES DISTINTO`

                    /-
                    ¿cuál es el problema aquí?
                    que para la inducción necesito < n no < m y r m < m...
                    hago inducción sobre m?? pero claro entonces... necesito pedirle a m en P que `n < m` para mantener la propiedad

                    tengo  r m < m y n < m
                    casos:

                      como n < m podemos aplicar q r m es la mejor elección fara f (r m) < f m
                      y obtener
                      f n ≤ f (r m)
                      entonces
                      * f n = f (r m) => n = r m -> r. abs
                      * f n < f (r m)
                        - si r m < n -> hi
                        - else? r m > n?
                    osea yo creo que aquí el problema es que tengo que inducir n y m

                    -/

                    have hrm := (r_prop m hm1).left
                    simp at hrm

                    specialize hi (r m)
                    trans Closure (G (s n))
                    · trans G (s n)
                      · exact (hG n hn.left).right
                      · exact set_inside_closure (G (s n))
                    · exact hi

              · -- caso m < n
                have fsnm : f (s n) ≤ f m
                · apply (s_prop n hn.left).right.right
                  simp
                  exact hnm
                  exact hfnm

                have s_options := s_options n hn.left
                cases' s_options with hs0 hs1

                · -- caso s(n) = 0
                  have aux : f (s n) = f m
                  · by_contra c
                    apply lt_of_le_of_ne at fsnm
                    specialize fsnm c
                    rw [hs0, f_prop.right.left] at fsnm
                    have hf := (f_in_icc01 m).right
                    rw [← not_lt] at hf
                    exact hf fsnm

                  have aux : s n = m
                  · apply f_prop.left.left
                    exact aux

                  rw [← aux]
                  exact (hG n hn.left).right

                · -- caso s(n) > 1

                  have cases : f (s n) = f m ∨ f (s n) < f m
                  exact Or.symm (Decidable.lt_or_eq_of_le fsnm)
                  cases' cases with fsnm fsnm

                  · -- caso f (s n) = f m
                    have aux : s n = m
                    · apply f_prop.left.left
                      exact fsnm
                    rw [← aux]
                    exact (hG n hn.left).right

                  · -- caso f (s n) < f m

                    have hsn := (s_prop n hn.left).left
                    simp at hsn

                    trans Closure (G (s n))
                    · trans G (s n)
                      · exact (hG n hn.left).right
                      · exact set_inside_closure (G (s n))
                    · specialize hin (s n) hsn hs1 fsnm
                      exact hin



/-
RESULTADO PRINCIPAL:
-/

lemma exists_G {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    (n : ℕ)
    (hn : n > 1)

    :
      ∃ G : ℕ → Set X, (
        (G 0 = C2ᶜ)
        ∧
        (G 1 = Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2))
        ∧
        IsOpen (G n)
        ∧
        (G (r n) ⊆ G n ∧ Closure (G n) ⊆ G (s n))
        )
    := by

  sorry


noncomputable def G' {X : Type} [T : TopologicalSpace X]

    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    := fun n ↦
      if n = 0 then C2ᶜ
      else if n = 1 then Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)
      else if hn : n > 1 then (Classical.choose (exists_G hT C1 C2 hC1 hC2 hC1C2 n hn)) n
      else ∅

lemma G'_prop1 {X : Type} [T : TopologicalSpace X]

    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n : ℕ, IsOpen (G' hT C1 C2 hC1 hC2 hC1C2 n) := by

  intro n

  cases' n with n
  · -- n = 0
    simp [G']
    exact { isOpen_compl := hC2 }

  cases' n with n
  · -- n = 1
    simp [G']
    have hT' := Classical.choose_spec (hT C2ᶜ C1 hC2 hC1 hC1C2)
    exact hT'.left

  · -- n > 1
    simp [G']
    have hG' := Classical.choose_spec (exists_G hT C1 C2 hC1 hC2 hC1C2 (n+1+1) (by linarith))
    exact hG'.right.right.left




lemma G'_prop2 {X : Type} [T : TopologicalSpace X]

    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n > 1, G' hT C1 C2 hC1 hC2 hC1C2 (r n) ⊆ G' hT C1 C2 hC1 hC2 hC1C2 n := by

  intro n hn
  induction' hn with n what HI

  · -- caso base
    have hr2 : r 2 = 1
    sorry
    simp [G', hr2]
    have kjdf := Classical.choose_spec (hT C2ᶜ C1 hC2 hC1 hC1C2)
    let V := Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)
    have hV : V = Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2) := by rfl
    rw [← hV]
    sorry

  · -- caso recursivo
    sorry




  have h := Classical.choose_spec (exists_G hT C1 C2 hC1 hC2 hC1C2 n hn)

  have aux : r n ≠ 0
  · by_contra c
    have r_prop := (r_prop n hn).right.left
    simp [c] at r_prop
    simp [f_prop.right.left] at r_prop
    have hf := (f_in_icc01 n).right
    exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false r_prop hf

  have hcases : r n = 1 ∨ r n > 1
  sorry






/-
como f es biyectiva, tiene inversa...
-/

lemma f_has_inverse : ∃ g : Q → ℕ, (
    (∀ n : ℕ, g (f n) = n) ∧
    (∀ q : Q, f (g q) = q)
  ) := by sorry

noncomputable def f_inv : Q → ℕ := Classical.choose f_has_inverse

lemma f_inv_prop : (∀ n : ℕ, f_inv (f n) = n) ∧
    (∀ q : Q, f (f_inv q) = q) := by
  let h := Classical.choose_spec f_has_inverse
  exact h


/-
DEFINICIÓN DE LA G FINAL
-/

def G {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ℚ → Set X := fun q ↦

  if q < 0 then ∅
  else if h : (0 ≤ q ∧ q ≤ 1) then (G' hT C1 C2 hC1 hC2 hC1C2 (f_inv ⟨q, h⟩))
  else Set.univ


/-
CUMPLE LAS PROPIEDADES???
-/

lemma prop1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ p : ℚ, IsOpen (G hT C1 C2 hC1 hC2 hC1C2 p) := by

  intro p

  have cases : p < 0 ∨ 0 ≤ p := by exact lt_or_le p 0
  cases' cases with hp hp

  · -- caso p < 0
    simp [G, hp]

  · -- caso 0 ≤ p
    have cases : p ≤ 1 ∨ 1 < p := by exact le_or_lt p 1
    cases' cases with hp' hp

    · -- caso 0 ≤ p ≤ 1
      have aux : ¬ p < 0
      · linarith
      have hp : 0 ≤ p ∧ p ≤ 1
      · constructor; exact hp; exact hp'

      simp [G, aux, hp]

      cases' (f_inv ⟨p, hp⟩) with k
      · simp [G']
        exact { isOpen_compl := hC2 }

      · cases' k with k
        · simp [G']
          let h := Classical.choose_spec (hT C2ᶜ C1 hC2 hC1 hC1C2)
          exact h.left

        · simp [G']
          have h := Classical.choose_spec (exists_G hT C1 C2 hC1 hC2 hC1C2 (k + 1 + 1) (by linarith))
          exact h.right.right.left

    · -- caso 1 < p
      have aux : ¬ p < 0
      · linarith
      have aux' : ¬ (0 ≤ p ∧ p ≤ 1)
      · simp
        intro
        exact hp
      simp [G, hp, aux, aux']



lemma prop2 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ p q: ℚ, p < q → Closure (G hT C1 C2 hC1 hC2 hC1C2 p) ⊆ G hT C1 C2 hC1 hC2 hC1C2 q := by

  intro p q hpq

  /-
  se divide en varios casos.

  1. si `p < 0`, entonces el goal se traduce a `∅ ⊆ U`,
    que es cierto para todo U

  2.  si `q > 1`, entonces el goal se traduce a `U ⊆ Set.univ`,
    que es cierto para todo U

  3. en caso contrario, si `0 ≤ p` y `q ≤ 1`, puesto que
    `p < q` se tiene `p, q ∈ Q`, luego podemos aplicar
    la inversa de `f` y la definición de `Gn`
  -/

  have cases : q < 0 ∨ 0 ≤ q := by exact lt_or_le q 0
  cases' cases with hq0 hq0

  · -- caso 1. q < 0
    have hp : p < 0 := by linarith
    simp [G, hp, hq0, closure_of_empty]

  have cases : q ≤ 1 ∨ q > 1 := by exact le_or_lt q 1
  cases' cases with hq1 hq1

  · -- casos 2 y 3. 0 ≤ q ≤ 1
    have cases : p < 0 ∨ 0 ≤ p := by exact lt_or_le p 0
    cases' cases with hp0 hp0

    · -- caso 2. p < 0, q ∈ [0, 1]
      simp [G, hp0, closure_of_empty]

    · -- caso 3. p, q ∈ [0, 1]
      have auxq : ¬ q < 0 := by linarith
      have auxp : ¬ p < 0 := by linarith
      have hq : 0 ≤ q ∧ q ≤ 1 := by simp [hq0, hq1]
      have hp : 0 ≤ p ∧ p ≤ 1 := by simp [hp0]; linarith

      simp [G, auxq, auxp, hq, hp]

      have h : p ≠ q := by linarith
      have h' : f_inv ⟨p, hp⟩ ≠ f_inv ⟨q, hq⟩
      · by_contra c
        apply congrArg f at c
        simp [f_inv_prop.right] at c
        exact h c

      have cases : f_inv ⟨p, hp⟩ = 0 ∨ f_inv ⟨p, hp⟩ > 0 := by exact Nat.eq_zero_or_pos (f_inv ⟨p, hp⟩)
      cases' cases with hfp hfp

      · -- caso 3.1. f⁻¹(p) = 0
        have cases : f_inv ⟨q, hq⟩ = 0 ∨ f_inv ⟨q, hq⟩ > 0 := by exact Nat.eq_zero_or_pos (f_inv ⟨q, hq⟩)
        cases' cases with hfq hfq

        · -- caso 3.1.1. f⁻¹(q) = 0
          -- imposible porque f⁻¹(p) ≠ f⁻¹(q)
          simp [hfp, hfq] at h'

        have cases : f_inv ⟨q, hq⟩ = 1 ∨ f_inv ⟨q, hq⟩ > 1 := by exact LE.le.eq_or_gt hfq
        cases' cases with hfq hfq

        · -- caso 3.1.2. f⁻¹(q) = 1
          have auxp : p = 1
          · apply congrArg f at hfp
            simp [f_prop.right.left, f_inv_prop.right] at hfp
            have h_proj := Subtype.mk.inj hfp
            -- no entiendo muy bien esto
            exact h_proj

          have auxq : q = 0
          · apply congrArg f at hfq
            simp [f_prop.right.right, f_inv_prop.right] at hfq
            have h_proj := Subtype.mk.inj hfq
            exact h_proj

          by_contra
          simp [auxp, auxq] at hpq
          linarith

        · -- caso 3.1.3. f⁻¹(q) > 1
          have auxq : ¬ f_inv ⟨q, hq⟩ = 0 := by linarith
          have auxq' : ¬ f_inv ⟨q, hq⟩ = 1 := by linarith
          simp [hfp, hfq, auxq, auxq', G']

          have h := (Classical.choose_spec (exists_G hT C1 C2 hC1 hC2 hC1C2 (f_inv ⟨q, hq⟩) hfq))
          have H := h.right.left
          have h0 := h.right.right

          have aux : f 0 < f (f_inv ⟨q, hq⟩)
          · simp [f_prop.right.left, f_inv_prop.right]
            sorry
          sorry

      · -- caso 3.2. f⁻¹(p) = 1

        sorry
  sorry


def propG {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    (n : ℕ)
    (hn : n > 1)
    (G : ℕ → Set X) : Prop :=

    (
      (G 0 = C2ᶜ) ∧
      (G 1 = Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)) ∧
      (∀ p ≤ n, IsOpen (G p)) ∧
      (∀ p ≤ n, ∀ q ≤ n, f p < f q → Closure (G p) ⊆ G q) ∧
      ((h : n - 1 > 1) →
        (∀ G' : ℕ → Set X, (propG hT C1 C2 hC1 hC2 hC1C2 (n-1) h G') →
          (∀ m < n, G m = G' m)
        )
      )
    )
