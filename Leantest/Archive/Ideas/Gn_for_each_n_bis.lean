import Leantest.Separation.normal
import Leantest.MyDefs.my_rs_functions


def exists_Gn {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ℕ → Prop := fun n ↦
      ∃ G : ℕ → Set X, (
        (∀ p : ℕ, p ≤ n → IsOpen (G p))
        ∧
        (∀ p q : ℕ, p ≤ n → q ≤ n → f p < f q → Closure (G p) ⊆ G q)
        ∧
        (G 0 = C2ᶜ)
        ∧
        (G 1 = Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2))
        ∧
        (G 2 = Classical.choose (hT
          C2ᶜ
          (Closure (Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)))
          hC2
          (by exact closure_is_closed (Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)))
          (by
            let hV := Classical.choose_spec (hT C2ᶜ C1 hC2 hC1 hC1C2)
            exact hV.right.right
          )
        ))
        )

def Gn {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)


    (n : ℕ)
    (hn1 : n > 1)
    (H : exists_Gn hT C1 C2 hC1 hC2 hC1C2 (n-1))

    : ℕ → Set X := fun m ↦
      if m < n then Classical.choose H m
      else if m = n then Classical.choose (
        hT
        (Classical.choose H (s n)) -- U
        (Closure (Classical.choose H (r n))) -- C
        (by -- U es abierto
          have hH := (Classical.choose_spec H).left
          apply hH
          have s_prop := (s_prop n hn1).left
          simp at s_prop
          apply Nat.le_of_lt_succ
          simp
          have aux : n-1+1 = n
          · apply Nat.sub_add_cancel
            linarith
          rw [aux]
          exact s_prop
        )
        (by -- C es cerrado
          exact closure_is_closed (Classical.choose H (r n))
        )
        (by -- C ⊆ U
          have hH := (Classical.choose_spec H).right.left
          apply hH
          · have r_prop := (r_prop n hn1).left
            simp at r_prop
            apply Nat.le_of_lt_succ
            simp
            have aux : n-1+1 = n
            · apply Nat.sub_add_cancel
              linarith
            rw [aux]
            exact r_prop
          · have s_prop := (s_prop n hn1).left
            simp at s_prop
            apply Nat.le_of_lt_succ
            simp
            have aux : n-1+1 = n
            · apply Nat.sub_add_cancel
              linarith
            rw [aux]
            exact s_prop
          · have r_prop := (r_prop n hn1).right.left
            have s_prop := (s_prop n hn1).right.left
            trans f n
            · exact r_prop
            · exact s_prop
        )
      )
      else ∅



lemma exists_G {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    (n : ℕ)
    (hn : n > 1)

    : exists_Gn hT C1 C2 hC1 hC2 hC1C2 n
    := by

  simp [exists_Gn]

  induction' hn with n hn HI

  let h := Classical.choose_spec (hT C2ᶜ C1 hC2 hC1 hC1C2)

  · --caso base
    simp
    let G : ℕ → Set X := fun n ↦
      if n = 0 then C2ᶜ
      else if n = 1 then Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)
      else Classical.choose (
        hT
          (C2ᶜ)
          (Closure (Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)))
          hC2
          (by apply closure_is_closed)
          h.right.right
      )

    let h' := Classical.choose_spec (
      hT
        (C2ᶜ)
        (Closure (Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)))
        hC2
        (by apply closure_is_closed)
        h.right.right
    )

    use G
    constructor

    · -- PROP 1
      intro p hp
      cases' hp with _ hp
      · -- caso p = 2
        simp [G]
        exact h'.left

      cases' hp with _ hp
      · -- caso p = 1
        simp [G]
        exact h.left

      · simp at hp
        simp [hp, G]
        exact { isOpen_compl := hC2 }

    constructor

    · -- PROP 2
      intro p q hp hq hpq

      /-
      NOTA: como f p < f q, y se tiene f 1 ≤ f 2 ≤ f 0,
      los únicos casos posibles son:
      - p = 1, q = 2
      - p = 1, q = 0
      - p = 2, q = 0
      -/

      cases' hp with _ hp

      · -- caso p = 2
        cases' hq with _ hq

        · -- caso q = 2
          -- (no puede ser)
          by_contra
          exact (lt_self_iff_false (f 2)).mp hpq

        cases' hq with _ hq

        · -- caso q = 1
          -- (no puede ser)
          by_contra
          simp at hpq
          rw [f_prop.right.right] at hpq
          exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false hpq (f 2).property.left
          -- wow.

        · -- caso q = 0
          simp at hq
          simp [hq, G]
          exact h'.right.right

      cases' hp with _ hp

      · -- caso p = 1

        cases' hq with _ hq

        · -- caso q = 2
          simp [G]
          exact h'.right.left

        cases' hq with _ hq

        · -- caso q = 1
          -- (no puede ser)
          by_contra
          exact (lt_self_iff_false (f 1)).mp hpq

        · -- caso q = 0
          simp at hq
          simp [hq, G]
          exact h.right.right

      · -- caso p = 0
        -- (no puede ser)
        by_contra
        simp at hp
        rw [hp] at hpq
        rw [f_prop.right.left] at hpq
        exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false hpq (f q).property.right

    constructor

    · -- PROP 3
      simp [G]

    constructor

    · -- PROP 4
      simp [G]

    · -- PROP 5
      simp [G]


  · -- caso recursivo

    simp
    simp at hn
    cases' HI with G' hG'

    let r := r (n + 1)
    let s := s (n + 1)

    have hr : r ≤ n
    apply Nat.le_of_lt_succ
    let aux := (r_prop (n+1) (by exact Nat.lt_add_right 1 hn)).left
    simp at aux
    exact aux

    have hs : s ≤ n
    apply Nat.le_of_lt_succ
    let aux := (s_prop (n+1) (by exact Nat.lt_add_right 1 hn)).left
    simp at aux
    exact aux

    have hGs : IsOpen (G' s)
    · apply hG'.left
      exact hs

    have hGrs : Closure (G' r) ⊆ G' s
    · apply hG'.right.left
      · exact hr
      · exact hs
      · trans f (n + 1)
        · let aux := (r_prop (n+1) (by exact Nat.lt_add_right 1 hn)).right.left
          exact aux
        · let aux := (s_prop (n+1) (by exact Nat.lt_add_right 1 hn)).right.left
          exact aux

    let G : ℕ → Set X := fun m ↦
      if m < n + 1 then G' m
      else Classical.choose (
        hT
        (G' s)
        (Closure (G' r))
        hGs
        (by apply closure_is_closed)
        hGrs
      )

    let h := Classical.choose_spec (
        hT
        (G' s)
        (Closure (G' r))
        hGs
        (by apply closure_is_closed)
        hGrs
      )

    use G

    constructor

    · -- PROP 1
      intro p hp
      cases' hp with _ hp

      · -- caso p = n + 1
        simp [G]
        exact h.left

      · -- caso p ≤ n
        simp at hp
        rw [← Order.lt_add_one_iff] at hp
        simp [hp, G]
        apply hG'.left
        exact Nat.le_of_lt_succ hp

    constructor

    · -- PROP 2
      intro p q hp hq hpq

      cases' hp with _ hp

      · -- caso p = n+1

        cases' hq with _ hq

        · -- caso q = n+1
          -- (no puede ser)
          by_contra
          exact (lt_self_iff_false (f (n+1))).mp hpq

        · -- caso q ≤ n
          simp at hq
          rw [← Order.lt_add_one_iff] at hq
          simp [hq, G]

          /-
          voy a diferenciar dos casos:
          - q = s
          - q ≠ s
          -/

          have cases : q = s ∨ q ≠ s := by exact eq_or_ne q s
          cases' cases with hqs hqs

          · -- caso q = s
            rw [hqs]
            exact h.right.right

          · -- caso q ≠ s

            trans (G' s)

            · exact h.right.right

            · trans (Closure (G' s))

              · apply set_inside_closure

              · apply hG'.right.left
                · exact hs
                · exact Nat.le_of_lt_succ hq
                · apply lt_of_le_of_ne

                  · simp [s]
                    apply (s_prop (n+1) (by exact Nat.lt_add_right 1 hn)).right.right
                    · simp
                      exact hq
                    · exact hpq

                  · by_contra c
                    apply f_prop.left.left at c
                    exact hqs (id (Eq.symm c))

      · -- caso p ≤ n
        simp at hp

        cases' hq with _ hq

        · -- caso q = n+1
          rw [← Order.lt_add_one_iff] at hp
          simp [hp, G]

          /-
          voy a diferenciar dos casos:
          - q = s
          - q ≠ s
          -/

          have cases : p = r ∨ p ≠ r := by exact eq_or_ne p r
          cases' cases with hpr hpr

          · -- caso p = r
            rw [hpr]
            exact h.right.left

          · -- caso p ≠ r

            trans (Closure (G' r))

            · trans (G' r)

              · apply hG'.right.left
                · exact Nat.le_of_lt_succ hp
                · exact hr
                · apply lt_of_le_of_ne

                  · simp [r]
                    apply (r_prop (n+1) (by exact Nat.lt_add_right 1 hn)).right.right
                    · simp
                      exact hp
                    · exact hpq

                  · by_contra c
                    apply f_prop.left.left at c
                    exact hpr c

              · apply set_inside_closure

            · exact h.right.left

        · -- caso q ≤ n
          simp at hq
          rw [← Order.lt_add_one_iff] at hp hq
          simp [hp, hq, G]
          apply hG'.right.left
          · exact Nat.le_of_lt_succ hp
          · exact Nat.le_of_lt_succ hq
          · exact hpq

    constructor

    · -- PROP 3
      simp [G]
      exact hG'.right.right.left

    constructor

    · -- PROP 4
      have aux : n > 0 := by linarith
      simp [G, aux]
      exact hG'.right.right.right.left

    · -- PROP 5
      have aux : n + 1 > 2 := by exact Order.lt_add_one_iff.mpr hn
      simp [G, aux]
      exact hG'.right.right.right.right



def G {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

  : ℕ → Set X := fun n ↦
    if n = 0 then ∅
    else if n = 1 then ∅
    else if n = 2 then ∅
    else if h : n > 2 then Gn hT C1 C2 hC1 hC2 hC1C2 n
      (by linarith)
      (by
        have aux : n - 1 > 1
        · exact Nat.lt_sub_of_add_lt h
        exact exists_G hT C1 C2 hC1 hC2 hC1C2 (n-1) aux)
      n
    else ∅


lemma unacosa_paso1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    (n : ℕ)
    (hn : n > 2)

  : ∀ m ≤ n, Gn hT C1 C2 hC1 hC2 hC1C2 n
      (by linarith)
      (by
        have aux : n - 1 > 1
        · exact Nat.lt_sub_of_add_lt hn
        exact exists_G hT C1 C2 hC1 hC2 hC1C2 (n-1) aux)
      m
    =
    Gn hT C1 C2 hC1 hC2 hC1C2 (n+1)
      (by linarith)
      (by
        have aux : (n+1) - 1 > 1
        · apply Nat.lt_sub_of_add_lt
          simp
          linarith
        exact exists_G hT C1 C2 hC1 hC2 hC1C2 ((n+1)-1) aux)
      m

    := by

  intro m hm

  let G := Gn hT C1 C2 hC1 hC2 hC1C2 (n+1)
      (by linarith)
      (by
        have aux : (n+1) - 1 > 1
        · apply Nat.lt_sub_of_add_lt
          simp
          linarith
        exact exists_G hT C1 C2 hC1 hC2 hC1C2 ((n+1)-1) aux)
  have G_def : G = Gn hT C1 C2 hC1 hC2 hC1C2 (n+1)
      (by linarith)
      (by
        have aux : (n+1) - 1 > 1
        · apply Nat.lt_sub_of_add_lt
          simp
          linarith
        exact exists_G hT C1 C2 hC1 hC2 hC1C2 ((n+1)-1) aux)
        := by rfl
  let Gm := G m
  have Gm_def : Gm = G m := by rfl

  rw [G_def] at Gm_def
  rw [← Gm_def]
  simp [Gn] at Gm_def

  have aux : m < n + 1 := by linarith

  simp [aux] at Gm_def

  have aux : (n+1) - 1 > 1
  · apply Nat.lt_sub_of_add_lt
    simp
    linarith

  have H : exists_Gn hT C1 C2 hC1 hC2 hC1C2 ((n+1)-1)
  · apply exists_G hT C1 C2 hC1 hC2 hC1C2
    exact aux

  let GH := Classical.choose H
  have GH_def : GH = Classical.choose H := by rfl


  have cases : m = n ∨ m < n := by exact Nat.eq_or_lt_of_le hm
  cases' cases with hm1 hm2

  · simp [Gn, hm1]

    sorry

  · sorry





  sorry

lemma unacosa {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    (n k : ℕ)
    (hn : n > 2)
    (hk : k > 0)

  : ∀ m ≤ n, Gn hT C1 C2 hC1 hC2 hC1C2 n
      (by linarith)
      (by
        have aux : n - 1 > 1
        · exact Nat.lt_sub_of_add_lt hn
        exact exists_G hT C1 C2 hC1 hC2 hC1C2 (n-1) aux)
      m
    =
    Gn hT C1 C2 hC1 hC2 hC1C2 (n+k)
      (by linarith)
      (by
        have aux : (n+k) - 1 > 1
        · apply Nat.lt_sub_of_add_lt
          simp
          linarith
        exact exists_G hT C1 C2 hC1 hC2 hC1C2 ((n+k)-1) aux)
      m

    := by


  induction' hk with k hk hi

  · -- k = 1
    intro m hm
    simp
    exact unacosa_paso1 hT C1 C2 hC1 hC2 hC1C2 n hn m hm


  · -- k > 1
    simp
    intro m hm
    specialize hi m hm
    rw [hi]
    exact unacosa_paso1 hT C1 C2 hC1 hC2 hC1C2 (n+k)
      (by exact Nat.lt_add_right k hn)
      m
      (by exact Nat.le_add_right_of_le hm)

    let U := Gn hT C1 C2 hC1 hC2 hC1C2 (n+1)
      (by linarith)
      (by
        have aux : (n+1) - 1 > 1
        · apply Nat.lt_sub_of_add_lt
          simp
          linarith
        exact exists_G hT C1 C2 hC1 hC2 hC1C2 ((n+1)-1) aux)
    have U_def : U = Gn hT C1 C2 hC1 hC2 hC1C2 (n+1)
      (by linarith)
      (by
        have aux : (n+1) - 1 > 1
        · apply Nat.lt_sub_of_add_lt
          simp
          linarith
        exact exists_G hT C1 C2 hC1 hC2 hC1C2 ((n+1)-1) aux)
    rfl

    rw [← U_def]

    let Un := U n
    have Un_def : Un = U n := by rfl

    simp [U, Gn] at Un_def
    simp [Gn]

    sorry


  · -- m > 1
    simp





  simp [Gn, hk]

  have H : exists_Gn hT C1 C2 hC1 hC2 hC1C2 (k - 1)
  · have aux : k - 1 > 1
    · apply Nat.lt_sub_of_add_lt
      simp
      linarith
    exact exists_G hT C1 C2 hC1 hC2 hC1C2 (k-1) aux

  let Gkn := Classical.choose H
  have Gkn_def : Gkn = Classical.choose H := by rfl
  have Gkn_prop := Classical.choose_spec H

  rw [← Gkn_def]
  rw [← Gkn_def] at Gkn_prop





  sorry

#check exists_G




def Gn' {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ℕ → (ℕ → Set X) :=

    fun n ↦
      if n = 0 then fun _ ↦ C2ᶜ
      else if n = 1 then fun m ↦
        if m = 0 then C2ᶜ
        else Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)
      else if n = 2 then fun m ↦
        if m = 0 then C2ᶜ
        else if m = 1 then Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)
        else Classical.choose (hT
          C2ᶜ
          (Closure (Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)))
          hC2
          (by exact closure_is_closed (Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)))
          (by
            let hV := Classical.choose_spec (hT C2ᶜ C1 hC2 hC1 hC1C2)
            exact hV.right.right
          )
        )
      else if h : n > 2 then fun m ↦
        if m < n then Classical.choose (exists_G hT C1 C2 hC1 hC2 hC1C2 (n-1)
          (by exact Nat.lt_sub_of_add_lt h)) m
        else if m = n then Classical.choose (exists_G hT C1 C2 hC1 hC2 hC1C2 n (by linarith)) m
        else ∅
      else fun _ ↦ ∅


lemma Gn'_prop1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n : ℕ, n > 0 →
      Gn' hT C1 C2 hC1 hC2 hC1C2 n (n-1) =
      Gn' hT C1 C2 hC1 hC2 hC1C2 (n-1) (n-1)
    := by

  intro n hn0

  have cases : n = 1 ∨ n > 1 := by exact LE.le.eq_or_gt hn0
  cases' cases with hn1 hn1

  · -- n = 1
    simp [hn1]

    let U : Set X := Gn' hT C1 C2 hC1 hC2 hC1C2 n (n-1)
    have U_def : U  = Gn' hT C1 C2 hC1 hC2 hC1C2 n (n-1) := by rfl
    let V : Set X := Gn' hT C1 C2 hC1 hC2 hC1C2 (n-1) (n-1)
    have V_def : V = Gn' hT C1 C2 hC1 hC2 hC1C2 (n-1) (n-1) := by rfl
    simp [hn1] at U_def V_def
    rw [← U_def, ← V_def]

    simp [Gn'] at U_def V_def
    simp [U_def, V_def]
    -- no se por qué lo he tenido que hacer así tan raro

  have cases : n = 2 ∨ n > 2 := by exact LE.le.eq_or_gt hn1
  cases' cases with hn2 hn2

  · -- n = 2
    simp [hn2]

    let U : Set X := Gn' hT C1 C2 hC1 hC2 hC1C2 n (n-1)
    have U_def : U  = Gn' hT C1 C2 hC1 hC2 hC1C2 n (n-1) := by rfl
    let V : Set X := Gn' hT C1 C2 hC1 hC2 hC1C2 (n-1) (n-1)
    have V_def : V = Gn' hT C1 C2 hC1 hC2 hC1C2 (n-1) (n-1) := by rfl
    simp [hn2] at U_def V_def
    rw [← U_def, ← V_def]

    simp [Gn'] at U_def V_def
    simp [U_def, V_def]

  · -- n > 2

    let U : Set X := Gn' hT C1 C2 hC1 hC2 hC1C2 n (n-1)
    have U_def : U  = Gn' hT C1 C2 hC1 hC2 hC1C2 n (n-1) := by rfl
    let V : Set X := Gn' hT C1 C2 hC1 hC2 hC1C2 (n-1) (n-1)
    have V_def : V = Gn' hT C1 C2 hC1 hC2 hC1C2 (n-1) (n-1) := by rfl
    rw [← U_def, ← V_def]

    have aux0 : n ≠ 0 := by exact Nat.not_eq_zero_of_lt hn0
    have aux1 : n ≠ 1 := by exact Ne.symm (Nat.ne_of_lt hn1)
    have aux2 : n ≠ 2 := by exact Ne.symm (Nat.ne_of_lt hn2)

    simp [Gn', aux0, aux1, aux2, hn2] at U_def
    simp [hn0] at U_def

    have aux0 : n - 1 ≠ 0 := by exact Nat.sub_ne_zero_iff_lt.mpr hn1
    have aux1 : n - 1 ≠ 1
    · by_contra c
      simp at c
      linarith

    have cases : n = 3 ∨ n > 3 := by exact LE.le.eq_or_gt hn2
    cases' cases with hn3 hn3

    · -- n = 3

      have aux : n - 1 = 2 := by exact Eq.symm (Nat.eq_sub_of_add_eq' (id (Eq.symm hn3)))
      simp [Gn', aux] at V_def

      have aux' : n - 1 > 1 := by exact Nat.lt_sub_of_add_lt hn2

      let A := Classical.choose (exists_G hT C1 C2 hC1 hC2 hC1C2 (n-1) aux')
      have A_def : A = Classical.choose (exists_G hT C1 C2 hC1 hC2 hC1C2 (n-1) aux') := by rfl

      let B := A (n-1)
      have B_def : B = A (n-1) := by rfl

      rw [A_def] at B_def

      have h : B = U
      · rw [U_def]

      have hA := Classical.choose_spec (exists_G hT C1 C2 hC1 hC2 hC1C2 (n-1) aux')
      have hA := hA.right.right.right.right

      simp [aux, hA] at B_def
      rw [B_def] at h
      rw [← h]
      rw [V_def]

    · -- n > 3

      have aux2 : n - 1 ≠ 2
      · by_contra c
        simp at c
        linarith

      have aux : n - 1 > 2 := by exact Nat.lt_sub_of_add_lt hn3
      simp [Gn', aux0, aux1, aux2, aux] at V_def
      simp [U_def, V_def]


lemma Gn'_prop2 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n k : ℕ, n > 0 → k < n →
      Gn' hT C1 C2 hC1 hC2 hC1C2 n k =
      Gn' hT C1 C2 hC1 hC2 hC1C2 (n-1) k
    := by

  intro n k hn hk

  have cases : n = 1 ∨ n > 1 := by exact LE.le.eq_or_gt hn
  cases' cases with hn1 hn1

  · -- caso n = 1 => k = 0

    have aux : k = 0 := by linarith
    simp [Gn', hn1, aux]

  have cases : n = 2 ∨ n > 2 := by exact LE.le.eq_or_gt hn1
  cases' cases with hn2 hn2

  · -- caso n = 2 => k = 0 o k = 1

    have cases : k = 0 ∨ k = 1
    · cases' k with k
      simp
      cases' k with k
      simp
      linarith

    cases' cases with hk0 hk1

    · -- k = 0
      simp [Gn', hn2, hk0]

    · -- k = 1
      simp [Gn', hn2, hk1]

  have cases : n = 3 ∨ n > 3 := by exact LE.le.eq_or_gt hn2
  cases' cases with hn3 hn3

  · -- caso n = 3

    have cases : k = 0 ∨ k = 1 ∨ k = 2
    · cases' k with k
      simp
      cases' k with k
      simp
      cases' k with k
      simp
      linarith

    have aux : n - 1 > 1 := by exact Nat.lt_sub_of_add_lt hn2
    have h := Classical.choose_spec (exists_G hT C1 C2 hC1 hC2 hC1C2 (n-1) aux)

    cases' cases with hk0 hk

    · -- k = 0
      simp [Gn', hn3, hk0]
      exact h.right.right.left

    cases' hk with hk1 hk2

    · -- k = 1
      simp [Gn', hn3, hk1]
      exact h.right.right.right.left

    · -- k = 2
      simp [Gn', hn3, hk2]
      exact h.right.right.right.right

  · -- caso n > 3

    have aux0 : n ≠ 0 := by exact Nat.not_eq_zero_of_lt hn
    have aux1 : n ≠ 1 := by exact Ne.symm (Nat.ne_of_lt hn1)
    have aux2 : n ≠ 2 := by exact Ne.symm (Nat.ne_of_lt hn2)
    have aux3 : n ≠ 3 := by exact Ne.symm (Nat.ne_of_lt hn3)
    have aux0' : n - 1 ≠ 0 := by exact Nat.sub_ne_zero_iff_lt.mpr hn1
    have aux' : n - 1 > 2 := by exact Nat.lt_sub_of_add_lt hn3

    have cases : k = n - 1 ∨ k < n - 1
    · sorry


    cases' cases with hk hk

    · -- caso k = n - 1
      simp [Gn', aux0, aux1, aux2, aux3, aux0', aux', hn2, hk]

    · -- caso k < n - 1

      simp [hk]



    sorry


def G'crazy {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ℕ → (ℕ → Set X) :=

    fun n ↦
      if n = 0 then fun _ ↦ C2ᶜ
      else if n = 1 then fun m ↦
        if m = 0 then C2ᶜ
        else Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)
      else if h : n > 1 then fun m ↦
        if m < n then G'crazy hT C1 C2 hC1 hC2 hC1C2 (n-1) m
        else if m = n then Classical.choose (exists_G hT C1 C2 hC1 hC2 hC1C2 n h) m
        else ∅
      else fun _ ↦ ∅

def Gcrazy {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ℕ → Set X := fun n ↦ G'crazy hT C1 C2 hC1 hC2 hC1C2 n n

-- something here doesn't seem right.
