import Mathlib.Tactic
import Leantest.Separation.normal


-- primera idea
example {X : Type}
    (T : TopologicalSpace X)
    (hT : NormalTopoSpace T)
    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsClosed C2)
    (P : Finset ℕ)
    (h0 : 0 ∈ P)
    (h1 : 1 ∈ P)
    (k : ℕ) (hk : k = P.card)
    (G : ℚ → Set X)
    (f : ℕ → ℚ)
    (hP1 : ∀ n ∈ P, IsOpen (G (f n)))
    (hP2 : ∀ n ∈ P, ∀ m ∈ P, f n < f m → Closure (G (f n)) ⊆ G (f m))
    (s : ℕ)
    :
    (∃ U : Set X, (IsOpen U) ∧
    (∀ t ∈ P, (f t < f s → Closure (G (f t)) ⊆ U))) := by

induction' s with s HI

· -- CB
  use G (f 0)

  constructor
  · exact hP1 0 h0
  · intro t ht1 ht2
    exact hP2 t ht1 0 h0 ht2

· -- CR

  have options : s ∈ P ∨ s ∉ P
  exact Decidable.em (s ∈ P)

  cases' options with hs hs

  · -- if s ∈ P, trivial
    use G (f (s))

    constructor
    · exact hP1 s hs
    · intro t ht1 ht2
      sorry
  sorry



-- segunda idea


example {X : Type}
    (T : TopologicalSpace X)
    (hT : NormalTopoSpace T)
    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsClosed C2)

    (G : ℚ → Set X)
    (f : ℕ → ℚ)

    (hf0 : f 0 = 1)
    (hf1 : f 1 = 0)

    (hf : ∀ n : ℕ, 0 ≤ f n ∧ f n ≤ 1)
    (finy : f.Injective)

    (P : Finset ℕ)

    (hP : { n : ℕ | IsOpen (G (f n)) ∧
    (∀ m ∈ P, f n < f m → Closure (G (f n)) ⊆ G (f m)) })


    (h0 : 0 ∈ P)
    (h1 : 1 ∈ P)

    --(k : ℕ) (hk : k = P.card)

    (s : ℕ)

    :

    s ∈ P := by

  apply Nat.strong_induction_on
  intro n hn

  /-
  paso 1. Quiero ver que n no es 0 ni 1
  (seguramente hay formas más fáciles de hacerlo)
  -/

  have aux : n = 0 ∨ n > 0
  exact Nat.eq_zero_or_pos n
  cases' aux with hn' hn'

  · -- n=0
    rw [hn']
    exact h0

  · have aux : n = 1 ∨ n > 1
    exact LE.le.eq_or_gt hn'
    cases' aux with hn' hn'

    · -- n=1
      rw [hn']
      exact h1

    · -- n not 0 or 1

  /-
  paso 2. si n no es 0 ni 1,
  entonces f n no es 0 ni 1 (f inyectiva)
  entonces puedo encontrar t,s en P tal que
  f t < f n < f s
  -/

      let S : Finset ℕ := P.filter (fun p ↦ f p > f n)
      -- nota: esto no son filtros jaja

      have H : S.Nonempty
      use 0
      rw [Finset.mem_filter]
      constructor
      · exact h0
      · rw [hf0]
        specialize hf n
        cases' hf with _ hf
        apply Ne.lt_of_le
        rw [← hf0]
        by_contra c
        apply finy at c
        linarith
        exact hf

      let s : ℕ := Finset.min' S H

      let I : Finset ℕ := P.filter (fun p ↦ f p < f n)
      -- nota: esto no son filtros jaja

      have H : I.Nonempty
      use 1
      rw [Finset.mem_filter]
      constructor
      · exact h1
      · rw [hf1]
        specialize hf n
        cases' hf with hf _
        apply Ne.lt_of_le
        rw [← hf1]
        by_contra c
        apply finy at c
        linarith
        exact hf

      let i : ℕ := Finset.max' I H

      sorry


example {X : Type}
    (T : TopologicalSpace X)
    (hT : NormalTopoSpace T)
    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsClosed C2)

    (f : ℕ → ℚ)

    (hf0 : f 0 = 1)
    (hf1 : f 1 = 0)

    (hf : ∀ n : ℕ, 0 ≤ f n ∧ f n ≤ 1)
    (finy : f.Injective)

    (P : Finset ℕ)

    (hP : { n : ℕ | (∃ U : Set X, IsOpen U ∧
    (∀ m ∈ P, ∃ V : Set X, (IsOpen V) ∧ (f n < f m → Closure (U) ⊆ V))) })

    /-
    es que esto no me convence nada porque
    la elección de V depende de la elección de U...
    y no se si eso luego se puede salvar a la
    hora de definir G...
    -/

    :

    True := by
  sorry



example {X : Type}
    (T : TopologicalSpace X)
    (hT : NormalTopoSpace T)
    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsClosed C2)

    (G : ℚ → Set X)
    (f : ℕ → ℚ)

    (hf0 : f 0 = 1)
    (hf1 : f 1 = 0)

    (hf : ∀ n : ℕ, 0 ≤ f n ∧ f n ≤ 1)
    (finy : f.Injective)

    (P : Finset ℕ)

    (hP : { n : ℕ | IsOpen (G (f n)) ∧
    (∀ m ∈ P, f n < f m → Closure (G (f n)) ⊆ G (f m)) })


    (h0 : 0 ∈ P)
    (h1 : 1 ∈ P)

    --(k : ℕ) (hk : k = P.card)

    (n : ℕ)

    (H : ℕ → Prop)
    (hH : H = fun n ↦ (n = 0) ∨ (n = 1) ∨ (∃ s ∈ P, (f s < f n ∧ (∀ m ∈ P, f m < f n → f m ≤ f s))))

    :

    H n := by

  apply Nat.strong_induction_on
  intro n hn

  have Hdef : H n = ((n = 0) ∨ (n = 1) ∨ (∃ s ∈ P, (f s < f n ∧ (∀ m ∈ P, f m < f n → f m ≤ f s))))
  exact congrFun hH n

  rw [Hdef]


  /-
  paso 1. Quiero ver que n no es 0 ni 1
  (seguramente hay formas más fáciles de hacerlo)
  -/

  have aux : n = 0 ∨ n > 0
  exact Nat.eq_zero_or_pos n
  cases' aux with hn' hn'

  · -- n=0
    rw [hn']
    left
    rfl

  · have aux : n = 1 ∨ n > 1
    exact LE.le.eq_or_gt hn'
    cases' aux with hn' hn'

    · -- n=1
      rw [hn']
      right
      left
      rfl

    · -- n not 0 or 1

  /-
  paso 2. si n no es 0 ni 1,
  entonces f n no es 0 ni 1 (f inyectiva)
  entonces puedo encontrar t,s en P tal que
  f t < f n < f s
  -/

      let I : Finset ℕ := P.filter (fun p ↦ f p < f n)
      -- nota: esto no son filtros jaja

      have hI : I.Nonempty
      use 1
      rw [Finset.mem_filter]
      constructor
      · exact h1
      · rw [hf1]
        specialize hf n
        cases' hf with hf _
        apply Ne.lt_of_le
        rw [← hf1]
        by_contra c
        apply finy at c
        linarith
        exact hf

      have hIP : I ⊆ P
      exact Finset.filter_subset (fun p ↦ f p < f n) P

      let hImem : ∀ i ∈ I, i ∈ P ∧ f i < f n
      intro i hi
      exact Finset.mem_filter.mp hi

      let i : ℕ := Finset.max' I hI

      #check Finset.le_max'

      have himax : ∀ m ∈ I, m ≤ i
      exact fun m a ↦ Finset.le_max' I m a

      right
      right
      use i

      constructor
      · apply hIP
        exact Finset.max'_mem I hI

      · constructor

        · specialize hImem i (by exact Finset.max'_mem I hI)
          exact hImem.right

        · intro m hmP hm
          -- ok aquí me he dado cuenta de que la he liado creo...

          sorry
