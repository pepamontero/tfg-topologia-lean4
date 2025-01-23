import Leantest.Separation.normal

/-
función que numera los racionales en [0, 1]
-/

def Q : Set ℚ := {q : ℚ | 0 ≤ q ∧ q ≤ 1} -- `ℚ ∩ [0, 1]`

lemma Q1 : 1 ∈ Q := by simp [Q]
lemma Q0 : 0 ∈ Q := by simp [Q]

lemma hf : ∃ f : ℕ → Q, (f.Bijective ∧ f 0 = ⟨1, Q1⟩  ∧ f 1 = ⟨0, Q0⟩) := by
  sorry

noncomputable def f : ℕ → Q := Classical.choose hf

lemma f_prop : (f.Bijective ∧ f 0 = ⟨1, Q1⟩  ∧ f 1 = ⟨0, Q0⟩) := by
  let hf := Classical.choose_spec hf
  exact hf

lemma f_in_icc01 : ∀ n : ℕ, ⟨0, Q0⟩ ≤ f n ∧ f n ≤ ⟨1, Q1⟩ := by
  intro n
  constructor
  · exact (f n).property.left -- x.property handles membership, here f n is recognized as an element of Q
  · exact (f n).property.right


/-

-/


example (a b : ℕ) (h1 : a ≤ b) (h2 : a ≠ b) : a < b := by exact Nat.lt_of_le_of_ne h1 h2

-- FINDING R
lemma exists_r (n : ℕ) (hn : n > 1) : ∃ r ∈ Finset.range n,
    ((f r < f n) ∧
    (∀ m ∈ Finset.range n, f m < f n → f m ≤ f r)) := by

  let R : Finset ℕ := (Finset.range n).filter (fun m ↦ f m < f n)
  -- tomamos `R = {m ∈ {0, 1, ..., n-1} | f m < f n}`

  -- vemos que R no es vacío
  have hR : R.Nonempty
  · use 1
    simp [R]
    constructor
    · exact hn
    · have aux : f 1 ≤ f n
      · rw [f_prop.right.right]
        exact (f n).property.left
      have aux' : f 1 ≠ f n
      · by_contra c
        apply (f_prop.left).left at c
        linarith
      exact lt_of_le_of_ne aux aux'

  let fR : Finset Q := R.image f
  -- tomamos el conjunto de as imágenes de R

  -- vemos que no es vacío
  let hfR : fR.Nonempty
  exact (Finset.image_nonempty).mpr hR

  -- tomamos el máximo de las imágenes
  let fr := Finset.max' fR hfR
  have hfr : fr ∈ fR
  exact Finset.max'_mem fR hfR

  -- condición de máximo
  have hfr' : ∀ fm ∈ fR, fm ≤ fr
  exact fun fm a ↦ Finset.le_max' fR fm a
  have hfr' : ∀ m ∈ R, f m ≤ fr
  intro m hm
  have aux : f m ∈ fR
  exact Finset.mem_image_of_mem f hm
  exact hfr' (f m) aux

  -- tomamos el argumento de fr, fr = f r
  have hfr'' : ∃ r ∈ R, f r = fr
  exact Finset.mem_image.mp hfr
  cases' hfr'' with r hr

  use r -- probamos que este r nos vale
  simp [R] at hr

  constructor

  · -- `r ∈ {0, 1, ..., n-1}`?
    simp
    exact hr.left.left

  constructor

  · -- `f r < f n`?
    exact hr.left.right

  · -- si `m ∈ {0, 1, ..., n-1}`, `f m ≤ f r`?
    intro m hm hmn

    have aux : m ∈ R
    simp [R]
    constructor
    · simp at hm
      exact hm
    · exact hmn

    rw [hr.right]
    exact hfr' m aux

noncomputable def r : ℕ → ℕ := fun n ↦
  if h : n > 1 then Classical.choose (exists_r n h)
  else 0

lemma r_prop (n : ℕ) (hn : n > 1) : (
  (r n ∈ Finset.range n) ∧
  (f (r n) < f n) ∧
  (∀ m ∈ Finset.range n, f m < f n → f m ≤ f (r n))
) := by
  let h := Classical.choose_spec (exists_r n hn)
  simp [r]
  simp [hn]
  simp at h
  exact h


-- FINDING S
example (n : ℕ) (hn : n > 1) : ∃ r ∈ Finset.range n,
    ((f r < f n) ∧
    (∀ m ∈ Finset.range n, f m < f n → f m ≤ f r)) := by

  induction' hn with n HI

  · --cb
    simp
    use 1


    sorry

  · --cr
    sorry





/-
Lo que he pensado ahora es:
1. realmente no necesito inducción completa??
  porque me vale para cada m < n+1 el G(m) de la G obtenida en el paso n
  (creo)

2. a lo mejor solo tendría que hacerlo para todo n
  tal que cumpla f n ∈ [0, 1]
  y luego debajo y encima del 0 ya pongo empty?? no se
-/

lemma loqueyoquiero {X : Type} [T : TopologicalSpace X]
    (hT : NormalTopoSpace T)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n : ℕ, (
      ∃ G : ℕ → Set X, (
        (∀ p : ℕ, p ≤ n → IsOpen (G p))
        ∧
        (∀ p q : ℕ, p ≤ n → q ≤ n → f p < f q → Closure (G p) ⊆ G q)
        )
    ) := by


  intro n
  induction' n with n HI

  · --caso base
    let G : ℕ → Set X := fun n ↦ C2ᶜ
    use G
    constructor
    · intro p hp
      simp [G]
      exact { isOpen_compl := hC2 }

    · intro p q hp hq hpq
      simp at hp hq
      rw [hp, hq] at hpq
      by_contra
      exact (lt_self_iff_false (f 0)).mp hpq

  · -- caso recursivo

    /-
    NOTA: igual aquí debería meter otro caso para n = 1,
    porque si no como que no estoy definiendo G (1) = Classical.choose...

    osea la movida es que aquí para la recursión necesito que haya al menos 2 elementos ya definidos
    -/
    rw [characterization_of_normal] at hT

    cases' HI with G' hG'

    let G : ℕ → Set X := fun m ↦
      if h : f m < 0 then ∅
      else if h : f m > 1 then Set.univ
      else if h : m < n + 1 then G' m
      else ∅

    use G

    constructor
    · sorry

    · sorry
