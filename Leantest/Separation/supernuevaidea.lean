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

example (a b : ℕ) : a = b → f a = f b := by exact fun a_1 ↦ congrArg f a_1

lemma f_in_icc01 : ∀ n : ℕ, ⟨0, Q0⟩ ≤ f n ∧ f n ≤ ⟨1, Q1⟩ := by
  intro n
  constructor
  · exact (f n).property.left -- x.property handles membership, here f n is recognized as an element of Q
  · exact (f n).property.right


/-
definición de las funciones r y s:
dado n ∈ ℕ, r y s devuelven naturales tales que
    f r < f n < f s
y estas son las mejores elecciones de r y s
-/


-- existencia de tal r
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

-- definición de r y propiedades

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



-- existencia de tal s
lemma exists_s (n : ℕ) (hn : n > 1) : ∃ s ∈ Finset.range n,
    ((f n < f s) ∧
    (∀ m ∈ Finset.range n, f n < f m → f s ≤ f m)) := by

  let S : Finset ℕ := (Finset.range n).filter (fun m ↦ f n < f m)
  -- tomamos `S = {m ∈ {0, 1, ..., n-1} | f n < f m}`

  -- vemos que S no es vacío
  have hS : S.Nonempty
  · use 0
    simp [S]
    constructor
    · linarith
    · have aux : f n ≤ f 0
      · rw [f_prop.right.left]
        exact (f n).property.right
      have aux' : f n ≠ f 0
      · by_contra c
        apply (f_prop.left).left at c
        linarith
      exact lt_of_le_of_ne aux aux'

  let fS : Finset Q := S.image f
  -- tomamos el conjunto de as imágenes de S

  -- vemos que no es vacío
  let hfS : fS.Nonempty
  exact (Finset.image_nonempty).mpr hS

  -- tomamos el mínimo de las imágenes
  let fs := Finset.min' fS hfS
  have hfs : fs ∈ fS
  exact Finset.min'_mem fS hfS

  -- condición de mínimo
  have hfs' : ∀ fm ∈ fS, fs ≤ fm
  exact fun fm a ↦ Finset.min'_le fS fm a
  have hfs' : ∀ m ∈ S, fs ≤ f m
  intro m hm
  have aux : f m ∈ fS
  exact Finset.mem_image_of_mem f hm
  exact hfs' (f m) aux

  -- tomamos el argumento de fs, fs = f s
  have hfs'' : ∃ s ∈ S, f s = fs
  exact Finset.mem_image.mp hfs
  cases' hfs'' with s hs

  use s -- probamos que este r nos vale
  simp [S] at hs

  constructor

  · -- `s ∈ {0, 1, ..., n-1}`?
    simp
    exact hs.left.left

  constructor

  · -- `f n < f s`?
    exact hs.left.right

  · -- si `m ∈ {0, 1, ..., n-1}`, `f r ≤ f m`?
    intro m hm hmn

    have aux : m ∈ S
    simp [S]
    constructor
    · simp at hm
      exact hm
    · exact hmn

    rw [hs.right]
    exact hfs' m aux


-- definición de s y propiedades

noncomputable def s : ℕ → ℕ := fun n ↦
  if h : n > 1 then Classical.choose (exists_s n h)
  else 0

lemma s_prop (n : ℕ) (hn : n > 1) : (
  (s n ∈ Finset.range n) ∧
  (f n < f (s n)) ∧
  (∀ m ∈ Finset.range n, f n < f m → f (s n) ≤ f m)
) := by
  let h := Classical.choose_spec (exists_s n hn)
  simp [s]
  simp [hn]
  simp at h
  exact h


-- otras propiedades de r y s

lemma r_is_not_0 (n : ℕ) (hn : n > 1) : r n ≠ 0 := by
  by_contra c
  have hr := (r_prop n hn).right.left
  simp [c, f_prop.right.left] at hr
  have h := (f_in_icc01 n).right
  exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false hr h -- exact?


lemma s_is_not_1 (n : ℕ) (hn : n > 1) : s n ≠ 1 := by
  by_contra c
  have hs := (s_prop n hn).right.left
  simp [c, f_prop.right.right] at hs
  have h := (f_in_icc01 n).left
  exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false hs h -- exact?


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


  sorry

#check Nat.strong_induction_on

theorem my_strong_induction (n : ℕ) (N : ℕ) (hn : n > N) (P : ℕ → Prop)
    (h : (∀ m < n, m > N → P m) → P n) :
    (P n) := by

  let k := n - N
  have k_def : k = n - N := by rfl
  have hk : n = k + N
  · sorry
  rw [hk]

  have cases : k = 0 ∨ k > 0 := by sorry

  cases' cases with hk0 hk0

  · rw [hk0]

    sorry


  let Q : ℕ → Prop := fun k ↦ P (k + N)
  have Q_def : ∀ k, Q k = P (k + N)
  · sorry
  rw [← Q_def]

  apply Nat.strong_induction_on
  intro r hr
  simp [Q]
  simp [Q] at hr




lemma somethingnew {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    (G : ℕ → Set X)
    (hG :
      (∀ n, IsOpen (G n))
      ∧
      (∀ n > 1,
        (Closure (G (r n)) ⊆ G n) ∧
        (Closure (G n) ⊆ G (s n)))
    )

    :

    ∀ n > 1, ∀ m > 1, f n < f m → Closure (G n) ⊆ G m
     := by

  intro n hn m hm hnm

  let P : ℕ → Prop := fun k ↦ Closure (G k) ⊆ G m
  have hP : P n = (Closure (G n) ⊆ G m) := by rfl

  rw [← hP]

  apply my_strong_induction n 1 hn P
  intro hi

  simp [P]
  simp [P] at hi


  have hsn := (s_prop n hn).left
  simp at hsn

  have cases : s n = 0 ∨ s n > 1 := by sorry
  cases' cases with hsn0 hsn1

  · -- si s n = 0 entonces ni idea
    sorry

  · -- si s n > 1
    specialize hi (s n) hsn hsn1
    trans G (s n)
    · exact (hG.right n hn).right
    · trans Closure (G (s n))
      · exact set_inside_closure (G (s n))
      · exact hi

  have hsk := (s_prop k aux).left
  simp at hsk
  specialize hk (s k') hsk

  trans G (s k')

  · exact (hG.right k' aux).right
  · trans Closure (G (s k'))
    · exact set_inside_closure (G (s k'))
    · exact hk



  have hk_aux : k ≠ 1
  · by_contra c
    specialize hk 0 (by linarith)
    simp at hk

  have kk_aux' : k ≠ 0
  · sorry

  ·

  cases' k with k

  · -- caso k = 0
    simp [P]

    let Q : ℕ → Prop := fun k ↦ Closure (G 0) ⊆ G k
    have hQ : Q m = (Closure (G 0) ⊆ G m) := by rfl
    rw [← hQ]

    apply Nat.strong_induction_on
    intro l hl

    simp [Q]
    simp [Q] at hl

    sorry

  · -- caso k > 0
    cases' k with k

    · -- caso k = 1
      sorry

    · -- caso k > 1

      let k' := k+1+1

      have aux : k' > 1 := by linarith

      simp [P]
      simp [P] at hk
      have hsk := (s_prop k' aux).left
      simp at hsk
      specialize hk (s k') hsk

      trans G (s k')

      · exact (hG.right k' aux).right
      · trans Closure (G (s k'))
        · exact set_inside_closure (G (s k'))
        · exact hk



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
