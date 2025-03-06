import Leantest.MyDefs.my_denumerableQ

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

lemma r_options (n : ℕ) (hn : n > 1) : r n = 1 ∨ r n > 1 := by
  have cases : r n = 0 ∨ r n > 0
  exact Nat.eq_zero_or_pos (r n)
  cases' cases with c1 c2
  by_contra c
  have hs := r_is_not_0 n hn
  exact hs c1
  exact LE.le.eq_or_gt c2


lemma s_is_not_1 (n : ℕ) (hn : n > 1) : s n ≠ 1 := by
  by_contra c
  have hs := (s_prop n hn).right.left
  simp [c, f_prop.right.right] at hs
  have h := (f_in_icc01 n).left
  exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false hs h -- exact?

lemma s_options (n : ℕ) (hn : n > 1) : s n = 0 ∨ s n > 1 := by
  have cases : s n = 0 ∨ s n > 0
  exact Nat.eq_zero_or_pos (s n)
  cases' cases with c1 c2
  left; exact c1
  right
  have cases : s n = 1 ∨ s n > 1
  exact LE.le.eq_or_gt c2
  cases' cases with c1 c2
  by_contra
  have hs := s_is_not_1 n hn
  exact hs c1
  exact c2
