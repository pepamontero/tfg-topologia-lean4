import Mathlib.Tactic
import Mathlib.Data.Rat.Denumerable

lemma bijective_nat_rat : ∃ f : ℕ → ℚ, f.Bijective  := by
    have f := (Rat.instDenumerable.eqv).symm
    use f
    exact f.bijective

/-
things i will need:
-/

/-
If `A ⊆ B`, then `Cardinal A ≤ Cardinal B`
-/
#check Cardinal.mk_le_mk_of_subset

/-
The Cardinal of `Set.univ` is the same
as the cardinal of the Type of Set.univ
-/
#check Cardinal.mk_univ

/-
The Cardinal of `ℚ` is `aleph0`
-/
#check Cardinal.mkRat

/-
It is equivalent for a set `A`:
  1. `A` is Finite
  2. `Cardinal A < aleph 0`
-/
#check Cardinal.lt_aleph0_iff_set_finite


lemma non_finite_rat_set_cardinal_aleph0 (A : Set ℚ) (hA : ¬ A.Finite) : Cardinal.mk ↑A = Cardinal.aleph0 := by

  apply le_antisymm

  · have aux : A ⊆ Set.univ := by intro a _; trivial
    apply Cardinal.mk_le_mk_of_subset at aux
    rw [@Cardinal.mk_univ ℚ, Cardinal.mkRat] at aux
    exact aux

  · rw [← @Cardinal.lt_aleph0_iff_set_finite ℚ A] at hA
    exact le_of_not_gt hA


/-
Definition of the set `Q = ℚ ∩ [0, 1]`
-/

def Q : Set ℚ := {q : ℚ | 0 ≤ q ∧ q ≤ 1} -- `ℚ ∩ [0, 1]`

lemma Q1 : 1 ∈ Q := by simp [Q]
lemma Q0 : 0 ∈ Q := by simp [Q]


/-
Prop: Q has cardinal aleph_0
-/

lemma Q_not_finite : ¬ Q.Finite := by

  let f : ℕ → ℚ := fun n ↦ 1 / (n + 1)

  have h_subset : Set.range f ⊆ Q
  · intro q hq
    obtain ⟨n, hn⟩ := hq
    simp [f] at hn
    rw [← hn]
    constructor
    · apply inv_nonneg_of_nonneg
      linarith
    · apply inv_le_one
      linarith

  have f_injective : f.Injective
  · intro n m hnm
    simp [f] at hnm
    exact hnm

  have f_infinite : Set.Infinite (Set.range f)
  · exact Set.infinite_range_of_injective f_injective

  exact Set.Infinite.mono h_subset f_infinite


lemma cardinalQ_aleph0 : Cardinal.mk Q = Cardinal.aleph0 := by
  apply non_finite_rat_set_cardinal_aleph0
  exact Q_not_finite

lemma Q_equiv_rat : Nonempty (ℚ ≃ Q) := by
  rw [← Cardinal.eq, Cardinal.mkRat]
  exact cardinalQ_aleph0.symm

lemma bijective_rat_Q : ∃ f : ℚ → Q, f.Bijective := by
  have h := Q_equiv_rat
  apply Set.exists_mem_of_nonempty at h
  obtain ⟨f⟩ := h
  use f
  exact Equiv.bijective f

lemma bijetcive_nat_Q : ∃ f : ℕ → Q, f.Bijective := by
  have h1 := bijective_nat_rat
  have h2 := bijective_rat_Q
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  use (g ∘ f)
  exact Function.Bijective.comp hg hf


/-
lastly we want to proof that:
if `f : A → B` is bijective
then for every a, b ∈ A,
`g : A → B` defined as:
  a ↦ f b
  b ↦ f a
  x ≠ a, b ↦ f x

is also bijective
-/

def permute_f {X Y : Type} [DecidableEq X]
    (f : X → Y) (a b : X)
    : X → Y :=
    fun x ↦
      if x = a then f b
      else if x = b then f a
      else f x


lemma permute_f_injectivity {X Y : Type} [DecidableEq X]
    {f : X → Y} (a b : X)
    (h : f.Injective) :
    (permute_f f a b).Injective := by

  intro x y hxy

  if hxa : x = a then
    if hya : y = a then rw [hxa, hya]
    else if hyb : y = b then
      if hab : a = b then rw [hxa, hyb, hab]
      else
        have hab : ¬ b = a := by exact fun a_1 ↦ hab (h (congrArg f (id (Eq.symm a_1))))
        simp [hxa, hya, hyb, hab, permute_f] at hxy
        apply h at hxy
        exact False.elim (hab hxy)
    else
      simp [hxa, hya, hyb, permute_f] at hxy
      apply h at hxy
      exact False.elim (hyb hxy.symm)

  else if hxb : x = b then
    if hya : y = a then
      if hab : a = b then rw [hxb, hya, hab.symm]
      else
        have hab : ¬ b = a := by exact fun a_1 ↦ hab (h (congrArg f (id (Eq.symm a_1))))
        simp [hxa, hxb, hya, hab, permute_f] at hxy
        apply h at hxy
        exact False.elim (hab hxy.symm)
    else if hyb : y = b then rw [hyb, hxb]
    else
      if hab : a = b then
        simp [hxa, hxb, hya, hyb, permute_f, hab] at hxy
        apply h at hxy
        exact False.elim (hyb hxy.symm)
      else
        have hab : ¬ b = a := by exact fun a_1 ↦ hab (h (congrArg f (id (Eq.symm a_1))))
        simp [hxa, hxb, hya, hyb, permute_f, hab] at hxy
        apply h at hxy
        exact False.elim (hya hxy.symm)

  else
    if hya : y = a then
      simp [hxa, hxb, hya, permute_f] at hxy
      apply h at hxy
      exact False.elim (hxb hxy)
    else if hyb : y = b then
      if hab : a = b then
        simp [hxa, hxb, hya, hyb, permute_f, hab] at hxy
        apply h at hxy
        exact False.elim (hxb hxy)
      else
        have hab : ¬ b = a := by exact fun a_1 ↦ hab (h (congrArg f (id (Eq.symm a_1))))
        simp [hxa, hxb, hya, hyb, permute_f, hab] at hxy
        apply h at hxy
        exact False.elim (hxa hxy)
    else
      simp [hxa, hxb, hya, hyb, permute_f] at hxy
      apply h at hxy
      exact hxy


lemma permute_f_surjectivity {X Y : Type} [DecidableEq X]
    {f : X → Y} (a b : X)
    (h : f.Surjective) :
    (permute_f f a b).Surjective := by

  intro y

  if hya : y = f a then
    use b
    if hab : a = b then
      simp [permute_f, hab]
      rw [← hab, hya]
    else
      have hab : b ≠ a := by exact fun a_1 ↦ hab (id (Eq.symm a_1))
      simp [permute_f, hab]
      exact hya.symm

  else if hyb : y = f b then
    use a
    if hab : a = b then
      simp [permute_f, hab]
      rw [← hab, hyb, hab]
    else
      have hab : b ≠ a := by exact fun a_1 ↦ hab (id (Eq.symm a_1))
      simp [permute_f, hab]
      exact hyb.symm

  else
    obtain ⟨c, hc⟩ := h y
    use c
    have hca : c ≠ a
    · by_contra co
      rw [co] at hc
      exact hya hc.symm
    have hcb : c ≠ b
    · by_contra co
      rw [co] at hc
      exact hyb hc.symm
    simp [permute_f, hca, hcb, hc]


lemma permute_f_bijectivity {X Y : Type} [DecidableEq X]
    {f : X → Y} (a b : X)
    (h : f.Bijective) :
    (permute_f f a b).Bijective := by
  constructor
  · exact permute_f_injectivity a b h.left
  · exact permute_f_surjectivity a b h.right


lemma hf : ∃ f : ℕ → Q, (f.Bijective ∧ f 0 = ⟨1, Q1⟩ ∧ f 1 = ⟨0, Q0⟩) := by
  obtain ⟨f, hf⟩ := bijetcive_nat_Q

  if H : (f 0 = ⟨1, Q1⟩ ∧ f 1 = ⟨0, Q0⟩) then
    use f
  else if H' : f 0 = ⟨1, Q1⟩ then
    simp [H'] at H
    obtain ⟨n, hn⟩ := hf.right ⟨0, Q0⟩
    use permute_f f 1 n
    constructor
    · exact permute_f_bijectivity 1 n hf
    constructor
    · have aux : 0 ≠ n
      · by_contra c
        rw [← c] at hn
        rw [hn] at H'
        exact ne_of_beq_false rfl H'
      simp [permute_f, aux, H']
    · simp [permute_f, hn]

  else if H'' :  f 1 = ⟨0, Q0⟩ then
    simp [H''] at H
    obtain ⟨n, hn⟩ := hf.right ⟨1, Q1⟩
    use permute_f f 0 n
    constructor
    · exact permute_f_bijectivity 0 n hf
    constructor
    · simp [permute_f, hn]
    · have aux : 1 ≠ n
      · by_contra c
        rw [← c] at hn
        rw [hn] at H''
        exact ne_of_beq_false rfl H''.symm
      simp [permute_f, aux, H'']

  else
    obtain ⟨n, hn⟩ := hf.right ⟨1, Q1⟩
    let g := permute_f f 0 n
    have hg : g.Bijective := by exact permute_f_bijectivity 0 n hf

    obtain ⟨m, hm⟩ := hg.right ⟨0, Q0⟩
    let h := permute_f g 1 m
    have hh : h.Bijective := by exact permute_f_bijectivity 1 m hg

    use h
    constructor
    · exact hh
    constructor
    · have aux : 0 ≠ m
      · by_contra c
        rw [← c] at hm
        simp [g, permute_f, hn] at hm
        exact ne_of_beq_false rfl hm.symm
      simp [h, permute_f, aux]
      simp [g, permute_f, hn]
    · simp [h, permute_f, hm]


noncomputable def f : ℕ → Q := Classical.choose hf


lemma f_prop : (f.Bijective ∧ f 0 = ⟨1, Q1⟩  ∧ f 1 = ⟨0, Q0⟩) := by
  let hf := Classical.choose_spec hf
  exact hf

lemma f_in_icc01 : ∀ n : ℕ, ⟨0, Q0⟩ ≤ f n ∧ f n ≤ ⟨1, Q1⟩ := by
  intro n
  constructor
  · exact (f n).property.left -- x.property handles membership, here f n is recognized as an element of Q
  · exact (f n).property.right


lemma f_has_inverse :  ∃ g, Function.LeftInverse g f ∧ Function.RightInverse g f
  := by
  rw [← Function.bijective_iff_has_inverse]
  exact f_prop.left

noncomputable def f_inv : Q → ℕ := Classical.choose f_has_inverse

lemma f_inv_prop : (∀ n : ℕ, f_inv (f n) = n) ∧
    (∀ q : Q, f (f_inv q) = q) := by
  let h := Classical.choose_spec f_has_inverse
  exact h

lemma f_inv_0 : f_inv ⟨0, Q0⟩ = 1 := by
  apply f_prop.left.left
  rw [f_inv_prop.right ⟨0, Q0⟩]
  exact f_prop.right.right.symm

lemma f_inv_1 : f_inv ⟨1, Q1⟩ = 0 := by
  apply f_prop.left.left
  rw [f_inv_prop.right ⟨1, Q1⟩]
  exact f_prop.right.left.symm
