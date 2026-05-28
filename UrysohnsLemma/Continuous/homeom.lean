import Mathlib.Tactic

open TopologicalSpace

variable (u v : Universe)


#check Homeomorph

-- ejemplo de uso:

example (X Y: Type) [TopologicalSpace X] [TopologicalSpace Y]
    (H : Homeomorph X Y) : ∃ f : X → Y, Continuous f := by
  use H.toFun
  exact H.continuous_toFun

/-
PROPOSICIÓN: Sea f : X → Y una función biyectiva.
Son equivalentes:
1. f abierta
2. f cerrada
3. f⁻¹ continua
-/

def OpenFunction {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
    ∀ (U : Set X), IsOpen U → IsOpen (f '' U)

def ClosedFunction {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
    ∀ (C : Set X), IsClosed C → IsClosed (f '' C)


example (X Y: Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : f.Bijective) :
    OpenFunction f ↔ ClosedFunction f := by

  constructor <;> intro h
  · rw [ClosedFunction]
    rw [OpenFunction] at h
    intro C hC
    rw [← isOpen_compl_iff] at *
    specialize h Cᶜ hC
    rw [Set.image_compl_eq hf] at h
    exact h

  · rw [OpenFunction]
    rw [ClosedFunction] at *
    intro U hU
    rw [← compl_compl U, ] at hU
    rw [isOpen_compl_iff] at hU
    specialize h Uᶜ hU
    rw [← isOpen_compl_iff] at h
    rw [Set.image_compl_eq hf] at h
    simp at h
    exact h


#check Function.invFun


/-
example (X Y: Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : f.Bijective) :
    OpenFunction f ↔ Continuous (f.invFun) := by
  sorry
-/

lemma aux {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {g : Y → X}
    (h_inv : ∀ x, g (f x) = x) (h_inv' : ∀ y, f (g y) = y)
    (S : Set X) : f '' S = g ⁻¹' S := by
  ext y
  constructor <;> intro hy
  · simp at *
    cases' hy with x hx
    specialize h_inv x
    rw [hx.right] at h_inv
    rw [h_inv]
    exact hx.left
  · simp at *
    use g y
    constructor
    exact hy
    specialize h_inv' y
    exact h_inv'

-- Esto se debería poder poner con f.invFun :(
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (g : Y → X) (hf : Function.Bijective f)
    (h_inv : ∀ x, g (f x) = x) (h_inv' : ∀ y, f (g y) = y) :
    OpenFunction f ↔ Continuous g := by

  constructor <;> intro h
  · rw [OpenFunction] at h
    rw [continuous_def]
    intro s hs
    specialize h s hs
    rw [← aux h_inv h_inv' s]
    exact h

  · rw [OpenFunction]
    rw [continuous_def] at h
    intro U hU
    specialize h U hU
    rw [aux h_inv h_inv' U]
    exact h

/-
Proposición: f es homeomorfismo sii
f es biyectiva, continua y abierta
-/

/-
My definitions
-/

def InverseFunction {X Y : Type} (f : X → Y) (g : Y → X)
    : Prop :=
    (∀ x, g (f x) = x) ∧ ∀ y, f (g y) = y

def Homeomorphism {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
    f.Bijective ∧ Continuous f ∧
    (∃ g : Y → X, InverseFunction f g ∧ Continuous g)

/-
My definition is analogous to the one
in the Mathlib library
-/
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (H : Homeomorph X Y) :
    Homeomorphism H.toFun := by
  rw [Homeomorphism]
  constructor
  · exact H.bijective
  · constructor
    · exact H.continuous_toFun
    · use H.invFun
      constructor
      · exact ⟨H.left_inv, H.right_inv⟩
      · exact H.continuous_invFun

-- Cosas interesantes:
#check Homeomorph.continuous_toFun
#check Homeomorph.continuous_invFun
#check Homeomorph.bijective

noncomputable section

lemma bij_hasInverse {X Y : Type} (f : X → Y)
    (hf : f.Bijective) : ∃ (g : Y → X), InverseFunction f g := by

  rw [Function.Bijective] at hf
  cases' hf with hf1 hf2
  rw [Function.Injective] at hf1
  rw [Function.Surjective] at hf2

  let g : Y → X := fun y : Y ↦ Classical.choose (hf2 y)
  use g
  rw [InverseFunction]
  constructor

  · intro x

    let a := Classical.choose (hf2 (f x))
    let p := Classical.choose_spec (hf2 (f x))

    have h : g (f x) = a
    rfl

    have h1 : f (g (f x)) = f a
    exact congrArg f h

    have h2 : f a = f x
    exact p

    rw [← h1] at h2
    apply hf1 at h2
    exact h2

  · intro y

    have hg : ∃ a, (g y = a ∧ f a = y)
    use Classical.choose (hf2 y)
    let p := Classical.choose_spec (hf2 y)
    constructor
    rfl
    exact p

    cases' hg with a ha
    rw [ha.left]
    exact ha.right


-- reescribo esto para la nueva definición de función
-- inversa aunque no me acaba de convencer la def

def Inverse {X Y : Type} (f : X → Y) (hf : f.Bijective)
    : Y → X := Classical.choose (bij_hasInverse f hf)

lemma Inverse_is_Inverse {X Y : Type} (f : X → Y) (hf : f.Bijective) :
    InverseFunction f (Inverse f hf) := by

    let g := Classical.choose (bij_hasInverse f hf)
    let p := Classical.choose_spec (bij_hasInverse f hf)

    have hg : g = Inverse f hf
    rw [Inverse]

    rw [← hg]
    exact p


lemma f_open_iff_continuous_inv (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (g : Y → X) (hf : f.Bijective)
    (h_inv : ∀ x, g (f x) = x) (h_inv' : ∀ y, f (g y) = y) :
    OpenFunction f ↔ Continuous g := by

  constructor <;> intro h
  · rw [OpenFunction] at h
    rw [continuous_def]
    intro s hs
    specialize h s hs
    rw [← aux h_inv h_inv' s]
    exact h

  · rw [OpenFunction]
    rw [continuous_def] at h
    intro U hU
    specialize h U hU
    rw [aux h_inv h_inv' U]
    exact h

-- UTILIZANDO SOLO QUE ES BIYECTIVA

lemma f_open_iff_continuous_inv' (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : f.Bijective) :
    OpenFunction f ↔ Continuous (Inverse f hf) := by

  let g := Inverse f hf

  have p : InverseFunction f g
  exact Inverse_is_Inverse f hf

  rw [InverseFunction] at p
  cases' p with h_inv h_inv'

  constructor <;> intro h
  · rw [OpenFunction] at h
    rw [continuous_def]
    intro s hs
    specialize h s hs
    rw [← aux h_inv h_inv' s]
    exact h

  · rw [OpenFunction]
    rw [continuous_def] at h
    intro U hU
    specialize h U hU
    rw [aux h_inv h_inv' U]
    exact h



example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Homeomorphism f ↔
    f.Bijective ∧ Continuous f ∧ OpenFunction f := by

  sorry
  /-
  rw [Homeomorphism]
  constructor <;> intro h

  constructor
  exact h.left
  constructor
  exact h.right.left
  rw [f_open_iff_continuous_inv]
  sorry
  -/
