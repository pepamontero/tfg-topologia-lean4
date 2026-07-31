import VersoManual
import Docs.Papers

open Verso.Genre Manual
open Verso.Code.External
open Verso.Genre.Manual.Docs (citetOther citepOther citehereOther)
open Docs (refWillard2012General)

set_option pp.rawOnError true
-- Keep this in every translated chapter so bibliography text renders in English:
set_option docs.bib.lang "en"
set_option verso.exampleProject "../../.."
set_option verso.exampleModule "UrysohnsLemma.BasicProp.basic"

#doc (Manual) "Topological Spaces in Lean" =>
%%%
tag := "espacios-topologicos"
file := "espacios-topologicos"
%%%

In this section we will see how some basic concepts of general topology are represented in Lean. The goal is not to develop the complete theory, but to show concrete examples of formal definitions and proofs, which serve as a first contact with working in Lean on topological spaces.

The mathematical definitions and results used are the usual ones in general topology. Although I initially based this work on the notes I took in the Elementary Topology course, I have later checked them against{citepOther refWillard2012General}[] as a standard reference.

# Topological spaces
%%%
file := "espacios"
%%%

## Definition 3.1 (Topological space)
%%%
tag := "def-espacio-topologico"
number := false
%%%

Let $`X` be a set and $`\mathcal{T}` a collection of subsets of $`X` such that

1. The sets $`\emptyset` and $`X` belong to $`\mathcal{T}`.
1. Any finite intersection of elements of $`\mathcal{T}` belongs to $`\mathcal{T}`.
1. Any arbitrary union of elements of $`\mathcal{T}` belongs to $`\mathcal{T}`.

Then we will say that $`\mathcal{T}` is a _topology_ on $`X`, that $`(X, \mathcal{T})` is a _topological space_ and that the elements of $`\mathcal{T}` are _open_ in this space.

In Lean, this definition is written as a structure consisting of four elements:

```anchor topologicalSpace_class_quote (module := UrysohnsLemma.Docs.Espacios)
class TopologicalSpace (X : Type u) where
  IsOpen : Set X → Prop
  isOpen_univ : IsOpen Set.univ
  isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)
```

The first element, `IsOpen`, is a function taking each set of $`X` to a proposition, that is, it is a description of the elements of $`\mathcal{T}` as the set `{U ∈ Set (X) | IsOpen U}`. The other three elements are proofs of the properties in the definition.

Let us look at some examples and their proofs in Lean.

## Example 3.1
%%%
tag := "ex-topologia-discreta"
number := false
%%%

Let $`X` be any set. Consider the collection of all subsets of $`X`, $`\mathcal{T} = \mathcal{P}(X)`. Then $`\mathcal{T}` is a topology on $`X`, which we call the _discrete topology_.

*Proof.* We can describe $`\mathcal T` as `{U ∈ Set (X) | true}`, because `IsOpen` is true for any $`U`.

```anchor DiscreteTopo_isOpen_field (module := UrysohnsLemma.TopoSpaces.discrete)
def DiscreteTopo (X : Type) : TopologicalSpace X where
  IsOpen (_ : Set X) := true
```

Now, proving the remaining properties is easy:

```anchor DiscreteTopo_isOpen_univ_partial (module := UrysohnsLemma.TopoSpaces.discrete)
  isOpen_univ := by
```

Applying the function `fun x ↦ true` to any set always returns `true`, so it suffices to use `trivial`.

```anchor DiscreteTopo (module := UrysohnsLemma.TopoSpaces.discrete)
@[reducible]
def DiscreteTopo (X : Type) : TopologicalSpace X where
  IsOpen (_ : Set X) := true
  isOpen_univ := by
    trivial
  isOpen_inter := by
    intros
    trivial
  isOpen_sUnion := by
    intros
    trivial
```
∎

## Example 3.2
%%%
tag := "ex-topologia-trivial"
number := false
%%%

Let $`X` be any set. Consider the collection $`\mathcal{T}=\{\emptyset, X\}`. Then $`\mathcal{T}` is a topology on $`X`, which we call the _trivial topology_.

*Proof.* We can describe $`\mathcal{T}` as `{U ∈ Set (X) | U = X ∨ U = ∅}`.

```anchor TrivialTopology_isOpen_field (module := UrysohnsLemma.TopoSpaces.trivial)
@[reducible]
def TrivialTopology (X : Type) : TopologicalSpace X where
  IsOpen (s : Set X) := s = Set.univ ∨ s = ∅
```

The first condition holds trivially: we want to see $`X = X \lor X = \emptyset`.

```anchor TrivialTopology_isOpen_univ (module := UrysohnsLemma.TopoSpaces.trivial)
  isOpen_univ := by
    left
    rfl
```

Let us now consider two open sets (`intro`). We distinguish cases:

```anchor TrivialTopology_isOpen_inter_partial (module := UrysohnsLemma.TopoSpaces.trivial)
  isOpen_inter := by
    intro s t hs ht
    cases' hs with hs_univ hs_empty
    cases' ht with ht_univ ht_empty
```

If both are $`X`, the intersection will be $`X` and therefore open. If one of the two is empty, then the intersection is empty, also open.

```anchor TrivialTopology_isOpen_inter_cases (module := UrysohnsLemma.TopoSpaces.trivial)
    · left -- 1. both are univ
      rw [hs_univ, ht_univ]
      simp
    · right -- 2. t is empty
      rw [ht_empty]
      simp
    · right -- 3. s is empty
      rw [hs_empty]
      simp
```

Finally, consider an arbitrary collection $`S` of open sets. To see whether the union is open, we consider two different cases: either $`X` is in $`S`, in which case the union is $`X`, or it is not, in which case all the sets in $`S` are the empty set and so is the union.

```anchor TrivialTopology_isOpen_sUnion (module := UrysohnsLemma.TopoSpaces.trivial)
  isOpen_sUnion := by
    intro S hS

    cases' Classical.em (Set.univ ∈ S) with h1 h2
    -- h1 : Set.univ ∈ S
    -- h2 : Set.univ ∉ S

    · left
      ext s
      constructor <;> intro hs
      · trivial
      · use Set.univ -- uses h1 implicitly to close the goal

    · right
      simp
      intro s hs
      specialize hS s hs
      cases' hS with hS hS
      · by_contra
        rw [hS] at hs
        exact h2 hs
      · exact hS
```
∎

## Example 3.3
%%%
number := false
%%%

Consider the real line and the usual definition of an open set in $`\mathbb{R}`, that is, $`A \subseteq \mathbb{R}` is open if and only if for each point $`x \in A` there exists an open ball centred at $`x` entirely contained in $`A`. Let $`\mathcal{T}` be the collection of these open sets. Then $`\mathcal{T}` is a topology on $`\mathbb{R}`, which we call the _usual topology_.

*Proof.* In Lean, we can describe this topological space by giving its elements in the following way, where each object is defined beforehand.

```anchor UsualTopology_def (module := UrysohnsLemma.TopoSpaces.usual)
def UsualTopology : TopologicalSpace ℝ where
  IsOpen := Real.IsOpen
  isOpen_univ := Real.isOpen_univ
  isOpen_inter := Real.isOpen_inter
  isOpen_sUnion := Real.isOpen_sUnion
```

The definition of an open set can be written like this:

```anchor Real_IsOpen_def (module := UrysohnsLemma.TopoSpaces.usual)
def Real.IsOpen (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∃ δ > 0, ∀ y : ℝ, x - δ < y ∧ y < x + δ → y ∈ s
```

We give the proof for the finite intersection. The others use similar mechanisms.

Let, therefore, $`s` and $`t` be two subsets of $`\mathcal{T}`. Let $`x \in t \cap s`; we want to see that there exists an open ball centred at $`x` and contained in $`t \cap s`.

```anchor Real_isOpen_inter_sig_partial (module := UrysohnsLemma.TopoSpaces.usual)
lemma Real.isOpen_inter (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  intro x hx
```

Since $`x \in s`, there exists a $`\delta_1>0` (`hδ1`) such that $`B_{\delta_1}(x) \subseteq s` (`hs`). Analogously, there exists a $`\delta_2>0` (`hδ2`) such that $`B_{\delta_2}(x) \subseteq t` (`ht`). It suffices to take $`\delta = \min \{\delta_1, \delta_2\}`.

```anchor Real_isOpen_inter_obtain (module := UrysohnsLemma.TopoSpaces.usual)
  obtain ⟨δ1, hδ1, hs⟩ := hs x hx.left
  obtain ⟨δ2, hδ2, ht⟩ := ht x hx.right
  use min δ1 δ2
```

Trivially $`\delta > 0`.

```anchor Real_isOpen_inter_constructor_partial (module := UrysohnsLemma.TopoSpaces.usual)
  constructor
  · exact lt_min hδ1 hδ2
```

To see that $`B_\delta (x) \subseteq s \cap t`, we consider $`y \in B_\delta(x)` and want to see that $`y \in s` and that $`y \in t`. To see $`y \in s`, since $`B_{\delta_1}(x) \subseteq s` (`hs`), it suffices to see $`y \in B_{\delta_1}(x)`.

```anchor Real_isOpen_inter_intro_y (module := UrysohnsLemma.TopoSpaces.usual)
  · intro y hy
    constructor
    · apply hs
```

Actually, this condition reduces to two inequalities, which are easy to prove given that $`\delta \leq \delta_1` (`hδ`).

```anchor Real_isOpen_inter_hs_finish (module := UrysohnsLemma.TopoSpaces.usual)
      have hδ := min_le_left δ1 δ2
      constructor
      all_goals linarith
```

Proving that $`y \in t` is analogous. ∎

## Open sets

As we have said, the open sets in a topological space are the elements of the topology. In Lean, it is a function `TopologicalSpace.IsOpen` of type `Set X → Prop`. We can use this definition directly to prove that an open set is indeed open.

### Example 3.4
%%%
number := false
%%%

By definition, the universe, $`X`, is always open. Indeed:

```anchor univ_isOpen_example (module := UrysohnsLemma.Docs.Espacios)
example (X : Type) [T : TopologicalSpace X] : T.IsOpen Set.univ := by
  exact TopologicalSpace.isOpen_univ
```

### Example 3.5
%%%
number := false
%%%

In Definition {ref "def-espacio-topologico"}[3.1], we had the condition $`\emptyset \in \mathcal{T}`, a condition that does not appear in the Mathlib definition.

It can be proved that the empty set is open from the remaining conditions: we can write $`\emptyset` as $`\emptyset = \bigcup_{x \in \emptyset} \{x\}`. Applying that the arbitrary union of open sets is open, it would suffice to see that $`\forall x \in \emptyset`, $`\{x\}` is an open set. Which is trivial.

```anchor isOpen_empty_example (module := UrysohnsLemma.BasicProp.basic)
example (X : Type) [TopologicalSpace X] : IsOpen (∅ : Set X) := by
  have h1 : ∅ = ⋃₀ ∅
  simp
  rw [h1]
  apply isOpen_sUnion
  intro t ht
  by_contra
  exact ht
```

### Example 3.6
%%%
tag := "ejemplo-intervalos-abiertos"
number := false
%%%

In the usual topology, $`(\mathbb{R}, \mathcal{T}_u)`, the open intervals $`I = (a, b)` with $`a < b` are open sets of the topology.

*Proof.* Consider an interval of the form $`(a, b)`; we want to see that it is open. To do so, let $`x \in (a, b)`, and let us see that there exists a $`\delta >0` such that $`\forall y \in \mathbb{R}`, if $`y \in B_\delta(x)` then $`y \in (a, b)`.

```anchor ioo_open_sig_partial (module := UrysohnsLemma.TopoSpaces.usual)
lemma ioo_open_in_R (a b : ℝ) :
    UsualTopology.IsOpen ((Set.Ioo a b) : Set ℝ) := by

  rw [UsualTopology]
  intro x hx
```

We take $`\delta = min \{x-a, b-x\}`. Obviously $`\delta >0` since $`a < x < b`.

```anchor ioo_open_delta_pos (module := UrysohnsLemma.TopoSpaces.usual)
  use min (x-a) (b-x)  -- nuestro δ

  constructor
  · -- δ > 0 ?
    simp only [lt_inf_iff]
    exact ⟨sub_pos.mpr hx.1, sub_pos.mpr hx.2⟩
```

Let now $`y \in B_\delta(x)`; we want to see that $`y \in (a, b)`. There are two possible cases, depending on the value $`\delta` takes. If $`\delta = x-a`, that is, $`x-a < b -x`, then we have
$$`y \in B_\delta(x) \implies x - (x - a) < y < x + (x - a) < x + (b - x) \implies a < y < b,`
hence $`y \in (a, b)`. The case $`\delta = b -x` is analogous.

```anchor ioo_open_cases (module := UrysohnsLemma.TopoSpaces.usual)
  · -- (x - δ, x + δ) ⊆ (a, b) ?
    -- hay que diferenciar cuando δ = x-a y δ = b-x
    intro y hy
    have cases := lt_or_ge (x - a) (b - x)
    cases' cases with h h
    all_goals
      try rw [min_eq_left_of_lt h] at hy
      try rw [min_eq_right h] at hy
      simp at hy
      constructor
      all_goals linarith
```
∎

### Definition 3.2 (Open neighbourhood)
%%%
number := false
%%%

Let $`(X, \mathcal{T})` be a topological space and $`x \in X`. An _open neighbourhood_ of $`x` in $`X` is an open set $`U \in \mathcal{T}` such that $`x \in U`.

```anchor OpenNeighbourhood_def (module := UrysohnsLemma.BasicProp.basic)
def OpenNeighbourhood {X : Type} [TopologicalSpace X]
    (U : Set X) (x : X) : Prop :=
    x ∈ U ∧ IsOpen U
```

### Example 3.7
%%%
number := false
%%%

The universe, $`X`, is an open neighbourhood of any point $`x \in X`. Indeed:

```anchor univ_is_OpenNeighb (module := UrysohnsLemma.BasicProp.basic)
lemma univ_is_OpenNeighb {X : Type} [TopologicalSpace X]
    (x : X) : OpenNeighbourhood Set.univ x := by
  constructor
  · trivial
  · exact isOpen_univ
```

### Definition 3.3 (Neighbourhood)
%%%
number := false
%%%

Let $`(X, \mathcal{T})` be a topological space and $`x \in X`. A _neighbourhood_ of $`x` in $`X` is a set $`V \subseteq X` such that there exists an open neighbourhood of $`x`, $`U \in \mathcal{T}`, with $`U \subseteq V`.

```anchor Neighbourhood_def (module := UrysohnsLemma.BasicProp.basic)
def Neighbourhood {X : Type} [TopologicalSpace X]
    (V : Set X) (x : X) : Prop :=
    ∃ U : Set X, U ⊆ V ∧ OpenNeighbourhood U x
```

### Example 3.8
%%%
number := false
%%%

An open neighbourhood is also a neighbourhood. Indeed:

```anchor OpenNeighb_is_Neighb (module := UrysohnsLemma.BasicProp.basic)
lemma OpenNeighb_is_Neighb {X : Type} [TopologicalSpace X]
    (U : Set X) (x : X) : OpenNeighbourhood U x →
    Neighbourhood U x := by
  intro hU
  use U
```

### Proposition 3.1 (Characterisation of open sets)
%%%
tag := "caracterizacion-abierto"
number := false
%%%

Let $`(X, \mathcal{T})` be a topological space and $`A \subseteq U` any set. $`A` is open if and only if it is a neighbourhood of all of its points.

```anchor A_open_iff_neighbourhood_of_all_sig (module := UrysohnsLemma.BasicProp.open)
lemma A_open_iff_neighbourhood_of_all
    {X : Type} [T : TopologicalSpace X]
    {A : Set X} : IsOpen A ↔
    ∀ x ∈ A, Neighbourhood A x := by
```

*Proof.* We prove each implication separately.

```anchor A_open_iff_constructor (module := UrysohnsLemma.BasicProp.open)
  constructor
  all_goals intro h
```

$`(\implies)` The first implication is easy: if $`A` is open, for each $`x \in A` it suffices to take $`A` as a neighbourhood of $`x`.

```anchor A_open_iff_forward (module := UrysohnsLemma.BasicProp.open)
  · -- →
    intro x hx
    use A
    constructor
    · trivial
    · constructor
      · exact hx
      · exact h
```

$`(\impliedby)` The converse is more complicated. We know that for each $`a \in A` there exists $`U_a`, a neighbourhood of $`a`. We will first prove that
$$`A = \bigcup_{a \in A} U_a`

```anchor A_open_iff_backward_hUnion_stmt (module := UrysohnsLemma.BasicProp.open)
  · -- ←
    have hUnion : A = ⋃ a : A, Classical.choose (h a a.property)
```

To do so, we prove both inclusions. If $`x \in A`, then by our hypothesis there exists a neighbourhood of $`x`, $`U_x`. And by the definition of neighbourhood, that means that $`x \in U_x`. Hence $`x \in \bigcup_{a}U_a`.

```anchor A_open_iff_backward_hUnion_forward (module := UrysohnsLemma.BasicProp.open)
    · ext x; constructor; all_goals intro hx
      · have ⟨_, hUx⟩  := Classical.choose_spec (h x hx)
        simp
        use x, hx
        exact hUx.left
```

Now, if $`x \in \bigcup_{a}U_a`, then there exists an $`a \in A` with $`x \in U_a` and $`U_a` an open neighbourhood of $`a` with $`U_a \subseteq A`. Hence $`x \in U_a \subseteq A`.

```anchor A_open_iff_backward_hUnion_backward (module := UrysohnsLemma.BasicProp.open)
      · simp at hx
        obtain ⟨a, ha, hx⟩ := hx
        have ⟨ha', _⟩ := Classical.choose_spec (h a ha)
        apply ha'
        exact hx
```

Then we have proved that $`A` can be expressed as a union of sets $`U_a`. But we know that all these sets are open neighbourhoods, hence they are open. It suffices to apply that the union of open sets is open.

```anchor A_open_iff_backward_finish (module := UrysohnsLemma.BasicProp.open)
    rw [hUnion]
    apply isOpen_iUnion
    intro a
    exact (Classical.choose_spec (h a a.property)).right.right
```
∎

### Definition 3.4 (Interior)
%%%
number := false
%%%

Let $`(X, \mathcal{T})` be a topological space and $`A \subseteq X`. We define the _interior_ as the set
$$`\overset{\circ}{A} = \bigcup \left\{ U \subseteq X | U \text{ is open and } U \subseteq A \right\}`

```anchor interior_def_quote (module := UrysohnsLemma.Docs.Espacios)
def interior (s : Set X) : Set X :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }
```

Let us look at several properties of the interior of a set.

### Proposition 3.2
%%%
number := false
%%%

Let $`(X, \mathcal{T})` be a topological space and $`A \subseteq X`. Then
$$`\overset{\circ}{A} \subseteq A`

In Mathlib, this result goes by the name `interior_subset`.

*Proof.* Let $`a \in \overset{\circ}{A}`. Then $`A` is a neighbourhood of $`a` and there exists an open set with $`a \in U \subseteq A`. Hence $`a \in A`.

```anchor interior_subset_example (module := UrysohnsLemma.BasicProp.interior)
example {X : Type} [T : TopologicalSpace X] (A : Set X) :
    interior A ⊆ A := by
  intro a ha
  obtain ⟨U, hU, ha⟩ := ha
  apply hU.right
  exact ha
```
∎

### Proposition 3.3
%%%
number := false
%%%

Let $`(X, \mathcal{T})` be a topological space and $`A \subseteq X`. Then $`\overset{\circ}{A}` is an open set.

In Mathlib, this result goes by the name `isOpen_interior`.

*Proof.* By the characterisation of open sets ({ref "caracterizacion-abierto"}[3.1]), it suffices to see that, given $`a \in \overset{\circ}{A}`, $`\overset{\circ}{A}` is a neighbourhood of $`a`.

If $`a \in \overset{\circ}{A}`, then there exists an open $`U` with $`a \in U \subseteq A`. We use this $`U` to prove that $`\overset{\circ}{A}` is a neighbourhood of $`a`.

```anchor isOpen_interior_example (module := UrysohnsLemma.BasicProp.interior)
example {X : Type} [T : TopologicalSpace X]
    (A : Set X) : IsOpen (interior A) := by
  apply A_open_iff_neighbourhood_of_all.mpr
  intro a ha
  obtain ⟨U, hU, ha⟩ := ha
  use U
  constructor
  · intro x hx
    use U
  · constructor
    · exact ha
    · exact hU.left
```
∎

### Proposition 3.4
%%%
number := false
%%%

Let $`(X, \mathcal{T})` be a topological space and $`A \subseteq X`. Then $`A` is open if and only if $`A` is equal to its interior.

In Mathlib, this result goes by the name `interior_eq_iff_isOpen`.

*Proof.* The converse is trivial, since we have already seen that the interior of a set is open.

```anchor interior_eq_iff_isOpen_forward (module := UrysohnsLemma.BasicProp.interior)
example {X : Type} [T : TopologicalSpace X] (A : Set X) :
    IsOpen A ↔ interior A = A:= by
  constructor; swap; all_goals intro h
  · rw [← h]
    exact isOpen_interior
```

Now, suppose that $`A` is open. We have already seen that $`\overset{\circ}{A} \subseteq A`, so it suffices to see the other inclusion. Let $`a \in A`. Since $`A` is open, it is an open neighbourhood of $`a` with $`A \subseteq A`. Hence $`a \in \overset{\circ}{A}`.

```anchor interior_eq_iff_isOpen_backward (module := UrysohnsLemma.BasicProp.interior)
  · apply Set.Subset.antisymm
    · exact interior_subset
    · intro a ha
      use A
      constructor
      · simp
        exact h
      · exact ha
```
∎

## Closed sets

### Definition 3.5 (Closed set)
%%%
number := false
%%%

Let $`(X, \mathcal{T})` be a topological space and $`A \subseteq X`. We say that $`A` is _closed_ in $`X` if $`A^c` is open in $`X`.

```anchor isClosed_class_quote (module := UrysohnsLemma.Docs.Espacios)
class IsClosed (s : Set X) : Prop where
  isOpen_compl : IsOpen sᶜ
```

### Example 3.9
%%%
number := false
%%%

The universe is closed, because the empty set is open. The empty set is closed, because the universe is closed.

```anchor isClosed_univ_example (module := UrysohnsLemma.BasicProp.closed)
example (X : Type) [TopologicalSpace X] : IsClosed (Set.univ : Set X) := by
  rw [← isOpen_compl_iff]
  rw [Set.compl_univ]
  exact isOpen_empty
```

### Example 3.10
%%%
number := false
%%%

The arbitrary intersection of closed sets is closed. The finite union of closed sets is closed. Both follow easily from the definition of topological space and closed set.

```anchor isClosed_union_example (module := UrysohnsLemma.BasicProp.closed)
example (X : Type) [TopologicalSpace X] (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) : IsClosed (A ∪ B) := by
  rw [← isOpen_compl_iff] at *
  rw [Set.compl_union]
  apply TopologicalSpace.isOpen_inter
  exact hA
  exact hB
```

### Definition 3.6 (Closure)
%%%
number := false
%%%

Let $`(X, \mathcal{T})` be a topological space and $`A \subseteq X`. We define the _closure_ of $`A` as the set
$$`\overline{A} = \bigcap \{K \subseteq X | K \text{ is closed and } A \subseteq K\}`

```anchor closure_def_quote (module := UrysohnsLemma.Docs.Espacios)
def closure (s : Set X) : Set X :=
  ⋂₀ { t | IsClosed t ∧ s ⊆ t }
```

Let us look at some properties of the closure of a set.

### Proposition 3.5
%%%
number := false
%%%

Let $`(X, \mathcal{T})` be a topological space and $`A \subseteq X`. Then
$$`A \subseteq \overline{A}`

In Mathlib, this result goes by the name `subset_closure`.

*Proof.* Let $`a \in A`; we want to see that $`a \in \overline{A}`. Since $`\overline{A}` is an intersection, this is equivalent to proving that for each closed $`K` with $`A \subseteq K`, $`x \in K`. But this is trivial because, for each of those $`K`, $`x \in A \subseteq K`.

```anchor subset_closure_example (module := UrysohnsLemma.BasicProp.closure)
example {X : Type} [T : TopologicalSpace X] (A : Set X) :
    A ⊆ closure A := by
  intro x hx
  intro K hK
  apply hK.right
  exact hx
```
∎

### Proposition 3.6
%%%
number := false
%%%

Let $`(X, \mathcal{T})` be a topological space and $`A \subseteq X`. Then
$$`(\overline{A})^c = \overset{\circ}{\overbrace{(A^c)}}`

In Mathlib, this result goes by the name `interior_compl`.

*Proof.* Let us see both inclusions separately.

```anchor interior_compl_sig (module := UrysohnsLemma.BasicProp.closure)
example {X : Type} [T : TopologicalSpace X] (A : Set X) :
    (closure A)ᶜ = interior (Aᶜ) := by

  ext x; constructor; all_goals intro hx
```

$`(\subseteq)` Suppose that $`x \in (\overline{A})^c`, that is, $`x \notin \overline{A}`. This means that there exists a closed $`K` such that $`A \subseteq K` and $`x \notin K`.

```anchor interior_compl_forward_start (module := UrysohnsLemma.BasicProp.closure)
  · simp [closure] at hx
    obtain ⟨K, hKclosed, hKA, hKx⟩ := hx
```

To see that $`x` is in the interior of $`A^c`, we want to see that there exists an open set contained in $`A^c` that contains $`x`. Consider the open set $`K^c`. Since $`A \subseteq K`, we have $`K^c \subseteq A^c`, and since $`x \notin K`, we have $`x \in K^c`.

```anchor interior_compl_forward_finish (module := UrysohnsLemma.BasicProp.closure)
    use Kᶜ
    constructor
    · constructor
      · exact isOpen_compl_iff.mpr hKclosed
      · exact Set.compl_subset_compl_of_subset hKA
    · exact hKx
```

$`(\supseteq)` Let $`x` be in the interior of $`A^c`. Then there exists an open $`U` with $`x \in U \subseteq A^c`. To see that $`x` is in the complement of $`\overline{A}`, suppose, for contradiction, that $`x \in \overline{A}`.

```anchor interior_compl_backward_start (module := UrysohnsLemma.BasicProp.closure)
  · obtain ⟨U, hU, hUx⟩ := hx
    obtain ⟨hUopen, hUA⟩ := hU
    by_contra hx
```

In that case, for each closed $`K` with $`A \subseteq K`, we have $`x \in K`. In particular, since $`U^c` is closed because $`U` is open, and $`A \subseteq U^c` because $`U \subseteq A^c`, we have that $`x \in U^c`. But $`x \in U`, which is a contradiction.

```anchor interior_compl_backward_finish (module := UrysohnsLemma.BasicProp.closure)
    simp [closure] at hx
    specialize hx Uᶜ (by exact isClosed_compl_iff.mpr hUopen) (by exact Set.subset_compl_comm.mp hUA)
    exact hx hUx
```
∎

### Proposition 3.7
%%%
number := false
%%%

Let $`(X, \mathcal{T})` be a topological space and $`A \subseteq X`. Then $`\overline{A}` is a closed set.

In Mathlib, this result goes by the name `isClosed_closure`.

*Proof.* The proof is easy using the previous result: $`\overline{A}` is closed if $`(\overline{A})^c` is open. But we have seen that $`(\overline{A})^c = (A^c)^\circ`, and the interior of any set is open.

```anchor isClosed_closure_example (module := UrysohnsLemma.BasicProp.closure)
example {X : Type} [T : TopologicalSpace X] (A : Set X) :
    IsClosed (closure A) := by
  apply isOpen_compl_iff.mp
  rw [← interior_compl]
  exact isOpen_interior
```
∎

### Proposition 3.8
%%%
number := false
%%%

Let $`(X, \mathcal{T})` be a topological space and $`A \subseteq X`. Then $`A` is closed if and only if it is equal to its closure.

*Proof.* The converse is trivial, since we have already seen that the closure of a set is closed.

```anchor closure_eq_iff_isClosed_forward (module := UrysohnsLemma.BasicProp.closure)
example {X : Type} [T : TopologicalSpace X] (A : Set X) :
    IsClosed A ↔ closure A = A := by
  constructor; swap; all_goals intro h
  · rw [← h]
    exact isClosed_closure
```

Now, suppose that $`A` is closed. Then $`A^c` is open, hence it is equal to its interior. But we have seen that the interior of $`A^c` is $`(\overline{A})^c`, hence $`A^c = (\overline{A})^c`, from which we deduce $`A = \overline{A}`.

```anchor closure_eq_iff_isClosed_backward (module := UrysohnsLemma.BasicProp.closure)
  · rw [← isOpen_compl_iff, ← interior_eq_iff_isOpen, interior_compl] at h
    rw [← compl_compl A, ← h, compl_compl]
    exact closure_closure
```
∎

# Bases
%%%
file := "bases"
%%%

## Definition 3.7
%%%
number := false
%%%

Let $`\mathcal{T}` be a topology. A _base of the topology_ $`\mathcal{T}` is a collection of open sets $`\mathcal{B} \subset \mathcal{T}` such that every open set of $`\mathcal{T}` is a union of open sets of $`\mathcal{B}`{margin}[There are several ways of giving this definition; this is the one I have chosen to define it in Lean, independently of Mathlib. Therefore, the results in this section are not literally found in Mathlib.].

```anchor isTopoBase_def (module := UrysohnsLemma.BasicProp.bases)
def isTopoBase {X : Type} [TopologicalSpace X]
    (B : Set (Set X)) : Prop :=
  (∀ U ∈ B, IsOpen U) ∧
  (∀ V : Set X, IsOpen V → ∃ UB ⊆ B, V = ⋃₀ UB)
```

## Example 3.11
%%%
number := false
%%%

The set of open intervals in $`\mathbb{R}`,
$$`\mathcal{B} = \left\{ I = (a, b) ~|~ a < b\right\},`
is a base of the usual topology $`(\mathbb{R}, \mathcal{T}_u)`.

*Proof.* We have seen that open intervals are open in the usual topology (Example {ref "ejemplo-intervalos-abiertos"}[3.6]). Therefore, we already have the first part of the definition of a base.

```anchor BaseOfRealTopo_forward (module := UrysohnsLemma.BasicProp.bases)
lemma BaseOfRealTopo [T : TopologicalSpace ℝ]
    (hT : T = UsualTopology) :
    isTopoBase {s | ∃ a b : ℝ, s = Set.Ioo a b} := by
  constructor
  · intro U hU
    obtain ⟨a, b, hU⟩ := hU
    rw [hU, hT]
    exact ioo_open_in_R a b
```

Now, for the second part, we consider an arbitrary $`U \subseteq X`. We want to see that it can be written as a union of open intervals.

```anchor BaseOfRealTopo_backward_start (module := UrysohnsLemma.BasicProp.bases)
  · intro U hUopen
    rw [hT] at hUopen
```

To do so, consider, for each $`x \in U`, the $`\delta_u` resulting from applying the definition of open set, that is, such that $`B_{\delta_x}(x) \subseteq U`. We want to prove that $`U = \bigcup \{B_{\delta_x}(x) | x \in U\}`, and that this is a subset of $`\mathcal{B}`.

```anchor BaseOfRealTopo_delta (module := UrysohnsLemma.BasicProp.bases)
    let δ : U → ℝ := fun x ↦ Classical.choose (hUopen x x.property)
    have δspec : ∀ x : U, 0 < δ x
        ∧ ∀ y : ℝ, ↑x - δ x < y ∧ y < ↑x + δ x → y ∈ U :=
      fun x ↦ Classical.choose_spec (hUopen x (x.property))

    use {s | ∃ x, s = Set.Ioo (x - δ x) (x + δ x)}
```

Obviously, it is a subset of $`\mathcal{B}` since it is a set formed by open intervals.

```anchor BaseOfRealTopo_subset_B (module := UrysohnsLemma.BasicProp.bases)
    constructor

    · intro V hV
      obtain ⟨x, hV⟩ := hV
      use (↑x - δ x), (↑x + δ x)
```

Now, to see that $`U = \bigcup \{B_{\delta_x}(x) | x \in U\}`, we prove the two inclusions separately.

```anchor BaseOfRealTopo_ext_u (module := UrysohnsLemma.BasicProp.bases)
    · ext u; constructor; all_goals intro hu
```

$`(\subseteq)` Let $`u \in U`. Then $`u \in B_{\delta_u}` trivially. Hence it is in the union.

```anchor BaseOfRealTopo_forward_incl (module := UrysohnsLemma.BasicProp.bases)
      · use Set.Ioo (↑u - δ ⟨u, hu⟩) (↑u + δ ⟨u, hu⟩)
        constructor
        · simp
          use u, hu
        · simp
          exact (δspec ⟨u, hu⟩).left
```

$`(\supseteq)` Let $`u \in \bigcup \{B_{\delta_x}(x) | x \in U\}`. Then there exists a $`v \in U` such that $`u \in B_{\delta_v}(v) \subseteq U`. Hence $`u \in U`.

```anchor BaseOfRealTopo_backward_incl (module := UrysohnsLemma.BasicProp.bases)
      · obtain ⟨I, hI, hu⟩ := hu
        obtain ⟨v, hI⟩ := hI
        rw [hI] at hu
        exact (δspec v).right u hu
```
∎

# Subspace topology
%%%
file := "topologia-relativa"
%%%

## Definition 3.8 (Subspace topology)
%%%
number := false
%%%

Let $`(X, \mathcal{T})` be a topological space and $`A \subseteq X` a subset. Then the collection
$$`\mathcal{T}|_A = \{U \cap A | U \in \mathcal{T}\}`
is a topology on $`A`, called the topology _relative_ to $`X` on $`A`, or the _subspace topology_.

We will say that $`(A, \mathcal{T}|_A)` is a _topological subspace_ of $`(X, \mathcal{T})`.

In Lean, in order to use this definition, we have to prove that this collection is, indeed, a topology.

*Proof.* Let $`(X, \mathcal{T})` be a topological space and $`A \subseteq X` a subset, and define the collection
$$`\mathcal{T}|_A = \{U \cap A | U \in \mathcal{T}\}`

```anchor TopoSubspace_isOpen_field (module := UrysohnsLemma.BasicProp.subspaces)
def TopoSubspace {X : Type} (T : TopologicalSpace X) (Y : Set X) :
  TopologicalSpace Y where

  IsOpen (V : Set Y) := ∃ U : Set X, T.IsOpen U ∧ V = U ∩ Y
```

(1) The universe is open. Indeed, since $`A = X \cap A` and $`X` is open in $`X`.

```anchor TopoSubspace_isOpen_univ (module := UrysohnsLemma.BasicProp.subspaces)
  isOpen_univ := by
    use (Set.univ : Set X)
    constructor
    · exact T.isOpen_univ
    · simp
```

(2) Let $`V_1` and $`V_2` be open in $`A`. Then $`V_1 = U_1 \cap A` and $`V_2 = U_2 \cap A` with $`U_1, U_2` open in $`X`. Hence
$$`V_1 \cap V_2 = (U_1 \cap A) \cap (U_2 \cap A) = (U_1 \cap U_2) \cap A,`
and $`U_1 \cap U_2` is open in $`X` by the second property.

```anchor TopoSubspace_isOpen_inter (module := UrysohnsLemma.BasicProp.subspaces)
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
```

(3) Let $`S = \{V_i\}_i` be a collection of open sets in $`A`. Then, for each $`V_i` there exists a $`U_i` open in $`X` such that $`V_i = U_i \cap A`. Then
$$`\bigcup S = \bigcup_{i}V_i = \bigcup_{i}(U_i \cap A) = A \cap \bigcup_{i}U_i,`
and $`\bigcup_{i}U_i` is open in $`X` by the third property. The Lean proof is not included here due to its greater complexity. ∎

## Example 3.12
%%%
number := false
%%%

Consider $`\mathbb{R}` with the usual topology and the interval $`[0, 1] \subset \mathbb{R}`. In the topology of $`[0, 1]` induced by the usual topology, the intervals of the form $`[0, b)` are open for every $`0 < b \leq 1` (even though they are not open in $`\mathbb{R}`). The intervals of the form $`(a, 1]` are also open for each $`0 \leq a < 1`.

*Proof.* For each $`b > 0`, it suffices to use, for example, the open interval $`(-1, b)`. We have already seen that open intervals are open in $`\mathbb{R}`, and we have $`(-1, b) \cap [0, 1] = [0, b)`. Hence $`[0, b)` is open in $`[0, 1]`.

```anchor ico_open_in_Icc01 (module := UrysohnsLemma.BasicProp.subspaces)
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
```
∎

# Continuity
%%%
file := "continuidad"
%%%

## Definition 3.9
%%%
number := false
%%%

Let $`X` and $`Y` be two topological spaces and $`f : X \to Y` a function between them. Then $`f` is _continuous_ at a point $`x_0 \in X` if for each neighbourhood $`V` of $`f(x_0)` in $`Y`, we have that $`f^{-1}(V)` is a neighbourhood of $`x_0` in $`X`. We will say that $`f` is _continuous_ on $`X` if it is continuous at every point.

## Proposition 3.9 (Characterisation of continuous functions)
%%%
number := false
%%%

Let $`X` and $`Y` be two topological spaces and $`f : X \to Y` a function between them. Then $`f` is continuous if and only if for each open $`V \subseteq Y`, we have that $`f^{-1}(V)` is open in $`X`.

*Proof.* Let us see both implications separately.

```anchor continuous_neighbourhood_sig (module := UrysohnsLemma.Continuous.basic)
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) :
      (∀ x : X, ∀ V : Set Y,
        Neighbourhood V (f x) → Neighbourhood (f ⁻¹' V) x)
      ↔ ∀ (V : Set Y), IsOpen V → IsOpen (f ⁻¹' V) := by

  constructor; all_goals intro h
```

$`(\implies)` Let $`f : X \to Y` be continuous and let $`V \subseteq Y` be an open set. We want to see that $`f^{-1}(V)` is open. To do so, it suffices to see that it is a neighbourhood of all of its points (Prop. {ref "caracterizacion-abierto"}[3.1]).

Let $`x \in f^{-1}(V)`. Then $`V` is a neighbourhood of $`f(x)`, since $`V` is an open set with $`f(x) \in V`. Hence, by the definition of continuity, $`f^{-1}(V)` is a neighbourhood of $`x`.

```anchor continuous_neighbourhood_forward (module := UrysohnsLemma.Continuous.basic)
  · intro V hVopen
    apply A_open_iff_neighbourhood_of_all.mpr
    intro x hx
    exact h x V
      (by use V; simp; exact ⟨hx, hVopen⟩)
```

$`(\impliedby)` Let now $`x \in X` and let $`V \subseteq Y` be a neighbourhood of $`f(x)` in $`Y`. We want to see that $`f^{-1}(V)` is a neighbourhood of $`x` in $`X`.

There exists an open neighbourhood $`U\subseteq V` of $`f(x)` in $`Y`. Then $`x \in f^{-1}(U)\subseteq f^{-1}(V)`, and it is open, by hypothesis. Therefore $`f^{-1}(V)` is a neighbourhood of $`x`.

```anchor continuous_neighbourhood_backward (module := UrysohnsLemma.Continuous.basic)
  · intro x V hV
    obtain ⟨U, hUV, hU⟩ := hV
    obtain ⟨hUx, hUopen⟩ := hU
    use f ⁻¹' U
    constructor
    · intro u hu
      apply hUV
      exact hu
    · constructor
      · exact hUx
      · exact h U hUopen
```
∎

Since both definitions are equivalent, Mathlib uses the second one to define continuous functions, and in general we will use this definition.

```anchor continuous_structure_quote (module := UrysohnsLemma.Docs.Espacios)
structure Continuous (f : X → Y) : Prop where
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
```

We will use `continuous_def` to rewrite `Continuous f` into this definition whenever we need it.

## Example 3.13
%%%
number := false
%%%

Let $`f : (X, \mathcal{T}_{disc}) \to (Y, \mathcal{T})` be a function where the domain has the discrete topology (Ex. {ref "ex-topologia-discreta"}[3.1]). Then $`f` is continuous.

If we take any open set of $`Y`, its preimage will be trivially open in the discrete topology, since every set is.

```anchor continuous_from_discrete (module := UrysohnsLemma.Continuous.examples)
lemma continuous_from_discrete {X Y : Type}
    [T : TopologicalSpace X]
    [TopologicalSpace Y]
    (h : T = DiscreteTopo X)
    (f : X → Y) : Continuous f := by

  rw [continuous_def]
  intro U _

  -- aquí lo que hago es que le digo
  -- que estoy trabajando con la discreta
  rw [h, DiscreteTopo]
  -- (Aunque parezca que no hago nada)
  trivial
```

## Example 3.14
%%%
number := false
%%%

Let $`f : (X, \mathcal{T}) \to (Y, \mathcal{T}_{trivial})` be a function where the codomain has the trivial topology (Ex. {ref "ex-topologia-trivial"}[3.2]). Then $`f` is continuous.

Since the only possible open sets to take in $`Y` are $`Y` itself and the empty set, their preimages will be, respectively, $`X` and the empty set, which are open.

```anchor continuous_to_trivial (module := UrysohnsLemma.Continuous.examples)
lemma continuous_to_trivial {X Y : Type}
    [TopologicalSpace X]
    [T : TopologicalSpace Y]
    (h : T = TrivialTopology Y)
    (f : X → Y) : Continuous f := by

  rw [continuous_def]
  intro U hU
  rw [h, TrivialTopology] at hU
  cases' hU with hUuniv hUempty

  · -- si U = Y
    rw [hUuniv]
    exact isOpen_univ

  · -- si U = ∅
    rw [hUempty]
    exact isOpen_empty
```

## Proposition 3.10
%%%
number := false
%%%

The composition of continuous functions between topological spaces is also a continuous function.

In Mathlib, this result goes by the name `Continuous.comp`.

*Proof.* Let $`f : X \to Y` and $`g : Y \to Z` be two continuous functions and consider their composition $`g \circ f : X \to Z`.

Let $`W` be an open set of $`Z`. Since $`g` is continuous, $`V = g^{-1}(W)` is open in $`Y`. Since $`f` is continuous, $`f^{-1}(V)` is open in $`X`. But
$$`f^{-1}(V) = f^{-1}(g^{-1}(W)) = (g \circ f)^{-1}(W)`

```anchor continuous_comp_example (module := UrysohnsLemma.Continuous.basic)
example (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by

  rw [continuous_def] at *
  intro W hW
  specialize hg W hW
  specialize hf (g ⁻¹' W) hg
  exact hf
```
∎

## Proposition 3.11 (Characterisation of continuity via closed sets)
%%%
number := false
%%%

Let $`X` and $`Y` be two topological spaces and $`f : X \to Y` a function between them. Then $`f` is continuous if and only if for each closed $`C \subseteq Y`, we have that $`f^{-1}(C)` is closed in $`X`.

In Mathlib, this result goes by the name `continuous_iff_isClosed`.

*Proof.* Suppose that $`f` is continuous. Let $`C` be closed in $`Y`. Then $`C^c` is open in $`Y`. Since $`f` is continuous, $`f^-1(C^c)` is open in $`X`. But $`f^-1(C^c) = f^-1(C)^c`, hence $`f^-1(C)` is closed in $`X`. The converse is analogous.

```anchor continuous_iff_isClosed_example (module := UrysohnsLemma.Continuous.basic)
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ C : Set Y, IsClosed C → IsClosed (f ⁻¹' C) := by
  constructor; all_goals intro h
  · rw [continuous_def] at h
    intro C hC
    rw [← isOpen_compl_iff] at *
    exact h Cᶜ hC

  · rw [continuous_def]
    intro U hU
    rw [← isClosed_compl_iff] at *
    exact h Uᶜ hU
```
∎

## Proposition 3.12 (Continuity in subspaces)
%%%
tag := "prop-continuidad-subespacio"
number := false
%%%

Let $`X` and $`Y` be topological spaces and $`Z` a topological subspace of Y. A function $`f : X \to Z` is continuous if and only if it is continuous as a function $`f : X \to Y`.

That is, to prove the continuity condition for $`f : X \to Z`, it suffices to take arbitrary open sets of $`Y`.

*Proof.* Let us see each implication separately.

```anchor continuousInSubspace_iff_trueForSpace_sig (module := UrysohnsLemma.Continuous.subspaces)
lemma continuousInSubspace_iff_trueForSpace {X Y : Type} {Z : Set Y}
    [TX : TopologicalSpace X] [TY : TopologicalSpace Y]
    [TZ : TopologicalSpace Z] (hZ : TZ = TopoSubspace TY Z)
    (f : X → Z) :
    Continuous f ↔ ∀ U : Set Y, TY.IsOpen U → TX.IsOpen (f ⁻¹' (Subtype.val ⁻¹' U)) := by

  rw [continuous_def]
  constructor
  all_goals intro h U hU
```

$`(\implies)` Suppose that $`f : X \to Z` is continuous. Let $`U` be an open set of $`Y`; we want to see that $`f^-1(U)` is open in $`X`. Since $`f` is continuous, it suffices to see that $`f(f^{-1})(U)` is open. But $`f(f^{-1})(U) = U \cap Y`, which is open by the definition of the subspace topology, since $`U` is open.

```anchor continuousInSubspace_iff_trueForSpace_forward (module := UrysohnsLemma.Continuous.subspaces)
  · -- →
    apply h
    rw [hZ]
    use U
    constructor
    · exact hU
    · simp
      exact Set.inter_comm Z U
```

$`(\impliedby)` Suppose now that $`f : X \to Y` is continuous. Let $`U` be an open set in $`Z`. Then, by the definition of the subspace topology, there exists a $`V` open in $`Y` such that $`U = V \cap Z`. Since $`f` is continuous, $`f^{-1}(V)` is open. Then $`f^{-1}(U) = f^{-1}(V \cap Z) = f^{-1}(V)`, since $`f : X \to Z`. Hence it is open.

```anchor continuousInSubspace_iff_trueForSpace_backward (module := UrysohnsLemma.Continuous.subspaces)
  · -- ←
    rw [hZ] at hU
    obtain ⟨V, hV⟩ := hU

    rw [← @Set.preimage_val_image_val_eq_self Y Z U, hV.right]
    simp
    apply h
    exact hV.left
```
∎

## Proposition 3.13
%%%
tag := "prop-continuous-base"
number := false
%%%

Let $`f : X \to Y` be a function between topological spaces and let $`\mathcal{B}` be a base of $`Y`. Then $`f` is continuous if and only if for each basic open set $`U \in \mathcal{B}`, we have that $`f^{-1}(U)` is open in $`X`.

That is, for the definition of continuity of a function it suffices to take the basic open sets.

```anchor continuous_iff_trueForBasics_sig (module := UrysohnsLemma.Continuous.bases)
lemma continuous_iff_trueForBasics {X Y : Type} [T : TopologicalSpace X]
    [T' : TopologicalSpace Y] (f : X → Y)
    (B : Set (Set Y)) (hB : isTopoBase B) :
    Continuous f ↔ ∀ U ∈ B, IsOpen (f ⁻¹' U)
```

*Proof.* The first implication is trivial; if the continuity property holds for every open set, it trivially holds for the basic open sets.

```anchor continuous_iff_trueForBasics_forward (module := UrysohnsLemma.Continuous.bases)
  rw [continuous_def]
  constructor; all_goals intro h
  · exact fun U hU ↦ h U (hB.left U hU)
```

$`(\impliedby)` Let $`V` be open in $`Y`; we want to see that $`f^{-1}(V)` is open in $`X`. Since $`\mathcal{B}` is a base of $`Y`, there exists a family $`\{B_i\}_i \subseteq \mathcal{B}` such that $`U = \bigcup_i B_i`. Then
$$`f^{-1}(U) = f^{-1}\big(\bigcup_i B_i\big) = \bigcup_i f^{-1}(B_i),`
which will be open when each of the components of the union is open. But $`B_i` is open because it belongs to a base, and $`f` is continuous, hence $`f^{-1}(B_i)` is open for each $`i`.

```anchor continuous_iff_trueForBasics_backward (module := UrysohnsLemma.Continuous.bases)
  · intro V hV
    obtain ⟨UB, hUB⟩ := hB.right V hV
    rw [hUB.right, Set.preimage_sUnion]
    apply isOpen_biUnion
    intro A hA
    apply h
    exact (hUB.left hA)
```
∎

These last two results can be combined, so that to prove that $`f : X \to Z \subseteq Y` is continuous, it suffices to prove the condition for the basic open sets of $`Y`. This result, which I have proved in Lean and called `continuousInSubspace_iff_trueForBase`, is one of the ones we will use to prove continuity in Urysohn's lemma.

# Separation
%%%
file := "separacion"
%%%

Not every topology on a set adequately reflects the properties of that set. For example, the trivial topology does not allow us to tell elements of the space apart, so under this topology it is not possible to distinguish some sets from others or even from a single point.

To go deeper into the study of topology, certain conditions are introduced that guarantee that the points of the space can be distinguished in some way by means of open sets. These conditions are known as separation axioms.

For example, a space is Hausdorff if given two distinct points, there exist disjoint open sets containing each of them. This condition is true for any metric space, and guarantees certain nice properties, such as the uniqueness of limits.

In this work we will focus, in particular, on normal spaces.

## Normal spaces

Normal spaces allow us to separate not only points, but disjoint closed sets by means of disjoint open sets. This property is more demanding, but also more powerful.

One of the most important properties of normal spaces is that they allow us to distinguish between closed sets by separating them with continuous functions, which is known as *Urysohn's lemma*. The formalisation of this result is one of the main objectives of this work.

### Definition 3.10
%%%
number := false
%%%

Let $`X` be a topological space. We will say that $`X` is a _normal_ space if for each pair of disjoint closed sets $`C, D \subseteq X` there exist disjoint open sets $`U` and $`V` in $`X` that separate $`C` and $`D`, that is, $`C \subseteq U` and $`D \subseteq V`{margin}[In Lean, the `NormalSpace` definition is slightly different, but it uses objects that we have not used. Instead, we use this one together with a proof that they are equivalent, which I have called `normal_space_def`.].

```anchor NormalSpace_illustrative_def (module := UrysohnsLemma.Docs.Espacios)
def NormalSpace {X : Type} (T : TopologicalSpace X) : Prop :=
  ∀ C : Set X, ∀ D : Set X,
  IsClosed C → IsClosed D → C ∩ D = ∅ →
  ∃ U : Set X, ∃ V : Set X,
    IsOpen U ∧ IsOpen V ∧ C ⊆ U ∧ D ⊆ V ∧ U ∩ V = ∅
```

Now we want to give a characterisation of this kind of space, which will make our work easier later on.

### Proposition 3.14 (Characterisation of normal spaces)
%%%
tag := "caracterizacion-normal"
number := false
%%%

Let $`X` be a topological space. $`X` is normal if and only if for each open $`U` and each closed $`C` of $`X` such that $`C \subseteq U`, there exists an open $`V \subset X` such that $`C \subseteq V \subseteq \overline{V} \subseteq U`.

```anchor characterization_of_normal_sig (module := UrysohnsLemma.Separation.normal)
lemma characterization_of_normal {X : Type}
    (T : TopologicalSpace X) :
    NormalSpace X ↔
    ∀ U : Set X, ∀ C : Set X,
    IsOpen U → IsClosed C → C ⊆ U →
    ∃ V : Set X, IsOpen V ∧
    C ⊆ V ∧ (closure V) ⊆ U := by
```

*Proof.* Let us see each implication separately.

```anchor characterization_of_normal_rw_constructor (module := UrysohnsLemma.Separation.normal)
  rw [normal_space_def]
  constructor
```

($`\implies`) Suppose that $`X` is a normal space (`hT`) and let $`U` be an open set (`hU`) and $`C` a closed set (`hC`) such that $`C \subseteq U` (`hCU`).

```anchor characterization_of_normal_forward_intro (module := UrysohnsLemma.Separation.normal)
  · intro hT U C hU hC hCU
```

Since $`X` is normal, by the definition, for $`C` and $`U^c` closed in $`X` we obtain $`V_1` and $`V_2` open (`V1_open`, `V2_open`) and disjoint (`hV`) such that $`C \subseteq V_1` (`hCV`) and $`U^c \subseteq V_2` (`hUV`).

```anchor characterization_of_normal_forward_obtain (module := UrysohnsLemma.Separation.normal)
    obtain ⟨V1, V2, V1_open, V2_open, hCV, hUV, hV⟩ :=
      hT C Uᶜ
      hC
      (by exact isClosed_compl_iff.mpr hU)
      (by rw [← Set.subset_compl_iff_disjoint_right, compl_compl]; exact hCU)
```

Of course, in Lean we have to specify why $`U^c` is closed and why $`U^c \subseteq V_2`. We take as $`V` the $`V_1` obtained in this way. We already know that $`V_1` is open and that $`C\subseteq V_1`, so it only remains to prove that $`\overline{V_1} \subseteq U`.

```anchor characterization_of_normal_forward_use_V1 (module := UrysohnsLemma.Separation.normal)
    use V1
    constructor
    · exact V1_open
    constructor
    · exact hCV
```

We know that $`U^c \subseteq V_2` (`hUV`), hence $`V_2^c \subseteq U`. It suffices to see that $`\overline{V_1} \subseteq V_2^c`.

But $`V_1 \cap V_2 = \emptyset \implies \overline{V_1} \cap V_2 = \emptyset`, since $`V_2` is open. Hence $`\overline{V_1} \subseteq V_2^c`.

```anchor characterization_of_normal_forward_finish (module := UrysohnsLemma.Separation.normal)
    · trans V2ᶜ; swap
      · exact Set.compl_subset_comm.mp hUV
      · apply Disjoint.closure_left at hV
        specialize hV V2_open
        exact Set.subset_compl_iff_disjoint_right.mpr hV
```

($`\impliedby`) We proceed in a similar way. Let $`C_1` and $`C_2` be disjoint (`hC`) closed sets (`C1_closed`, `C2_closed`). We can apply the hypothesis (`h`) to the open set $`C_1^c` and the closed set $`C_2` to obtain an open $`V` (`V_open`) such that $`C_2 \subseteq V \subseteq \overline{V} \subseteq C_1^c` (`hV`).

```anchor characterization_of_normal_backward_obtain (module := UrysohnsLemma.Separation.normal)
  · intro h C1 C2 C1_closed C2_closed hC

    obtain ⟨V, V_open, hV⟩ :=
      h C1ᶜ C2
      (by exact IsClosed.isOpen_compl)
      C2_closed
      (by rw [Set.subset_compl_iff_disjoint_left]; exact hC)
```

Now we take the open sets $`U_1 = \overline{V}^c` and $`U_2 = V`. We want to see that they satisfy the normality condition for $`C_1` and $`C_2`, that is:

```
  IsOpen (closure V)ᶜ ∧ IsOpen V ∧ C1 ⊆ (closure V)ᶜ ∧ C2 ⊆ V ∧ Disjoint (closure V)ᶜ V
```

Indeed, both are open ($`\overline{V}^c` for being the complement of a closure and $`V` by construction).

```anchor characterization_of_normal_backward_isOpen (module := UrysohnsLemma.Separation.normal)
    constructor
    · apply isOpen_compl_iff.mpr
      exact isClosed_closure
    constructor
    · exact V_open
```

Moreover, $`C_1 \subseteq \overline{V}^c` is equivalent to $`\overline{V} \subseteq C_1^c`, which is true by the construction of $`V`, as is $`C_2 \subseteq V`.

```anchor characterization_of_normal_backward_subset (module := UrysohnsLemma.Separation.normal)
    constructor
    · apply Set.subset_compl_comm.mp
      exact hV.right
    constructor
    · exact hV.left
```

Finally, we have
$$`\overline{V}^c \cap V = \emptyset \iff V \cap \overline{V}^c = \emptyset \iff
  V \subseteq \overline{V}^{cc} \iff V \subseteq \overline{V},`
which is true by the properties of the closure.

```anchor characterization_of_normal_backward_disjoint (module := UrysohnsLemma.Separation.normal)
    · rw [← Set.subset_compl_iff_disjoint_left, compl_compl]
      exact subset_closure
```
∎
