import VersoManual
import Docs.Referencias
import Docs.Papers

open Verso.Genre Manual
open Verso.Code.External
open Verso.Genre.Manual.Docs (citetOther citepOther citehereOther)
open Docs (refWillard2012General)

set_option pp.rawOnError true
set_option verso.exampleProject "../../.."
set_option verso.exampleModule "UrysohnsLemma.BasicProp.basic"

#doc (Manual) "Espacios topológicos en Lean" =>
%%%
tag := "espacios-topologicos"
%%%

En esta sección veremos cómo se representan en Lean algunos conceptos básicos de topología general. El objetivo no es desarrollar la teoría completa, sino mostrar ejemplos concretos de definiciones y demostraciones formales, que sirvan como primer contacto con el trabajo en Lean sobre espacios topológicos.

Las definiciones y resultados matemáticos utilizados son los habituales en topología general. Aunque inicialmente me basé en los apuntes que tomé en la asignatura Topología Elemental, posteriormente los he contrastado con{citepOther refWillard2012General}[] como referencia estándar.

# Espacios topológicos

## Definición 3.1 (Espacio topológico)
%%%
tag := "def-espacio-topologico"
number := false
%%%

Sea $`X` un conjunto y $`\mathcal{T}` una colección de subconjuntos de $`X` de forma que

1. Los conjuntos $`\emptyset` y $`X` pertenecen a $`\mathcal{T}`.
1. Cualquier intersección finita de elementos de $`\mathcal{T}` pertenece a $`\mathcal{T}`.
1. Cualquier unión arbitraria de elementos de $`\mathcal{T}` pertenece a $`\mathcal{T}`.

Entonces diremos que $`\mathcal{T}` es una _topología_ sobre $`X`, que $`(X, \mathcal{T})` es un _espacio topológico_ y que los elementos de $`\mathcal{T}` son _abiertos_ en este espacio.

En Lean, esta definición se escribe como una estructura que consta de cuatro elementos:

```anchor topologicalSpace_class_quote (module := UrysohnsLemma.Docs.Espacios)
class TopologicalSpace (X : Type u) where
  IsOpen : Set X → Prop
  isOpen_univ : IsOpen Set.univ
  isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)
```

El primer elemento, `IsOpen`, es una función que lleva cada conjunto de $`X` en una proposición, es decir, es una descripción de los elementos de $`\mathcal{T}` como el conjunto `{U ∈ Set (X) | IsOpen U}`. Los otros tres elementos son demostraciones de las propiedades de la definición.

Veamos algunos ejemplos y sus demostraciones en Lean.

## Ejemplo 3.1
%%%
tag := "ex-topologia-discreta"
number := false
%%%

Sea $`X` un conjunto cualquiera. Consideremos la colección de todos los subconjuntos de $`X`, $`\mathcal{T} = \mathcal{P}(X)`. Entonces $`\mathcal{T}` es una topología sobre $`X`, a la que llamamos _topología discreta_.

*Demostración.* Podemos describir $`\mathcal T` como `{U ∈ Set (X) | true}`, porque `IsOpen` es cierto para cualquier $`U`.

```anchor DiscreteTopo_isOpen_field (module := UrysohnsLemma.TopoSpaces.discrete)
def DiscreteTopo (X : Type) : TopologicalSpace X where
  IsOpen (_ : Set X) := true
```

Ahora, demostrar el resto de propiedades es sencillo:

```anchor DiscreteTopo_isOpen_univ_partial (module := UrysohnsLemma.TopoSpaces.discrete)
  isOpen_univ := by
```

Aplicar la función `fun x ↦ true` a cualquier conjunto retorna siempre `true`, por tanto basta con usar `trivial`.

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

## Ejemplo 3.2
%%%
tag := "ex-topologia-trivial"
number := false
%%%

Sea $`X` un conjunto cualquiera. Consideremos la colección $`\mathcal{T}=\{\emptyset, X\}`. Entonces $`\mathcal{T}` es una topología sobre $`X`, a la que llamamos _topología trivial_.

*Demostración.* Podemos describir $`\mathcal{T}` como `{U ∈ Set (X) | U = X ∨ U = ∅}`.

```anchor TrivialTopology_isOpen_field (module := UrysohnsLemma.TopoSpaces.trivial)
@[reducible]
def TrivialTopology (X : Type) : TopologicalSpace X where
  IsOpen (s : Set X) := s = Set.univ ∨ s = ∅
```

La primera condición se cumple trivialmente: queremos ver $`X = X \lor X = \emptyset`.

```anchor TrivialTopology_isOpen_univ (module := UrysohnsLemma.TopoSpaces.trivial)
  isOpen_univ := by
    left
    rfl
```

Consideremos ahora dos abiertos (`intro`). Diferenciamos en casos:

```anchor TrivialTopology_isOpen_inter_partial (module := UrysohnsLemma.TopoSpaces.trivial)
  isOpen_inter := by
    intro s t hs ht
    cases' hs with hs_univ hs_empty
    cases' ht with ht_univ ht_empty
```

Si ambos son $`X`, la intersección será $`X` y por tanto abierta. Si uno de los dos es vacío, entonces la intersección es vacía, también abierta.

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

Consideremos finalmente una colección arbitraria $`S` de abiertos. Para ver si la unión es abierta, consideramos dos casos distintos: o bien $`X` está en $`S`, en cuyo caso la unión es $`X`, o bien no lo está, en cuyo caso todos los conjuntos de $`S` son el vacío y la unión también lo es.

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

## Ejemplo 3.3
%%%
number := false
%%%

Consideremos la recta real y la definición usual de conjunto abierto en $`\mathbb{R}`, es decir, $`A \subseteq \mathbb{R}` es abierto si y solo si para cada punto $`x \in A` existe una bola abierta centrada en $`x` enteramente contenida en $`A`. Sea $`\mathcal{T}` la colección de estos abiertos. Entonces $`\mathcal{T}` es una topología sobre $`\mathbb{R}`, a la que llamamos _topología usual_.

*Demostración.* En Lean, podemos describir este espacio topológico dando sus elementos de la siguiente forma, donde cada objeto esta definido anteriormente.

```anchor UsualTopology_def (module := UrysohnsLemma.TopoSpaces.usual)
def UsualTopology : TopologicalSpace ℝ where
  IsOpen := Real.IsOpen
  isOpen_univ := Real.isOpen_univ
  isOpen_inter := Real.isOpen_inter
  isOpen_sUnion := Real.isOpen_sUnion
```

La definición de abierto se puede escribir así:

```anchor Real_IsOpen_def (module := UrysohnsLemma.TopoSpaces.usual)
def Real.IsOpen (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∃ δ > 0, ∀ y : ℝ, x - δ < y ∧ y < x + δ → y ∈ s
```

Damos la demostración para la intersección finita. El resto utilizan mecanismos parecidos.

Sean por tanto dos subconjuntos $`s` y $`t` de $`\mathcal{T}`. Sea $`x \in t \cap s` y queremos ver que existe una bola abierta centrada en $`x` y contenida en $`t \cap s`.

```anchor Real_isOpen_inter_sig_partial (module := UrysohnsLemma.TopoSpaces.usual)
lemma Real.isOpen_inter (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  intro x hx
```

Puesto que $`x \in s`, existe un $`\delta_1>0` (`hδ1`) de forma que $`B_{\delta_1}(x) \subseteq s` (`hs`). Análogamente, existe un $`\delta_2>0` (`hδ2`) de forma que $`B_{\delta_2}(x) \subseteq t` (`ht`). Basta con tomar $`\delta = \min \{\delta_1, \delta_2\}`.

```anchor Real_isOpen_inter_obtain (module := UrysohnsLemma.TopoSpaces.usual)
  obtain ⟨δ1, hδ1, hs⟩ := hs x hx.left
  obtain ⟨δ2, hδ2, ht⟩ := ht x hx.right
  use min δ1 δ2
```

Trivialmente $`\delta > 0`.

```anchor Real_isOpen_inter_constructor_partial (module := UrysohnsLemma.TopoSpaces.usual)
  constructor
  · exact lt_min hδ1 hδ2
```

Para ver que $`B_\delta (x) \subseteq s \cap t`, consideramos $`y \in B_\delta(x)` y queremos ver que $`y \in s` y que $`y \in t`. Para ver $`y \in s`, como $`B_{\delta_1}(x) \subseteq s` (`hs`), basta ver $`y \in B_{\delta_1}(x)`.

```anchor Real_isOpen_inter_intro_y (module := UrysohnsLemma.TopoSpaces.usual)
  · intro y hy
    constructor
    · apply hs
```

En realidad, esta condición se reduce a dos inecuaciones, que son fáciles de probar contando con que $`\delta \leq \delta_1` (`hδ`).

```anchor Real_isOpen_inter_hs_finish (module := UrysohnsLemma.TopoSpaces.usual)
      have hδ := min_le_left δ1 δ2
      constructor
      all_goals linarith
```

Probar que $`y \in t` es análogo. ∎

## Conjuntos abiertos

Como hemos dicho, los conjuntos abiertos en un espacio topológico son los elementos de la topología. En Lean, es una función `TopologicalSpace.IsOpen` de tipo `Set X → Prop`. Podemos utilizar esta definición directamente para demostrar que un abierto lo es.

### Ejemplo 3.4
%%%
number := false
%%%

Por definición, el universo, $`X`, siempre es abierto. En efecto:

```anchor univ_isOpen_example (module := UrysohnsLemma.Docs.Espacios)
example (X : Type) [T : TopologicalSpace X] : T.IsOpen Set.univ := by
  exact TopologicalSpace.isOpen_univ
```

### Ejemplo 3.5
%%%
number := false
%%%

En la Definición {ref "def-espacio-topologico"}[3.1], teníamos la condición $`\emptyset \in \mathcal{T}`, condición que no aparece en la definición de Mathlib.

Se puede probar que el vacío es abierto a partir del resto de condiciones: podemos escribir $`\emptyset` como $`\emptyset = \bigcup_{x \in \emptyset} \{x\}`. Aplicando que la unión arbitraria de abiertos es abierta, bastaría ver que $`\forall x \in \emptyset`, $`\{x\}` es un conjunto abierto. Lo cual es trivial.

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

### Ejemplo 3.6
%%%
tag := "ejemplo-intervalos-abiertos"
number := false
%%%

En la topología usual, $`(\mathbb{R}, \mathcal{T}_u)`, los intervalos abiertos $`I = (a, b)` con $`a < b` son abiertos de la topología.

*Demostración.* Consideremos un intervalo de la forma $`(a, b)` y queremos ver que es abierto. Para ello, sea $`x \in (a, b)`, y veamos que existe un $`\delta >0` tal que $`\forall y \in \mathbb{R}`, si $`y \in B_\delta(x)` entonces $`y \in (a, b)`.

```anchor ioo_open_sig_partial (module := UrysohnsLemma.TopoSpaces.usual)
lemma ioo_open_in_R (a b : ℝ) :
    UsualTopology.IsOpen ((Set.Ioo a b) : Set ℝ) := by

  rw [UsualTopology]
  intro x hx
```

Tomamos $`\delta = min \{x-a, b-x\}`. Obviamente $`\delta >0` pues $`a < x < b`.

```anchor ioo_open_delta_pos (module := UrysohnsLemma.TopoSpaces.usual)
  use min (x-a) (b-x)  -- nuestro δ

  constructor
  · -- δ > 0 ?
    simp only [lt_inf_iff]
    exact ⟨sub_pos.mpr hx.1, sub_pos.mpr hx.2⟩
```

Sea ahora $`y \in B_\delta(x)` y queremos ver que $`y \in (a, b)`. Hay dos posibles casos, según el valor que tome $`\delta`. Si $`\delta = x-a`, es decir, $`x-a < b -x`, entonces se tiene
$$`y \in B_\delta(x) \implies x - (x - a) < y < x + (x - a) < x + (b - x) \implies a < y < b,`
luego $`y \in (a, b)`. El caso $`\delta = b -x` es análogo.

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

### Definición 3.2 (Entorno abierto)
%%%
number := false
%%%

Sea $`(X, \mathcal{T})` un espacio topológico y $`x \in X`. Un _entorno abierto_ de $`x` en $`X` es un conjunto abierto $`U \in \mathcal{T}` de forma que $`x \in U`.

```anchor OpenNeighbourhood_def (module := UrysohnsLemma.BasicProp.basic)
def OpenNeighbourhood {X : Type} [TopologicalSpace X]
    (U : Set X) (x : X) : Prop :=
    x ∈ U ∧ IsOpen U
```

### Ejemplo 3.7
%%%
number := false
%%%

El universo, $`X`, es entorno abierto de cualquier punto $`x \in X`. En efecto:

```anchor univ_is_OpenNeighb (module := UrysohnsLemma.BasicProp.basic)
lemma univ_is_OpenNeighb {X : Type} [TopologicalSpace X]
    (x : X) : OpenNeighbourhood Set.univ x := by
  constructor
  · trivial
  · exact isOpen_univ
```

### Definición 3.3 (Entorno)
%%%
number := false
%%%

Sea $`(X, \mathcal{T})` un espacio topológico y $`x \in X`. Un _entorno_ de $`x` en $`X` es un conjunto $`V \subseteq X` de forma que existe un entorno abierto de $`x`, $`U \in \mathcal{T}`, con $`U \subseteq V`.

```anchor Neighbourhood_def (module := UrysohnsLemma.BasicProp.basic)
def Neighbourhood {X : Type} [TopologicalSpace X]
    (V : Set X) (x : X) : Prop :=
    ∃ U : Set X, U ⊆ V ∧ OpenNeighbourhood U x
```

### Ejemplo 3.8
%%%
number := false
%%%

Un entorno abierto es también un entorno. En efecto:

```anchor OpenNeighb_is_Neighb (module := UrysohnsLemma.BasicProp.basic)
lemma OpenNeighb_is_Neighb {X : Type} [TopologicalSpace X]
    (U : Set X) (x : X) : OpenNeighbourhood U x →
    Neighbourhood U x := by
  intro hU
  use U
```

### Proposición 3.1 (Caracterización de conjuntos abiertos)
%%%
tag := "caracterizacion-abierto"
number := false
%%%

Sea $`(X, \mathcal{T})` un espacio topológico y $`A \subseteq U` un conjunto cualquiera. $`A` es abierto si y solo si es entorno de todos sus puntos.

```anchor A_open_iff_neighbourhood_of_all_sig (module := UrysohnsLemma.BasicProp.open)
lemma A_open_iff_neighbourhood_of_all
    {X : Type} [T : TopologicalSpace X]
    {A : Set X} : IsOpen A ↔
    ∀ x ∈ A, Neighbourhood A x := by
```

*Demostración.* Demostramos cada implicación separadamente.

```anchor A_open_iff_constructor (module := UrysohnsLemma.BasicProp.open)
  constructor
  all_goals intro h
```

$`(\implies)` La primera implicación es sencilla: si $`A` es abierto, para cada $`x \in A` basta tomar $`A` como entorno de $`x`.

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

$`(\impliedby)` El recíproco es más complicado. Sabemos que para cada $`a \in A` existe $`U_a` entorno de $`a`. Primero probaremos que
$$`A = \bigcup_{a \in A} U_a`

```anchor A_open_iff_backward_hUnion_stmt (module := UrysohnsLemma.BasicProp.open)
  · -- ←
    have hUnion : A = ⋃ a : A, Classical.choose (h a a.property)
```

Para ello, probamos ambas inclusiones. Si $`x \in A`, entonces por nuestra hipótesis existe un entorno de $`x`, $`U_x`. Y por la definición de entorno, eso quiere decir que $`x \in U_x`. Luego $`x \in \bigcup_{a}U_a`.

```anchor A_open_iff_backward_hUnion_forward (module := UrysohnsLemma.BasicProp.open)
    · ext x; constructor; all_goals intro hx
      · have ⟨_, hUx⟩  := Classical.choose_spec (h x hx)
        simp
        use x, hx
        exact hUx.left
```

Ahora, si $`x \in \bigcup_{a}U_a`, entonces existe un $`a \in A` con $`x \in U_a` y $`U_a` entorno abierto de $`a` con $`U_a \subseteq A`. Luego $`x \in U_a \subseteq A`.

```anchor A_open_iff_backward_hUnion_backward (module := UrysohnsLemma.BasicProp.open)
      · simp at hx
        obtain ⟨a, ha, hx⟩ := hx
        have ⟨ha', _⟩ := Classical.choose_spec (h a ha)
        apply ha'
        exact hx
```

Entonces hemos probado que $`A` se expresa como una unión de conjuntos $`U_a`. Pero sabemos que todos estos conjuntos son entornos abiertos, luego son abiertos. Basta aplicar que la unión de abiertos es abierta.

```anchor A_open_iff_backward_finish (module := UrysohnsLemma.BasicProp.open)
    rw [hUnion]
    apply isOpen_iUnion
    intro a
    exact (Classical.choose_spec (h a a.property)).right.right
```
∎

### Definición 3.4 (Interior)
%%%
number := false
%%%

Sea $`(X, \mathcal{T})` un espacio topológico y $`A \subseteq X`. Definimos el _interior_ como el conjunto
$$`\overset{\circ}{A} = \bigcup \left\{ U \subseteq X | U \text{ es abierto y } U \subseteq A \right\}`

```anchor interior_def_quote (module := UrysohnsLemma.Docs.Espacios)
def interior (s : Set X) : Set X :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }
```

Veamos varias propiedades del interior de un conjunto.

### Proposición 3.2
%%%
number := false
%%%

Sea $`(X, \mathcal{T})` un espacio topológico y $`A \subseteq X`. Entonces
$$`\overset{\circ}{A} \subseteq A`

En Mathlib, este resultado recibe el nombre de `interior_subset`.

*Demostración.* Sea $`a \in \overset{\circ}{A}`. Entonces $`A` es entorno de $`a` y existe un abierto con $`a \in U \subseteq A`. Luego $`a \in A`.

```anchor interior_subset_example (module := UrysohnsLemma.BasicProp.interior)
example {X : Type} [T : TopologicalSpace X] (A : Set X) :
    interior A ⊆ A := by
  intro a ha
  obtain ⟨U, hU, ha⟩ := ha
  apply hU.right
  exact ha
```
∎

### Proposición 3.3
%%%
number := false
%%%

Sea $`(X, \mathcal{T})` un espacio topológico y $`A \subseteq X`. Entonces $`\overset{\circ}{A}` es un conjunto abierto.

En Mathlib, este resultado recibe el nombre de `isOpen_interior`.

*Demostración.* Por la caracterización de conjuntos abiertos ({ref "caracterizacion-abierto"}[3.1]), basta ver que dado $`a \in \overset{\circ}{A}`, $`\overset{\circ}{A}` es entorno de $`a`.

Si $`a \in \overset{\circ}{A}`, entonces existe abierto $`U` con $`a \in U \subseteq A`. Usamos este $`U` para demostrar que $`\overset{\circ}{A}` es entorno de $`a`.

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

### Proposición 3.4
%%%
number := false
%%%

Sea $`(X, \mathcal{T})` un espacio topológico y $`A \subseteq X`. Entonces $`A` es abierto si y solo si $`A` es igual a su interior.

En Mathlib, este resultado recibe el nombre de `interior_eq_iff_isOpen`.

*Demostración.* El recíproco es trivial, pues ya hemos visto que el interior de un conjunto es abierto.

```anchor interior_eq_iff_isOpen_forward (module := UrysohnsLemma.BasicProp.interior)
example {X : Type} [T : TopologicalSpace X] (A : Set X) :
    IsOpen A ↔ interior A = A:= by
  constructor; swap; all_goals intro h
  · rw [← h]
    exact isOpen_interior
```

Ahora, supongamos que $`A` es abierto. Ya hemos visto que $`\overset{\circ}{A} \subseteq A`, luego basta ver el otro contenido. Sea $`a \in A`. Como $`A` es abierto, es un entorno abierto de $`a` con $`A \subseteq A`. Luego $`a \in \overset{\circ}{A}`.

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

## Conjuntos cerrados

### Definición 3.5 (Conjunto cerrado)
%%%
number := false
%%%

Sea $`(X, \mathcal{T})` un espacio topológico y $`A \subseteq X`. Decimos que $`A` es _cerrado_ en $`X` si $`A^c` es abierto en $`X`.

```anchor isClosed_class_quote (module := UrysohnsLemma.Docs.Espacios)
class IsClosed (s : Set X) : Prop where
  isOpen_compl : IsOpen sᶜ
```

### Ejemplo 3.9
%%%
number := false
%%%

El universo es cerrado, porque el vacío es abierto. El vacío es cerrado, porque el universo es cerrado.

```anchor isClosed_univ_example (module := UrysohnsLemma.BasicProp.closed)
example (X : Type) [TopologicalSpace X] : IsClosed (Set.univ : Set X) := by
  rw [← isOpen_compl_iff]
  rw [Set.compl_univ]
  exact isOpen_empty
```

### Ejemplo 3.10
%%%
number := false
%%%

La intersección arbitraria de cerrados es cerrada. La unión finita de cerrados es cerrada. Ambas se deducen de manera sencilla de la definición de espacio topológico y de conjunto cerrado.

```anchor isClosed_union_example (module := UrysohnsLemma.BasicProp.closed)
example (X : Type) [TopologicalSpace X] (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) : IsClosed (A ∪ B) := by
  rw [← isOpen_compl_iff] at *
  rw [Set.compl_union]
  apply TopologicalSpace.isOpen_inter
  exact hA
  exact hB
```

### Definición 3.6 (Clausura)
%%%
number := false
%%%

Sea $`(X, \mathcal{T})` un espacio topológico y $`A \subseteq X`. Definimos la _clausura_ de $`A` como el conjunto
$$`\overline{A} = \bigcap \{K \subseteq X | K \text{ es cerrado y } A \subseteq K\}`

```anchor closure_def_quote (module := UrysohnsLemma.Docs.Espacios)
def closure (s : Set X) : Set X :=
  ⋂₀ { t | IsClosed t ∧ s ⊆ t }
```

Veamos algunas propiedades de la clausura de un conjunto.

### Proposición 3.5
%%%
number := false
%%%

Sea $`(X, \mathcal{T})` un espacio topológico y $`A \subseteq X`. Entonces
$$`A \subseteq \overline{A}`

En Mathlib, este resultado recibe el nombre de `subset_closure`.

*Demostración.* Sea $`a \in A` y queremos ver que $`a \in \overline{A}`. Como $`\overline{A}` es una intersección, esto es equivalente a probar que para cada $`K` cerrado con $`A \subseteq K`, $`x \in K`. Pero esto es trivial porque, para cada uno de esos $`K`, $`x \in A \subseteq K`.

```anchor subset_closure_example (module := UrysohnsLemma.BasicProp.closure)
example {X : Type} [T : TopologicalSpace X] (A : Set X) :
    A ⊆ closure A := by
  intro x hx
  intro K hK
  apply hK.right
  exact hx
```
∎

### Proposición 3.6
%%%
number := false
%%%

Sea $`(X, \mathcal{T})` un espacio topológico y $`A \subseteq X`. Entonces
$$`(\overline{A})^c = \overset{\circ}{\overbrace{(A^c)}}`

En Mathlib, este resultado recibe el nombre de `interior_compl`.

*Demostración.* Veamos ambos contenidos por separado.

```anchor interior_compl_sig (module := UrysohnsLemma.BasicProp.closure)
example {X : Type} [T : TopologicalSpace X] (A : Set X) :
    (closure A)ᶜ = interior (Aᶜ) := by

  ext x; constructor; all_goals intro hx
```

$`(\subseteq)` Supongamos que $`x \in (\overline{A})^c`, es decir $`x \notin \overline{A}`. Esto quiere decir que existe un $`K` cerrado de forma que $`A \subseteq K` y $`x \notin K`.

```anchor interior_compl_forward_start (module := UrysohnsLemma.BasicProp.closure)
  · simp [closure] at hx
    obtain ⟨K, hKclosed, hKA, hKx⟩ := hx
```

Para ver que $`x` está en el interior de $`A^c`, queremos ver que existe un abierto contenido en $`A^c` que contiene a $`x`. Consideremos el abierto $`K^c`. Como $`A \subseteq K`, se tiene $`K^c \subseteq A^c`, y como $`x \notin K`, se tiene $`x \in K^c`

```anchor interior_compl_forward_finish (module := UrysohnsLemma.BasicProp.closure)
    use Kᶜ
    constructor
    · constructor
      · exact isOpen_compl_iff.mpr hKclosed
      · exact Set.compl_subset_compl_of_subset hKA
    · exact hKx
```

$`(\supseteq)` Sea $`x` en el interior de $`A^c`. Entonces existe un abierto $`U` con $`x \in U \subseteq A^c`. Para ver que $`x` está en el complementario de $`\overline{A}`, supongamos, por reducción al absurdo, que $`x \in \overline{A}`.

```anchor interior_compl_backward_start (module := UrysohnsLemma.BasicProp.closure)
  · obtain ⟨U, hU, hUx⟩ := hx
    obtain ⟨hUopen, hUA⟩ := hU
    by_contra hx
```

En ese caso, para cada $`K` cerrado con $`A \subseteq K`, se tiene $`x \in K`. En particular, como $`U^c` es cerrado por ser $`U` abierto y tiene $`A \subseteq U^c` por ser $`U \subseteq A^c`, se tiene que $`x \in U^c`. Pero $`x \in U`, lo cual es una contradicción.

```anchor interior_compl_backward_finish (module := UrysohnsLemma.BasicProp.closure)
    simp [closure] at hx
    specialize hx Uᶜ (by exact isClosed_compl_iff.mpr hUopen) (by exact Set.subset_compl_comm.mp hUA)
    exact hx hUx
```
∎

### Proposición 3.7
%%%
number := false
%%%

Sea $`(X, \mathcal{T})` un espacio topológico y $`A \subseteq X`. Entonces $`\overline{A}` es un conjunto cerrado.

En Mathlib, este resultado recibe el nombre de `isClosed_closure`.

*Demostración.* La prueba es sencilla utilizando el resultado anterior: $`\overline{A}` es cerrado si $`(\overline{A})^c` es abierto. Pero hemos visto que $`(\overline{A})^c = (A^c)^\circ`, y el interior de cualquier conjunto es abierto.

```anchor isClosed_closure_example (module := UrysohnsLemma.BasicProp.closure)
example {X : Type} [T : TopologicalSpace X] (A : Set X) :
    IsClosed (closure A) := by
  apply isOpen_compl_iff.mp
  rw [← interior_compl]
  exact isOpen_interior
```
∎

### Proposición 3.8
%%%
number := false
%%%

Sea $`(X, \mathcal{T})` un espacio topológico y $`A \subseteq X`. Entonces $`A` es cerrado si y solo si es igual a su clausura.

*Demostración.* El recíproco es trivial, pues ya hemos visto que la clausura de un conjunto es cerrada.

```anchor closure_eq_iff_isClosed_forward (module := UrysohnsLemma.BasicProp.closure)
example {X : Type} [T : TopologicalSpace X] (A : Set X) :
    IsClosed A ↔ closure A = A := by
  constructor; swap; all_goals intro h
  · rw [← h]
    exact isClosed_closure
```

Ahora, supongamos que $`A` es cerrado. Entonces $`A^c` es abierto, luego es igual a su interior. Pero el interior de $`A^c` hemos visto que es $`(\overline{A})^c`, luego $`A^c = (\overline{A})^c`, de lo que se deduce $`A = \overline{A}`.

```anchor closure_eq_iff_isClosed_backward (module := UrysohnsLemma.BasicProp.closure)
  · rw [← isOpen_compl_iff, ← interior_eq_iff_isOpen, interior_compl] at h
    rw [← compl_compl A, ← h, compl_compl]
    exact closure_closure
```
∎

# Bases

## Definición 3.7
%%%
number := false
%%%

Sea $`\mathcal{T}` una topología. Una _base de la topología_ $`\mathcal{T}` es una colección de abiertos $`\mathcal{B} \subset \mathcal{T}` de forma que cada abierto de $`\mathcal{T}` es unión de abiertos de $`\mathcal{B}`{margin}[Hay varias formas de dar esta definición, esta es la que yo he elegido para definirla en Lean, de manera independiente a Mathlib. Por tanto, los resultados de esta sección no se encuentran literalmente en Mathlib.].

```anchor isTopoBase_def (module := UrysohnsLemma.BasicProp.bases)
def isTopoBase {X : Type} [TopologicalSpace X]
    (B : Set (Set X)) : Prop :=
  (∀ U ∈ B, IsOpen U) ∧
  (∀ V : Set X, IsOpen V → ∃ UB ⊆ B, V = ⋃₀ UB)
```

## Ejemplo 3.11
%%%
number := false
%%%

El conjunto de los intervalos abiertos en $`\mathbb{R}`,
$$`\mathcal{B} = \left\{ I = (a, b) ~|~ a < b\right\},`
es una base de la topología usual $`(\mathbb{R}, \mathcal{T}_u)`.

*Demostración.* Hemos visto que los intervalos abiertos son abiertos en la topología usual (Ejemplo {ref "ejemplo-intervalos-abiertos"}[3.6]). Por tanto la primera parte de la definición de base ya la tenemos.

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

Ahora, para la segunda parte, consideramos un $`U \subseteq X` cualquiera. Queremos ver que se escribe como unión de intervalos abiertos.

```anchor BaseOfRealTopo_backward_start (module := UrysohnsLemma.BasicProp.bases)
  · intro U hUopen
    rw [hT] at hUopen
```

Para ello, consideremos para cada $`x \in U`, el $`\delta_u` resultante de aplicar la definición de abierto, es decir, tal que $`B_{\delta_x}(x) \subseteq U`. Queremos demostrar que $`U = \bigcup \{B_{\delta_x}(x) | x \in U\}`, y que este es un subconjunto de $`\mathcal{B}`.

```anchor BaseOfRealTopo_delta (module := UrysohnsLemma.BasicProp.bases)
    let δ : U → ℝ := fun x ↦ Classical.choose (hUopen x x.property)
    have δspec : ∀ x : U, 0 < δ x
        ∧ ∀ y : ℝ, ↑x - δ x < y ∧ y < ↑x + δ x → y ∈ U :=
      fun x ↦ Classical.choose_spec (hUopen x (x.property))

    use {s | ∃ x, s = Set.Ioo (x - δ x) (x + δ x)}
```

Obviamente, es un subconjunto de $`\mathcal{B}` puesto que es un conjunto formado por intervalos abiertos.

```anchor BaseOfRealTopo_subset_B (module := UrysohnsLemma.BasicProp.bases)
    constructor

    · intro V hV
      obtain ⟨x, hV⟩ := hV
      use (↑x - δ x), (↑x + δ x)
```

Ahora, para ver que $`U = \bigcup \{B_{\delta_x}(x) | x \in U\}`, demostramos las dos inclusiones de manera separada.

```anchor BaseOfRealTopo_ext_u (module := UrysohnsLemma.BasicProp.bases)
    · ext u; constructor; all_goals intro hu
```

$`(\subseteq)` Sea $`u \in U`. Entonces $`u \in B_{\delta_u}` trivialmente. Luego está en la unión.

```anchor BaseOfRealTopo_forward_incl (module := UrysohnsLemma.BasicProp.bases)
      · use Set.Ioo (↑u - δ ⟨u, hu⟩) (↑u + δ ⟨u, hu⟩)
        constructor
        · simp
          use u, hu
        · simp
          exact (δspec ⟨u, hu⟩).left
```

$`(\supseteq)` Sea $`u \in \bigcup \{B_{\delta_x}(x) | x \in U\}`. Entonces existe un $`v \in U` de forma que $`u \in B_{\delta_v}(v) \subseteq U`. Luego $`u \in U`.

```anchor BaseOfRealTopo_backward_incl (module := UrysohnsLemma.BasicProp.bases)
      · obtain ⟨I, hI, hu⟩ := hu
        obtain ⟨v, hI⟩ := hI
        rw [hI] at hu
        exact (δspec v).right u hu
```
∎

# Topología relativa

## Definición 3.8 (Topología relativa)
%%%
number := false
%%%

Sea $`(X, \mathcal{T})` un espacio topológico y $`A \subseteq X` un subconjunto. Entonces la colección
$$`\mathcal{T}|_A = \{U \cap A | U \in \mathcal{T}\}`
es una topología sobre $`A`, llamada la _topología relativa_ a $`X` de $`A`.

Diremos que $`(A, \mathcal{T}|_A)` es un _subespacio topológico_ de $`(X, \mathcal{T})`.

En Lean, para poder utilizar esta definición, tenemos que demostrar que este conjunto es, en efecto, una topología.

*Demostración.* Sea $`(X, \mathcal{T})` un espacio topológico y $`A \subseteq X` un subconjunto, y definimos la colección
$$`\mathcal{T}|_A = \{U \cap A | U \in \mathcal{T}\}`

```anchor TopoSubspace_isOpen_field (module := UrysohnsLemma.BasicProp.subspaces)
def TopoSubspace {X : Type} (T : TopologicalSpace X) (Y : Set X) :
  TopologicalSpace Y where

  IsOpen (V : Set Y) := ∃ U : Set X, T.IsOpen U ∧ V = U ∩ Y
```

(1) El universo es abierto. En efecto, pues $`A = X \cap A` y $`X` es abierto en $`X`.

```anchor TopoSubspace_isOpen_univ (module := UrysohnsLemma.BasicProp.subspaces)
  isOpen_univ := by
    use (Set.univ : Set X)
    constructor
    · exact T.isOpen_univ
    · simp
```

(2) Sean $`V_1` y $`V_2` abiertos en $`A`. Entonces $`V_1 = U_1 \cap A` y $`V_2 = U_2 \cap A` con $`U_1, U_2` abiertos en $`X`. Luego
$$`V_1 \cap V_2 = (U_1 \cap A) \cap (U_2 \cap A) = (U_1 \cap U_2) \cap A,`
y $`U_1 \cap U_2` es abierto en $`X` por la segunda propiedad.

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

(3) Sea $`S = \{V_i\}_i` una colección de abiertos en $`A`. Entonces, para cada $`V_i` existe un $`U_i` abierto en $`X` de forma que $`V_i = U_i \cap A`. Entonces
$$`\bigcup S = \bigcup_{i}V_i = \bigcup_{i}(U_i \cap A) = A \cap \bigcup_{i}U_i,`
y $`\bigcup_{i}U_i` es abierto en $`X` por la tercera propiedad. No se incluye aquí la demostración en Lean debido a su mayor complejidad. ∎

## Ejemplo 3.12
%%%
number := false
%%%

Consideremos $`\mathbb{R}` con la topología usual y el intervalo $`[0, 1] \subset \mathbb{R}`. En la topología de $`[0, 1]` inducida por la topología usual, los intervalos de la forma $`[0, b)` son abiertos para todo $`0 < b \leq 1` (aunque no lo sean en $`\mathbb{R}`). También son abiertos los intervalos de la forma $`(a, 1]` para cada $`0 \leq a < 1`.

*Demostración.* Para cada $`b > 0`, basta con usar por ejemplo el intervalo abierto $`(-1, b)`. Ya hemos visto que los intervalos abiertos son abiertos en $`\mathbb{R}`, y se tiene $`(-1, b) \cap [0, 1] = [0, b)`. Luego $`[0, b)` es abierto en $`[0, 1]`.

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

# Continuidad

## Definición 3.9
%%%
number := false
%%%

Sean $`X` e $`Y` dos espacios topológicos y $`f : X \to Y` una función entre ambos. Entonces $`f` es _continua_ en un punto $`x_0 \in X` si para cada entorno $`V` de $`f(x_0)` en $`Y`, se tiene que $`f^{-1}(V)` es entorno de $`x_0` en $`X`. Diremos que $`f` es _continua_ en $`X` si es continua en cada punto.

## Proposición 3.9 (Caracterización de funciones continuas)
%%%
number := false
%%%

Sean $`X` e $`Y` dos espacios topológicos y $`f : X \to Y` una función entre ambos. Entonces $`f` es continua si y solo si para cada $`V \subseteq Y` abierto, se tiene que $`f^{-1}(V)` es abierto en $`X`.

*Demostración.* Veamos ambas implicaciones por separado.

```anchor continuous_neighbourhood_sig (module := UrysohnsLemma.Continuous.basic)
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) :
      (∀ x : X, ∀ V : Set Y,
        Neighbourhood V (f x) → Neighbourhood (f ⁻¹' V) x)
      ↔ ∀ (V : Set Y), IsOpen V → IsOpen (f ⁻¹' V) := by

  constructor; all_goals intro h
```

$`(\implies)` Sea $`f : X \to Y` continua y sea $`V \subseteq Y` un conjunto abierto. Queremos ver que $`f^{-1}(V)` es abierto. Para ello, basta ver que es entorno de todos sus puntos (Prop. {ref "caracterizacion-abierto"}[3.1]).

Sea $`x \in f^{-1}(V)`. Entonces $`V` es entorno de $`f(x)`, por ser $`V` un abierto con $`f(x) \in V`. Luego, por la definición de continuidad, $`f^{-1}(V)` es entorno de $`x`.

```anchor continuous_neighbourhood_forward (module := UrysohnsLemma.Continuous.basic)
  · intro V hVopen
    apply A_open_iff_neighbourhood_of_all.mpr
    intro x hx
    exact h x V
      (by use V; simp; exact ⟨hx, hVopen⟩)
```

$`(\impliedby)` Sea ahora $`x \in X` y $`V \subseteq Y` un entorno de $`f(x)` en $`Y`. Queremos ver que $`f^{-1}(V)` es entorno de $`x` en $`X`.

Existe un entorno abierto $`U\subseteq V` de $`f(x)` en $`Y`. Entonces $`x \in f^{-1}(U)\subseteq f^{-1}(V)`, y es un abierto, por hipótesis. Por tanto $`f^{-1}(V)` es entorno de $`x`.

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

Puesto que ambas definiciones son equivalentes, en Mathlib se utiliza la segunda para definir las funciones continuas, y en general utilizaremos esta definición.

```anchor continuous_structure_quote (module := UrysohnsLemma.Docs.Espacios)
structure Continuous (f : X → Y) : Prop where
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
```

Utilizaremos `continuous_def` para re escribir `Continuous f` por esta definición cuando lo necesitemos.

## Ejemplo 3.13
%%%
number := false
%%%

Sea $`f : (X, \mathcal{T}_{disc}) \to (Y, \mathcal{T})` una función en la que el espacio de salida tiene la topología discreta (Ej. {ref "ex-topologia-discreta"}[3.1]). Entonces $`f` es continua.

Si tomamos cualquier abierto de $`Y`, su preimagen será abierta en la topología discreta trivialmente, puesto que cualquier conjunto lo es.

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

## Ejemplo 3.14
%%%
number := false
%%%

Sea $`f : (X, \mathcal{T}) \to (Y, \mathcal{T}_{trivial})` una función en la que el espacio de llegada tiene la topología trivial (Ej. {ref "ex-topologia-trivial"}[3.2]). Entonces $`f` es continua.

Puesto que las únicas posibilidades de abiertos a tomar en $`Y` son el propio $`Y` y el conjunto vacío, sus preimágenes serán respectivamente $`X` y el conjunto vacío, que son abiertos.

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

## Proposición 3.10
%%%
number := false
%%%

La composición de funciones continuas entre espacios topológicos es también una función continua.

En Mathlib, este resultado recibe el nombre de `Continuous.comp`.

*Demostración.* Sean $`f : X \to Y` y $`g : Y \to Z` dos funciones continuas y consideremos su composición $`g \circ f : X \to Z`.

Sea $`W` un abierto de $`Z`. Como $`g` es continua, $`V = g^{-1}(W)` es abierto en $`Y`. Como $`f` es continua, $`f^{-1}(V)` es abierto en $`X`. Pero
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

## Proposición 3.11 (Caracterización de la continuidad por cerrados)
%%%
number := false
%%%

Sean $`X` e $`Y` dos espacios topológicos y $`f : X \to Y` una función entre ambos. Entonces $`f` es continua si y solo si para cada $`C \subseteq Y` cerrado, se tiene que $`f^{-1}(C)` es cerrado en $`X`.

En Mathlib, este resultado recibe el nombre de `continuous_iff_isClosed`.

*Demostración.* Supongamos que $`f` es continua. Sea $`C` cerrado en $`Y`. Entonces $`C^c` es abierto en $`Y`. Por ser $`f` continua, $`f^-1(C^c)` es abierto en $`X`. Pero $`f^-1(C^c) = f^-1(C)^c`, luego $`f^-1(C)` es cerrado en $`X`. El recíproco es análogo.

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

## Proposición 3.12 (Continuidad del subespacio)
%%%
tag := "prop-continuidad-subespacio"
number := false
%%%

Sean $`X` e $`Y` espacios topológicos y $`Z` un subespacio topológico de Y. Una función $`f : X \to Z` es continua si y solo si lo es como función $`f : X \to Y`.

Es decir, para demostrar la condición de continuidad de $`f : X \to Z`, basta con tomar abiertos arbitrarios de $`Y`.

*Demostración.* Veamos cada implicación por separado.

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

$`(\implies)` Supongamos que $`f : X \to Z` es continua. Sea $`U` un abierto de $`Y` y queremos ver que $`f^-1(U)` es abierto en $`X`. Puesto que $`f` es continua, basta ver que $`f(f^{-1})(U)` es abierto. Pero $`f(f^{-1})(U) = U \cap Y`, que es abierto por la definición de topología relativa por ser $`U` abierto.

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

$`(\impliedby)` Supongamos ahora que $`f : X \to Y` es continua. Sea $`U` un abierto en $`Z`. Entonces, por la definición de la topología relativa, existe un $`V` abierto en $`Y` de forma que $`U = V \cap Z`. Por ser $`f` continua, $`f^{-1}(V)` es abierto. Entonces $`f^{-1}(U) = f^{-1}(V \cap Z) = f^{-1}(V)`, por ser $`f : X \to Z`. Luego es abierto.

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

## Proposición 3.13
%%%
tag := "prop-continuous-base"
number := false
%%%

Sea $`f : X \to Y` una función entre espacios topológicos y sea $`\mathcal{B}` una base de $`Y`. Entonces $`f` es continua si y solo si para cada $`U \in \mathcal{B}` abierto básico, se tiene que $`f^{-1}(U)` es abierto en $`X`.

Es decir, para la definición de continuidad de una función basta tomar los abiertos básicos.

```anchor continuous_iff_trueForBasics_sig (module := UrysohnsLemma.Continuous.bases)
lemma continuous_iff_trueForBasics {X Y : Type} [T : TopologicalSpace X]
    [T' : TopologicalSpace Y] (f : X → Y)
    (B : Set (Set Y)) (hB : isTopoBase B) :
    Continuous f ↔ ∀ U ∈ B, IsOpen (f ⁻¹' U)
```

*Demostración.* La primera implicación es trivial; si la propiedad de continuidad se cumple para cada abierto trivialmente se cumple para los abiertos básicos.

```anchor continuous_iff_trueForBasics_forward (module := UrysohnsLemma.Continuous.bases)
  rw [continuous_def]
  constructor; all_goals intro h
  · exact fun U hU ↦ h U (hB.left U hU)
```

$`(\impliedby)` Sea $`V` abierto en $`Y` y queremos ver que $`f^{-1}(V)` es abierto en $`X`. Como $`\mathcal{B}` es base de $`Y`, existe una familia $`\{B_i\}_i \subseteq \mathcal{B}` de forma que $`U = \bigcup_i B_i`. Entonces
$$`f^{-1}(U) = f^{-1}\big(\bigcup_i B_i\big) = \bigcup_i f^{-1}(B_i),`
que será abierto cuando cada uno de los componentes de la unión sea abierto. Pero $`B_i` es abierto por pertenecer a una base, y $`f` es continua, luego $`f^{-1}(B_i)` es continuo para cada $`i`.

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

Estos dos últimos resultados se pueden combinar, de manera que para demostrar que $`f : X \to Z \subseteq Y` es continua, basta con demostrar la condición para los abiertos básicos de $`Y`. Este resultado, que he demostrado en Lean y llamado `continuousInSubspace_iff_trueForBase`, es uno de los que utilizaremos para demostrar la continuidad en el lema de Urysohn.

# Separación

No cualquier topología sobre un conjunto refleja adecuadamente las propiedades de dicho conjunto. Por ejemplo, la topología trivial no permite diferenciar elementos del espacio, por lo que bajo esta topología no es posible diferenciar unos conjuntos de otros o incluso de un único punto.

Para profundizar en el estudio de la topología, se introducen ciertas condiciones que garantizan que los puntos del espacio puedan distinguirse de alguna forma mediante abiertos. Estas condiciones se conocen como axiomas de separación.

Por ejemplo, un espacio es de Hausdorff si dados dos puntos distintos, existen abiertos disjuntos que contienen a cada uno de ellos. Esta condición es cierta para cualquier espacio métrico, y garantiza ciertas propiedades buenas, como la unicidad de los límites.

En este trabajo nos centraremos, en particular, en los espacios normales.

## Espacios normales

Los espacios normales permiten separar no solo puntos, sino conjuntos cerrados disjuntos mediante abiertos disjuntos. Esta propiedad es más exigente, pero también más potente.

Uno de las propiedades más importantes de los espacios normales es que nos permiten distinguir entre conjuntos cerrados separándolos mediante funciones continuas, lo que se conoce como *lema de Urysohn*. La formalización de este resultado es uno de los objetivos principales de este trabajo.

### Definición 3.10
%%%
number := false
%%%

Sea $`X` un espacio topológico. Diremos que $`X` es un espacio _normal_ si para cada par de cerrados disjuntos $`C, D \subseteq X` existen abiertos disjuntos $`U` y $`V` en $`X` tales  que separan $`C` y $`D`, es decir, $`C \subseteq U` y $`D \subseteq V`{margin}[En Lean, la definición `NormalSpace` es ligeramente distinta, pero utiliza objetos que nosotros no hemos usado. En su lugar, utilizamos esta y una demostración de que son equivalentes, a la que he llamado `normal_space_def`.].

```anchor NormalSpace_illustrative_def (module := UrysohnsLemma.Docs.Espacios)
def NormalSpace {X : Type} (T : TopologicalSpace X) : Prop :=
  ∀ C : Set X, ∀ D : Set X,
  IsClosed C → IsClosed D → C ∩ D = ∅ →
  ∃ U : Set X, ∃ V : Set X,
    IsOpen U ∧ IsOpen V ∧ C ⊆ U ∧ D ⊆ V ∧ U ∩ V = ∅
```

Ahora queremos dar una caracterización para este tipo de espacios, que nos facilitará el trabajo más adelante.

### Proposición 3.14 (Caracterización de espacios normales)
%%%
tag := "caracterizacion-normal"
number := false
%%%

Sea $`X` un espacio topológico. $`X` es normal si y sólo si para cada abierto $`U` y cada cerrado $`C` de $`X` tales que $`C \subseteq U`, existe un abierto $`V \subset X` de forma que $`C \subseteq V \subseteq \overline{V} \subseteq U`.

```anchor characterization_of_normal_sig (module := UrysohnsLemma.Separation.normal)
lemma characterization_of_normal {X : Type}
    (T : TopologicalSpace X) :
    NormalSpace X ↔
    ∀ U : Set X, ∀ C : Set X,
    IsOpen U → IsClosed C → C ⊆ U →
    ∃ V : Set X, IsOpen V ∧
    C ⊆ V ∧ (closure V) ⊆ U := by
```

*Demostración.* Veamos cada implicación por separado.

```anchor characterization_of_normal_rw_constructor (module := UrysohnsLemma.Separation.normal)
  rw [normal_space_def]
  constructor
```

($`\implies`) Supongamos que $`X` es un espacio normal (`hT`) y sean $`U` un abierto (`hU`) y $`C` un cerrado (`hC`) tales que $`C \subseteq U` (`hCU`).

```anchor characterization_of_normal_forward_intro (module := UrysohnsLemma.Separation.normal)
  · intro hT U C hU hC hCU
```

Puesto que $`X` es normal, por la definición, para $`C` y $`U^c` cerrados en $`X` obtenemos $`V_1` y $`V_2` abiertos (`V1_open`, `V2_open`) disjuntos (`hV`) tales que $`C \subseteq V_1` (`hCV`) y $`U^c \subseteq V_2` (`hUV`).

```anchor characterization_of_normal_forward_obtain (module := UrysohnsLemma.Separation.normal)
    obtain ⟨V1, V2, V1_open, V2_open, hCV, hUV, hV⟩ :=
      hT C Uᶜ
      hC
      (by exact isClosed_compl_iff.mpr hU)
      (by rw [← Set.subset_compl_iff_disjoint_right, compl_compl]; exact hCU)
```

Por supuesto, en Lean tenemos que especificar por qué $`U^c` es cerrado y por qué $`U^c \subseteq V_2`. Tomamos como $`V` el $`V_1` obtenido de esta forma. Ya sabemos que $`V_1` es abierto y que $`C\subseteq V_1`, luego sólo falta demostrar que $`\overline{V_1} \subseteq U`.

```anchor characterization_of_normal_forward_use_V1 (module := UrysohnsLemma.Separation.normal)
    use V1
    constructor
    · exact V1_open
    constructor
    · exact hCV
```

Sabemos que $`U^c \subseteq V_2` (`hUV`), luego $`V_2^c \subseteq U`. Basta ver que $`\overline{V_1} \subseteq V_2^c`.

Pero $`V_1 \cap V_2 = \emptyset \implies \overline{V_1} \cap V_2 = \emptyset`, por ser $`V_2` abierto. Luego $`\overline{V_1} \subseteq V_2^c`.

```anchor characterization_of_normal_forward_finish (module := UrysohnsLemma.Separation.normal)
    · trans V2ᶜ; swap
      · exact Set.compl_subset_comm.mp hUV
      · apply Disjoint.closure_left at hV
        specialize hV V2_open
        exact Set.subset_compl_iff_disjoint_right.mpr hV
```

($`\impliedby`) Procedemos de manera similar. Sean $`C_1` y $`C_2` cerrados (`C1_closed`, `C2_closed`) disjuntos (`hC`). Podemos aplicar la hipótesis (`h`) al abierto $`C_1^c` y al cerrado $`C_2` para obtener obtener un abierto $`V` (`V_open`) de manera que $`C_2 \subseteq V \subseteq \overline{V} \subseteq C_1^c` (`hV`).

```anchor characterization_of_normal_backward_obtain (module := UrysohnsLemma.Separation.normal)
  · intro h C1 C2 C1_closed C2_closed hC

    obtain ⟨V, V_open, hV⟩ :=
      h C1ᶜ C2
      (by exact IsClosed.isOpen_compl)
      C2_closed
      (by rw [Set.subset_compl_iff_disjoint_left]; exact hC)
```

Ahora tomamos los abiertos $`U_1 = \overline{V}^c` y $`U_2 = V`. Queremos ver que cumplen la condición de normalidad para $`C_1` y $`C_2`, es decir:

```
  IsOpen (closure V)ᶜ ∧ IsOpen V ∧ C1 ⊆ (closure V)ᶜ ∧ C2 ⊆ V ∧ Disjoint (closure V)ᶜ V
```

En efecto, ambos son abiertos ($`\overline{V}^c` por ser el complementario de una clausura y $`V` por construcción).

```anchor characterization_of_normal_backward_isOpen (module := UrysohnsLemma.Separation.normal)
    constructor
    · apply isOpen_compl_iff.mpr
      exact isClosed_closure
    constructor
    · exact V_open
```

Además, $`C_1 \subseteq \overline{V}^c` es equivalente a $`\overline{V} \subseteq C_1^c`, que es cierto por construcción de $`V`, igual que $`C_2 \subseteq V`.

```anchor characterization_of_normal_backward_subset (module := UrysohnsLemma.Separation.normal)
    constructor
    · apply Set.subset_compl_comm.mp
      exact hV.right
    constructor
    · exact hV.left
```

Por último, se tiene
$$`\overline{V}^c \cap V = \emptyset \iff V \cap \overline{V}^c = \emptyset \iff
  V \subseteq \overline{V}^{cc} \iff V \subseteq \overline{V},`
que es cierto por las propiedades de la adherencia.

```anchor characterization_of_normal_backward_disjoint (module := UrysohnsLemma.Separation.normal)
    · rw [← Set.subset_compl_iff_disjoint_left, compl_compl]
      exact subset_closure
```
∎
