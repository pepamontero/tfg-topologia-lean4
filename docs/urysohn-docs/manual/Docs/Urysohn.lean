import VersoManual
import Docs.Referencias
import Docs.Espacios

open Verso.Genre Manual
open Verso.Code.External

set_option pp.rawOnError true
set_option verso.exampleProject "../../.."
set_option verso.exampleModule "UrysohnsLemma.Separation.urysohn"

#doc (Manual) "El Lema de Urysohn" =>
%%%
tag := "lema-urysohn"
%%%

El lema de Urysohn es uno de los resultados centrales de la topología general. Su importancia radica en que permite caracterizar la normalidad de un espacio topológico en términos de funciones continuas.

Mientras que en los axiomas de separación clásicos se exige la existencia de abiertos disjuntos para separar puntos o conjuntos, existen versiones que requieren separar mediante funciones continuas. Estas versiones son más restrictivas y, por tanto, definen propiedades más fuertes. Sin embargo, el lema de Urysohn muestra que en el caso de los espacios normales, esto no ocurre, sino que separar conjuntos cerrados mediante funciones continuas es equivalente a hacerlo mediante abiertos.

Este resultado tiene aplicaciones clave, como su uso en la demostración del teorema de metrización de Urysohn, que proporciona condiciones suficientes para que un espacio sea metrizable. Además, la demostración del lema es de gran interés por sí misma, especialmente para nuestros propósitos, ya que se basa en una construcción explícita y no trivial de la función buscada. Es precisamente la construcción de esta función a la que dedicaremos buena parte de esta sección.

# Teorema 4.1 (Lema de Urysohn)
%%%
tag := "thm-urysohn"
number := false
%%%

{ref "ref-willard2012general"}[\[16, p. 102, 15.6. Urysohn's Lemma\]]

Sea $`(X, \mathcal{T})` un espacio topológico. $`X` es un espacio normal si y solo si para cada par de conjuntos cerrados disjuntos $`C` y $`D` en $`X`, existe una función $`f : X \to [0, 1]` de manera que $`f(C) = \{0\}` y $`f(D) = \{1\}`.

Para la fomalización en Lean, pediremos que los cerrados $`C` y $`D` sean no vacíos. Obviamente, si uno de los dos es vacío, basta tomar la función continua $`f(x) \equiv 1`, pero podemos descartar estos casos triviales.

```anchor Urysohn_sig (module := UrysohnsLemma.Separation.urysohn)
lemma Urysohn {X : Type} {Y : Set ℝ}
    (T : TopologicalSpace X)
    [T' : TopologicalSpace ℝ]
    (hT' : T' = UsualTopology)
    {R : TopologicalSpace Y}
    {hY : Y = Set.Icc 0 1}
    {hR : R = TopoSubspace T' Y} :
    NormalSpace X ↔
      ∀ C1 : Set X, ∀ C2 : Set X,
      C1 ≠ ∅ → C2 ≠ ∅ →
      IsClosed C1 → IsClosed C2 →
      Disjoint C1 C2 →
      ∃ f : X → Y,
        Continuous f ∧
        f '' C1 = ({⟨0, by simp [hY]⟩} : Set Y) ∧
        f '' C2 = ({⟨1, by simp [hY]⟩} : Set Y) := by
```

# El recíproco

Veamos primero la demostración del recíproco, que es más sencilla.

*Demostración.* Supongamos que cualquier par de cerrados disjuntos de $`X` se pueden separar mediante una función continua y veamos que entonces $`X` es un espacio normal. Sean $`C_1` y $`C_2` cerrados disjuntos en $`X`.

```anchor Urysohn_reciprocal_intro (module := UrysohnsLemma.Separation.urysohn)
    intro h
    rw [normal_space_def] -- `1`
    intro C1 C2 hC1 hC2 hinter -- `2`
```

Como en la definición de normal no pedimos que los cerrados sean no vacíos, tenemos que diferenciar estos casos. Sin embargo, estos casos son triviales porque basta tomar el conjunto vacío para recubrir el vacío y $`X` para recubrir el otro conjunto. En Lean hay que ser rigurosos con este paso, pero aquí lo obviaremos por simplicidad.

Supongamos entonces que $`C_1` y $`C_2` son no vacíos. Por hipótesis, existe una función continua $`f : X \to [0, 1]` de forma que $`f(C_1) = \{0\}` y $`f(C_2) = \{1\}`.

```anchor Urysohn_reciprocal_obtain (module := UrysohnsLemma.Separation.urysohn)
    obtain ⟨f, hf, hfC1, hfC2⟩ := h C1 C2 hC1nempty hC2nempty hC1 hC2 hinter
```

Consideremos entonces los conjuntos $`U_1 = f^{-1}([0, \frac{1}{2}))` y $`U_2 = f^{-1}((\frac{1}{2}, 1])`. Queremos ver que son los abiertos que necesitamos de la definición de normal, es decir, que son abiertos en $`X`, que $`C_i \subseteq U_i` y que son disjuntos.

```anchor Urysohn_reciprocal_use (module := UrysohnsLemma.Separation.urysohn)
    use f ⁻¹' ({y | (y : ℝ) ∈ Set.Ico 0 (1 / 2)})
    use f ⁻¹' ({y | (y : ℝ) ∈ Set.Ioc (1 / 2) 1})
```

Para ver que $`U_1` es abierto, utilizamos que $`f` es continua. Basta ver que $`[0, \frac{1}{2})` es abierto en $`[0, 1]`. Pero ya vimos que los intervalos de la forma $`[0, b)` son abiertos en $`[0, 1]`, así que basta aplicar esta propiedad. Análogo para $`U_2`.

```anchor Urysohn_reciprocal_U1_open (module := UrysohnsLemma.Separation.urysohn)
    · apply hf -- aplicar def. de f continua
      apply ico_open_in_Icc01 -- `[0, 1/2)` es abierto en `[0, 1]`
      · exact hY
      · exact hR
      · norm_num
```

Para ver que $`C_1 \subseteq U_1`, basta ver que $`f(C_1) \subseteq [0, \frac{1}{2})`, que es trivial. Análogo para $`U_2`.

```anchor Urysohn_reciprocal_C1_subset_U1 (module := UrysohnsLemma.Separation.urysohn)
    · rw [← Set.image_subset_iff, hfC1] -- `{0} ⊆ [0, 1/2)` ?
      simp
```

Para ver que son disjuntos, vemos que $`[0, \frac{1}{2})` y $`(\frac{1}{2}, 1]` son disjuntos. Obviamente lo son, pero para Lean es un poco más complicado, así que procedemos por reducción al absurdo para poder simplificar las expresiones. Finalmente llegamos a que no existe un $`x` con $`x < 1/2` y $`x > 1/2`.

```anchor Urysohn_reciprocal_disjoint (module := UrysohnsLemma.Separation.urysohn)
    · apply Disjoint.preimage
      by_contra c
      apply (not_iff_not.mpr (Set.disjoint_iff_inter_eq_empty)).mp at c
      rw [← ne_eq, ← Set.nonempty_iff_ne_empty] at c
      obtain ⟨x, hxu, hxv⟩ := c
      simp at hxu hxv
      linarith
```
∎

La otra implicación es mucho más compleja, especialmente en su formalización en Lean, como veremos a continuación.

# Esquema de la demostración

Para la demostración de la primera implicación, he seguido la estrategia clásica basada en construir una familia de abiertos indexada por racionales. Aunque existen variantes que emplean subconjuntos particulares como los racionales diádicos, aquí hemos optado por una construcción sobre $`\mathbb{Q} \cap [0,1]`, siguiendo versiones habituales del lema presentes en la literatura. Aún así, el esquema que se presenta a continuación es también el resultado del proceso de demostración en Lean, que ha ido tomando forma a medida que se resolvían los distintos obstáculos que se han ido presentando.

Supongamos que $`X` es un espacio normal, y sean $`C_1` y $`C_2` dos cerrados disjuntos no vacíos de $`X`.

Consideremos $`U_1 = X` abierto. Consideremos el cerrado $`C_1` el abierto $`C_2^c` y aplicamos la caracterización de espacios normales ({ref "caracterizacion-normal"}[3.14]), obteniendo otro abierto $`U_0` de manera que

$$`C_1 \subseteq U_0 \subseteq \overline{U_0} \subseteq C_2^c \subseteq U_1 = X`

Podemos hacer lo mismo para $`\overline{U_0}` cerrado y $`C_2^c` abierto, obteniendo, por ejemplo, $`U_{\frac{1}{2}}` de forma que

$$`C_1 \subseteq U_0 \subseteq \overline{U_0} \subseteq U_{\frac{1}{2}} \subseteq \overline{U_{\frac{1}{2}}} \subseteq C_2^c \subseteq U_1`

Reiterando este proceso, vamos a construir una sucesión de abiertos sobre $`\mathbb{Q}\cap[0, 1]`, $`\{U_p | p \in \mathbb{Q}\cap[0, 1]\}`, de manera que

## La propiedad (★)
%%%
tag := "eq-star"
number := false
%%%

$$`\forall p , q \in \mathbb{Q}, p < q \implies \overline{U_p} \subseteq U_q`

Una vez tenemos esta sucesión, la extenderemos a todo $`\mathbb{Q}`, obteniendo lo que en Lean será una función $`G : \mathbb{Q} \to \mathcal{P}(X)`. Después, definiremos otra función $`F` sobre $`X` que a cada $`x \in X` le hace corresponder el conjunto

$$`F(x) = \{p \in \mathbb{Q} ~|~ x \in G(p)\}`

Por último, tomaremos la función $`f : X \to [0, 1]` definida por

$$`f(x) = \textnormal{inf}~F(x)`

Esta función será la que utilicemos. Tendremos que demostrar que efectivamente toma valores en $`[0, 1]`, que es continua y que separa nuestros conjuntos cerrados.

Sin embargo, una vez construidas estas funciones, este último paso es relativamente sencillo. La principal dificultad a la hora de formalizar esta demostración ha sido construir función $`G` y demostrar sus propiedades.

Como se puede apreciar en las primeras iteraciones de la construcción de cada $`U_q`, esta sucesión se construye por inducción. Para poder hacer inducción sobre los racionales, nos basamos en que son numerables, y, en particular, en que $`\mathbb{Q}\cap[0, 1]` lo es. Vamos a encontrar una función $`f : \mathbb{N} \to \mathbb{Q} \cap [0, 1]` biyectiva (invertible), de manera que $`f(0) = 1` y $`f(1) = 0`. Esto nos servirá para construir cada $`U_q`.

Después, para demostrar que efectivamente se cumple la condición ({ref "eq-star"}[★]), necesitaremos utilizar inducción sobre dos variables. Para ello, utilizaremos que el orden lexicográfico de $`(\mathbb{N} \times \mathbb{N})`, definido por $`(n, m) < (n', m') \iff n<n' \lor (n=n' \land m<m')`, es una relación bien fundada, y por tanto admite inducción sobre pares de naturales.

La principal dificultad de esta construcción ha sido encontrar los objetos adecuados para poder formalizar las ideas de la demostración, como la numerabilidad de los racionales o el orden lexicográfico, y aprender la forma correcta en la que trabajar con ciertas estructuras en Lean, como definir funciones recursivas con una recursión no usual.

# Construcción de la sucesión de abiertos

En primer lugar construiremos una sucesión de abiertos sobre $`\mathbb{Q}\cap[0, 1]`, y después la extenderemos al resto de los racionales. Sea $`Q = \mathbb{Q}\cap[0, 1]`. Para construir la sucesión $`\{U_p ~|~ p \in Q\}`, o, lo que es lo mismo, la función $`G : Q \to \mathcal{P}(X)`, $`G(p) = U_p`, vamos a proceder de la siguiente forma.

Como $`Q` es numerable, consideramos la numeración $`Q = \{p_k ~|~ k \in \mathbb{N}\}`, y suponemos por simplicidad que $`p_0 = 1` y que $`p_1 = 0`. Vamos a construir los abiertos con la condición ({ref "eq-star"}[★]) por inducción completa sobre $`k`.

Tomamos entonces, como base de la inducción,

* $`U_1 = U_{p_0} = X`.
* $`U_0 = U_{p_1}` el abierto obtenido al aplicar la caracterización de espacios normales ({ref "caracterizacion-normal"}[3.14]) al cerrado $`C_1` y el abierto $`C_2^c`.

Trivialmente se tiene que $`\overline{U_0} \subseteq U_1 = X` (con $`0<1`), luego se satisface ({ref "eq-star"}[★]).

Ahora, para el caso inductivo, supongamos que hemos definido $`U_{p_k}` para cada $`k = 0, 1, ..., n` satisfaciendo ({ref "eq-star"}[★]), y ahora queremos construir $`U_{p_{n+1}}`.

Notar que el conjunto $`\{p_0, p_1, ..., p_n\} \subset Q` no está necesariamente ordenado. Sin embargo, es un conjunto finito de números racionales, por tanto, podemos encontrar unos elementos $`p_r` y $`p_s` de manera que $`p_r` es el predecesor inmediato de $`p_{n+1}` y $`p_s` es el sucesor inmediato de $`p_{n+1}`. Es decir, se tiene

$$`p_r < p_{n+1} < p_s`

y no existe $`k\leq n` de forma que $`p_r < p_k < p_{n+1}` ni $`p_{n+1} < p_k < p_s`.

Puesto que $`p_r < p_s`, por la hipótesis de inducción completa se tiene que ambos son abiertos y que $`\overline{U_{p_r}} \subseteq U_{p_s}` ({ref "eq-star"}[★]). Aplicamos de nuevo la caracterización de espacios normales ({ref "caracterizacion-normal"}[3.14]), para encontrar un nuevo abierto $`U = U_{p_{n+1}}` tal que

$$`\overline{U_{p_r}} \subseteq U \subseteq \overline{U} \subseteq U_{p_s}`

Con lo que concluye la inducción.

Veamos ahora como se traduce esto en Lean.

## Numerar los racionales

Los racionales son numerables, es decir existe una biyección entre $`\mathbb{N}` y $`\mathbb{Q}`. En particular, necesitamos una función $`f : \mathbb{N} \to Q` donde $`Q = \mathbb{Q} \cap [0, 1]`, de forma que $`f` sea biyectiva, $`f(0) = 1` y $`f(1) = 0`. Es decir, la función que nos lleva cada $`k \in \mathbb{N}` a $`p_k`.

```anchor hf_sig (module := UrysohnsLemma.MyDefs.my_denumerableQ)
lemma hf : ∃ f : ℕ → Q, (f.Bijective ∧ f 0 = ⟨1, Q1⟩ ∧ f 1 = ⟨0, Q0⟩) := by
```

Para demostrar la existencia de tal función necesitamos una serie de resultados previos.

En primer lugar, la numerabilidad de los racionales ya está demostrada en Mathlib como `Rat.instDenumerable`. Para poder extraer una función biyectiva de este resultado, he escrito el siguiente lema:

```anchor bijective_nat_rat_full (module := UrysohnsLemma.MyDefs.my_denumerableQ)
lemma bijective_nat_rat : ∃ f : ℕ → ℚ, f.Bijective  := by
    have f := (Rat.instDenumerable.eqv).symm
    use f
    exact f.bijective
```

Evidentemente, por la independencia de las demostraciones de Lean, no podremos evaluar esta función de manera explícita. Pero tenemos la información que necesitamos de ella.

Ahora, quiero demostrar que existe una función biyectiva de $`\mathbb{N}` en $`Q`. Como ya tenemos una función biyectiva de $`\mathbb{N}` en $`\mathbb{Q}`, la idea es componerla con una biyección de $`\mathbb{Q}` en $`Q`.

Para demostrar que esta biyección existe, basta demostrar que $`\mathbb{Q}` y $`Q` tienen el mismo cardinal (`Cardinal.eq`). Pero, de hecho, cualquier subconjunto de $`\mathbb{Q}` no finito tiene cardinal $`\aleph_0` (demostrado en `non_finite_rat_set_cardinal_aleph0`). Basta demostrar que $`Q` no es finito (queda demostrado en `Q_not_finite`).

```anchor non_finite_rat_set_cardinal_aleph0_sig (module := UrysohnsLemma.MyDefs.my_denumerableQ)
lemma non_finite_rat_set_cardinal_aleph0 (A : Set ℚ) (hA : ¬ A.Finite) : Cardinal.mk ↑A = Cardinal.aleph0 := by
```

Por último, cualquier permutación de dos valores de una función preserva la biyectividad (demostrado en `permute_f_bijectivity`). Por tanto, podemos forzar que $`f(0) = 1` y $`f(1) = 0`.

```anchor permute_f_def (module := UrysohnsLemma.MyDefs.my_denumerableQ)
def permute_f {X Y : Type} [DecidableEq X]
    (f : X → Y) (a b : X)
    : X → Y :=
    fun x ↦
      if x = a then f b
      else if x = b then f a
      else f x
```

```anchor permute_f_bijectivity_sig (module := UrysohnsLemma.MyDefs.my_denumerableQ)
lemma permute_f_bijectivity {X Y : Type} [DecidableEq X]
    {f : X → Y} (a b : X)
    (h : f.Bijective) :
    (permute_f f a b).Bijective := by
```

Una vez demostrado `hf`, podemos definir $`f` mediante `Classical.choose` y empezar a trabajar con ella, aunque no la conozcamos explícitamente.

```anchor f_def (module := UrysohnsLemma.MyDefs.my_denumerableQ)
noncomputable def f : ℕ → Q := Classical.choose hf
```

Por ejemplo, podemos probar que tiene inversa.

```anchor f_has_inverse_full (module := UrysohnsLemma.MyDefs.my_denumerableQ)
lemma f_has_inverse :  ∃ g, Function.LeftInverse g f ∧ Function.RightInverse g f
  := by
  rw [← Function.bijective_iff_has_inverse]
  exact f_prop.left
```

## Encontrar el sucesor y predecesor inmediato

Ahora tenemos cada $`p_k` definido en Lean como $`f(k)` para cada $`k \in \mathbb{N}`. Para poder definir cada abierto $`U_{p_k}`, necesitamos ser capaces de encontrar para cada conjunto $`\{p_0, p_1, \dots, p_{n-1}\}`, el predecesor inmediato $`p_r` y el sucesor inmediato $`p_s` de $`p_{n}`.

De nuevo, en Lean esto se codifica como funciones; queremos encontrar una función $`r : \mathbb{N} \to \mathbb{N}` que, para cada $`n>1`, devuelva el predecesor inmediato de $`f(n)`, de entre $`\{f(k) ~|~ k < n\}`, y lo mismo para una función $`s : \mathbb{N} \to \mathbb{N}` que encuentre el sucesor inmediato. Sin embargo, la existencia de tales funciones no es trivial.

### Lema 4.1
%%%
number := false
%%%

Sea $`n > 1`. Entonces existe un $`r_n < n` de forma que $`f(r_n) < f(n)`, y si $`k < n` es tal que $`f(k) < f(n)` entonces $`f(k) \leq f(r_n)`.

```anchor exists_r_sig (module := UrysohnsLemma.MyDefs.my_rs_functions)
lemma exists_r (n : ℕ) (hn : n > 1) : ∃ r ∈ Finset.range n,
    ((f r < f n) ∧
    (∀ m ∈ Finset.range n, f m < f n → f m ≤ f r)) := by
```

*Demostración.* Sea $`n>1`. Consideremos el conjunto

$$`R = \{m : \mathbb{N} ~|~ m < n \land f(m) < f(n)\}`

```anchor exists_r_R_def (module := UrysohnsLemma.MyDefs.my_rs_functions)
  let R : Finset ℕ := (Finset.range n).filter (fun m ↦ f m < f n)
```

$`R` es un conjunto finito no vacío, pues $`1 \in R`

```anchor exists_r_hR_nonempty_preview (module := UrysohnsLemma.Docs.Urysohn)
  have hR : R.Nonempty
  · use 1; sorry
```

Tomamos el conjunto $`f(R)`, que también es un conjunto finito y no vacío, por serlo $`R`, luego tiene máximo. Tomamos el argumento máximo de $`f(R)`, $`r_n = \arg \max \{f(m) ~|~ m \in R\}`, y veamos que satisface las condiciones que pedimos.

```anchor exists_r_finish (module := UrysohnsLemma.MyDefs.my_rs_functions)
  let fR : Finset Q := R.image f
  -- tomamos el conjunto de as imágenes de R

  -- vemos que no es vacío
  have hfR : fR.Nonempty := (Finset.image_nonempty).mpr hR

  -- tomamos el máximo de las imágenes
  let fr := Finset.max' fR ((Finset.image_nonempty).mpr hR)
  -- tomamos el argumento de fr, fr = f r
  obtain ⟨r, hr⟩ := Finset.mem_image.mp (by exact Finset.max'_mem fR hfR)

  use r -- probamos que este r nos vale
```

Se tiene que $`r \in R`, luego $`r < n` y $`f(r) < f(n)`. Sea entonces un $`k < n` con $`f(k) < f(n)`. Por construcción, $`k \in R` y por tanto $`f(k) \in f(R)`. Como $`r` es el argumento máximo de $`f(R)`, $`f(r)` es el máximo de $`f(R)` y por tanto $`f(k) \leq f(R)`, como queríamos. ∎

La demostración completa está en el repositorio, así como el análogo para $`s`.

Garantizada la existencia de estas funciones, podemos tomar ahora las funciones $`r` y $`s` y empezar a trabajar con ellas.

```anchor r_def (module := UrysohnsLemma.MyDefs.my_rs_functions)
noncomputable def r : ℕ → ℕ := fun n ↦
  if h : n > 1 then Classical.choose (exists_r n h)
  else 1
```

```anchor s_def (module := UrysohnsLemma.MyDefs.my_rs_functions)
noncomputable def s : ℕ → ℕ := fun n ↦
  if h : n > 1 then Classical.choose (exists_s n h)
  else 0
```

Veamos las principales propiedades de estas dos funciones. En primer lugar, tenemos las propiedades básicas de $`r` y $`s` que son simplemente por construcción.

### Lema 4.2
%%%
number := false
%%%

Para cada $`n > 1`, se tiene:

$$`\left\{
  \begin{array}{l}
    r(n) < n \\
    f(r(n)) < f (n) \\
    \forall m < n, \textnormal{ si } f(m) < f(n) \textnormal{ entonces } f(m) \leq f(r(n))
  \end{array}
\right.`

```anchor r_prop_sig (module := UrysohnsLemma.MyDefs.my_rs_functions)
lemma r_prop (n : ℕ) (hn : n > 1) : (
  (r n ∈ Finset.range n) ∧
  (f (r n) < f n) ∧
  (∀ m ∈ Finset.range n, f m < f n → f m ≤ f (r n))
) := by
```

El resultado es simétrico para $`s` y recibe el nombre de `s_prop`.

### Lema 4.3
%%%
number := false
%%%

Sea $`n > 1`. Entonces o bien $`r(n) = 1` o bien $`r(n) > 1`. Es decir, no puede ser $`r(n) = 0`. De forma análoga, no puede ser $`s(n) = 1`, luego o bien $`s(n) = 0` o bien $`s(n) > 1`.

```anchor r_options_sig (module := UrysohnsLemma.MyDefs.my_rs_functions)
lemma r_options (n : ℕ) (hn : n > 1) : r n = 1 ∨ r n > 1 := by
```

```anchor s_options_sig (module := UrysohnsLemma.MyDefs.my_rs_functions)
lemma s_options (n : ℕ) (hn : n > 1) : s n = 0 ∨ s n > 1 := by
```

También se obtiene un resultado `rs_options` que encapsula las cuatro combinaciones posibles de valores para $`r` y $`s`, para facilitar el trabajo con ellas.

*Demostración.* Si fuera $`r(n) = 0`, tendríamos $`1 = f(0) = f(r(n)) < f(n)`, lo que es imposible pues $`f` toma valores en $`[0, 1]`. ∎

### Lema 4.4
%%%
number := false
%%%

Sea $`n > 1` y supongamos que $`s(n) > 1` y que $`r(n) < s(n)`. Entonces $`r(n) = r(s(n))`.

De manera análoga, si $`r(n) >1` y $`s(n) < r(n)`, entonces $`s(n) = s(r(n))`.

```anchor rn_eq_rsn_sig (module := UrysohnsLemma.MyDefs.my_rs_functions)
lemma rn_eq_rsn (n : ℕ) (hn : n > 1)
    (hsn : s n > 1)
    (h : r n < s n)
    : r n = r (s n) := by
```

El análogo a este recibe el nombre de `sn_eq_srn`.

*Demostración.* Demostramos solo el primero y el segundo es parecido. Sea $`n > 1` y supongamos que $`s(n) > 1` y que $`r(n) < s(n)`. Queremos ver que $`r(n) = r(s(n))`. Por la inyectividad de $`f`, podemos comprobar en su lugar que $`f (r (n)) = f (r (s (n)))`. Veamos que se cumplen ambas desigualdades.

```anchor rn_eq_rsn_start (module := UrysohnsLemma.MyDefs.my_rs_functions)
  apply f_prop.left.left
  apply ge_antisymm
```

(1) Para ver $`f (r (s (n))) \leq f (r (n))`, aplicamos la tercera parte de `r_prop`. Luego hay que ver que $`r(s(n)) < n`, lo cual sencillo por ser $`r(s(n)) < s(n) < n`, y que $`f (r (s (n))) < f n`. Esto último es cierto porque si fuera $`f(n) < f(r(s(n)))`, como $`r(s(n)) < s(n)` tendríamos $`f(s (n)) \leq f(r(s(n)))`, pero eso es imposible porque $`f(r(s(n))) < f(s(n))` por construcción (esta última parte viene dada por un resultado auxiliar `f_rs_prop`).

```anchor rn_eq_rsn_case1 (module := UrysohnsLemma.MyDefs.my_rs_functions)
  · -- f (r (s n)) ≤ f (r n)
    apply (r_prop n hn).right.right
    · simp
      trans s n
      · exact List.mem_range.mp (r_prop (s n) hsn).left
      · exact List.mem_range.mp (s_prop n hn).left
    · exact f_rs_prop n hn hsn
```

(2) Para ver que $`f (r (n)) \leq f (r (s (n)))`, basta ver que $`r(n) < s(n)` por hipótesis y que $`f(r(n)) < f(n) < f(s(n))` por las propiedades de $`r` y $`s`. Luego aplicando la tercera propiedad básica a $`s(n) > 1` y $`r(n) < s(n)` obtenemos el resultado.

```anchor rn_eq_rsn_case2 (module := UrysohnsLemma.MyDefs.my_rs_functions)
  · -- f (r n) ≤ f (r (s n))
    apply (r_prop (s n) hsn).right.right
    · exact List.mem_range.mpr h
    · trans f n
      · exact (r_prop n hn).right.left
      · exact (s_prop n hn).right.left
```
∎

## Construcción de $`G`

La construcción de $`G : \mathbb{Q} \to \mathcal{P}(X)` es, como hemos explicado, una construcción por inducción. Para empezar, es más fácil construir $`G : \mathbb{N} \to \mathcal{P}(X)`, y después tomar $`G \circ f^{-1} : Q \to \mathcal{P}(X)` donde $`f` es la función que numera $`Q` que habíamos obtenido antes.

Lean admite definiciones inductivas de una manera muy natural. Un ejemplo muy utilizado es la sucesión de Fibonacci: definir $`Fib(0) = 0` y $`Fib(1) = 1`, y a partir de ahí, $`Fib(n) = Fib(n-1)+Fib(n-2)` para cada $`n > 1`. En Lean, escribimos

```anchor Fib_def (module := UrysohnsLemma.Docs.Urysohn)
def Fib : ℕ → ℕ := fun n ↦
  if n = 0 then 0
  else if n = 1 then 1
  else Fib (n-1) + Fib (n-2)
```

En vista de esto, mi primer acercamiento a la construcción de $`G` fue el siguiente:

* Para $`n = 0`, definir $`G(0) = C_2^c`.
* Para $`n = 1`, tomar $`G(1)` el resultado de aplicar la caracterización de espacios normales al abierto $`C_2^c` y el cerrado $`C_1`.
* Para $`n >1`, tomar $`G(n)` el resultado de aplicar la caracterización de espacios normales ({ref "caracterizacion-normal"}[3.14]) al abierto $`G(s(n))` y el cerrado $`\overline{G(r(n))}`.

```
  def G {X : Type} [TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U →
      ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X) (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ) (hC1C2 : C1 ⊆ C2ᶜ)
    : ℕ → Set X := fun n ↦
      if n = 0 then C2ᶜ
      else if n = 1 then Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)
      else
        let U := g hT C1 C2 hC1 hC2 hC1C2 (s n)
        let C := closure (g hT C1 C2 hC1 hC2 hC1C2 (r n))
        Classical.choose (hT U C (by sorry) (by sorry) (by sorry))
```

Donde en los últimos `sorry` habría que demostrar que $`G(s(n))` es abierto, que $`\overline{G(r(n))}` es cerrado y que $`\overline{G(r(n))} \subseteq G(s(n))`, para poder aplicar la caracterización de la normalidad (`hT`).

Todo esto nosotros "lo sabemos": es la hipótesis de inducción. Pero a Lean todavía no le hemos dicho nada de eso. ¿Cómo podemos probar algo sobre un objeto que aún no hemos definido, porque necesitamos haberlo probado para poder definirlo?

Para evitar este problema, tomé una estrategia distinta. Primero, defino la noción de _par normal_ de la siguiente manera.

### Definición 4.1
%%%
number := false
%%%

Dados $`U, C \subseteq X`, decimos que $`(U, C)` es un _par normal_ si $`U` es abierto, $`C` es cerrado y $`C \subseteq U`. Es decir, si satisfacen las condiciones para poder aplicar la caracterización de espacios normales ({ref "caracterizacion-normal"}[3.14]).

```anchor normal_pair_def (module := UrysohnsLemma.Separation.def_G)
def normal_pair {X : Type} [TopologicalSpace X]
    : (Set X × Set X) → Prop := fun (U, C) ↦ (IsOpen U ∧ IsClosed C ∧ C ⊆ U)
```

Ahora, defino una función `from_normality` que toma dos conjuntos cualesquiera de $`X`, y devuelve el resultado de aplicar la caracterización de espacios normales si forman un par normal, y el conjunto vacío en caso contrario.

```anchor from_normality_def (module := UrysohnsLemma.Separation.def_G)
noncomputable def from_normality {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    : (Set X × Set X) → Set X :=

    fun (U, C) ↦

    if h : normal_pair (U, C) = True then
      Classical.choose (hT
        U
        C
        (by simp at h; exact h.left)
        (by simp at h; exact h.right.left)
        (by simp at h; exact h.right.right)
      )

    else ∅
```

Ahora, al construir $`G`, ya no me tengo que preocupar de si produce siempre conjuntos abiertos o no, porque lo puedo definir a partir de esta última función, que está definida para cualquieras dos conjuntos. Una vez definida, puedo demostrar que cada conjunto obtenido es de hecho abierto.

```anchor G_def_body (module := UrysohnsLemma.Separation.def_G)
def G {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)

    : ℕ → Set X

    := fun n ↦
      if n = 0 then C2ᶜ
      else if n = 1 then from_normality hT (C2ᶜ, C1)
      else if n > 1 then
        let U := G hT C1 C2 (s n)
        let C := closure (G hT C1 C2 (r n))
        from_normality hT (U, C)
      else ∅
```

Sin embargo, a Lean esto sigue sin parecerle suficiente, y recibimos este error: `fail to show termination for G`. Esto es, estamos definiendo una función recursiva, $`G`, pero no es evidente que las veces que estamos llamando a $`G` dentro de $`G` constituyan conjuntos ya definidos. Es decir, no es evidente que $`r(n) < n` y $`s(n) < n`. Por tanto, al final de la definición tenemos que añadir una demostración de que sí es así.

```
  ...
      else ∅

    decreasing_by
    · let s_prop := s_prop
      have aux : ∀ n > 1, s n < n
      · intro n hn
        specialize s_prop n hn
        simp at s_prop
        exact s_prop.left
      apply aux
      linarith
    · sorry -- analogo r
```

¡Ya tenemos nuestra función $`G`! Aunque todavía queda mucho trabajo. Veamos que se cumplen las propiedades que queríamos de $`G`.

### Lema 4.5
%%%
tag := "prop-G-open"
number := false
%%%

Para cada $`n \in \mathbb{N}`, $`G(n)` es abierto en $`X`.

```anchor G_Prop1_sig (module := UrysohnsLemma.Separation.def_G)
lemma G_Prop1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n : ℕ, IsOpen (G hT C1 C2 n) := by
```

*Demostración.* Notemos que la función `from_normality` siempre produce abiertos, porque o bien es el resultado de aplicar {ref "caracterizacion-normal"}[3.14], o bien es el vacío que es abierto (demostrado en `from_normality_open`).

Sea $`n \in \mathbb{N}`. Tenemos que distinguir en tres casos, pues existen tres casos en la definición de $`G`.

(1) Si $`n = 0`, entonces simplemente por hipótesis $`G(0) = C_2^c` es abierto.

```anchor G_Prop1_case_n0 (module := UrysohnsLemma.Separation.def_G)
  intro n


  cases' Nat.eq_zero_or_pos n with hn hn
  · -- n = 0
    simp [hn, G]
    exact { isOpen_compl := hC2 }
```

(2) Si $`n = 1`, entonces estamos aplicando la función `from_normality` a $`C_2^c` y $`C_1`. Luego es abierto.

```anchor G_Prop1_case_n1 (module := UrysohnsLemma.Separation.def_G)
  have : n = 1 ∨ n > 1  := Or.symm (Decidable.lt_or_eq_of_le' hn)
  cases' this with hn1 hn1
  · -- n = 1
    rw [G]
    simp [hn1]
    exact from_normality_open hT C2ᶜ C1
```

(3) Ahora, si $`n > 1`, entonces estamos aplicando la función `from_normality` a $`G(s(n))` y $`\overline{G(r(n))}`. Luego es abierto análogamente. ∎

Para el siguiente resultado vamos a utilizar inducción completa. Yo he definido mi propio principio de inducción completa, demostrado a partir de la inducción completa usual en Lean, por sencillez.

```anchor my_stronger_induction_sig (module := UrysohnsLemma.MyDefs.my_induction)
theorem my_stronger_induction (n : ℕ) (P Q : ℕ → Prop)
    (hn : P n)
    (h : ∀ n : ℕ, P n → ((∀ m < n, P m → Q m) → Q n)) :
    (Q n) := by
```

### Lema 4.6
%%%
number := false
%%%

Para cada $`n > 1`, se tiene:

$$`\overline{G(r(n))} \subseteq G(n) \subseteq \overline{G(n)} \subseteq G(s(n))`

```anchor G_Prop2_sig (module := UrysohnsLemma.Separation.def_G)
lemma G_Prop2 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n > 1, closure (G hT C1 C2 (r n)) ⊆ (G hT C1 C2 n)
      ∧ closure (G hT C1 C2 n) ⊆ (G hT C1 C2 (s n)) := by
```

*Demostración.* Procedemos por inducción completa sobre $`n`.

```anchor G_Prop2_start (module := UrysohnsLemma.Separation.def_G)
  intro n hn

  let P : ℕ → Prop := fun m ↦ m > 1
  apply my_stronger_induction n P
  exact hn
  simp [P]
  intro n hn hi
```

Tenemos la siguiente hipótesis de inducción: para cada $`m < n` con $`m > 1` se tiene que $`\overline{G(r(m))} \subseteq G(m) \subseteq \overline{G(m)} \subseteq G(s(m))`.

Queremos ver que entonces lo mismo se tiene para $`n`.

```
hi : ∀ m < n, 1 < m → closure (G hT C1 C2 (r m)) ⊆ G hT C1 C2 m ∧ closure (G hT C1 C2 m) ⊆ G hT C1 C2 (s m)

⊢ closure (G hT C1 C2 (r n)) ⊆ G hT C1 C2 n ∧ closure (G hT C1 C2 n) ⊆ G hT C1 C2 (s n)
```

Notemos que si $`G(n)` está obtenido mediante {ref "caracterizacion-normal"}[3.14] aplicado a $`G(s(n))` y $`\overline{G(r(n))}`, lo anterior se reduce a comprobar que $`(G(s(n)), \overline{G(r(n))})` es un par normal (demostrado en `from_normality_prop2`).

```anchor G_Prop2_normalpair_stmt (module := UrysohnsLemma.Separation.def_G)
  have normalpair : normal_pair (G hT C1 C2 (s n), closure (G hT C1 C2 (r n)))
```

Hemos visto que $`r(n)` es o bien $`r(n) = 1` o bien $`r(n) > 1` (`r_options`) y $`s(n)` es o bien $`s(n) = 0` o bien $`s(n) > 1` (`s_options`). Veamos por ejemplo el caso $`r(n) = 1`, $`s(n) > 1`. El resto son parecidos y se pueden consultar en el repositorio.

(1) Ver que $`G(s(n))` es abierto es sencillo; ya hemos visto que $`G` siempre devuelve abiertos.

```
  ...
    · exact G_Prop1 hT C1 C2 hC1 hC2 hC1C2 (s n)
```

(2) Ver que $`\overline{G(r(n))}` es cerrado es sencillo; ya hemos visto que la adherencia de cualquier conjunto es cerrada.

```
  ...
    · exact isClosed_closure
```

(3) Ahora, para ver que $`\overline{G(r(n))} \subseteq G(s(n))`, necesitamos utilizar la hipótesis de inducción.

Sabemos que $`s(n) < n`. Luego podemos aplicar la hipótesis de inducción a $`s(n)`, obteniendo que

$$`\overline{G(r(s(n)))} \subseteq G(s(n)) \subseteq \overline{G(s(n))} \subseteq G(s(s(n)))`

Pero, puesto que $`s(n) >1`, se tiene que $`r(n) = r(s(n))` (`rn_eq_rsn`), obteniendo $`\overline{G(r(n))} \subseteq G(s(n))`.

```
  ...
    · have hsn := (s_prop n hn).left -- hsn : s n ∈ Finset.range n
      simp at hsn -- hsn : s n < n
      specialize hi (s n) hsn hs -- aplicar la H.I. a s(n)
      rw [rn_eq_rsn n hn hs (by linarith)] -- usar r(n) = r(s(n))
      exact hi.left
```
∎

## La propiedad (★)

Esta es la propiedad más importante que queremos pedirle a la función $`G`, pues es la que garantiza la continuidad de la función que queremos construir para la demostración del lema de Urysohn, como veremos más adelante.

### Lema 4.7
%%%
number := false
%%%

Sean $`n, m \in \mathbb{N}` con $`f(n) < f(m)`. Entonces

$$`\overline{G(n)} \subseteq G(m)`

```anchor G_Prop2_ext_sig (module := UrysohnsLemma.Separation.def_G)
lemma G_Prop2_ext {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n m, f n < f m → closure (G hT C1 C2 n) ⊆ G hT C1 C2 m := by
```

Para demostrar este resultado vamos a utilizar un principio de inducción más general que la inducción usual sobre los naturales. Siempre que se cuente con una relación bien fundada en un conjunto, se puede describir un principio de inducción sobre este conjunto.

En nuestro caso, vamos a utilizar el orden lexicográfico sobre $`\mathbb{N}^2`, definido por $`(n, m) < (n', m') \iff n<n' \lor (n=n' \land m<m')`. Este ya está definido en Mathlib, y también está demostrado que es una relación bien fundada.

```anchor lt_pair_defs (module := UrysohnsLemma.MyDefs.my_lex_order)
def lt_pair : (ℕ × ℕ) → (ℕ × ℕ) → Prop := Prod.Lex (Nat.lt) (Nat.lt)
def lt_pair_wfr : WellFoundedRelation (ℕ × ℕ) := Prod.lex (Nat.lt_wfRel) (Nat.lt_wfRel)
lemma lt_pair_wf : WellFounded lt_pair := lt_pair_wfr.wf
```

*Demostración.* Procedemos por tanto por inducción bien fundada sobre el par $`(n, m)`

```
    := by
  ... -- ciertas modificaciones del objetivo
  apply WellFounded.induction lt_pair_wf
  ...
  intro n m
  intro hi hnm
```

Por tanto tenemos la siguiente hipótesis de inducción:

```
  hi : ∀ (a b : ℕ), lt_pair (a, b) (n, m) → f a < f b → closure (G hT C1 C2 a) ⊆ G hT C1 C2 b
```

Ahora dividimos entre distintos casos de valores de $`n` y $`m`. Nos centramos en el caso $`n >1, m>1`, que es el más interesante, y el resto se pueden consultar en el repositorio.

Además, hay tres casos posibles: o bien $`f(s(n)) < f(m)`, o bien $`f(s(n)) = f(m)`, o bien $`f(s(n)) > f(m)`.

(1) Si $`f(s(n)) < f(m)`, tenemos por un lado que $`\overline{G(s(n))} \subseteq G(m)`, por ser $`(s(n), m) < (n, m)` y la hipótesis de inducción.

Por otro lado, $`\overline{G(n)} \subseteq G(s(n))`, por la segunda propiedad de $`G`. Luego tenemos

$$`\overline{G(n)} \subseteq G(s(n)) \subseteq \overline{G(s(n))} \subseteq G(m)`

```
  ...
    · -- si f (s n) < f m
      trans closure (G hT C1 C2 (s n))
      · trans G hT C1 C2 (s n)
        · exact (G_Prop2 n hn1).right
        · exact subset_closure
      · exact hi (s n) m (by left; exact s_prop.left) h
```

(2) Si $`f(s(n)) = f(m)` es muy fácil, porque entonces por la inyectividad de $`f` se tiene $`s(n)= m`, y $`\overline{G(n)} \subseteq G(s(n)) = G(m)` por la segunda propiedad de $`G`.

```
  ...
    · -- si f (s n) = f m
      apply f_prop.left.left at h
      rw [h]
      exact (G_Prop2 n hn1).right
```

(3) Supongamos ahora que $`f(s(n))>f(m)`. Este es el caso más complicado, y requiere que volvamos a dividir en tres posibles opciones para $`f(n) \sim f(r(m))`.

Si $`f(n) < f(r(m))`, procedemos de manera parecida a (1), utilizando la hipótesis de inducción para $`(n, r(m)) < (n, m)`. Si $`f(n) = f(r(m))`, hacemos lo mismo que en (2). Por último, queda demostrar que no se puede dar $`f(r(m)) < f(n)`.

En efecto, si $`f(s(n))>f(m)`, se tiene que dar $`n < m`, porque si fuera $`m<n` tendríamos $`f(n) < f(m) < f(s(n))`, lo cual es imposible por las propiedades de $`s`. Pero entonces si fuera $`f(r(m)) < f(n)` tendríamos $`f(r(m)) < f(n) < f(m)` con $`n < m`, que es imposible por las propiedades de $`r`.

```
  ...
    · -- si f (r m) < f n
      by_contra
      have r_prop := r_prop.right.right n n_lt_m hnm -- f n ≤ f (r m)
      apply not_lt.mpr at r_prop -- ¬f (r m) < f n
      exact r_prop h' -- teniamos h' : f (r m) < f n
```
∎

## Composición con $`f^{-1}`

Por último, recordemos que la función $`G` que estábamos buscando no es de la forma $`\mathbb{N} \to \mathcal{P}(X)` sino de la forma $`\mathbb{Q} \cap [0, 1] \to \mathcal{P}(X)`. En particular, vamos a extenderla a $`\mathbb{Q} \to \mathcal{P}(X)` de la siguiente forma:

$$`H : \mathbb{Q} \to \mathcal{P}(X), ~~ q \mapsto
\begin{cases}
\emptyset & \text{si } q < 0 \\
(G \circ f^{-1})(q) & \text{si } 0 \leq q \leq 1 \\
X & \text{si } 1 < q
\end{cases}`

```anchor H_def (module := UrysohnsLemma.Separation.def_H)
def H {X : Type} [TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)

    : ℚ → Set X := fun q ↦

  if q < 0 then ∅
  else if h : 0 ≤ q ∧ q ≤ 1 then G hT C1 C2 (f_inv ⟨q, h⟩)
  else Set.univ
```

### Lema 4.8
%%%
number := false
%%%

Para los cerrados $`C_1` y $`C_2` elegidos al principio de la sección, la función $`H` previamente definida satisface las siguientes propiedades:

1. $`H(1) = C_2^c`
1. $`H(0)` es tal que $`C_1 \subseteq H(0) \subseteq \overline{H(0)} \subseteq C_2^c`
1. Para cada $`q \in \mathbb{Q}`, $`H(q)` es abierto en $`X`.
1. Para cada $`p, q \in \mathbb{Q}` con $`p < q`, se tiene $`\overline{H(p)} \subseteq H(q)`

*Demostración.* Todas estas propiedades se deducen casi trivialmente de las de $`G`, utilizando que $`f` es biyectiva y los valores fijos que toma en el $`0` y el $`1`. El único añadido son los valores fuera de $`[0, 1]`, para los que las últimas propiedades se demuestran fácilmente puesto que $`\emptyset` y $`X` son abiertos, $`\overline{\emptyset} = \emptyset \subseteq U` para cualquier $`U` y $`U \subseteq X` para cualquier $`U`. ∎

# Construcción de una función continua separadora

Siguiendo con el esquema que habíamos propuesto, construimos ahora la siguiente función

$$`\begin{array}{rcrcl}
  F & : & X & \longrightarrow & \mathcal{P}(\mathbb{Q}) \\
    & & x & \longmapsto & \{p \in \mathbb{Q} ~|~ x \in H(p)\}
\end{array}`

```anchor F_def (module := UrysohnsLemma.Separation.def_F)
def F {X : Type} [TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)

    : X → Set ℚ := fun x : X ↦ {p : ℚ | x ∈ H hT C1 C2 p}
```

Ahora, queremos construir una función de la siguiente forma

$$`\begin{array}{rcrcl}
  f & : & X & \longrightarrow & [0, 1] \\
    & & x & \longmapsto & \inf F(x)
\end{array}`

Sin embargo, tenemos que asegurarnos de que podemos definir esta función, es decir, de que el conjunto $`F(x)` tiene ínfimo para cada $`x \in X`.

## La función $`F`
%%%
tag := "seccion-funcion-F"
%%%

### Lema 4.9
%%%
number := false
%%%

Sea $`F :  X  \to \mathcal{P}(\mathbb{Q})` la función definida anteriormente. Entonces para cada $`x \in X`, $`F(x)` es un conjunto no vacío.

*Demostración.* Sea $`x \in X`. Cualquier $`q > 1` es tal que $`q \in F(x)`, pues si $`q >1`, $`H(q) = X`, luego $`x \in H(q)`. ∎

```anchor hF_non_empty_full (module := UrysohnsLemma.Separation.def_F)
lemma hF_non_empty {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    :  ∀ x : X, (F hT C1 C2 x).Nonempty := by
  intro x
  use 2
  simp [F, H]
```

### Lema 4.10
%%%
number := false
%%%

Para cada $`x \in X`, si $`q < 0` entonces $`q \notin F(x)`. Es decir, todos los elementos de $`F(x)` son no negativos.

*Demostración.* Sea $`x \in X` y $`q < 0`. Entonces $`H(q) = \emptyset`, luego obviamente $`x \notin H(q)`. ∎

Llamaremos a este resultado `hFx_non_neg`. Como consecuencia, se tiene:

### Lema 4.11
%%%
number := false
%%%

Para cada $`x \in X`, $`0` es una cota inferior de $`F(x)`.

```anchor hFx_has_lb_0_sig (module := UrysohnsLemma.Separation.def_F)
lemma hFx_has_lb_0 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, 0 ∈ lowerBounds (F hT C1 C2 x) := by
```

Por tanto, dado $`x \in X`, puesto que $`F(x)` es un conjunto no vacío y acotado inferiormente, podemos concluir que $`F(x)` tiene un ínfimo *como conjunto real*, es decir, podemos concluir que existe un número $`r \in \mathbb{R}` de forma que $`r = \inf F(x)`. Este resultado está incluido en Mathlib:

```anchor Real_exists_isGLB_quote (module := UrysohnsLemma.Docs.Urysohn)
theorem Real.exists_isGLB {s : Set ℝ} (hne : s.Nonempty) (hbdd : BddBelow s) :
    ∃ x, IsGLB s x
```

Podríamos intentar escribir algo así:

```
  lemma hFx_has_lb_0 (...)
    : ∀ x : X, ∃ r : ℝ, IsGLB (F hT C1 C2 x) r := by sorry
```

Sin embargo, esto nos da el siguiente error:

```
  argument r has type ℝ but is expected to have type ℚ
```

Esto es porque, en Mathlib, `IsGLB` está definido de la siguiente forma:

```anchor IsGLB_def_quote (module := UrysohnsLemma.Docs.Urysohn)
def IsGLB [Preorder α] (s : Set α) : α → Prop :=
  IsGreatest (lowerBounds s)
```

Es decir, sólo está definido para valores de tipo $`\alpha` si $`s \subset \alpha`. Como $`F(x) \subset \mathbb{Q}`, no podemos decir que $`r \in \mathbb{R}` sea su ínfimo.

Por tanto, necesitamos definir en Lean una función auxiliar $`\tilde{F}` de forma que $`\tilde{F}(x) = F(x)` para cada $`x`, pero visto como subconjunto de $`\mathbb{R}`. Lo hacemos de la siguiente manera.

```anchor inclQR_F_Real_def (module := UrysohnsLemma.Separation.def_F)
def inclQR : ℚ → ℝ := fun q ↦ q

def F_Real {X : Type} [TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : X → Set ℝ :=

    fun x ↦ inclQR '' (F hT C1 C2 x)
```

Esta nueva función $`\tilde{F}` es una función con las mismas propiedades que $`F`, es decir, para cada $`x \in X`, $`\tilde{F}(x)` es un conjunto no vacío con $`0` como cota inferior. Esto se prueba de manera inmediata utilizando las propiedades de $`F`, aunque es necesario tener cuidado con la inferencia de tipos de Lean en algunos casos.

Pero ahora $`\tilde{F}` devuelve subconjuntos de $`\mathbb{R}`, luego podemos asegurar que tiene un ínfimo en $`\mathbb{R}`.

```anchor F_Real_has_inf_full (module := UrysohnsLemma.Separation.def_F)
lemma F_Real_has_inf {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, ∃ r : ℝ, IsGLB (F_Real hT C1 C2 x) r := by

  intro x
  apply Real.exists_isGLB
  exact F_Real_Nonempty hT C1 C2 x
  exact F_Real_BddBelow hT C1 C2 x
```

## La función $`f`
%%%
tag := "seccion-funcion-f"
%%%

Una vez hemos asegurado que $`\tilde{F}` tiene ínfimo, podemos intentar definir nuestra función $`f` como queríamos. Antes de eso, hagamos la siguiente anotación.

Nosotros queremos encontrar una función $`f : X \to [0, 1]`. Sin embargo, sólo hemos garantizado que $`\inf \tilde{F}(x) \in \mathbb{R}`; no necesariamente $`\inf \tilde{F}(x) \in [0, 1]`.

Evidentemente, esto último es cierto, porque $`0` es cota inferior, luego el ínfimo será al menos $`0`, y $`\forall q>1, q \in F(x)`, luego el ínfimo no podrá ser mayor que $`1`.

Sin embargo, por facilidad a la hora de trabajar con Lean, definiremos primero una función que sea simplemente

$$`\begin{array}{rcrcl}
  k & : & X & \longrightarrow & \mathbb{R} \\
    & & x & \longmapsto & \inf \tilde{F}(x)
\end{array}`

y probamos que en efecto $`k(x) \in [0, 1]` para cada $`x\in X`. Más tarde, utilizaremos la función $`f(x) = k(x)` teniendo cuidado en especificar que $`k(x) \in [0, 1]`.

```anchor k_def (module := UrysohnsLemma.Separation.def_k)
noncomputable def k {X : Type} [TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : X → ℝ :=
    fun x ↦ Classical.choose (F_Real_has_inf hT C1 C2 x)
```

Obtenemos la siguiente propiedad, fruto de aplicar `Classical.choose_spec` a $`k`.

```anchor k_prop_sig (module := UrysohnsLemma.Separation.def_k)
lemma k_prop {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x, IsGLB (F_Real hT C1 C2 x) (k hT C1 C2 x) := by
```

### Lema 4.12
%%%
number := false
%%%

Para cada $`x \in X`, la función $`k : X \to \mathbb{R}` que acabamos de definir satisface $`k(x) \in [0, 1]`.

```anchor k_in_01_sig (module := UrysohnsLemma.Separation.def_k)
lemma k_in_01 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, (k hT C1 C2 x) ∈ Set.Icc 0 1 := by
```

*Demostración.* La prueba es sencilla y ya la hemos explicado, pero en Lean necesitamos dar una especificación completa, así que la explicamos.

Sea $`x \in X`. Recordemos que $`k(x)` es cota inferior de $`\tilde{F}(x)` (`klb`) y es la mayor de ellas (`kglb`).

```anchor k_in_01_start (module := UrysohnsLemma.Separation.def_k)
  intro x
  have ⟨klb, kglb⟩ := k_prop hT C1 C2 x
  constructor
```

Ver que $`k(x) \geq 0` es fácil, porque ya hemos visto que $`0` es cota superior, y $`k(x)` es la mayor.

```anchor k_in_01_case1 (module := UrysohnsLemma.Separation.def_k)
  · exact kglb (F_Real_0_is_LB hT C1 C2 x)
```

Ahora, para ver que $`k(x) \leq 1`, procedemos por reducción al absurdo. Supongamos que $`k(x) > 1`. Entonces existe un número racional $`q` de forma que $`1 < q < k(x)`. Como $`q > 1`, sabemos que $`q \in \tilde{F}(x)`. Pero en ese caso, como $`k(x)` es cota inferior, $`k(x) \leq q`, lo que es contradictorio.

```anchor k_in_01_case2 (module := UrysohnsLemma.Separation.def_k)
  · by_contra c
    simp at c
    obtain ⟨q, hq1, hqk⟩ := exists_rat_btwn c
    have hq := F_Real_1inf hT C1 C2 x q (by exact_mod_cast hq1)
    apply klb at hq
    apply not_lt.mpr at hq
    exact hq hqk
```
∎

Por último, antes de pasar a la demostración del lema de Urysohn finalmente, damos varias propiedades de $`k` que necesitaremos. Recordemos que $`H` era $`G \circ f^{-1}` extendida a $`\mathbb{Q}`.

### Lema 4.13
%%%
tag := "claim1"
number := false
%%%

Para cada $`p \in \mathbb{Q}` y cada $`x \in X`, si $`x \in \overline{H(p)}` entonces $`k(x) \leq p`.

```anchor k_claim1_sig (module := UrysohnsLemma.Separation.def_k)
lemma k_claim1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ p : ℚ, ∀ x : X, x ∈ closure (H hT C1 C2 p) → (k hT C1 C2 x) ≤ p := by
```

*Demostración.* Sean $`p \in \mathbb{Q}` y $`x \in X` con $`x \in \overline{H(p)}`. Supongamos, por reducción al absurdo, que $`k(x) > p`. Entonces existe un racional $`q \in \mathbb{Q}` de forma que $`p < q < k(x)`.

```anchor k_claim1_start (module := UrysohnsLemma.Separation.def_k)
  intro p x hx
  by_contra c
  simp at c
  have ⟨q, hq⟩ := exists_rat_btwn c
```

Como $`p < q` y $`x \in \overline{H(p)}`, por ({ref "eq-star"}[★]) se tiene que $`x \in H(q)`.

```anchor k_claim1_apply_ordered (module := UrysohnsLemma.Separation.def_k)
  apply H_isOrdered hT C1 C2 hC1 hC2 hC1C2 p q
    (by exact_mod_cast hq.left)
    at hx
```

Ahora, $`x \in H(q)` quiere decir que $`q \in \tilde{F}(x)`. Pero $`k(x)` es cota superior de $`\tilde{F}(x)`, luego $`k(x) < q`, lo que contradice $`q < k(x)`.

```anchor k_claim1_finish (module := UrysohnsLemma.Separation.def_k)
  have aux : inclQR q ∈ F_Real hT C1 C2 x
  · simp [F_Real]
    use q
    simp
    exact hx

  have ⟨klb, _⟩ := k_prop hT C1 C2 x
  apply klb at aux
  apply not_lt.mpr at aux
  exact aux hq.right
```
∎

### Lema 4.14
%%%
tag := "claim2"
number := false
%%%

Para cada $`p \in \mathbb{Q}` y cada $`x \in X`, si $`x \notin H(p)` entonces $`k(x) \geq p`.

```anchor k_claim2_sig (module := UrysohnsLemma.Separation.def_k)
lemma k_claim2 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ p : ℚ, ∀ x : X, x ∉ (H hT C1 C2 p) → (k hT C1 C2 x) ≥ p := by
```

*Demostración.* La demostración es muy parecida a la anterior y puede encontrarse en el repositorio. ∎

## Propiedades sobre los cerrados $`C_1` y $`C_2`

Por último, veamos cómo se comportan la función $`k` en los cerrados que queremos separar. Esto nos dejará el camino completamente allanado para completar la demostración del lema de Urysohn. Vamos a ver las demostraciones para $`C_1`, y para $`C_2` son similares y se pueden comprobar en el repositorio.

Queremos llegar a que $`k(C_1) = \{0\}`. Esta propiedad se construye paso a paso, utilizando propiedades de las funciones en las que se apoya.

### Lema 4.15
%%%
number := false
%%%

Consideremos $`F : X \to \mathcal{P}(\mathbb{Q})`. Para cada $`x \in C_1`, se tiene que $`F(x) = \{q \in \mathbb{Q} ~|~ q \geq 0\}`.

```anchor F_at_C1_sig (module := UrysohnsLemma.Separation.def_F)
lemma F_at_C1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ x : X, x ∈ C1 → F hT C1 C2 x = {q : ℚ | q ≥ 0} := by
```

*Demostración.* Sea $`x \in C_1`. Ver que $`F(x) \subseteq \{q \in \mathbb{Q} ~|~ q \geq 0\}` es sencillo, pues ya hemos visto que ningún valor de $`F(x)` es negativo (`hFx_non_neg`). Ahora, sea $`q \geq 0` y veamos que $`q \in F(x)`, es decir, que $`x \in H(q)`.

Si $`q > 0`, por la propiedad ({ref "eq-star"}[★]) de $`H`, $`\overline{H(0)} \subseteq H(q)`. Y por construcción de $`H` se tiene $`C_1 \subseteq H(0)`. Luego $`x \in H(q)`. Si $`q = 0`, como $`C_1 \subseteq H(0)`, $`x\in H(q)`.

```anchor F_at_C1_case_q_geq_0 (module := UrysohnsLemma.Separation.def_F)
  · simp only [ge_iff_le, Set.mem_setOf_eq] at hq
    cases' Decidable.lt_or_eq_of_le hq with hq hq

    · apply H_isOrdered hT C1 C2 hC1 hC2 hC1C2 0 q hq
      apply subset_closure
      exact H_C1_in_H0 hT C1 C2 hC1 hC2 hC1C2 hx

    · rw [← hq]
      exact H_C1_in_H0 hT C1 C2 hC1 hC2 hC1C2 hx
```
∎

### Lema 4.16
%%%
number := false
%%%

Consideremos $`F : X \to \mathcal{P}(\mathbb{Q})`. Para cada $`x \in C_1`, se tiene que $`\inf{F}(x) = 0`.

```anchor F_0_GLB_in_C1_sig (module := UrysohnsLemma.Separation.def_F)
lemma F_0_GLB_in_C1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ x : X, x ∈ C1 → IsGLB (F hT C1 C2 x) 0 := by
```

Una vez sabemos que $`F(x) = \{q \in \mathbb{Q} ~|~ q \geq 0\}`, ver que el ínfimo de este conjunto es 0 es directo. Notemos que aquí sí podemos definir el ínfimo sobre $`F` porque $`0 \in \mathbb{Q}`. Ahora podemos afirmar lo mismo para $`\tilde{F}`, simplemente teniendo cuidado con el tipo de $`F(x)` y de $`0`.

### Lema 4.17
%%%
number := false
%%%

Consideremos $`\tilde{F} : X \to \mathcal{P}(\mathbb{R})`. Para cada $`x \in C_1`, se tiene que $`\inf{\tilde{F}}(x) = 0`.

```anchor F_Real_0_GLB_in_C1_sig (module := UrysohnsLemma.Separation.def_F)
lemma F_Real_0_GLB_in_C1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ x : X, x ∈ C1 → IsGLB (F_Real hT C1 C2 x) 0 := by
```

Por último, tenemos:

### Lema 4.18
%%%
tag := "prop-kC1"
number := false
%%%

Consideremos $`k : X \to \mathbb{R}`. Recordemos que $`C_1` es no vacío. Se tiene que $`k (C_1) = \{0\}`.

```anchor k_in_C1_is_0_sig (module := UrysohnsLemma.Separation.def_k)
lemma k_in_C1_is_0 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)
    (hC1_nonempty : C1 ≠ ∅)

    : k hT C1 C2 '' C1 = {0} := by
```

*Demostración.* Para ver que $`k(C_1) \subseteq \{0\}`, puesto que $`k(x) := \inf \tilde{F}(x)`, y $`\inf \tilde{F}(x) = 0` para $`x \in C_1` por el resultado anterior, basta utilizar el el ínfimo es único.

```anchor k_in_C1_is_0_forward (module := UrysohnsLemma.Separation.def_k)
  ext r
  constructor
  · intro ⟨x, hx, hr⟩
    rw [← hr]
    apply IsGLB.unique (k_prop hT C1 C2 x)
    exact F_Real_0_GLB_in_C1 hT C1 C2 hC1 hC2 hC1C2 x hx
```

Para ver que $`\{0\} \subseteq k(x)`, necesitamos ver que existe un $`x \in C_1` tal que $`k(x) = 0`. Como $`C_1` es no vacío, sea $`x \in C_1` cualquiera. Entonces $`k(x) = 0`, procediendo de la misma forma que en el primer contenido.

```anchor k_in_C1_is_0_backward (module := UrysohnsLemma.Separation.def_k)
  · intro hr
    rw [hr]
    obtain ⟨x, hx⟩ := nonempty_has_element C1 hC1_nonempty
    use x
    constructor
    · exact hx
    · have aux := F_Real_0_GLB_in_C1 hT C1 C2 hC1 hC2 hC1C2 x hx
      have aux' := Classical.choose_spec (F_Real_has_inf hT C1 C2 x)
      exact IsGLB.unique aux' aux
```
∎

# La demostración

Vamos a demostrar, por tanto, la implicación principal del lema de Urysohn, siguiendo paso a paso la demostración en Lean.

Sea $`X` un espacio normal. Queremos demostrar que para cada par de cerrados disjuntos no vacíos $`C_1` y $`C_2` existe una función continua $`f : X \to [0, 1]` de forma que $`f(C_1) = \{0\}` y $`f(C_2) = \{1\}`.

Sean por tanto $`C_1` y $`C_2` cerrados con esas condiciones.

```anchor Urysohn_forward_intro (module := UrysohnsLemma.Separation.urysohn)
  · -- →
    intro hT C1 C2 C1nempty C2nempty C1closed C2closed C1C2disj
```

Para empezar, demostramos algunas propiedades auxiliares, como que $`C_2^c` es abierto (por ser $`C_2` cerrado), y que $`C_1 \subseteq C_2^c` (por ser disjuntos), que nos facilitarán aplicar el resto de resultados que hemos ido probando. También utilizaremos la caracterización de espacios normales ({ref "caracterizacion-normal"}[3.14]) sobre la hipótesis de $`X` normal.

```anchor Urysohn_forward_aux (module := UrysohnsLemma.Separation.urysohn)
    have C2c_open : IsOpen C2ᶜ := by exact IsClosed.isOpen_compl
    have hC1C2 : C1 ⊆ C2ᶜ := by exact Disjoint.subset_compl_left (id (Disjoint.symm C1C2disj))

    rw [characterization_of_normal] at hT
```

Ahora, por comodidad vamos a definir las siguientes funciones.

```anchor Urysohn_forward_let_Gg (module := UrysohnsLemma.Separation.urysohn)
    let G := H hT C1 C2
    let g := fun x ↦ k hT C1 C2 x
```

De esta forma no tenemos que arrastrar los argumentos de $`H` y $`k` en cada paso. Cambio el nombre de $`H` a $`G` para seguir con la notación del esquema, puesto que es la función de la forma $`G : \mathbb{N} \to \mathcal{P}(X)`. También cambio el nombre de $`k` a $`g`, para evitar confusiones.

Ahora, recordemos que $`k : X \to \mathbb{R}` no era exactamente la función que buscábamos. Vamos a definir finalmente la función a utilizar para separar nuestros cerrados, $`f`, de la siguiente manera:

```anchor Urysohn_forward_let_f (module := UrysohnsLemma.Separation.urysohn)
    let f : X → Y := fun x ↦ ⟨g x, by
      rw [hY]
      exact k_in_01 hT C1 C2 x⟩
```

Es decir, $`f` es una función que toma valores en $`X` y devuelve un valor real y una demostración de que este valor está en realidad en el intervalo $`[0, 1]`, dada utilizando `k_in_01`, que habíamos demostrado antes. Por tanto, Lean la interpreta como una función $`f : X \to [0, 1]`, que es justo lo que queríamos.

Así que ya tenemos la función separadora y podemos dar el gran paso:

```anchor Urysohn_forward_use_f (module := UrysohnsLemma.Separation.urysohn)
    use f
```

Nos queda por demostrar que $`f` es continua, que $`f(C_1) = \{0\}` y que $`f(C_1) = \{1\}`.

```anchor Urysohn_forward_constructor (module := UrysohnsLemma.Separation.urysohn)
    constructor
```

## Continuidad de $`f`

Queremos ver que $`f` es continua. Para ello, aplicamos el resultado `continuousInSubspace_iff_trueForBase`, que vimos que era combinación de {ref "prop-continuidad-subespacio"}[3.12] y {ref "prop-continuous-base"}[3.13].

```anchor Urysohn_continuity_rw (module := UrysohnsLemma.Separation.urysohn)
    · rw [@continuousInSubspace_iff_trueForBase
        X ℝ Y T T' R hR f
        {s | ∃ a b : ℝ, s = Set.Ioo a b}
        (by exact BaseOfRealTopo hT')]
```

Luego basta demostrar que para cada abierto básico $`W` de $`\mathbb{R}`, $`f^{-1}(W)` es abierto en $`X`. Sea $`W = (a, b)` un abierto de la base formada por los intervalos abiertos reales.

```anchor Urysohn_continuity_introW (module := UrysohnsLemma.Separation.urysohn)
      intro W hW
      obtain ⟨a, b, hW⟩ := hW
```

Queremos ver que $`f^{-1}(W)` es abierto en $`X`. Utilizando la caracterización de abiertos ({ref "caracterizacion-abierto"}[3.1]), basta ver que es entorno de todos sus puntos. Sea entonces $`x \in f^{-1}(W)`, lo que quiere decir que $`f(x) \in (a, b)`.

```anchor Urysohn_continuity_neighbourhood (module := UrysohnsLemma.Separation.urysohn)
      rw [A_open_iff_neighbourhood_of_all]
      intro x hx
      rw [Set.mem_preimage, hW] at hx
```

Puesto que $`f(x) \in (a, b)`, se tiene que existe $`p \in \mathbb{Q}` con $`a < p < f(x)`, y también existe $`q \in \mathbb{Q}` con $`f(x) < q < b`.

```anchor Urysohn_continuity_pq (module := UrysohnsLemma.Separation.urysohn)
      obtain ⟨p, hp⟩ := exists_rat_btwn hx.left
      obtain ⟨q, hq⟩ := exists_rat_btwn hx.right
```

Vamos a demostrar que $`x \in G(q)` y que $`x \notin \overline{G(p)}`.

Primero recordemos los resultados {ref "claim1"}[4.13] y {ref "claim2"}[4.14] (con los nombres de las funciones correspondientes a la notación actual):

* `k_claim1`: $`\forall p \in \mathbb{Q},\forall x \in X, x \in \overline{G(p)} \implies g(x) \leq p`
* `k_claim2`: $`\forall p \in \mathbb{Q},\forall x \in X, x \notin G(p) \implies g(x) \geq p`

```anchor Urysohn_continuity_claims (module := UrysohnsLemma.Separation.urysohn)
      have claim1 := k_claim1 hT C1 C2
        C1closed (by exact IsClosed.isOpen_compl)
        (by exact hC1C2)

      have claim2 := k_claim2 hT C1 C2
        C1closed (by exact IsClosed.isOpen_compl)
        (by exact hC1C2)
```

(1) Para ver que $`x \notin \overline{G(p)}`, por reducción al absurdo supongamos que sí está. Entonces podemos aplicar `claim1` y obtener que $`g(x) \leq p` pero teníamos $`p < f(x) = g(x)`, contradicción.

```anchor Urysohn_continuity_aux1 (module := UrysohnsLemma.Separation.urysohn)
      have aux1 : x ∉ closure (G p)
      · by_contra c
        apply claim1 p x at c
        linarith
```

(2) De manera similar, si suponemos por reducción al absurdo que $`x \notin U(q)`, entonces por `claim2` obtenemos que $`g(x) \geq q`, pero teníamos $`q > f(x) = g(x)`, contradicción.

```anchor Urysohn_continuity_aux2 (module := UrysohnsLemma.Separation.urysohn)
      have aux2 : x ∈ G q
      · by_contra c
        apply claim2 q x at c
        linarith
```

Recapitulando, queremos ver que $`f^{-1}(W)` es entorno de $`x` ($`x` era arbitrario). Esto es, por definición, encontrar un conjunto $`U\subseteq X` que sea abierto y de manera que $`x \in U \subseteq f^{-1}(W)`.

Tomemos el conjunto $`U = G(q) \cap (\overline{G(p)})^c` y veamos que cumple estas condiciones.

```anchor Urysohn_continuity_use_U (module := UrysohnsLemma.Separation.urysohn)
      use (G q) ∩ (closure (G p))ᶜ

      constructor
```

(1) Veamos que $`U \subseteq f^{-1}(W)`. Para ello, sea $`y \in U` y veamos que $`y \in f^{-1}(W) = f^{-1}((a, b))`, es decir, veamos que $`a < f(y) < b`.

```anchor Urysohn_continuity_use_U_intro_y (module := UrysohnsLemma.Separation.urysohn)
      · intro y hy
        rw [hW]
        constructor
```

Se tiene que $`y \notin G(p)`, pues en caso contrario, $`y \in G(p) \subseteq \overline{G(p)}`, pero $`y \in \overline{G(p)}^c`. Aplicando `claim1`, se tiene que $`f(y) = g(y) \geq p > a`.

```anchor Urysohn_continuity_case_a (module := UrysohnsLemma.Separation.urysohn)
        · have hy : y ∉ G p
          · by_contra c
            apply subset_closure at c
            exact hy.right c
          apply claim2 p y at hy
          linarith
```

Por otro lado, como $`y \in G(q) \subseteq \overline{G(q)}`, por `claim2` se tiene que $`f(y) = g(y) \leq q < b`.

```anchor Urysohn_continuity_case_b (module := UrysohnsLemma.Separation.urysohn)
        · have hy := hy.left
          apply subset_closure at hy
          specialize claim1 q y hy
          linarith
```

Luego concluimos que $`f(y) \in (a, b) = W`. El trabajo duro ya está hecho, ya solo falta ver que $`x \in U` y que $`U` es abierto.

```anchor Urysohn_continuity_constructor2 (module := UrysohnsLemma.Separation.urysohn)
      constructor
```

(2) Como habíamos visto, $`x \in G(q)` y $`x \notin \overline{G(p)}`. Luego $`x \in U`.

```anchor Urysohn_continuity_xinV (module := UrysohnsLemma.Separation.urysohn)
      · -- probar que `x ∈ V`
        constructor
        · exact aux2
        · exact aux1
```

(3) Probar que $`U` es abierto es sencillo: como es una intersección finita, basta ver que ambos componentes son abiertos. Por {ref "prop-G-open"}[4.5], $`G(q)` es abierto. Además, $`\overline{G(p)}` es cerrado por ser una clausura, luego su complementario es abierto.

```anchor Urysohn_continuity_Vopen (module := UrysohnsLemma.Separation.urysohn)
      · -- probar que `V` es abierto
        apply IsOpen.inter
        · exact H_isOpen hT C1 C2 C1closed C2c_open hC1C2 q
        · rw [isOpen_compl_iff]
          exact isClosed_closure
```

## Imagen de $`f`

Para terminar la demostración, solo nos falta ver que $`f(C_1) = \{0\}` y que $`f(C_2) = \{1\}`.

Para empezar, notemos que $`f(A) = g(A)` para cualquier $`A \subseteq X`.

```anchor Urysohn_image_aux (module := UrysohnsLemma.Separation.urysohn)
    have aux : ∀ A : Set X, f '' A = g '' A
    · intro A; ext x; simp [f]
```

Luego podemos reducir el objetivo a $`g(C_1) = \{0\}` y que $`g(C_2) = \{1\}`.

El resultado se deduce entonces del lema {ref "prop-kC1"}[4.18] y su análogo para $`C_2`.

```anchor Urysohn_forward_finish (module := UrysohnsLemma.Separation.urysohn)
    constructor
    /-
            2. f(C1) = {0}
    -/
    · exact k_in_C1_is_0 hT C1 C2 C1closed C2c_open hC1C2 C1nempty
    /-
            3. f(C2) = {1}
    -/

    · exact k_in_C2_is_1 hT C1 C2 C1closed C2c_open hC1C2 C2nempty
```

Lo que concluye la prueba del lema de Urysohn.

# La prueba de Mathlib

La prueba del lema de Urysohn que he descrito en este capítulo ha sido implementada por mí de manera completamente independiente a la de Mathlib, la cual no leí hasta haber escrito completamente mi demostración. Para cerrar este capítulo me gustaría hacer una breve comparación de ambas.

La implementación que se encuentra en Mathlib está documentada en {ref "ref-mathlib2023urysohn"}[\[17\]].

Como comentamos al principio del capítulo, la parte más complicada de la demostración ha sido construir la función $`G`, por requerir inducción completa para construir los abiertos e inducción sobre dos variables para probar sus propiedades. En efecto, en la documentación de Mathlib, escriben:

> La mayoría de las fuentes prueban el lema de Urysohn utilizando una familia de conjuntos abiertos indexada por los números racionales diádicos en $`[0, 1]`. Hay muchas dificultades técnicas al formalizar esta demostración (por ejemplo, es necesario formalizar la "inducción diádica", y luego probar que la familia resultante de conjuntos abiertos es monótona).

En efecto, es posible construir la sucesión que nosotros hemos construido tomando sólo los diádicos, pero uno se encuentra con problemas parecidos a los que hemos encontrado nosotros. El objetivo de la prueba de Mathlib, es, por tanto, evitar esta complicación. A continuación veremos un esquema de la demostración de Mathlib.

Sea $`X` un espacio normal. Sea $`\mathcal{CU}_X` el conjunto de los pares normales de $`X`, es decir, los pares de la forma $`(C, U)` con $`U` abierto, $`C` cerrado y $`C \subseteq U`. Definimos las funciones:

$$`\begin{array}{ccrclcccrcl}
  L & : & \mathcal{CU}_X & \longrightarrow & \mathcal{CU}_X & ~~y~~ & R & : & \mathcal{CU}_X & \longrightarrow & \mathcal{CU}_X \\
  & & (C, U) & \longmapsto & (C, V) & & & & (C, V) & \longmapsto & (\overline{V}, U)
\end{array}`

Donde $`V` es el resultado de aplicar la caracterización de espacios normales ({ref "caracterizacion-normal"}[3.14]) al par $`(C, U)` correspondiente.

Además, para cada $`(C, U) \in \mathcal{CU}_X` consideremos la sucesión de funciones $`\{f_n^{(C, U)} : X \to \mathbb{R}\}_{n\in \mathbb{N}}` dada por

$$`\left\{
\begin{array}{lclc}
  f_0^{(C, U)}(x)  & = & \chi_{U^c}(x) & \\
  & & & \\
  f_{n+1}^{(C, U)}(x) & = & \dfrac{f_n^{L(C, U)}(x) + f_n^{R(C, U)}(x)}{2}, & n = 0, 1, \dots
\end{array}
\right.`

Se puede probar que esta es una sucesión monótona de funciones de forma que, para cada par $`(C, U)` y cada $`n \in \mathbb{N}`, $`f_n^{(C, U)}(x) =0, \forall x \in C`, $`f_n^{(C, U)}(x) = 1,\forall x \in D`, y $`f_n^{(C, U)}(x) \in [0, 1],\forall x \in X`.

En particular, sean $`C` y $`D` los cerrados disjuntos que queremos separar y consideremos el par $`(C, D^c) \in \mathcal{CU}_X`. Sea $`f : X \to \mathbb{R}` la función dada por

$$`f(x) = \lim_{n \to \infty} f_n^{(C, D^c)}`

Entonces $`f` es una función continua que separa $`C` y $`D`.
