import VersoManual
import DocsEn.Espacios
import Docs.Papers

open Verso.Genre Manual
open Verso.Code.External
open Verso.Genre.Manual.Docs (citetOther citepOther citehereOther)
open Docs (refWillard2012General refMathlib2023Urysohn)

set_option pp.rawOnError true
-- Keep this in every translated chapter so bibliography text renders in English:
set_option docs.bib.lang "en"
set_option verso.exampleProject "../../.."
set_option verso.exampleModule "UrysohnsLemma.Separation.urysohn"

#doc (Manual) "Urysohn's Lemma" =>
%%%
tag := "lema-urysohn"
file := "lema-urysohn"
%%%

Urysohn's lemma is one of the central results of general topology. Its importance lies in the fact that it makes it possible to characterise the normality of a topological space in terms of continuous functions.

While the classical separation axioms require the existence of disjoint open sets to separate points or sets, there are versions that require separation by continuous functions. These versions are more restrictive and, therefore, define stronger properties. However, Urysohn's lemma shows that in the case of normal spaces this does not happen: separating closed sets by continuous functions is equivalent to doing so by open sets.

This result has key applications, such as its use in the proof of Urysohn's metrisation theorem, which provides sufficient conditions for a space to be metrisable. Moreover, the proof of the lemma is of great interest in itself, especially for our purposes, since it is based on an explicit and non-trivial construction of the desired function. It is precisely the construction of this function that a good part of this section will be devoted to.

# Theorem 4.1 (Urysohn's Lemma)
%%%
tag := "thm-urysohn"
number := false
file := "teorema-4-1"
%%%

{citepOther refWillard2012General}[] (p. 102, 15.6. Urysohn's Lemma).

Let $`(X, \mathcal{T})` be a topological space. $`X` is a normal space if and only if for each pair of disjoint closed sets $`C` and $`D` in $`X`, there exists a function $`f : X \to [0, 1]` such that $`f(C) = \{0\}` and $`f(D) = \{1\}`.

For the formalisation in Lean, we will require the closed sets $`C` and $`D` to be non-empty. Obviously, if one of the two is empty, it suffices to take the continuous function $`f(x) \equiv 1`, but we can discard these trivial cases.

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

# The converse
%%%
file := "el-reciproco"
%%%

Let us first see the proof of the converse, which is easier.

*Proof.* Suppose that any pair of disjoint closed sets of $`X` can be separated by a continuous function, and let us see that then $`X` is a normal space. Let $`C_1` and $`C_2` be disjoint closed sets in $`X`.

```anchor Urysohn_reciprocal_intro (module := UrysohnsLemma.Separation.urysohn)
    intro h
    rw [normal_space_def] -- `1`
    intro C1 C2 hC1 hC2 hinter -- `2`
```

Since in the definition of normal we do not ask the closed sets to be non-empty, we have to distinguish these cases. However, these cases are trivial because it suffices to take the empty set to cover the empty set and $`X` to cover the other set. In Lean we have to be rigorous with this step, but here we will skip it for simplicity.

Suppose, then, that $`C_1` and $`C_2` are non-empty. By hypothesis, there exists a continuous function $`f : X \to [0, 1]` such that $`f(C_1) = \{0\}` and $`f(C_2) = \{1\}`.

```anchor Urysohn_reciprocal_obtain (module := UrysohnsLemma.Separation.urysohn)
    obtain ⟨f, hf, hfC1, hfC2⟩ := h C1 C2 hC1nempty hC2nempty hC1 hC2 hinter
```

Consider then the sets $`U_1 = f^{-1}([0, \frac{1}{2}))` and $`U_2 = f^{-1}((\frac{1}{2}, 1])`. We want to see that they are the open sets we need for the definition of normal, that is, that they are open in $`X`, that $`C_i \subseteq U_i` and that they are disjoint.

```anchor Urysohn_reciprocal_use (module := UrysohnsLemma.Separation.urysohn)
    use f ⁻¹' ({y | (y : ℝ) ∈ Set.Ico 0 (1 / 2)})
    use f ⁻¹' ({y | (y : ℝ) ∈ Set.Ioc (1 / 2) 1})
```

To see that $`U_1` is open, we use that $`f` is continuous. It suffices to see that $`[0, \frac{1}{2})` is open in $`[0, 1]`. But we already saw that intervals of the form $`[0, b)` are open in $`[0, 1]`, so it suffices to apply that property. Analogous for $`U_2`.

```anchor Urysohn_reciprocal_U1_open (module := UrysohnsLemma.Separation.urysohn)
    · apply hf -- aplicar def. de f continua
      apply ico_open_in_Icc01 -- `[0, 1/2)` es abierto en `[0, 1]`
      · exact hY
      · exact hR
      · norm_num
```

To see that $`C_1 \subseteq U_1`, it suffices to see that $`f(C_1) \subseteq [0, \frac{1}{2})`, which is trivial. Analogous for $`U_2`.

```anchor Urysohn_reciprocal_C1_subset_U1 (module := UrysohnsLemma.Separation.urysohn)
    · rw [← Set.image_subset_iff, hfC1] -- `{0} ⊆ [0, 1/2)` ?
      simp
```

To see that they are disjoint, we see that $`[0, \frac{1}{2})` and $`(\frac{1}{2}, 1]` are disjoint. Obviously they are, but for Lean it is a bit more complicated, so we proceed by contradiction in order to simplify the expressions. Finally we arrive at the fact that there is no $`x` with $`x < 1/2` and $`x > 1/2`.

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

The other implication is much more complex, especially in its Lean formalisation, as we will see next.

# Outline of the proof
%%%
file := "esquema"
%%%

For the proof of the first implication, I have followed the classical strategy based on constructing a family of open sets indexed by rationals. Although there are variants that use particular subsets such as the dyadic rationals, here we have opted for a construction over $`\mathbb{Q} \cap [0,1]`, following usual versions of the lemma found in the literature. Even so, the outline presented below is also the result of the proof process in Lean, which took shape as the various obstacles that came up were resolved.

Suppose that $`X` is a normal space, and let $`C_1` and $`C_2` be two non-empty disjoint closed sets of $`X`.

Consider the open set $`U_1 = X`. Consider the closed set $`C_1` and the open set $`C_2^c` and apply the characterisation of normal spaces ({ref "caracterizacion-normal"}[3.14]), obtaining another open set $`U_0` such that

$$`C_1 \subseteq U_0 \subseteq \overline{U_0} \subseteq C_2^c \subseteq U_1 = X`

We can do the same for the closed set $`\overline{U_0}` and the open set $`C_2^c`, obtaining, for example, $`U_{\frac{1}{2}}` such that

$$`C_1 \subseteq U_0 \subseteq \overline{U_0} \subseteq U_{\frac{1}{2}} \subseteq \overline{U_{\frac{1}{2}}} \subseteq C_2^c \subseteq U_1`

Iterating this process, we are going to construct a sequence of open sets over $`\mathbb{Q}\cap[0, 1]`, $`\{U_p | p \in \mathbb{Q}\cap[0, 1]\}`, such that

## The property (★)
%%%
tag := "eq-star"
number := false
%%%

$$`\forall p , q \in \mathbb{Q}, p < q \implies \overline{U_p} \subseteq U_q`

Once we have this sequence, we will extend it to all of $`\mathbb{Q}`, obtaining what in Lean will be a function $`G : \mathbb{Q} \to \mathcal{P}(X)`. Afterwards, we will define another function $`F` on $`X` that assigns to each $`x \in X` the set

$$`F(x) = \{p \in \mathbb{Q} ~|~ x \in G(p)\}`

Finally, we will take the function $`f : X \to [0, 1]` defined by

$$`f(x) = \textnormal{inf}~F(x)`

This will be the function we use. We will have to prove that it indeed takes values in $`[0, 1]`, that it is continuous and that it separates our closed sets.

However, once these functions are constructed, this last step is relatively easy. The main difficulty in formalising this proof has been constructing the function $`G` and proving its properties.

As can be seen in the first iterations of the construction of each $`U_q`, this sequence is built by induction. In order to do induction over the rationals, we rely on the fact that they are countable, and, in particular, on the fact that $`\mathbb{Q}\cap[0, 1]` is. We are going to find a bijective (invertible) function $`f : \mathbb{N} \to \mathbb{Q} \cap [0, 1]`, such that $`f(0) = 1` and $`f(1) = 0`. This will serve us to construct each $`U_q`.

Then, to prove that condition ({ref "eq-star"}[★]) indeed holds, we will need to use induction on two variables. To do so, we will use that the lexicographic order on $`(\mathbb{N} \times \mathbb{N})`, defined by $`(n, m) < (n', m') \iff n<n' \lor (n=n' \land m<m')`, is a well-founded relation, and therefore admits induction on pairs of naturals.

The main difficulty of this construction has been finding the right objects to formalise the ideas of the proof, such as the countability of the rationals or the lexicographic order, and learning the correct way to work with certain structures in Lean, such as defining recursive functions with an unusual recursion.

# Construction of the sequence of open sets
%%%
file := "construccion-abiertos"
%%%

First we will construct a sequence of open sets over $`\mathbb{Q}\cap[0, 1]`, and then we will extend it to the rest of the rationals. Let $`Q = \mathbb{Q}\cap[0, 1]`. To construct the sequence $`\{U_p ~|~ p \in Q\}`, or, equivalently, the function $`G : Q \to \mathcal{P}(X)`, $`G(p) = U_p`, we are going to proceed in the following way.

Since $`Q` is countable, we consider the numbering $`Q = \{p_k ~|~ k \in \mathbb{N}\}`, and we assume for simplicity that $`p_0 = 1` and that $`p_1 = 0`. We are going to construct the open sets with condition ({ref "eq-star"}[★]) by complete induction on $`k`.

We take then, as the base of the induction,

* $`U_1 = U_{p_0} = X`.
* $`U_0 = U_{p_1}` the open set obtained when applying the characterisation of normal spaces ({ref "caracterizacion-normal"}[3.14]) to the closed set $`C_1` and the open set $`C_2^c`.

Trivially we have that $`\overline{U_0} \subseteq U_1 = X` (with $`0<1`), hence ({ref "eq-star"}[★]) is satisfied.

Now, for the inductive case, suppose we have defined $`U_{p_k}` for each $`k = 0, 1, ..., n` satisfying ({ref "eq-star"}[★]), and now we want to construct $`U_{p_{n+1}}`.

Note that the set $`\{p_0, p_1, ..., p_n\} \subset Q` is not necessarily ordered. However, it is a finite set of rational numbers; therefore, we can find elements $`p_r` and $`p_s` such that $`p_r` is the immediate predecessor of $`p_{n+1}` and $`p_s` is the immediate successor of $`p_{n+1}`. That is, we have

$$`p_r < p_{n+1} < p_s`

and there is no $`k\leq n` such that $`p_r < p_k < p_{n+1}` nor $`p_{n+1} < p_k < p_s`.

Since $`p_r < p_s`, by the complete induction hypothesis we have that both are open and that $`\overline{U_{p_r}} \subseteq U_{p_s}` ({ref "eq-star"}[★]). We apply the characterisation of normal spaces ({ref "caracterizacion-normal"}[3.14]) again, to find a new open set $`U = U_{p_{n+1}}` such that

$$`\overline{U_{p_r}} \subseteq U \subseteq \overline{U} \subseteq U_{p_s}`

Which concludes the induction.

Let us now see how this is translated into Lean.

## Numbering the rationals

The rationals are countable, that is, there exists a bijection between $`\mathbb{N}` and $`\mathbb{Q}`. In particular, we need a function $`f : \mathbb{N} \to Q` where $`Q = \mathbb{Q} \cap [0, 1]`, such that $`f` is bijective, $`f(0) = 1` and $`f(1) = 0`. That is, the function that takes each $`k \in \mathbb{N}` to $`p_k`.

```anchor hf_sig (module := UrysohnsLemma.MyDefs.my_denumerableQ)
lemma hf : ∃ f : ℕ → Q, (f.Bijective ∧ f 0 = ⟨1, Q1⟩ ∧ f 1 = ⟨0, Q0⟩) := by
```

To prove the existence of such a function we need a series of previous results.

First of all, the countability of the rationals is already proved in Mathlib as `Rat.instDenumerable`. In order to extract a bijective function from this result, I have written the following lemma:

```anchor bijective_nat_rat_full (module := UrysohnsLemma.MyDefs.my_denumerableQ)
lemma bijective_nat_rat : ∃ f : ℕ → ℚ, f.Bijective  := by
    have f := (Rat.instDenumerable.eqv).symm
    use f
    exact f.bijective
```

Evidently, by the proof irrelevance of Lean, we will not be able to evaluate this function explicitly. But we have the information we need from it.

Now, I want to prove that there exists a bijective function from $`\mathbb{N}` to $`Q`. Since we already have a bijective function from $`\mathbb{N}` to $`\mathbb{Q}`, the idea is to compose it with a bijection from $`\mathbb{Q}` to $`Q`.

To prove that this bijection exists, it suffices to prove that $`\mathbb{Q}` and $`Q` have the same cardinality (`Cardinal.eq`). But, in fact, any non-finite subset of $`\mathbb{Q}` has cardinality $`\aleph_0` (proved in `non_finite_rat_set_cardinal_aleph0`). It suffices to prove that $`Q` is not finite (proved in `Q_not_finite`).

```anchor non_finite_rat_set_cardinal_aleph0_sig (module := UrysohnsLemma.MyDefs.my_denumerableQ)
lemma non_finite_rat_set_cardinal_aleph0 (A : Set ℚ) (hA : ¬ A.Finite) : Cardinal.mk ↑A = Cardinal.aleph0 := by
```

Finally, any permutation of two values of a function preserves bijectivity (proved in `permute_f_bijectivity`). Therefore, we can force $`f(0) = 1` and $`f(1) = 0`.

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

Once `hf` is proved, we can define $`f` via `Classical.choose` and start working with it, even if we do not know it explicitly.

```anchor f_def (module := UrysohnsLemma.MyDefs.my_denumerableQ)
noncomputable def f : ℕ → Q := Classical.choose hf
```

For example, we can prove that it has an inverse.

```anchor f_has_inverse_full (module := UrysohnsLemma.MyDefs.my_denumerableQ)
lemma f_has_inverse :  ∃ g, Function.LeftInverse g f ∧ Function.RightInverse g f
  := by
  rw [← Function.bijective_iff_has_inverse]
  exact f_prop.left
```

## Finding the immediate successor and predecessor

We now have each $`p_k` defined in Lean as $`f(k)` for each $`k \in \mathbb{N}`. In order to define each open set $`U_{p_k}`, we need to be able to find, for each set $`\{p_0, p_1, \dots, p_{n-1}\}`, the immediate predecessor $`p_r` and the immediate successor $`p_s` of $`p_{n}`.

Again, in Lean this is encoded as functions; we want to find a function $`r : \mathbb{N} \to \mathbb{N}` that, for each $`n>1`, returns the immediate predecessor of $`f(n)`, among $`\{f(k) ~|~ k < n\}`, and likewise a function $`s : \mathbb{N} \to \mathbb{N}` that finds the immediate successor. However, the existence of such functions is not trivial.

### Lemma 4.1
%%%
number := false
%%%

Let $`n > 1`. Then there exists an $`r_n < n` such that $`f(r_n) < f(n)`, and if $`k < n` is such that $`f(k) < f(n)` then $`f(k) \leq f(r_n)`.

```anchor exists_r_sig (module := UrysohnsLemma.MyDefs.my_rs_functions)
lemma exists_r (n : ℕ) (hn : n > 1) : ∃ r ∈ Finset.range n,
    ((f r < f n) ∧
    (∀ m ∈ Finset.range n, f m < f n → f m ≤ f r)) := by
```

*Proof.* Let $`n>1`. Consider the set

$$`R = \{m : \mathbb{N} ~|~ m < n \land f(m) < f(n)\}`

```anchor exists_r_R_def (module := UrysohnsLemma.MyDefs.my_rs_functions)
  let R : Finset ℕ := (Finset.range n).filter (fun m ↦ f m < f n)
```

$`R` is a non-empty finite set, since $`1 \in R`

```anchor exists_r_hR_nonempty_preview (module := UrysohnsLemma.Docs.Urysohn)
  have hR : R.Nonempty
  · use 1; sorry
```

We take the set $`f(R)`, which is also a finite and non-empty set, since $`R` is, hence it has a maximum. We take the argument of the maximum of $`f(R)`, $`r_n = \arg \max \{f(m) ~|~ m \in R\}`, and let us see that it satisfies the conditions we require.

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

We have that $`r \in R`, hence $`r < n` and $`f(r) < f(n)`. Let then $`k < n` with $`f(k) < f(n)`. By construction, $`k \in R` and therefore $`f(k) \in f(R)`. Since $`r` is the argument of the maximum of $`f(R)`, $`f(r)` is the maximum of $`f(R)` and therefore $`f(k) \leq f(R)`, as we wanted. ∎

The complete proof is in the repository, as well as the analogue for $`s`.

Having guaranteed the existence of these functions, we can now take the functions $`r` and $`s` and start working with them.

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

Let us see the main properties of these two functions. First, we have the basic properties of $`r` and $`s`, which hold simply by construction.

### Lemma 4.2
%%%
number := false
%%%

For each $`n > 1`, we have:

$$`\left\{
  \begin{array}{l}
    r(n) < n \\
    f(r(n)) < f (n) \\
    \forall m < n, \textnormal{ if } f(m) < f(n) \textnormal{ then } f(m) \leq f(r(n))
  \end{array}
\right.`

```anchor r_prop_sig (module := UrysohnsLemma.MyDefs.my_rs_functions)
lemma r_prop (n : ℕ) (hn : n > 1) : (
  (r n ∈ Finset.range n) ∧
  (f (r n) < f n) ∧
  (∀ m ∈ Finset.range n, f m < f n → f m ≤ f (r n))
) := by
```

The result is symmetric for $`s` and goes by the name `s_prop`.

### Lemma 4.3
%%%
number := false
%%%

Let $`n > 1`. Then either $`r(n) = 1` or $`r(n) > 1`. That is, $`r(n) = 0` is impossible. Analogously, $`s(n) = 1` is impossible, hence either $`s(n) = 0` or $`s(n) > 1`.

```anchor r_options_sig (module := UrysohnsLemma.MyDefs.my_rs_functions)
lemma r_options (n : ℕ) (hn : n > 1) : r n = 1 ∨ r n > 1 := by
```

```anchor s_options_sig (module := UrysohnsLemma.MyDefs.my_rs_functions)
lemma s_options (n : ℕ) (hn : n > 1) : s n = 0 ∨ s n > 1 := by
```

We also obtain a result `rs_options` that encapsulates the four possible combinations of values for $`r` and $`s`, to make working with them easier.

*Proof.* If we had $`r(n) = 0`, we would have $`1 = f(0) = f(r(n)) < f(n)`, which is impossible since $`f` takes values in $`[0, 1]`. ∎

### Lemma 4.4
%%%
number := false
%%%

Let $`n > 1` and suppose that $`s(n) > 1` and that $`r(n) < s(n)`. Then $`r(n) = r(s(n))`.

Analogously, if $`r(n) >1` and $`s(n) < r(n)`, then $`s(n) = s(r(n))`.

```anchor rn_eq_rsn_sig (module := UrysohnsLemma.MyDefs.my_rs_functions)
lemma rn_eq_rsn (n : ℕ) (hn : n > 1)
    (hsn : s n > 1)
    (h : r n < s n)
    : r n = r (s n) := by
```

The analogue of this one goes by the name `sn_eq_srn`.

*Proof.* We prove only the first one; the second one is similar. Let $`n > 1` and suppose that $`s(n) > 1` and that $`r(n) < s(n)`. We want to see that $`r(n) = r(s(n))`. By the injectivity of $`f`, we can check instead that $`f (r (n)) = f (r (s (n)))`. Let us see that both inequalities hold.

```anchor rn_eq_rsn_start (module := UrysohnsLemma.MyDefs.my_rs_functions)
  apply f_prop.left.left
  apply ge_antisymm
```

(1) To see $`f (r (s (n))) \leq f (r (n))`, we apply the third part of `r_prop`. So we have to see that $`r(s(n)) < n`, which is easy since $`r(s(n)) < s(n) < n`, and that $`f (r (s (n))) < f n`. The latter is true because if we had $`f(n) < f(r(s(n)))`, since $`r(s(n)) < s(n)` we would have $`f(s (n)) \leq f(r(s(n)))`, but that is impossible because $`f(r(s(n))) < f(s(n))` by construction (this last part is given by an auxiliary result `f_rs_prop`).

```anchor rn_eq_rsn_case1 (module := UrysohnsLemma.MyDefs.my_rs_functions)
  · -- f (r (s n)) ≤ f (r n)
    apply (r_prop n hn).right.right
    · simp
      trans s n
      · exact List.mem_range.mp (r_prop (s n) hsn).left
      · exact List.mem_range.mp (s_prop n hn).left
    · exact f_rs_prop n hn hsn
```

(2) To see that $`f (r (n)) \leq f (r (s (n)))`, it suffices to see that $`r(n) < s(n)` by hypothesis and that $`f(r(n)) < f(n) < f(s(n))` by the properties of $`r` and $`s`. Then applying the third basic property to $`s(n) > 1` and $`r(n) < s(n)` we obtain the result.

```anchor rn_eq_rsn_case2 (module := UrysohnsLemma.MyDefs.my_rs_functions)
  · -- f (r n) ≤ f (r (s n))
    apply (r_prop (s n) hsn).right.right
    · exact List.mem_range.mpr h
    · trans f n
      · exact (r_prop n hn).right.left
      · exact (s_prop n hn).right.left
```
∎

## Construction of $`G`

The construction of $`G : \mathbb{Q} \to \mathcal{P}(X)` is, as we have explained, a construction by induction. To begin with, it is easier to construct $`G : \mathbb{N} \to \mathcal{P}(X)`, and afterwards take $`G \circ f^{-1} : Q \to \mathcal{P}(X)` where $`f` is the function numbering $`Q` that we had obtained before.

Lean supports inductive definitions in a very natural way. A widely used example is the Fibonacci sequence: define $`Fib(0) = 0` and $`Fib(1) = 1`, and from there, $`Fib(n) = Fib(n-1)+Fib(n-2)` for each $`n > 1`. In Lean, we write

```anchor Fib_def (module := UrysohnsLemma.Docs.Urysohn)
def Fib : ℕ → ℕ := fun n ↦
  if n = 0 then 0
  else if n = 1 then 1
  else Fib (n-1) + Fib (n-2)
```

In view of this, my first approach to the construction of $`G` was the following:

* For $`n = 0`, define $`G(0) = C_2^c`.
* For $`n = 1`, take $`G(1)` to be the result of applying the characterisation of normal spaces to the open set $`C_2^c` and the closed set $`C_1`.
* For $`n >1`, take $`G(n)` to be the result of applying the characterisation of normal spaces ({ref "caracterizacion-normal"}[3.14]) to the open set $`G(s(n))` and the closed set $`\overline{G(r(n))}`.

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

Where in the final `sorry`s we would have to prove that $`G(s(n))` is open, that $`\overline{G(r(n))}` is closed and that $`\overline{G(r(n))} \subseteq G(s(n))`, in order to be able to apply the characterisation of normality (`hT`).

All of this, we "know": it is the induction hypothesis. But we have not told Lean anything about it yet. How can we prove something about an object we have not defined yet, when we need to have proved it in order to define it?

To avoid this problem, I took a different strategy. First, I define the notion of a _normal pair_ in the following way.

### Definition 4.1
%%%
number := false
%%%

Given $`U, C \subseteq X`, we say that $`(U, C)` is a _normal pair_ if $`U` is open, $`C` is closed and $`C \subseteq U`. That is, if they satisfy the conditions needed to apply the characterisation of normal spaces ({ref "caracterizacion-normal"}[3.14]).

```anchor normal_pair_def (module := UrysohnsLemma.Separation.def_G)
def normal_pair {X : Type} [TopologicalSpace X]
    : (Set X × Set X) → Prop := fun (U, C) ↦ (IsOpen U ∧ IsClosed C ∧ C ⊆ U)
```

Now, I define a function `from_normality` that takes any two sets of $`X`, and returns the result of applying the characterisation of normal spaces if they form a normal pair, and the empty set otherwise.

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

Now, when constructing $`G`, I no longer have to worry about whether it always produces open sets or not, because I can define it in terms of this last function, which is defined for any two sets. Once it is defined, I can prove that each set obtained is in fact open.

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

However, Lean is still not satisfied with this, and we receive this error: `fail to show termination for G`. That is, we are defining a recursive function, $`G`, but it is not evident that the calls to $`G` inside $`G` refer to already-defined sets. In other words, it is not evident that $`r(n) < n` and $`s(n) < n`. Therefore, at the end of the definition we have to add a proof that this is indeed the case.

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

We have our function $`G`! Although there is still a lot of work to do. Let us see that the properties we wanted from $`G` hold.

### Lemma 4.5
%%%
tag := "prop-G-open"
number := false
%%%

For each $`n \in \mathbb{N}`, $`G(n)` is open in $`X`.

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

*Proof.* Note that the function `from_normality` always produces open sets, because either it is the result of applying {ref "caracterizacion-normal"}[3.14], or it is the empty set, which is open (proved in `from_normality_open`).

Let $`n \in \mathbb{N}`. We have to distinguish three cases, since there are three cases in the definition of $`G`.

(1) If $`n = 0`, then simply by hypothesis $`G(0) = C_2^c` is open.

```anchor G_Prop1_case_n0 (module := UrysohnsLemma.Separation.def_G)
  intro n


  cases' Nat.eq_zero_or_pos n with hn hn
  · -- n = 0
    simp [hn, G]
    exact { isOpen_compl := hC2 }
```

(2) If $`n = 1`, then we are applying the function `from_normality` to $`C_2^c` and $`C_1`. Hence it is open.

```anchor G_Prop1_case_n1 (module := UrysohnsLemma.Separation.def_G)
  have : n = 1 ∨ n > 1  := Or.symm (Decidable.lt_or_eq_of_le' hn)
  cases' this with hn1 hn1
  · -- n = 1
    rw [G]
    simp [hn1]
    exact from_normality_open hT C2ᶜ C1
```

(3) Now, if $`n > 1`, then we are applying the function `from_normality` to $`G(s(n))` and $`\overline{G(r(n))}`. Hence it is open analogously. ∎

For the next result we are going to use complete induction. I have defined my own principle of complete induction, proved from the usual complete induction in Lean, for simplicity.

```anchor my_stronger_induction_sig (module := UrysohnsLemma.MyDefs.my_induction)
theorem my_stronger_induction (n : ℕ) (P Q : ℕ → Prop)
    (hn : P n)
    (h : ∀ n : ℕ, P n → ((∀ m < n, P m → Q m) → Q n)) :
    (Q n) := by
```

### Lemma 4.6
%%%
number := false
%%%

For each $`n > 1`, we have:

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

*Proof.* We proceed by complete induction on $`n`.

```anchor G_Prop2_start (module := UrysohnsLemma.Separation.def_G)
  intro n hn

  let P : ℕ → Prop := fun m ↦ m > 1
  apply my_stronger_induction n P
  exact hn
  simp [P]
  intro n hn hi
```

We have the following induction hypothesis: for each $`m < n` with $`m > 1` we have that $`\overline{G(r(m))} \subseteq G(m) \subseteq \overline{G(m)} \subseteq G(s(m))`.

We want to see that then the same holds for $`n`.

```
hi : ∀ m < n, 1 < m → closure (G hT C1 C2 (r m)) ⊆ G hT C1 C2 m ∧ closure (G hT C1 C2 m) ⊆ G hT C1 C2 (s m)

⊢ closure (G hT C1 C2 (r n)) ⊆ G hT C1 C2 n ∧ closure (G hT C1 C2 n) ⊆ G hT C1 C2 (s n)
```

Note that if $`G(n)` is obtained via {ref "caracterizacion-normal"}[3.14] applied to $`G(s(n))` and $`\overline{G(r(n))}`, the above reduces to checking that $`(G(s(n)), \overline{G(r(n))})` is a normal pair (proved in `from_normality_prop2`).

```anchor G_Prop2_normalpair_stmt (module := UrysohnsLemma.Separation.def_G)
  have normalpair : normal_pair (G hT C1 C2 (s n), closure (G hT C1 C2 (r n)))
```

We have seen that $`r(n)` is either $`r(n) = 1` or $`r(n) > 1` (`r_options`) and $`s(n)` is either $`s(n) = 0` or $`s(n) > 1` (`s_options`). Let us see, for example, the case $`r(n) = 1`, $`s(n) > 1`. The rest are similar and can be consulted in the repository.

(1) Seeing that $`G(s(n))` is open is easy; we have already seen that $`G` always returns open sets.

```
  ...
    · exact G_Prop1 hT C1 C2 hC1 hC2 hC1C2 (s n)
```

(2) Seeing that $`\overline{G(r(n))}` is closed is easy; we have already seen that the closure of any set is closed.

```
  ...
    · exact isClosed_closure
```

(3) Now, to see that $`\overline{G(r(n))} \subseteq G(s(n))`, we need to use the induction hypothesis.

We know that $`s(n) < n`. So we can apply the induction hypothesis to $`s(n)`, obtaining that

$$`\overline{G(r(s(n)))} \subseteq G(s(n)) \subseteq \overline{G(s(n))} \subseteq G(s(s(n)))`

But, since $`s(n) >1`, we have that $`r(n) = r(s(n))` (`rn_eq_rsn`), obtaining $`\overline{G(r(n))} \subseteq G(s(n))`.

```
  ...
    · have hsn := (s_prop n hn).left -- hsn : s n ∈ Finset.range n
      simp at hsn -- hsn : s n < n
      specialize hi (s n) hsn hs -- aplicar la H.I. a s(n)
      rw [rn_eq_rsn n hn hs (by linarith)] -- usar r(n) = r(s(n))
      exact hi.left
```
∎

## The property (★)

This is the most important property we want to require of the function $`G`, since it is the one that guarantees the continuity of the function we want to construct for the proof of Urysohn's lemma, as we will see later.

### Lemma 4.7
%%%
number := false
%%%

Let $`n, m \in \mathbb{N}` with $`f(n) < f(m)`. Then

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

To prove this result we are going to use a more general induction principle than the usual induction on the naturals. Whenever we have a well-founded relation on a set, an induction principle on that set can be described.

In our case, we are going to use the lexicographic order on $`\mathbb{N}^2`, defined by $`(n, m) < (n', m') \iff n<n' \lor (n=n' \land m<m')`. This is already defined in Mathlib, and it is also proved that it is a well-founded relation.

```anchor lt_pair_defs (module := UrysohnsLemma.MyDefs.my_lex_order)
def lt_pair : (ℕ × ℕ) → (ℕ × ℕ) → Prop := Prod.Lex (Nat.lt) (Nat.lt)
def lt_pair_wfr : WellFoundedRelation (ℕ × ℕ) := Prod.lex (Nat.lt_wfRel) (Nat.lt_wfRel)
lemma lt_pair_wf : WellFounded lt_pair := lt_pair_wfr.wf
```

*Proof.* We proceed, therefore, by well-founded induction on the pair $`(n, m)`

```
    := by
  ... -- ciertas modificaciones del objetivo
  apply WellFounded.induction lt_pair_wf
  ...
  intro n m
  intro hi hnm
```

We therefore have the following induction hypothesis:

```
  hi : ∀ (a b : ℕ), lt_pair (a, b) (n, m) → f a < f b → closure (G hT C1 C2 a) ⊆ G hT C1 C2 b
```

Now we split into different cases of values of $`n` and $`m`. We focus on the case $`n >1, m>1`, which is the most interesting one, and the rest can be consulted in the repository.

Moreover, there are three possible cases: either $`f(s(n)) < f(m)`, or $`f(s(n)) = f(m)`, or $`f(s(n)) > f(m)`.

(1) If $`f(s(n)) < f(m)`, we have on the one hand that $`\overline{G(s(n))} \subseteq G(m)`, since $`(s(n), m) < (n, m)` and the induction hypothesis.

On the other hand, $`\overline{G(n)} \subseteq G(s(n))`, by the second property of $`G`. So we have

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

(2) If $`f(s(n)) = f(m)` it is very easy, because then by the injectivity of $`f` we have $`s(n)= m`, and $`\overline{G(n)} \subseteq G(s(n)) = G(m)` by the second property of $`G`.

```
  ...
    · -- si f (s n) = f m
      apply f_prop.left.left at h
      rw [h]
      exact (G_Prop2 n hn1).right
```

(3) Suppose now that $`f(s(n))>f(m)`. This is the most complicated case, and it requires splitting again into three possible options for $`f(n) \sim f(r(m))`.

If $`f(n) < f(r(m))`, we proceed in a similar way to (1), using the induction hypothesis for $`(n, r(m)) < (n, m)`. If $`f(n) = f(r(m))`, we do the same as in (2). Finally, it remains to prove that $`f(r(m)) < f(n)` cannot happen.

Indeed, if $`f(s(n))>f(m)`, it must be that $`n < m`, because if we had $`m<n` we would have $`f(n) < f(m) < f(s(n))`, which is impossible by the properties of $`s`. But then, if we had $`f(r(m)) < f(n)` we would have $`f(r(m)) < f(n) < f(m)` with $`n < m`, which is impossible by the properties of $`r`.

```
  ...
    · -- si f (r m) < f n
      by_contra
      have r_prop := r_prop.right.right n n_lt_m hnm -- f n ≤ f (r m)
      apply not_lt.mpr at r_prop -- ¬f (r m) < f n
      exact r_prop h' -- teniamos h' : f (r m) < f n
```
∎

## Composition with $`f^{-1}`

Finally, let us remember that the function $`G` we were looking for is not of the form $`\mathbb{N} \to \mathcal{P}(X)` but of the form $`\mathbb{Q} \cap [0, 1] \to \mathcal{P}(X)`. In particular, we are going to extend it to $`\mathbb{Q} \to \mathcal{P}(X)` in the following way:

$$`H : \mathbb{Q} \to \mathcal{P}(X), ~~ q \mapsto
\begin{cases}
\emptyset & \text{if } q < 0 \\
(G \circ f^{-1})(q) & \text{if } 0 \leq q \leq 1 \\
X & \text{if } 1 < q
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

### Lemma 4.8
%%%
number := false
%%%

For the closed sets $`C_1` and $`C_2` chosen at the beginning of the section, the previously defined function $`H` satisfies the following properties:

1. $`H(1) = C_2^c`
1. $`H(0)` is such that $`C_1 \subseteq H(0) \subseteq \overline{H(0)} \subseteq C_2^c`
1. For each $`q \in \mathbb{Q}`, $`H(q)` is open in $`X`.
1. For each $`p, q \in \mathbb{Q}` with $`p < q`, we have $`\overline{H(p)} \subseteq H(q)`

*Proof.* All these properties follow almost trivially from those of $`G`, using that $`f` is bijective and the fixed values it takes at $`0` and $`1`. The only addition is the values outside $`[0, 1]`, for which the last properties are proved easily since $`\emptyset` and $`X` are open, $`\overline{\emptyset} = \emptyset \subseteq U` for any $`U` and $`U \subseteq X` for any $`U`. ∎

# Construction of a separating continuous function
%%%
file := "construccion-funcion"
%%%

Continuing with the outline we had proposed, we now construct the following function

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

Now, we want to construct a function of the following form

$$`\begin{array}{rcrcl}
  f & : & X & \longrightarrow & [0, 1] \\
    & & x & \longmapsto & \inf F(x)
\end{array}`

However, we have to make sure that we can define this function, that is, that the set $`F(x)` has an infimum for each $`x \in X`.

## The function $`F`
%%%
tag := "seccion-funcion-F"
%%%

### Lemma 4.9
%%%
number := false
%%%

Let $`F :  X  \to \mathcal{P}(\mathbb{Q})` be the function defined above. Then for each $`x \in X`, $`F(x)` is a non-empty set.

*Proof.* Let $`x \in X`. Any $`q > 1` is such that $`q \in F(x)`, since if $`q >1`, $`H(q) = X`, hence $`x \in H(q)`. ∎

```anchor hF_non_empty_full (module := UrysohnsLemma.Separation.def_F)
lemma hF_non_empty {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    :  ∀ x : X, (F hT C1 C2 x).Nonempty := by
  intro x
  use 2
  simp [F, H]
```

### Lemma 4.10
%%%
number := false
%%%

For each $`x \in X`, if $`q < 0` then $`q \notin F(x)`. That is, all the elements of $`F(x)` are non-negative.

*Proof.* Let $`x \in X` and $`q < 0`. Then $`H(q) = \emptyset`, hence obviously $`x \notin H(q)`. ∎

We will call this result `hFx_non_neg`. As a consequence, we have:

### Lemma 4.11
%%%
number := false
%%%

For each $`x \in X`, $`0` is a lower bound of $`F(x)`.

```anchor hFx_has_lb_0_sig (module := UrysohnsLemma.Separation.def_F)
lemma hFx_has_lb_0 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, 0 ∈ lowerBounds (F hT C1 C2 x) := by
```

Therefore, given $`x \in X`, since $`F(x)` is a non-empty set bounded from below, we can conclude that $`F(x)` has an infimum *as a real set*, that is, we can conclude that there exists a number $`r \in \mathbb{R}` such that $`r = \inf F(x)`. This result is included in Mathlib:

```anchor Real_exists_isGLB_quote (module := UrysohnsLemma.Docs.Urysohn)
theorem Real.exists_isGLB {s : Set ℝ} (hne : s.Nonempty) (hbdd : BddBelow s) :
    ∃ x, IsGLB s x
```

We could try to write something like this:

```
  lemma hFx_has_lb_0 (...)
    : ∀ x : X, ∃ r : ℝ, IsGLB (F hT C1 C2 x) r := by sorry
```

However, this gives us the following error:

```
  argument r has type ℝ but is expected to have type ℚ
```

This is because, in Mathlib, `IsGLB` is defined in the following way:

```anchor IsGLB_def_quote (module := UrysohnsLemma.Docs.Urysohn)
def IsGLB [Preorder α] (s : Set α) : α → Prop :=
  IsGreatest (lowerBounds s)
```

That is, it is only defined for values of type $`\alpha` if $`s \subset \alpha`. Since $`F(x) \subset \mathbb{Q}`, we cannot say that $`r \in \mathbb{R}` is its infimum.

Therefore, we need to define in Lean an auxiliary function $`\tilde{F}` such that $`\tilde{F}(x) = F(x)` for each $`x`, but seen as a subset of $`\mathbb{R}`. We do it in the following way.

```anchor inclQR_F_Real_def (module := UrysohnsLemma.Separation.def_F)
def inclQR : ℚ → ℝ := fun q ↦ q

def F_Real {X : Type} [TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : X → Set ℝ :=

    fun x ↦ inclQR '' (F hT C1 C2 x)
```

This new function $`\tilde{F}` is a function with the same properties as $`F`, that is, for each $`x \in X`, $`\tilde{F}(x)` is a non-empty set with $`0` as a lower bound. This is proved immediately using the properties of $`F`, although it is necessary to be careful with Lean's type inference in some cases.

But now $`\tilde{F}` returns subsets of $`\mathbb{R}`, so we can assert that it has an infimum in $`\mathbb{R}`.

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

## The function $`f`
%%%
tag := "seccion-funcion-f"
%%%

Once we have made sure that $`\tilde{F}` has an infimum, we can try to define our function $`f` as we wanted. Before that, let us make the following remark.

We want to find a function $`f : X \to [0, 1]`. However, we have only guaranteed that $`\inf \tilde{F}(x) \in \mathbb{R}`; not necessarily $`\inf \tilde{F}(x) \in [0, 1]`.

Evidently, the latter is true, because $`0` is a lower bound, so the infimum will be at least $`0`, and $`\forall q>1, q \in F(x)`, so the infimum cannot be greater than $`1`.

However, for ease of working with Lean, we will first define a function that is simply

$$`\begin{array}{rcrcl}
  k & : & X & \longrightarrow & \mathbb{R} \\
    & & x & \longmapsto & \inf \tilde{F}(x)
\end{array}`

and we prove that indeed $`k(x) \in [0, 1]` for each $`x\in X`. Later, we will use the function $`f(x) = k(x)`, taking care to specify that $`k(x) \in [0, 1]`.

```anchor k_def (module := UrysohnsLemma.Separation.def_k)
noncomputable def k {X : Type} [TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : X → ℝ :=
    fun x ↦ Classical.choose (F_Real_has_inf hT C1 C2 x)
```

We obtain the following property, the result of applying `Classical.choose_spec` to $`k`.

```anchor k_prop_sig (module := UrysohnsLemma.Separation.def_k)
lemma k_prop {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x, IsGLB (F_Real hT C1 C2 x) (k hT C1 C2 x) := by
```

### Lemma 4.12
%%%
number := false
%%%

For each $`x \in X`, the function $`k : X \to \mathbb{R}` we have just defined satisfies $`k(x) \in [0, 1]`.

```anchor k_in_01_sig (module := UrysohnsLemma.Separation.def_k)
lemma k_in_01 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, (k hT C1 C2 x) ∈ Set.Icc 0 1 := by
```

*Proof.* The proof is easy and we have already explained it, but in Lean we need to give a complete specification, so we explain it.

Let $`x \in X`. Recall that $`k(x)` is a lower bound of $`\tilde{F}(x)` (`klb`) and it is the greatest of them (`kglb`).

```anchor k_in_01_start (module := UrysohnsLemma.Separation.def_k)
  intro x
  have ⟨klb, kglb⟩ := k_prop hT C1 C2 x
  constructor
```

Seeing that $`k(x) \geq 0` is easy, because we have already seen that $`0` is a lower bound, and $`k(x)` is the greatest one.

```anchor k_in_01_case1 (module := UrysohnsLemma.Separation.def_k)
  · exact kglb (F_Real_0_is_LB hT C1 C2 x)
```

Now, to see that $`k(x) \leq 1`, we proceed by contradiction. Suppose that $`k(x) > 1`. Then there exists a rational number $`q` such that $`1 < q < k(x)`. Since $`q > 1`, we know that $`q \in \tilde{F}(x)`. But in that case, since $`k(x)` is a lower bound, $`k(x) \leq q`, which is contradictory.

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

Finally, before moving on to the proof of Urysohn's lemma at last, we give several properties of $`k` that we will need. Recall that $`H` was $`G \circ f^{-1}` extended to $`\mathbb{Q}`.

### Lemma 4.13
%%%
tag := "claim1"
number := false
%%%

For each $`p \in \mathbb{Q}` and each $`x \in X`, if $`x \in \overline{H(p)}` then $`k(x) \leq p`.

```anchor k_claim1_sig (module := UrysohnsLemma.Separation.def_k)
lemma k_claim1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ p : ℚ, ∀ x : X, x ∈ closure (H hT C1 C2 p) → (k hT C1 C2 x) ≤ p := by
```

*Proof.* Let $`p \in \mathbb{Q}` and $`x \in X` with $`x \in \overline{H(p)}`. Suppose, for contradiction, that $`k(x) > p`. Then there exists a rational $`q \in \mathbb{Q}` such that $`p < q < k(x)`.

```anchor k_claim1_start (module := UrysohnsLemma.Separation.def_k)
  intro p x hx
  by_contra c
  simp at c
  have ⟨q, hq⟩ := exists_rat_btwn c
```

Since $`p < q` and $`x \in \overline{H(p)}`, by ({ref "eq-star"}[★]) we have that $`x \in H(q)`.

```anchor k_claim1_apply_ordered (module := UrysohnsLemma.Separation.def_k)
  apply H_isOrdered hT C1 C2 hC1 hC2 hC1C2 p q
    (by exact_mod_cast hq.left)
    at hx
```

Now, $`x \in H(q)` means that $`q \in \tilde{F}(x)`. But $`k(x)` is a lower bound of $`\tilde{F}(x)`, hence $`k(x) < q`, which contradicts $`q < k(x)`.

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

### Lemma 4.14
%%%
tag := "claim2"
number := false
%%%

For each $`p \in \mathbb{Q}` and each $`x \in X`, if $`x \notin H(p)` then $`k(x) \geq p`.

```anchor k_claim2_sig (module := UrysohnsLemma.Separation.def_k)
lemma k_claim2 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ p : ℚ, ∀ x : X, x ∉ (H hT C1 C2 p) → (k hT C1 C2 x) ≥ p := by
```

*Proof.* The proof is very similar to the previous one and can be found in the repository. ∎

## Properties on the closed sets $`C_1` and $`C_2`

Finally, let us see how the function $`k` behaves on the closed sets we want to separate. This will leave the path completely clear to complete the proof of Urysohn's lemma. We are going to see the proofs for $`C_1`; the ones for $`C_2` are similar and can be checked in the repository.

We want to arrive at $`k(C_1) = \{0\}`. This property is built step by step, using properties of the functions it relies on.

### Lemma 4.15
%%%
number := false
%%%

Consider $`F : X \to \mathcal{P}(\mathbb{Q})`. For each $`x \in C_1`, we have that $`F(x) = \{q \in \mathbb{Q} ~|~ q \geq 0\}`.

```anchor F_at_C1_sig (module := UrysohnsLemma.Separation.def_F)
lemma F_at_C1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ x : X, x ∈ C1 → F hT C1 C2 x = {q : ℚ | q ≥ 0} := by
```

*Proof.* Let $`x \in C_1`. Seeing that $`F(x) \subseteq \{q \in \mathbb{Q} ~|~ q \geq 0\}` is easy, since we have already seen that no value of $`F(x)` is negative (`hFx_non_neg`). Now, let $`q \geq 0` and let us see that $`q \in F(x)`, that is, that $`x \in H(q)`.

If $`q > 0`, by the property ({ref "eq-star"}[★]) of $`H`, $`\overline{H(0)} \subseteq H(q)`. And by the construction of $`H` we have $`C_1 \subseteq H(0)`. Hence $`x \in H(q)`. If $`q = 0`, since $`C_1 \subseteq H(0)`, $`x\in H(q)`.

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

### Lemma 4.16
%%%
number := false
%%%

Consider $`F : X \to \mathcal{P}(\mathbb{Q})`. For each $`x \in C_1`, we have that $`\inf{F}(x) = 0`.

```anchor F_0_GLB_in_C1_sig (module := UrysohnsLemma.Separation.def_F)
lemma F_0_GLB_in_C1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ x : X, x ∈ C1 → IsGLB (F hT C1 C2 x) 0 := by
```

Once we know that $`F(x) = \{q \in \mathbb{Q} ~|~ q \geq 0\}`, seeing that the infimum of this set is 0 is direct. Note that here we can indeed define the infimum over $`F` because $`0 \in \mathbb{Q}`. Now we can state the same for $`\tilde{F}`, simply being careful with the type of $`F(x)` and of $`0`.

### Lemma 4.17
%%%
number := false
%%%

Consider $`\tilde{F} : X \to \mathcal{P}(\mathbb{R})`. For each $`x \in C_1`, we have that $`\inf{\tilde{F}}(x) = 0`.

```anchor F_Real_0_GLB_in_C1_sig (module := UrysohnsLemma.Separation.def_F)
lemma F_Real_0_GLB_in_C1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ x : X, x ∈ C1 → IsGLB (F_Real hT C1 C2 x) 0 := by
```

Finally, we have:

### Lemma 4.18
%%%
tag := "prop-kC1"
number := false
%%%

Consider $`k : X \to \mathbb{R}`. Recall that $`C_1` is non-empty. We have that $`k (C_1) = \{0\}`.

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

*Proof.* To see that $`k(C_1) \subseteq \{0\}`, since $`k(x) := \inf \tilde{F}(x)`, and $`\inf \tilde{F}(x) = 0` for $`x \in C_1` by the previous result, it suffices to use that the infimum is unique.

```anchor k_in_C1_is_0_forward (module := UrysohnsLemma.Separation.def_k)
  ext r
  constructor
  · intro ⟨x, hx, hr⟩
    rw [← hr]
    apply IsGLB.unique (k_prop hT C1 C2 x)
    exact F_Real_0_GLB_in_C1 hT C1 C2 hC1 hC2 hC1C2 x hx
```

To see that $`\{0\} \subseteq k(x)`, we need to see that there exists an $`x \in C_1` such that $`k(x) = 0`. Since $`C_1` is non-empty, let $`x \in C_1` be arbitrary. Then $`k(x) = 0`, proceeding in the same way as in the first inclusion.

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

# The proof
%%%
file := "la-demostracion"
%%%

We are going to prove, therefore, the main implication of Urysohn's lemma, following the Lean proof step by step.

Let $`X` be a normal space. We want to prove that for each pair of non-empty disjoint closed sets $`C_1` and $`C_2` there exists a continuous function $`f : X \to [0, 1]` such that $`f(C_1) = \{0\}` and $`f(C_2) = \{1\}`.

Let, then, $`C_1` and $`C_2` be closed sets with those conditions.

```anchor Urysohn_forward_intro (module := UrysohnsLemma.Separation.urysohn)
  · -- →
    intro hT C1 C2 C1nempty C2nempty C1closed C2closed C1C2disj
```

To begin with, we prove some auxiliary properties, such as that $`C_2^c` is open (since $`C_2` is closed), and that $`C_1 \subseteq C_2^c` (since they are disjoint), which will make it easier to apply the rest of the results we have been proving. We will also use the characterisation of normal spaces ({ref "caracterizacion-normal"}[3.14]) on the hypothesis that $`X` is normal.

```anchor Urysohn_forward_aux (module := UrysohnsLemma.Separation.urysohn)
    have C2c_open : IsOpen C2ᶜ := by exact IsClosed.isOpen_compl
    have hC1C2 : C1 ⊆ C2ᶜ := by exact Disjoint.subset_compl_left (id (Disjoint.symm C1C2disj))

    rw [characterization_of_normal] at hT
```

Now, for convenience we are going to define the following functions.

```anchor Urysohn_forward_let_Gg (module := UrysohnsLemma.Separation.urysohn)
    let G := H hT C1 C2
    let g := fun x ↦ k hT C1 C2 x
```

This way we do not have to drag the arguments of $`H` and $`k` along at every step. I rename $`H` to $`G` to keep the notation of the outline, since it is the function of the form $`G : \mathbb{N} \to \mathcal{P}(X)`. I also rename $`k` to $`g`, to avoid confusion.

Now, recall that $`k : X \to \mathbb{R}` was not exactly the function we were looking for. We are finally going to define the function to use to separate our closed sets, $`f`, in the following way:

```anchor Urysohn_forward_let_f (module := UrysohnsLemma.Separation.urysohn)
    let f : X → Y := fun x ↦ ⟨g x, by
      rw [hY]
      exact k_in_01 hT C1 C2 x⟩
```

That is, $`f` is a function that takes values in $`X` and returns a real value together with a proof that this value is actually in the interval $`[0, 1]`, given using `k_in_01`, which we had proved before. Therefore, Lean interprets it as a function $`f : X \to [0, 1]`, which is exactly what we wanted.

So we already have the separating function and we can take the big step:

```anchor Urysohn_forward_use_f (module := UrysohnsLemma.Separation.urysohn)
    use f
```

It remains to prove that $`f` is continuous, that $`f(C_1) = \{0\}` and that $`f(C_1) = \{1\}`.

```anchor Urysohn_forward_constructor (module := UrysohnsLemma.Separation.urysohn)
    constructor
```

## Continuity of $`f`

We want to see that $`f` is continuous. To do so, we apply the result `continuousInSubspace_iff_trueForBase`, which we saw was a combination of {ref "prop-continuidad-subespacio"}[3.12] and {ref "prop-continuous-base"}[3.13].

```anchor Urysohn_continuity_rw (module := UrysohnsLemma.Separation.urysohn)
    · rw [@continuousInSubspace_iff_trueForBase
        X ℝ Y T T' R hR f
        {s | ∃ a b : ℝ, s = Set.Ioo a b}
        (by exact BaseOfRealTopo hT')]
```

So it suffices to prove that for each basic open set $`W` of $`\mathbb{R}`, $`f^{-1}(W)` is open in $`X`. Let $`W = (a, b)` be an open set of the base formed by the real open intervals.

```anchor Urysohn_continuity_introW (module := UrysohnsLemma.Separation.urysohn)
      intro W hW
      obtain ⟨a, b, hW⟩ := hW
```

We want to see that $`f^{-1}(W)` is open in $`X`. Using the characterisation of open sets ({ref "caracterizacion-abierto"}[3.1]), it suffices to see that it is a neighbourhood of all of its points. Let then $`x \in f^{-1}(W)`, which means that $`f(x) \in (a, b)`.

```anchor Urysohn_continuity_neighbourhood (module := UrysohnsLemma.Separation.urysohn)
      rw [A_open_iff_neighbourhood_of_all]
      intro x hx
      rw [Set.mem_preimage, hW] at hx
```

Since $`f(x) \in (a, b)`, there exists $`p \in \mathbb{Q}` with $`a < p < f(x)`, and there also exists $`q \in \mathbb{Q}` with $`f(x) < q < b`.

```anchor Urysohn_continuity_pq (module := UrysohnsLemma.Separation.urysohn)
      obtain ⟨p, hp⟩ := exists_rat_btwn hx.left
      obtain ⟨q, hq⟩ := exists_rat_btwn hx.right
```

We are going to prove that $`x \in G(q)` and that $`x \notin \overline{G(p)}`.

First let us recall the results {ref "claim1"}[4.13] and {ref "claim2"}[4.14] (with the function names corresponding to the current notation):

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

(1) To see that $`x \notin \overline{G(p)}`, suppose by contradiction that it is. Then we can apply `claim1` and obtain that $`g(x) \leq p`, but we had $`p < f(x) = g(x)`, contradiction.

```anchor Urysohn_continuity_aux1 (module := UrysohnsLemma.Separation.urysohn)
      have aux1 : x ∉ closure (G p)
      · by_contra c
        apply claim1 p x at c
        linarith
```

(2) Similarly, if we suppose by contradiction that $`x \notin U(q)`, then by `claim2` we obtain that $`g(x) \geq q`, but we had $`q > f(x) = g(x)`, contradiction.

```anchor Urysohn_continuity_aux2 (module := UrysohnsLemma.Separation.urysohn)
      have aux2 : x ∈ G q
      · by_contra c
        apply claim2 q x at c
        linarith
```

Recapping, we want to see that $`f^{-1}(W)` is a neighbourhood of $`x` ($`x` was arbitrary). This is, by definition, finding a set $`U\subseteq X` that is open and such that $`x \in U \subseteq f^{-1}(W)`.

Let us take the set $`U = G(q) \cap (\overline{G(p)})^c` and see that it satisfies these conditions.

```anchor Urysohn_continuity_use_U (module := UrysohnsLemma.Separation.urysohn)
      use (G q) ∩ (closure (G p))ᶜ

      constructor
```

(1) Let us see that $`U \subseteq f^{-1}(W)`. To do so, let $`y \in U` and let us see that $`y \in f^{-1}(W) = f^{-1}((a, b))`, that is, let us see that $`a < f(y) < b`.

```anchor Urysohn_continuity_use_U_intro_y (module := UrysohnsLemma.Separation.urysohn)
      · intro y hy
        rw [hW]
        constructor
```

We have that $`y \notin G(p)`, since otherwise, $`y \in G(p) \subseteq \overline{G(p)}`, but $`y \in \overline{G(p)}^c`. Applying `claim1`, we have that $`f(y) = g(y) \geq p > a`.

```anchor Urysohn_continuity_case_a (module := UrysohnsLemma.Separation.urysohn)
        · have hy : y ∉ G p
          · by_contra c
            apply subset_closure at c
            exact hy.right c
          apply claim2 p y at hy
          linarith
```

On the other hand, since $`y \in G(q) \subseteq \overline{G(q)}`, by `claim2` we have that $`f(y) = g(y) \leq q < b`.

```anchor Urysohn_continuity_case_b (module := UrysohnsLemma.Separation.urysohn)
        · have hy := hy.left
          apply subset_closure at hy
          specialize claim1 q y hy
          linarith
```

So we conclude that $`f(y) \in (a, b) = W`. The hard work is already done; it only remains to see that $`x \in U` and that $`U` is open.

```anchor Urysohn_continuity_constructor2 (module := UrysohnsLemma.Separation.urysohn)
      constructor
```

(2) As we had seen, $`x \in G(q)` and $`x \notin \overline{G(p)}`. Hence $`x \in U`.

```anchor Urysohn_continuity_xinV (module := UrysohnsLemma.Separation.urysohn)
      · -- probar que `x ∈ V`
        constructor
        · exact aux2
        · exact aux1
```

(3) Proving that $`U` is open is easy: since it is a finite intersection, it suffices to see that both components are open. By {ref "prop-G-open"}[4.5], $`G(q)` is open. Moreover, $`\overline{G(p)}` is closed for being a closure, so its complement is open.

```anchor Urysohn_continuity_Vopen (module := UrysohnsLemma.Separation.urysohn)
      · -- probar que `V` es abierto
        apply IsOpen.inter
        · exact H_isOpen hT C1 C2 C1closed C2c_open hC1C2 q
        · rw [isOpen_compl_iff]
          exact isClosed_closure
```

## Image of $`f`

To finish the proof, it only remains to see that $`f(C_1) = \{0\}` and that $`f(C_2) = \{1\}`.

To begin with, note that $`f(A) = g(A)` for any $`A \subseteq X`.

```anchor Urysohn_image_aux (module := UrysohnsLemma.Separation.urysohn)
    have aux : ∀ A : Set X, f '' A = g '' A
    · intro A; ext x; simp [f]
```

So we can reduce the goal to $`g(C_1) = \{0\}` and $`g(C_2) = \{1\}`.

The result then follows from lemma {ref "prop-kC1"}[4.18] and its analogue for $`C_2`.

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

Which concludes the proof of Urysohn's lemma.

# The Mathlib proof
%%%
file := "prueba-mathlib"
%%%

The proof of Urysohn's lemma that I have described in this chapter was implemented by me completely independently of the Mathlib one, which I did not read until I had completely written my proof. To close this chapter I would like to make a brief comparison of the two.

The implementation found in Mathlib is documented{citepOther refMathlib2023Urysohn}[].

As we mentioned at the beginning of the chapter, the most complicated part of the proof has been constructing the function $`G`, since it requires complete induction to construct the open sets and induction on two variables to prove their properties. Indeed, in the Mathlib documentation, they write:

> Most sources prove Urysohn's lemma using a family of open sets indexed by the dyadic rational numbers in $`[0, 1]`. There are many technical difficulties when formalising this proof (e.g., one needs to formalise the "dyadic induction", and then prove that the resulting family of open sets is monotone).

Indeed, it is possible to build the sequence we have constructed taking only the dyadics, but one runs into problems similar to the ones we have encountered. The goal of the Mathlib proof is, therefore, to avoid this complication. Below we will see an outline of the Mathlib proof.

Let $`X` be a normal space. Let $`\mathcal{CU}_X` be the set of normal pairs of $`X`, that is, the pairs of the form $`(C, U)` with $`U` open, $`C` closed and $`C \subseteq U`. We define the functions:

$$`\begin{array}{ccrclcccrcl}
  L & : & \mathcal{CU}_X & \longrightarrow & \mathcal{CU}_X & ~~\textnormal{and}~~ & R & : & \mathcal{CU}_X & \longrightarrow & \mathcal{CU}_X \\
  & & (C, U) & \longmapsto & (C, V) & & & & (C, V) & \longmapsto & (\overline{V}, U)
\end{array}`

Where $`V` is the result of applying the characterisation of normal spaces ({ref "caracterizacion-normal"}[3.14]) to the corresponding pair $`(C, U)`.

Moreover, for each $`(C, U) \in \mathcal{CU}_X` consider the sequence of functions $`\{f_n^{(C, U)} : X \to \mathbb{R}\}_{n\in \mathbb{N}}` given by

$$`\left\{
\begin{array}{lclc}
  f_0^{(C, U)}(x)  & = & \chi_{U^c}(x) & \\
  & & & \\
  f_{n+1}^{(C, U)}(x) & = & \dfrac{f_n^{L(C, U)}(x) + f_n^{R(C, U)}(x)}{2}, & n = 0, 1, \dots
\end{array}
\right.`

It can be proved that this is a monotone sequence of functions such that, for each pair $`(C, U)` and each $`n \in \mathbb{N}`, $`f_n^{(C, U)}(x) =0, \forall x \in C`, $`f_n^{(C, U)}(x) = 1,\forall x \in D`, and $`f_n^{(C, U)}(x) \in [0, 1],\forall x \in X`.

In particular, let $`C` and $`D` be the disjoint closed sets we want to separate and consider the pair $`(C, D^c) \in \mathcal{CU}_X`. Let $`f : X \to \mathbb{R}` be the function given by

$$`f(x) = \lim_{n \to \infty} f_n^{(C, D^c)}`

Then $`f` is a continuous function that separates $`C` and $`D`.
